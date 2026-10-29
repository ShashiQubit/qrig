#!/usr/bin/env python3
"""End-to-end benchmark pipeline: MQT Bench -> Qiskit DAG -> qrig -> MQT QCEC.

For every (benchmark, size) pair:

1. **Ingest**: fetch the circuit from MQT Bench at the ``algorithmic`` level and expose
   its multi-controlled structure (custom composite gates are unrolled until only
   standard or controlled gates remain; ``mcx``/``mcphase`` etc. are kept whole).
2. **Optimise**: run the verified DAG pass ``qrig.dag.QrigControlEquations`` (the
   control equations of the paper, every rewrite proved sound in Lean).
3. **Measure**: gate count, depth, multi-controlled gate count, and the CNOT count
   after compiling to ``{cx, u}`` with Qiskit's level-3 pipeline, with and without the
   qrig pre-pass.
4. **Verify**: MQT QCEC checks (with decision diagrams) that
   (a) the qrig output is equivalent to the benchmark, and
   (b) the fully compiled "qrig + Qiskit" circuit is equivalent to the benchmark.
   For up to ``--operator-max`` qubits, the unitaries are also compared with Qiskit's
   ``Operator`` as an independent check.

Usage::

    python benchmarks/mqt_pipeline.py                       # default suite
    python benchmarks/mqt_pipeline.py --benchmarks grover qft --sizes 4 6 8
    python benchmarks/mqt_pipeline.py --quick               # small smoke test

Writes ``mqt_results.md`` and ``mqt_results.json`` next to this file (or ``--out``).
Requires ``pip install qiskit mqt.bench mqt.qcec``.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
import traceback

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from qiskit import QuantumCircuit, transpile  # noqa: E402
from qiskit.circuit import ControlledGate  # noqa: E402
from qiskit.circuit.library import get_standard_gate_name_mapping  # noqa: E402
from qiskit.quantum_info import Operator  # noqa: E402
from qiskit.transpiler import PassManager  # noqa: E402

from qrig.dag import QrigControlEquations  # noqa: E402

try:
    from mqt.bench import BenchmarkLevel, get_benchmark
except ImportError:  # pragma: no cover
    sys.exit("mqt.bench is required: pip install mqt.bench")
try:
    from mqt import qcec
except ImportError:  # pragma: no cover
    sys.exit("mqt.qcec is required: pip install mqt.qcec")

STANDARD = set(get_standard_gate_name_mapping()) | {"measure", "barrier", "reset", "mcx",
                                                    "mcphase", "delay"}

# benchmark -> admissible sizes (MQT Bench constraints)
DEFAULT_SUITE = {
    "grover": [3, 4, 5, 6, 7],
    "qwalk": [3, 4, 5, 6],
    "hrs_cumulative_multiplier": [5, 9],
    "cdkm_ripple_carry_adder": [4, 6, 8],
    "vbe_ripple_carry_adder": [4, 7],
    "full_adder": [4, 6, 8],
    "multiplier": [4, 8],
    "draper_qft_adder": [4, 6, 8],
    "rg_qft_multiplier": [4, 8],
    "modular_adder": [4, 6],
    "qft": [4, 6, 8],
    "qftentangled": [4, 6, 8],
    "qpeexact": [4, 6, 8],
    "ae": [4, 6],
    "dj": [4, 8],
    "bv": [4, 8],
    "ghz": [4, 8],
    "wstate": [4, 8],
    "graphstate": [4, 8],
    "randomcircuit": [4, 6],
}
SCALE_SUITE = {
    "grover": [9, 11],
    "qwalk": [8, 10],
    "multiplier": [12, 16],
    "rg_qft_multiplier": [12],
    "cdkm_ripple_carry_adder": [16, 32],
    "vbe_ripple_carry_adder": [16, 31],
    "draper_qft_adder": [16, 32],
    "qft": [16, 32],
    "qpeexact": [16, 32],
    "dj": [32, 64],
    "bv": [32, 64],
    "ghz": [64, 128],
}
QUICK_SUITE = {"grover": [4, 5], "qwalk": [4], "qft": [4], "cdkm_ripple_carry_adder": [4]}


def expose(qc: QuantumCircuit, max_rounds: int = 20) -> QuantumCircuit:
    """Unroll composite (non-standard, non-controlled) gates, one level at a time."""
    for _ in range(max_rounds):
        names = {inst.operation.name for inst in qc.data
                 if inst.operation.name not in STANDARD
                 and not isinstance(inst.operation, ControlledGate)}
        if not names:
            break
        qc = qc.decompose(gates_to_decompose=list(names))
    return qc


def n_multi_controlled(qc: QuantumCircuit) -> int:
    return sum(1 for inst in qc.data
               if isinstance(inst.operation, ControlledGate)
               and inst.operation.num_ctrl_qubits >= 2)


def cx_count(qc: QuantumCircuit, seed: int = 0) -> int:
    t = transpile(qc, basis_gates=["cx", "u"], optimization_level=3, seed_transpiler=seed)
    return t.count_ops().get("cx", 0), t


def status(res) -> str:
    return str(res.equivalence).split(".")[-1]


def _qcec_child(a, b, conn):
    try:
        conn.send(status(qcec.verify(a, b)))
    except Exception as e:  # pragma: no cover
        conn.send(f"error: {type(e).__name__}: {e}")


def verify(a: QuantumCircuit, b: QuantumCircuit, seconds: float) -> str:
    """``qcec.verify`` with a hard time limit (QCEC runs in a forked child process)."""
    if not seconds:
        return status(qcec.verify(a, b))
    import multiprocessing as mp
    ctx = mp.get_context("fork")
    parent, child = ctx.Pipe(duplex=False)
    proc = ctx.Process(target=_qcec_child, args=(a, b, child))
    proc.start()
    if parent.poll(seconds):
        out = parent.recv()
        proc.join()
        return out
    proc.kill()
    proc.join()
    return "timeout"


def unitary_equal(a: QuantumCircuit, b: QuantumCircuit) -> bool:
    a = a.remove_final_measurements(inplace=False)
    b = b.remove_final_measurements(inplace=False)
    return Operator(a).equiv(Operator(b))


def run_one(name: str, n: int, args) -> dict:
    row = {"benchmark": name, "qubits": n}
    qc = get_benchmark(name, BenchmarkLevel.ALG, n)
    raw = expose(qc)
    row["qubits"] = raw.num_qubits

    t0 = time.perf_counter()
    pm = PassManager([QrigControlEquations(window=args.window, fuel=args.fuel)])
    opt = pm.run(raw)
    row["t_qrig"] = time.perf_counter() - t0
    st = pm.property_set["qrig_stats"]
    row["rules"] = dict(st.rules)
    row["core_gates_in"], row["core_gates_out"] = st.gates_in, st.gates_out

    row["raw_gates"], row["opt_gates"] = raw.size(), opt.size()
    row["raw_depth"], row["opt_depth"] = raw.depth(), opt.depth()
    row["raw_mc"], row["opt_mc"] = n_multi_controlled(raw), n_multi_controlled(opt)

    t0 = time.perf_counter()
    row["cx_qiskit"], _ = cx_count(raw)
    row["cx_qrig_qiskit"], compiled = cx_count(opt)
    row["t_qiskit"] = time.perf_counter() - t0

    t0 = time.perf_counter()
    row["qcec_opt"] = verify(raw, opt, args.qcec_timeout)
    row["qcec_compiled"] = verify(raw, compiled, args.qcec_timeout)
    row["t_qcec"] = time.perf_counter() - t0
    if raw.num_qubits <= args.operator_max:
        row["operator_opt"] = unitary_equal(raw, opt)
    return row


OK = {"equivalent", "equivalent_up_to_global_phase"}
BAD = {"not_equivalent", "probably_not_equivalent"}


def to_markdown(rows) -> str:
    head = ("| benchmark | n | gates raw→qrig | depth raw→qrig | MC gates raw→qrig | "
            "CX Qiskit O3 | CX qrig+O3 | rules id/fuse/cancel/compl/xconj | QCEC qrig | "
            "QCEC compiled | Operator | qrig s |\n|" + "---|" * 12 + "\n")
    lines = []
    for r in rows:
        if "error" in r:
            lines.append(f"| {r['benchmark']} | {r['qubits']} | error: {r['error']} |"
                         + " |" * 8)
            continue
        ru = r["rules"]
        lines.append(
            f"| {r['benchmark']} | {r['qubits']} | {r['raw_gates']}→{r['opt_gates']} | "
            f"{r['raw_depth']}→{r['opt_depth']} | {r['raw_mc']}→{r['opt_mc']} | "
            f"{r['cx_qiskit']} | {r['cx_qrig_qiskit']} | "
            f"{ru['idRem']}/{ru['fuse']}/{ru['cancel']}/{ru['compl']}/{ru['xconj']} | "
            f"{r['qcec_opt']} | {r['qcec_compiled']} | "
            f"{ {True: 'equal', False: 'DIFFERENT', None: '-'}[r.get('operator_opt')] } | "
            f"{r['t_qrig']:.3f} |")
    ok = [r for r in rows if "error" not in r]
    a = sum(r["cx_qiskit"] for r in ok)
    b = sum(r["cx_qrig_qiskit"] for r in ok)
    better = sum(1 for r in ok if r["cx_qrig_qiskit"] < r["cx_qiskit"])
    worse = sum(1 for r in ok if r["cx_qrig_qiskit"] > r["cx_qiskit"])
    lines.append("")
    lines.append(f"Total CX over {len(ok)} circuits: Qiskit O3 {a}, qrig + Qiskit O3 {b} "
                 f"({100 * (a - b) / max(a, 1):.1f}% fewer); fewer CX on {better}, "
                 f"more on {worse}, equal on {len(ok) - better - worse}.")
    return head + "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--benchmarks", nargs="*", default=None)
    ap.add_argument("--sizes", nargs="*", type=int, default=None)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--scale", action="store_true", help="also run the larger sizes")
    ap.add_argument("--window", type=int, default=128)
    ap.add_argument("--fuel", type=int, default=16)
    ap.add_argument("--operator-max", type=int, default=7)
    ap.add_argument("--qcec-timeout", type=float, default=120.0,
                    help="seconds per QCEC check (0 = no limit)")
    ap.add_argument("--out", default=HERE)
    args = ap.parse_args()

    suite = QUICK_SUITE if args.quick else dict(DEFAULT_SUITE)
    if args.scale and not args.quick:
        for b, ns in SCALE_SUITE.items():
            suite[b] = suite.get(b, []) + ns
    if args.benchmarks:
        suite = {b: (args.sizes or DEFAULT_SUITE.get(b, [4])) for b in args.benchmarks}
    elif args.sizes:
        suite = {b: args.sizes for b in suite}

    rows = []
    for name, sizes in suite.items():
        for n in sizes:
            try:
                r = run_one(name, n, args)
            except Exception as e:  # keep going; report the failure
                r = {"benchmark": name, "qubits": n, "error": f"{type(e).__name__}: {e}"}
                traceback.print_exc()
            rows.append(r)
            if "error" in r:
                print(f"{name:28s} n={n:<3d} ERROR {r['error']}")
            else:
                print(f"{name:28s} n={r['qubits']:<3d} gates {r['raw_gates']:>6d} -> "
                      f"{r['opt_gates']:<6d} CX {r['cx_qiskit']:>6d} -> {r['cx_qrig_qiskit']:<6d}"
                      f" QCEC {r['qcec_opt']}/{r['qcec_compiled']}", flush=True)

    md = to_markdown(rows)
    with open(os.path.join(args.out, "mqt_results.md"), "w") as f:
        f.write(md)
    with open(os.path.join(args.out, "mqt_results.json"), "w") as f:
        json.dump(rows, f, indent=1)
    print()
    print(md)
    done = [r for r in rows if "error" not in r]
    bad = [r for r in done if r["qcec_opt"] in BAD or r["qcec_compiled"] in BAD
           or r.get("operator_opt") is False]
    open_ = [r for r in done if r not in bad and
             (r["qcec_opt"] not in OK or r["qcec_compiled"] not in OK)]
    errors = [r for r in rows if "error" in r]
    if bad:
        print("VERIFICATION FAILURES:", [(r["benchmark"], r["qubits"]) for r in bad])
    if open_:
        print("QCEC gave no proof (timeout / probabilistic) for:",
              [(r["benchmark"], r["qubits"], r["qcec_opt"], r["qcec_compiled"]) for r in open_])
    if errors:
        print("errors:", [(r["benchmark"], r["qubits"]) for r in errors])
    if not bad and not open_ and not errors:
        print("All optimised circuits verified equivalent by MQT QCEC.")
    return 1 if bad or errors else 0


if __name__ == "__main__":
    sys.exit(main())
