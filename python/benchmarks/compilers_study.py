#!/usr/bin/env python3
"""qrig in front of three different compilers: Qiskit, TKET and BQSKit.

For every circuit of ``paper_study.py`` (same suites) and every compiler X we compare
*X alone* with *qrig + X* (qrig's verified control-equation pass first). Target: all-to-all
connectivity, gate set {cx, rz, sx, x}, depolarizing noise p2 = 0.3 %, p1 = 0.03 % (the
``depolarizing`` model of ``noise_benchmark.py``).

Compilers
``qiskit``  Qiskit preset pass manager, optimisation level 3, best of 10 seeds (taken from
            ``study/study_results.json``, model ``depolarizing``).
``tket``    pytket: DecomposeBoxes, FullPeepholeOptimise, AutoRebase{CX, Rz, SX, X},
            RemoveRedundancies. FullPeepholeOptimise may end with an implicit wire
            permutation; on an all-to-all device this is a free relabelling of the output
            qubits, so it is not charged (it is taken into account in the equivalence check).
``bqskit``  BQSKit ``compile`` at optimisation level 2 (block partitioning + numerical
            resynthesis, synthesis_epsilon 1e-8) to {CNOT, U3}; the input is first unrolled
            by Qiskit (no optimisation, no ancilla assumptions); U3 gates are translated to
            {rz, sx, x} with Qiskit's one-qubit decomposition only. BQSKit is limited to
            circuits with at most ``--bqskit-max-qubits`` qubits.

Metrics: two-qubit count, depth, compile time (the qrig pass time is reported separately),
equivalence (process infidelity 1 - |tr(U†V)|/2ⁿ against the original benchmark, after
undoing any output relabelling), ESP, and state fidelity F (density matrix, 3 random
product inputs) for circuits that qrig changes.

Usage (from ``python/``)::

    python3 benchmarks/compilers_study.py          # needs pytket pytket-qiskit bqskit
Writes ``study/compilers_results.json``.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import subprocess
import sys
import time
import warnings
from concurrent.futures import ThreadPoolExecutor, as_completed

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("RAYON_NUM_THREADS", "1")
warnings.filterwarnings("ignore")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, HERE)

SEED = 20261009


def unitary_infidelity(a, b) -> float:
    import numpy as np
    from qiskit.quantum_info import Operator
    U, V = Operator(a).data, Operator(b).data
    return float(max(0.0, 1 - abs(np.trace(U.conj().T @ V)) / U.shape[0]))


def single_register(qc):
    """Same circuit on one register ``q`` (converters may reorder multiple registers)."""
    from qiskit import QuantumCircuit
    out = QuantumCircuit(qc.num_qubits, global_phase=qc.global_phase)
    out.compose(qc, qubits=list(range(qc.num_qubits)), inplace=True)
    return out


_TK_OK = {}


def _converts_exactly(op, n) -> bool:
    """Does pytket's Qiskit converter translate this single instruction exactly?"""
    from pytket.extensions.qiskit import qiskit_to_tk, tk_to_qiskit
    from qiskit import QuantumCircuit
    from qiskit.quantum_info import Operator
    key = (op.name, n, getattr(op, "ctrl_state", None),
           tuple(float(p) if isinstance(p, (int, float)) else str(p) for p in op.params))
    if key not in _TK_OK:
        s = QuantumCircuit(n)
        s.append(op, range(n))
        try:
            ok = Operator(tk_to_qiskit(qiskit_to_tk(s))).equiv(Operator(s))
        except Exception:
            ok = False
        _TK_OK[key] = ok
    return _TK_OK[key]


def tk_convertible(qc):
    """Same circuit, with every instruction that pytket's converter rejects or translates
    incorrectly (e.g. ``rccx``, ``mcx_vchain``, controlled composite gates) replaced by
    its Qiskit definition, recursively. Every other instruction is passed through."""
    from qiskit import QuantumCircuit
    out = QuantumCircuit(qc.num_qubits, global_phase=qc.global_phase)

    def add(op, qubits):
        if op.name in ("barrier",) or _converts_exactly(op, len(qubits)):
            out.append(op, qubits)
            return
        d = op.definition
        if d is None:
            raise RuntimeError(f"pytket cannot convert {op.name}")
        out.global_phase += d.global_phase
        for ins in d.data:
            add(ins.operation, [qubits[d.find_bit(q).index] for q in ins.qubits])

    for ins in qc.data:
        add(ins.operation, [qc.find_bit(q).index for q in ins.qubits])
    return out


def run_tket(qc):
    from pytket import OpType
    from pytket.extensions.qiskit import qiskit_to_tk, tk_to_qiskit
    from pytket.passes import AutoRebase, DecomposeBoxes, FullPeepholeOptimise, RemoveRedundancies
    from qiskit import QuantumCircuit
    from qiskit.circuit.library import PermutationGate
    qc = single_register(qc)
    c = qiskit_to_tk(tk_convertible(qc))
    t0 = time.perf_counter()
    DecomposeBoxes().apply(c)
    FullPeepholeOptimise().apply(c)
    AutoRebase({OpType.CX, OpType.Rz, OpType.SX, OpType.X}).apply(c)
    RemoveRedundancies().apply(c)
    dt = time.perf_counter() - t0
    perm = c.implicit_qubit_permutation()
    idx = {q: i for i, q in enumerate(c.qubits)}
    pattern = [0] * c.n_qubits
    for a, b in perm.items():
        pattern[idx[a]] = idx[b]
    out = tk_to_qiskit(c, replace_implicit_swaps=False) if _has_kw() else tk_to_qiskit(c)
    # logical circuit for the equivalence check: compiled circuit, then the relabelling
    check = QuantumCircuit(qc.num_qubits)
    check.compose(out, inplace=True)
    if pattern != list(range(c.n_qubits)):
        # pytket wire a ends on wire perm[a]; Qiskit's PermutationGate(p) sends qubit p[j]->j
        inv = [0] * len(pattern)
        for a, b in enumerate(pattern):
            inv[b] = a
        check.append(PermutationGate(inv), range(qc.num_qubits))
    return out, check, dt, pattern != list(range(c.n_qubits))


def _has_kw():
    import inspect
    from pytket.extensions.qiskit import tk_to_qiskit
    return "replace_implicit_swaps" in inspect.signature(tk_to_qiskit).parameters


def run_bqskit(qc):
    from bqskit import MachineModel, compile
    from bqskit.compiler import Compiler
    from bqskit.ext import bqskit_to_qiskit, qiskit_to_bqskit
    from bqskit.ir.gates import CNOTGate, U3Gate
    from qiskit import QuantumCircuit, transpile
    from qiskit.circuit.library import PermutationGate
    qc = single_register(qc)
    u = transpile(qc, basis_gates=["cx", "u3"], optimization_level=0,
                  qubits_initially_zero=False)
    b = qiskit_to_bqskit(u)
    # BQSKit's attached runtime server always listens on the same port, so BQSKit
    # compilations must not run concurrently; the driver runs them one at a time and
    # gives each one several worker processes instead.
    comp = Compiler(num_workers=int(os.environ.get("QRIG_BQSKIT_WORKERS", "1")))
    try:
        t0 = time.perf_counter()
        model = MachineModel(qc.num_qubits, gate_set={CNOTGate(), U3Gate()})
        res, pi, pf = compile(b, model=model, optimization_level=2, synthesis_epsilon=1e-8,
                              max_synthesis_size=3, compiler=comp, seed=0, with_mapping=True)
        dt = time.perf_counter() - t0
    finally:
        comp.close()
    q = bqskit_to_qiskit(res)
    n = qc.num_qubits
    out = QuantumCircuit(n)
    out.compose(q, inplace=True)
    out = _one_qubit_cleanup(out)
    check = QuantumCircuit(n)
    relabel = list(pi) != list(range(n)) or list(pf) != list(range(n))
    if list(pi) != list(range(n)):
        check.append(PermutationGate(list(pi)), range(n))
    check.compose(out, inplace=True)
    if list(pf) != list(range(n)):
        check.append(PermutationGate(list(pf)).inverse(), range(n))
    return out, check, dt, relabel


def _one_qubit_cleanup(qc):
    from qiskit.transpiler import PassManager
    from qiskit.transpiler.passes import BasisTranslator, Optimize1qGatesDecomposition
    from qiskit.circuit.equivalence_library import SessionEquivalenceLibrary as sel
    basis = ["cx", "rz", "sx", "x"]
    pm = PassManager([BasisTranslator(sel, basis), Optimize1qGatesDecomposition(basis=basis)])
    return pm.run(qc)


# ---------------------------------------------------------------- one job (subprocess)
def one(label: str, compiler: str, variant: str, simulate: bool) -> dict:
    import numpy as np
    import paper_study as ps
    import noise_benchmark as nb
    from qrig.dag import optimize_circuit
    cases = {c["label"]: c for c in ps.mqt_cases() + ps.app_cases() + ps.pattern_cases()}
    qc = ps.build(cases[label]["build"])
    circ = qc
    t_qrig = 0.0
    if variant == "qrig":
        t0 = time.perf_counter()
        circ, _ = optimize_circuit(qc)
        t_qrig = time.perf_counter() - t0
    out, check, dt, relabel = (run_tket if compiler == "tket" else run_bqskit)(circ)
    model = nb.Model("depolarizing")
    c = nb.Compact(out, model)
    res = {"label": label, "compiler": compiler, "variant": variant, "twoq": c.count_2q,
           "oneq": c.count_1q, "depth": c.depth, "compile_time": dt, "t_qrig": t_qrig,
           "ESP": math.exp(c.esp_log), "ESP_log": c.esp_log, "relabelled": relabel}
    if qc.num_qubits <= 10:
        res["infidelity_vs_benchmark"] = unitary_infidelity(check, qc)
    if simulate:
        rng = np.random.default_rng([SEED, sum(map(ord, label))])
        inputs = [[nb.random_qubit_state(rng) for _ in range(qc.num_qubits)] for _ in range(3)]
        a_ = ps.Args(10, 300, 3)
        ev = nb.evaluate(c, model, inputs, [0] * qc.num_qubits, a_, SEED)
        res["F"] = ev["F"]
    return res


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--one", nargs=4, metavar=("LABEL", "COMPILER", "VARIANT", "SIM"))
    ap.add_argument("--workers", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--compilers", nargs="*", default=["tket", "bqskit"])
    ap.add_argument("--bqskit-max-qubits", type=int, default=8)
    ap.add_argument("--bqskit-workers", type=int, default=max(1, (os.cpu_count() or 4) - 2),
                    help="worker processes of each (sequential) BQSKit compilation")
    ap.add_argument("--bqskit-max-2q", type=int, default=1500,
                    help="skip BQSKit when Qiskit alone needs more two-qubit gates")
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--only", nargs="*", default=None)
    ap.add_argument("--resume", action="store_true",
                    help="keep every successful result already in compilers_results.json "
                         "and run only the missing or failed jobs")
    ap.add_argument("--merge", action="store_true",
                    help="keep the results already in compilers_results.json for other circuits")
    args = ap.parse_args()
    if args.one:
        lab, comp, var, sim = args.one
        print("RESULT " + json.dumps(one(lab, comp, var, sim == "1")))
        return 0

    with open(os.path.join(HERE, "study", "study_results.json")) as f:
        study = json.load(f)
    out_path = os.path.join(HERE, "study", "compilers_results.json")
    jobs = []
    for c in study["cases"]:
        lab = c["label"]
        if args.only and lab not in args.only:
            continue
        pc = study["per_case"].get(lab)
        pm = study["per_model"].get(lab, {}).get("depolarizing")
        if not pc or "error" in pc or not pm or "error" in pm:
            continue
        sim = pc["changed"] and pc["qubits"] <= 10
        for comp in args.compilers:
            if comp == "bqskit" and (pc["qubits"] > args.bqskit_max_qubits
                                     or pm["qiskit"]["twoq"] > args.bqskit_max_2q):
                continue
            variants = ("input", "qrig") if pc["changed"] else ("input",)
            for v in variants:
                jobs.append((lab, comp, v, sim, pc["qubits"] ** 2 * pm["qiskit"]["twoq"]))
    jobs.sort(key=lambda j: -j[4] * (20 if j[1] == "bqskit" else 1))
    results = []
    if args.resume and os.path.exists(out_path):
        with open(out_path) as f:
            results = [r for r in json.load(f)["results"] if "error" not in r]
        have = {(r["label"], r["compiler"], r["variant"]) for r in results}
        jobs = [j for j in jobs if (j[0], j[1], j[2]) not in have]
    print(f"{len(jobs)} jobs", flush=True)
    if args.merge and os.path.exists(out_path):
        redo = {(j[0], j[1], j[2]) for j in jobs}
        with open(out_path) as f:
            results = [r for r in json.load(f)["results"]
                       if (r["label"], r["compiler"], r["variant"]) not in redo]
    t_start = time.time()

    def run(job):
        lab, comp, v, sim, _ = job
        cmd = [sys.executable, os.path.abspath(__file__), "--one", lab, comp, v, "1" if sim else "0"]
        env = dict(os.environ, QRIG_BQSKIT_WORKERS=str(args.bqskit_workers))
        try:
            p = subprocess.run(cmd, capture_output=True, text=True, timeout=args.timeout,
                               env=env)
            for line in p.stdout.splitlines():
                if line.startswith("RESULT "):
                    return json.loads(line[7:])
            return {"label": lab, "compiler": comp, "variant": v,
                    "error": (p.stderr or "no result")[-800:]}
        except subprocess.TimeoutExpired:
            return {"label": lab, "compiler": comp, "variant": v,
                    "error": f"timeout after {args.timeout} s"}

    def save():
        import pytket
        import bqskit
        with open(out_path, "w") as f:
            json.dump({"versions": {"pytket": pytket.__version__,
                                    "bqskit": bqskit.__version__},
                       "settings": vars(args), "results": results,
                       "wall_time_s": time.time() - t_start}, f, indent=1)

    # TKET jobs in parallel; BQSKit jobs strictly one at a time (see run_bqskit)
    with ThreadPoolExecutor(args.workers) as ex, ThreadPoolExecutor(1) as ex_bq:
        futs = [(ex_bq if j[1] == "bqskit" else ex).submit(run, j) for j in jobs]
        for i, fut in enumerate(as_completed(futs)):
            r = fut.result()
            results.append(r)
            print(f"[{i + 1}/{len(jobs)} {time.time() - t_start:6.0f}s] {r['label']:30s} "
                  f"{r['compiler']:7s} {r['variant']:6s} "
                  f"{r.get('twoq', '')} {r.get('error', '')[:120]}", flush=True)
            save()
    print("wrote", out_path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
