#!/usr/bin/env python3
"""qrig study for the paper: does a verified control-equation pre-pass help, on which
circuits, by how much, and how robust is the effect?

All targets have **all-to-all connectivity**, so hardware topology (routing / SWAP
insertion) cannot bias the comparison. For every circuit two pipelines are compared:

* **Qiskit**:        Qiskit 2.x preset pass manager, optimisation level 3.
* **qrig + Qiskit**: ``qrig.dag.optimize_circuit`` (rewrites proved sound in Lean)
                     first, then the *same* level-3 pass manager.

Circuit suites (``--suites``)

``mqt``      every unitary MQT Bench benchmark (algorithm level), at up to three sizes
             between 4 and 10 qubits: the neutral, not hand-picked suite.
``app``      controlled-logic application kernels not in MQT Bench (``app_circuits``):
             SAT-oracle Grover, QROM table lookup, incrementer, Qiskit-library Grover,
             comparator, weighted adder, polynomial rotations, state preparation, and an
             Ising Trotter circuit as a control.
``pattern``  the six structured circuits of ``noise_benchmark.synthetic_cases`` that
             contain exactly the patterns the control equations target.

Targets / noise models (all-to-all; from ``noise_benchmark.Model``)

``depolarizing``   {cx, rz, sx, x}, depolarizing gate noise p2 = 0.3 %, p1 = 0.03 %.
``heron_all2all``  {cz, rz, sx, x}, median IBM Heron (FakeTorino) gate errors,
                   durations and T1/T2; idle relaxation (ALAP schedule).
``trapped_ion``    {rxx, rz, sx, x}, assumed trapped-ion parameters, idle relaxation.

Metrics, per circuit and target, for both pipelines

* resources: two-qubit gate count, one-qubit gate count, depth, two-qubit depth;
* fault-tolerant cost: T-count and number of arbitrary-angle rotations after compiling
  to Clifford+T+Rz (Qiskit level 3, basis {cx, h, s, sdg, t, tdg, x, z, rz});
* time: qrig pass time, Qiskit compile time, scheduled execution time of the circuit
  on the device model;
* noise: state fidelity F (3 random product inputs), task success P, estimated success
  probability ESP (density-matrix simulation, circuits up to ``--dm-max`` qubits);
* correctness: exact unitary comparison of the qrig output with the input circuit, and
  agreement of the ideal outputs of both compiled circuits with the benchmark;
* robustness: (i) spread over ``--nseeds`` transpiler seeds (best, median, worst; share
  of seeds where qrig is no worse); (ii) noise-strength sweep (Heron model with all
  error rates scaled by 1/4 ... 4); (iii) noise type (gate errors only, idle
  decoherence only, coherent over-rotation errors).

Usage (from ``python/``)::

    python3 benchmarks/paper_study.py               # everything (~1-2 h on 8 cores)
    python3 benchmarks/paper_study.py --quick       # smoke test
    python3 benchmarks/paper_study.py --robust-only # rerun only the robustness part

Writes ``study/study_results.json``; ``make_report.py`` turns it into the report.
"""
from __future__ import annotations

import argparse
import json
import math
import multiprocessing as mp
import os
import platform
import statistics
import sys
import time
import traceback
import warnings

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("RAYON_NUM_THREADS", "1")
warnings.filterwarnings("ignore")

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, HERE)

import numpy as np  # noqa: E402
import qiskit  # noqa: E402
import qiskit_aer  # noqa: E402
from qiskit import QuantumCircuit, transpile  # noqa: E402
from qiskit.quantum_info import Operator, Statevector  # noqa: E402
from qiskit_aer.noise import (NoiseModel, coherent_unitary_error,  # noqa: E402
                              depolarizing_error)

import qrig  # noqa: E402
from qrig.dag import optimize_circuit  # noqa: E402
import noise_benchmark as nb  # noqa: E402

SEED = 20261009
MODELS = ("depolarizing", "heron_all2all", "trapped_ion")
OUT_DIR = os.path.join(HERE, "study")

# MQT Bench benchmarks that are not unitary (mid-circuit measurement / reset) or have
# no instance in the size range
MQT_EXCLUDE = {"dynamic_qft", "ghz_dynamic", "iqpe", "shor", "seven_qubit_steane_code",
               "shors_nine_qubit_code"}


# ============================================================================ suites
def mqt_cases(lo=4, hi=10, per=3):
    from mqt.bench import BenchmarkLevel, get_benchmark
    from mqt.bench.benchmarks import get_available_benchmark_names
    out = []
    for name in get_available_benchmark_names():
        if name in MQT_EXCLUDE:
            continue
        sizes = []
        for n in range(lo, hi + 1):
            try:
                qc = get_benchmark(name, BenchmarkLevel.ALG, n)
            except Exception:
                continue
            if qc.num_qubits == n:
                sizes.append(n)
        if not sizes:
            continue
        pick = sorted({sizes[0], sizes[len(sizes) // 2], sizes[-1]})[:per]
        for n in pick:
            out.append({"label": f"{name} {n}", "family": name, "suite": "mqt",
                        "build": ("mqt", name, n)})
    return out


def app_cases():
    from app_circuits import APP_CASES
    return [{"label": f"{fam} {sz}", "family": fam, "suite": "app",
             "build": ("app", i)} for i, (fam, sz, _) in enumerate(APP_CASES)]


def pattern_cases():
    return [{"label": name, "family": name.split(" (")[0].split(" x")[0], "suite": "pattern",
             "build": ("pattern", i)} for i, (name, _) in enumerate(nb.synthetic_cases())]


def build(spec) -> QuantumCircuit:
    kind = spec[0]
    if kind == "mqt":
        return nb.mqt_circuit(spec[1], spec[2])
    if kind == "app":
        from app_circuits import APP_CASES
        return APP_CASES[spec[1]][2]()
    if kind == "pattern":
        return nb.synthetic_cases()[spec[1]][1]
    raise ValueError(spec)


# ============================================================================ helpers
class Args:          # what noise_benchmark.evaluate needs
    def __init__(self, dm_max, shots, inputs):
        self.dm_max, self.shots, self.inputs = dm_max, shots, inputs


def two_q_depth(t: QuantumCircuit) -> int:
    return t.depth(filter_function=lambda i: i.operation.num_qubits == 2
                   and i.operation.name not in ("barrier",))


def ft_cost(qc: QuantumCircuit) -> dict:
    """T-count and arbitrary rotations after Clifford+T+Rz compilation (level 3)."""
    t0 = time.perf_counter()
    t = transpile(qc, basis_gates=["cx", "h", "s", "sdg", "t", "tdg", "x", "z", "rz"],
                  optimization_level=3, seed_transpiler=0, qubits_initially_zero=False)
    tc = rot = 0
    for inst in t.data:
        name = inst.operation.name
        if name in ("t", "tdg"):
            tc += 1
        elif name == "rz":
            a = float(inst.operation.params[0]) / (math.pi / 4)
            k = round(a)
            if abs(a - k) < 1e-9:
                tc += k % 2
            else:
                rot += 1
    return {"t_count": tc, "rotations": rot, "cx": t.count_ops().get("cx", 0),
            "time": time.perf_counter() - t0}


def is_search(label: str) -> bool:
    return "grover" in label


def compile_all_seeds(qc: QuantumCircuit, model, seeds):
    """Compile with every seed; return best (by ESP) compiled circuit + per-seed data."""
    per, best = [], None
    for s in seeds:
        t0 = time.perf_counter()
        t = model.pass_manager(s, qc.num_qubits).run(qc)
        dt = time.perf_counter() - t0
        c = nb.Compact(t, model)
        per.append({"seed": s, "twoq": c.count_2q, "depth": c.depth, "esp_log": c.esp_log,
                    "time": dt})
        key = (-c.esp_log, c.count_2q, c.depth)
        if best is None or key < best[0]:
            best = (key, t, c)
    return best[1], best[2], per


def seed_summary(per):
    xs = [p["twoq"] for p in per]
    return {"min": min(xs), "median": statistics.median(xs), "max": max(xs),
            "all": xs, "compile_time_median": statistics.median(p["time"] for p in per)}


# ============================================================================ tasks
def case_task(case, args_d):
    """Model-independent part: qrig pass, exact equivalence, FT cost."""
    try:
        qc = build(case["build"])
        times = []
        for _ in range(3):
            t0 = time.perf_counter()
            opt, stats = optimize_circuit(qc)
            times.append(time.perf_counter() - t0)
        changed = not (opt == qc)
        res = {"label": case["label"], "qubits": qc.num_qubits, "gates_in": qc.size(),
               "gates_qrig": opt.size(), "rules": dict(stats.rules),
               "rewrites": int(sum(stats.rules.values())), "changed": changed,
               "t_qrig": statistics.median(times)}
        if qc.num_qubits <= args_d["equiv_max"]:
            d = float(np.max(np.abs(Operator(qc).data - Operator(opt).data)))
            res["equiv"] = {"method": "exact unitary (Operator)", "max_abs_diff": d,
                            "equal": d < 1e-8}
        else:
            res["equiv"] = {"method": "not checked here (too large)", "equal": None}
        if args_d["ft"]:
            res["ft_qiskit"] = ft_cost(qc)
            res["ft_qrig"] = ft_cost(opt) if changed else dict(res["ft_qiskit"])
        return res
    except Exception as e:  # pragma: no cover
        return {"label": case["label"], "error": f"{type(e).__name__}: {e}",
                "trace": traceback.format_exc()}


def model_task(case, model_name, args_d):
    """Compile both pipelines for one target, simulate under its noise model."""
    try:
        qc = build(case["build"])
        opt, _ = optimize_circuit(qc)
        changed = not (opt == qc)
        model = nb.Model(model_name, args_d["p2"])
        seeds = list(range(args_d["nseeds"]))
        n = qc.num_qubits
        rng = np.random.default_rng([SEED, sum(map(ord, case["label"]))])
        inputs = [[nb.random_qubit_state(rng) for _ in range(n)]
                  for _ in range(args_d["inputs"])]
        task = [0] * n if is_search(case["label"]) else [int(rng.integers(2)) for _ in range(n)]
        sim = n <= args_d["dm_max"]
        a_ = Args(args_d["dm_max"], 300, args_d["inputs"])
        out = {"label": case["label"], "model": model_name, "simulated": sim}
        variants = (("qiskit", qc), ("qrig", opt)) if changed else (("qiskit", qc),)
        compiled = {}
        for vname, circ in variants:
            t, c, per = compile_all_seeds(circ, model, seeds)
            v = {"twoq": c.count_2q, "oneq": c.count_1q, "depth": c.depth,
                 "twoq_depth": two_q_depth(c.ideal), "duration_us": c.duration * 1e6,
                 "ESP": math.exp(c.esp_log), "ESP_log": c.esp_log,
                 "seeds": seed_summary(per)}
            if sim:
                ev = nb.evaluate(c, model, inputs, task, a_, SEED)
                v.update({"F": ev["F"], "P": ev["P"]})
                v["_p"] = ev["_p_ideal"]
            out[vname] = v
            compiled[vname] = t
        if not changed:
            out["qrig"] = json.loads(json.dumps({k: v for k, v in out["qiskit"].items()
                                                 if k != "_p"}))
            if "_p" in out["qiskit"]:
                out["qrig"]["_p"] = out["qiskit"]["_p"]
            out["unchanged"] = True
        if sim:
            pa, pb = out["qiskit"].pop("_p"), out["qrig"].pop("_p")
            out["ideal_outputs_agree"] = bool(np.allclose(pa, pb, atol=1e-6))
            sv = Statevector.from_label("".join(str(b) for b in reversed(task)))
            ref = sv.evolve(qc).probabilities()
            out["matches_benchmark"] = bool(np.allclose(pa, ref, atol=1e-6))
        # paired seed comparison
        qa, qb = out["qiskit"]["seeds"]["all"], out["qrig"]["seeds"]["all"]
        out["seed_no_worse"] = sum(b <= a for a, b in zip(qa, qb)) / len(qa)
        out["seed_better"] = sum(b < a for a, b in zip(qa, qb)) / len(qa)
        return out, compiled if args_d["keep_compiled"] else None
    except Exception as e:  # pragma: no cover
        return {"label": case["label"], "model": model_name,
                "error": f"{type(e).__name__}: {e}", "trace": traceback.format_exc()}, None


# ---------------------------------------------------------------- robustness variants
class VariantModel:
    """Heron all-to-all physics with modified noise: scaled, gates-only, idle-only or
    coherent over-rotations. Durations (hence the schedule) are unchanged."""

    def __init__(self, base, kind: str, scale: float = 1.0, eps2=0.1, eps1=0.02):
        self.base, self.kind, self.scale, self.eps2, self.eps1 = base, kind, scale, eps2, eps1
        pr = base.params
        self.dt = base.dt
        self.twoq = base.twoq
        idle = kind in ("scaled", "idle_only", "coherent+idle")
        gates = kind in ("scaled", "gates_only")
        s = scale if kind == "scaled" else 1.0
        self.p2 = pr["p2"] * s if gates else 0.0
        self.p1 = pr["p1"] * s if gates else 0.0
        big = 1e9
        self._t1 = pr["t1"] / s if idle else big
        self._t2 = min(pr["t2"], 2 * pr["t1"]) / s if idle else big
        self.t1 = [self._t1] * 256
        self.t2 = [min(self._t2, 2 * self._t1)] * 256

    def target_for(self, n):
        t = self.base.target_for(n)
        self.t1 = [self._t1] * n
        self.t2 = [min(self._t2, 2 * self._t1)] * n
        return t

    def gate_error(self, name, phys):
        return self.p2 if name in nb.TWO_Q else self.p1 if name in nb.ONE_Q else 0.0

    def noise_model(self, compact):
        nm = NoiseModel(basis_gates=["cx", "cz", "rxx", "rz", "sx", "x"])
        if self.kind.startswith("coherent"):
            from qiskit.circuit.library import RXGate, RZZGate
            nm.add_all_qubit_quantum_error(
                coherent_unitary_error(Operator(RZZGate(self.eps2)).data), [self.twoq])
            nm.add_all_qubit_quantum_error(
                coherent_unitary_error(Operator(RXGate(self.eps1)).data), list(nb.ONE_Q))
            return nm
        if self.p1 > 0:
            nm.add_all_qubit_quantum_error(depolarizing_error(self.p1, 1), list(nb.ONE_Q))
        if self.p2 > 0:
            nm.add_all_qubit_quantum_error(depolarizing_error(self.p2, 2), [self.twoq])
        return nm


ROBUST_VARIANTS = ([("scaled", s) for s in (0.25, 0.5, 1.0, 2.0, 4.0)]
                   + [("gates_only", 1.0), ("idle_only", 1.0), ("coherent", 1.0),
                      ("coherent+idle", 1.0)])


def robust_task(case, args_d):
    try:
        qc = build(case["build"])
        opt, _ = optimize_circuit(qc)
        base = nb.Model("heron_all2all")
        seeds = list(range(args_d["nseeds"]))
        tq, _, _ = compile_all_seeds(qc, base, seeds)
        tr, _, _ = compile_all_seeds(opt, base, seeds)
        n = qc.num_qubits
        rng = np.random.default_rng([SEED + 7, sum(map(ord, case["label"]))])
        inputs = [[nb.random_qubit_state(rng) for _ in range(n)] for _ in range(2)]
        task = [0] * n if is_search(case["label"]) else [int(rng.integers(2)) for _ in range(n)]
        a_ = Args(args_d["dm_max"], 300, 2)
        rows = []
        for kind, s in ROBUST_VARIANTS:
            vm = VariantModel(base, kind, s)
            r = {"kind": kind, "scale": s}
            for vname, t in (("qiskit", tq), ("qrig", tr)):
                c = nb.Compact(t, vm)
                ev = nb.evaluate(c, vm, inputs, task, a_, SEED)
                r[vname] = {"F": ev["F"], "P": ev["P"], "twoq": c.count_2q}
            rows.append(r)
        return {"label": case["label"], "rows": rows}
    except Exception as e:  # pragma: no cover
        return {"label": case["label"], "error": f"{type(e).__name__}: {e}",
                "trace": traceback.format_exc()}


def _star(f_args):
    f, a = f_args[0], f_args[1:]
    return f(*a)


# ============================================================================ main
def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--suites", nargs="*", default=["mqt", "app", "pattern"])
    ap.add_argument("--models", nargs="*", default=list(MODELS))
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--nseeds", type=int, default=10)
    ap.add_argument("--inputs", type=int, default=3)
    ap.add_argument("--dm-max", type=int, default=10)
    ap.add_argument("--equiv-max", type=int, default=10)
    ap.add_argument("--p2", type=float, default=3e-3)
    ap.add_argument("--workers", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--no-ft", action="store_true")
    ap.add_argument("--robust-only", action="store_true")
    ap.add_argument("--robust-max", type=int, default=8,
                    help="largest circuit (qubits) in the robustness study")
    ap.add_argument("--missing-only", action="store_true",
                    help="keep existing results; run only circuits (and robustness "
                         "entries) not yet present in study_results.json")
    ap.add_argument("--out", default=OUT_DIR)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    path = os.path.join(args.out, "study_results.json")

    cases = []
    if "mqt" in args.suites:
        cases += mqt_cases(per=1 if args.quick else 3, hi=6 if args.quick else 10)
    if "app" in args.suites:
        cases += app_cases()[:4] if args.quick else app_cases()
    if "pattern" in args.suites:
        cases += pattern_cases()[:2] if args.quick else pattern_cases()
    if args.quick:
        args.nseeds = min(args.nseeds, 3)
    args_d = {"p2": args.p2, "nseeds": args.nseeds, "inputs": args.inputs,
              "dm_max": args.dm_max, "equiv_max": args.equiv_max, "ft": not args.no_ft,
              "keep_compiled": False}
    print(f"{len(cases)} circuits, models {args.models}, {args.workers} workers", flush=True)

    data = {}
    if os.path.exists(path):
        with open(path) as f:
            data = json.load(f)

    def save():
        data.update({"versions": {"qiskit": qiskit.__version__, "aer": qiskit_aer.__version__,
                                  "qrig": qrig.__version__, "python": platform.python_version(),
                                  "machine": platform.machine(), "cpus": os.cpu_count()},
                     "settings": {k: v for k, v in args_d.items() if k != "keep_compiled"},
                     "model_info": {m: nb.Model(m, args.p2).describe() for m in MODELS},
                     "cases": [{k: v for k, v in c.items() if k != "build"} for c in cases]})
        with open(path, "w") as f:
            json.dump(data, f, indent=1, default=float)

    ctx = mp.get_context("spawn")
    t_start = time.time()
    done = set(data.get("per_case", {})) if args.missing_only else set()
    if args.missing_only:
        print(f"missing-only: {len([c for c in cases if c['label'] not in done])} new circuits",
              flush=True)
    if not args.robust_only:
        todo = [c for c in cases if c["label"] not in done]
        jobs = [(case_task, c, args_d) for c in todo]
        jobs += [(model_task, c, m, args_d) for c in todo for m in args.models]
        # longest first: big circuits / ion model
        jobs.sort(key=lambda j: -(build_size(j[1]) * (2 if len(j) == 4 else 1)))
        if not args.missing_only:
            data["per_case"], data["per_model"] = {}, {}
        data.setdefault("per_case", {})
        data.setdefault("per_model", {})
        with ctx.Pool(args.workers, maxtasksperchild=4) as pool:
            for i, r in enumerate(pool.imap_unordered(_star, jobs)):
                if isinstance(r, tuple):
                    r = r[0]
                    data["per_model"].setdefault(r["label"], {})[r["model"]] = r
                    tag = r["model"]
                else:
                    data["per_case"][r["label"]] = r
                    tag = "case"
                err = r.get("error", "")
                print(f"[{i + 1}/{len(jobs)} {time.time() - t_start:6.0f}s] {r['label']:32s} "
                      f"{tag:13s} {err}", flush=True)
                if (i + 1) % 10 == 0:
                    save()
        save()

    # robustness subset: circuits where qrig changes the Heron 2q count, <= robust_max
    sel = []
    for c in cases:
        pm = data.get("per_model", {}).get(c["label"], {}).get("heron_all2all")
        if not pm or "error" in pm:
            continue
        if pm.get("unchanged"):
            continue
        nq = data["per_case"][c["label"]]["qubits"]
        if nq <= args.robust_max and pm["qrig"]["twoq"] != pm["qiskit"]["twoq"]:
            sel.append(c)
    if args.missing_only:
        sel = [c for c in sel if c["label"] not in data.get("robust", {})]
    else:
        data["robust"] = {}
    data.setdefault("robust", {})
    print(f"robustness study on {len(sel)} circuits: {[c['label'] for c in sel]}", flush=True)
    with ctx.Pool(args.workers, maxtasksperchild=2) as pool:
        for i, r in enumerate(pool.imap_unordered(_star, [(robust_task, c, args_d) for c in sel])):
            data["robust"][r["label"]] = r
            print(f"[robust {i + 1}/{len(sel)} {time.time() - t_start:6.0f}s] {r['label']} "
                  f"{r.get('error', '')}", flush=True)
    data["robust_variants"] = ROBUST_VARIANTS
    if args.missing_only:
        data["wall_time_s"] = data.get("wall_time_s", 0.0) + time.time() - t_start
    else:
        data["wall_time_s"] = time.time() - t_start
    save()
    print("wrote", path)
    return 0


_SIZE_CACHE = {}


def build_size(case):
    lab = case["label"]
    if lab not in _SIZE_CACHE:
        try:
            qc = build(case["build"])
            _SIZE_CACHE[lab] = qc.num_qubits ** 2 * max(qc.size(), 1)
        except Exception:
            _SIZE_CACHE[lab] = 0
    return _SIZE_CACHE[lab]


if __name__ == "__main__":
    sys.exit(main())
