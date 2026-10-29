"""Before/after benchmark: what does qrig add to a conventional Qiskit workflow?

Conventional: Qiskit's preset level-3 pass manager targeting the basis {cx, u}
              (what ``transpile(qc, basis_gates=["cx", "u"], optimization_level=3)`` does).
With qrig:    the same pass manager, with qrig's ``QrigOptimize`` pass added as a
              *pre-pass* (``pre_init`` stage), so qrig rewrites the high-level circuit
              with the control equations and Qiskit's optimiser then does the rest.

Both pipelines use ``qubits_initially_zero=False``: circuits are compiled as
unitaries (reusable subroutines). With Qiskit's default (``True``) Qiskit may use idle
qubits as clean ancillas, and the result is then only correct when those qubits start
in |0>, so it cannot be checked as a unitary. Every compiled circuit is checked against
the original with Qiskit's ``Operator`` before its gates are counted. Run::

    cd python && python3 benchmarks/benchmark.py

Outputs (next to this script): ``benchmark.png``, ``results.json``, ``results.md``.
"""
from __future__ import annotations

import json
import os
import platform
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

import matplotlib  # noqa: E402

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402
import qiskit  # noqa: E402
from qiskit import QuantumCircuit  # noqa: E402
from qiskit.circuit.library import UnitaryGate, grover_operator  # noqa: E402
from qiskit.quantum_info import Operator  # noqa: E402
from qiskit.transpiler import PassManager  # noqa: E402
from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager  # noqa: E402

import qrig  # noqa: E402
from qrig import H, T, V, Vdg, controlled_on  # noqa: E402
from qrig.qiskit_bridge import QrigOptimize, optimize_qiskit  # noqa: E402

SEED = 20260925
BASIS = ["cx", "u"]


# ----------------------------------------------------------------------------- pipelines
def conventional_pm():
    return generate_preset_pass_manager(optimization_level=3, basis_gates=BASIS,
                                        seed_transpiler=0, qubits_initially_zero=False)


def qrig_prepass_pm():
    pm = generate_preset_pass_manager(optimization_level=3, basis_gates=BASIS,
                                      seed_transpiler=0, qubits_initially_zero=False)
    # run qrig first, then whatever Qiskit already had in its pre_init stage
    old = list(pm.pre_init.to_flow_controller().tasks) if pm.pre_init is not None else []
    pm.pre_init = PassManager([QrigOptimize()] + old)
    return pm


CONVENTIONAL = conventional_pm()
WITH_QRIG = qrig_prepass_pm()


def metrics(t: QuantumCircuit) -> dict:
    return {"cx": t.count_ops().get("cx", 0), "gates": t.size(), "depth": t.depth()}


def same_unitary(original: QuantumCircuit, compiled: QuantumCircuit) -> bool:
    """Exact (not up to phase) equality; ``from_circuit`` undoes the final qubit
    permutation Qiskit records when it absorbs SWAP gates into the layout."""
    return np.allclose(Operator(original).data, Operator.from_circuit(compiled).data,
                       atol=1e-8)


def before_after(qc: QuantumCircuit) -> tuple[dict, dict]:
    """(conventional, qrig pre-pass + conventional) metrics for one circuit."""
    t0 = CONVENTIONAL.run(qc)
    t1 = WITH_QRIG.run(qc)
    if not (same_unitary(qc, t0) and same_unitary(qc, t1)):
        raise AssertionError("a compiled circuit differs from the original")
    return metrics(t0), metrics(t1)


# ----------------------------------------------------------------------------- workloads
_NAMED = {"h": qrig.H, "s": qrig.S, "sdg": qrig.Sdg, "t": qrig.T, "tdg": qrig.Tdg,
          "z": qrig.Z, "y": qrig.Y, "sx": qrig.V, "sxdg": qrig.Vdg, "x": qrig.X}


def random_controlled_circuit(rng: random.Random, n: int, length: int) -> qrig.Circuit:
    """Random Clifford+T gates with 0-3 controls of random polarity, plus swaps."""
    parts = []
    for _ in range(length):
        if rng.random() < 0.1:
            a, b = rng.sample(range(n), 2)
            parts.append(qrig.on_wires(qrig.SWAP, [a, b], n))
            continue
        g = _NAMED[rng.choice(list(_NAMED))]
        k = rng.randint(0, min(3, n - 1))
        wires = rng.sample(range(n), k + 1)
        ctrls = [(w, rng.random() < 0.5) for w in wires[:k]]
        parts.append(controlled_on(g, ctrls, [wires[k]], n))
    return qrig.seq(*parts)


def multiplexer(rng: random.Random, k: int) -> qrig.Circuit:
    """A uniformly controlled gate: one branch per control pattern (Gray-code order),
    each branch drawn from {H, H, H, T}, so neighbouring branches often coincide."""
    n = k + 1
    parts = []
    for g in qrig.gray_code(k):
        u = rng.choice([H, H, H, T])
        ctrls = [(j, bool((g >> (k - 1 - j)) & 1)) for j in range(k)]
        parts.append(controlled_on(u, ctrls, [k], n))
    return qrig.seq(*parts)


def grover(n: int, iterations: int = 2) -> QuantumCircuit:
    oracle = QuantumCircuit(n)
    oracle.h(n - 1)
    oracle.mcx(list(range(n - 1)), n - 1)
    oracle.h(n - 1)
    g = grover_operator(oracle)
    qc = QuantumCircuit(n)
    qc.h(range(n))
    for _ in range(iterations):
        qc.compose(g, inplace=True)
    return qc


def mean_metrics(pairs):
    keys = pairs[0][0].keys()
    before = {k: float(np.mean([p[0][k] for p in pairs])) for k in keys}
    after = {k: float(np.mean([p[1][k] for p in pairs])) for k in keys}
    return before, after


# ----------------------------------------------------------------------------- experiments
def exp_families() -> list:
    """Panel A: fixed-size workloads."""
    rng = random.Random(SEED)
    rows = []

    def add(name, why, pairs):
        b, a = mean_metrics(pairs)
        rows.append({"family": name, "note": why, "samples": len(pairs),
                     "before": b, "after": a})
        print(f"  {name:45s} cx {b['cx']:8.1f} -> {a['cx']:8.1f}", flush=True)

    add("Random controlled Clifford+T (4q, 40 gates)",
        "unstructured: little for qrig to find",
        [before_after(random_controlled_circuit(rng, 4, 40).to_qiskit()) for _ in range(10)])
    add("Grover (Qiskit library), 5q, 2 iterations",
        "no adjacent controlled gates qrig can merge",
        [before_after(grover(5))])
    add("Multiplexer, 4 controls, repeated branches",
        "equation (e) C0(f);C1(f) = id+f, and (a)",
        [before_after(multiplexer(rng, 4).to_qiskit()) for _ in range(5)])
    ctrl3 = [(0, True), (1, True), (2, True)]
    add("Repeated controlled phase C^3(T) x4",
        "equation (a) C(f);C(g) = C(f;g), T^4 = Z",
        [before_after(qrig.seq(*[controlled_on(T, ctrl3, [3], 4)] * 4).to_qiskit())])
    add("Compute/uncompute U;U^-1 (4q, 30 gates)",
        "stack-wise cancellation of controlled gates",
        [before_after((c >> qrig.dagger(c)).to_qiskit())
         for c in (random_controlled_circuit(rng, 4, 30) for _ in range(5))])
    add("C^3(H);C^3(V);C^3(V^-1);C^3(H)",
        "equation (a) + one-qubit gate fusion",
        [before_after(qrig.seq(controlled_on(H, ctrl3, [3], 4), controlled_on(V, ctrl3, [3], 4),
                               controlled_on(Vdg, ctrl3, [3], 4),
                               controlled_on(H, ctrl3, [3], 4)).to_qiskit())])
    return rows


def exp_multiplexer_scaling() -> list:
    rng = random.Random(SEED + 1)
    rows = []
    for k in range(2, 7):
        pairs = [before_after(multiplexer(rng, k).to_qiskit()) for _ in range(3)]
        b, a = mean_metrics(pairs)
        rows.append({"controls": k, "before": b, "after": a})
        print(f"  k={k}: cx {b['cx']:.1f} -> {a['cx']:.1f}", flush=True)
    return rows


def exp_synthesis() -> list:
    """Panel C: reversible (permutation) synthesis. Conventional = Qiskit's generic
    unitary synthesis of the permutation matrix; qrig = Gray-code synthesis (Thm 9),
    both compiled with the conventional level-3 pipeline."""
    rng = random.Random(SEED + 2)
    rows = []
    for n in range(2, 6):
        res = {"qiskit": [], "qrig": [], "qrig_simplified": []}
        for _ in range(3):
            p = list(range(2 ** n))
            rng.shuffle(p)
            m = np.zeros((2 ** n, 2 ** n))
            for i, j in enumerate(p):
                m[j, i] = 1
            base = QuantumCircuit(n)
            base.append(UnitaryGate(m), range(n))
            c = qrig.synthesize_permutation(p)
            variants = {"qiskit": base, "qrig": c.to_qiskit(),
                        "qrig_simplified": qrig.simplify(c).to_qiskit()}
            for key, qc in variants.items():
                t = CONVENTIONAL.run(qc)
                assert np.allclose(Operator.from_circuit(t).data, m, atol=1e-8)
                res[key].append(metrics(t)["cx"])
        row = {"qubits": n, **{k: float(np.mean(v)) for k, v in res.items()}}
        rows.append(row)
        print(f"  n={n}: {row}", flush=True)
    return rows


def exp_runtime() -> list:
    """Panel D: wall-clock cost of qrig's exact operations vs Qiskit's."""
    rng = random.Random(SEED + 3)
    rows = []
    for n in range(2, 7):
        c = random_controlled_circuit(rng, n, 100)
        d = qrig.simplify(c)
        qc, qd = c.to_qiskit(), d.to_qiskit()
        t0 = time.perf_counter(); ok1 = qrig.equivalent(c, d); t1 = time.perf_counter()
        ok2 = Operator(qc).equiv(Operator(qd)); t2 = time.perf_counter()
        optimize_qiskit(qc); t3 = time.perf_counter()
        CONVENTIONAL.run(qc); t4 = time.perf_counter()
        assert ok1 and ok2
        rows.append({"qubits": n, "qrig_equiv_s": t1 - t0, "qiskit_equiv_s": t2 - t1,
                     "qrig_optimize_s": t3 - t2, "qiskit_transpile_s": t4 - t3})
        print(f"  n={n}: " + ", ".join(f"{k}={v:.3f}" for k, v in rows[-1].items()
                                       if k != "qubits"), flush=True)
    return rows


# ----------------------------------------------------------------------------- output
def plot(fam, mux, syn, rt, path):
    fig, axes = plt.subplots(2, 2, figsize=(16, 11))
    c_before, c_after = "#9aa5b1", "#2b7bba"

    ax = axes[0, 0]
    labels = [r["family"] for r in fam]
    b = [r["before"]["cx"] for r in fam]
    a = [r["after"]["cx"] for r in fam]
    y = np.arange(len(fam))
    ax.barh(y - 0.2, b, 0.4, color=c_before, label="Qiskit level 3 alone")
    ax.barh(y + 0.2, a, 0.4, color=c_after, label="qrig pre-pass + Qiskit level 3")
    for i, (bb, aa) in enumerate(zip(b, a)):
        red = 0 if bb == 0 else 100 * (bb - aa) / bb
        if red >= 0.5:
            verdict = f"{red:.0f}% fewer"
        elif red <= -0.5:
            verdict = f"{-red:.0f}% more"
        else:
            verdict = f"{red:+.1f}%: no real change"
        txt = f"{bb:.1f} → {aa:.1f}  ({verdict})"
        ax.text(max(bb, aa) + max(b) * 0.02, i, txt, va="center", fontsize=9)
    ax.set_yticks(y)
    ax.set_yticklabels(labels, fontsize=9)
    ax.invert_yaxis()
    ax.set_xlabel("CNOT count after compiling to {CX, U}  (lower is better)")
    ax.set_xlim(0, max(b + a) * 1.55)
    ax.set_title("A. Before / after adding qrig as a pre-pass")
    ax.legend(loc="lower right", fontsize=9)

    ax = axes[0, 1]
    ks = [r["controls"] for r in mux]
    ax.plot(ks, [r["before"]["cx"] for r in mux], "o-", color=c_before,
            label="Qiskit level 3 alone")
    ax.plot(ks, [r["after"]["cx"] for r in mux], "o-", color=c_after,
            label="qrig pre-pass + Qiskit level 3")
    ax.set_xticks(ks)
    ax.set_yscale("log")
    ax.set_xlabel("control qubits k  (2^k branches)")
    ax.set_ylabel("CNOT count (log scale)")
    ax.set_title("B. Multiplexer with repeated branches: scaling")
    ax.legend()
    ax.grid(alpha=0.3)

    ax = axes[1, 0]
    ns = [r["qubits"] for r in syn]
    ax.plot(ns, [r["qiskit"] for r in syn], "o-", color=c_before,
            label="Qiskit generic synthesis of the permutation matrix")
    ax.plot(ns, [r["qrig"] for r in syn], "s-", color="#d9534f",
            label="qrig Gray-code synthesis (Theorem 9)")
    ax.plot(ns, [r["qrig_simplified"] for r in syn], "^--", color="#f0ad4e",
            label="qrig synthesis + qrig optimiser")
    ax.set_yscale("log")
    ax.set_xticks(ns)
    ax.set_xlabel("qubits (random permutation of the 2^n basis states)")
    ax.set_ylabel("CNOT count (log scale)")
    ax.set_title("C. Reversible synthesis: qrig is NOT competitive here")
    ax.legend(fontsize=9)
    ax.grid(alpha=0.3)

    ax = axes[1, 1]
    ns = [r["qubits"] for r in rt]
    ax.plot(ns, [r["qrig_equiv_s"] for r in rt], "s-", color="#d9534f",
            label="qrig.equivalent (exact arithmetic)")
    ax.plot(ns, [r["qiskit_equiv_s"] for r in rt], "o-", color=c_before,
            label="Qiskit Operator.equiv (floating point)")
    ax.plot(ns, [r["qrig_optimize_s"] for r in rt], "^-", color=c_after,
            label="qrig optimiser pass")
    ax.plot(ns, [r["qiskit_transpile_s"] for r in rt], "v-", color="#555555",
            label="Qiskit level-3 transpile")
    ax.set_yscale("log")
    ax.set_xticks(ns)
    ax.set_xlabel("qubits (random 100-gate controlled circuit)")
    ax.set_ylabel("wall-clock seconds (log scale)")
    ax.set_title("D. Cost: the pre-pass is cheap, exact equivalence is not")
    ax.legend(fontsize=9)
    ax.grid(alpha=0.3)

    fig.suptitle(f"qrig {qrig.__version__} vs Qiskit {qiskit.__version__}; every compiled "
                 "circuit checked equal to its input", fontsize=13)
    fig.tight_layout(rect=(0, 0, 1, 0.96))
    fig.savefig(path, dpi=130)


def write_markdown(fam, mux, syn, rt, path):
    L = ["# qrig benchmark results", "",
         f"Qiskit {qiskit.__version__}, qrig {qrig.__version__} (backend "
         f"`{qrig.backend().name}`), Python {platform.python_version()}, seed {SEED}.", "",
         "*Before*: Qiskit's preset level-3 pass manager, basis {cx, u}, "
         "`qubits_initially_zero=False` (circuits compiled as unitaries). "
         "*After*: the same pass manager with `QrigOptimize` as a pre-pass (`pre_init` stage). "
         "Values are means over the samples. Generated by `benchmarks/benchmark.py`.", "",
         "## A. Workloads", "",
         "| workload | why | samples | CX before | CX after | gates before | gates after | depth before | depth after |",
         "|---|---|---|---|---|---|---|---|---|"]
    for r in fam:
        b, a = r["before"], r["after"]
        L.append(f"| {r['family']} | {r['note']} | {r['samples']} | {b['cx']:.1f} | {a['cx']:.1f} | "
                 f"{b['gates']:.1f} | {a['gates']:.1f} | {b['depth']:.1f} | {a['depth']:.1f} |")
    L += ["", "## B. Multiplexer scaling", "", "| controls | CX before | CX after |", "|---|---|---|"]
    for r in mux:
        L.append(f"| {r['controls']} | {r['before']['cx']:.1f} | {r['after']['cx']:.1f} |")
    L += ["", "## C. Permutation synthesis (CX count)", "",
          "| qubits | Qiskit generic | qrig Gray-code | qrig + optimiser |", "|---|---|---|---|"]
    for r in syn:
        L.append(f"| {r['qubits']} | {r['qiskit']:.1f} | {r['qrig']:.1f} | {r['qrig_simplified']:.1f} |")
    L += ["", "## D. Runtime (seconds)", "",
          "| qubits | qrig exact equiv | Qiskit Operator.equiv | qrig optimise | Qiskit transpile |",
          "|---|---|---|---|---|"]
    for r in rt:
        L.append(f"| {r['qubits']} | {r['qrig_equiv_s']:.3f} | {r['qiskit_equiv_s']:.3f} | "
                 f"{r['qrig_optimize_s']:.3f} | {r['qiskit_transpile_s']:.3f} |")
    with open(path, "w") as f:
        f.write("\n".join(L) + "\n")


def main():
    print("A. workloads", flush=True)
    fam = exp_families()
    print("B. multiplexers", flush=True)
    mux = exp_multiplexer_scaling()
    print("C. synthesis", flush=True)
    syn = exp_synthesis()
    print("D. runtime", flush=True)
    rt = exp_runtime()
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump({"qiskit": qiskit.__version__, "qrig": qrig.__version__, "seed": SEED,
                   "workloads": fam, "multiplexer": mux, "synthesis": syn, "runtime": rt},
                  f, indent=2)
    write_markdown(fam, mux, syn, rt, os.path.join(HERE, "results.md"))
    plot(fam, mux, syn, rt, os.path.join(HERE, "benchmark.png"))
    print("wrote benchmark.png, results.json, results.md")


if __name__ == "__main__":
    main()
