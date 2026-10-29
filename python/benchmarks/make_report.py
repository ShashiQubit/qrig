#!/usr/bin/env python3
"""Build the consolidated qrig results report (Markdown + PDF) from the JSON results.

Inputs (all in ``python/benchmarks/``):
    study/study_results.json   paper_study.py   (all-to-all study, this report's core)
    noise_results.json         noise_benchmark.py (larger circuits, IBM Torino topology)
    mqt_results.json           mqt_pipeline.py  (74 MQT circuits up to 128 qubits, QCEC)
    results.json               benchmark.py     (first Qiskit comparison)

Outputs (in ``<repo>/report/``):
    qrig_results.md   plain Markdown (tables + figure links), easy to parse
    qrig_results.pdf  the same document rendered with pandoc + XeLaTeX
    figures/*.png

Usage (from ``python/``):  python3 benchmarks/make_report.py [--no-pdf]
"""
from __future__ import annotations

import argparse
import json
import math
import os
import statistics
import subprocess

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
REPORT = os.path.join(ROOT, "report")
FIG = os.path.join(REPORT, "figures")
MODELS = ("depolarizing", "heron_all2all", "trapped_ion")
MNAME = {"depolarizing": "CX model", "heron_all2all": "CZ model",
         "trapped_ion": "RXX model", "ibm_torino": "FakeTorino heavy-hex"}
SUITE_NAME = {"mqt": "MQT Bench (neutral suite)", "app": "application kernels",
              "pattern": "control-pattern circuits"}


def load(name):
    p = os.path.join(HERE, name)
    with open(p) as f:
        return json.load(f)


def pct(x, digits=0):
    return f"{100 * x:+.{digits}f} %"


def f4(x):
    if x is None:
        return "–"
    if x != 0 and abs(x) < 1e-2:
        return f"{x:.1e}"
    return f"{x:.3f}"


def err_red(a, b):
    ea, eb = 1 - a, 1 - b
    return (ea - eb) / ea if ea > 1e-12 else 0.0


def scrambled(a, b, n):
    return max(a, b) < 2.0 / 2 ** n


def table(header, rows, align=None):
    out = ["| " + " | ".join(header) + " |",
           "|" + "|".join(align or ["---"] * len(header)) + "|"]
    for r in rows:
        out.append("| " + " | ".join(str(x) for x in r) + " |")
    return "\n".join(out)


# ============================================================================ analysis
class Study:
    def __init__(self, d):
        self.d = d
        self.cases = d["cases"]
        self.pc = d["per_case"]
        self.pm = d["per_model"]
        self.robust = d.get("robust", {})
        self.ok = [c for c in self.cases
                   if c["label"] in self.pc and "error" not in self.pc[c["label"]]
                   and all(m in self.pm.get(c["label"], {}) and
                           "error" not in self.pm[c["label"]][m] for m in MODELS)]
        self.failed = [c["label"] for c in self.cases if c not in self.ok]

    def m(self, label, model):
        return self.pm[label][model]

    def changed2q(self, label, model="heron_all2all"):
        r = self.m(label, model)
        return r["qrig"]["twoq"] != r["qiskit"]["twoq"]

    def any_changed(self, label):
        return any(self.changed2q(label, m) for m in MODELS)


# ============================================================================ figures
def fig_scatter(st: Study, path):
    fig, axs = plt.subplots(1, 3, figsize=(13, 4.2))
    colors = {"mqt": "tab:blue", "app": "tab:orange", "pattern": "tab:green"}
    for ax, m in zip(axs, MODELS):
        for suite, col in colors.items():
            xs, ys = [], []
            for c in st.ok:
                if c["suite"] != suite:
                    continue
                r = st.m(c["label"], m)
                xs.append(max(r["qiskit"]["twoq"], 0.8))
                ys.append(max(r["qrig"]["twoq"], 0.8))
            ax.scatter(xs, ys, s=18, alpha=0.75, color=col, label=SUITE_NAME[suite])
        lim = [0.7, 2e4]
        ax.plot(lim, lim, "k--", lw=0.8)
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.set_xlim(lim)
        ax.set_ylim(lim)
        ax.set_xlabel("two-qubit gates, Qiskit alone")
        ax.set_ylabel("two-qubit gates, qrig + Qiskit")
        ax.set_title(MNAME[m])
        ax.grid(alpha=0.3, which="both")
    axs[0].legend(fontsize=8, loc="upper left")
    fig.suptitle("Every circuit of the study: points below the diagonal are improved by qrig; "
                 "none lie above it by more than compiler noise", fontsize=10)
    fig.tight_layout()
    fig.savefig(path, dpi=150)
    plt.close(fig)


def fig_fidelity(st: Study, labels, path):
    fig, axs = plt.subplots(1, 3, figsize=(14, 0.32 * len(labels) + 1.6), sharey=True)
    y = np.arange(len(labels))
    for ax, m in zip(axs, MODELS):
        fq = [st.m(lab, m)["qiskit"].get("F", np.nan) for lab in labels]
        fr = [st.m(lab, m)["qrig"].get("F", np.nan) for lab in labels]
        ax.barh(y + 0.2, fq, 0.4, label="Qiskit alone", color="tab:gray")
        ax.barh(y - 0.2, fr, 0.4, label="qrig + Qiskit", color="tab:red")
        ax.set_xlim(0, 1)
        ax.set_title(MNAME[m], fontsize=10)
        ax.set_xlabel("state fidelity F")
        ax.grid(alpha=0.3, axis="x")
    axs[0].set_yticks(y)
    axs[0].set_yticklabels(labels, fontsize=7)
    axs[0].invert_yaxis()
    axs[0].legend(fontsize=8, loc="lower right")
    fig.tight_layout()
    fig.savefig(path, dpi=150)
    plt.close(fig)


def fig_noise_scale(st: Study, path):
    fig, axs = plt.subplots(1, 2, figsize=(12, 4.2))
    for lab, r in sorted(st.robust.items()):
        if "error" in r:
            continue
        rows = [x for x in r["rows"] if x["kind"] == "scaled"]
        s = [x["scale"] for x in rows]
        er = [err_red(x["qiskit"]["F"], x["qrig"]["F"]) for x in rows]
        g = [x["qrig"]["F"] / x["qiskit"]["F"] for x in rows]
        axs[0].plot(s, [100 * e for e in er], "o-", ms=3, label=lab)
        axs[1].plot(s, g, "o-", ms=3, label=lab)
    for ax in axs:
        ax.set_xscale("log", base=2)
        ax.set_xlabel("noise scale (× CZ-model error rates, T1/T2 ÷ scale)")
        ax.grid(alpha=0.3, which="both")
        ax.axvline(1, color="k", lw=0.6, ls=":")
    axs[0].set_ylabel("error removed by qrig, 1-(1-F_qrig)/(1-F_qiskit)  [%]")
    axs[1].set_ylabel("fidelity ratio F_qrig / F_qiskit")
    axs[1].set_yscale("log")
    axs[1].legend(fontsize=6, ncol=2, loc="upper left")
    fig.tight_layout()
    fig.savefig(path, dpi=150)
    plt.close(fig)


def fig_noise_type(st: Study, path):
    kinds = [("gates_only", "gate errors only"), ("idle_only", "idle T1/T2 only"),
             ("coherent", "coherent over-rotation"), ("coherent+idle", "coherent + idle"),
             ("scaled", "full model (×1)")]
    labs = [lab for lab, r in sorted(st.robust.items()) if "error" not in r]
    fig, ax = plt.subplots(figsize=(12, 4.2))
    w = 0.8 / len(kinds)
    x = np.arange(len(labs))
    for i, (k, kn) in enumerate(kinds):
        vals = []
        for lab in labs:
            rows = [r for r in st.robust[lab]["rows"] if r["kind"] == k
                    and (k != "scaled" or r["scale"] == 1.0)]
            vals.append(100 * err_red(rows[0]["qiskit"]["F"], rows[0]["qrig"]["F"]))
        ax.bar(x + (i - len(kinds) / 2 + 0.5) * w, vals, w, label=kn)
    ax.set_xticks(x)
    ax.set_xticklabels(labs, rotation=30, ha="right", fontsize=7)
    ax.set_ylabel("error removed by qrig [%]")
    ax.axhline(0, color="k", lw=0.6)
    ax.legend(fontsize=8)
    ax.grid(alpha=0.3, axis="y")
    fig.tight_layout()
    fig.savefig(path, dpi=150)
    plt.close(fig)


def fig_time(st: Study, path):
    fig, axs = plt.subplots(1, 2, figsize=(12, 4.2))
    xs, ys, cs = [], [], []
    for c in st.ok:
        lab = c["label"]
        tq = st.m(lab, "heron_all2all")["qiskit"]["seeds"]["compile_time_median"]
        xs.append(tq)
        ys.append(st.pc[lab]["t_qrig"])
        cs.append("tab:red" if st.any_changed(lab) else "tab:gray")
    axs[0].scatter(xs, ys, c=cs, s=14)
    lim = [1e-4, 1e2]
    axs[0].plot(lim, lim, "k--", lw=0.8)
    axs[0].set_xscale("log")
    axs[0].set_yscale("log")
    axs[0].set_xlim(lim)
    axs[0].set_ylim(lim)
    axs[0].set_xlabel("Qiskit level-3 compile time per seed [s]")
    axs[0].set_ylabel("qrig pass time [s]")
    axs[0].set_title("compile-time cost (red: circuits qrig improves)")
    axs[0].grid(alpha=0.3, which="both")
    for m, col in (("heron_all2all", "tab:blue"), ("trapped_ion", "tab:purple")):
        a, b = [], []
        for c in st.ok:
            r = st.m(c["label"], m)
            if st.changed2q(c["label"], m) and r["qiskit"]["duration_us"] > 0:
                a.append(r["qiskit"]["duration_us"])
                b.append(r["qrig"]["duration_us"])
        axs[1].scatter(a, b, s=14, color=col, label=MNAME[m])
    lim = [1e-1, 1e7]
    axs[1].plot(lim, lim, "k--", lw=0.8)
    axs[1].set_xscale("log")
    axs[1].set_yscale("log")
    axs[1].set_xlim(lim)
    axs[1].set_ylim(lim)
    axs[1].set_xlabel("scheduled circuit duration, Qiskit alone [µs]")
    axs[1].set_ylabel("scheduled circuit duration, qrig + Qiskit [µs]")
    axs[1].set_title("execution time on the device model (circuits qrig changes)")
    axs[1].legend(fontsize=8)
    axs[1].grid(alpha=0.3, which="both")
    fig.tight_layout()
    fig.savefig(path, dpi=150)
    plt.close(fig)


# ============================================================================ report
def build(no_pdf=False, study="study/study_results.json"):
    os.makedirs(FIG, exist_ok=True)
    st = Study(load(study))
    noise = load("noise_results.json")
    mqt = load("mqt_results.json")
    first = load("results.json")
    d = st.d
    ver = d["versions"]
    S = d["settings"]

    fig_scatter(st, os.path.join(FIG, "fig1_twoq_all_circuits.png"))
    changed = [c["label"] for c in st.ok if st.any_changed(c["label"])]
    fig_fidelity(st, changed, os.path.join(FIG, "fig2_fidelity.png"))
    if st.robust:
        fig_noise_scale(st, os.path.join(FIG, "fig3_noise_scale.png"))
        fig_noise_type(st, os.path.join(FIG, "fig4_noise_type.png"))
    fig_time(st, os.path.join(FIG, "fig5_time.png"))

    L = []
    w = L.append

    # ------------------------------------------------------------------ numbers
    n_all = len(st.ok)
    by_suite = {s: [c for c in st.ok if c["suite"] == s] for s in SUITE_NAME}
    n_rewritten = sum(1 for c in st.ok if st.pc[c["label"]]["changed"])
    eq_checked = [c for c in st.ok if st.pc[c["label"]]["equiv"]["equal"] is not None]
    eq_ok = [c for c in eq_checked if st.pc[c["label"]]["equiv"]["equal"]]
    sim_rows = [(c["label"], m) for c in st.ok for m in MODELS if st.m(c["label"], m)["simulated"]]
    agree = sum(1 for lab, m in sim_rows if st.m(lab, m).get("ideal_outputs_agree"))
    match = sum(1 for lab, m in sim_rows if st.m(lab, m).get("matches_benchmark"))

    def counts(model, suite=None):
        better = worse = same = 0
        tq = tr = 0
        for c in st.ok:
            if suite and c["suite"] != suite:
                continue
            r = st.m(c["label"], model)
            a, b = r["qiskit"]["twoq"], r["qrig"]["twoq"]
            tq += a
            tr += b
            better += b < a
            worse += b > a
            same += b == a
        return better, same, worse, tq, tr

    # ------------------------------------------------------------------ title
    w("---")
    w('title: "qrig: a verified implementation of the control equations of '
      '*One rig to control them all* — consolidated results"')
    w('subtitle: "All-to-all noise study, resource, time, fault-tolerance and robustness metrics"')
    w('date: "generated by python/benchmarks/make_report.py"')
    w("---")
    w("")
    w("This document collects every result obtained with the `qrig` package so far. It is "
      "generated from the JSON result files by `python/benchmarks/make_report.py`; the PDF and "
      "the Markdown file have the same content. All numbers are **classical simulations** "
      f"(Qiskit {ver['qiskit']}, Qiskit Aer {ver['aer']}, qrig {ver['qrig']}, Python "
      f"{ver['python']}, {ver['cpus']} CPU cores). No real quantum hardware was used. The Lean "
      "proofs cover the optimiser core, not the measurements reported here.")
    w("")

    # ------------------------------------------------------------------ 1 questions
    key_idx = len(L)
    w("# 1. Answers to the questions behind this study")
    w("")
    w("**Is robustness a valid metric?** Yes, if it is defined precisely. In this study "
      "*robustness* means: does the benefit of adding qrig survive when the conditions "
      "change? We measure three versions of it: (i) across compiler randomness (10 "
      "transpiler seeds per circuit and target), (ii) across noise strength (all error "
      "rates of the CZ model scaled from ¼× to 4×), and (iii) across noise "
      "type (stochastic gate errors only, idle decoherence only, coherent over-rotations, "
      "coherent + idle). A pass whose gains vanish or reverse under one of these is "
      "fragile. Section 8 shows that, wherever qrig lowers the two-qubit count, the gain survives all of these changes; the exceptions are listed there.")
    w("")
    w("**Is equivalence a robustness metric?** No. Equivalence (the optimised circuit "
      "implements exactly the same unitary) is a **correctness** property, and for qrig it "
      "is a *guarantee*, not a statistic: every rewrite rule is proved sound in Lean 4 "
      "(`peephole_sound`), and the executable core is compiled from that Lean code to C. We "
      "still check it empirically (exact unitary comparison and ideal-output comparison for "
      "every circuit, Section 3) because the Python ↔ Qiskit bridge is not proved. "
      "Correctness should be reported as its own column (\"verified / checked\"), next to "
      "the performance metrics, not as one of them.")
    w("")
    w("**Which metrics show that qrig is useful?** We report six families, all with "
      "all-to-all connectivity so that hardware topology cannot bias the result:")
    w("")
    w(table(["family", "metric(s)", "why it matters"], [
        ["correctness", "proved rewrite soundness; exact unitary check; ideal outputs agree",
         "an optimiser that may change the circuit is unusable"],
        ["resources", "two-qubit gate count, depth, two-qubit depth", "two-qubit gates dominate "
         "error and time on every platform"],
        ["noise", "state fidelity F, task success P, estimated success probability ESP",
         "what a user actually gets out of a noisy device"],
        ["time", "qrig pass time, Qiskit compile time, scheduled execution time, shots needed ∝ 1/F²",
         "cost of using qrig vs time saved on the device"],
        ["fault tolerance", "T-count and arbitrary rotations after Clifford+T+Rz compilation",
         "cost on future error-corrected machines"],
        ["robustness", "seed spread, noise-strength sweep, noise-type sweep", "whether the "
         "gains are an artefact of one setting"],
    ]))
    w("")
    w("**Is the all-to-all experiment complete?** The earlier all-to-all experiment covered "
      "17 circuits that were *selected because qrig reduced their gate count*. That is enough "
      "to show the effect exists, but it is a biased sample. This study extends it to "
      f"**{n_all} circuits**: every unitary MQT Bench benchmark at up to three sizes "
      f"({len(by_suite['mqt'])} circuits, not hand-picked), {len(by_suite['app'])} "
      "application kernels written the textbook way (SAT-oracle Grover, membership "
      "oracles, QROM table lookup, LCU SELECT oracles, comparators, adders, Shor's modular "
      "adder, Hamming weight, state preparation, swap test, Ising Trotter steps, …), and the "
      f"{len(by_suite['pattern'])} control-pattern circuits of the earlier study; on three "
      "all-to-all targets, with all metric families above. Circuits up to "
      f"{S['dm_max']} qubits are simulated exactly with density matrices; the earlier "
      "12- and 16-qubit multiplier runs are included in Section 10. Section 9 repeats the comparison with two other compilers, TKET and BQSKit.")
    w("")

    # ------------------------------------------------------------------ 2 contribution
    w("# 2. What qrig adds to the original paper")
    w("")
    w("The paper *One rig to control them all* gives a sound and complete equational theory "
      "for quantum circuits with controlled gates (control equations (a)–(h), Figure 1). It "
      "does not give an implementation, an optimisation algorithm, or a measurement of "
      "their effect on noisy hardware. qrig contributes:")
    w("")
    w("1. **A verified implementation.** The circuit language, its semantics, exact "
      "arithmetic in ℚ(ω), an exact equivalence checker, Gray-code permutation synthesis and "
      "a rewrite optimiser are written in Lean 4; the eight control equations and the "
      "soundness of every rewrite the optimiser performs are proved (no `sorry`, standard "
      "axioms only). The C code that runs is generated by the Lean compiler from this code.")
    w("2. **An optimisation algorithm built from the equations** (the paper has none): "
      "fusion/cancellation (a, b), complementarity C⁰(f)·C¹(f) = f (e), commutation (f) and "
      "diagonal commutation, and colour change — pushing NOT gates through controls (d) — "
      "applied to whole Qiskit DAGs within a 128-gate window.")
    w("3. **A usable package**: `import qrig`, a Qiskit transpiler pass "
      "(`QrigControlEquations`) that can be put in front of any Qiskit pipeline, "
      "conversion to/from Qiskit, and a test-suite (265 tests) against Qiskit's simulators.")
    w("4. **The empirical study in this document**: which real circuits benefit, by how "
      "much in gates, fidelity and time, and how robust the effect is.")
    w("")
    w("Equivalence of every optimised circuit is a theorem, so improvements never cost "
      "correctness. The study below shows what they buy.")
    w("")

    # ------------------------------------------------------------------ 3 setup
    w("# 3. Set-up")
    w("")
    w("**Pipelines.** *Qiskit alone* = Qiskit's preset pass manager at optimisation level 3 "
      "(its strongest). *qrig + Qiskit* = `qrig.dag.optimize_circuit` first, then the same "
      "level-3 pass manager. For each circuit, target and pipeline we compile with "
      f"{S['nseeds']} transpiler seeds and keep the compilation with the highest estimated "
      "success probability (what a user would do); the spread over seeds is reported in "
      "Section 6.")
    w("")
    w("**Targets.** All three targets are all-to-all; they differ in native two-qubit gate "
      "(CX, CZ, RXX) and noise parameters. The CZ model uses the median FakeTorino "
      "calibration (an IBM Heron-generation snapshot shipped with Qiskit); the RXX model uses "
      "assumed values. Only the calibration numbers are borrowed: the CZ model is not a model "
      "of that device, which is not all-to-all and whose readout error and crosstalk are "
      "omitted here. Below, the targets are called the CX, CZ and RXX models.")
    w("")
    w(table(["target", "native gates", "noise model"], [
        ["CX model", "cx, rz, sx, x", d["model_info"]["depolarizing"]],
        ["CZ model", "cz, rz, sx, x", "median FakeTorino calibration: "
         + d["model_info"]["heron_all2all"] + "; idle relaxation in an ALAP schedule"],
        ["RXX model", "rxx, rz, sx, x", "assumed round numbers (not a vendor "
         "calibration): " + d["model_info"]["trapped_ion"] + "; idle relaxation"],
    ]))
    w("")
    w("**Circuits.**")
    w("")
    fam = {}
    for c in st.ok:
        fam.setdefault(c["suite"], {}).setdefault(c["family"], []).append(
            str(st.pc[c["label"]]["qubits"]))
    w(table(["suite", "circuits", "families (qubit counts)"], [
        [SUITE_NAME[s], len(by_suite[s]),
         "; ".join(f"{f} ({', '.join(v)})" for f, v in sorted(fam.get(s, {}).items()))]
        for s in SUITE_NAME]))
    w("")
    w("The MQT suite contains every unitary benchmark of MQT Bench at the algorithm level "
      "(dynamic circuits with mid-circuit measurement, and benchmarks with no instance in the "
      "size range, are excluded). Sizes are the smallest, middle and largest admissible size "
      f"between 4 and {S['dm_max']} qubits. The application kernels are written the way a "
      "Qiskit user writes them (library objects or the textbook construction); their source "
      "is `python/benchmarks/app_circuits.py`. The control-pattern circuits contain exactly "
      "the patterns the control equations target and are reported separately so that they "
      "do not inflate the averages.")
    w("")
    w("**Metrics.** F = state fidelity ⟨ψ|ρ|ψ⟩ averaged over "
      f"{S['inputs']} random product input states; P = Hellinger fidelity of the output "
      "distribution for one classical input (the success probability when the answer is "
      "deterministic); *error removed* = 1 − (1 − F_qrig)/(1 − F_Qiskit); *ratio* = "
      "F_qrig/F_Qiskit; ESP = ∏(1 − e_gate). When noise scales a measured signal by F, the "
      "shots needed for a fixed precision scale like 1/F², so the *shot saving* is "
      "(F_qrig/F_Qiskit)². Duration = length of the ALAP-scheduled compiled circuit.")
    w("")

    # ------------------------------------------------------------------ 3b correctness
    w("## 3.1 Correctness checks (all circuits)")
    w("")
    w(f"* qrig rewrote {n_rewritten} of the {n_all} circuits (at least one rule applied).")
    w(f"* Exact unitary comparison, qrig output vs input circuit: {len(eq_ok)} of "
      f"{len(eq_checked)} circuits identical up to 10⁻⁸ in every matrix entry "
      "(not up to global phase — exactly).")
    w(f"* Ideal (noise-free) outputs of the two compiled circuits agree in {agree} of "
      f"{len(sim_rows)} (circuit, target) pairs, and agree with the statevector of the "
      f"original benchmark in {match} of {len(sim_rows)}.")
    w(f"* Earlier MQT pipeline run (74 circuits up to 128 qubits): MQT QCEC proved the qrig "
      f"output equivalent for "
      f"{sum(1 for r in mqt if str(r.get('qcec_opt', '')).startswith('equivalent'))} "
      f"circuits; the rest timed out; none was found non-equivalent.")
    if st.failed:
        w(f"* Circuits that failed to run (excluded): {', '.join(st.failed)}.")
    w("")

    w("## 3.2 What is proved in Lean about the kernels and the metrics")
    w("")
    w("Besides the soundness of every qrig rewrite, `QrigProofs/Study/` proves what several "
      "application kernels compute and the properties of the metrics this report relies on "
      "(no `sorry`, standard axioms only):")
    w("")
    w(table(["file", "theorems", "statement"], [
        ["`Reversible.lean`", "`incrementer_spec`, `hamming_weight_correct`, "
         "`memberOracle_spec`, `qrom_spec`",
         "incrementer adds 1 mod 2ⁿ; the Hamming-weight counter ends with the popcount; the "
         "membership oracle flips its target iff the input is in the set; QROM XORs "
         "table[address] into the data register"],
        ["`Reversible.lean`", "`run_xconj`",
         "colour change (d) on basis states: NOT gates around a block flip the polarity of "
         "the controls they touch (the rewrite qrig applies to these kernels)"],
        ["`Draper.lean`", "`phiAdd_correct`, `phiAddOld_wrong`",
         "the phase angles of the Draper adder in `shor_modadd` map QFT\\|x⟩ to "
         "QFT\\|(x+a) mod 2ⁿ⟩ under Qiskit's `QFTGate` convention; the angle formula used before "
         "a fix during the study does not"],
        ["`Metrics.lean`", "`esp_sublist_le`, `espUniform_robust`, "
         "`espUniform_tradeoff_not_robust`",
         "removing gates never lowers ESP; no more 1q and no more 2q gates ⇒ ESP at least as "
         "high at every noise scale; with a 1q/2q trade-off the ESP comparison can flip"],
        ["`Metrics.lean`", "`shotsNeeded_div`, `geomean_le_one`, `geomean_lt_one`",
         "shot saving = (F_qrig/F_Qiskit)²; if no circuit gets worse the per-circuit "
         "geometric-mean ratio is ≤ 1, and < 1 once one circuit improves"],
    ]))
    w("")
    w("The kernel theorems are about a Lean gate-list model written to mirror "
      "`python/benchmarks/app_circuits.py`; `python/tests/test_kernels.py` runs the actual "
      "Qiskit circuits on every basis state and checks them against the same specifications. "
      "The simulated numbers themselves are not checked in Lean.")
    w("")

    # ------------------------------------------------------------------ 4 resources
    w("# 4. Resources: two-qubit gates and depth")
    w("")
    w("![Two-qubit gate count of every circuit, Qiskit alone vs qrig + Qiskit, on the three "
      "all-to-all targets.](figures/fig1_twoq_all_circuits.png)")
    w("")
    rows = []
    for s in SUITE_NAME:
        for m in MODELS:
            b, sm, wo, tq, tr = counts(m, s)
            rows.append([SUITE_NAME[s], MNAME[m], b, sm, wo, f"{tq} → {tr}",
                         pct((tr - tq) / tq if tq else 0, 1)])
    for m in MODELS:
        b, sm, wo, tq, tr = counts(m)
        rows.append(["**all**", MNAME[m], b, sm, wo, f"{tq} → {tr}",
                     pct((tr - tq) / tq if tq else 0, 1)])
    w(table(["suite", "target", "fewer 2q", "equal", "more 2q", "total 2q gates", "change"], rows))
    w("")
    w("*fewer/equal/more*: number of circuits where qrig + Qiskit has fewer / the same / more "
      "two-qubit gates than Qiskit alone (best seed of each).")
    w("")
    # per circuit table of changed
    w("Circuits whose two-qubit count changes on at least one target:")
    w("")
    rows = []
    for lab in changed:
        pc = st.pc[lab]
        r = [lab, pc["qubits"]]
        for m in MODELS:
            x = st.m(lab, m)
            r.append(f"{x['qiskit']['twoq']} → {x['qrig']['twoq']}")
        x = st.m(lab, "heron_all2all")
        r.append(f"{x['qiskit']['depth']} → {x['qrig']['depth']}")
        r.append(", ".join(f"{k} {v}" for k, v in pc["rules"].items() if v))
        rows.append(r)
    w(table(["circuit", "qubits", "2q (CX)", "2q (CZ)", "2q (RXX)", "depth (CZ)",
             "rules applied"], rows))
    w("")
    w("Rules: `xconj` colour change (d), `compl` complementarity (e), `cancel`/`fuse` "
      "equations (a)/(b), `idRem` identity removal.")
    w("")
    category_section(w, st)

    # ------------------------------------------------------------------ 5 noise
    w("# 5. Noise: fidelity of the compiled circuits")
    w("")
    w("![State fidelity with and without qrig, circuits whose gate count qrig changes.]"
      "(figures/fig2_fidelity.png)")
    w("")
    rows = []
    for lab in changed:
        n = st.pc[lab]["qubits"]
        r = [lab]
        for m in MODELS:
            x = st.m(lab, m)
            if not x["simulated"]:
                r.append("–")
                continue
            a, b = x["qiskit"]["F"], x["qrig"]["F"]
            tag = " (scr.)" if scrambled(a, b, n) else ""
            r.append(f"{f4(a)} → {f4(b)}{tag}")
        x = st.m(lab, "heron_all2all")
        a, b = x["qiskit"]["F"], x["qrig"]["F"]
        r.append(pct(err_red(a, b)))
        r.append(f"×{b / a:.2f}" if a > 0 else "–")
        r.append(f"×{(b / a) ** 2:.2f}" if a > 0 and not scrambled(a, b, n) else "–")
        rows.append(r)
    w(table(["circuit", "F (CX)", "F (CZ)", "F (RXX)", "error removed (CZ)",
             "ratio (CZ)", "shot saving (CZ)"], rows))
    w("")
    w("*(scr.)*: both fidelities below 2/2ⁿ, i.e. the output is essentially noise either way.")
    w("")
    # aggregate statements
    imp = []
    for lab in changed:
        for m in MODELS:
            x = st.m(lab, m)
            if x["simulated"]:
                imp.append((lab, m, x["qiskit"]["F"], x["qrig"]["F"]))
    up = [t for t in imp if t[3] > t[2] + 1e-9]
    down = [t for t in imp if t[3] < t[2] - 1e-9]
    w(f"Over the {len(imp)} simulated (circuit, target) pairs that qrig changes, the fidelity "
      f"is higher with qrig in {len(up)} and lower in {len(down)}"
      + (": " + "; ".join(f"{t[0]} on {MNAME[t[1]]} ({f4(t[2])} → {f4(t[3])})" for t in down)
         if down else "") + ".")
    w("")
    unchanged_F = [(c["label"], m) for c in st.ok for m in MODELS
                   if st.m(c["label"], m).get("unchanged")]
    w(f"For the {len(set(l for l, _ in unchanged_F))} circuits that qrig leaves exactly "
      "unchanged, both pipelines produce the same compiled circuit and therefore the same "
      "fidelity (not simulated twice).")
    w("")

    # ------------------------------------------------------------------ time
    w("# 6. Time")
    w("")
    w("![Left: qrig pass time against Qiskit's compile time. Right: scheduled execution "
      "time of the compiled circuits on the two device models.](figures/fig5_time.png)")
    w("")
    tq_all = [st.pc[c["label"]]["t_qrig"] for c in st.ok]
    comp = [st.m(c["label"], "heron_all2all")["qiskit"]["seeds"]["compile_time_median"]
            for c in st.ok]
    ratio = [a / b for a, b in zip(tq_all, comp) if b > 0]
    w(f"* **Compile-time cost.** qrig pass: median {1e3 * statistics.median(tq_all):.1f} ms, "
      f"maximum {max(tq_all):.2f} s per circuit. Qiskit level 3 (one seed, CZ model): "
      f"median {1e3 * statistics.median(comp):.1f} ms, maximum {max(comp):.2f} s. Median "
      f"ratio qrig/Qiskit {statistics.median(ratio):.2f}.")
    rows = []
    for lab in changed:
        r = [lab]
        for m in ("heron_all2all", "trapped_ion"):
            x = st.m(lab, m)
            a, b = x["qiskit"]["duration_us"], x["qrig"]["duration_us"]
            unit, sc = ("µs", 1) if m == "heron_all2all" else ("ms", 1e-3)
            r.append(f"{a * sc:.1f} → {b * sc:.1f} {unit} ({pct((b - a) / a if a else 0)})")
        rows.append(r)
    w("* **Execution time on the device.** Removing gates also shortens the scheduled "
      "circuit, so each shot runs faster and (Section 5) fewer shots are needed:")
    w("")
    w(table(["circuit", "duration, CZ model", "duration, RXX model"], rows))
    w("")
    w("Time-to-solution for a fixed precision scales roughly like duration × 1/F² "
      "(ignoring fixed per-shot overheads such as reset and readout); both factors fall with "
      "qrig on the circuits above.")
    w("")

    # ------------------------------------------------------------------ FT
    w("# 7. Fault-tolerant cost (T-count)")
    w("")
    rows = []
    for lab in changed:
        pc = st.pc[lab]
        if "ft_qiskit" not in pc:
            continue
        a, b = pc["ft_qiskit"], pc["ft_qrig"]
        rows.append([lab, f"{a['t_count']} → {b['t_count']}", f"{a['rotations']} → {b['rotations']}",
                     f"{a['cx']} → {b['cx']}"])
    w("Both pipelines compiled with Qiskit level 3 to {cx, h, s, sdg, t, tdg, x, z, rz}; "
      "`rz` angles that are odd multiples of π/4 count as T, other non-Clifford angles as "
      "*arbitrary rotations* (each costs tens of T gates after synthesis).")
    w("")
    w(table(["circuit", "T-count", "arbitrary rotations", "CX"], rows))
    w("")
    tt = [(st.pc[l]["ft_qiskit"], st.pc[l]["ft_qrig"]) for l in changed if "ft_qiskit" in st.pc[l]]
    t_down = sum(1 for a, b in tt if b["t_count"] < a["t_count"])
    r_up = [l for l in changed if "ft_qiskit" in st.pc[l]
            and st.pc[l]["ft_qrig"]["rotations"] > st.pc[l]["ft_qiskit"]["rotations"]]
    w(f"qrig lowers the T-count on {t_down} of the {len(tt)} circuits it changes. "
      + (f"On {len(r_up)} circuits ({', '.join(r_up)}) it *increases* the number of "
         "arbitrary rotations: Qiskit synthesises the multi-controlled gates that qrig emits "
         "(e.g. C³Z instead of a multi-controlled phase of π) without ancillas, using "
         "π/8-type rotations. This is a property of Qiskit's ancilla-free synthesis, not of "
         "the rewrite; T-count is therefore a mixed metric for qrig today and an open "
         "improvement (emit the multi-controlled gates in the form Qiskit synthesises best)."
         if r_up else ""))
    w("")

    # ------------------------------------------------------------------ robustness
    w("# 8. Robustness")
    w("")
    w("## 8.1 Across compiler randomness (transpiler seeds)")
    w("")
    rows = []
    tot = no_worse = 0
    for lab in changed:
        r = [lab]
        for m in MODELS:
            x = st.m(lab, m)
            a, b = x["qiskit"]["seeds"], x["qrig"]["seeds"]
            r.append(f"{a['min']}/{a['median']:g}/{a['max']} → {b['min']}/{b['median']:g}/{b['max']}")
        x = st.m(lab, "heron_all2all")
        r.append(f"{100 * x['seed_no_worse']:.0f} %")
        rows.append(r)
    for c in st.ok:
        for m in MODELS:
            x = st.m(c["label"], m)
            k = len(x["qiskit"]["seeds"]["all"])
            tot += k
            no_worse += round(x["seed_no_worse"] * k)
    w(table(["circuit", "2q min/median/max, CX", "CZ", "RXX",
             "seeds no worse (CZ)"], rows))
    w("")
    w(f"Over all {tot} (circuit, target, seed) compilations, qrig + Qiskit used no more "
      f"two-qubit gates than Qiskit alone with the same seed in {no_worse} "
      f"({100 * no_worse / tot:.1f} %).")
    w("")
    spread = sum(1 for c in st.ok for m in MODELS
                 for v in ("qiskit", "qrig")
                 if st.m(c["label"], m)[v]["seeds"]["min"] != st.m(c["label"], m)[v]["seeds"]["max"])
    w(f"Note: with all-to-all connectivity there is no layout or routing step, which is where "
      f"Qiskit's randomness mostly acts; the two-qubit count varies across seeds in only "
      f"{spread} of the {2 * len(st.ok) * len(MODELS)} (circuit, target, pipeline) "
      "combinations. Seed robustness is therefore close to automatic here; it becomes a "
      "real test on a restricted topology (Section 10).")
    w("")
    if st.robust:
        labs = [l for l, r in sorted(st.robust.items()) if "error" not in r]
        w("## 8.2 Across noise strength")
        w("")
        w(f"Circuits whose CZ-model two-qubit count qrig changes and that have at most 8 qubits "
          f"({len(labs)} circuits) were re-simulated on the CZ model with every "
          "gate error multiplied, and T1/T2 divided, by a common scale factor (the compiled "
          "circuits are the same; only the noise changes).")
        w("")
        w("![Error removed (left) and fidelity ratio (right) as the noise strength changes.]"
          "(figures/fig3_noise_scale.png)")
        w("")
        scales = [s for k, s in d["robust_variants"] if k == "scaled"]
        rows = []
        for lab in labs:
            rr = {x["scale"]: x for x in st.robust[lab]["rows"] if x["kind"] == "scaled"}
            rows.append([lab] + [f"{pct(err_red(rr[s]['qiskit']['F'], rr[s]['qrig']['F']))} "
                                 f"(×{rr[s]['qrig']['F'] / rr[s]['qiskit']['F']:.2f})"
                                 for s in scales])
        w(table(["circuit"] + [f"scale {s:g}" for s in scales], rows))
        w("")
        w("## 8.3 Across noise type")
        w("")
        w("![Error removed under different kinds of noise (same compiled circuits).]"
          "(figures/fig4_noise_type.png)")
        w("")
        kinds = [("gates_only", "gate errors only"), ("idle_only", "idle T1/T2 only"),
                 ("coherent", "coherent"), ("coherent+idle", "coherent + idle")]
        rows = []
        for lab in labs:
            r = [lab]
            for k, _ in kinds:
                x = [y for y in st.robust[lab]["rows"] if y["kind"] == k][0]
                r.append(f"{f4(x['qiskit']['F'])} → {f4(x['qrig']['F'])}")
            rows.append(r)
        w(table(["circuit (F: Qiskit → qrig)"] + [k for _, k in kinds], rows))
        w("")
        w("*Coherent*: every two-qubit gate is followed by an unwanted RZZ(0.1 rad) and every "
          "`sx`/`x` by RX(0.02 rad), no stochastic noise. Coherent errors can add up or cancel "
          "depending on the circuit, so this is the hardest case for any claim of the form "
          "\"fewer gates ⇒ higher fidelity\".")
        w("")
        neg = []
        for lab in labs:
            for x in st.robust[lab]["rows"]:
                if x["qrig"]["F"] < x["qiskit"]["F"] - 1e-9:
                    neg.append(f"{lab} ({x['kind']} {x['scale']:g}: {f4(x['qiskit']['F'])} → "
                               f"{f4(x['qrig']['F'])})")
        n_var = sum(len(st.robust[l]["rows"]) for l in labs)
        w(f"Across all {n_var} (circuit, noise variant) simulations the qrig circuit has the "
          f"higher fidelity in {n_var - len(neg)}"
          + (f"; the exceptions are {'; '.join(neg)}." if neg else "."))
        w("")

    # ------------------------------------------------------------------ other compilers
    comp_path = os.path.join(HERE, "study", "compilers_results.json")
    comp_sum = {}
    if os.path.exists(comp_path):
        with open(comp_path) as f:
            comp_sum = compilers_section(w, st, json.load(f))

    # ------------------------------------------------------------------ larger / topology
    w("# 10. Larger circuits and the effect of topology (earlier runs)")
    w("")
    w("From `noise_benchmark.py` (5 transpiler seeds, density matrices up to 12 qubits, 300 "
      "quantum trajectories for 16 qubits). The last column is FakeTorino itself: its "
      "heavy-hex coupling map, where Qiskit inserts SWAP gates, and its per-qubit "
      "calibration (the CZ model uses the medians of the same calibration, all-to-all).")
    w("")
    rows = []
    for r in noise["rows"]:
        if r["qubits"] <= 10 and not r["case"].startswith("grover"):
            continue
        out = [r["case"], r["qubits"]]
        for m in ("depolarizing", "heron_all2all", "trapped_ion", "ibm_torino"):
            x = r["models"].get(m)
            if not x:
                out.append("–")
                continue
            a, b = x["qiskit"], x["qrig"]
            out.append(f"{a['cx']}→{b['cx']}; F {f4(a['F'])}→{f4(b['F'])}")
        rows.append(out)
    w(table(["circuit", "qubits", "CX model", "CZ model", "RXX model",
             "FakeTorino (heavy-hex)"], rows))
    w("")
    w("Findings of that run: the gain persists at 12–16 qubits as a fidelity *ratio* (×1.5 "
      "to ×3.9) even when both fidelities are low; on the heavy-hex device the only "
      "regression (Grover 5, −2 % error removed) disappears with all-to-all connectivity, "
      "i.e. it was caused by routing, not by qrig.")
    w("")
    w("**MQT pipeline, 74 circuits up to 128 qubits (CX basis, no noise).** Total CX after "
      "Qiskit O3: " + f"{sum(r['cx_qiskit'] for r in mqt)} → "
      f"{sum(r['cx_qrig_qiskit'] for r in mqt)} with qrig "
      f"({pct((sum(r['cx_qrig_qiskit'] for r in mqt) - sum(r['cx_qiskit'] for r in mqt)) / sum(r['cx_qiskit'] for r in mqt), 1)}); "
      f"fewer CX on {sum(1 for r in mqt if r['cx_qrig_qiskit'] < r['cx_qiskit'])} circuits, "
      f"more on {sum(1 for r in mqt if r['cx_qrig_qiskit'] > r['cx_qiskit'])}. "
      "Largest savings: Grover 11 (16750 → 13550), multiplier 16 (719 → 592).")
    w("")
    w("**First Qiskit comparison (`benchmark.py`).**")
    w("")
    w(table(["workload", "CX: Qiskit → qrig + Qiskit"], [
        [x["family"], f"{x['before']['cx']:g} → {x['after']['cx']:g}"] for x in first["workloads"]]))
    w("")
    w("qrig's own permutation synthesis (the paper's Gray-code construction, Theorem 9) is "
      "correct by construction but uses 10–100× more CNOTs than Qiskit's generic synthesis; "
      "it is not used in the pipelines above.")
    w("")

    # ------------------------------------------------------------------ conclusions
    b_all = {m: counts(m) for m in MODELS}
    w("# 11. Summary")
    w("")
    sum_start = len(L)
    w(f"* **Correctness**: every rewrite is proved sound in Lean; all {len(eq_checked)} "
      "circuits checked exactly were identical after qrig; no circuit in any run was found "
      "non-equivalent.")
    w("* **Do no harm**: " + "; ".join(
        f"{MNAME[m]}: fewer 2q gates on {b_all[m][0]}, equal on {b_all[m][1]}, more on "
        f"{b_all[m][2]} of {n_all} circuits" for m in MODELS) + ".")
    cats_hit = sorted({category_of(c) for c in st.ok
                       if st.m(c["label"], "heron_all2all")["qrig"]["twoq"]
                       < st.m(c["label"], "heron_all2all")["qiskit"]["twoq"]})
    w(f"* **Where it helps**: qrig lowers the CZ-model two-qubit count in {len(cats_hit)} "
      f"application categories ({', '.join(cats_hit)}): circuits with multi-controlled "
      "gates next to each other or conjugated by NOT gates — Grover and SAT oracles, "
      "membership oracles, QROM / table lookup, LCU SELECT oracles, multiplexers, the MQT "
      "multipliers, compute/uncompute blocks. On circuits without such structure (QFT, QPE, "
      "VQE/QAOA ansätze, GHZ, W-state, Trotter circuits, swap test) it changes nothing and "
      "costs a few milliseconds.")
    sim_ch = [(lab, m, st.m(lab, m)) for lab in changed for m in MODELS
              if st.m(lab, m)["simulated"]]
    f_up = sum(1 for _, _, x in sim_ch if x["qrig"]["F"] > x["qiskit"]["F"] + 1e-9)
    f_dn = []
    for lab, m, x in sim_ch:
        if x["qrig"]["F"] < x["qiskit"]["F"] - 1e-9:
            n = st.pc[lab]["qubits"]
            if x["qrig"]["twoq"] > x["qiskit"]["twoq"]:
                why = (f"qrig + Qiskit ends with more two-qubit gates, "
                       f"{x['qiskit']['twoq']} → {x['qrig']['twoq']}")
            else:
                why = (f"output close to fully mixed for both, F ≈ "
                       f"{x['qiskit']['F'] * 2 ** n:.1f} × 2⁻ⁿ with n = {n}")
            f_dn.append(f"{lab} on {MNAME[m]}: {why}")
    w(f"* **Noise**: over the {len(sim_ch)} simulated (circuit, target) pairs that qrig "
      f"changes, the fidelity is higher with qrig in {f_up} and lower in {len(f_dn)}"
      + (f" ({'; '.join(f_dn)})" if f_dn else "") + ". Where the fidelity rises, the gain "
      "holds from ¼× to 4× today's error rates and under gate-only, idle-only and coherent "
      "noise (Section 8).")
    if comp_sum:
        w("* **Other compilers**: " + "; ".join(
            f"{k}: qrig + {k} has fewer 2q gates on {v[1]}, equal on {v[2]}, more on {v[3]} "
            f"of {v[0]} circuits, total {v[4]} → {v[5]} ({pct((v[5] - v[4]) / v[4] if v[4] else 0, 1)})"
            for k, v in comp_sum.items()) + ". The benefit is therefore not specific to "
          "Qiskit. TKET alone already reaches qrig's saving on the MQT Grover and multiplier "
          "circuits; on data loading (QROM, LCU SELECT, multiplexers), membership oracles and "
          "the control patterns, qrig lowers the count in front of all three compilers "
          "(Section 9).")
    w("* **Time**: the qrig pass costs milliseconds; the compiled circuits are shorter on "
      "the device and need fewer shots.")
    w("* **Fault tolerance**: T-count is mixed (Section 7).")
    w("")
    key = ["**Key findings** (details and exceptions in Sections 4–9; summary repeated in "
           "Section 11):", ""] + L[sum_start:]
    L[key_idx:key_idx] = key
    w("# 12. Limitations")
    w("")
    w("* Simulation only; the CZ model borrows median calibration numbers but is all-to-all, "
      "and the RXX model uses assumed round numbers. Readout error and crosstalk are not "
      "modelled.")
    w(f"* Exact density-matrix simulation limits the noise study to ≤ {S['dm_max']} qubits "
      "(≤ 16 with trajectories in the earlier run).")
    w("* Compilers: Qiskit level 3, TKET `FullPeepholeOptimise` and BQSKit level 2 with "
      "default settings. BQSKit was run only up to 8 qubits, and its higher levels / larger "
      "synthesis blocks were not tried (too slow for this suite). Other tools (e.g. "
      "Quarl, VOQC, PyZX) were not compared.")
    w("* The QROM kernel is the textbook ancilla-free construction; ancilla-based "
      "constructions (e.g. unary iteration) are cheaper to begin with.")
    w("* The Python ↔ Qiskit bridge, the Lean compiler and the C compiler are trusted, not "
      "verified; the bridge is tested and every output here was checked.")
    w("")
    w("# 13. Reproducing")
    w("")
    w("```")
    w("pip install qiskit qiskit-aer qiskit-ibm-runtime mqt.bench mqt.qcec matplotlib")
    w("cd python")
    w(f"python3 benchmarks/paper_study.py     # this study ({d.get('wall_time_s', 0) / 60:.0f} min on {ver['cpus']} cores)")
    w("pip install pytket pytket-qiskit bqskit   # for Section 9")
    w("python3 benchmarks/compilers_study.py # Section 9 (needs study_results.json)")
    w("python3 benchmarks/make_report.py     # this document (needs pandoc + xelatex for the PDF)")
    w("python3 benchmarks/noise_benchmark.py # Section 10, noise on larger circuits / Torino")
    w("python3 benchmarks/mqt_pipeline.py --scale  # Section 10, 74 MQT circuits + QCEC")
    w("```")
    w("")
    w("Raw data: `python/benchmarks/study/study_results.json`, "
      "`python/benchmarks/noise_results.json`, `python/benchmarks/mqt_results.json`, "
      "`python/benchmarks/results.json`, `python/benchmarks/study/compilers_results.json`.")
    w("")
    w("# Appendix A. Every circuit of the study")
    w("")
    rows = []
    for c in st.ok:
        lab = c["label"]
        pc = st.pc[lab]
        r = [lab, c["suite"], pc["qubits"], pc["rewrites"]]
        for m in MODELS:
            x = st.m(lab, m)
            s = f"{x['qiskit']['twoq']}→{x['qrig']['twoq']}"
            if x["simulated"]:
                s += f"; F {f4(x['qiskit']['F'])}→{f4(x['qrig']['F'])}"
            r.append(s)
        r.append("yes" if pc["equiv"]["equal"] else ("–" if pc["equiv"]["equal"] is None else "NO"))
        rows.append(r)
    w(table(["circuit", "suite", "qubits", "rewrites", "CX", "CZ", "RXX", "exact equiv."],
            rows))
    w("")

    md = "\n".join(L)
    md_path = os.path.join(REPORT, "qrig_results.md")
    with open(md_path, "w") as f:
        f.write(md)
    print("wrote", md_path)
    if not no_pdf:
        make_pdf(md_path)


def compilers_section(w, st, cd):
    """Section: qrig in front of Qiskit, TKET and BQSKit (all-to-all CX target)."""
    res = {}
    errors = []
    for r in cd["results"]:
        if "error" in r:
            errors.append(r)
            continue
        res[(r["label"], r["compiler"], r["variant"])] = r
    comps = ["qiskit", "tket", "bqskit"]
    cname = {"qiskit": "Qiskit O3", "tket": "TKET", "bqskit": "BQSKit"}

    def get(lab, comp, var):
        """dict with twoq/depth/F/time for pipeline (comp, var) or None."""
        changed = st.pc[lab]["changed"]
        if comp == "qiskit":
            x = st.m(lab, "depolarizing")["qiskit" if var == "input" else "qrig"]
            return {"twoq": x["twoq"], "depth": x["depth"], "F": x.get("F"),
                    "time": x["seeds"]["compile_time_median"]}
        r = res.get((lab, comp, "input" if not changed else var))
        if r is None:
            return None
        F = r.get("F")
        return {"twoq": r["twoq"], "depth": r["depth"], "F": F, "time": r["compile_time"],
                "inf": r.get("infidelity_vs_benchmark")}

    w("# 9. qrig in front of other compilers: TKET and BQSKit")
    w("")
    v = cd.get("versions", {})
    w(f"Is the benefit specific to Qiskit? We put qrig in front of two other optimising "
      f"compilers — **TKET** (pytket {v.get('pytket', '?')}, `FullPeepholeOptimise`, its "
      f"strongest generic optimisation) and **BQSKit** ({v.get('bqskit', '?')}, "
      "`compile` at optimisation level 2: block partitioning and numerical resynthesis, "
      "ε = 10⁻⁸) — and compare *X alone* with *qrig + X* for each. Target: all-to-all, "
      "{cx, rz, sx, x}; noise: the depolarizing model (p2 = 0.3 %, p1 = 0.03 %). BQSKit was "
      f"run on circuits with at most {cd['settings']['bqskit_max_qubits']} qubits "
      "(numerical synthesis is slow). Qiskit numbers are those of Sections 4–5. "
      "Source: `python/benchmarks/compilers_study.py`.")
    w("")
    rows = []
    summary = {}
    for comp in comps:
        b = s_ = wo = tq = tr = n = 0
        for c in st.ok:
            lab = c["label"]
            a, q = get(lab, comp, "input"), get(lab, comp, "qrig")
            if a is None or q is None:
                continue
            n += 1
            tq += a["twoq"]
            tr += q["twoq"]
            b += q["twoq"] < a["twoq"]
            wo += q["twoq"] > a["twoq"]
            s_ += q["twoq"] == a["twoq"]
        summary[cname[comp]] = (n, b, s_, wo, tq, tr)
        rows.append([cname[comp], n, b, s_, wo, f"{tq} → {tr}",
                     pct((tr - tq) / tq if tq else 0, 1)])
    w(table(["compiler X", "circuits", "qrig + X fewer 2q", "equal", "more", "total 2q: X → qrig + X",
             "change"], rows))
    w("")
    # per circuit table for circuits qrig rewrites and where any compiler changes
    labs = []
    for c in st.ok:
        lab = c["label"]
        if not st.pc[lab]["changed"]:
            continue
        vals = [(get(lab, k, "input"), get(lab, k, "qrig")) for k in comps]
        if any(a and q and a["twoq"] != q["twoq"] for a, q in vals):
            labs.append(lab)
    rows = []
    for lab in labs:
        r = [lab]
        best = None
        for k in comps:
            a, q = get(lab, k, "input"), get(lab, k, "qrig")
            if a is None or q is None:
                r.append("–")
                continue
            r.append(f"{a['twoq']} → {q['twoq']}")
            for nm, x in ((cname[k], a), ("qrig+" + cname[k], q)):
                if best is None or x["twoq"] < best[1]:
                    best = (nm, x["twoq"])
        r.append(f"{best[0]} ({best[1]})" if best else "–")
        rows.append(r)
    w("Two-qubit gates, *X alone → qrig + X*, for the circuits where qrig changes the result "
      "of at least one compiler:")
    w("")
    w(table(["circuit", "Qiskit O3", "TKET", "BQSKit", "fewest overall"], rows))
    w("")
    full = [lab for lab in labs if all(get(lab, k, "input") and get(lab, k, "qrig") for k in comps)]
    all3 = [lab for lab in full
            if all(get(lab, k, "qrig")["twoq"] < get(lab, k, "input")["twoq"] for k in comps)]
    win = sum(1 for r in rows if r[-1].startswith("qrig+"))
    tk_only = [lab for lab in labs if get(lab, "tket", "input") and get(lab, "qiskit", "input")
               and get(lab, "qiskit", "qrig")["twoq"] < get(lab, "qiskit", "input")["twoq"]
               and get(lab, "tket", "qrig")["twoq"] == get(lab, "tket", "input")["twoq"]]
    w(f"Of the {len(full)} circuits in this table on which all three compilers ran, qrig "
      f"lowers the two-qubit count for **all three** on {len(all3)} "
      f"({', '.join(all3)}). In {win} of the {len(rows)} rows the overall minimum is reached "
      "by a pipeline that starts with qrig. "
      + (f"On {len(tk_only)} circuits ({', '.join(tk_only)}) qrig helps Qiskit but not "
         "TKET: TKET's `FullPeepholeOptimise` already finds the same saving on its own (it "
         "resynthesises multi-qubit blocks), so there qrig mainly closes the gap between "
         "Qiskit and TKET. " if tk_only else "")
      + "The savings on data loading (QROM, LCU SELECT, multiplexers), membership oracles "
      "and the control-pattern circuits come from the control equations (merging and "
      "cancelling multi-controlled gates before they are decomposed), which none of the "
      "three compilers does by itself.")
    w("")
    rows = []
    for lab in labs:
        r = [lab]
        for k in comps:
            a, q = get(lab, k, "input"), get(lab, k, "qrig")
            if a is None or q is None or a.get("F") is None or q.get("F") is None:
                r.append("–")
                continue
            r.append(f"{f4(a['F'])} → {f4(q['F'])} ({pct(err_red(a['F'], q['F']))})")
        rows.append(r)
    w("State fidelity under depolarizing noise, *X alone → qrig + X* (error removed):")
    w("")
    w(table(["circuit", "Qiskit O3", "TKET", "BQSKit"], rows))
    w("")
    # who wins without qrig: tket vs qiskit vs bqskit, and does qrig close the gap
    rows = []
    for k in comps:
        ts = [get(c["label"], k, "input") for c in st.ok]
        ts = [t["time"] for t in ts if t]
        if ts:
            rows.append([cname[k], f"{1e3 * statistics.median(ts):.0f} ms", f"{max(ts):.1f} s"])
    tq = [st.pc[c["label"]]["t_qrig"] for c in st.ok]
    rows.append(["qrig pass", f"{1e3 * statistics.median(tq):.1f} ms", f"{max(tq):.2f} s"])
    w("Compile time per circuit (one run; Qiskit: one seed):")
    w("")
    w(table(["", "median", "maximum"], rows))
    w("")
    infs = [r.get("infidelity_vs_benchmark") for r in res.values()
            if r.get("infidelity_vs_benchmark") is not None]
    w(f"Correctness: every TKET and BQSKit output was compared with the original benchmark "
      f"unitary ({len(infs)} outputs up to 10 qubits); the largest process infidelity "
      f"1 − |tr(U†V)|/2ⁿ was {max(infs):.1e}" if infs else "")
    w(" (BQSKit's numerical resynthesis is approximate by design, with ε = 10⁻⁸; qrig's "
      "rewrites and TKET's are exact)." if infs else "")
    w("")
    w("Implementation note: pytket's Qiskit converter rejects some Qiskit instructions "
      "(`rccx`, some controlled composite gates) and translates `mcx_vchain` incorrectly. "
      "Before handing a circuit to TKET, every instruction is converted on its own and "
      "compared exactly with the original; instructions that fail are replaced by their "
      "Qiskit definition (recursively). Both TKET variants (with and without qrig) go "
      "through the same step.")
    if errors:
        w("")
        w(f"Runs that did not finish ({len(errors)}): " + "; ".join(
            f"{e['label']} / {e['compiler']} / {e['variant']}: {e['error'].splitlines()[-1][:80]}"
            for e in errors[:12]) + ".")
    w("")
    return summary


CATEGORY = [
    ("search & oracles", ["grover", "grover_sat", "lib_grover", "membership_oracle", "dj", "bv"]),
    ("arithmetic", ["cdkm_ripple_carry_adder", "draper_qft_adder", "full_adder", "half_adder",
                    "hrs_cumulative_multiplier", "modular_adder", "multiplier",
                    "rg_qft_multiplier", "vbe_ripple_carry_adder", "comparator",
                    "weighted_adder", "incrementer", "shor_modadd", "hamming_weight"]),
    ("data loading & block encoding", ["qrom", "lcu_select", "state_prep", "poly_rotation",
                                       "multiplexer"]),
    ("Fourier & phase estimation", ["qft", "qftentangled", "qpeexact", "qpeinexact", "ae",
                                    "hhl"]),
    ("simulation & walks", ["ising_trotter", "qwalk"]),
    ("variational, ML & finance", ["qaoa", "qnn", "vqe_real_amp", "vqe_su2", "vqe_two_local",
                                   "bmw_quark_cardinality", "bmw_quark_copula"]),
    ("states & primitives", ["ghz", "graphstate", "wstate", "randomcircuit", "swap_test"]),
]


def category_of(c):
    if c["suite"] == "pattern" and c["family"] != "multiplexer":
        return "control patterns"
    for name, fams in CATEGORY:
        if c["family"] in fams:
            return name
    return "other"


def geomean(xs):
    xs = [x for x in xs if x > 0]
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else float("nan")


def category_section(w, st):
    """Results grouped by application category (circuit diversity)."""
    cats = {}
    for c in st.ok:
        cats.setdefault(category_of(c), []).append(c)
    order = [n for n, _ in CATEGORY] + ["control patterns", "other"]
    rows = []
    for name in order:
        cs = cats.get(name)
        if not cs:
            continue
        fams = sorted({c["family"] for c in cs})
        r = [name, len(cs), len(fams), sum(1 for c in cs if st.pc[c["label"]]["changed"])]
        for m in ("depolarizing", "heron_all2all"):
            a = sum(st.m(c["label"], m)["qiskit"]["twoq"] for c in cs)
            b = sum(st.m(c["label"], m)["qrig"]["twoq"] for c in cs)
            fe = sum(1 for c in cs if st.m(c["label"], m)["qrig"]["twoq"]
                     < st.m(c["label"], m)["qiskit"]["twoq"])
            mo = sum(1 for c in cs if st.m(c["label"], m)["qrig"]["twoq"]
                     > st.m(c["label"], m)["qiskit"]["twoq"])
            r.append(f"{fe}/{mo}; {pct((b - a) / a if a else 0, 1)}")
        best = None
        for c in cs:
            x = st.m(c["label"], "heron_all2all")
            a, b = x["qiskit"]["twoq"], x["qrig"]["twoq"]
            if a and b < a and (best is None or b / a < best[1]):
                best = (c["label"], b / a, a, b)
        r.append(f"{best[0]} ({best[2]} → {best[3]})" if best else "–")
        rows.append(r)
    w("## 4.1 Results by application category")
    w("")
    w("To show that the effect is not limited to one algorithm (e.g. Grover), the circuits "
      "are grouped by what they are used for. *fewer/more*: circuits with fewer / more "
      "two-qubit gates after qrig; the percentage is the change of the category total.")
    w("")
    w(table(["category", "circuits", "families", "rewritten", "CX target: fewer/more; total",
             "CZ: fewer/more; total", "largest CZ reduction"], rows))
    w("")
    nong = [c for c in st.ok if category_of(c) not in ("search & oracles", "control patterns")]
    nb = sum(1 for c in nong if st.m(c["label"], "heron_all2all")["qrig"]["twoq"]
             < st.m(c["label"], "heron_all2all")["qiskit"]["twoq"])
    w(f"Outside search/oracle circuits and the control-pattern circuits, qrig lowers the "
      f"CZ-model two-qubit count on {nb} of {len(nong)} circuits.")
    w("")
    rows = []
    for m in MODELS:
        ch = [st.m(c["label"], m) for c in st.ok]
        ratios = [x["qrig"]["twoq"] / x["qiskit"]["twoq"] for x in ch if x["qiskit"]["twoq"]]
        imp = [r for r in ratios if r != 1.0]
        better = [r for r in ratios if r < 1.0]
        rows.append([MNAME[m], f"{geomean(ratios):.3f}",
                     f"{geomean(imp):.3f}" if imp else "–",
                     f"{100 * statistics.median([1 - r for r in better]):.0f} %" if better else "–",
                     f"{100 * (1 - min(ratios)):.0f} %"])
    w("Per-circuit view (each circuit weighted equally, so a few large circuits cannot "
      "dominate):")
    w("")
    w(table(["target", "geometric mean of 2q ratio, all circuits",
             "geometric mean, circuits whose count changes",
             "median reduction where it drops", "largest reduction"], rows))
    w("")


HEADER_TEX = r"""
\usepackage{etoolbox}
\AtBeginEnvironment{longtable}{\scriptsize}
\usepackage{float}
\let\origfigure\figure
\let\endorigfigure\endfigure
\renewenvironment{figure}[1][2] {\expandafter\origfigure\expandafter[H]} {\endorigfigure}
"""


def make_pdf(md_path):
    hdr = os.path.join(REPORT, ".header.tex")
    with open(hdr, "w") as f:
        f.write(HEADER_TEX)
    pdf = md_path[:-3] + ".pdf"
    cmd = ["pandoc", os.path.basename(md_path), "-o", os.path.basename(pdf),
           "--pdf-engine=xelatex", "-H", hdr, "--toc",
           "-V", "geometry:margin=1.8cm", "-V", "fontsize=10pt",
           "-V", "mainfont=DejaVu Serif", "-V", "sansfont=DejaVu Sans",
           "-V", "monofont=DejaVu Sans Mono", "-V", "colorlinks=true",
           "-V", "columns=200"]
    subprocess.run(cmd, check=True, cwd=REPORT)
    os.remove(hdr)
    print("wrote", pdf)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-pdf", action="store_true")
    ap.add_argument("--study", default="study/study_results.json")
    a = ap.parse_args()
    build(a.no_pdf, a.study)
