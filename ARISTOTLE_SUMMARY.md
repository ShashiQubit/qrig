# Summary of changes for run 7db4273f-21dd-4fe7-ad2f-e9d2a0c3f960
The zip `paper/qrig_paper_overleaf.zip` now includes the results report as a LaTeX file, `qrig_results.tex`.

**Why it was missing:** there was no results `.tex` file in the project before. The report only existed as Markdown (`report/qrig_results.md`) plus a PDF made from it. I converted the current Markdown into a standalone LaTeX document and saved it as `report/qrig_results.tex`. It has the same text, tables, contents page and all five figures.

**What's in the zip now**
- `main.tex`: the paper, unchanged.
- `qrig_results.tex`: the full results report, a separate document. It loads its figures from the same `figures/` folder.
- `figures/`: all five plots. `fig4_noise_type.png` and `fig5_time.png` are no longer unused, because the results report uses them.
- `README.txt`: now explains how to compile the report. In Overleaf, choose Menu → Main document → `qrig_results.tex`, then switch back to `main.tex` for the paper.

**Compiler:** `qrig_results.tex` uses only plain ASCII. Symbols like →, ×, µ and ℚ are written as ordinary LaTeX commands, so no special fonts are needed. It should work with pdfLaTeX (Overleaf's default), XeLaTeX or LuaLaTeX, and it needs no BibTeX.

**Check:** I unpacked the new zip into an empty folder and compiled both files with a XeLaTeX-based engine. pdfLaTeX wasn't available for testing, so the pdfLaTeX route hasn't been tried. `main.tex` gave the same 10-page paper, and `qrig_results.tex` gave an 18-page report. Neither had compile errors or broken `??` references. A few long file names and table cells run slightly into the right margin in the report, but nothing is cut off.

**To rebuild after editing the report:** run `python3 paper/make_results_tex.py`, which needs pandoc, then `python3 paper/make_overleaf_zip.py`.

I also rebuilt the old, out-of-date `report/qrig_results.pdf` from the current report. Your git ignore rules exclude PDFs, so it is in the project folder but not committed. The new `.tex`, both scripts and the updated zip are committed. Only LaTeX files and scripts changed, so there is nothing to build in Lean.

# Summary of changes for run 49a3f832-9057-4807-b63b-5592d0ed45a8
The zip for Overleaf is at `paper/qrig_paper_overleaf.zip`. To use it, go to Overleaf, choose New Project → Upload Project, and select the zip. It should compile without changes.

**What's in the zip**
- `main.tex`: the paper from `paper/qrig_paper.tex`. The only change is the figure path, which now points to `figures/` inside the zip instead of `../report/figures/`. The bibliography is written into the file, so there is no separate bibliography step. The default pdfLaTeX compiler works.
- `figures/`: all five plots from `report/figures/`.
  - `fig1_twoq_all_circuits.png`, `fig2_fidelity.png` and `fig3_noise_scale.png` are Figures 1–3 in the paper.
  - `fig4_noise_type.png` and `fig5_time.png` are included in case you want them, but the text doesn't use them yet.
- `README.txt`: a short note on the main file, the compiler and what each figure is.

**Check:** I unpacked the zip into an empty folder and compiled `main.tex` with a LaTeX engine. It produced the same 10-page paper with all three figures, and there were no broken references (`??`).

**Still in the text:** the red `[TODO: …]` markers for authors, the repository URL and the missing experiments are still there for you to fill in.

**To rebuild the zip** after editing the paper or the plots, run `python3 paper/make_overleaf_zip.py`.

Only the paper bundle was added, so there is nothing to build in Lean. Both files are committed. Because of the repository's `*.zip` ignore rule, I had to add the zip to git explicitly.

# Summary of changes for run ed77da26-162c-4696-a07e-8ac2d841b068
I relabelled the targets as you suggested. The three targets are now called the **CX, CZ and RXX models** everywhere, and the vendor is named only where the calibration numbers are sourced.

**Paper (`paper/qrig_paper.tex`, rebuilt as `paper/qrig_paper.pdf`, still 10 pages)**
- **Section 5.1 (Targets)** now opens with your wording: "All three targets are all-to-all; they differ in native two-qubit gate (CX, CZ, RXX) and noise parameters. The CZ model uses the median FakeTorino calibration; the RXX model uses assumed values." The detailed parameters follow. Heron is mentioned only here, once, as the source of the FakeTorino snapshot. A new sentence says that only the numbers are borrowed: the CZ model is not a model of that device, which is not all-to-all, and its readout error and crosstalk are left out.
- **Tables 2–3:** "CZ (Heron)" and "RXX (ion)" are now "CZ" and "RXX".
- **Sections 5.4–5.5, the Figure 3 caption and the threats-to-validity list:** "Heron model" and "ion" are now "CZ model" and "RXX model". The noise scaling is now described relative to the CZ model's error rates.
- **Topology paragraph:** this one keeps a vendor name, because that run really did use FakeTorino itself: heavy-hex coupling map and per-qubit calibration. I reworded it to say exactly that. The earlier text called it "the same physics" as the CZ model, which was slightly wrong, since the CZ model uses only the medians of that calibration.
- The remaining "IBM" in the PDF is the existing `[TODO]` about a run on real hardware, which really is about IBM hardware.

**Figures and report**
The figure titles come from `python/benchmarks/make_report.py`, so I changed the labels there:
- panel titles now read "CX model", "CZ model" and "RXX model";
- the Figure 3 x-axis now reads "× CZ-model error rates";
- the report's tables, targets text and limitations section use the same labels, with the same opening sentence.

I then regenerated `report/figures/*.png` and `report/qrig_results.md` from the existing result files. Before changing anything, I re-ran the generator unchanged and its output matched the committed files byte for byte. So the new versions differ only in their labels, and no numbers changed. No experiments were re-run.

The internal model identifiers in the benchmark code (such as `heron_all2all`) and the developer notes in `python/benchmarks/` are unchanged. All changes are committed.

# Summary of changes for run fa2d1bb2-19f7-4e14-9fd5-f7e254732186
I checked whether the results are complete enough for a paper and wrote a draft. Everything is in the new `paper/` folder, and the top-level `README.md` now points to it.

**Check of the current state**
- **Lean proofs:** `lake build` passes for the core and all proofs, with no warnings and no `sorry`/`admit`/`axiom`. The main theorems (`peephole_sound`, `unitary_simplifyQ`, `equivExact_iff`, the control equations) use only the standard axioms.
- **Shipped C code:** the committed C in `python/csrc/generated/` is byte-identical to what Lean emits from the current sources, so the code that runs is the code that was proved.
- **Python tests** (with Qiskit 2.5.2, Aer, MQT Bench and QCEC installed): 264 passed, 1 skipped. The skipped test needs the optional in-process library, which a fresh checkout doesn't build.
- **Benchmark numbers were not re-run.** The paper takes them from `report/qrig_results.md` and the JSON result files.

**Verdict (details in `paper/COMPLETENESS.md`):** the results are enough for a tool/artefact paper. For a stronger venue, reviewers are likely to ask for:
1. **A small run on real hardware.** Every result so far is classical simulation.
2. **A comparison with another verified optimiser**, such as VOQC; PyZX would be a useful unverified baseline.
3. **A per-rule ablation**, plus how results depend on the 128-gate window.
4. **Spread or confidence intervals on the fidelities.** These are currently averages over only 3 random inputs.
5. **A response to the "straw man" concern.** The application kernels use textbook constructions without helper qubits, which are more expensive to begin with.

The paper should also state these limits of the formal story:
- The original paper's completeness theorem is not formalised.
- The Python–Qiskit conversion, the parsers and the compilers are trusted, not verified. The conversion also rounds an angle to a nearby simple fraction of π when it is within \(10^{-12}\) of one, so "exact" holds after that rounding.
- The kernel proofs are about a Lean model of the Python code; the link to the actual code is a test, not a proof.
- The permutation synthesis is not proved to always succeed; its output is checked when it runs.

Smaller issues in the existing material:
- `report/qrig_results.pdf` is out of date; the Markdown version is current.
- One cross-reference in the report points to the wrong section: the seed spread is in 8.1, not 6.
- "Never worse" is not guaranteed: two circuits end up with more two-qubit gates on the IBM-like model. A simple guard that keeps the cheaper of the two compiled circuits would fix this.
- The seed-robustness test tells you almost nothing on all-to-all targets, because there is no routing step.

**Draft paper:** `paper/qrig_paper.tex`, compiled to `paper/qrig_paper.pdf` (10 pages). Sections:
- abstract and introduction with contributions;
- background, including a table of equations (a)–(h) next to their Lean theorems;
- architecture (Lean core, generated C, Python/Qiskit pass, the optimiser's rewrite rules) with a usage snippet I ran against Qiskit 2.5.2;
- what is and is not verified;
- evaluation, organised as six research questions: correctness, gate counts, fidelity, robustness, other compilers, and time / T-count;
- threats to validity, related work, and conclusion.

It uses three figures from `report/figures/` and a hand-picked bibliography of well-known references, which you should check. Every figure in the text comes from the existing report, and the two regressions and the mixed T-count are reported openly. Red `[TODO]` markers show where your input is needed: authors, repository URL, and the missing hardware, ablation, statistics and VOQC items.

No Lean code changed this session, so there are no new Lean build results. All files are committed.

# Summary of changes for run d7169d49-09ef-4aeb-ac93-3215578f021e
The previous session had already written Lean proofs for some of the study's application kernels and metrics (`QrigProofs/Study/`). It stopped before documenting or testing them. This session finished that work. `lake build` passes with no `sorry` and no warnings, and the main theorems use only the standard axioms.

**What the `Study/` proofs establish**
- `Reversible.lean`:
  - the incrementer adds 1 mod \(2^n\) (`incrementer_spec`);
  - the Hamming-weight kernel ends with the number of `1` inputs in its counter (`hamming_weight_correct`);
  - the membership oracle flips its target exactly when the input is in the set (`memberOracle_spec`);
  - QROM XORs `table[address]` into the data register (`qrom_spec`);
  - colour change (equation (d)) holds on basis states (`run_xconj`).
- `Draper.lean`: the phase angles of the Draper adder in `shor_modadd` take \(\mathrm{QFT}|x\rangle\) to \(\mathrm{QFT}|(x+a) \bmod 2^n\rangle\) under Qiskit's `QFTGate` convention (`phiAdd_correct`). The angle formula used before a fix made during the study does not (`phiAddOld_wrong`).
- `Metrics.lean`:
  - removing gates never lowers the estimated success probability (ESP);
  - using no more 1-qubit and no more 2-qubit gates gives an ESP at least as high at every noise strength, and both counts are needed for this;
  - the shot saving equals the square of the fidelity ratio;
  - the per-circuit geometric-mean ratio is at most 1 when no circuit gets worse.

**What this session added**
- **New test `python/tests/test_kernels.py`.** The kernel proofs are about a Lean model written to match `benchmarks/app_circuits.py`, not about the Python code itself. This test closes that gap: it runs the actual Qiskit circuits on every basis state and checks them against the same specifications. It covers the incrementer, Hamming weight, membership oracle, QROM, and the Draper adder for every constant and both signs. All 27 cases pass. The full suite gives 264 passed and 1 skipped (Qiskit 2.5.2, with MQT Bench installed).
- **Documentation.**
  - `python/README.md`'s table of proved results now lists the study theorems, with the model-versus-code caveat.
  - The top-level `README.md` describes `QrigProofs/Study/`.
  - The report generator gained a section 3.2 on these proofs, and `report/qrig_results.md` was regenerated with it. The report's test count was updated to 265.
- **Properties table.** Seven entries were added and marked proved: the incrementer, Hamming weight, membership oracle, QROM, Draper adder, ESP robustness and ESP monotonicity.
- **Repository fixes.** The bundled `qrig-core` executable had again been stored in git without its executable permission; it is now committed as executable. Python cache files are no longer tracked and are now in `.gitignore`.

**Caveats**
- **The PDF report is out of date.** `report/qrig_results.pdf` was not rebuilt because this environment has no XeLaTeX, so it lacks the new section 3.2. The file is also excluded from git by the existing `*.pdf` rule. Running `python3 benchmarks/make_report.py` in `python/` on a machine with pandoc and XeLaTeX regenerates it.
- **No measurements were re-run.** The simulation and benchmark figures in the report are unchanged, and they remain classical simulations that are not checked in Lean.

All work is committed.

# Summary of changes for run 4d7b240c-7724-4d1d-bff9-efac55dcf674


## Suggested follow-up

I reached this run’s time limit. Send “continue” to pick up where I left off.

# Summary of changes for run 320e3888-3d5a-4954-b0d3-11f1fd80d62e
I added two all-to-all noise models to the noise study, so the comparison no longer depends on a device's wiring. Everything here is Qiskit Aer simulation (Qiskit 2.5.2, Aer 0.17.2). Nothing ran on hardware, and none of this is covered by the Lean proofs.

**What was added** in `python/benchmarks/noise_benchmark.py`:
- **`heron_all2all`**: IBM Heron physics without the heavy-hex layout. Every qubit and pair gets the *median* FakeTorino calibration: CZ error 0.419 %, 1-qubit error 0.027 %, CZ 68 ns, 1-qubit 32 ns, T1 185 µs, T2 138 µs, plus decay while qubits sit idle. It has the same physics as the existing `ibm_torino` model, so comparing the two isolates the effect of the topology.
- **`trapped_ion`**: an all-to-all ion-trap-style device like IonQ's, with native gates {rxx, rz, sx, x}. Its settings are **my assumed round numbers, not a vendor calibration**: rxx error 0.5 %, 1-qubit error 0.03 %, rxx 600 µs, 1-qubit 100 µs, T1 100 s, T2 1 s. The rxx error is assumed not to depend on the rotation angle. You can change all of these with `--ion-p2/--ion-p1/--ion-d2/--ion-d1/--ion-t1/--ion-t2` (times in seconds).
- As before, each circuit is compiled once by Qiskit alone and once by qrig followed by Qiskit, and both results are simulated. Each run checks that the two versions are equivalent when there is no noise.

**Results** (share of the output error removed by qrig; Heron all-to-all / trapped ion):

| circuit | Heron all-to-all | trapped ion |
|---|---|---|
| Grover 4 | 22 % | 15 % |
| Grover 5 | 4 % | 13 % (fidelity ×1.17) |
| multipliers, 8 qubits | 13 % | 15 % |
| multipliers, 12 qubits | 5–6 % (fidelity ×1.5) | 9 % (fidelity ×1.55) |
| multiplier, 16 qubits | fidelity ×3.3 | fidelity ×3.9 |
| multiplexers, 3 / 4 / 5 controls | 88 % / 26 % / 10 % (fidelity up to ×7) | 89 % / 27 % / 10 % |
| four repeated C³(T) gates | 79 % | 78 % |
| compute/uncompute, C³H·C³V·C³V†·C³H | 100 % | 100 % |

**Findings:**
- **Grover 5's small loss on Torino (−2 %) was caused by the wiring, not by qrig.** With the same physics but all-to-all connectivity, qrig removes 4 % of the error, and 13 % on the ion model.
- **Without SWAPs, both versions need about half the two-qubit gates** (multiplier 8: 115 against 229). Fidelities stay higher, so the error qrig removes on 8–12-qubit circuits is larger than on Torino.
- **The two all-to-all models agree closely**, even though their gate speeds differ by about 10,000×. The gain therefore comes from the removed gates, not from one platform's details.
- **Two small exceptions.** On the Heron all-to-all model, Grover 7 comes out marginally lower with qrig (fidelity 0.0162 → 0.0153), but both outputs are essentially pure noise there. The control circuit `hrs_cumulative_multiplier`, where qrig removes nothing, stays within ±3 %.

**Files:**
- `benchmarks/NOISE.md` has a new all-to-all section with the table, the topology comparison and the caveats, plus updated method and run instructions.
- New figure `benchmarks/noise_all_to_all.png`; `noise_benchmark.png`, `noise_results.md` and `noise_results.json` now cover all four models.
- The script's docstring, `python/README.md` and `benchmarks/README.md` are updated.
- `tests/test_noise.py` passes (3 tests), and pyflakes reports no problems.
- To rerun only the new models: `python3 benchmarks/noise_benchmark.py --models heron_all2all trapped_ion`. A full run of all four models takes about 75 minutes on 8 cores (estimated).

Everything is committed. There were no Lean changes, so no Lean build targets apply.

# Summary of changes for run dc876ec8-40b7-40ab-9417-5440c87ef289
I built the MQT benchmarking pipeline for `qrig`: MQT Bench circuits go into a Qiskit `DAGCircuit`, through the control-equation optimiser (written in Lean and compiled to C), then reduction statistics are recorded and MQT QCEC checks equivalence. The Lean project builds with `lake build`, contains no `sorry`, and uses only the standard axioms. The Python tests pass (235 in total, 85 of them for the new DAG pass).

**New Lean code**
- `Qrig/Core/Peephole.lean` is the optimiser core; this is the code that gets compiled to C. It turns each circuit into a list of multiply-controlled one-qubit gates. It then applies these rules:
  - fusion and cancellation of gates with the same controls (equations (a) and (b));
  - complementarity, where `C⁰_w(f)` followed by `C¹_w(f)` becomes `f` with the control `w` removed (equation (e));
  - commutation, both for gates whose controls contradict (equation (f)) and for gates that share wires only as controls or diagonal targets;
  - colour change, where a NOT gate is pushed through a gate and flips that gate's control colour (equation (d)).
- The optimiser is callable from Python as `qrig` version 1.1.0.
- **Proved:** `QrigProofs/Peephole.lean` and `QrigProofs/PeepholeOps.lean` prove the optimiser preserves semantics.
  - `peephole_sound`: for the gate set used (X, Y, H, SX, SX†, and phase/RZ/RX/RY with rational multiples of π, plus arbitrary opaque gates), the optimised gate list acts on every state vector exactly as the original does.
  - The generic theorems `combine_sound`, `commutes_sound`, `xconj_sound` and `optimize_sound` are proved too.
- The proofs cover the Lean core only. The Python conversion between Qiskit DAG nodes and gate lists is ordinary code: it is tested against Qiskit's `Operator` and checked by QCEC, not proved.

**Python**
- `python/qrig/dag.py` provides `optimize_dag`, `optimize_circuit`, and a Qiskit pass `QrigControlEquations` that stores per-rule statistics in `property_set["qrig_stats"]`.
- `python/benchmarks/mqt_quickstart.py` is your four-step script, with the MQT API calls corrected and a working optimiser in step 2.
- `python/benchmarks/mqt_pipeline.py` is the full run. It exits with an error if any circuit is found **not** equivalent.
- `python/examples/dag_rule_complementarity.py` shows equation (e) written as a DAG node-replacement rule.
- `python/benchmarks/MQT_PIPELINE.md` documents everything. Install the optional dependencies with `pip install qiskit mqt.bench mqt.qcec` (or the `mqt` extra).

**Your two questions**
1. **Pattern matching or a symbolic matrix?** Pattern-matching rewrite rules. Matrices appear only in the Lean proofs, never while optimising. Each new gate is merged with an earlier one if a rule applies. It is moved backwards only past gates it provably commutes with, within a 128-gate window. A NOT gate is pushed forward and flips the control colours of the gates it passes (equation (d)). Gates are never reordered unless a merge results. Equations (c), (g) and (h) are proved in Lean but not used as rewrite rules: the flat gate representation handles (c) and (h) automatically, and (g) only rewrites swaps.
2. **Do you need help writing a DAG rule for Equation (e)?** No. The pass already applies equation (e) across whole DAGs, and the example file shows how a single hand-written node-replacement rule would look.

**Results** (74 circuits with `--scale`, up to 128 qubits; full tables in `python/benchmarks/mqt_results.md` and `.json`)
- **Equivalence:** no circuit was found non-equivalent. QCEC proved the qrig output equivalent to the benchmark for 72 of 74 circuits; the other two (the 32-qubit qft and qpeexact) hit the time limit. Compared with the compiled circuits, QCEC proved 66, gave no answer on 2, and timed out on 6. Qiskit's `Operator` confirmed equality on 37.
- **Reduction:** after Qiskit's O3 compilation, adding qrig cut the total CX count from 37058 to 32565 (−12.1%). It was fewer on 12 circuits (mainly grover, through colour change, and the multipliers) and worse on none.
- **Speed:** qrig took at most 0.06 s per circuit.

**Two things to know about QCEC**
- It reports `equivalent_up_to_global_phase` even for circuits that are exactly equal, so the script accepts both statuses. Raw versus Qiskit O3 output gets the same report.
- Its built-in timeout option was not honoured, so the pipeline enforces its own time limit (`--qcec-timeout`, default 120 s).

**How to run** (from `python/`)
- `python3 benchmarks/mqt_quickstart.py grover 5`
- `python3 benchmarks/mqt_pipeline.py [--scale] [--benchmarks …] [--sizes …]`
- `python3 -m pytest -q tests/test_dag.py`

# Summary of changes for run 67ab63db-81f5-496a-a5eb-11e287f689e2
Yes, it's a fair question if you ask it the way you suggested: add qrig as a pre-pass in front of Qiskit's own optimiser and compare with Qiskit alone. That is what the new benchmark does. The plot is `python/benchmarks/benchmark.png` and the explanation is `python/benchmarks/README.md`. It is only part of the story: the paper gives a complete set of equations for controlled circuits, not an optimisation algorithm, and qrig's main extras (exact equivalence checking, and rewrites proved correct in Lean) are guarantees rather than speed-ups.

**Setup.** "Before" is Qiskit 2.5.2's level-3 pipeline compiling to CNOT and one-qubit gates. "After" is the same pipeline with qrig's `QrigOptimize` pass run first. qrig has to go first: once Qiskit has compiled a circuit, the controlled-gate structure qrig uses is gone. Every compiled circuit was checked equal to the original with Qiskit's `Operator` before its gates were counted.

**Results (CNOT count, Qiskit alone → with qrig first):**

| workload | before → after |
|---|---|
| random controlled Clifford+T circuits | 213.6 → 214.2 (no real change) |
| Grover, Qiskit library, 5 qubits | 144 → 144 (no change) |
| multiplexer with repeated branches, 4 controls | 602 → 288 (−52%) |
| four repeated 3-controlled T gates | 80 → 14 (−82%) |
| compute then uncompute (`U` followed by `U⁻¹`) | 314 → 223 (−29%) |
| `C³(H) C³(V) C³(V†) C³(H)` | 64 → 0 (−100%) |

- **Where it helps:** circuits built from multi-controlled gates that sit next to each other and can be merged by the paper's control equations. Qiskit does not merge these; for example, two Toffoli gates in a row still cost 12 CNOTs after Qiskit's level 3. For multiplexers the saving holds at every size from 2 to 6 controls (about half or more).
- **Where it does nothing:** random or already tidy circuits.
- **Where it is worse:** qrig's permutation synthesis (the paper's Gray-code construction) needs 10–100× more CNOTs than Qiskit's generic synthesis. It gives a circuit that is correct by construction, not a small one.
- **Cost:** the qrig pre-pass takes 0.1 s or less on these sizes, up to about 2–3× Qiskit's own compile time. qrig's exact equivalence check grows about 4× per qubit and is about 15× slower than Qiskit's floating-point check at 6 qubits.

**Caveats:**
- Rows 3–6 were chosen because they contain the patterns qrig targets. They show which kinds of circuit benefit, not how common those circuits are.
- Both pipelines compile circuits as full unitaries. By default Qiskit may borrow idle qubits on the assumption that they start in |0⟩, and its output then can't be checked as a unitary. That is Qiskit's documented behaviour, not a bug in either tool.
- Timings come from one run on one machine.

**Also fixed:** the bundled `qrig-core` executable had lost its executable permission in git, so `import qrig` failed on a fresh checkout. The permission is restored, and the loader now repairs it automatically if it is lost again. After that fix, the existing test suite passes here (149 passed, 1 skipped).

To rerun: `cd python && python3 benchmarks/benchmark.py` (needs `qiskit` and `matplotlib`, about 1–2 minutes). It rewrites the plot, `results.md` and `results.json`. No Lean code changed this session, and none of these numbers are Lean-verified; they are measurements.

# Summary of changes for run 86e430f1-a81b-418c-b59e-0529613ea3a4
`qrig` is finished: you can `import qrig` in Python, and the actual computation runs in C code that the Lean 4 compiler generated from Lean code with machine-checked proofs. `lake build` passes with no errors, warnings or `sorry`. `#print axioms` on the main theorems shows only the standard axioms. The Python test suite (150 tests, checked against Qiskit 2.5.2) passes on both backends, and `pip install ./python` works in a fresh virtual environment.

**How it is built**
- `Qrig/` is the Lean code that runs. It has no Mathlib dependency and covers:
  - the circuit language of the paper's Definition 6 and its semantics `den` (the functor A : cP → P₂);
  - exact arithmetic in ℚ(ω), exact simulation, unitaries and equivalence checking;
  - Gray codes and permutation synthesis (Theorem 9);
  - a circuit optimiser driven by the control equations;
  - one exported C entry point.
- `python/csrc/generated/` holds the C code Lean emitted; it is committed.
- `python/qrig/` is the Python front end. It builds circuits with `>>`, `+`, `C0`/`C1`, named gates and helpers, converts to and from Qiskit (`to_qiskit`, `from_qiskit`), and provides a Qiskit optimisation pass (`QrigOptimize`). `qrig.paper` builds the constructions from the paper: equations (a)–(h), Sleator–Weinfurter, Gray transpositions and equation (11).
- There are two backends: an in-process `libqrig.so`, which needs a Lean installation, and a self-contained executable, `qrig-core`, used automatically otherwise. Only `qrig-core` is committed to git, so a fresh clone uses that one until `python/build_native.py` is run.

**What is proved in Lean** (`QrigProofs/`)
- All eight control equations (a)–(h) of Figure 1 hold in `den`, for any base gates that act locally.
- The fast array evaluator equals `den`.
- `simulate`, `unitary` and the exact equivalence check are correct; equivalence is decided exactly.
- Every circuit the synthesiser returns uses only NOT/controlled-NOT gates and implements the requested permutation.
- The Gray code map is a bijection, and consecutive codewords differ in exactly one bit.
- The optimiser preserves semantics in general (`simplify_sound`), and the concrete version behind `qrig.simplify` preserves the exact unitary (`unitary_simplifyQ`).
- ℚ(ω) arithmetic forms a commutative ring.

These results are listed in the Properties table and in `python/README.md`.

**What is not formally proved (tested only)**
- The paper's completeness theorem (that every valid equation follows from (a)–(h)) is not formalised; `qrig` decides equality by computing semantics instead.
- The synthesiser is not proved to always succeed. Its output is checked at run time before being returned. The tests show it succeeds on all 40 320 three-bit permutations and on random 4- and 5-bit ones.
- The text format passed between Python and C, `dagger`, equivalence up to phase, the C glue code and the Qiskit bridge are ordinary tested code.
- The Lean compiler and the C compiler are trusted.

**What the tests cover**: every named gate; every control pattern and wire placement up to 4 qubits; swaps and Fredkin gates; random circuits compared with Qiskit's `Operator` and `Statevector`; importing Qiskit circuits; `dagger` against Qiskit's `inverse`; the optimiser on random Qiskit circuits up to 5 qubits; the paper's identities; error handling; serialisation round trips; concurrent calls; and a 12-wire multi-controlled NOT.

**Usage**: `cd python && python3 build_native.py` rebuilds the C core from Lean; `python3 -m pytest -q tests` runs the tests; `pip install .` installs the package. The top-level `README.md` describes the layout, and `python/README.md` covers the API and the proved/not-proved lists.