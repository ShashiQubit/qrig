#!/usr/bin/env python3
"""How much noise does qrig remove?  Noisy-simulation benchmark.

The point of removing controlled gates is to lower the effect of noise. This script
measures that directly, for the circuits where qrig reduces the gate count:

* **Qiskit alone**:  Qiskit's level-3 pipeline compiles the circuit.
* **qrig + Qiskit**: the verified DAG pass ``qrig.dag.QrigControlEquations`` runs
  first, then the *same* Qiskit level-3 pipeline.

Both compiled circuits are simulated with Qiskit Aer under four noise models (three of
them with all-to-all connectivity, so that routing/topology does not bias the result):

``depolarizing``
    all-to-all connectivity, basis ``{cx, rz, sx, x}``; depolarizing error ``p2`` after
    every CX and ``p1 = p2/10`` after every ``sx``/``x`` (``rz`` is virtual and exact).
    Default ``p2 = 0.3%`` (roughly today's best superconducting devices).
``ibm_torino``
    the calibration snapshot of the 133-qubit IBM Heron device ``FakeTorino`` shipped
    with ``qiskit-ibm-runtime``: its heavy-hex coupling map (so Qiskit inserts SWAPs),
    its native gates ``{cz, rz, sx, x}``, per-qubit / per-pair gate errors and gate
    durations, plus T1/T2 relaxation during *idle* periods (the circuit is scheduled
    ALAP and every idle slot becomes a thermal-relaxation channel of that length).
    Readout error is not included (both variants measure the same qubits).
``heron_all2all``
    the same Heron physics without the heavy-hex layout: an all-to-all CZ target whose
    every qubit/pair carries the *median* FakeTorino calibration (errors, durations,
    T1/T2), idle relaxation as for ``ibm_torino``.
``trapped_ion``
    an all-to-all trapped-ion-like device, basis ``{rxx, rz, sx, x}``, with *assumed*
    parameters (``ION_DEFAULTS``: rxx error 0.5%, 1q error 0.03%, rxx 600 us, 1q 100 us,
    T1 100 s, T2 1 s; override with ``--ion-p2/--ion-p1/--ion-d2/--ion-d1/--ion-t1/
    --ion-t2``, times in seconds). The rxx error is taken as independent of the angle.

Metrics (for each case and model, both variants):

``F``   state fidelity  <psi_ideal| rho_noisy |psi_ideal>, averaged over random
        product-state inputs (prepared noiselessly), i.e. how close the noisy output
        state is to the exact one.
``P``   task success: for a fixed classical input (Grover: |0...0>; arithmetic
        circuits: a random basis state), the Hellinger fidelity between the noisy and
        the ideal output distribution. For a deterministic output this is simply the
        probability of reading the correct answer.
``ESP`` estimated success probability  prod_g (1 - e_g)  from the gate error rates
        (analytic, used for the error-rate sweep plot).

Derived: *infidelity reduction* ``1 - (1 - F_qrig) / (1 - F_qiskit)`` (the fraction of
the noise-induced error removed by qrig) and *fidelity gain* ``F_qrig / F_qiskit``.

Density-matrix simulation is exact; above ``--dm-max`` active qubits Aer quantum
trajectories (``--shots`` statevector samples) are used and a standard error is given.
Correctness checks: the ideal output distributions of both compiled variants must
agree with each other and (up to 12 qubits) with Qiskit's ``Statevector`` of the
original benchmark, otherwise the script stops.

Usage (from ``python/``)::

    python3 benchmarks/noise_benchmark.py            # default suite, 4 models (~75 min on 8 cores)
    python3 benchmarks/noise_benchmark.py --quick    # smoke test (~1 min)
    python3 benchmarks/noise_benchmark.py --scale    # + grover 11 (slow)

Writes ``noise_results.md``, ``noise_results.json``, ``noise_benchmark.png``,
``noise_all_to_all.png``.
Requires ``pip install qiskit qiskit-aer qiskit-ibm-runtime mqt.bench matplotlib``.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import platform
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, HERE)

import numpy as np  # noqa: E402
import qiskit  # noqa: E402
from qiskit import QuantumCircuit  # noqa: E402
from qiskit.quantum_info import Statevector  # noqa: E402
from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager  # noqa: E402

try:
    import qiskit_aer
    from qiskit_aer import AerSimulator
    from qiskit_aer.noise import NoiseModel, depolarizing_error, thermal_relaxation_error
    from qiskit_aer.noise.device import basic_device_gate_errors
except ImportError:  # pragma: no cover
    sys.exit("qiskit-aer is required: pip install qiskit-aer")

import qrig  # noqa: E402
from qrig import H, T, V, Vdg, controlled_on  # noqa: E402
from qrig.dag import optimize_circuit  # noqa: E402

SEED = 20260929
ONE_Q = ("sx", "x")          # noisy one-qubit gates (rz is a virtual frame change)
TWO_Q = ("cx", "cz", "ecr", "rxx")


# ============================================================================ workloads
def mqt_circuit(name: str, n: int) -> QuantumCircuit:
    from mqt.bench import BenchmarkLevel, get_benchmark
    from mqt_pipeline import expose
    qc = expose(get_benchmark(name, BenchmarkLevel.ALG, n))
    return qc.remove_final_measurements(inplace=False)


def multiplexer(rng: random.Random, k: int) -> QuantumCircuit:
    """Uniformly controlled gate (one branch per control pattern, Gray-code order,
    branches drawn from {H, H, H, T}); same construction as ``benchmark.py``."""
    n = k + 1
    parts = []
    for g in qrig.gray_code(k):
        u = rng.choice([H, H, H, T])
        ctrls = [(j, bool((g >> (k - 1 - j)) & 1)) for j in range(k)]
        parts.append(controlled_on(u, ctrls, [k], n))
    return qrig.seq(*parts).to_qiskit()


_NAMED = {"h": qrig.H, "s": qrig.S, "sdg": qrig.Sdg, "t": qrig.T, "tdg": qrig.Tdg,
          "z": qrig.Z, "y": qrig.Y, "sx": qrig.V, "sxdg": qrig.Vdg, "x": qrig.X}


def random_controlled(rng: random.Random, n: int, length: int) -> qrig.Circuit:
    parts = []
    for _ in range(length):
        g = _NAMED[rng.choice(list(_NAMED))]
        k = rng.randint(0, min(3, n - 1))
        wires = rng.sample(range(n), k + 1)
        parts.append(controlled_on(g, [(w, rng.random() < 0.5) for w in wires[:k]],
                                   [wires[k]], n))
    return qrig.seq(*parts)


def synthetic_cases():
    rng = random.Random(SEED)
    c3 = [(0, True), (1, True), (2, True)]
    cu = random_controlled(rng, 4, 30)
    return [
        ("multiplexer (3 controls)", multiplexer(rng, 3)),
        ("multiplexer (4 controls)", multiplexer(rng, 4)),
        ("multiplexer (5 controls)", multiplexer(rng, 5)),
        ("C3(T) x4", qrig.seq(*[controlled_on(T, c3, [3], 4)] * 4).to_qiskit()),
        ("compute/uncompute U;U^-1", (cu >> qrig.dagger(cu)).to_qiskit()),
        ("C3(H);C3(V);C3(V^-1);C3(H)",
         qrig.seq(controlled_on(H, c3, [3], 4), controlled_on(V, c3, [3], 4),
                  controlled_on(Vdg, c3, [3], 4), controlled_on(H, c3, [3], 4)).to_qiskit()),
    ]


# MQT Bench circuits where qrig reduced the CX count in mqt_results.md
MQT_CASES = [("grover", 4), ("grover", 5), ("grover", 7), ("grover", 9),
             ("multiplier", 8), ("multiplier", 12), ("multiplier", 16),
             ("rg_qft_multiplier", 8), ("rg_qft_multiplier", 12),
             ("hrs_cumulative_multiplier", 5), ("hrs_cumulative_multiplier", 9)]
SCALE_CASES = [("grover", 11)]
QUICK_CASES = [("grover", 4), ("multiplier", 8)]


# ============================================================================ compiling
# Representative trapped-ion parameters (assumptions, not a vendor calibration; override
# on the command line). All-to-all connectivity, Molmer-Sorensen type two-qubit gate.
ION_DEFAULTS = {"p2": 5e-3, "p1": 3e-4, "d1": 100e-6, "d2": 600e-6, "t1": 100.0, "t2": 1.0}

MODEL_TITLES = {
    "depolarizing": "all-to-all, pure depolarizing gate noise",
    "heron_all2all": "all-to-all, IBM Heron median calibration (gate errors + T1/T2 idle)",
    "trapped_ion": "all-to-all, trapped-ion-like parameters (gate errors + T1/T2 idle)",
    "ibm_torino": "IBM Torino heavy-hex (routing, per-qubit calibration, T1/T2 idle)",
}
ALL_TO_ALL = ("depolarizing", "heron_all2all", "trapped_ion")


class Model:
    """A compilation target plus a noise model.

    ``depolarizing``   all-to-all, {cx, rz, sx, x}, depolarizing gate noise only.
    ``heron_all2all``  all-to-all, {cz, rz, sx, x}, uniform gate errors / durations and
                       T1/T2 = the *median* values of the FakeTorino calibration; the
                       same device physics as ``ibm_torino`` without its topology.
    ``trapped_ion``    all-to-all, {rxx, rz, sx, x}, uniform parameters ``ION_DEFAULTS``.
    ``ibm_torino``     FakeTorino itself: heavy-hex routing and per-qubit calibration.

    For the uniform models every gate gets a depolarizing error equal to its gate error,
    and every idle period a thermal-relaxation channel (circuits are scheduled ALAP).
    """

    def __init__(self, name: str, p2: float = 3e-3, ion: dict | None = None):
        self.name = name
        self.backend = None
        self.twoq = "cx"
        self.p2, self.p1 = p2, p2 / 10
        self._targets = {}
        if name == "depolarizing":
            pass
        elif name == "ibm_torino":
            from qiskit_ibm_runtime.fake_provider import FakeTorino
            self.backend = FakeTorino()
            self.twoq = "cz"
            self.dt = self.backend.dt
            self.gate_errors = basic_device_gate_errors(target=self.backend.target)
            self.t1 = [self.backend.qubit_properties(q).t1 for q in range(self.backend.num_qubits)]
            self.t2 = [min(self.backend.qubit_properties(q).t2, 2 * self.t1[q])
                       for q in range(self.backend.num_qubits)]
        elif name == "heron_all2all":
            from qiskit_ibm_runtime.fake_provider import FakeTorino
            b = FakeTorino()
            tg = b.target

            def med(gate, attr):
                return float(np.median([getattr(v, attr) for v in tg[gate].values()
                                        if v is not None and getattr(v, attr)]))
            t1 = float(np.median([b.qubit_properties(q).t1 for q in range(b.num_qubits)]))
            t2 = float(np.median([min(b.qubit_properties(q).t2, 2 * b.qubit_properties(q).t1)
                                  for q in range(b.num_qubits)]))
            self.twoq = "cz"
            self.params = {"p2": med("cz", "error"), "p1": med("sx", "error"),
                           "d2": med("cz", "duration"), "d1": med("sx", "duration"),
                           "t1": t1, "t2": t2}
            self.dt = b.dt
        elif name == "trapped_ion":
            self.twoq = "rxx"
            self.params = dict(ION_DEFAULTS, **(ion or {}))
            self.dt = 1e-7
        else:
            raise ValueError(name)
        if hasattr(self, "params"):
            self.p2, self.p1 = self.params["p2"], self.params["p1"]

    @property
    def uniform(self) -> bool:
        return hasattr(self, "params")

    def target_for(self, n: int):
        """The all-to-all target of a uniform model, sized for an ``n``-qubit circuit."""
        if self.backend is not None:
            return self.backend.target
        if not self.uniform:
            return None
        if n not in self._targets:
            from qiskit.circuit import Delay, Parameter
            from qiskit.circuit.library import CZGate, RXXGate, RZGate, SXGate, XGate
            from qiskit.transpiler import InstructionProperties, Target
            pr = self.params
            t = Target(num_qubits=n, dt=self.dt)
            t.add_instruction(RZGate(Parameter("a")),
                              {(q,): InstructionProperties(0.0, 0.0) for q in range(n)})
            for g in (SXGate(), XGate()):
                t.add_instruction(g, {(q,): InstructionProperties(pr["d1"], pr["p1"])
                                      for q in range(n)})
            g2 = CZGate() if self.twoq == "cz" else RXXGate(Parameter("b"))
            t.add_instruction(g2, {(a, b): InstructionProperties(pr["d2"], pr["p2"])
                                   for a in range(n) for b in range(n) if a != b})
            t.add_instruction(Delay(Parameter("t")), {(q,): None for q in range(n)})
            self._targets[n] = t
        self.t1 = [self.params["t1"]] * n
        self.t2 = [min(self.params["t2"], 2 * self.params["t1"])] * n
        return self._targets[n]

    def pass_manager(self, seed: int, n: int):
        if self.backend is None and not self.uniform:
            return generate_preset_pass_manager(
                optimization_level=3, basis_gates=["cx", "rz", "sx", "x"],
                seed_transpiler=seed, qubits_initially_zero=False)
        return generate_preset_pass_manager(
            optimization_level=3, target=self.target_for(n), seed_transpiler=seed,
            scheduling_method="alap", qubits_initially_zero=False)

    def describe(self) -> str:
        if self.name == "depolarizing":
            return f"p2 = {100 * self.p2:g}%, p1 = {100 * self.p1:g}%, no idle noise"
        if self.name == "ibm_torino":
            return "FakeTorino calibration snapshot (qiskit-ibm-runtime)"
        pr = self.params
        return (f"{self.twoq} error {100 * pr['p2']:.3g}%, 1q error {100 * pr['p1']:.3g}%, "
                f"{self.twoq} {pr['d2'] * 1e6:.3g} µs, 1q {pr['d1'] * 1e6:.3g} µs, "
                f"T1 {pr['t1'] * 1e6:.4g} µs, T2 {pr['t2'] * 1e6:.4g} µs")

    # ---------------------------------------------------------------- per-gate errors
    def gate_error(self, name: str, phys) -> float:
        if self.backend is None:
            return self.p2 if name in TWO_Q else self.p1 if name in ONE_Q else 0.0
        props = self.backend.target[name].get(tuple(phys)) if name in self.backend.target else None
        return (props.error or 0.0) if props is not None else 0.0

    def noise_model(self, compact) -> NoiseModel:
        nm = NoiseModel(basis_gates=["cx", "cz", "rxx", "rz", "sx", "x"])
        if self.backend is None:
            nm.add_all_qubit_quantum_error(depolarizing_error(self.p1, 1), list(ONE_Q))
            nm.add_all_qubit_quantum_error(depolarizing_error(self.p2, 2), [self.twoq])
            return nm
        idx = compact.index
        for name, qubits, err in self.gate_errors:
            if name in ("reset", "measure", "id", "delay"):
                continue
            if all(q in idx for q in qubits):
                nm.add_quantum_error(err, name, [idx[q] for q in qubits])
        return nm


class Compact:
    """A compiled circuit restricted to its active qubits, with layout bookkeeping."""

    def __init__(self, t: QuantumCircuit, model: Model):
        bit = {q: i for i, q in enumerate(t.qubits)}
        active = sorted({bit[q] for inst in t.data
                         if inst.operation.name not in ("delay", "barrier")
                         for q in inst.qubits})
        n_log = t.layout._input_qubit_count if t.layout is not None else t.num_qubits
        if t.layout is not None:
            init = t.layout.initial_index_layout(filter_ancillas=True)
            final = t.layout.final_index_layout(filter_ancillas=True)
        else:
            init = final = list(range(t.num_qubits))
        # logical qubits that the compiler left completely idle are still part of the state
        active = sorted(set(active) | set(init[:n_log]) | set(final[:n_log]))
        self.index = {p: i for i, p in enumerate(active)}
        self.phys = active
        self.n = len(active)
        self.n_log = n_log
        self.init = [self.index[p] for p in init[:n_log]]
        self.final = [self.index[p] for p in final[:n_log]]
        self.ideal = QuantumCircuit(self.n)
        self.noisy = QuantumCircuit(self.n)
        self.count_2q = self.count_1q = 0
        self.esp_log = 0.0          # sum log(1 - e_g)
        self.duration = 0.0
        for inst in t.data:
            op, qs = inst.operation, [bit[q] for q in inst.qubits]
            if op.name == "barrier":
                continue
            if any(q not in self.index for q in qs):
                continue            # delay on an unused qubit
            cq = [self.index[q] for q in qs]
            if op.name == "delay":
                scale = {"dt": model.dt, "s": 1, "ms": 1e-3, "us": 1e-6, "ns": 1e-9}
                secs = float(op.duration) * scale[op.unit]
                p = qs[0]
                if secs > 0:
                    self.noisy.append(thermal_relaxation_error(
                        model.t1[p], model.t2[p], secs).to_instruction(), cq)
                continue
            self.ideal.append(op, cq)
            self.noisy.append(op, cq)
            if op.name in TWO_Q:
                self.count_2q += 1
            elif op.name in ONE_Q:
                self.count_1q += 1
            e = model.gate_error(op.name, qs)
            if e > 0:
                self.esp_log += math.log1p(-e)
        self.depth = self.ideal.depth()
        self.ideal.global_phase = t.global_phase
        self.noisy.global_phase = t.global_phase
        if model.target_for(t.num_qubits) is not None and getattr(t, "_op_start_times", None):
            self.duration = t.estimate_duration(model.target_for(t.num_qubits), unit="s")

    # --------------------------------------------------------------- input states
    def product_state(self, qubit_states) -> np.ndarray:
        """Kronecker product state: logical qubit i in ``qubit_states[i]``, other
        (ancilla) qubits in |0>. Little-endian like Qiskit."""
        per = [np.array([1, 0], dtype=complex) for _ in range(self.n)]
        for i, s in enumerate(qubit_states):
            per[self.init[i]] = np.asarray(s, dtype=complex)
        psi = np.array([1], dtype=complex)
        for s in per:              # qubit n-1 is the most significant
            psi = np.kron(s, psi)
        return psi

    def logical_probs(self, probs: np.ndarray) -> np.ndarray:
        idx = np.arange(len(probs))
        lidx = np.zeros_like(idx)
        for i, c in enumerate(self.final):
            lidx |= ((idx >> c) & 1) << i
        return np.bincount(lidx, weights=probs, minlength=2 ** self.n_log)


def compile_best(qc: QuantumCircuit, model: Model, seeds) -> tuple:
    """Best of several transpiler seeds: the one with the highest estimated success
    probability (fewest / least noisy gates, best qubits), as one would pick in practice."""
    best = None
    for s in seeds:
        t = model.pass_manager(s, qc.num_qubits).run(qc)
        c = Compact(t, model)
        key = (-c.esp_log, c.count_2q, c.depth)
        if best is None or key < best[0]:
            best = (key, t, c)
    return best[1], best[2]


# ============================================================================ simulation
def random_qubit_state(rng: np.random.Generator) -> np.ndarray:
    v = rng.normal(size=2) + 1j * rng.normal(size=2)
    return v / np.linalg.norm(v)


def basis_qubit(b: int) -> np.ndarray:
    return np.array([1, 0] if b == 0 else [0, 1], dtype=complex)


def run_ideal(c: Compact, psi0: np.ndarray) -> np.ndarray:
    qc = QuantumCircuit(c.n)
    qc.set_statevector(psi0)
    qc.compose(c.ideal, inplace=True)
    qc.save_statevector(label="sv")
    sim = AerSimulator(method="statevector")
    return np.asarray(sim.run(qc).result().data(0)["sv"])


def run_noisy(c: Compact, psi0: np.ndarray, noise: NoiseModel, psi_ideal: np.ndarray,
              dm_max: int, shots: int, seed: int):
    """Returns (fidelity, standard error, output probabilities)."""
    if c.n <= dm_max:
        qc = QuantumCircuit(c.n)
        qc.set_density_matrix(np.outer(psi0, psi0.conj()))
        qc.compose(c.noisy, inplace=True)
        qc.save_density_matrix(label="rho")
        sim = AerSimulator(method="density_matrix", noise_model=noise)
        rho = np.asarray(sim.run(qc, seed_simulator=seed).result().data(0)["rho"])
        f = float(np.real(np.vdot(psi_ideal, rho @ psi_ideal)))
        return f, 0.0, np.clip(np.real(np.diag(rho)), 0, None)
    qc = QuantumCircuit(c.n)
    qc.set_statevector(psi0)
    qc.compose(c.noisy, inplace=True)
    qc.save_statevector(label="sv", pershot=True)
    sim = AerSimulator(method="statevector", noise_model=noise)
    svs = sim.run(qc, shots=shots, seed_simulator=seed).result().data(0)["sv"]
    fs, probs = [], np.zeros(2 ** c.n)
    for s in svs:
        s = np.asarray(s)
        fs.append(abs(np.vdot(psi_ideal, s)) ** 2)
        probs += np.abs(s) ** 2
    fs = np.array(fs)
    return float(fs.mean()), float(fs.std(ddof=1) / math.sqrt(len(fs))), probs / len(svs)


def hellinger(p: np.ndarray, q: np.ndarray) -> float:
    return float(np.sum(np.sqrt(np.clip(p, 0, None) * np.clip(q, 0, None))) ** 2)


def evaluate(c: Compact, model: Model, inputs, task_input, args, seed: int) -> dict:
    noise = model.noise_model(c)
    fids, errs = [], []
    for k, states in enumerate(inputs):
        psi0 = c.product_state(states)
        ideal = run_ideal(c, psi0)
        f, e, _ = run_noisy(c, psi0, noise, ideal, args.dm_max, args.shots, seed + k)
        fids.append(f)
        errs.append(e)
    psi0 = c.product_state([basis_qubit(b) for b in task_input])
    ideal = run_ideal(c, psi0)
    _, _, probs = run_noisy(c, psi0, noise, ideal, args.dm_max, args.shots, seed + 99)
    p_ideal = c.logical_probs(np.abs(ideal) ** 2)
    p_noisy = c.logical_probs(probs)
    se = math.sqrt(sum(e * e for e in errs)) / len(errs)
    return {"F": float(np.mean(fids)), "F_se": se, "P": hellinger(p_ideal, p_noisy),
            "ESP": math.exp(c.esp_log), "ESP_log": c.esp_log, "cx": c.count_2q, "oneq": c.count_1q,
            "depth": c.depth, "qubits_active": c.n, "duration_us": c.duration * 1e6,
            "method": "density matrix" if c.n <= args.dm_max else f"{args.shots} trajectories",
            "_p_ideal": p_ideal}


def reductions(a: dict, b: dict, key: str) -> dict:
    ea, eb = 1 - a[key], 1 - b[key]
    return {"infidelity_reduction": (ea - eb) / ea if ea > 1e-12 else 0.0,
            "gain": b[key] / a[key] if a[key] > 0 else float("inf")}


def run_case(label: str, qc: QuantumCircuit, models, args, rng, prev: dict | None = None) -> dict:
    """Simulate one circuit under every model; models already present in ``prev`` (a row
    of an earlier run with the same random inputs) are reused."""
    n = qc.num_qubits
    t0 = time.perf_counter()
    opt, stats = optimize_circuit(qc)
    t_qrig = time.perf_counter() - t0
    inputs = [[random_qubit_state(rng) for _ in range(n)] for _ in range(args.inputs)]
    if label.startswith("grover"):
        task = [0] * n
    else:
        task = [int(rng.integers(2)) for _ in range(n)]
    reference = None
    if n <= 12:
        sv = Statevector.from_label("".join(str(b) for b in reversed(task)))
        reference = sv.evolve(qc).probabilities()
    row = {"case": label, "qubits": n, "t_qrig": t_qrig, "rules": dict(stats.rules),
           "task_input": "".join(map(str, task)), "models": {}}
    for m in models:
        if prev is not None and m.name in prev.get("models", {}):
            row["models"][m.name] = prev["models"][m.name]
            print(f"  {label:32s} {m.name:12s} (from previous run)", flush=True)
            continue
        res = {}
        for variant, circ in (("qiskit", qc), ("qrig", opt)):
            _, c = compile_best(circ, m, args.seeds)
            res[variant] = evaluate(c, m, inputs, task, args, SEED)
        pa, pb = res["qiskit"].pop("_p_ideal"), res["qrig"].pop("_p_ideal")
        if not np.allclose(pa, pb, atol=1e-6):
            raise AssertionError(f"{label}/{m.name}: ideal outputs of the variants differ")
        if reference is not None and not np.allclose(pa, reference, atol=1e-6):
            raise AssertionError(f"{label}/{m.name}: compiled circuit differs from benchmark")
        res["F"] = reductions(res["qiskit"], res["qrig"], "F")
        res["P"] = reductions(res["qiskit"], res["qrig"], "P")
        res["ESP"] = reductions(res["qiskit"], res["qrig"], "ESP")
        row["models"][m.name] = res
        a, b = res["qiskit"], res["qrig"]
        print(f"  {label:32s} {m.name:13s} 2q {a['cx']:6d}->{b['cx']:<6d} "
              f"F {a['F']:.4f}->{b['F']:.4f} ({100 * res['F']['infidelity_reduction']:+.1f}% "
              f"infidelity, x{res['F']['gain']:.2f})  P {a['P']:.4f}->{b['P']:.4f}  "
              f"[{a['method']}]", flush=True)
    return row


# ============================================================================ output
def sweep(rows, model_name="depolarizing"):
    """Analytic ESP ratio vs two-qubit error rate for the depolarizing model."""
    ps = np.logspace(-4, -1.3, 40)
    out = {}
    for r in rows:
        m = r["models"].get(model_name)
        if m is None:
            continue
        a, b = m["qiskit"], m["qrig"]

        def esp(v, p):
            return (1 - p) ** v["cx"] * (1 - p / 10) ** v["oneq"]
        out[r["case"]] = [(float(p), 1 - (1 - esp(b, p)) / (1 - esp(a, p)),
                           esp(b, p) / esp(a, p)) for p in ps]
    return out


def error_events(v: dict) -> float:
    """Expected number of gate-error events per run, lambda = -ln ESP."""
    return -(v["ESP_log"] if "ESP_log" in v else math.log(v["ESP"]))


def events_removed(m: dict) -> float:
    a, b = error_events(m["qiskit"]), error_events(m["qrig"])
    return 1 - b / a if a > 0 else 0.0


def plot(rows, sw, path, p2):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    models = [m for m in MODEL_TITLES if all(m in r["models"] for r in rows)]
    nbar = (len(models) + 1) // 2
    fig = plt.figure(figsize=(17, 5 + nbar * (2 + 0.45 * len(rows))))
    gs = fig.add_gridspec(nbar + 1, 2, height_ratios=[max(2.0, 0.28 * len(rows))] * nbar
                          + [1.9])
    labels = [r["case"] for r in rows]
    y = np.arange(len(rows))
    for j, mn in enumerate(models):
        ax = fig.add_subplot(gs[j // 2, j % 2])
        fa = [r["models"][mn]["qiskit"]["F"] for r in rows]
        fb = [r["models"][mn]["qrig"]["F"] for r in rows]
        ax.barh(y - 0.2, fa, 0.4, color="#9aa5b1", label="Qiskit level 3 alone")
        ax.barh(y + 0.2, fb, 0.4, color="#2b7bba", label="qrig + Qiskit level 3")
        for i, r in enumerate(rows):
            red = r["models"][mn]["F"]
            x = 100 * red["infidelity_reduction"]
            word = f"{x:.0f}% less error" if x >= 0.5 else \
                f"{-x:.0f}% more error" if x <= -0.5 else "error ±0%"
            ax.text(max(fa[i], fb[i]) + 0.02, i, f"{word}, fidelity ×{red['gain']:.2f}",
                    va="center", fontsize=8)
        ax.set_yticks(y)
        ax.set_yticklabels(labels, fontsize=9)
        ax.invert_yaxis()
        ax.set_xlim(0, 1.6)
        ax.set_xticks([0, 0.2, 0.4, 0.6, 0.8, 1.0])
        ax.set_xlabel("state fidelity of the noisy output  (higher is better)")
        ax.set_title(f"{chr(65 + j)}. {MODEL_TITLES[mn]} (simulated)", fontsize=10)
        ax.legend(loc="lower right", fontsize=8)

    ax1 = fig.add_subplot(gs[nbar, 0])
    styles = ["-", "--", ":", "-."]
    changed = [r for r in rows if r["case"] in sw
               and r["models"]["depolarizing"]["qiskit"]["cx"]
               != r["models"]["depolarizing"]["qrig"]["cx"]]
    for k, r in enumerate(changed):
        pts = [pt for pt in sw[r["case"]] if pt[0] <= 0.03]
        ax1.plot([100 * p for p, _, _ in pts], [100 * v for _, v, _ in pts],
                 styles[(k // 10) % 4], color=f"C{k % 10}", label=r["case"])
    ax1.set_xscale("log")
    ax1.set_xlabel("two-qubit gate error p2 in %  (p1 = p2/10)")
    ax1.grid(alpha=0.3)
    ax1.axvline(100 * p2, color="k", lw=0.8, ls=":")
    ax1.set_ylabel("infidelity removed by qrig, %")
    k0 = len(models)
    ax1.set_title(f"{chr(65 + k0)}. Infidelity removed vs gate error, depolarizing model "
                  "(analytic: 1-(1-ESP_qrig)/(1-ESP_qiskit))", fontsize=10)
    ax1.legend(fontsize=7, ncol=2, loc="center right", bbox_to_anchor=(1.0, 0.42))

    ax2 = fig.add_subplot(gs[nbar, 1])
    w = 0.8 / len(models)
    colors = {"depolarizing": "#2b7bba", "heron_all2all": "#5cb85c",
              "trapped_ion": "#9467bd", "ibm_torino": "#d9822b"}
    for j, mn in enumerate(models):
        vals = [100 * events_removed(r["models"][mn]) for r in rows]
        ax2.bar(y + (j - (len(models) - 1) / 2) * w, vals, w, color=colors[mn],
                label=mn)
    ax2.axhline(0, color="k", lw=0.8)
    ax2.set_xticks(y)
    ax2.set_xticklabels(labels, rotation=60, ha="right", fontsize=8)
    ax2.set_ylabel("gate-error events removed, %")
    ax2.set_title(f"{chr(66 + k0)}. Expected gate-error events per run removed by qrig "
                  "(1 - λ_qrig/λ_qiskit, λ = -ln ESP)", fontsize=10)
    ax2.legend(fontsize=8)
    ax2.grid(alpha=0.3, axis="y")
    fig.suptitle(f"Noise with and without qrig (qrig {qrig.__version__}, Qiskit "
                 f"{qiskit.__version__}, Aer {qiskit_aer.__version__})", fontsize=13)
    fig.tight_layout(rect=(0, 0, 1, 0.97))
    fig.savefig(path, dpi=110)


def plot_all_to_all(rows, args, path):
    """Error removed and fidelity gain under the three all-to-all models."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    colors = {"depolarizing": "#2b7bba", "heron_all2all": "#5cb85c", "trapped_ion": "#9467bd"}
    info = getattr(args, "model_info", {})
    labels = [r["case"] for r in rows]
    y = np.arange(len(rows))
    w = 0.8 / len(ALL_TO_ALL)
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(17, 3 + 0.5 * len(rows)), sharey=True)
    for j, mn in enumerate(ALL_TO_ALL):
        off = (j - (len(ALL_TO_ALL) - 1) / 2) * w
        red = [100 * r["models"][mn]["F"]["infidelity_reduction"] for r in rows]
        gain = [r["models"][mn]["F"]["gain"] for r in rows]
        lab = f"{mn}: {info.get(mn, '')}"
        ax1.barh(y + off, red, w, color=colors[mn], label=lab)
        ax2.barh(y + off, gain, w, color=colors[mn], label=lab)
    ax1.axvline(0, color="k", lw=0.8)
    ax1.set_yticks(y)
    ax1.set_yticklabels(labels, fontsize=9)
    ax1.invert_yaxis()
    ax1.set_xlabel("output error removed by qrig: 1 - (1-F_qrig)/(1-F_qiskit), %")
    ax1.set_title("A. Share of the output error removed (higher is better)", fontsize=10)
    ax1.grid(alpha=0.3, axis="x")
    ax2.axvline(1, color="k", lw=0.8)
    ax2.set_xscale("log")
    ax2.set_xlabel("fidelity gain F_qrig / F_qiskit (log scale; > 1 means qrig is better)")
    ax2.set_title("B. Fidelity gain (meaningful also when both fidelities are low)",
                  fontsize=10)
    ax2.grid(alpha=0.3, axis="x")
    ax1.legend(fontsize=7, loc="lower right")
    fig.suptitle("All-to-all connectivity (no routing): noise with and without qrig, "
                 "three noise models (simulated)", fontsize=12)
    fig.tight_layout(rect=(0, 0, 1, 0.96))
    fig.savefig(path, dpi=110)


def pct(x):
    return f"{100 * x:+.1f}%"


def fmt(x):
    return f"{x:.4f}" if x >= 0.01 else f"{x:.2e}"


def write_markdown(rows, args, path):
    L = ["# Noise with and without qrig", "",
         f"Qiskit {qiskit.__version__}, Qiskit Aer {qiskit_aer.__version__}, qrig "
         f"{qrig.__version__}, Python {platform.python_version()}, seed {SEED}. "
         f"Generated by `benchmarks/noise_benchmark.py`; see `NOISE.md` for the method.", "",
         "*Qiskit*: Qiskit level-3 compilation alone. *qrig*: `QrigControlEquations` first, "
         "then the same Qiskit compilation. For each, the transpiler seed (of "
         f"{list(args.seeds)}) with the highest estimated success probability is used. `F` = state fidelity (mean over {args.inputs} random "
         "product inputs), `P` = Hellinger fidelity of the output distribution for the task "
         "input (= probability of the correct answer when it is deterministic), "
         "`err↓` = infidelity reduction 1-(1-F_qrig)/(1-F_qiskit), `×` = F_qrig/F_qiskit, "
         "ESP = product of (1 - gate error) over all gates, *gate-error events removed* = "
         "1 - λ_qrig/λ_qiskit with λ = -ln ESP (expected number of gate errors per run; "
         "does not saturate for deep circuits, but ignores idle decoherence). Rows marked *(scrambled)* have "
         "F below 2/2^n for both variants: the output is essentially noise either way, so "
         "only the ESP columns are meaningful there.", ""]
    order = [m for m in MODEL_TITLES if all(m in r["models"] for r in rows)]
    info = getattr(args, "model_info", {})
    L += ["## Summary: error removed by qrig (err↓ of F) and fidelity gain (×), per model", "",
          "| circuit | " + " | ".join(order) + " |", "|---|" + "---|" * len(order)]
    for r in rows:
        cells = []
        for mn in order:
            red = r["models"][mn]["F"]
            cells.append(f"{pct(red['infidelity_reduction'])} (×{red['gain']:.2f})")
        L.append(f"| {r['case']} | " + " | ".join(cells) + " |")
    L += ["", "Model parameters:", ""]
    for mn in order:
        L.append(f"* `{mn}`: {MODEL_TITLES[mn]}; {info.get(mn, '')}")
    L.append("")
    for mn in order:
        title = f"## `{mn}`: {MODEL_TITLES[mn]}"
        L += [title, "", info.get(mn, ""), "",
              "| circuit | qubits (active) | 2q gates Qiskit→qrig | depth Qiskit→qrig | "
              "F Qiskit | F qrig | err↓ (F) | × (F) | P Qiskit | P qrig | err↓ (P) | "
              "ESP Qiskit→qrig | gate-error events removed | sim |",
              "|" + "---|" * 14]
        for r in rows:
            a, b, red = r["models"][mn]["qiskit"], r["models"][mn]["qrig"], r["models"][mn]
            se = (f" (±{a['F_se']:.1e} / ±{b['F_se']:.1e})"
                  if a["F_se"] or b["F_se"] else "")
            scr = " *(scrambled)*" if max(a["F"], b["F"]) < 2 / 2 ** r["qubits"] else ""
            L.append(f"| {r['case']}{scr} | {r['qubits']} ({a['qubits_active']}/{b['qubits_active']}) "
                     f"| {a['cx']}→{b['cx']} | {a['depth']}→{b['depth']} | {fmt(a['F'])} | "
                     f"{fmt(b['F'])}{se} | {pct(red['F']['infidelity_reduction'])} | "
                     f"×{red['F']['gain']:.2f} | {fmt(a['P'])} | {fmt(b['P'])} | "
                     f"{pct(red['P']['infidelity_reduction'])} | {fmt(a['ESP'])}→{fmt(b['ESP'])} "
                     f"| {pct(events_removed(red))} | {a['method']} |")
        L.append("")
    with open(path, "w") as f:
        f.write("\n".join(L) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--scale", action="store_true", help="also run grover 11 (slow)")
    ap.add_argument("--no-synthetic", action="store_true")
    ap.add_argument("--models", nargs="*",
                    default=["depolarizing", "heron_all2all", "trapped_ion", "ibm_torino"],
                    choices=list(MODEL_TITLES))
    ap.add_argument("--p2", type=float, default=3e-3, help="depolarizing two-qubit error")
    for k, v in ION_DEFAULTS.items():
        ap.add_argument(f"--ion-{k}", type=float, default=v,
                        help=f"trapped_ion model: {k} (default {v:g}; durations/T in s)")
    ap.add_argument("--inputs", type=int, default=3, help="random product inputs per case")
    ap.add_argument("--dm-max", type=int, default=12,
                    help="largest active-qubit count simulated with density matrices")
    ap.add_argument("--shots", type=int, default=300, help="trajectories above --dm-max")
    ap.add_argument("--seeds", type=int, nargs="*", default=[0, 1, 2, 3, 4])
    ap.add_argument("--out", default=HERE)
    ap.add_argument("--resume", action="store_true",
                    help="reuse the cases already present in noise_results.json")
    ap.add_argument("--replot", action="store_true",
                    help="only redraw the plot and tables from noise_results.json")
    args = ap.parse_args()

    if args.replot:
        with open(os.path.join(args.out, "noise_results.json")) as f:
            data = json.load(f)
        args.p2, args.inputs, args.seeds = data["p2"], data["inputs"], data["seeds"]
        rows = data["rows"]
        args.model_info = data.get("model_info", {})
        write_outputs(rows, args)
        return 0

    ion = {k: getattr(args, f"ion_{k}") for k in ION_DEFAULTS}
    models = [Model(m, args.p2, ion) for m in args.models]
    args.model_info = {m.name: m.describe() for m in models}
    cases = QUICK_CASES if args.quick else MQT_CASES + (SCALE_CASES if args.scale else [])
    work = [(f"{b} {n}", (lambda b=b, n=n: mqt_circuit(b, n))) for b, n in cases]
    if not args.no_synthetic:
        syn = synthetic_cases()
        if args.quick:
            syn = syn[1:2]
        work += [(name, (lambda qc=qc: qc)) for name, qc in syn]

    json_path = os.path.join(args.out, "noise_results.json")
    done = {}
    if args.resume and os.path.exists(json_path):
        with open(json_path) as f:
            old = json.load(f)
            done = {r["case"]: r for r in old["rows"]}
            args.model_info = dict(old.get("model_info", {}), **args.model_info)

    def save(rows):
        with open(json_path, "w") as f:
            json.dump({"qiskit": qiskit.__version__, "aer": qiskit_aer.__version__,
                       "qrig": qrig.__version__, "seed": SEED, "p2": args.p2,
                       "inputs": args.inputs, "shots": args.shots, "seeds": list(args.seeds),
                       "dm_max": args.dm_max, "model_info": args.model_info, "rows": rows,
                       "sweep": sweep(rows)}, f, indent=1)

    rows = []
    for label, make in work:
        # a fresh generator per case keeps the random inputs independent of resuming
        rng = np.random.default_rng([SEED, sum(map(ord, label))])
        print(label, flush=True)
        prev = done.get(label)
        row = run_case(label, make(), models, args, rng, prev)
        if prev is not None:     # keep models of the earlier run that were not re-run
            for k, v in prev["models"].items():
                row["models"].setdefault(k, v)
        rows.append(row)
        save(rows)
    save(rows)
    write_outputs(rows, args)
    return 0


def write_outputs(rows, args):
    write_markdown(rows, args, os.path.join(args.out, "noise_results.md"))
    if all("depolarizing" in r["models"] for r in rows):
        plot(rows, sweep(rows), os.path.join(args.out, "noise_benchmark.png"), args.p2)
    if all(m in r["models"] for r in rows for m in ALL_TO_ALL):
        plot_all_to_all(rows, args, os.path.join(args.out, "noise_all_to_all.png"))
    print("wrote noise_results.md, noise_results.json and plots to", args.out)


if __name__ == "__main__":
    sys.exit(main())
