"""Tests for the DAG-level optimiser ``qrig.dag`` (control equations on Qiskit DAGs)."""
import math
import random

import numpy as np
import pytest

qiskit = pytest.importorskip("qiskit")
from qiskit import QuantumCircuit  # noqa: E402
from qiskit.circuit import Parameter  # noqa: E402
from qiskit.circuit.library import (CHGate, CPhaseGate, CRXGate, CRYGate, CRZGate, CSdgGate,  # noqa: E402
                                    CSGate, CSXGate, CU1Gate, CU3Gate, CUGate, CXGate, CYGate,
                                    CZGate, HGate, MCPhaseGate, MCXGate, PhaseGate, RXGate,
                                    RYGate, RZGate, SXGate, TGate, UGate, XGate, YGate, ZGate,
                                    C3SXGate, CCZGate, RGate, U2Gate, UnitaryGate)
from qiskit.quantum_info import Operator, random_unitary  # noqa: E402
from qiskit.transpiler import PassManager  # noqa: E402

from qrig.dag import (QrigControlEquations, flat_to_qiskit, optimize_circuit,  # noqa: E402
                      to_pi_fraction, _convert, _GenTable)


def same_unitary(a, b):
    a = a.remove_final_measurements(inplace=False)
    b = b.remove_final_measurements(inplace=False)
    return np.allclose(Operator(a).data, Operator(b).data, atol=1e-9)


def opt(qc, **kw):
    out, st = optimize_circuit(qc, **kw)
    return out, st


# ---------------------------------------------------------------- conversion
ONE_Q = [XGate(), YGate(), ZGate(), HGate(), SXGate(), TGate(), PhaseGate(0.37), RZGate(-1.1),
         RXGate(2.5), RYGate(0.3), UGate(0.1, 0.2, 0.3), U2Gate(0.4, -0.7), RGate(0.9, 0.2),
         UGate(math.pi / 2, math.pi / 4, -math.pi / 8)]


@pytest.mark.parametrize("g", ONE_Q, ids=lambda g: g.name)
def test_one_qubit_gates_exact(g):
    qc = QuantumCircuit(1)
    qc.append(g, [0])
    out, _ = opt(qc)
    assert same_unitary(qc, out)


CONTROLLED = [(CXGate(), 2), (CYGate(), 2), (CZGate(), 2), (CHGate(), 2), (CSXGate(), 2),
              (CSGate(), 2), (CSdgGate(), 2), (CPhaseGate(0.7), 2), (CRZGate(0.4), 2),
              (CRXGate(-0.4), 2), (CRYGate(1.3), 2), (CU1Gate(0.2), 2), (CU3Gate(0.1, 0.2, 0.3), 2),
              (CUGate(0.1, 0.2, 0.3, 0.4), 2), (CCZGate(), 3), (C3SXGate(), 4),
              (MCXGate(4), 5), (MCPhaseGate(0.3, 3), 4), (CXGate(ctrl_state=0), 2),
              (MCXGate(3, ctrl_state=5), 4)]


@pytest.mark.parametrize("g,n", CONTROLLED, ids=lambda x: getattr(x, "name", str(x)))
def test_controlled_gates_exact(g, n):
    rng = random.Random(n)
    for _ in range(3):
        qs = rng.sample(range(n + 1), n)
        qc = QuantumCircuit(n + 1)
        qc.append(g, qs)
        out, _ = opt(qc)
        assert same_unitary(qc, out)


def test_every_ctrl_state_of_a_toffoli():
    for st in range(4):
        qc = QuantumCircuit(3)
        qc.append(XGate().control(2, ctrl_state=st, annotated=False), [2, 0, 1])
        out, _ = opt(qc)
        assert same_unitary(qc, out)


def test_flat_round_trip():
    gens = _GenTable()
    for g, n in CONTROLLED:
        if g.name == "cu":
            continue
        fl = _convert(g, list(range(n)), gens)
        assert fl is not None, g.name
        qc = QuantumCircuit(n)
        for f in fl:
            op, qs = flat_to_qiskit(f, gens)
            qc.append(op, qs)
        ref = QuantumCircuit(n)
        ref.append(g, list(range(n)))
        assert same_unitary(ref, qc), g.name


def test_angles_are_exact_fractions():
    from fractions import Fraction
    assert to_pi_fraction(math.pi / 8) == Fraction(1, 8)
    assert to_pi_fraction(-3 * math.pi / 4) == Fraction(-3, 4)
    assert to_pi_fraction(0.123) == Fraction(0.123 / math.pi)
    assert to_pi_fraction(Parameter("a")) is None


# ---------------------------------------------------------------- each rule
def test_rule_a_fusion_of_controlled_phases():
    qc = QuantumCircuit(3)
    qc.cp(0.3, 0, 2)
    qc.h(1)
    qc.cp(0.5, 0, 2)
    out, st = opt(qc)
    assert st.rules["fuse"] == 1
    assert out.count_ops().get("cp", 0) == 1
    assert same_unitary(qc, out)


def test_rule_cancel_toffolis_and_mcx():
    qc = QuantumCircuit(5)
    qc.ccx(0, 1, 2)
    qc.ccx(1, 0, 2)          # same control set, different order
    qc.mcx([0, 1, 2, 3], 4)
    qc.mcx([3, 2, 1, 0], 4)
    out, st = opt(qc)
    assert out.size() == 0
    assert st.rules["cancel"] == 2
    assert same_unitary(qc, out)


def test_rule_b_identity_removed():
    qc = QuantumCircuit(2)
    qc.cp(0.0, 0, 1)
    qc.crz(4 * math.pi, 0, 1)
    out, st = opt(qc)
    assert out.size() == 0
    assert same_unitary(qc, out)


def test_rule_e_complementarity():
    """C0(f) ; C1(f) = id + f : the control disappears (equation (e))."""
    qc = QuantumCircuit(3)
    qc.append(HGate().control(2, ctrl_state=0b01, annotated=False), [0, 1, 2])  # q1 = 0
    qc.append(HGate().control(2, ctrl_state=0b11, annotated=False), [0, 1, 2])  # q1 = 1
    out, st = opt(qc)
    assert st.rules["compl"] == 1
    assert out.size() == 1 and out.data[0].operation.name == "ch"
    assert same_unitary(qc, out)


def test_rule_e_full_multiplexer_collapses():
    """All 2^k control patterns of the same gate collapse to the bare gate."""
    k = 3
    qc = QuantumCircuit(k + 1)
    for st in range(2 ** k):
        qc.append(RYGate(0.7).control(k, ctrl_state=st, annotated=False), list(range(k + 1)))
    out, st = opt(qc)
    assert out.size() == 1 and out.data[0].operation.name == "ry"
    assert st.rules["compl"] == 2 ** k - 1
    assert same_unitary(qc, out)


def test_rule_d_colour_change():
    """x_w ; C1_w(f) ; x_w = C0_w(f)  (equation (d))."""
    qc = QuantumCircuit(3)
    qc.x(0)
    qc.ccx(0, 1, 2)
    qc.cz(0, 1)
    qc.x(0)
    out, st = opt(qc)
    assert st.rules["xconj"] == 1
    assert "x" not in out.count_ops()
    assert same_unitary(qc, out)


def test_rule_f_commutation_through_contradictory_controls():
    """C0(f1) ; C1(f2) ; C0(f1)^-1 : the outer pair meets via equation (f)."""
    qc = QuantumCircuit(3)
    qc.append(XGate().control(1, ctrl_state=0, annotated=False), [0, 2])
    qc.append(HGate().control(1, ctrl_state=1, annotated=False), [0, 2])
    qc.append(XGate().control(1, ctrl_state=0, annotated=False), [0, 2])
    out, st = opt(qc)
    assert out.size() == 1
    assert same_unitary(qc, out)


def test_diagonal_gates_commute():
    qc = QuantumCircuit(3)
    qc.t(0)
    qc.cp(0.4, 0, 1)
    qc.cz(0, 2)
    qc.tdg(0)
    out, st = opt(qc)
    assert out.size() == 2
    assert same_unitary(qc, out)


def test_non_commuting_gates_block():
    qc = QuantumCircuit(2)
    qc.cx(0, 1)
    qc.h(1)
    qc.cx(0, 1)
    out, st = opt(qc)
    assert out.size() == 3
    assert same_unitary(qc, out)


def test_window_limits_search():
    qc = QuantumCircuit(3)
    qc.cx(0, 1)
    for _ in range(10):
        qc.t(2)
        qc.tdg(2)
    qc.cx(0, 1)
    out, _ = opt(qc, window=128)
    assert out.size() == 0
    qc2 = QuantumCircuit(3)
    qc2.cx(0, 1)
    for _ in range(10):
        qc2.h(2)
        qc2.x(2)
    qc2.cx(0, 1)
    out2, _ = opt(qc2, window=2)
    assert same_unitary(qc2, out2)


# ---------------------------------------------------------------- robustness
def test_measurements_barriers_resets_are_kept_in_place():
    qc = QuantumCircuit(3, 3)
    qc.h(0)
    qc.cx(0, 1)
    qc.measure(1, 1)
    qc.cx(0, 1)          # must NOT cancel with the first cx (measurement in between)
    qc.barrier()
    qc.reset(2)
    qc.ccx(0, 1, 2)
    qc.ccx(0, 1, 2)
    qc.measure([0, 1, 2], [0, 1, 2])
    out, st = opt(qc)
    ops = out.count_ops()
    assert ops["cx"] == 2 and ops["measure"] == 4 and ops["reset"] == 1
    assert "ccx" not in ops
    assert [i.operation.name for i in out.data].index("measure") > 0


def test_gates_on_other_wires_pass_a_measurement():
    qc = QuantumCircuit(3, 1)
    qc.cx(0, 1)
    qc.measure(2, 0)
    qc.cx(0, 1)
    out, _ = opt(qc)
    assert out.count_ops().get("cx", 0) == 0


def test_symbolic_parameters_are_kept():
    a = Parameter("a")
    qc = QuantumCircuit(2)
    qc.rz(a, 0)
    qc.cx(0, 1)
    qc.cx(0, 1)
    qc.rz(a, 0)
    out, _ = opt(qc)
    assert out.count_ops() == {"rz": 2}


def test_opaque_unitary_gates_and_complementarity():
    u = UnitaryGate(random_unitary(2, seed=3))
    qc = QuantumCircuit(2)
    qc.append(u.control(1, ctrl_state=0, annotated=False), [0, 1])
    qc.append(u.control(1, ctrl_state=1, annotated=False), [0, 1])
    out, st = opt(qc)
    assert st.rules["compl"] == 1
    assert same_unitary(qc, out)


def test_global_phase_preserved():
    qc = QuantumCircuit(2, global_phase=0.3)
    qc.append(CUGate(0.1, 0.2, 0.3, 0.4), [0, 1])
    qc.h(0)
    qc.h(0)
    out, _ = opt(qc)
    assert same_unitary(qc, out)


def test_transpiler_pass_and_stats():
    qc = QuantumCircuit(3)
    qc.ccx(0, 1, 2)
    qc.ccx(0, 1, 2)
    pm = PassManager([QrigControlEquations()])
    out = pm.run(qc)
    assert out.size() == 0
    assert pm.property_set["qrig_stats"].rules["cancel"] == 1


def random_controlled_circuit(n, m, rng):
    pool = [XGate(), HGate(), TGate(), ZGate(), SXGate(), YGate(),
            PhaseGate(rng.choice([0.25, 0.5, -0.5]) * math.pi), RYGate(0.7), RZGate(-0.3)]
    qc = QuantumCircuit(n)
    for _ in range(m):
        g = rng.choice(pool)
        k = rng.randint(0, min(3, n - 1))
        qs = rng.sample(range(n), k + 1)
        if k:
            g = g.control(k, ctrl_state=rng.randrange(2 ** k), annotated=False)
        qc.append(g, qs)
        if rng.random() < 0.3:      # repeat or complement the gate to create patterns
            if k and rng.random() < 0.5:
                g2 = g.base_gate.control(k, ctrl_state=g.ctrl_state ^ (1 << rng.randrange(k)),
                                         annotated=False)
                qc.append(g2, qs)
            else:
                qc.append(g.inverse(), qs)
    return qc


@pytest.mark.parametrize("seed", range(25))
def test_random_controlled_circuits_exact(seed):
    rng = random.Random(seed)
    n = rng.randint(2, 5)
    qc = random_controlled_circuit(n, rng.randint(5, 40), rng)
    out, _ = opt(qc, window=rng.choice([1, 4, 128]))
    assert same_unitary(qc, out)
    assert out.size() <= qc.size() + 0  # conversion never adds gates for this gate set


@pytest.mark.parametrize("seed", range(5))
def test_random_circuits_verified_by_qcec(seed):
    qcec = pytest.importorskip("mqt.qcec")
    rng = random.Random(100 + seed)
    qc = random_controlled_circuit(6, 80, rng)
    out, _ = opt(qc)
    res = qcec.verify(qc, out)
    assert str(res.equivalence).split(".")[-1] in ("equivalent", "equivalent_up_to_global_phase")


def test_large_circuit_is_fast():
    import time
    rng = random.Random(7)
    qc = QuantumCircuit(40)
    for _ in range(20000):
        a, b, c = rng.sample(range(40), 3)
        r = rng.random()
        if r < 0.4:
            qc.ccx(a, b, c)
        elif r < 0.7:
            qc.cx(a, b)
        else:
            qc.t(a)
    t0 = time.perf_counter()
    out, st = opt(qc, window=64)
    assert time.perf_counter() - t0 < 60
    assert out.size() <= qc.size()


def test_mqt_bench_grover_end_to_end():
    pytest.importorskip("mqt.bench")
    qcec = pytest.importorskip("mqt.qcec")
    from mqt.bench import BenchmarkLevel, get_benchmark
    qc = get_benchmark("grover", BenchmarkLevel.ALG, 4).decompose()
    out, st = opt(qc)
    assert out.size() < qc.size()
    assert str(qcec.verify(qc, out).equivalence).split(".")[-1] == "equivalent"
