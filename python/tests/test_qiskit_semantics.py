"""The exact semantics computed by the verified core agrees with Qiskit.

Circuits are built independently in qrig and in Qiskit (no conversion involved) and
their unitaries compared; then the exporter/importer are checked as well.
"""
import itertools

import numpy as np
import pytest
from qiskit import QuantumCircuit
from qiskit.circuit.library import SwapGate, XGate
from qiskit.quantum_info import Operator, Statevector

import qrig
from qrig import C0, C1, I, SWAP, X

from conftest import control_gate, NAMED, assert_same_unitary, operator, qiskit_gate, random_pair


@pytest.mark.parametrize("name", sorted(NAMED))
def test_single_gates(name):
    qc = QuantumCircuit(1)
    qc.append(qiskit_gate(name), [0])
    assert_same_unitary(NAMED[name], qc)


@pytest.mark.parametrize("name", sorted(NAMED))
@pytest.mark.parametrize("n", [2, 3, 4])
def test_every_control_pattern_and_placement(name, n):
    """Every gate, with every number of controls, every control colouring and every
    placement of controls/target on n wires."""
    count = 0
    for k in range(n):
        for wires in itertools.permutations(range(n), k + 1):
            ctrl_wires, target = wires[:k], wires[k]
            if list(ctrl_wires) != sorted(ctrl_wires) and n == 4:
                continue  # order of controls is irrelevant; keep n=4 affordable
            for vals in itertools.product([False, True], repeat=k):
                c = qrig.controlled_on(NAMED[name], list(zip(ctrl_wires, vals)), [target], n)
                qc = QuantumCircuit(n)
                g = qiskit_gate(name)
                if k:
                    g = control_gate(g, k, sum(1 << j for j, v in enumerate(vals) if v))
                qc.append(g, [n - 1 - w for w in ctrl_wires] + [n - 1 - target])
                assert_same_unitary(c, qc)
                assert np.allclose(operator(c.to_qiskit()), operator(qc))
                count += 1
    assert count > 0


@pytest.mark.parametrize("n", [2, 3, 4])
def test_swaps_and_fredkin(n):
    for a, b in itertools.permutations(range(n), 2):
        c = qrig.on_wires(SWAP, [a, b], n)
        qc = QuantumCircuit(n)
        qc.swap(n - 1 - a, n - 1 - b)
        assert_same_unitary(c, qc)
        for w in range(n):
            if w in (a, b):
                continue
            for v in (False, True):
                c = qrig.controlled_on(SWAP, [(w, v)], [a, b], n)
                qc = QuantumCircuit(n)
                qc.append(control_gate(SwapGate(), 1, int(v)), [n - 1 - w, n - 1 - a, n - 1 - b])
                assert_same_unitary(c, qc)
                assert np.allclose(operator(c.to_qiskit()), operator(qc))


def test_scalars_and_controlled_phases():
    w = qrig.GLOBAL_OMEGA
    qc = QuantumCircuit(1)
    qc.global_phase = np.pi / 4
    assert_same_unitary(w + I(1), qc)
    # C1(omega) is the T gate, C0(omega) is X T X
    assert qrig.equivalent(C1(w), qrig.T)
    assert qrig.equivalent(C0(w), X >> qrig.T >> X)
    assert qrig.equivalent(C1(C1(w)), C1(qrig.T))
    for c in [C1(w), C0(w), C1(C0(w)), C0(C1(C1(w)))]:
        assert np.allclose(operator(c.to_qiskit()), qrig.unitary(c, exact=False))


@pytest.mark.parametrize("n", [1, 2, 3, 4, 5])
def test_random_circuits(rng, n):
    for _ in range(25):
        c, qc = random_pair(rng, n, rng.randint(1, 25))
        assert_same_unitary(c, qc)
        assert np.allclose(operator(c.to_qiskit()), operator(qc))


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_import_random_qiskit_circuits(rng, n):
    for _ in range(25):
        _, qc = random_pair(rng, n, rng.randint(1, 20))
        c = qrig.from_qiskit(qc)
        assert_same_unitary(c, qc)
        back = qrig.to_qiskit(c)
        assert np.allclose(operator(back), operator(qc))


def test_import_library_gates():
    qc = QuantumCircuit(4)
    qc.h(0); qc.cx(0, 1); qc.ccx(0, 1, 2); qc.mcx([0, 1, 2], 3); qc.cz(1, 3); qc.cy(2, 0)
    qc.ch(3, 1); qc.cswap(0, 2, 3); qc.cs(1, 2); qc.csdg(2, 1); qc.csx(0, 3); qc.t(2)
    qc.tdg(1); qc.s(3); qc.sdg(0); qc.sx(1); qc.sxdg(2); qc.y(3); qc.z(0); qc.swap(0, 3)
    qc.rccx(0, 1, 2); qc.iswap(1, 2); qc.ecr(0, 1); qc.dcx(2, 3); qc.cp(np.pi / 2, 0, 2)
    qc.rz(np.pi / 2, 1); qc.u(np.pi / 2, 0, np.pi, 3)
    qc.global_phase = 3 * np.pi / 4
    c = qrig.from_qiskit(qc)
    assert_same_unitary(c, qc)


def test_import_rejects_inexact():
    qc = QuantumCircuit(1)
    qc.rx(0.1234, 0)
    with pytest.raises(ValueError):
        qrig.from_qiskit(qc)


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_simulate_matches_statevector(rng, n):
    for _ in range(10):
        c, qc = random_pair(rng, n, 15)
        for j in range(2 ** n):
            psi = [0] * (2 ** n)
            psi[j] = 1
            out = qrig.simulate(c, psi, exact=False)
            ref = Statevector.from_int(j, 2 ** n).evolve(qc).data
            assert np.allclose(out, ref)
