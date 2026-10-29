"""Equations and constructions from the paper, checked exactly and against Qiskit."""
import random

import numpy as np
import pytest

import qrig
from qrig import C0, C1, H, I, S, SWAP, T, V, Vdg, X, Y, Z, Sdg, Tdg
from qrig.paper import (commuting_cnots, control_equations, gray_transposition,
                        sleator_weinfurter)
from conftest import NAMED, operator, random_pair


def _check_pair(lhs, rhs):
    assert qrig.equivalent(lhs, rhs), (lhs, rhs)
    assert np.allclose(operator(lhs.to_qiskit()), operator(rhs.to_qiskit()))


@pytest.mark.parametrize("name", sorted(NAMED))
def test_control_equations_on_gates(name):
    f = NAMED[name]
    for g in (X, H, T, S, V):
        for key, (lhs, rhs) in control_equations(f, g, g).items():
            _check_pair(lhs, rhs)


def test_control_equations_on_random_circuits(rng):
    for n in (1, 2, 3):
        for _ in range(8):
            f, _ = random_pair(rng, n, 6)
            g, _ = random_pair(rng, n, 6)
            f2, _ = random_pair(rng, n, 6)
            for m in (1, 2):
                for key, (lhs, rhs) in control_equations(f, g, f2, m).items():
                    _check_pair(lhs, rhs)


def test_control_equations_with_scalars():
    w = qrig.GLOBAL_OMEGA
    for key, (lhs, rhs) in control_equations(w, w + I(0)).items():
        assert qrig.equivalent(lhs, rhs), key


def test_non_equations_are_detected():
    # sanity check: the checker is not vacuous
    assert not qrig.equivalent(C1(X), C0(X))
    assert not qrig.equivalent(C1(H) >> C1(T), C1(T) >> C1(H))
    assert qrig.equivalent(C1(H) >> C0(T), C0(T) >> C1(H))  # (f) commutativity


@pytest.mark.parametrize("f", [X, V, Vdg, H, S, T, Z, Y, Sdg, Tdg])
def test_sleator_weinfurter(f):
    """Figure 3: C1(C1(f^2)) = SW(f) for unitary f."""
    lhs = C1(C1(f >> f))
    rhs = sleator_weinfurter(f)
    _check_pair(lhs, rhs)


def test_sleator_weinfurter_two_qubit_target(rng):
    f, _ = random_pair(rng, 2, 8)
    _check_pair(C1(C1(f >> f)), sleator_weinfurter(f))


def test_commuting_cnots():
    lhs, rhs = commuting_cnots()
    _check_pair(lhs, rhs)


def test_gray_code_matches_figure_2():
    assert qrig.gray_code(3) == [0b000, 0b001, 0b011, 0b010, 0b110, 0b111, 0b101, 0b100]
    for n in range(1, 9):
        code = qrig.gray_code(n)
        assert sorted(code) == list(range(2 ** n))
        for a, b in zip(code, code[1:]):
            assert bin(a ^ b).count("1") == 1


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_gray_transpositions(n):
    code = qrig.gray_code(n)
    for i in range(2 ** n - 1):
        c = gray_transposition(n, i)
        p = list(range(2 ** n))
        p[code[i]], p[code[i + 1]] = p[code[i + 1]], p[code[i]]
        assert qrig.permutation(c) == p


def test_example_multicontrolled_gate_from_section_3():
    # "1011 <-> 1001": NOT on the third wire controlled by 1, 0 and 1.
    c = qrig.mcx({0: True, 1: False, 3: True}, 2, 4)
    p = qrig.permutation(c)
    assert p[0b1011] == 0b1001 and p[0b1001] == 0b1011
    assert sum(1 for i, j in enumerate(p) if i != j) == 2


def test_modal_quantum_theory_independence_model():
    """Proposition 24's model: X -> NOT, J -> identity satisfies the control equations
    but not equation (18); here: C1(X) >> C0(X) ... the swap (g) holds while
    replacing J by the identity breaks the J-analogue."""
    J = I(1)
    lhs = C1(J) >> SWAP  # a swap
    rhs = I(2)
    assert not qrig.equivalent(lhs, rhs)


def test_clifford_t_generators_section_5_5():
    """Section 5.5: X = V^2, CX = C1(X), CCX = C1(CX), T = C1(omega), S = C1(omega^2),
    H = omega^7 . S V S."""
    w = qrig.GLOBAL_OMEGA
    assert qrig.equivalent(V >> V, X)
    assert qrig.equivalent(C1(w), T)
    assert qrig.equivalent(C1(w >> w), S)
    w7 = qrig.phase(qrig.omega_pow(7))
    assert qrig.equivalent((w7 + I(1)) >> S >> V >> S, H)
