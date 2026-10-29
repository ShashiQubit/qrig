"""Synthesis of reversible circuits from permutations (Theorem 9, functor beta)."""
import itertools
import random

import numpy as np
import pytest

import qrig
from conftest import operator


def perm_matrix(p):
    N = len(p)
    m = np.zeros((N, N))
    for i, j in enumerate(p):
        m[j, i] = 1
    return m


@pytest.mark.parametrize("n", [0, 1, 2])
def test_all_permutations_small(n):
    for p in itertools.permutations(range(2 ** n)):
        c = qrig.synthesize_permutation(list(p), n)
        assert c.n == n
        assert c.is_classical()
        assert qrig.permutation(c) == list(p)
        assert np.allclose(operator(c.to_qiskit()), perm_matrix(p))


def test_all_permutations_of_three_bits():
    """All 40320 permutations of 3-bit basis states."""
    perms = list(itertools.permutations(range(8)))
    assert len(perms) == 40320
    for p in perms:
        c = qrig.synthesize_permutation(list(p), 3)
        assert qrig.permutation(c) == list(p)


def test_three_bits_against_qiskit():
    rng = random.Random(3)
    perms = list(itertools.permutations(range(8)))
    for p in rng.sample(perms, 400):
        c = qrig.synthesize_permutation(list(p), 3)
        assert np.allclose(operator(c.to_qiskit()), perm_matrix(p))


@pytest.mark.parametrize("n", [4, 5])
def test_random_permutations(n):
    rng = random.Random(n)
    for _ in range(30):
        p = list(range(2 ** n))
        rng.shuffle(p)
        c = qrig.synthesize_permutation(p, n)
        assert qrig.permutation(c) == p
        if n == 4:
            assert np.allclose(operator(c.to_qiskit()), perm_matrix(p))


def test_known_gates():
    cnot = qrig.synthesize_permutation([0, 1, 3, 2])
    assert qrig.equivalent(cnot, qrig.C1(qrig.X))
    tof = qrig.synthesize_permutation([0, 1, 2, 3, 4, 5, 7, 6])
    assert qrig.equivalent(tof, qrig.C1(qrig.C1(qrig.X)))
    swap = qrig.synthesize_permutation([0, 2, 1, 3])
    assert qrig.equivalent(swap, qrig.SWAP)


@pytest.mark.parametrize("bad", [[0, 0, 1, 2], [0, 1, 2], [1, 2, 3, 4], [0, 1, 2, 3, 4, 5, 6]])
def test_rejects_non_permutations(bad):
    with pytest.raises(qrig.QrigError):
        qrig.synthesize_permutation(bad, 2 if len(bad) == 4 else None)


def test_permutation_of_nonclassical_rejected():
    with pytest.raises(qrig.QrigError):
        qrig.permutation(qrig.H)
