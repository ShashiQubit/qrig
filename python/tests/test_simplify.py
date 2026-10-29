"""The verified optimiser preserves semantics and reduces circuits."""
import numpy as np
import pytest
from qiskit import QuantumCircuit
from qiskit.transpiler import PassManager

import qrig
from qrig import C0, C1, H, I, S, SWAP, T, Tdg, V, X
from qrig.qiskit_bridge import QrigOptimize, optimize_qiskit
from conftest import operator, random_pair


def test_basic_rewrites():
    assert qrig.simplify(C1(X) >> C1(X)) == I(2)
    assert qrig.simplify(SWAP >> SWAP) == I(2)
    assert qrig.simplify(C1(I(3))) == I(4)
    assert qrig.simplify(C0(H) >> C1(H)).gates() == 1          # (e): I1 + H
    assert qrig.equivalent(qrig.simplify(C0(H) >> C1(H)), I(1) + H)
    assert qrig.simplify(T >> T >> T >> T >> T >> T >> T >> T) == I(1)
    assert qrig.simplify(H >> H) == I(1)
    assert qrig.simplify(C1(T) >> C1(Tdg)) == I(2)
    assert qrig.simplify(C1(C1(S)) >> C1(C1(S))).gates() == 1
    assert qrig.simplify(C1(C1(S)) >> C1(C1(S)) >> C1(C1(S)) >> C1(C1(S))) == I(3)


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_random_preserves_semantics(rng, n):
    for _ in range(30):
        c, qc = random_pair(rng, n, rng.randint(1, 30))
        s = qrig.simplify(c)
        assert s.n == c.n
        assert qrig.equivalent(s, c)
        assert s.gates() <= c.gates()
        assert np.allclose(operator(s.to_qiskit()), operator(qc))


def test_inverse_cancels(rng):
    for n in (1, 2, 3):
        for _ in range(10):
            c, _ = random_pair(rng, n, 12)
            d = qrig.dagger(c)
            assert qrig.equivalent(c >> d, I(n))
            assert qrig.simplify(c >> d) == I(n) or qrig.equivalent(qrig.simplify(c >> d), I(n))


def test_qiskit_pass():
    qc = QuantumCircuit(3)
    qc.h(0); qc.h(0); qc.ccx(0, 1, 2); qc.ccx(0, 1, 2); qc.t(1); qc.tdg(1); qc.cx(2, 0)
    out = optimize_qiskit(qc)
    assert np.allclose(operator(out), operator(qc))
    assert out.size() < qc.size()
    pm = PassManager([QrigOptimize()])
    out2 = pm.run(qc)
    assert np.allclose(operator(out2), operator(qc))


def test_qiskit_pass_leaves_inexact_circuits_alone():
    qc = QuantumCircuit(1)
    qc.rx(0.3, 0)
    out = PassManager([QrigOptimize()]).run(qc)
    assert np.allclose(operator(out), operator(qc))
