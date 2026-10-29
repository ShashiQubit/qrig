"""Cross-checks against Qiskit on larger random workloads, and concurrency."""
import threading

import numpy as np
import pytest
from qiskit import QuantumCircuit

import qrig
from qrig import I
from qrig.qiskit_bridge import optimize_qiskit
from conftest import operator, random_pair

EXACT_GATES = ["h", "x", "y", "z", "s", "sdg", "t", "tdg", "sx", "sxdg", "cx", "cz", "cy",
               "ch", "swap", "ccx", "cswap"]


def random_exact_qiskit(rng, n, depth):
    qc = QuantumCircuit(n)
    for _ in range(depth):
        name = rng.choice(EXACT_GATES)
        arity = {"cx": 2, "cz": 2, "cy": 2, "ch": 2, "swap": 2, "ccx": 3, "cswap": 3}.get(name, 1)
        if arity > n:
            continue
        qubits = rng.sample(range(n), arity)
        getattr(qc, name)(*qubits)
    return qc


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_dagger_matches_qiskit_inverse(rng, n):
    for _ in range(15):
        c, qc = random_pair(rng, n, 12)
        assert np.allclose(qrig.unitary(qrig.dagger(c), exact=False), operator(qc.inverse()),
                           atol=1e-9)


@pytest.mark.parametrize("n", [1, 2, 3, 4, 5])
def test_optimizer_on_random_qiskit_circuits(rng, n):
    for _ in range(10):
        qc = random_exact_qiskit(rng, n, 30)
        out = optimize_qiskit(qc)
        assert np.allclose(operator(out), operator(qc), atol=1e-9)
        # the imported circuit is exactly equivalent to its optimised form
        c = qrig.from_qiskit(qc)
        assert qrig.equivalent(c, qrig.simplify(c))


def test_equivalence_up_to_phase():
    from qrig import GLOBAL_OMEGA, T
    assert not qrig.equivalent(T, T + GLOBAL_OMEGA)
    assert qrig.equivalent(T, T + GLOBAL_OMEGA, up_to_phase=True)


def test_concurrent_calls(rng):
    pairs = [random_pair(rng, 3, 10) for _ in range(8)]
    expected = [qrig.unitary(c, exact=False) for c, _ in pairs]
    errors = []

    def worker(k):
        try:
            for _ in range(5):
                u = qrig.unitary(pairs[k][0], exact=False)
                assert np.allclose(u, expected[k])
        except Exception as e:  # pragma: no cover
            errors.append(e)

    ts = [threading.Thread(target=worker, args=(k,)) for k in range(8)]
    for t in ts:
        t.start()
    for t in ts:
        t.join()
    assert not errors


def test_wide_classical_circuit():
    # permutations work on many wires without building a matrix
    n = 12
    c = qrig.mcx({k: True for k in range(n - 1)}, n - 1, n)
    p = qrig.permutation(c)
    assert p[2 ** n - 1] == 2 ** n - 2 and p[2 ** n - 2] == 2 ** n - 1
    assert all(p[i] == i for i in range(2 ** n - 2))
    c6 = qrig.mcx({0: True, 2: False, 3: True, 5: False}, 1, 6)
    assert qrig.equivalent(c6 >> c6, I(6))
