"""The application kernels of the study, checked against the specifications proved in Lean.

`QrigProofs/Study/Reversible.lean` and `QrigProofs/Study/Draper.lean` prove what the
kernels `incrementer`, `hamming_weight`, `membership_oracle`, `qrom` and the Draper adder
inside `shor_modadd` compute, for a gate-list model written to mirror
`benchmarks/app_circuits.py`.  The proofs are about that model, not about the Python code;
these tests close the gap by running the actual Qiskit circuits on every basis state and
comparing with the proved specification (Qiskit's little-endian convention: qubit ``k`` is
bit ``k`` of the basis-state index, as in the Lean ``regVal``).
"""
import math
import os
import random
import sys

import numpy as np
import pytest

qiskit = pytest.importorskip("qiskit")
from qiskit import QuantumCircuit  # noqa: E402
from qiskit.quantum_info import Operator, Statevector  # noqa: E402

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                                "benchmarks"))
pytest.importorskip("mqt.bench")           # app_circuits imports the MQT pipeline helpers
import app_circuits as ac  # noqa: E402


def basis_map(qc):
    """The permutation of basis states of a classical reversible circuit (asserted to be one)."""
    u = Operator(qc).data
    n = u.shape[0]
    out = []
    for j in range(n):
        col = u[:, j]
        i = int(np.argmax(np.abs(col)))
        assert abs(abs(col[i]) - 1) < 1e-9, "circuit is not a basis permutation"
        assert abs(col[i] - 1) < 1e-9, "classical kernel introduced a phase"
        out.append(i)
    return out


def bits(x, lo, m):
    return (x >> lo) & ((1 << m) - 1)


@pytest.mark.parametrize("n", [1, 2, 3, 4, 5, 6])
def test_incrementer_spec(n):
    # Lean: incrementer_spec — the register maps x to (x + 1) mod 2^n.
    perm = basis_map(ac.incrementer(n))
    assert perm == [(x + 1) % 2 ** n for x in range(2 ** n)]


@pytest.mark.parametrize("nin", [1, 2, 3, 4, 5, 6, 7])
def test_hamming_weight_spec(nin):
    # Lean: hamming_spec — inputs unchanged, counter += popcount (mod 2^nout);
    # hammingOut nin = max 1 (clog 2 (nin+1)) is the width the kernel uses.
    nout = max(1, math.ceil(math.log2(nin + 1)))
    assert nout == max(1, (nin).bit_length())          # = clog 2 (nin + 1)
    perm = basis_map(ac.hamming_weight(nin))
    for s in range(2 ** (nin + nout)):
        x, c = bits(s, 0, nin), bits(s, nin, nout)
        t = perm[s]
        assert bits(t, 0, nin) == x
        assert bits(t, nin, nout) == (c + bin(x).count("1")) % 2 ** nout


def member_set(n):
    rng = ac._rng("member", n)
    return rng.sample(range(2 ** n), min(2 ** n, 2 * n))


@pytest.mark.parametrize("n", [2, 3, 4, 5])
def test_membership_oracle_spec(n):
    # Lean: memberOracle_spec — the target (wire n) is flipped iff the input is in S.
    S = set(member_set(n))
    perm = basis_map(ac.mcx_ladder_oracle(n))
    for s in range(2 ** (n + 1)):
        x, b = bits(s, 0, n), (s >> n) & 1
        assert perm[s] == x | ((b ^ (x in S)) << n)


def qrom_table(addr, data):
    rng = ac._rng("qrom", addr * 10 + data)
    return [rng.randrange(1, 2 ** data) for _ in range(2 ** addr)]


@pytest.mark.parametrize("addr,data", [(1, 1), (2, 2), (2, 3), (3, 2), (3, 3)])
def test_qrom_spec(addr, data):
    # Lean: qrom_spec — address unchanged, data register XORed with table[address].
    table = qrom_table(addr, data)
    perm = basis_map(ac.qrom(addr, data))
    for s in range(2 ** (addr + data)):
        a, d = bits(s, 0, addr), bits(s, addr, data)
        assert perm[s] == a | ((d ^ table[a]) << addr)


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_phi_add_spec(n):
    # Lean: phiAdd_correct — QFT, then the phase gates of _phi_add(a), then QFT^{-1}
    # maps |x> to |(x + a) mod 2^n>, for every a and x (sign = -1 subtracts).
    for a in range(2 ** n):
        for sign in (1, -1):
            qc = QuantumCircuit(n)
            ac._qft(qc, list(range(n)))
            ac._phi_add(qc, a, list(range(n)), [], sign=sign)
            ac._qft(qc, list(range(n)), inverse=True)
            u = Operator(qc).data
            for x in range(2 ** n):
                y = (x + sign * a) % 2 ** n
                assert abs(abs(u[y, x]) - 1) < 1e-9


def test_phi_add_old_formula_wrong():
    # Lean: phiAddOld_wrong — the angle formula used before the fix does not add 1 for n = 3.
    n, a = 3, 1
    qc = QuantumCircuit(n)
    ac._qft(qc, list(range(n)))
    for i in range(n):
        turns = sum(1 / 2 ** (i - j + 1) for j in range(i + 1) if (a >> j) & 1)
        qc.p(2 * math.pi * turns, i)
    ac._qft(qc, list(range(n)), inverse=True)
    sv = Statevector.from_label("000").evolve(qc)
    assert abs(sv.data[1]) < 0.99
