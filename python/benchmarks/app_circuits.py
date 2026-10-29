"""Application circuits for the qrig study that are *not* in MQT Bench.

Every builder returns a unitary ``QuantumCircuit`` written the way a Qiskit user would
write it (library objects or textbook constructions), unrolled to standard gates and
multi-controlled gates with ``mqt_pipeline.expose``. Nothing here is tuned to qrig:
the constructions are the standard ones from the literature / Qiskit documentation.

``grover_sat``     Grover search for a satisfying assignment of a random 3-SAT formula
                   (planted solution), phase oracle built gate-by-gate from the clauses
                   with an ancilla per clause (compute / MCZ-flag / uncompute).
``qrom``           table lookup (QROM) of a random table: for every address, X on the
                   0-bits, multi-controlled X onto each 1-bit of the data word, X back.
``incrementer``    n-bit +1 counter (cascade of multi-controlled X), the shift operator
                   of quantum walks.
``lib_grover``     Qiskit's ``grover_operator`` with a multi-controlled-Z oracle marking
                   one random item.
``comparator``     Qiskit ``IntegerComparator`` (|x>|0> -> |x>|x >= c>).
``weighted_adder`` Qiskit ``WeightedAdder``.
``poly_rotation``  Qiskit ``PolynomialPauliRotations`` (amplitude-loading step of
                   quantum Monte-Carlo / option pricing).
``state_prep``     Qiskit ``StatePreparation`` of a random real vector (uniformly
                   controlled rotations).
``ising_trotter``  2 Trotter steps of a transverse-field Ising chain (control case:
                   no controlled gates at all).
"""
from __future__ import annotations

import math
import os
import random
import sys

import numpy as np
from qiskit import QuantumCircuit

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from mqt_pipeline import expose  # noqa: E402

SEED = 20261009


def _rng(name: str, n: int) -> random.Random:
    return random.Random(f"{SEED}-{name}-{n}")


def grover_sat(nvars: int, nclauses: int | None = None) -> QuantumCircuit:
    rng = _rng("sat", nvars)
    m = nclauses or nvars
    sol = [rng.random() < 0.5 for _ in range(nvars)]
    clauses = []
    while len(clauses) < m:
        vs = rng.sample(range(nvars), 3)
        lits = [(v, rng.random() < 0.5) for v in vs]          # (var, negated)
        if any((sol[v] != neg) for v, neg in lits):            # satisfied by planted sol
            clauses.append(lits)
    n = nvars + m + 1
    qc = QuantumCircuit(n, name=f"grover_sat_{nvars}")
    anc = list(range(nvars, nvars + m))
    out = n - 1
    qc.h(range(nvars))
    qc.x(out)
    qc.h(out)

    def clause_gate(c, j):
        # ancilla j := OR of literals = NOT AND of negated literals
        for v, neg in c:
            if not neg:
                qc.x(v)
        qc.mcx([v for v, _ in c], anc[j])
        qc.x(anc[j])
        for v, neg in c:
            if not neg:
                qc.x(v)

    iters = 1
    for _ in range(iters):
        for j, c in enumerate(clauses):
            clause_gate(c, j)
        qc.mcx(anc, out)
        for j, c in reversed(list(enumerate(clauses))):
            # uncompute (each clause_gate is self-inverse)
            clause_gate(c, j)
        # diffusion
        qc.h(range(nvars))
        qc.x(range(nvars))
        qc.h(nvars - 1)
        qc.mcx(list(range(nvars - 1)), nvars - 1)
        qc.h(nvars - 1)
        qc.x(range(nvars))
        qc.h(range(nvars))
    return qc


def qrom(addr: int, data: int) -> QuantumCircuit:
    rng = _rng("qrom", addr * 10 + data)
    n = addr + data
    qc = QuantumCircuit(n, name=f"qrom_{addr}x{data}")
    for a in range(2 ** addr):
        word = rng.randrange(1, 2 ** data)
        zeros = [q for q in range(addr) if not (a >> q) & 1]
        for q in zeros:
            qc.x(q)
        for b in range(data):
            if (word >> b) & 1:
                qc.mcx(list(range(addr)), addr + b)
        for q in zeros:
            qc.x(q)
    return qc


def incrementer(n: int) -> QuantumCircuit:
    qc = QuantumCircuit(n, name=f"incrementer_{n}")
    for t in reversed(range(n)):
        if t == 0:
            qc.x(0)
        else:
            qc.mcx(list(range(t)), t)
    return qc


def lib_grover(n: int) -> QuantumCircuit:
    from qiskit.circuit.library import grover_operator
    rng = _rng("libgrover", n)
    marked = rng.randrange(2 ** n)
    oracle = QuantumCircuit(n)
    zeros = [q for q in range(n) if not (marked >> q) & 1]
    for q in zeros:
        oracle.x(q)
    oracle.h(n - 1)
    oracle.mcx(list(range(n - 1)), n - 1)
    oracle.h(n - 1)
    for q in zeros:
        oracle.x(q)
    g = grover_operator(oracle)
    qc = QuantumCircuit(n, name=f"lib_grover_{n}")
    qc.h(range(n))
    qc.compose(g, inplace=True)
    return expose(qc)


def comparator(k: int) -> QuantumCircuit:
    from qiskit.circuit.library import IntegerComparator
    rng = _rng("cmp", k)
    c = IntegerComparator(k, rng.randrange(1, 2 ** k))
    return expose(c.decompose())


def weighted_adder(k: int) -> QuantumCircuit:
    from qiskit.circuit.library import WeightedAdder
    rng = _rng("wadd", k)
    w = [rng.randrange(1, 4) for _ in range(k)]
    return expose(WeightedAdder(k, w).decompose())


def poly_rotation(k: int) -> QuantumCircuit:
    from qiskit.circuit.library import PolynomialPauliRotations
    rng = _rng("poly", k)
    coeffs = [round(rng.uniform(-1, 1), 3) for _ in range(3)]
    return expose(PolynomialPauliRotations(k, coeffs).decompose())


def state_prep(n: int) -> QuantumCircuit:
    from qiskit.circuit.library import StatePreparation
    rs = np.random.default_rng(SEED + n)
    v = rs.normal(size=2 ** n)
    v /= np.linalg.norm(v)
    qc = QuantumCircuit(n, name=f"state_prep_{n}")
    qc.append(StatePreparation(v), range(n))
    # unroll down to standard gates (StatePreparation -> isometry -> ucr gates ...)
    for _ in range(8):
        qc = qc.decompose()
        if all(i.operation.name in ("cx", "ry", "rz", "u", "u3", "h", "x", "p", "r")
               for i in qc.data):
            break
    return expose(qc)


def ising_trotter(n: int, steps: int = 2) -> QuantumCircuit:
    qc = QuantumCircuit(n, name=f"ising_{n}")
    for _ in range(steps):
        for i in range(n - 1):
            qc.rzz(0.3, i, i + 1)
        for i in range(n):
            qc.rx(0.7, i)
    return qc


#: (family, size parameter, builder); sizes chosen so that the total qubit count
#: stays at or below 10 (exact density-matrix simulation).
APP_CASES = [
    ("grover_sat", "3v3c", lambda: grover_sat(3)),
    ("grover_sat", "4v4c", lambda: grover_sat(4)),
    ("grover_sat", "4v5c", lambda: grover_sat(4, 5)),
    ("qrom", "2x3", lambda: qrom(2, 3)),
    ("qrom", "3x3", lambda: qrom(3, 3)),
    ("qrom", "3x5", lambda: qrom(3, 5)),
    ("qrom", "4x4", lambda: qrom(4, 4)),
    ("incrementer", 4, lambda: incrementer(4)),
    ("incrementer", 6, lambda: incrementer(6)),
    ("incrementer", 8, lambda: incrementer(8)),
    ("lib_grover", 4, lambda: lib_grover(4)),
    ("lib_grover", 5, lambda: lib_grover(5)),
    ("lib_grover", 6, lambda: lib_grover(6)),
    ("comparator", 3, lambda: comparator(3)),
    ("comparator", 4, lambda: comparator(4)),
    ("comparator", 5, lambda: comparator(5)),
    ("weighted_adder", 3, lambda: weighted_adder(3)),
    ("weighted_adder", 4, lambda: weighted_adder(4)),
    ("poly_rotation", 3, lambda: poly_rotation(3)),
    ("poly_rotation", 5, lambda: poly_rotation(5)),
    ("state_prep", 3, lambda: state_prep(3)),
    ("state_prep", 5, lambda: state_prep(5)),
    ("ising_trotter", 6, lambda: ising_trotter(6)),
    ("ising_trotter", 10, lambda: ising_trotter(10)),
]


# ---------------------------------------------------------------- more families
def lcu_select(k: int, nsys: int) -> QuantumCircuit:
    """SELECT oracle of a linear combination of unitaries (LCU / qubitization): for every
    index j of a k-qubit register, apply a random Pauli string P_j to the system,
    controlled on |j> (textbook ancilla-free construction: X on the 0-bits of j,
    multi-controlled Paulis, X back)."""
    rng = _rng("select", k * 10 + nsys)
    n = k + nsys
    qc = QuantumCircuit(n, name=f"lcu_select_{k}x{nsys}")
    ctrls = list(range(k))
    for j in range(2 ** k):
        zeros = [q for q in range(k) if not (j >> q) & 1]
        for q in zeros:
            qc.x(q)
        for s in range(nsys):
            p = rng.choice("IXYZ")
            t = k + s
            if p == "X":
                qc.mcx(ctrls, t)
            elif p == "Z":
                qc.h(t)
                qc.mcx(ctrls, t)
                qc.h(t)
            elif p == "Y":
                qc.sdg(t)
                qc.mcx(ctrls, t)
                qc.s(t)
        for q in zeros:
            qc.x(q)
    return qc


def swap_test(m: int) -> QuantumCircuit:
    """Swap test between two m-qubit registers (ancilla, H, controlled-SWAPs, H), with
    random single-qubit state preparation on both registers."""
    rng = _rng("swap", m)
    n = 2 * m + 1
    qc = QuantumCircuit(n, name=f"swap_test_{m}")
    for q in range(1, n):
        qc.ry(round(rng.uniform(0, math.pi), 3), q)
    qc.h(0)
    for i in range(m):
        qc.cswap(0, 1 + i, 1 + m + i)
    qc.h(0)
    return qc


def _phi_add(qc, a: int, reg, ctrls, sign=1):
    """Draper adder in Fourier space: add the constant a (mod 2^len(reg)) to a
    Fourier-transformed register, controlled on ``ctrls`` (Beauregard 2003)."""
    n = len(reg)
    for i, q in enumerate(reg):          # reg[0] least significant
        # Qiskit's QFTGate maps |x> to sum_k e^{2 pi i x k / 2^n} |k>, so qubit i of the
        # transformed register carries the phase 2 pi x 2^i / 2^n.
        ang = (sign * 2 * math.pi * ((a * 2 ** i) % 2 ** n) / 2 ** n) % (2 * math.pi)
        if abs(ang) < 1e-12:
            continue
        if ctrls:
            qc.mcp(ang, list(ctrls), q)
        else:
            qc.p(ang, q)


def _qft(qc, reg, inverse=False):
    from qiskit.circuit.library import QFTGate
    g = QFTGate(len(reg))
    qc.append(g.inverse() if inverse else g, reg)


def modular_adder_shor(nbits: int) -> QuantumCircuit:
    """Doubly-controlled modular adder ccΦADD(a) mod N of Shor's algorithm in
    Beauregard's 2n+3-qubit construction (here only the adder block: 2 controls,
    an (n+1)-qubit register in Fourier space and one ancilla)."""
    rng = _rng("modadd", nbits)
    N = rng.randrange(2 ** (nbits - 1) + 1, 2 ** nbits) | 1
    a = rng.randrange(1, N)
    c1, c2 = 0, 1
    reg = list(range(2, 2 + nbits + 1))
    anc = 2 + nbits + 1
    qc = QuantumCircuit(anc + 1, name=f"shor_modadd_{nbits}")
    _qft(qc, reg)
    _phi_add(qc, a, reg, [c1, c2])
    _phi_add(qc, N, reg, [], sign=-1)
    _qft(qc, reg, inverse=True)
    qc.cx(reg[-1], anc)
    _qft(qc, reg)
    _phi_add(qc, N, reg, [anc])
    _phi_add(qc, a, reg, [c1, c2], sign=-1)
    _qft(qc, reg, inverse=True)
    qc.x(reg[-1])
    qc.cx(reg[-1], anc)
    qc.x(reg[-1])
    _qft(qc, reg)
    _phi_add(qc, a, reg, [c1, c2])
    _qft(qc, reg, inverse=True)
    return expose(qc.decompose(gates_to_decompose=["qft", "IQFT", "qft_dg"]))


def hamming_weight(nin: int) -> QuantumCircuit:
    """Population count (RevLib-style 'rd' function): adds every input bit to a
    ceil(log2(nin+1))-bit counter with a controlled incrementer (MCX cascade)."""
    nout = max(1, math.ceil(math.log2(nin + 1)))
    qc = QuantumCircuit(nin + nout, name=f"hamming_weight_{nin}")
    cnt = list(range(nin, nin + nout))
    for i in range(nin):
        for t in reversed(range(nout)):
            qc.mcx([i] + cnt[:t], cnt[t])
    return qc


def mcx_ladder_oracle(n: int) -> QuantumCircuit:
    """Boolean 'comparison with a constant' oracle x == c built the textbook way
    (X on 0-bits of c, MCX onto the target, X back), applied for several constants:
    the structure of membership / database-lookup oracles."""
    rng = _rng("member", n)
    qc = QuantumCircuit(n + 1, name=f"membership_oracle_{n}")
    for c in rng.sample(range(2 ** n), min(2 ** n, 2 * n)):
        zeros = [q for q in range(n) if not (c >> q) & 1]
        for q in zeros:
            qc.x(q)
        qc.mcx(list(range(n)), n)
        for q in zeros:
            qc.x(q)
    return qc


APP_CASES += [
    ("lcu_select", "2x3", lambda: lcu_select(2, 3)),
    ("lcu_select", "3x3", lambda: lcu_select(3, 3)),
    ("lcu_select", "3x5", lambda: lcu_select(3, 5)),
    ("swap_test", 2, lambda: swap_test(2)),
    ("swap_test", 3, lambda: swap_test(3)),
    ("swap_test", 4, lambda: swap_test(4)),
    ("shor_modadd", 3, lambda: modular_adder_shor(3)),
    ("shor_modadd", 4, lambda: modular_adder_shor(4)),
    ("hamming_weight", 3, lambda: hamming_weight(3)),
    ("hamming_weight", 5, lambda: hamming_weight(5)),
    ("hamming_weight", 7, lambda: hamming_weight(7)),
    ("membership_oracle", 4, lambda: mcx_ladder_oracle(4)),
    ("membership_oracle", 6, lambda: mcx_ladder_oracle(6)),
]
