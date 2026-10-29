import os
import random
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import qrig  # noqa: E402
from qrig.qiskit_bridge import control_gate  # noqa: E402,F401
from qrig import C0, C1, H, I, S, SWAP, T, Tdg, V, Vdg, X, Y, Z, Sdg  # noqa: E402

NAMED = {"x": X, "h": H, "s": S, "sdg": Sdg, "t": T, "tdg": Tdg, "z": Z, "y": Y,
         "sx": V, "sxdg": Vdg}


def qiskit_gate(name):
    from qiskit.circuit.library import (HGate, SdgGate, SGate, SXdgGate, SXGate, TdgGate,
                                        TGate, XGate, YGate, ZGate)
    return {"x": XGate, "h": HGate, "s": SGate, "sdg": SdgGate, "t": TGate, "tdg": TdgGate,
            "z": ZGate, "y": YGate, "sx": SXGate, "sxdg": SXdgGate}[name]()


def operator(qc):
    from qiskit.quantum_info import Operator
    return Operator(qc).data


def assert_same_unitary(c, qc, up_to_phase=False):
    u = qrig.unitary(c, exact=False)
    v = operator(qc)
    if up_to_phase:
        k = np.argmax(np.abs(v))
        lam = u.flat[k] / v.flat[k]
        v = v * lam
    assert u.shape == v.shape
    assert np.allclose(u, v, atol=1e-9), f"mismatch for {c}"


def random_pair(rng: random.Random, n: int, depth: int):
    """A random circuit built *independently* in qrig and in Qiskit."""
    from qiskit import QuantumCircuit
    qc = QuantumCircuit(n)
    parts = []
    names = list(NAMED)
    for _ in range(depth):
        kind = rng.random()
        if kind < 0.1 and n >= 2:
            a, b = rng.sample(range(n), 2)
            parts.append(qrig.on_wires(SWAP, [a, b], n))
            qc.swap(n - 1 - a, n - 1 - b)
            continue
        name = rng.choice(names)
        k = rng.randint(0, min(3, n - 1))
        wires = rng.sample(range(n), k + 1)
        ctrl_wires, target = wires[:k], wires[k]
        vals = [rng.random() < 0.5 for _ in range(k)]
        parts.append(qrig.controlled_on(NAMED[name], list(zip(ctrl_wires, vals)), [target], n))
        g = qiskit_gate(name)
        if k:
            state = sum(1 << j for j, v in enumerate(vals) if v)
            g = control_gate(g, k, state)
        qc.append(g, [n - 1 - w for w in ctrl_wires] + [n - 1 - target])
    return (qrig.seq(*parts) if parts else I(n)), qc


@pytest.fixture
def rng():
    return random.Random(20260925)
