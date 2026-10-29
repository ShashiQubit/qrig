"""Conversion between qrig circuits and Qiskit ``QuantumCircuit`` objects.

Conventions: wire ``k`` of an ``n``-wire qrig circuit is Qiskit qubit ``n - 1 - k``.
With this choice ``qiskit.quantum_info.Operator(to_qiskit(c)).data`` equals
``qrig.unitary(c, exact=False)`` entry-by-entry.

* :func:`to_qiskit` exports a circuit.  Uncontrolled symmetries are compiled away by
  relabelling qubits (they cost no gates); controlled ones become Fredkin gates.
* :func:`from_qiskit` imports any circuit whose gates have matrix entries in Q(omega)
  (Clifford+T, multiply controlled Toffoli, NCV, controlled Hadamards, ...), after
  recursively unrolling gate definitions where needed.
* :class:`QrigOptimize` is a Qiskit transpiler pass running the verified optimiser.
"""
from __future__ import annotations

import cmath
import math
from typing import Dict, List, Sequence, Tuple

import numpy as np

from .circuit import (Circuit, SWAP, X, controlled_on, gate, matrix_name, on_wires, phase,
                      seq, I)
from .exact import OMEGA, ONE, QOmega

try:  # pragma: no cover - import guard
    from qiskit import QuantumCircuit
    from qiskit.circuit import ControlledGate, Gate
    from qiskit.circuit.library import (HGate, PhaseGate, SdgGate, SGate, SwapGate, SXdgGate,
                                        SXGate, TdgGate, TGate, UnitaryGate, XGate, YGate,
                                        ZGate)
    from qiskit.quantum_info import Operator
except ImportError as e:  # pragma: no cover
    raise ImportError("qrig.qiskit_bridge requires qiskit (pip install qiskit)") from e

_STD = {"h": HGate, "s": SGate, "sdg": SdgGate, "t": TGate, "tdg": TdgGate, "z": ZGate,
        "y": YGate, "sx": SXGate, "sxdg": SXdgGate, "x": XGate}


# ============================================================================ export
def control_gate(g, k: int, state: int):
    """``g.control(k, ctrl_state=state)`` as an explicit ``ControlledGate``."""
    try:
        return g.control(k, ctrl_state=state, annotated=False)
    except TypeError:  # older Qiskit
        return g.control(k, ctrl_state=state)


def _base_gate(c: Circuit):
    """Qiskit gate for a one-qubit qrig generator."""
    name = c.name or matrix_name(c.args)
    if name in _STD:
        return _STD[name]()
    m = np.array([[complex(c.args[0]), complex(c.args[1])],
                  [complex(c.args[2]), complex(c.args[3])]])
    return UnitaryGate(m, label="U")


def _append(qc, g, ctrls: List[Tuple[int, bool]], targets: List[int]):
    if ctrls:
        state = sum((1 << j) for j, (_, b) in enumerate(ctrls) if b)
        g = control_gate(g, len(ctrls), state)
        qc.append(g, [q for q, _ in ctrls] + targets)
    else:
        qc.append(g, targets)


def _emit(c: Circuit, wires: List[int], ctrls: List[Tuple[int, bool]], qc) -> List[int]:
    # explicit stack to support very long circuits
    k = c.kind
    if k == "id":
        return wires
    if k == "x":
        _append(qc, XGate(), ctrls, [wires[0]])
        return wires
    if k == "swap":
        if not ctrls:
            return [wires[1], wires[0]]
        _append(qc, SwapGate(), ctrls, [wires[0], wires[1]])
        return wires
    if k == "u":
        _append(qc, _base_gate(c), ctrls, [wires[0]])
        return wires
    if k == "ph":
        z = c.args[0]
        if (z * z.conj()) != ONE:
            raise ValueError(f"scalar {z} is not a phase; cannot export to Qiskit")
        ang = cmath.phase(complex(z))
        if not ctrls:
            qc.global_phase += ang
            return wires
        (q, b), rest = ctrls[-1], ctrls[:-1]
        if not b:
            qc.x(q)
        _append(qc, PhaseGate(ang), rest, [q])
        if not b:
            qc.x(q)
        return wires
    if k == "seq":
        w = wires
        stack = [c]
        # flatten nested sequences iteratively
        order: List[Circuit] = []
        while stack:
            d = stack.pop()
            if d.kind == "seq":
                stack.append(d.args[1])
                stack.append(d.args[0])
            else:
                order.append(d)
        for d in order:
            w = _emit(d, w, ctrls, qc)
        return w
    if k == "par":
        f, g = c.args
        wf = _emit(f, wires[:f.n], ctrls, qc)
        wg = _emit(g, wires[f.n:], ctrls, qc)
        return wf + wg
    if k == "ctrl":
        b, f = c.args
        _emit(f, wires[1:], ctrls + [(wires[0], b)], qc)
        return wires
    raise ValueError(f"unknown circuit node {k}")


def to_qiskit(c: Circuit, name: str | None = None) -> "QuantumCircuit":
    """Export a qrig circuit to a Qiskit ``QuantumCircuit``."""
    n = c.n
    qc = QuantumCircuit(n, name=name)
    start = [n - 1 - k for k in range(n)]
    final = _emit(c, list(start), [], qc)
    # undo the relabelling performed by uncontrolled swaps
    cur = list(final)  # logical wire k currently lives on qubit cur[k]
    for k in range(n):
        if cur[k] != start[k]:
            j = cur.index(start[k])
            qc.swap(cur[k], cur[j])
            cur[k], cur[j] = cur[j], cur[k]
    return qc


# ============================================================================ import
def _exact_matrix(op) -> Tuple[QOmega, QOmega, QOmega, QOmega]:
    m = Operator(op).data
    return tuple(QOmega.from_complex(complex(z)) for z in (m[0, 0], m[0, 1], m[1, 0], m[1, 1]))


def _phase_circuit(theta: float) -> Circuit | None:
    theta = float(theta)
    if abs(theta) < 1e-12:
        return None
    z = QOmega.from_complex(cmath.exp(1j * theta))
    return phase(z)


def _import_local(op, m: int, depth: int) -> Circuit:
    """Import a (non-controlled) Qiskit operation acting on ``m`` local wires
    (Qiskit local qubit ``j`` -> qrig wire ``m - 1 - j``)."""
    name = op.name
    if name == "x" and m == 1:
        return X
    if name == "swap" and m == 2:
        return SWAP
    if m == 1:
        try:
            return gate(_exact_matrix(op))
        except ValueError:
            pass
    if isinstance(op, ControlledGate):
        return _import_controlled(op, list(range(m)), m, depth)
    if getattr(op, "definition", None) is not None and depth < 32:
        sub = op.definition
        return _import_circuit(sub, depth + 1)
    raise ValueError(f"gate '{name}' has no exact representation over Q(exp(i pi/4))")


def _import_controlled(op, qubits: Sequence[int], n: int, depth: int) -> Circuit:
    k = op.num_ctrl_qubits
    state = op.ctrl_state
    controls = [(n - 1 - qubits[j], bool((state >> j) & 1)) for j in range(k)]
    tq = list(qubits[k:])
    base = _import_local(op.base_gate, len(tq), depth + 1)
    # base acts on local wires: local wire i <-> Qiskit local qubit (len-1-i)
    targets = [n - 1 - tq[len(tq) - 1 - i] for i in range(len(tq))]
    return controlled_on(base, controls, targets, n)


def _import_circuit(qc, depth: int = 0) -> Circuit:
    n = qc.num_qubits
    parts: List[Circuit] = []
    for inst in qc.data:
        op = inst.operation
        if op.name in ("barrier", "delay"):
            continue
        if not isinstance(op, Gate):
            raise ValueError(f"non-unitary instruction '{op.name}' cannot be imported")
        qubits = [qc.find_bit(q).index for q in inst.qubits]
        if isinstance(op, ControlledGate):
            parts.append(_import_controlled(op, qubits, n, depth))
            continue
        local = _import_local(op, len(qubits), depth)
        # local wire i <-> qubit qubits[len-1-i]
        wires = [n - 1 - qubits[len(qubits) - 1 - i] for i in range(len(qubits))]
        parts.append(on_wires(local, wires, n))
    ph = _phase_circuit(qc.global_phase)
    if ph is not None:
        parts.append(par(ph, I(n)) if n else ph)
    if not parts:
        return I(n)
    return seq(*parts)


def par(*cs):
    from .circuit import par as _par
    return _par(*cs)


def from_qiskit(qc: "QuantumCircuit") -> Circuit:
    """Import a Qiskit circuit (gates must have entries in Q(exp(i pi/4)))."""
    return _import_circuit(qc)


# ============================================================================ transpiler pass
def optimize_qiskit(qc: "QuantumCircuit") -> "QuantumCircuit":
    """Round-trip a Qiskit circuit through the verified qrig optimiser."""
    from .core import simplify
    return to_qiskit(simplify(from_qiskit(qc)), name=qc.name)


try:  # pragma: no cover - optional
    from qiskit.converters import circuit_to_dag, dag_to_circuit
    from qiskit.transpiler.basepasses import TransformationPass

    class QrigOptimize(TransformationPass):
        """Transpiler pass: optimise with the control equations (verified in Lean)."""

        def run(self, dag):
            qc = dag_to_circuit(dag)
            try:
                out = optimize_qiskit(qc)
            except ValueError:
                return dag  # gates outside Q(omega): leave untouched
            return circuit_to_dag(out)
except ImportError:  # pragma: no cover
    pass
