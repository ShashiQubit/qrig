"""Qiskit ``DAGCircuit`` optimisation with the control equations of the paper.

This module connects Qiskit's circuit DAG to the Lean-verified peephole optimiser
(``Qrig/Core/Peephole.lean``, proved sound in ``QrigProofs/Peephole*.lean``).

How the optimiser treats the eight equations
--------------------------------------------
It does **pattern matching with rewrite rules**, not symbolic matrix manipulation.
Every gate of the DAG is read as a *multiply controlled one-qubit gate*
``C^{b1}_{w1} ... C^{bk}_{wk}(U)`` on a target wire (``cx``, ``ccx``, ``mcx``, ``cp``,
``mcphase``, ``crz``, ``ch``, ``c3sx``, ``h``, ``t``, ``u``, ... all have this shape). The
verified core then scans the gate list in DAG (topological) order and rewrites:

=========  ========  ====================================================================
rule       equation  rewrite
=========  ========  ====================================================================
idRem      (b)       ``C..C(id) -> nothing``
fuse       (a)       ``C^c(f) ; C^c(g) -> C^c(f;g)``  (e.g. ``cp(a) cp(b) -> cp(a+b)``)
cancel     (a)+(b)   ``C^c(f) ; C^c(f^-1) -> nothing`` (e.g. ``ccx ccx``)
compl      (e)       ``C^c C0_w(f) ; C^c C1_w(f) -> C^c(f)``  (drops the control ``w``)
xconj      (d)       ``x_w ; M ; x_w -> M`` with the colour of every control on ``w`` flipped
commute    (f)       gates with contradictory controls commute; so do gates that share
                     wires only as controls or as targets of diagonal gates
=========  ========  ====================================================================

A new gate is merged with an earlier gate whenever it can be moved backwards to it past
gates it provably commutes with (a bounded window). Equations (c), (g), (h) are
structural equations about ``+`` and the symmetry ``sigma``; in the flat DAG view they
are implicit (wire placement), and (g) is how Qiskit already defines ``swap``.

Every rewrite, and the whole optimiser, is proved in Lean to preserve the action of
the circuit on every state vector, **exactly** (``peephole_sound``). Angles are passed to
the core as exact rational multiples of pi; the only floating point step is the final
conversion of a fused angle back to a Qiskit float parameter.

Operations the core does not model (measurements, resets, barriers, conditional or
parameterised gates, ``swap`` by default) are kept as they are; the optimiser never moves
a gate across them (the circuit is cut into segments at those operations, using a
topological order that postpones them as long as possible).
"""
from __future__ import annotations

import math
import time
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

from ._native import call

try:  # pragma: no cover - import guard
    from qiskit.circuit import ControlledGate, Gate
    from qiskit.circuit.library import (HGate, PhaseGate, RXGate, RYGate, RZGate, SdgGate, UGate,
                                        SGate, SXdgGate, SXGate, TdgGate, TGate, XGate, YGate,
                                        ZGate)
    from qiskit.converters import circuit_to_dag, dag_to_circuit
    from qiskit.dagcircuit import DAGCircuit
    from qiskit.transpiler.basepasses import TransformationPass
except ImportError as e:  # pragma: no cover
    raise ImportError("qrig.dag requires qiskit (pip install qiskit)") from e

RULES = ("idRem", "fuse", "cancel", "compl", "xconj")

#: Operations that are never expanded into their definition (kept as barriers).
DEFAULT_KEEP = frozenset({"swap", "measure", "reset", "barrier", "delay", "store"})

# A flat gate: (opcode, angle-or-None, target wire, ((wire, colour), ...))
Flat = Tuple[str, object, int, Tuple[Tuple[int, bool], ...]]


# ============================================================================ angles
def to_pi_fraction(theta) -> Optional[Fraction]:
    """``theta / pi`` as an exact rational (``None`` for symbolic parameters).

    Angles that are within 1e-12 of a fraction with denominator at most 2**16 (e.g. pi/8)
    are snapped to it; others are converted exactly (the binary value of the float)."""
    try:
        t = float(theta)
    except (TypeError, ValueError):
        return None
    if not math.isfinite(t):
        return None
    x = t / math.pi
    f = Fraction(x).limit_denominator(1 << 16)
    if abs(float(f) - x) <= 1e-12:
        return f
    return Fraction(x)


def _tok(f: Fraction) -> str:
    return str(f.numerator) if f.denominator == 1 else f"{f.numerator}/{f.denominator}"


def _angle(f: Fraction, period: int) -> float:
    """``f * pi`` with ``f`` reduced into ``(-period/2, period/2]``."""
    f = f % period
    if f > Fraction(period, 2):
        f -= period
    return float(f) * math.pi


# ============================================================================ Qiskit -> flat
_FIXED = {"x": [("X", None)], "y": [("Y", None)], "h": [("H", None)], "sx": [("SX", None)],
          "sxdg": [("SXDG", None)], "z": [("P", Fraction(1))], "s": [("P", Fraction(1, 2))],
          "sdg": [("P", Fraction(-1, 2))], "t": [("P", Fraction(1, 4))],
          "tdg": [("P", Fraction(-1, 4))], "id": [], "i": []}


class _GenTable:
    """Opaque one-qubit gates, numbered so that equal gates get equal numbers."""

    def __init__(self):
        self.ops: List[object] = []
        self.index: Dict[object, int] = {}

    def key(self, op):
        """Equal keys only for gates with identical matrices (or identical symbolic
        parameters, for unbound parameterised gates)."""
        import numpy as np
        try:
            m = np.asarray(op.to_matrix(), dtype=complex)
            return ("m", m.shape, m.tobytes())
        except Exception:
            pass
        if getattr(op, "is_parameterized", lambda: False)():
            return ("sym", op.name, tuple(str(p) for p in op.params))
        return None

    def get(self, op) -> Optional[int]:
        k = self.key(op)
        if k is None:
            return None
        if k not in self.index:
            self.index[k] = len(self.ops)
            self.ops.append(op)
        return self.index[k]


def _base_ops(op, gens: _GenTable) -> Optional[List[Tuple[str, object]]]:
    """A one-qubit Qiskit gate as a sequence (time order) of base gates of the core."""
    name = op.name
    if name in _FIXED:
        return list(_FIXED[name])
    if name in ("p", "u1", "phase", "rz", "rx", "ry", "u", "u3", "u2", "r"):
        ps = [to_pi_fraction(p) for p in op.params]
        if any(p is None for p in ps):      # symbolic: an opaque gate
            k = gens.get(op) if op.num_qubits == 1 else None
            return None if k is None else [("G", k)]
        if name in ("p", "u1", "phase"):
            return [("P", ps[0])]
        if name in ("rz", "rx", "ry"):
            return [(name.upper(), ps[0])]
        if name in ("u", "u3"):          # U(t, f, l) = P(f) RY(t) P(l)  (exactly)
            t, f, l = ps
            return [("P", l), ("RY", t), ("P", f)]
        if name == "u2":                 # U2(f, l) = U(pi/2, f, l)
            f, l = ps
            return [("P", l), ("RY", Fraction(1, 2)), ("P", f)]
        t, f = ps                        # R(t, f) = U(t, f - pi/2, pi/2 - f)
        return [("P", Fraction(1, 2) - f), ("RY", t), ("P", f - Fraction(1, 2))]
    if isinstance(op, Gate) and op.num_qubits == 1:
        k = gens.get(op)
        return None if k is None else [("G", k)]
    return None


def _convert(op, qubits: Sequence[int], gens: _GenTable) -> Optional[List[Flat]]:
    """Flat gates for a Qiskit operation on the given wires, or ``None`` if the
    operation is not a multiply controlled one-qubit gate from the supported set."""
    if getattr(op, "condition", None) is not None:
        return None
    if isinstance(op, ControlledGate):
        base = op.base_gate
        k = op.num_ctrl_qubits
        if op.name == "cu" or base.num_qubits != 1 or op.num_qubits != k + 1:
            return None
        st = op.ctrl_state
        ctrls = tuple((qubits[j], bool((st >> j) & 1)) for j in range(k))
        tgt = qubits[k]
        bops = _base_ops(base, gens)
        if bops is None:
            return None
        return [(o, a, tgt, ctrls) for o, a in bops]
    if isinstance(op, Gate) and op.num_qubits == 1:
        bops = _base_ops(op, gens)
        if bops is None:
            return None
        return [(o, a, qubits[0], ()) for o, a in bops]
    return None


def _flat_to_str(g: Flat) -> str:
    o, a, t, cs = g
    parts = [o]
    if a is not None:
        parts.append(_tok(a) if isinstance(a, Fraction) else str(a))
    parts.append(str(t))
    parts += [("+" if b else "-") + str(w) for w, b in cs]
    return " ".join(parts)


def _parse_flat(s: str) -> Flat:
    toks = s.split()
    o = toks[0]
    i = 1
    a = None
    if o in ("P", "RZ", "RX", "RY"):
        a = Fraction(toks[1])
        i = 2
    elif o == "G":
        a = int(toks[1])
        i = 2
    t = int(toks[i])
    cs = tuple((int(c[1:]), c[0] == "+") for c in toks[i + 1:])
    return (o, a, t, cs)


# ============================================================================ flat -> Qiskit
def _qiskit_base(o: str, a, gens: _GenTable, controlled: bool):
    if o == "X":
        return XGate()
    if o == "Y":
        return YGate()
    if o == "H":
        return HGate()
    if o == "SX":
        return SXGate()
    if o == "SXDG":
        return SXdgGate()
    if o == "P":
        f = a % 2
        named = {Fraction(1): ZGate, Fraction(1, 2): SGate, Fraction(3, 2): SdgGate,
                 Fraction(1, 4): TGate, Fraction(7, 4): TdgGate}
        if f in named and (not controlled or f == 1):
            return named[f]()
        return PhaseGate(_angle(a, 2))
    if o == "RZ":
        return RZGate(_angle(a, 4))
    if o == "RX":
        return RXGate(_angle(a, 4))
    if o == "RY":
        return RYGate(_angle(a, 4))
    if o == "G":
        return gens.ops[a]
    raise ValueError(f"unknown opcode {o}")


def flat_to_qiskit(g: Flat, gens: _GenTable):
    """The Qiskit operation and qubit indices of a flat gate."""
    o, a, t, cs = g
    base = _qiskit_base(o, a, gens, bool(cs))
    if not cs:
        return base, [t]
    state = sum(1 << j for j, (_, b) in enumerate(cs) if b)
    try:
        gate = base.control(len(cs), ctrl_state=state, annotated=False)
    except TypeError:  # older Qiskit
        gate = base.control(len(cs), ctrl_state=state)
    return gate, [w for w, _ in cs] + [t]


# ============================================================================ the optimiser
@dataclass
class PeepholeStats:
    """Rule applications and bookkeeping of one optimisation run."""
    rules: Dict[str, int] = field(default_factory=lambda: {r: 0 for r in RULES})
    gates_in: int = 0          # flat gates sent to the verified core
    gates_out: int = 0         # flat gates returned
    segments: int = 0          # number of calls into the core
    kept_ops: int = 0          # operations left untouched (measure, barrier, ...)
    expanded_ops: int = 0      # operations replaced by their definition
    seconds_core: float = 0.0  # time spent in the verified core

    def merge_rules(self, counts: Sequence[int]):
        for r, c in zip(RULES, counts):
            self.rules[r] += int(c)

    def as_dict(self) -> dict:
        d = dict(self.__dict__)
        d["rules"] = dict(self.rules)
        return d


def peephole_flat(gates: List[Flat], window: int = 128, fuel: int = 16,
                  stats: Optional[PeepholeStats] = None) -> List[Flat]:
    """Run the verified core on a list of flat gates."""
    if not gates:
        return []
    t0 = time.perf_counter()
    out = call("peephole", f"{window} {fuel} | " + ";".join(_flat_to_str(g) for g in gates))
    head, _, body = out.partition("|")
    res = [_parse_flat(s) for s in body.split(";") if s.strip()]
    if stats is not None:
        stats.merge_rules(head.split())
        stats.gates_in += len(gates)
        stats.gates_out += len(res)
        stats.segments += 1
        stats.seconds_core += time.perf_counter() - t0
    return res


def _expand(op, depth: int, keep) -> Optional[list]:
    """Definition of a unitary gate as (op, local qubit indices) pairs, plus phase."""
    if depth <= 0 or op.name in keep or not isinstance(op, Gate):
        return None
    if op.is_parameterized():
        return None
    if getattr(op, "condition", None) is not None:
        return None
    try:
        d = op.definition
    except Exception:  # pragma: no cover
        return None
    if d is None:
        return None
    return d


def optimize_dag(dag: "DAGCircuit", window: int = 128, fuel: int = 16,
                 expand: bool = True, keep=DEFAULT_KEEP, max_segment: int = 20000,
                 stats: Optional[PeepholeStats] = None) -> "DAGCircuit":
    """Optimise a ``DAGCircuit`` with the verified control-equation rewriter.

    * ``window``: how far back (in gates) a new gate may be moved to find a partner;
    * ``fuel``: maximal number of passes (the core stops earlier at a fixed point);
    * ``expand``: replace gates the core cannot read (e.g. ``rccx``, ``cswap``, ``Q``) by
      their Qiskit definition, recursively, except operations listed in ``keep``.
    """
    stats = stats if stats is not None else PeepholeStats()
    gens = _GenTable()
    qindex = {q: i for i, q in enumerate(dag.qubits)}
    out = dag.copy_empty_like()
    phase = [0.0]
    items: list = []  # sequence of ("g", Flat) | ("op", op, qargs, cargs)

    def emit_op(op, qargs, cargs, depth=12):
        if isinstance(op, Gate) and not cargs:
            fl = _convert(op, [qindex[q] for q in qargs], gens)
            if fl is not None:
                items.extend(("g", g) for g in fl)
                return
            if expand:
                d = _expand(op, depth, keep)
                if d is not None:
                    stats.expanded_ops += 1
                    phase[0] += float(d.global_phase)
                    for inst in d.data:
                        sub_q = [qargs[d.find_bit(q).index] for q in inst.qubits]
                        emit_op(inst.operation, sub_q, [], depth - 1)
                    return
        stats.kept_ops += 1
        items.append(("op", op, qargs, cargs))

    def is_opaque(node) -> bool:
        op = getattr(node, "op", None)
        return op is not None and (not isinstance(op, Gate) or op.name in keep)

    for node in dag.topological_op_nodes(key=lambda n: ("1" if is_opaque(n) else "0")
                                         + "%012d" % n._node_id):
        emit_op(node.op, list(node.qargs), list(node.cargs))

    pending: Dict[int, List[Flat]] = {}

    def put(op, qs):
        out.apply_operation_back(op, tuple(dag.qubits[w] for w in qs), (), check=False)

    def release(w: int):
        """Emit the buffered uncontrolled one-qubit gates of wire ``w``, turning each
        ``P(l) RY(t) P(f)`` run back into the single gate ``U(t, f, l)`` (exact)."""
        buf = pending.pop(w, [])
        i = 0
        zero = Fraction(0)
        while i < len(buf):
            ops = [g[0] for g in buf[i:i + 3]]
            if ops[:2] == ["P", "RY"]:
                l, t = buf[i][1], buf[i + 1][1]
                f, used = (buf[i + 2][1], 3) if ops[2:] == ["P"] else (zero, 2)
            elif ops[:2] == ["RY", "P"]:
                l, t, f, used = zero, buf[i][1], buf[i + 1][1], 2
            else:
                op, qs = flat_to_qiskit(buf[i], gens)
                put(op, qs)
                i += 1
                continue
            put(UGate(_angle(t, 4), _angle(f, 2), _angle(l, 2)), [w])
            i += used

    def emit_flat(g: Flat):
        o, a, t, cs = g
        if not cs and o in ("P", "RY"):
            pending.setdefault(t, []).append(g)
            return
        for w in [t] + [c for c, _ in cs]:
            if w in pending:
                release(w)
        op, qs = flat_to_qiskit(g, gens)
        put(op, qs)

    def release_all(ws=None):
        for w in list(pending) if ws is None else [w for w in ws if w in pending]:
            release(w)

    def flush(seg: List[Flat]):
        for i in range(0, len(seg), max_segment):
            for g in peephole_flat(seg[i:i + max_segment], window, fuel, stats):
                emit_flat(g)

    seg: List[Flat] = []
    for it in items:
        if it[0] == "g":
            seg.append(it[1])
        else:
            flush(seg)
            seg = []
            _, op, qargs, cargs = it
            release_all([qindex[q] for q in qargs])
            out.apply_operation_back(op, tuple(qargs), tuple(cargs), check=False)
    flush(seg)
    release_all()
    out.global_phase = dag.global_phase + phase[0]
    return out


def optimize_circuit(qc, **kw):
    """Optimise a ``QuantumCircuit``; returns ``(circuit, PeepholeStats)``."""
    stats = PeepholeStats()
    dag = optimize_dag(circuit_to_dag(qc), stats=stats, **kw)
    out = dag_to_circuit(dag)
    out.name = qc.name
    return out, stats


class QrigControlEquations(TransformationPass):
    """Qiskit transpiler pass: DAG-level optimisation with the paper's control equations,
    every rewrite proved sound in Lean (``peephole_sound``).

    The rule statistics of the last run are stored in ``self.property_set["qrig_stats"]``.
    """

    def __init__(self, window: int = 128, fuel: int = 16, expand: bool = True,
                 keep=DEFAULT_KEEP):
        super().__init__()
        self.window, self.fuel, self.expand, self.keep = window, fuel, expand, keep

    def run(self, dag):
        stats = PeepholeStats()
        new = optimize_dag(dag, self.window, self.fuel, self.expand, self.keep, stats=stats)
        self.property_set["qrig_stats"] = stats
        return new
