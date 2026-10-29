"""Circuits of the controlled prop cP ("One rig to control them all").

A :class:`Circuit` is an immutable term built from

* ``I(n)``            identities,
* ``X``               the distinguished involution (NOT gate),
* ``SWAP``            the symmetry sigma_{1,1},
* ``gate(M)``         one-qubit base generators (2x2 matrices over Q(omega)),
* ``phase(z)``        scalars (0 -> 0 generators, e.g. the global phase omega),
* ``f >> g``          sequential composition (first ``f``, then ``g``),
* ``f + g``           parallel composition (``f`` on the top wires),
* ``C1(f)``, ``C0(f)`` the two control functors (control on a new top wire).

Wire 0 is the *top* wire, i.e. the most significant bit of a basis index.  When a
circuit is exported to Qiskit, wire ``k`` of an ``n``-wire circuit becomes qubit
``n - 1 - k`` so that matrices agree entry-by-entry with Qiskit's conventions.

All semantic operations (unitary, simulation, equivalence, simplification,
synthesis, ...) are performed by the verified Lean core; see :mod:`qrig.core`.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from .exact import INV_SQRT2, OMEGA, ONE, ZERO, I as IMAG, QOmega

Matrix2 = Tuple[QOmega, QOmega, QOmega, QOmega]


class Circuit:
    """An immutable circuit term on ``n`` wires."""

    __slots__ = ("kind", "n", "args", "name", "_hash")

    def __init__(self, kind: str, n: int, args: tuple = (), name: Optional[str] = None):
        self.kind = kind
        self.n = n
        self.args = args
        self.name = name
        self._hash = None

    # ------------------------------------------------------------ combinators
    def __rshift__(self, other: "Circuit") -> "Circuit":
        """``f >> g``: first ``f``, then ``g``."""
        return seq(self, other)

    def __add__(self, other: "Circuit") -> "Circuit":
        """``f + g``: ``f`` on the top wires, ``g`` below (the paper's ``+``)."""
        return par(self, other)

    def controlled(self, value: bool = True) -> "Circuit":
        """Control on a new top wire (``C1`` if ``value`` else ``C0``)."""
        return C1(self) if value else C0(self)

    # ------------------------------------------------------------ inspection
    @property
    def num_wires(self) -> int:
        return self.n

    def gates(self) -> int:
        """Number of primitive gates (X, SWAP, base generators)."""
        total = 0
        stack = [self]
        while stack:
            c = stack.pop()
            if c.kind in ("x", "swap", "u", "ph"):
                total += 1
            elif c.kind in ("seq", "par"):
                stack.extend(c.args)
            elif c.kind == "ctrl":
                stack.append(c.args[1])
        return total

    def is_classical(self) -> bool:
        stack = [self]
        while stack:
            c = stack.pop()
            if c.kind in ("u", "ph"):
                return False
            if c.kind in ("seq", "par"):
                stack.extend(c.args)
            elif c.kind == "ctrl":
                stack.append(c.args[1])
        return True

    # ------------------------------------------------------------ serialisation
    def serialize(self) -> str:
        out: List[str] = []
        stack: List[object] = [self]
        while stack:
            c = stack.pop()
            if isinstance(c, str):
                out.append(c)
                continue
            k = c.kind
            if k == "id":
                out += ["I", str(c.n)]
            elif k == "x":
                out.append("X")
            elif k == "swap":
                out.append("W")
            elif k == "u":
                out.append("U")
                out += [z.token() for z in c.args]
            elif k == "ph":
                out += ["P", c.args[0].token()]
            elif k in ("seq", "par"):
                out.append("S" if k == "seq" else "T")
                stack.append(c.args[1])
                stack.append(c.args[0])
            elif k == "ctrl":
                out.append("C1" if c.args[0] else "C0")
                stack.append(c.args[1])
        return " ".join(out)

    @staticmethod
    def parse(text: str) -> "Circuit":
        toks = text.split()
        # iterative prefix parser
        results: List[Circuit] = []
        ops: List[tuple] = []  # pending constructors: (tag, needed, extra)
        pos = 0

        def reduce_():
            while ops and ops[-1][1] == 0:
                tag, _, extra, start = ops.pop()
                if tag in ("S", "T"):
                    g = results.pop()
                    f = results.pop()
                    results.append(seq2(f, g) if tag == "S" else par(f, g))
                else:
                    f = results.pop()
                    results.append(ctrl(tag == "C1", f))
                if ops:
                    t, need, e, s = ops[-1]
                    ops[-1] = (t, need - 1, e, s)

        def push_leaf(c):
            results.append(c)
            if ops:
                t, need, e, s = ops[-1]
                ops[-1] = (t, need - 1, e, s)
            reduce_()

        while pos < len(toks):
            t = toks[pos]
            pos += 1
            if t == "I":
                push_leaf(I(int(toks[pos])))
                pos += 1
            elif t == "X":
                push_leaf(X)
            elif t == "W":
                push_leaf(SWAP)
            elif t == "U":
                m = tuple(QOmega.from_token(toks[pos + i]) for i in range(4))
                pos += 4
                push_leaf(gate(m))
            elif t == "P":
                push_leaf(phase(QOmega.from_token(toks[pos])))
                pos += 1
            elif t in ("S", "T"):
                ops.append((t, 2, None, len(results)))
            elif t in ("C0", "C1"):
                ops.append((t, 1, None, len(results)))
            else:
                raise ValueError(f"unknown token {t!r}")
        if ops or len(results) != 1:
            raise ValueError("malformed circuit text")
        return results[0]

    # ------------------------------------------------------------ equality / display
    def _key(self):
        return self.serialize()

    def __eq__(self, other):
        return isinstance(other, Circuit) and self.n == other.n and self._key() == other._key()

    def __hash__(self):
        if self._hash is None:
            self._hash = hash(self._key())
        return self._hash

    def __repr__(self):
        return f"<qrig.Circuit on {self.n} wires: {_show(self, 60)}>"

    def __str__(self):
        return _show(self, 10 ** 9)

    # ------------------------------------------------------------ semantics (via the core)
    def unitary(self, exact: bool = True):
        from . import core
        return core.unitary(self, exact=exact)

    def simplify(self) -> "Circuit":
        from . import core
        return core.simplify(self)

    def dagger(self) -> "Circuit":
        from . import core
        return core.dagger(self)

    inverse = dagger

    def equiv(self, other: "Circuit", up_to_phase: bool = False) -> bool:
        from . import core
        return core.equivalent(self, other, up_to_phase=up_to_phase)

    def to_qiskit(self):
        from .qiskit_bridge import to_qiskit
        return to_qiskit(self)


# ---------------------------------------------------------------------------- display
def _show(c: Circuit, budget: int) -> str:
    parts: List[str] = []
    length = 0

    def emit(s):
        nonlocal length
        parts.append(s)
        length += len(s)

    stack: List[object] = [c]
    while stack:
        if length > budget:
            parts.append("...")
            break
        x = stack.pop()
        if isinstance(x, str):
            emit(x)
            continue
        k = x.kind
        if k == "id":
            emit(f"I{x.n}")
        elif k == "x":
            emit("X")
        elif k == "swap":
            emit("SWAP")
        elif k == "u":
            emit(x.name.upper() if x.name else "U")
        elif k == "ph":
            emit(f"phase({x.name or x.args[0]})")
        elif k == "seq":
            stack += [")", x.args[1], " >> ", x.args[0], "("]
        elif k == "par":
            stack += [")", x.args[1], " + ", x.args[0], "("]
        elif k == "ctrl":
            stack += [")", x.args[1], "C1(" if x.args[0] else "C0("]
    return "".join(parts)


# ---------------------------------------------------------------------------- constructors
def I(n: int) -> Circuit:
    """Identity on ``n`` wires."""
    if n < 0:
        raise ValueError("negative number of wires")
    return Circuit("id", n)


X = Circuit("x", 1)
"""The distinguished involution (NOT gate)."""

SWAP = Circuit("swap", 2)
"""The symmetry sigma_{1,1}."""


def gate(matrix, name: Optional[str] = None) -> Circuit:
    """A one-qubit base generator with the given 2x2 matrix (entries in Q(omega)).

    ``matrix`` may be ``[[a, b], [c, d]]`` or a flat 4-tuple; entries may be
    :class:`QOmega`, integers, fractions, or floats/complex numbers that are exactly
    recognisable as elements of Q(omega) (e.g. ``1/sqrt(2)``, ``(1+1j)/2``).
    """
    if isinstance(matrix, tuple) and len(matrix) == 4 and not isinstance(matrix[0], (list, tuple)):
        entries = matrix
    else:
        rows = [list(r) for r in matrix]
        if len(rows) != 2 or any(len(r) != 2 for r in rows):
            raise ValueError("a base gate must be a 2x2 matrix")
        entries = (rows[0][0], rows[0][1], rows[1][0], rows[1][1])
    m = tuple(QOmega.coerce(z) for z in entries)
    if name is None:
        name = _NAMES.get(m)
    return Circuit("u", 1, m, name)


def phase(z, name: Optional[str] = None) -> Circuit:
    """A scalar (0-wire generator), e.g. ``phase(OMEGA)``; controlled scalars are
    relative phases (``C1(phase(OMEGA))`` is the T gate)."""
    return Circuit("ph", 0, (QOmega.coerce(z),), name)


def seq2(f: Circuit, g: Circuit) -> Circuit:
    if f.n != g.n:
        raise ValueError(f"cannot compose circuits on {f.n} and {g.n} wires")
    return Circuit("seq", f.n, (f, g))


def seq(*cs: Circuit) -> Circuit:
    """Sequential composition (as a balanced tree) of one or more circuits."""
    if len(cs) == 1 and not isinstance(cs[0], Circuit):
        cs = tuple(cs[0])
    if not cs:
        raise ValueError("seq() needs at least one circuit")
    n = cs[0].n
    for c in cs:
        if c.n != n:
            raise ValueError(f"cannot compose circuits on {n} and {c.n} wires")

    def build(lo, hi):
        if hi - lo == 1:
            return cs[lo]
        mid = (lo + hi) // 2
        return Circuit("seq", n, (build(lo, mid), build(mid, hi)))

    return build(0, len(cs))


def par(*cs: Circuit) -> Circuit:
    """Parallel composition ``c0 + c1 + ...`` (``c0`` on the top wires)."""
    if len(cs) == 1 and not isinstance(cs[0], Circuit):
        cs = tuple(cs[0])
    if not cs:
        return I(0)
    acc = cs[-1]
    for c in reversed(cs[:-1]):
        acc = Circuit("par", c.n + acc.n, (c, acc))
    return acc


def ctrl(value: bool, f: Circuit) -> Circuit:
    return Circuit("ctrl", f.n + 1, (bool(value), f))


def C1(f: Circuit) -> Circuit:
    """Positive control on a new top wire."""
    return ctrl(True, f)


def C0(f: Circuit) -> Circuit:
    """Negative control on a new top wire."""
    return ctrl(False, f)


# ---------------------------------------------------------------------------- gate library
_h = INV_SQRT2
H = gate((_h, _h, _h, -_h), "h")
S = gate((ONE, ZERO, ZERO, IMAG), "s")
Sdg = gate((ONE, ZERO, ZERO, -IMAG), "sdg")
T = gate((ONE, ZERO, ZERO, OMEGA), "t")
Tdg = gate((ONE, ZERO, ZERO, OMEGA.conj()), "tdg")
Z = gate((ONE, ZERO, ZERO, -ONE), "z")
Y = gate((ZERO, -IMAG, IMAG, ZERO), "y")
_p = QOmega(Fraction(1, 2), 0, Fraction(1, 2), 0)   # (1+i)/2
_m = QOmega(Fraction(1, 2), 0, Fraction(-1, 2), 0)  # (1-i)/2
V = gate((_p, _m, _m, _p), "sx")
"""The V gate (square root of NOT), Qiskit's ``sx``."""
Vdg = gate((_m, _p, _p, _m), "sxdg")
XGATE = gate((ZERO, ONE, ONE, ZERO), "x")
"""The NOT matrix as an ordinary base generator (use :data:`X` for the involution)."""
GLOBAL_OMEGA = phase(OMEGA, "w")
"""The scalar omega = e^{i pi/4} (a 0 -> 0 generator)."""

_NAMES: Dict[Matrix2, str] = {}
for _g in (H, S, Sdg, T, Tdg, Z, Y, V, Vdg, XGATE):
    _NAMES[_g.args] = _g.name
_NAMES[(ONE, ZERO, ZERO, ONE)] = "id"

SX, SXdg = V, Vdg


def matrix_name(m: Matrix2) -> Optional[str]:
    return _NAMES.get(tuple(m))


# ---------------------------------------------------------------------------- wire placement
def adjacent_swap(pos: int, n: int) -> Circuit:
    """SWAP of wires ``pos`` and ``pos + 1`` in an ``n``-wire register."""
    if not 0 <= pos < n - 1:
        raise ValueError("bad swap position")
    parts = []
    if pos > 0:
        parts.append(I(pos))
    parts.append(SWAP)
    if n - pos - 2 > 0:
        parts.append(I(n - pos - 2))
    return par(*parts)


def _gather_swaps(order: Sequence[int], n: int) -> List[int]:
    """Adjacent swap positions bringing wire ``order[j]`` to position ``j``."""
    cur = list(range(n))
    swaps = []
    for j, w in enumerate(order):
        p = cur.index(w)
        while p > j:
            swaps.append(p - 1)
            cur[p - 1], cur[p] = cur[p], cur[p - 1]
            p -= 1
    return swaps


def on_wires(f: Circuit, wires: Sequence[int], n: int) -> Circuit:
    """Apply the ``m``-wire circuit ``f`` to the given wires of an ``n``-wire register
    (``wires[j]`` receives wire ``j`` of ``f``)."""
    wires = list(wires)
    m = f.n
    if len(wires) != m or len(set(wires)) != m or any(not 0 <= w < n for w in wires):
        raise ValueError(f"invalid wire list {wires} for a {m}-wire circuit on {n} wires")
    t = wires[0] if wires else 0
    if wires == list(range(t, t + m)):  # consecutive wires: no symmetry needed
        parts = ([I(t)] if t > 0 else []) + [f] + ([I(n - t - m)] if n - t - m > 0 else [])
        return par(*parts) if parts else f
    order = wires + [w for w in range(n) if w not in wires]
    swaps = _gather_swaps(order, n)
    body = f if m == n else par(f, I(n - m))
    if not swaps:
        return body
    P = [adjacent_swap(p, n) for p in swaps]
    return seq(*P, body, *reversed(P))


def controlled_on(f: Circuit, controls: Dict[int, bool] | Sequence[Tuple[int, bool]],
                  targets: Sequence[int], n: int) -> Circuit:
    """``f`` applied to ``targets`` and controlled by ``controls`` (wire -> value)."""
    items = list(controls.items()) if isinstance(controls, dict) else list(controls)
    targets = list(targets)
    cw = [w for w, _ in items]
    if len(set(cw) | set(targets)) != len(cw) + len(targets):
        raise ValueError("control and target wires must be distinct")
    t = targets[0] if targets else 0
    if (targets == list(range(t, t + len(targets))) and all(0 <= w < t for w in cw)
            and t + len(targets) <= n):
        # controls above consecutive targets: C^b(...) with idle wires, no symmetry needed
        vals = dict(items)
        body = f if t + f.n == n else par(f, I(n - t - f.n))
        j = t - 1
        while j >= 0:
            if j in vals:
                body = ctrl(vals[j], body)
                j -= 1
            else:
                k = j
                while k >= 0 and k not in vals:
                    k -= 1
                body = par(I(j - k), body)
                j = k
        return body
    g = f
    for w, b in reversed(items):
        g = ctrl(b, g)
    return on_wires(g, [w for w, _ in items] + list(targets), n)


def mcx(controls: Dict[int, bool] | Sequence[Tuple[int, bool]], target: int, n: int) -> Circuit:
    """Multiply controlled NOT (e.g. Toffoli: ``mcx({0: True, 1: True}, 2, 3)``)."""
    return controlled_on(X, controls, [target], n)
