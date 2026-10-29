"""Semantic operations, all computed by the verified Lean core (compiled to C)."""
from __future__ import annotations

from typing import List, Sequence

from ._native import QrigError, call
from .circuit import Circuit
from .exact import QOmega


def _circ(c) -> str:
    if isinstance(c, Circuit):
        return c.serialize()
    if isinstance(c, str):
        return c
    try:  # Qiskit QuantumCircuit
        from .qiskit_bridge import from_qiskit
        return from_qiskit(c).serialize()
    except ImportError:  # pragma: no cover
        pass
    raise TypeError(f"expected a qrig.Circuit, got {type(c).__name__}")


def _to_circuit(c) -> Circuit:
    if isinstance(c, Circuit):
        return c
    return Circuit.parse(_circ(c))


def version() -> str:
    return call("version")


def check(c) -> dict:
    """Type-check a circuit in the core; returns wires, gate count and classicality."""
    n, size, cl = call("check", _circ(c)).split()
    return {"wires": int(n), "gates": int(size), "classical": cl == "1"}


def unitary(c, exact: bool = True):
    """The unitary (in fact, the matrix semantics ``A(c)``) of a circuit.

    With ``exact=True`` a list of rows of :class:`QOmega` is returned, otherwise a
    ``numpy`` complex array.  Row/column index = basis state with wire 0 as the most
    significant bit (= Qiskit's little-endian convention after :func:`to_qiskit`).
    """
    text = call("unitary", _circ(c))
    rows = [[QOmega.from_token(t) for t in line.split()] for line in text.split("\n")]
    if exact:
        return rows
    import numpy as np
    return np.array([[complex(z) for z in r] for r in rows], dtype=complex)


def simulate(c, state: Sequence, exact: bool = True):
    """Apply a circuit to a state vector of length ``2**n`` (exactly)."""
    vec = " ".join(QOmega.coerce(z).token() for z in state)
    out = [QOmega.from_token(t) for t in call("simulate", _circ(c) + " | " + vec).split()]
    if exact:
        return out
    import numpy as np
    return np.array([complex(z) for z in out], dtype=complex)


def permutation(c) -> List[int]:
    """The permutation of basis states implemented by a classical (reversible
    Boolean) circuit: basis state ``i`` is mapped to ``result[i]``."""
    return [int(t) for t in call("perm", _circ(c)).split()]


def synthesize_permutation(perm: Sequence[int], n: int | None = None) -> Circuit:
    """Synthesise a reversible circuit of multiply controlled NOT gates implementing
    the permutation ``perm`` of the ``2**n`` basis states (the functor beta of
    Theorem 9, via Gray-code transpositions).  The result is checked by the core."""
    perm = [int(p) for p in perm]
    if n is None:
        n = max(len(perm) - 1, 0).bit_length()
    if len(perm) != 2 ** n:
        raise QrigError(f"a permutation of 2^n basis states is needed (got {len(perm)})")
    return Circuit.parse(call("synth", " ".join(map(str, [n] + perm))))


def simplify(c) -> Circuit:
    """Optimise a circuit using the control equations (proved sound in Lean)."""
    return Circuit.parse(call("simplify", _circ(c)))


def dagger(c) -> Circuit:
    """The adjoint (inverse, for unitary circuits) of a circuit."""
    return Circuit.parse(call("dagger", _circ(c)))


def equivalent(c1, c2, up_to_phase: bool = False) -> bool:
    """Exact equality of the semantics of two circuits (optionally up to a global
    scalar)."""
    cmd = "equivphase" if up_to_phase else "equiv"
    return call(cmd, _circ(c1) + " | " + _circ(c2)) == "1"


def gray_code(n: int) -> List[int]:
    """The reflected Gray code r_n(0), ..., r_n(2^n - 1) of Section 2.3."""
    return [int(t) for t in call("gray", str(n)).split()]
