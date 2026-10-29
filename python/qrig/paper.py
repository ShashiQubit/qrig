"""Constructions and identities from "One rig to control them all".

* :func:`control_equations` instantiates the eight equations (a)-(h) of Definition 6
  (Figure 1) for given circuits; each instance is a pair of circuits whose semantics
  agree (this is proved once and for all in Lean, ``QrigProofs.ControlEquations``).
* :func:`sleator_weinfurter` builds the right-hand side of Figure 3.
* :func:`gray_transposition` builds beta(theta_{n,i}) of Section 3.1.
* :func:`commuting_cnots` gives the two sides of equation (11).
"""
from __future__ import annotations

from typing import Dict, Tuple

from .circuit import C0, C1, SWAP, X, Circuit, I, controlled_on, mcx, par, seq
from .core import gray_code


def control_equations(f: Circuit, g: Circuit | None = None, f2: Circuit | None = None,
                      m: int = 1) -> Dict[str, Tuple[Circuit, Circuit]]:
    """The control equations (a)-(h) instantiated at ``f`` (and ``g``, ``f2``).

    ``g`` and ``f2`` must act on as many wires as ``f``; ``m`` is the number of idle
    wires used in the strength equation (c).
    """
    n = f.n
    g = g if g is not None else f
    f2 = f2 if f2 is not None else g
    xi = par(X, I(n)) if n else X
    eqs = {
        "a_composition": (C1(f >> g), C1(f) >> C1(g)),
        "b_identity": (C1(I(n)), I(n + 1)),
        "c_strength": (C1(par(f, I(m))), par(C1(f), I(m))),
        "d_colour_change": (xi >> C0(f) >> xi, C1(f)),
        "e_complementarity": (C1(f) >> C0(f), par(I(1), f)),
        "f_commutativity": (C1(f2) >> C0(f), C0(f) >> C1(f2)),
        "g_swap": (C1(X) >> SWAP >> C1(X) >> SWAP >> C1(X), SWAP),
        "h_swap_coherence": (C1(C1(f)) >> par(SWAP, I(n)), par(SWAP, I(n)) >> C1(C1(f))),
    }
    return eqs


def sleator_weinfurter(f: Circuit, f_dagger: Circuit | None = None) -> Circuit:
    """Figure 3: a doubly controlled ``f^2`` from singly controlled ``f``, ``f^dagger``
    and CNOTs (wires: control 0, control 1, then the ``f.n`` target wires)."""
    if f_dagger is None:
        f_dagger = f.dagger()
    n = f.n + 2
    tgt = list(range(2, n))
    return seq(
        controlled_on(f, {1: True}, tgt, n),
        mcx({0: True}, 1, n),
        controlled_on(f_dagger, {1: True}, tgt, n),
        mcx({0: True}, 1, n),
        controlled_on(f, {0: True}, tgt, n),
    )


def doubly_controlled(f: Circuit) -> Circuit:
    """``C1(C1(f))`` (left-hand side of the Sleator-Weinfurter identity for ``f^2``)."""
    return C1(C1(f))


def gray_transposition(n: int, i: int) -> Circuit:
    """beta(theta_{n,i}): the multiply controlled NOT swapping the ``i``-th and
    ``(i+1)``-th words of the Gray code on ``n`` bits."""
    code = gray_code(n)
    a, b = code[i], code[i + 1]
    diff = a ^ b
    bit = diff.bit_length() - 1
    target = n - 1 - bit
    controls = {w: bool((a >> (n - 1 - w)) & 1) for w in range(n) if w != target}
    return mcx(controls, target, n)


def commuting_cnots() -> Tuple[Circuit, Circuit]:
    """Equation (11): two CNOTs with the same control but different targets commute."""
    a = mcx({0: True}, 1, 3)
    b = mcx({0: True}, 2, 3)
    return a >> b, b >> a
