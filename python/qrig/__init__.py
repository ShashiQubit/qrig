"""qrig -- verified controlled circuits ("One rig to control them all").

The computational core of this package is written and proved correct in Lean 4 and
compiled to C by the Lean compiler; this Python layer only builds circuit terms and
converts data.  Quick start::

    import qrig
    from qrig import X, H, T, C0, C1, I

    toffoli = C1(C1(X))
    qrig.unitary(toffoli)                         # exact 8x8 permutation matrix
    qrig.equivalent(C1(X) >> C0(X), I(1) + X)     # equation (e): True
    qc = toffoli.to_qiskit()                      # a Qiskit QuantumCircuit
    qrig.synthesize_permutation([0, 1, 3, 2])     # CNOT, via Gray codes
"""
from ._native import QrigError, backend
from .circuit import (C0, C1, GLOBAL_OMEGA, H, I, S, SWAP, SX, SXdg, T, V, Vdg, X, XGATE, Y, Z,
                      Circuit, Sdg, Tdg, adjacent_swap, controlled_on, ctrl, gate, mcx,
                      on_wires, par, phase, seq)
from .core import (check, dagger, equivalent, gray_code, permutation, simplify, simulate,
                   synthesize_permutation, unitary, version)
from .exact import I as IMAG, INV_SQRT2, OMEGA, SQRT2, QOmega, omega_pow
from . import paper

__version__ = "1.1.0"


def to_qiskit(c):
    from .qiskit_bridge import to_qiskit as _t
    return _t(c)


def from_qiskit(qc):
    from .qiskit_bridge import from_qiskit as _f
    return _f(qc)


__all__ = [
    "Circuit", "I", "X", "SWAP", "H", "S", "Sdg", "T", "Tdg", "Z", "Y", "V", "Vdg", "SX",
    "SXdg", "XGATE", "GLOBAL_OMEGA", "C0", "C1", "ctrl", "gate", "phase", "seq", "par",
    "on_wires", "controlled_on", "mcx", "adjacent_swap", "unitary", "simulate",
    "permutation", "synthesize_permutation", "simplify", "dagger", "equivalent",
    "gray_code", "check", "version", "QOmega", "OMEGA", "IMAG", "SQRT2", "INV_SQRT2",
    "omega_pow", "to_qiskit", "from_qiskit", "QrigError", "backend", "paper",
]
