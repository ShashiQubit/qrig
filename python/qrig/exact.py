"""Exact scalars in the cyclotomic field Q(omega), omega = exp(i pi / 4).

An element is ``a + b*omega + c*omega**2 + d*omega**3`` with rational coefficients.
This mirrors the Lean type ``Qrig.QOmega`` used by the verified core; the textual
token format ``a:b:c:d`` (each coefficient ``p`` or ``p/q``) is shared with it.
"""
from __future__ import annotations

import cmath
import math
from fractions import Fraction
from numbers import Number, Rational
from typing import Iterable, Tuple, Union

_SQRT2 = math.sqrt(2.0)
_OMEGA_C = cmath.exp(1j * math.pi / 4)

Scalar = Union["QOmega", int, Fraction]


def _frac(x) -> Fraction:
    if isinstance(x, Fraction):
        return x
    if isinstance(x, (int, Rational)):
        return Fraction(x)
    if isinstance(x, str):
        return Fraction(x)
    raise TypeError(f"cannot convert {x!r} to an exact rational")


class QOmega:
    """An exact element ``a + b w + c w^2 + d w^3`` of Q(w), ``w = e^{i pi/4}``."""

    __slots__ = ("a", "b", "c", "d")

    def __init__(self, a=0, b=0, c=0, d=0):
        self.a = _frac(a)
        self.b = _frac(b)
        self.c = _frac(c)
        self.d = _frac(d)

    # ----------------------------------------------------------------- conversion
    @staticmethod
    def coerce(x) -> "QOmega":
        if isinstance(x, QOmega):
            return x
        if isinstance(x, (int, Fraction, Rational)):
            return QOmega(x)
        if isinstance(x, complex) or isinstance(x, float):
            return QOmega.from_complex(complex(x))
        if isinstance(x, Number):
            return QOmega.from_complex(complex(x))
        raise TypeError(f"cannot convert {x!r} to QOmega")

    def coeffs(self) -> Tuple[Fraction, Fraction, Fraction, Fraction]:
        return (self.a, self.b, self.c, self.d)

    def __complex__(self) -> complex:
        return (float(self.a) + float(self.b) * _OMEGA_C + float(self.c) * 1j
                + float(self.d) * _OMEGA_C ** 3)

    def to_complex(self) -> complex:
        return complex(self)

    def token(self) -> str:
        return ":".join(_fmt(x) for x in self.coeffs())

    @staticmethod
    def from_token(tok: str) -> "QOmega":
        parts = tok.split(":")
        if len(parts) != 4:
            raise ValueError(f"bad scalar token {tok!r}")
        return QOmega(*(Fraction(p) for p in parts))

    @staticmethod
    def from_complex(z: complex, tol: float = 1e-9, max_log_den: int = 8) -> "QOmega":
        """Recognise a complex number of the form ``x + i y`` with
        ``x, y`` in ``Q + Q sqrt(2)`` (small dyadic denominators).

        Raises ``ValueError`` if no exact representation is found.
        """
        z = complex(z)
        rx = _recognise_real(z.real, tol, max_log_den)
        ry = _recognise_real(z.imag, tol, max_log_den)
        if rx is None or ry is None:
            raise ValueError(f"{z} is not recognisably an element of Q(exp(i pi/4))")
        (p, e), (q, f) = rx, ry
        # x = p + e sqrt2, y = q + f sqrt2 ; with w = (1+i)/sqrt2, w^3 = (-1+i)/sqrt2:
        # x + iy = p + q i + (e+f)... solve  b - d = 2e, b + d = 2f
        b = e + f
        d = f - e
        return QOmega(p, b, q, d)

    # ----------------------------------------------------------------- arithmetic
    def __add__(self, o):
        o = QOmega.coerce(o)
        return QOmega(self.a + o.a, self.b + o.b, self.c + o.c, self.d + o.d)

    __radd__ = __add__

    def __neg__(self):
        return QOmega(-self.a, -self.b, -self.c, -self.d)

    def __sub__(self, o):
        return self + (-QOmega.coerce(o))

    def __rsub__(self, o):
        return QOmega.coerce(o) - self

    def __mul__(self, o):
        o = QOmega.coerce(o)
        x, y = self, o
        return QOmega(
            x.a * y.a - x.b * y.d - x.c * y.c - x.d * y.b,
            x.a * y.b + x.b * y.a - x.c * y.d - x.d * y.c,
            x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d,
            x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a,
        )

    __rmul__ = __mul__

    def conj(self) -> "QOmega":
        return QOmega(self.a, -self.d, -self.c, -self.b)

    def norm2(self) -> "QOmega":
        """|z|^2 (an element of Q(sqrt 2))."""
        return self * self.conj()

    def inverse(self) -> "QOmega":
        """Multiplicative inverse (Q(w) is a field)."""
        if self.is_zero():
            raise ZeroDivisionError("QOmega division by zero")
        # z^{-1} = conj(z) * s^{-1}, s = z conj(z) = u + v sqrt2 with sqrt2 = w - w^3
        s = self * self.conj()
        u, v = s.a, (s.b - s.d) / 2  # s = u + v (w - w^3)
        den = u * u - 2 * v * v
        s_inv = QOmega(u / den, -v / den, 0, v / den)
        return self.conj() * s_inv

    def __truediv__(self, o):
        return self * QOmega.coerce(o).inverse()

    def __rtruediv__(self, o):
        return QOmega.coerce(o) * self.inverse()

    def __pow__(self, k: int):
        if k < 0:
            return self.inverse() ** (-k)
        r = QOmega(1)
        b = self
        while k:
            if k & 1:
                r = r * b
            b = b * b
            k >>= 1
        return r

    def is_zero(self) -> bool:
        return self.a == 0 and self.b == 0 and self.c == 0 and self.d == 0

    def __eq__(self, o):
        try:
            o = QOmega.coerce(o)
        except (TypeError, ValueError):
            return NotImplemented
        return self.coeffs() == o.coeffs()

    def __hash__(self):
        return hash(self.coeffs())

    def __repr__(self):
        terms = []
        for coef, sym in zip(self.coeffs(), ("", "w", "w^2", "w^3")):
            if coef != 0:
                terms.append(f"{coef}{('*' + sym) if sym else ''}")
        return "QOmega(" + (" + ".join(terms) if terms else "0") + ")"


def _fmt(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def _recognise_real(x: float, tol: float, max_log_den: int):
    """Find rationals (p, e) with small dyadic denominators such that x = p + e sqrt 2."""
    for k in range(max_log_den + 1):
        den = 2 ** k
        bound = int(abs(x) * den / _SQRT2) + 2 * den + 2
        for en in range(-bound, bound + 1):
            e = Fraction(en, den)
            rest = x - float(e) * _SQRT2
            pn = round(rest * den)
            if abs(rest * den - pn) < tol * den:
                return (Fraction(pn, den), e)
    return None


# Useful constants
ZERO = QOmega(0)
ONE = QOmega(1)
OMEGA = QOmega(0, 1, 0, 0)
I = QOmega(0, 0, 1, 0)
SQRT2 = QOmega(0, 1, 0, -1)
INV_SQRT2 = QOmega(0, Fraction(1, 2), 0, Fraction(-1, 2))


def omega_pow(k: int) -> QOmega:
    return OMEGA ** (k % 8)


def as_matrix(rows: Iterable[Iterable]) -> list:
    return [[QOmega.coerce(x) for x in row] for row in rows]
