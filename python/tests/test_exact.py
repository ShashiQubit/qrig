import cmath
import math
import random
from fractions import Fraction

import pytest

from qrig.exact import INV_SQRT2, OMEGA, ONE, QOmega, SQRT2, I


def rand_q(rng):
    return QOmega(*(Fraction(rng.randint(-9, 9), rng.choice([1, 2, 3, 4, 8])) for _ in range(4)))


def test_constants():
    assert OMEGA ** 8 == ONE
    assert OMEGA ** 4 == -ONE
    assert OMEGA ** 2 == I
    assert SQRT2 * SQRT2 == QOmega(2)
    assert SQRT2 * INV_SQRT2 == ONE
    assert abs(complex(OMEGA) - cmath.exp(1j * math.pi / 4)) < 1e-12


def test_field_axioms_numerically():
    rng = random.Random(1)
    for _ in range(300):
        x, y, z = rand_q(rng), rand_q(rng), rand_q(rng)
        assert abs(complex(x * y) - complex(x) * complex(y)) < 1e-9
        assert abs(complex(x + y) - (complex(x) + complex(y))) < 1e-9
        assert (x * y) * z == x * (y * z)
        assert x * (y + z) == x * y + x * z
        assert abs(complex(x.conj()) - complex(x).conjugate()) < 1e-9
        if not x.is_zero():
            assert x * x.inverse() == ONE


def test_token_roundtrip():
    rng = random.Random(2)
    for _ in range(100):
        x = rand_q(rng)
        assert QOmega.from_token(x.token()) == x


@pytest.mark.parametrize("z", [0, 1, -1, 1j, -1j, 1 / math.sqrt(2), (1 + 1j) / 2, (1 - 1j) / 2,
                               cmath.exp(1j * math.pi / 4), cmath.exp(-3j * math.pi / 4),
                               0.5 + math.sqrt(2) / 4 * 1j, 3 / 8 - 1j / math.sqrt(2)])
def test_from_complex(z):
    q = QOmega.from_complex(z)
    assert abs(complex(q) - z) < 1e-12


def test_from_complex_rejects():
    with pytest.raises(ValueError):
        QOmega.from_complex(cmath.exp(0.1j))
