"""API behaviour, error handling, serialisation and backends."""
import os
import subprocess
import sys

import pytest

import qrig
from qrig import C0, C1, H, I, SWAP, T, X, Circuit
from conftest import random_pair


def test_version_and_check():
    assert qrig.version().startswith("qrig")
    info = qrig.check(C1(C1(X)))
    assert info == {"wires": 3, "gates": 1, "classical": True}
    assert qrig.check(H)["classical"] is False


def test_type_errors_are_caught_in_python():
    with pytest.raises(ValueError):
        C1(X) >> X
    with pytest.raises(ValueError):
        qrig.gate([[1, 2, 3]])
    with pytest.raises(ValueError):
        qrig.on_wires(SWAP, [0, 0], 3)


def test_type_errors_are_caught_in_the_core():
    from qrig._native import call
    with pytest.raises(qrig.QrigError):
        call("unitary", "S X W")  # 1 vs 2 wires
    with pytest.raises(qrig.QrigError):
        call("unitary", "S X")    # truncated
    with pytest.raises(qrig.QrigError):
        call("unitary", "Q")      # unknown token
    with pytest.raises(qrig.QrigError):
        call("simulate", "X | 1:0:0:0")  # wrong vector length
    with pytest.raises(qrig.QrigError):
        call("nonsense", "")
    with pytest.raises(qrig.QrigError):
        call("unitary", "I 40")  # too many wires


def test_serialisation_roundtrip(rng):
    for n in (1, 2, 3, 4):
        for _ in range(20):
            c, _ = random_pair(rng, n, 15)
            assert Circuit.parse(c.serialize()) == c
            assert qrig.equivalent(Circuit.parse(c.serialize()), c)


def test_long_circuits():
    c = qrig.seq(*([T] * 5000))
    assert qrig.simplify(c) == I(1)   # 5000 = 625 * 8
    assert qrig.equivalent(c, I(1))


def test_exact_unitary_entries():
    u = qrig.unitary(H)
    assert u[0][0] == qrig.INV_SQRT2 and u[1][1] == -qrig.INV_SQRT2
    u = qrig.unitary(T)
    assert u[1][1] == qrig.OMEGA


def test_repr_and_str():
    s = str(C1(H) >> (X + T))
    assert "C1(H)" in s and "X + T" in s
    assert "wires" in repr(C1(H))


@pytest.mark.parametrize("backend", ["process", "inproc"])
def test_backends_agree(backend):
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    bin_dir = os.path.join(here, "qrig", "_bin")
    shared_exists = any(os.path.exists(os.path.join(bin_dir, f)) for f in ["libqrig.so", "libqrig.dylib", "libqrig.dll", "qrig.dll"])
    if backend == "inproc" and not shared_exists:
        pytest.skip("in-process library not built")
    code = ("import qrig; from qrig import *; "
            "print(qrig.backend().name, qrig.permutation(C1(C1(X))), "
            "qrig.equivalent(C1(X) >> C0(X), I(1) + X), qrig.simplify(H >> H))")
    out = subprocess.check_output([sys.executable, "-c", code], cwd=here,
                                  env=dict(os.environ, QRIG_BACKEND=backend), text=True)
    assert out.split()[0] == backend
    assert "[0, 1, 2, 3, 4, 5, 7, 6] True I1" in out
