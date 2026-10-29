"""Smoke tests for the noisy-simulation benchmark (benchmarks/noise_benchmark.py).

Skipped unless qiskit-aer is installed."""
import argparse
import os
import sys

import pytest

pytest.importorskip("qiskit")
pytest.importorskip("qiskit_aer")

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                                "benchmarks"))

import numpy as np  # noqa: E402
import noise_benchmark as nb  # noqa: E402

ARGS = argparse.Namespace(dm_max=12, shots=50, inputs=2, seeds=[0])


def _case(name):
    return dict(nb.synthetic_cases())[name]


def test_repeated_c3t_less_noise_with_qrig():
    row = nb.run_case("C3(T) x4", _case("C3(T) x4"), [nb.Model("depolarizing")], ARGS,
                      np.random.default_rng(0))
    m = row["models"]["depolarizing"]
    assert m["qrig"]["cx"] < m["qiskit"]["cx"]
    assert m["qrig"]["F"] > m["qiskit"]["F"]
    assert m["qrig"]["ESP"] > m["qiskit"]["ESP"]
    assert 0 < m["F"]["infidelity_reduction"] <= 1


def test_noiseless_limit_gives_fidelity_one():
    row = nb.run_case("multiplexer (3 controls)", _case("multiplexer (3 controls)"),
                      [nb.Model("depolarizing", p2=0.0)], ARGS, np.random.default_rng(1))
    m = row["models"]["depolarizing"]
    for v in ("qiskit", "qrig"):
        assert m[v]["F"] == pytest.approx(1.0, abs=1e-9)
        assert m[v]["P"] == pytest.approx(1.0, abs=1e-9)


def test_trajectories_agree_with_density_matrix():
    qc = _case("C3(T) x4")
    model = nb.Model("depolarizing", p2=0.02)
    _, c = nb.compile_best(qc, model, [0])
    rng = np.random.default_rng(2)
    psi0 = c.product_state([nb.random_qubit_state(rng) for _ in range(qc.num_qubits)])
    ideal = nb.run_ideal(c, psi0)
    noise = model.noise_model(c)
    f_dm, _, _ = nb.run_noisy(c, psi0, noise, ideal, 12, 0, 1)
    f_tr, se, _ = nb.run_noisy(c, psi0, noise, ideal, 0, 2000, 1)
    assert abs(f_dm - f_tr) < 5 * se + 1e-3
