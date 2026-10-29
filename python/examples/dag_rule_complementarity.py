#!/usr/bin/env python3
"""Equation (e) (complementarity) as a Qiskit DAG node-replacement rule.

Part 1 is a hand-written rule that works directly on the ``DAGCircuit``: it finds two
DAG-adjacent controlled gates ``C0_w(f)`` and ``C1_w(f)`` with the same other controls and
replaces them by ``f`` without the control ``w`` (``C0(f) ; C1(f) = id + f``).  It shows how
such a rule plugs into the DAG loop (``op_successors`` / ``substitute_node_with_dag`` /
``remove_op_node``).  It is *not* verified, and it only sees pairs that are adjacent in
the DAG.

Part 2 runs the same circuits through ``qrig.dag.QrigControlEquations``, where equation (e)
is one rule of the Lean-verified core: it also finds pairs separated by gates that
commute with them (equation (f), diagonal gates), counts the rewrites, and every rewrite
is covered by the Lean theorem ``peephole_sound``.  Both results are checked with Qiskit's
``Operator`` and, if installed, MQT QCEC.
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import numpy as np
from qiskit import QuantumCircuit
from qiskit.circuit import ControlledGate
from qiskit.circuit.library import HGate, RYGate
from qiskit.converters import circuit_to_dag, dag_to_circuit
from qiskit.dagcircuit import DAGCircuit
from qiskit.quantum_info import Operator
from qiskit.transpiler import PassManager

from qrig.dag import QrigControlEquations


# ----------------------------------------------------------------------------- part 1
def _controls(node):
    """{qubit: colour} of a controlled node, and its target qubit."""
    op = node.op
    k = op.num_ctrl_qubits
    ctrls = {node.qargs[j]: (op.ctrl_state >> j) & 1 for j in range(k)}
    return ctrls, node.qargs[k]


def complementarity_rule(dag: DAGCircuit) -> int:
    """Apply equation (e) to DAG-adjacent pairs; returns the number of rewrites."""
    rewrites = 0
    changed = True
    while changed:
        changed = False
        for a in dag.op_nodes():
            op = a.op
            if not isinstance(op, ControlledGate) or op.num_qubits != op.num_ctrl_qubits + 1:
                continue
            succ = list(dag.op_successors(a))
            if len(succ) != 1:
                continue
            b = succ[0]
            if (not isinstance(b.op, ControlledGate) or set(b.qargs) != set(a.qargs)
                    or b.op.base_gate != op.base_gate
                    or b.op.num_ctrl_qubits != op.num_ctrl_qubits):
                continue
            ca, ta = _controls(a)
            cb, tb = _controls(b)
            if ta != tb:
                continue
            diff = [q for q in ca if ca[q] != cb[q]]
            if len(diff) != 1:
                continue
            w = diff[0]
            rest = [q for q in ca if q != w]
            state = sum(ca[q] << j for j, q in enumerate(rest))
            new = (op.base_gate.control(len(rest), ctrl_state=state, annotated=False)
                   if rest else op.base_gate)
            mini = DAGCircuit()
            mini.add_qubits(list(a.qargs))
            mini.apply_operation_back(new, tuple(rest) + (ta,), ())
            dag.substitute_node_with_dag(a, mini, wires=list(a.qargs))
            dag.remove_op_node(b)
            rewrites += 1
            changed = True
            break
    return rewrites


# ----------------------------------------------------------------------------- demo
def multiplexer(k: int, gate) -> QuantumCircuit:
    """All 2^k control patterns of the same gate: collapses to the bare gate by (e)."""
    qc = QuantumCircuit(k + 1)
    for st in range(2 ** k):
        qc.append(gate.control(k, ctrl_state=st, annotated=False), list(range(k + 1)))
    return qc


def separated_pair() -> QuantumCircuit:
    """C0(H) and C1(H) (control on q1) separated by gates they commute with (a CZ on the
    other control, a T on the complementary control): not adjacent in the DAG, but
    equation (f) and diagonality let the verified core bring them together."""
    qc = QuantumCircuit(4)
    qc.append(HGate().control(2, ctrl_state=0b01, annotated=False), [0, 1, 2])
    qc.cz(0, 3)
    qc.t(1)
    qc.append(HGate().control(2, ctrl_state=0b11, annotated=False), [0, 1, 2])
    return qc


def check(ref, out):
    same = np.allclose(Operator(ref).data, Operator(out).data)
    try:
        from mqt import qcec
        q = str(qcec.verify(ref, out).equivalence).split(".")[-1]
    except ImportError:
        q = "(mqt.qcec not installed)"
    return same, q


def main():
    for name, qc in [("multiplexer k=3, RY(0.7)", multiplexer(3, RYGate(0.7))),
                     ("separated C0(H) / C1(H)", separated_pair())]:
        print(f"== {name}: {qc.size()} gates")
        dag = circuit_to_dag(qc)
        n = complementarity_rule(dag)
        hand = dag_to_circuit(dag)
        exact, q = check(qc, hand)
        print(f"   hand-written DAG rule : {n} rewrites -> {hand.size()} gates, "
              f"exact={exact}, QCEC={q}")
        pm = PassManager([QrigControlEquations()])
        out = pm.run(qc)
        st = pm.property_set["qrig_stats"]
        exact, q = check(qc, out)
        print(f"   qrig (Lean-verified)  : compl={st.rules['compl']} -> {out.size()} gates, "
              f"exact={exact}, QCEC={q}")


if __name__ == "__main__":
    main()
