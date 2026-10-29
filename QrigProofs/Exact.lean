module

public import QrigProofs.ArrayEval
public import Qrig.Core.Gate

/-!
# Correctness of exact simulation, unitaries and equivalence checking

For the concrete gate set (`Gate`, scalars in `ℚ(ω)`):

* `simulate_spec`: `simulate` computes the semantics `den Gate.act`;
* `unitary_spec`: entry `(i, j)` of `unitary c` is the amplitude of `|i⟩` in the image
  of the basis vector `|j⟩`;
* `equivExact_iff`: `equivExact c₁ c₂` holds iff the two circuits have the same matrix.
-/

@[expose] public section

namespace Qrig

/-- The base generators act locally. -/
theorem gate_local : LocalAct Gate.act := by
  intro g v v' h i hi
  cases g with
  | u m00 m01 m10 m11 =>
    have h0 := h 0 (by simp [GateSig.arity])
    have h1 := h 1 (by simp [GateSig.arity])
    simp only [Gate.act, h0, h1]
    split_ifs <;> first | rfl | (exfalso; simp [GateSig.arity] at hi; omega)
  | ph z =>
    have h0 := h 0 (by simp [GateSig.arity])
    simp only [Gate.act, h0]
    split_ifs <;> first | rfl | (exfalso; simp [GateSig.arity] at hi; omega)

/-- `simulate` computes the semantics of the circuit on the given state. -/
theorem simulate_spec {n : Nat} (c : QCirc n) (psi : Array QOmega) (h : psi.size = 2 ^ n) :
    simulate c psi = tab (2 ^ n) (den Gate.act c (aget psi)) :=
  denA_eq_tab_den gate_local c psi h

/-- The computational basis vector `|j⟩`. -/
def basis (j : Nat) : Vec QOmega := fun k => if k = j then 1 else 0

/-- Entry `(i, j)` of `unitary c` is `⟨i| A(c) |j⟩`. -/
theorem unitary_spec {n : Nat} (c : QCirc n) {i j : Nat} (hi : i < 2 ^ n) (hj : j < 2 ^ n) :
    aget (aget (unitary c) i) j = den Gate.act c (basis j) i := by
  simp only [unitary]
  rw [aget_tab _ hi, aget_tab _ hj, aget_tab _ hj,
    simulate_spec _ _ (by simp [basisVec]), aget_tab _ hi]
  apply den_local gate_local c _ _ _ _ hi
  intro k hk
  simp [basisVec, aget_tab _ hk, basis]

theorem size_unitary {n : Nat} (c : QCirc n) : (unitary c).size = 2 ^ n := by
  simp [unitary]

theorem size_unitary_row {n : Nat} (c : QCirc n) {i : Nat} (hi : i < 2 ^ n) :
    (aget (unitary c) i).size = 2 ^ n := by
  simp [unitary, aget_tab _ hi]

/-- The exact equivalence check is correct and complete: it succeeds iff the two
circuits have the same matrix. -/
theorem equivExact_iff {n : Nat} (c₁ c₂ : QCirc n) :
    equivExact c₁ c₂ = true ↔
      ∀ i j, i < 2 ^ n → j < 2 ^ n → den Gate.act c₁ (basis j) i = den Gate.act c₂ (basis j) i := by
  simp only [equivExact, beq_iff_eq]
  constructor
  · intro h i j hi hj
    rw [← unitary_spec c₁ hi hj, ← unitary_spec c₂ hi hj, h]
  · intro h
    simp only [unitary]
    apply tab_ext
    intro i hi
    apply tab_ext
    intro j hj
    have := h i j hi hj
    rw [← unitary_spec c₁ hi hj, ← unitary_spec c₂ hi hj] at this
    simpa [unitary, aget_tab _ hi, aget_tab _ hj] using this

end Qrig

end
