module

public import QrigProofs.Basic

/-!
# Correctness of the array-based evaluator

`denA` (the evaluator that is compiled to C and used by `simulate` / `unitary`) computes
exactly the denotational semantics `den`:

`denA_eq_tab_den : a.size = 2ⁿ → denA act c a = tab (2ⁿ) (den act c (aget a))`.
-/

@[expose] public section

namespace Qrig

variable {G : Type} [GateSig G] {R : Type} [Inhabited R]

omit [Inhabited R] in
@[simp] lemma size_tab (N : Nat) (v : Vec R) : (tab N v).size = N := by simp [tab]

lemma aget_tab {N : Nat} (v : Vec R) {i : Nat} (h : i < N) : aget (tab N v) i = v i := by
  simp [aget, tab, h]

omit [Inhabited R] in
lemma tab_ext {N : Nat} {v w : Vec R} (h : ∀ i, i < N → v i = w i) : tab N v = tab N w := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [tab, Array.getElem_ofFn]
    exact h i (by simpa using h1)

lemma tab_aget (a : Array R) {N : Nat} (h : a.size = N) : tab N (aget a) = a := by
  subst h
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [tab, aget]

/-- The array evaluator agrees with the denotational semantics. -/
theorem denA_eq_tab_den {act : (g : G) → Vec R → Vec R} (hact : LocalAct act) :
    ∀ {n : Nat} (c : Circ G n) (a : Array R), a.size = 2 ^ n →
      denA act c a = tab (2 ^ n) (den act c (aget a)) := by
  intro n c
  induction c with
  | id n => intro a ha; simp only [denA, den]; exact (tab_aget a ha).symm
  | x => intro a _; rfl
  | swap => intro a _; rfl
  | gen g =>
    intro a _
    simp only [denA]
    apply tab_ext
    intro i hi
    simp [den, hi]
  | seq f g ihf ihg =>
    intro a ha
    simp only [denA]
    rw [ihf a ha, ihg _ (size_tab _ _)]
    apply tab_ext
    intro i hi
    apply den_local hact g _ _ _ i hi
    intro j hj
    exact aget_tab _ hj
  | @par m n f g ihf ihg =>
    intro a _
    simp only [denA]
    apply tab_ext
    intro i hi
    have hr : i % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
    have hq : i / 2 ^ n < 2 ^ m := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact hi
    simp only [den, if_pos hi]
    rw [aget_tab _ hr, ihf _ (size_tab _ _), aget_tab _ hq]
    apply den_local hact f _ _ _ _ hq
    intro p hp
    rw [aget_tab _ hp, aget_tab _ hp, ihg _ (size_tab _ _), aget_tab _ hr]
    apply den_local hact g _ _ _ _ hr
    intro b hb
    exact aget_tab _ hb
  | @ctrl n b f ihf =>
    intro a _
    simp only [denA]
    apply tab_ext
    intro i _
    simp only [den]
    split
    · next hh =>
      have hlt : i - ctrlOff b n < 2 ^ n := by rw [inHalf_true_iff] at hh; omega
      rw [ihf _ (size_tab _ _), aget_tab _ hlt]
      apply den_local hact f _ _ _ _ hlt
      intro j hj
      exact aget_tab _ hj
    · rfl

end Qrig

end
