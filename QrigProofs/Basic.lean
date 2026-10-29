module

public import Qrig.Core.Circ
public import Mathlib

/-!
# Basic facts about the semantics `den`

* `den_out`: outside of the meaningful range `[0, 2ⁿ)` every circuit acts as the identity.
* `den_local`: inside the range, the output only depends on the input inside the range
  (provided the base generators have this property).
-/

@[expose] public section

namespace Qrig

variable {G : Type} [GateSig G] {R : Type}

/-- A transformation of vectors on `k` wires is *local* if its meaningful outputs
depend only on the meaningful inputs. -/
def Local (k : Nat) (F : Vec R → Vec R) : Prop :=
  ∀ v v' : Vec R, (∀ j, j < 2 ^ k → v j = v' j) → ∀ i, i < 2 ^ k → F v i = F v' i

/-- The base generators are interpreted by local transformations. -/
def LocalAct (act : (g : G) → Vec R → Vec R) : Prop :=
  ∀ g, Local (GateSig.arity g) (act g)

lemma two_pow_succ' (n : Nat) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
  rw [Nat.pow_succ]; omega

lemma inHalf_true_iff (b : Bool) (n i : Nat) :
    inHalf b n i = true ↔ ctrlOff b n ≤ i ∧ i < ctrlOff b n + 2 ^ n := by
  cases b <;> simp [inHalf, ctrlOff, two_pow_succ']

lemma inHalf_lt {b : Bool} {n i : Nat} (h : inHalf b n i = true) : i < 2 ^ (n + 1) := by
  rw [inHalf_true_iff] at h
  have : ctrlOff b n ≤ 2 ^ n := by cases b <;> simp [ctrlOff]
  rw [two_pow_succ']; omega

lemma ctrlOff_add_lt {b : Bool} {n j : Nat} (h : j < 2 ^ n) :
    ctrlOff b n + j < 2 ^ (n + 1) := by
  have : ctrlOff b n ≤ 2 ^ n := by cases b <;> simp [ctrlOff]
  rw [two_pow_succ']; omega

lemma mul_pow_add_lt {m n a b : Nat} (ha : a < 2 ^ m) (hb : b < 2 ^ n) :
    a * 2 ^ n + b < 2 ^ (m + n) := by
  rw [Nat.pow_add]
  have : a * 2 ^ n + 2 ^ n ≤ 2 ^ m * 2 ^ n := by
    have := Nat.mul_le_mul_right (2 ^ n) (Nat.succ_le_of_lt ha)
    simpa [Nat.succ_mul] using this
  omega

lemma den_par_eq {act : (g : G) → Vec R → Vec R} {m n : Nat} (f : Circ G m) (g : Circ G n)
    (v : Vec R) (i : Nat) :
    den act (Circ.par f g) v i =
      if i < 2 ^ (m + n) then
        den act f (fun a => den act g (fun b => v (a * 2 ^ n + b)) (i % 2 ^ n)) (i / 2 ^ n)
      else v i := rfl

lemma den_ctrl_eq {act : (g : G) → Vec R → Vec R} {b : Bool} {n : Nat} (f : Circ G n)
    (v : Vec R) (i : Nat) :
    den act (Circ.ctrl b f) v i =
      if inHalf b n i then den act f (fun j => v (ctrlOff b n + j)) (i - ctrlOff b n)
      else v i := rfl

/-- Outside of the meaningful range, circuits act as the identity. -/
theorem den_out (act : (g : G) → Vec R → Vec R) :
    ∀ {n : Nat} (c : Circ G n) (v : Vec R) (i : Nat), 2 ^ n ≤ i → den act c v i = v i := by
  intro n c
  induction c with
  | id n => intro v i _; rfl
  | x => intro v i h; simp at h; simp [den]; omega
  | swap => intro v i h; simp at h; simp only [den]; rw [if_neg (by omega), if_neg (by omega)]
  | gen g => intro v i h; simp [den]; omega
  | seq f g ihf ihg => intro v i h; simp only [den]; rw [ihg _ _ h, ihf _ _ h]
  | par f g ihf ihg => intro v i h; simp only [den]; rw [if_neg (by omega)]
  | @ctrl n b f ihf =>
    intro v i h
    simp only [den]
    have : inHalf b n i = false := by
      cases hh : inHalf b _ i
      · rfl
      · have := inHalf_lt hh; omega
    rw [this]; rfl

/-- Meaningful outputs of a circuit depend only on meaningful inputs. -/
theorem den_local {act : (g : G) → Vec R → Vec R} (hact : LocalAct act) :
    ∀ {n : Nat} (c : Circ G n), Local n (den act c) := by
  intro n c
  induction c with
  | id n => intro v v' h i hi; exact h i hi
  | x =>
    intro v v' h i hi
    simp only [den]
    split_ifs <;> apply h <;> simp at hi ⊢ <;> omega
  | swap =>
    intro v v' h i hi
    simp only [den]
    split_ifs <;> apply h <;> first | (simp at hi ⊢; omega) | simp
  | gen g =>
    intro v v' h i hi
    simp only [den, if_pos hi]
    exact hact g v v' h i hi
  | seq f g ihf ihg =>
    intro v v' h i hi
    exact ihg _ _ (fun j hj => ihf v v' h j hj) i hi
  | @par m n f g ihf ihg =>
    intro v v' h i hi
    simp only [den, if_pos hi]
    apply ihf
    · intro a ha
      apply ihg
      · intro b hb
        exact h _ (mul_pow_add_lt ha hb)
      · exact Nat.mod_lt _ (by positivity)
    · rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact hi
  | @ctrl n b f ihf =>
    intro v v' h i hi
    simp only [den]
    split
    · next hh =>
      apply ihf
      · intro j hj; exact h _ (ctrlOff_add_lt hj)
      · rw [inHalf_true_iff] at hh; omega
    · exact h i hi

end Qrig

end
