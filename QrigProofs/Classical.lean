module

public import QrigProofs.Basic
public import Qrig.Core.Classical

/-!
# Reversible Boolean circuits: classical semantics and synthesis

* `den_perm`: for a gate-free circuit `c`, the linear semantics is the permutation
  matrix of `perm c`: `den act c v (perm c i) = v i` (for every interpretation `act`).
* `perm_lt`, `perm_injOn`: `perm c` is a permutation of the basis states `[0, 2ⁿ)`.
* `synthPerm_sound`: every circuit returned by the synthesis `synthPerm n p` is a
  reversible Boolean circuit implementing exactly the permutation `p`.
-/

@[expose] public section

namespace Qrig

variable {G : Type} [GateSig G] {R : Type}

theorem perm_out : ∀ {n : Nat} (c : Circ G n) (i : Nat), 2 ^ n ≤ i → perm c i = i := by
  intro n c
  induction c with
  | id n => intro i _; rfl
  | x => intro i h; simp at h; simp [perm]; omega
  | swap => intro i h; simp at h; simp only [perm]; rw [if_neg (by omega), if_neg (by omega)]
  | gen g => intro i _; rfl
  | seq f g ihf ihg => intro i h; simp only [perm]; rw [ihf _ h, ihg _ h]
  | par f g ihf ihg => intro i h; simp only [perm]; rw [if_neg (by omega)]
  | @ctrl n b f ihf =>
    intro i h
    simp only [perm]
    have : inHalf b n i = false := by
      cases hh : inHalf b n i
      · rfl
      · have := inHalf_lt hh; omega
    rw [this]; rfl

theorem perm_lt : ∀ {n : Nat} (c : Circ G n) (i : Nat), i < 2 ^ n → perm c i < 2 ^ n := by
  intro n c
  induction c with
  | id n => intro i h; exact h
  | x => intro i h; simp at h ⊢; simp only [perm]; split_ifs; omega
  | swap => intro i h; simp at h ⊢; simp only [perm]; split_ifs <;> omega
  | gen g => intro i h; exact h
  | seq f g ihf ihg => intro i h; exact ihg _ (ihf _ h)
  | @par m n f g ihf ihg =>
    intro i h
    simp only [perm, if_pos h]
    apply mul_pow_add_lt
    · apply ihf; rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact h
    · exact ihg _ (Nat.mod_lt _ (by positivity))
  | @ctrl n b f ihf =>
    intro i h
    simp only [perm]
    split
    · next hh =>
      apply ctrlOff_add_lt
      apply ihf
      rw [inHalf_true_iff] at hh; omega
    · exact h

/-- A gate-free circuit denotes the permutation matrix of `perm c`. -/
theorem den_perm (act : (g : G) → Vec R → Vec R) :
    ∀ {n : Nat} (c : Circ G n), isClassical c = true →
      ∀ (v : Vec R) (i : Nat), den act c v (perm c i) = v i := by
  intro n c
  induction c with
  | id n => intro _ v i; rfl
  | x =>
    intro _ v i
    simp only [den, perm]
    by_cases h : i < 2
    · rw [if_pos h, if_pos (by omega)]; congr 1; omega
    · rw [if_neg h, if_neg h]
  | swap =>
    intro _ v i
    simp only [den, perm]
    by_cases h1 : i = 1
    · subst h1; simp
    · by_cases h2 : i = 2
      · subst h2; simp
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
  | gen g => intro h; simp [isClassical] at h
  | seq f g ihf ihg =>
    intro h v i
    simp only [isClassical, Bool.and_eq_true] at h
    simp only [den, perm]
    rw [ihg h.2, ihf h.1]
  | @par m n f g ihf ihg =>
    intro h v i
    simp only [isClassical, Bool.and_eq_true] at h
    have hN : 0 < 2 ^ n := by positivity
    by_cases hi : i < 2 ^ (m + n)
    · have hq : i / 2 ^ n < 2 ^ m := by
        rw [Nat.div_lt_iff_lt_mul hN, ← Nat.pow_add]; exact hi
      have hr : i % 2 ^ n < 2 ^ n := Nat.mod_lt _ hN
      have hpf := perm_lt f _ hq
      have hpg := perm_lt g _ hr
      simp only [perm, if_pos hi]
      rw [den_par_eq, if_pos (mul_pow_add_lt hpf hpg)]
      have e1 : (perm f (i / 2 ^ n) * 2 ^ n + perm g (i % 2 ^ n)) / 2 ^ n = perm f (i / 2 ^ n) := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hpg, Nat.zero_add]
      have e2 : (perm f (i / 2 ^ n) * 2 ^ n + perm g (i % 2 ^ n)) % 2 ^ n = perm g (i % 2 ^ n) := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpg]
      rw [e1, e2, ihf h.1, ihg h.2]
      congr 1
      exact Nat.div_add_mod' i (2 ^ n)
    · simp only [perm, if_neg hi]
      rw [den_par_eq, if_neg hi]
  | @ctrl n b f ihf =>
    intro h v i
    simp only [isClassical] at h
    by_cases hh : inHalf b n i = true
    · have hlt : i - ctrlOff b n < 2 ^ n := by rw [inHalf_true_iff] at hh; omega
      have hp := perm_lt f _ hlt
      have hh' : inHalf b n (ctrlOff b n + perm f (i - ctrlOff b n)) = true := by
        rw [inHalf_true_iff]; omega
      simp only [perm, hh, if_true]
      rw [den_ctrl_eq, if_pos hh', Nat.add_sub_cancel_left, ihf h]
      congr 1
      rw [inHalf_true_iff] at hh; omega
    · have hh' : inHalf b n i = false := by simpa using hh
      simp only [perm, hh', Bool.false_eq_true, if_false]
      rw [den_ctrl_eq, hh']
      simp

/-- `perm c` is injective on the basis states (for gate-free circuits). -/
theorem perm_injOn {n : Nat} (c : Circ G n) (hc : isClassical c = true) {i j : Nat}
    (h : perm c i = perm c j) : i = j := by
  have hi := den_perm (G := G) (R := Nat) (fun _ v => v) c hc id i
  have hj := den_perm (G := G) (R := Nat) (fun _ v => v) c hc id j
  rw [h] at hi
  simpa [hi] using hj

/-! ## Synthesis -/

theorem isClassical_castC {m n : Nat} (h : m = n) (c : Circ G m) :
    isClassical (castC h c) = isClassical c := by
  subst h; rfl

theorem isClassical_ctrlBelowX : ∀ w : List Bool, isClassical (ctrlBelowX (G := G) w) = true
  | [] => rfl
  | b :: w => by
    simp [ctrlBelowX, isClassical_castC, isClassical, isClassical_ctrlBelowX w]

theorem isClassical_mcx : ∀ (above below : List Bool),
    isClassical (mcx (G := G) above below) = true
  | [], below => isClassical_ctrlBelowX below
  | b :: above, below => by simp [mcx, isClassical, isClassical_mcx above below]

theorem isClassical_theta (n i : Nat) : isClassical (theta (G := G) n i) = true := by
  simp only [theta, mcxOn]
  split
  · rw [isClassical_castC]; exact isClassical_mcx _ _
  · rfl

theorem isClassical_seqList {n : Nat} :
    ∀ l : List (Circ G n), (∀ c ∈ l, isClassical c = true) → isClassical (seqList l) = true
  | [], _ => rfl
  | [c], h => h c (by simp)
  | c :: d :: cs, h => by
    simp only [seqList, isClassical, Bool.and_eq_true]
    exact ⟨h c (by simp), isClassical_seqList (d :: cs) (fun e he => h e (by simp [he]))⟩

theorem isClassical_synthPermRaw (n : Nat) (p : Array Nat) :
    isClassical (synthPermRaw (G := G) n p) = true := by
  simp only [synthPermRaw]
  apply isClassical_seqList
  intro c hc
  simp only [List.mem_map] at hc
  obtain ⟨j, _, rfl⟩ := hc
  exact isClassical_theta n j

/-- **Soundness of synthesis.**  If `synthPerm n p` returns a circuit, then it is a
reversible Boolean circuit (only `x`, `swap`, identities and controls) that sends each
basis state `i < 2ⁿ` to `p[i]`; its linear semantics is the corresponding permutation
matrix, for every interpretation of base generators. -/
theorem synthPerm_sound {n : Nat} {p : Array Nat} {c : Circ G n}
    (h : synthPerm n p = .ok c) :
    isClassical c = true ∧ (∀ i, i < 2 ^ n → perm c i = p[i]!) ∧
      ∀ (act : (g : G) → Vec R → Vec R) (v : Vec R) i, i < 2 ^ n →
        den act c v p[i]! = v i := by
  simp only [synthPerm] at h
  split at h
  · cases h
  · split at h
    · next hc =>
      cases h
      have hperm : ∀ i, i < 2 ^ n → perm (synthPermRaw (G := G) n p) i = p[i]! := by
        intro i hi
        rw [beq_iff_eq] at hc
        have h2 : (permTable (synthPermRaw (G := G) n p))[i]! = p[i]! := by rw [hc]
        rw [← h2]
        simp [permTable, hi]
      refine ⟨isClassical_synthPermRaw n p, hperm, ?_⟩
      intro act v i hi
      rw [← hperm i hi]
      exact den_perm act _ (isClassical_synthPermRaw n p) v i
    · cases h

end Qrig

end
