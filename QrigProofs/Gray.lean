module

public import Mathlib
public import Qrig.Core.Classical

/-!
# The reflected Gray code (Section 2.3)

`grayR n` (the translation permutation `rₙ`) is a bijection of `{0, …, 2ⁿ - 1}`, and
consecutive words of the Gray code differ in exactly one bit.  This is what makes each
`θₙ,ᵢ = rₙ⁻¹ ∘ τᵢ ∘ rₙ` a single multiply controlled NOT gate.
-/

@[expose] public section

namespace Qrig

theorem two_pow_add_eq_xor (n a : Nat) (h : a < 2 ^ n) : 2 ^ n + a = 2 ^ n ^^^ a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases lt_trichotomy i n with hi | rfl | hi
  · rw [Nat.testBit_two_pow_add_gt hi]; simp [hi.ne']
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h]; simp
  · have hp : 2 ^ (n + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    have h1 : 2 ^ n + a < 2 ^ i := by rw [pow_succ] at hp; omega
    have h2 : a < 2 ^ i := by omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]; simp [hi.ne]

/-- Every Gray code word is a basis state on `n` wires. -/
theorem grayR_lt : ∀ (n i : Nat), grayR n i < 2 ^ n
  | 0, _ => by simp [grayR]
  | n + 1, i => by
    have := grayR_lt n i
    have := grayR_lt n (2 ^ (n + 1) - 1 - i)
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    unfold grayR
    split_ifs <;> omega

/-- `rₙ` is injective on `{0, …, 2ⁿ - 1}`. -/
theorem grayR_injOn : ∀ (n : Nat) {i j : Nat}, i < 2 ^ n → j < 2 ^ n →
    grayR n i = grayR n j → i = j
  | 0, i, j, hi, hj, _ => by simp at hi hj; omega
  | n + 1, i, j, hi, hj, h => by
    have := grayR_lt n i
    have := grayR_lt n j
    have := grayR_lt n (2 ^ (n + 1) - 1 - i)
    have := grayR_lt n (2 ^ (n + 1) - 1 - j)
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    unfold grayR at h
    split_ifs at h with h1 h2 h2
    · exact grayR_injOn n h1 h2 h
    · omega
    · omega
    · have := grayR_injOn n (i := 2 ^ (n + 1) - 1 - i) (j := 2 ^ (n + 1) - 1 - j)
        (by omega) (by omega) (by omega)
      omega

/-- `rₙ` is a bijection of `{0, …, 2ⁿ - 1}`. -/
theorem grayR_bijOn (n : Nat) :
    Set.BijOn (grayR n) (Set.Iio (2 ^ n)) (Set.Iio (2 ^ n)) := by
  have hm : Set.MapsTo (grayR n) (Set.Iio (2 ^ n)) (Set.Iio (2 ^ n)) :=
    fun i _ => grayR_lt n i
  refine ((Set.finite_Iio _).injOn_iff_bijOn_of_mapsTo hm).1 ?_
  intro i hi j hj h
  exact grayR_injOn n hi hj h

/-- **Gray code property**: consecutive words `hₙ(i)` and `hₙ(i+1)` differ in exactly
one bit. -/
theorem grayR_adjacent : ∀ (n i : Nat), i + 1 < 2 ^ n →
    ∃ k, k < n ∧ grayR n i ^^^ grayR n (i + 1) = 2 ^ k
  | 0, i, hi => by simp at hi
  | n + 1, i, hi => by
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    by_cases h1 : i + 1 < 2 ^ n
    · obtain ⟨k, hk, e⟩ := grayR_adjacent n i h1
      refine ⟨k, by omega, ?_⟩
      simp only [grayR, if_pos h1, if_pos (show i < 2 ^ n by omega), e]
    · by_cases h2 : i + 1 = 2 ^ n
      · refine ⟨n, by omega, ?_⟩
        have e : 2 ^ (n + 1) - 1 - (i + 1) = i := by omega
        simp only [grayR, if_pos (show i < 2 ^ n by omega), if_neg h1, e]
        rw [two_pow_add_eq_xor _ _ (grayR_lt n i), ← Nat.xor_assoc, Nat.xor_comm (grayR n i),
          Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      · obtain ⟨k, hk, e⟩ := grayR_adjacent n (2 ^ (n + 1) - 1 - (i + 1)) (by omega)
        refine ⟨k, by omega, ?_⟩
        have e2 : 2 ^ (n + 1) - 1 - (i + 1) + 1 = 2 ^ (n + 1) - 1 - i := by omega
        rw [e2] at e
        simp only [grayR, if_neg (show ¬ i < 2 ^ n by omega), if_neg h1]
        rw [two_pow_add_eq_xor _ _ (grayR_lt n _), two_pow_add_eq_xor _ _ (grayR_lt n _),
          Nat.xor_assoc, ← Nat.xor_assoc (grayR n _), Nat.xor_comm (grayR n _) (2 ^ n),
          Nat.xor_assoc, ← Nat.xor_assoc (2 ^ n), Nat.xor_self, Nat.zero_xor, Nat.xor_comm, e]

end Qrig

end
