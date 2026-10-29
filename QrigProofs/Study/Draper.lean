module

public import Mathlib

/-!
# The Fourier-space adder of the Shor modular-adder kernel

The application kernel `shor_modadd` (`python/benchmarks/app_circuits.py`, function
`modular_adder_shor`) is built from Draper's adder `_phi_add`: to add a constant `a` to an
`n`-qubit register that has been Fourier transformed, it applies a phase gate to each
qubit `i`.  The angle used (after a bug fix during the study) is

  `2π · ((a · 2ⁱ) mod 2ⁿ) / 2ⁿ`       (`phiAddTurns n a i` turns).

Qiskit's `QFTGate` maps `|x⟩` to `∑ₖ e^{2πi·x·k/2ⁿ} |k⟩` (little-endian `k`).  This file
proves that the phase gates turn `QFT|x⟩` into `QFT|(x + a) mod 2ⁿ⟩`, amplitude by
amplitude (`phiAdd_correct`), and per qubit in the product form
(`phiAdd_correct_qubit`).  It also shows that the angle formula used before the fix
(`phiAddTurnsOld`, the convention of a QFT *without* the final qubit reversal) does not
add `a` under Qiskit's convention (`phiAddOld_wrong`).
-/

@[expose] public section

namespace Qrig.Study

open Complex Finset Real

/-- `e N m = e^{2πi·m/N}`. -/
noncomputable def eTurn (N : ℕ) (m : ℤ) : ℂ := exp (2 * π * I * ((m : ℂ) / N))

/-- Phase of the amplitude of `|k⟩` in Qiskit's `QFT|x⟩` on `n` qubits (unnormalised):
`e^{2πi·x·k/2ⁿ}`. -/
noncomputable def qftAmp (n x k : ℕ) : ℂ := eTurn (2 ^ n) (x * k)

/-- The angle, in turns, that `_phi_add` applies to qubit `i` of an `n`-qubit register
to add the constant `a`: `((a · 2ⁱ) mod 2ⁿ) / 2ⁿ`. -/
def phiAddTurns (n a i : ℕ) : ℕ := (a * 2 ^ i) % 2 ^ n

/-- Factor by which the phase gates of `_phi_add` multiply the amplitude of `|k⟩`: the
product of the phases of the qubits `i` with `kᵢ = 1`. -/
noncomputable def phiAddFactor (n a k : ℕ) : ℂ :=
  ∏ i ∈ range n, if k.testBit i then eTurn (2 ^ n) (phiAddTurns n a i) else 1

theorem eTurn_add (N : ℕ) (m m' : ℤ) : eTurn N (m + m') = eTurn N m * eTurn N m' := by
  unfold eTurn
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eTurn_zero (N : ℕ) : eTurn N 0 = 1 := by simp [eTurn]

/-- `e N m` only depends on `m mod N`. -/
theorem eTurn_congr {N : ℕ} (hN : 0 < N) {m m' : ℤ} (h : m ≡ m' [ZMOD N]) :
    eTurn N m = eTurn N m' := by
  obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.1 h)
  have hm' : m' = m + N * t := by linarith
  rw [hm', eTurn_add]
  have : eTurn N (N * t) = 1 := by
    unfold eTurn
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have : 2 * π * I * (((N * t : ℤ) : ℂ) / N) = t * (2 * π * I) := by
      push_cast
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [this, mul_one]

/-- Binary expansion: `k = ∑_{i<n} kᵢ 2ⁱ` for `k < 2ⁿ`. -/
theorem sum_testBit_mul_pow {n k : ℕ} (hk : k < 2 ^ n) :
    ∑ i ∈ range n, (k.testBit i).toNat * 2 ^ i = k := by
  induction n generalizing k with
  | zero => simp at hk; simp [hk]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have h2 : k / 2 < 2 ^ n := by
      rw [pow_succ] at hk; omega
    have hs : ∑ i ∈ range n, (k.testBit (i + 1)).toNat * 2 ^ (i + 1)
        = 2 * ∑ i ∈ range n, ((k / 2).testBit i).toNat * 2 ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.testBit_succ, pow_succ]
      ring
    rw [hs, ih h2, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h] <;> omega

/-- The phases add up to `a · k` modulo `2ⁿ`. -/
theorem sum_phiAddTurns_modEq (n a k : ℕ) (hk : k < 2 ^ n) :
    ∑ i ∈ range n, (k.testBit i).toNat * phiAddTurns n a i ≡ a * k [MOD 2 ^ n] := by
  conv_rhs => rw [← sum_testBit_mul_pow hk, Finset.mul_sum]
  refine Nat.ModEq.sum fun i _ => ?_
  unfold phiAddTurns
  calc (k.testBit i).toNat * (a * 2 ^ i % 2 ^ n)
      ≡ (k.testBit i).toNat * (a * 2 ^ i) [MOD 2 ^ n] := Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
    _ = a * ((k.testBit i).toNat * 2 ^ i) := by ring

theorem prod_ite_eTurn (N m : ℕ) (b : ℕ → Bool) (t : ℕ → ℕ) :
    ∏ i ∈ range m, (if b i then eTurn N (t i) else 1)
      = eTurn N (∑ i ∈ range m, (b i).toNat * t i : ℕ) := by
  induction m with
  | zero => simp [eTurn_zero]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, Finset.sum_range_succ]
    push_cast
    rw [eTurn_add]
    cases b m <;> simp [eTurn_zero]

theorem phiAddFactor_eq (n a k : ℕ) :
    phiAddFactor n a k
      = eTurn (2 ^ n) (∑ i ∈ range n, (k.testBit i).toNat * phiAddTurns n a i : ℕ) :=
  prod_ite_eTurn _ _ _ _

/-- **Draper's adder (Qiskit convention).**  On the Fourier-transformed register, the phase
gates of `_phi_add` map the amplitude of every basis state `|k⟩` of `QFT|x⟩` to the
amplitude of `|k⟩` in `QFT|(x + a) mod 2ⁿ⟩`; hence they map `QFT|x⟩` to
`QFT|(x + a) mod 2ⁿ⟩`. -/
theorem phiAdd_correct (n a x k : ℕ) (hk : k < 2 ^ n) :
    qftAmp n x k * phiAddFactor n a k = qftAmp n ((x + a) % 2 ^ n) k := by
  unfold qftAmp
  rw [phiAddFactor_eq, ← eTurn_add]
  apply eTurn_congr (by positivity)
  have h1 := Int.natCast_modEq_iff.2 (sum_phiAddTurns_modEq n a k hk)
  have h2 := Int.natCast_modEq_iff.2 (Nat.mod_modEq (x + a) (2 ^ n))
  push_cast at h1 h2 ⊢
  calc (x : ℤ) * k + ∑ i ∈ range n, ((k.testBit i).toNat : ℤ) * (phiAddTurns n a i : ℤ)
      ≡ x * k + a * k [ZMOD 2 ^ n] := Int.ModEq.add_left _ h1
    _ = (x + a) * k := by ring
    _ ≡ ((x + a) % 2 ^ n : ℤ) * k [ZMOD 2 ^ n] := Int.ModEq.mul_right _ h2.symm

/-- Per-qubit form: qubit `i` of `QFT|x⟩` carries the relative phase `e^{2πi·x·2ⁱ/2ⁿ}`;
the phase gate on qubit `i` turns it into the phase for `(x + a) mod 2ⁿ`. -/
theorem phiAdd_correct_qubit (n a x i : ℕ) :
    eTurn (2 ^ n) (x * 2 ^ i) * eTurn (2 ^ n) (phiAddTurns n a i)
      = eTurn (2 ^ n) (((x + a) % 2 ^ n) * 2 ^ i) := by
  rw [← eTurn_add]
  apply eTurn_congr (by positivity)
  have h1 := Int.natCast_modEq_iff.2 (Nat.mod_modEq (a * 2 ^ i) (2 ^ n))
  have h2 := Int.natCast_modEq_iff.2 (Nat.mod_modEq (x + a) (2 ^ n))
  unfold phiAddTurns
  push_cast at h1 h2 ⊢
  calc (x : ℤ) * 2 ^ i + (a * 2 ^ i % 2 ^ n : ℤ)
      ≡ x * 2 ^ i + a * 2 ^ i [ZMOD 2 ^ n] := Int.ModEq.add_left _ h1
    _ = (x + a) * 2 ^ i := by ring
    _ ≡ ((x + a) % 2 ^ n : ℤ) * 2 ^ i [ZMOD 2 ^ n] := Int.ModEq.mul_right _ h2.symm

/-- The angle formula used before the fix: qubit `i` gets `∑_{j ≤ i, aⱼ = 1} 1/2^{i-j+1}`
turns, the convention of a QFT without the final qubit reversal.  Expressed as a numerator
over `2ⁿ` (exact for `i < n`). -/
def phiAddTurnsOld (n a i : ℕ) : ℕ :=
  ∑ j ∈ range (i + 1), if a.testBit j then 2 ^ n / 2 ^ (i - j + 1) else 0

/-- With Qiskit's QFT convention the old formula does not add `a`: for `n = 3`, `a = 1`,
`x = 0`, qubit `0` ends with the phase `e^{2πi·4/8}` instead of the phase `e^{2πi·1/8}` of
`QFT|1⟩`. -/
theorem phiAddOld_wrong :
    eTurn (2 ^ 3) (0 * 2 ^ 0) * eTurn (2 ^ 3) (phiAddTurnsOld 3 1 0)
      ≠ eTurn (2 ^ 3) (((0 + 1) % 2 ^ 3) * 2 ^ 0) := by
  have hold : phiAddTurnsOld 3 1 0 = 4 := by decide
  rw [hold, ← eTurn_add]
  unfold eTurn
  rw [Ne, Complex.exp_eq_exp_iff_exists_int]
  rintro ⟨t, ht⟩
  have hpi : (2 * π * I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero]
  have : ((3 : ℂ) / 8) = t := by
    have := congrArg (· / (2 * π * I)) ht
    simp only at this
    field_simp at this
    push_cast at this
    linear_combination this / 8
  have h8 : ((3 : ℤ) : ℂ) = ((8 * t : ℤ) : ℂ) := by
    push_cast
    linear_combination 8 * this
  have h8' : (3 : ℤ) = 8 * t := by exact_mod_cast h8
  omega

end Qrig.Study
