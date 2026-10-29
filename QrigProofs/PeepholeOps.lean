module

public import QrigProofs.Peephole

/-!
# Soundness of the concrete peephole optimiser

The gates `Op` are interpreted by their standard complex matrices (the Qiskit
conventions; an angle `q : ℚ` stands for `θ = qπ`):

| `Op`      | matrix |
|-----------|--------|
| `x`       | `[[0, 1], [1, 0]]` |
| `y`       | `[[0, -i], [i, 0]]` |
| `h`       | `[[1, 1], [1, -1]] / √2` |
| `sx`      | `[[1+i, 1-i], [1-i, 1+i]] / 2` |
| `sxdg`    | `[[1-i, 1+i], [1+i, 1-i]] / 2` |
| `p q`     | `diag(1, e^{iθ})` |
| `rz q`    | `diag(e^{-iθ/2}, e^{iθ/2})` |
| `rx q`    | `[[cos θ/2, -i sin θ/2], [-i sin θ/2, cos θ/2]]` |
| `ry q`    | `[[cos θ/2, -sin θ/2], [sin θ/2, cos θ/2]]` |
| `gen k`   | an arbitrary matrix `genMat k` |

`opSound`: the syntactic operations of `OpAlg Op` (fusion, identity/diagonal/NOT tests)
are sound for this interpretation.  `peephole_sound`: the optimiser `peephole` used by
`qrig` preserves the action of a gate list on every complex state vector, whatever the
matrices of the opaque gates are.
-/

@[expose] public section

namespace Qrig.Flat

open Complex

/-- The complex matrix of a base gate (row `r`, column `s`; `false` = `|0⟩`). -/
noncomputable def opMat (genMat : Nat → Mat ℂ) : Op → Mat ℂ
  | .x => fun r s => if r = s then 0 else 1
  | .y => fun r s => if r = s then 0 else if r then I else -I
  | .h => fun r s => (if r && s then -1 else 1) / ((Real.sqrt 2 : ℝ) : ℂ)
  | .sx => fun r s => if r = s then (1 + I) / 2 else (1 - I) / 2
  | .sxdg => fun r s => if r = s then (1 - I) / 2 else (1 + I) / 2
  | .p q => fun r s => if r = s then (if r then exp (Real.pi * (q : ℂ) * I) else 1) else 0
  | .rz q => fun r s =>
      if r = s then (if r then exp (Real.pi * (q : ℂ) / 2 * I) else exp (-(Real.pi * (q : ℂ) / 2 * I)))
      else 0
  | .rx q => fun r s =>
      if r = s then cos (Real.pi * (q : ℂ) / 2) else -I * sin (Real.pi * (q : ℂ) / 2)
  | .ry q => fun r s =>
      if r = s then cos (Real.pi * (q : ℂ) / 2)
      else if r then sin (Real.pi * (q : ℂ) / 2) else -sin (Real.pi * (q : ℂ) / 2)
  | .gen k => genMat k

theorem normMod_cast (m q : ℚ) :
    ((normMod m q : ℚ) : ℂ) = (q : ℂ) - (m : ℂ) * (((q / m).floor : ℤ) : ℂ) := by
  simp [normMod]

theorem exp_normMod2 (q : ℚ) :
    exp (Real.pi * ((normMod 2 q : ℚ) : ℂ) * I) = exp (Real.pi * (q : ℂ) * I) := by
  rw [normMod_cast]
  set k : ℤ := (q / 2).floor
  have : (Real.pi : ℂ) * ((q : ℂ) - ((2 : ℚ) : ℂ) * (k : ℂ)) * I =
      Real.pi * (q : ℂ) * I - k * (2 * Real.pi * I) := by push_cast; ring
  rw [this, exp_sub, exp_int_mul_two_pi_mul_I, div_one]

theorem exp_normMod4 (q : ℚ) (s : ℂ) (hs : s = 1 ∨ s = -1) :
    exp (s * (Real.pi * ((normMod 4 q : ℚ) : ℂ) / 2 * I)) =
      exp (s * (Real.pi * (q : ℂ) / 2 * I)) := by
  rw [normMod_cast]
  set k : ℤ := (q / 4).floor
  rcases hs with rfl | rfl
  · have : (1 : ℂ) * (Real.pi * ((q : ℂ) - ((4 : ℚ) : ℂ) * (k : ℂ)) / 2 * I) =
        1 * (Real.pi * (q : ℂ) / 2 * I) - k * (2 * Real.pi * I) := by push_cast; ring
    rw [this, exp_sub, exp_int_mul_two_pi_mul_I, div_one]
  · have : (-1 : ℂ) * (Real.pi * ((q : ℂ) - ((4 : ℚ) : ℂ) * (k : ℂ)) / 2 * I) =
        -1 * (Real.pi * (q : ℂ) / 2 * I) - (-k : ℤ) * (2 * Real.pi * I) := by push_cast; ring
    rw [this, exp_sub, exp_int_mul_two_pi_mul_I, div_one]

theorem exp_normMod4_pos (q : ℚ) :
    exp (Real.pi * ((normMod 4 q : ℚ) : ℂ) / 2 * I) = exp (Real.pi * (q : ℂ) / 2 * I) := by
  simpa using exp_normMod4 q 1 (Or.inl rfl)

theorem exp_normMod4_neg (q : ℚ) :
    exp (-(Real.pi * ((normMod 4 q : ℚ) : ℂ) / 2 * I)) = exp (-(Real.pi * (q : ℂ) / 2 * I)) := by
  simpa using exp_normMod4 q (-1) (Or.inr rfl)

theorem half_normMod4 (q : ℚ) :
    (Real.pi * ((normMod 4 q : ℚ) : ℂ) / 2) =
      Real.pi * (q : ℂ) / 2 - (((q / 4).floor : ℤ) : ℂ) * (2 * Real.pi) := by
  rw [normMod_cast]; push_cast; ring

theorem cos_normMod4 (q : ℚ) :
    cos (Real.pi * ((normMod 4 q : ℚ) : ℂ) / 2) = cos (Real.pi * (q : ℂ) / 2) := by
  rw [half_normMod4, cos_sub_int_mul_two_pi]

theorem sin_normMod4 (q : ℚ) :
    sin (Real.pi * ((normMod 4 q : ℚ) : ℂ) / 2) = sin (Real.pi * (q : ℂ) / 2) := by
  rw [half_normMod4, sin_sub_int_mul_two_pi]

theorem opFuse_sound (genMat : Nat → Mat ℂ) (a b c : Op) (h : Op.fuse a b = some c) (r s : Bool) :
    opMat genMat c r s = opMat genMat b r false * opMat genMat a false s +
      opMat genMat b r true * opMat genMat a true s := by
  cases a <;> cases b <;> simp only [Op.fuse, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    cases r <;> cases s
  all_goals simp only [opMat, exp_normMod2, exp_normMod4_pos, exp_normMod4_neg, cos_normMod4,
    sin_normMod4]
  all_goals (try push_cast)
  all_goals try simp only [show ∀ x y : ℂ, ↑Real.pi * (x + y) / 2 = ↑Real.pi * x / 2 + ↑Real.pi * y / 2
      from fun x y => by ring,
    show ∀ x y : ℂ, ↑Real.pi * (x + y) * I = ↑Real.pi * x * I + ↑Real.pi * y * I
      from fun x y => by ring,
    show ∀ x y : ℂ, (x + y) * I = x * I + y * I from fun x y => by ring,
    cos_add, sin_add, exp_add, neg_add]
  all_goals try simp
  all_goals try ring_nf
  all_goals try (simp only [I_sq]; ring)
  all_goals (rw [inv_pow, ← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num)

theorem opSound (genMat : Nat → Mat ℂ) : OpSound (opMat genMat) := by
  refine ⟨opFuse_sound genMat, ?_, ?_, ?_⟩
  · intro a h r s
    cases a <;> simp only [OpAlg.isId, Op.isId, beq_iff_eq, reduceCtorEq] at h
    · rw [opMat, ← exp_normMod2, h]
      cases r <;> cases s <;> simp
    · rw [opMat, ← exp_normMod4_pos, ← exp_normMod4_neg, h]
      cases r <;> cases s <;> simp
    · rw [opMat, ← cos_normMod4, ← sin_normMod4, h]
      cases r <;> cases s <;> simp
    · rw [opMat, ← cos_normMod4, ← sin_normMod4, h]
      cases r <;> cases s <;> simp
  · intro a h r
    cases a <;> simp only [OpAlg.isDiag, Op.isDiag, reduceCtorEq] at h <;> (cases r <;> simp [opMat])
  · intro a h r s
    cases a <;> simp only [OpAlg.isX, Op.isX, reduceCtorEq] at h
    cases r <;> cases s <;> simp [opMat]

/-- **Soundness of `qrig`'s DAG-level optimiser.**  For every interpretation of the
opaque gates, the optimised gate list acts on every complex state vector exactly as the
original list. -/
theorem peephole_sound (genMat : Nat → Mat ℂ) (window fuel : Nat) (gs : List (MCG Op))
    (v : Nat → ℂ) : run (opMat genMat) (peephole window fuel gs).1 v = run (opMat genMat) gs v :=
  optimize_sound (opSound genMat) window fuel gs v

end Qrig.Flat

end
