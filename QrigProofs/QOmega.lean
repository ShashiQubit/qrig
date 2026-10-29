module

public import Mathlib
public import Qrig.Core.QOmega

/-!
# `ℚ(ω)` is a commutative ring

The exact scalars used by `qrig` (`QOmega`, elements `a + bω + cω² + dω³` with `ω⁴ = -1`)
form a commutative ring with the operations implemented in `Qrig.Core.QOmega`.
-/

@[expose] public section

namespace Qrig.QOmega

@[ext] theorem ext' {x y : QOmega} (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c)
    (hd : x.d = y.d) : x = y := by
  cases x; cases y; simp_all

@[simp] theorem zero_a : (0 : QOmega).a = 0 := rfl
@[simp] theorem zero_b : (0 : QOmega).b = 0 := rfl
@[simp] theorem zero_c : (0 : QOmega).c = 0 := rfl
@[simp] theorem zero_d : (0 : QOmega).d = 0 := rfl
@[simp] theorem one_a : (1 : QOmega).a = 1 := rfl
@[simp] theorem one_b : (1 : QOmega).b = 0 := rfl
@[simp] theorem one_c : (1 : QOmega).c = 0 := rfl
@[simp] theorem one_d : (1 : QOmega).d = 0 := rfl

section
variable (x y : QOmega)
@[simp] theorem add_a : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b : (x + y).b = x.b + y.b := rfl
@[simp] theorem add_c : (x + y).c = x.c + y.c := rfl
@[simp] theorem add_d : (x + y).d = x.d + y.d := rfl
@[simp] theorem neg_a : (-x).a = -x.a := rfl
@[simp] theorem neg_b : (-x).b = -x.b := rfl
@[simp] theorem neg_c : (-x).c = -x.c := rfl
@[simp] theorem neg_d : (-x).d = -x.d := rfl
@[simp] theorem sub_a : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b : (x - y).b = x.b - y.b := rfl
@[simp] theorem sub_c : (x - y).c = x.c - y.c := rfl
@[simp] theorem sub_d : (x - y).d = x.d - y.d := rfl
@[simp] theorem mul_a : (x * y).a = x.a * y.a - x.b * y.d - x.c * y.c - x.d * y.b := rfl
@[simp] theorem mul_b : (x * y).b = x.a * y.b + x.b * y.a - x.c * y.d - x.d * y.c := rfl
@[simp] theorem mul_c : (x * y).c = x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d := rfl
@[simp] theorem mul_d : (x * y).d = x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a := rfl
end

/-- `ℚ(ω)` is a commutative ring. -/
instance instCommRing : CommRing QOmega where
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  mul_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  sub_eq_add_neg := by intros; ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

end Qrig.QOmega

end
