module

public import QrigProofs.QOmega
public import QrigProofs.Simplify
public import QrigProofs.Exact
public import Qrig.Core.GateFuse

/-!
# Soundness of gate fusion and of the concrete optimiser

* `gateFuse_sound`: multiplying adjacent one-qubit gates and adjacent scalars is sound;
* `simplifyQ_sound`: the optimiser used by `qrig` preserves the exact semantics
  of circuits over the concrete gate set.
-/

@[expose] public section

namespace Qrig

open Circ

theorem asU_eq : ∀ {k : Nat} (f : QCirc k) (A : M2), asU f = some A →
    ∃ h : 1 = k, f = castC h (Circ.gen (Gate.u A.a A.b A.c A.d) : QCirc 1) := by
  intro k f A h
  cases f with
  | gen g =>
    cases g with
    | u a b c d =>
      simp only [asU, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
    | ph z => simp [asU] at h
  | _ => simp [asU] at h

theorem asPh_eq : ∀ {k : Nat} (f : QCirc k) (z : QOmega), asPh f = some z →
    ∃ h : 0 = k, f = castC h (Circ.gen (Gate.ph z) : QCirc 0) := by
  intro k f z h
  cases f with
  | gen g =>
    cases g with
    | u a b c d => simp [asPh] at h
    | ph w =>
      simp only [asPh, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
  | _ => simp [asPh] at h

theorem ofM2_den (A B : M2) (v : Vec QOmega) :
    den Gate.act (ofM2 (B.mul A)) v =
      den Gate.act (Circ.gen (Gate.u B.a B.b B.c B.d) : QCirc 1)
        (den Gate.act (Circ.gen (Gate.u A.a A.b A.c A.d) : QCirc 1) v) := by
  have key : den Gate.act (Circ.gen (Gate.u (B.mul A).a (B.mul A).b (B.mul A).c (B.mul A).d) :
      QCirc 1) v = den Gate.act (Circ.gen (Gate.u B.a B.b B.c B.d) : QCirc 1)
        (den Gate.act (Circ.gen (Gate.u A.a A.b A.c A.d) : QCirc 1) v) := by
    funext i
    simp only [den, Gate.act, GateSig.arity, M2.mul]
    split_ifs <;> first | omega | contradiction | ring
  unfold ofM2
  split_ifs with h
  · rw [← key, h]
    funext i
    simp only [den, Gate.act, GateSig.arity, M2.one]
    split_ifs <;> first | omega | contradiction | (subst_vars; ring)
  · exact key

theorem ofPh_den (z w : QOmega) (v : Vec QOmega) :
    den Gate.act (ofPh (w * z)) v =
      den Gate.act (Circ.gen (Gate.ph w) : QCirc 0)
        (den Gate.act (Circ.gen (Gate.ph z) : QCirc 0) v) := by
  have key : den Gate.act (Circ.gen (Gate.ph (w * z)) : QCirc 0) v =
      den Gate.act (Circ.gen (Gate.ph w) : QCirc 0)
        (den Gate.act (Circ.gen (Gate.ph z) : QCirc 0) v) := by
    funext i
    simp only [den, Gate.act, GateSig.arity]
    split_ifs <;> first | omega | contradiction | ring
  unfold ofPh
  split_ifs with h
  · rw [← key, h]
    funext i
    simp only [den, Gate.act, GateSig.arity]
    split_ifs <;> first | omega | contradiction | (subst_vars; ring)
  · exact key

/-- Fusion of adjacent one-qubit gates / scalars is sound. -/
theorem gateFuse_sound : FuseSound gateFuse Gate.act := by
  intro n f g r h
  dsimp only [gateFuse] at h
  split_ifs at h with h1 h0
  · subst h1
    split at h
    · next A B hA hB =>
      cases h
      obtain ⟨e1, rfl⟩ := asU_eq f A hA
      obtain ⟨e2, rfl⟩ := asU_eq g B hB
      funext v
      rw [den_castC, den_castC, den_castC, ofM2_den]
    · cases h
  · subst h0
    split at h
    · next z w hz hw =>
      cases h
      obtain ⟨e1, rfl⟩ := asPh_eq f z hz
      obtain ⟨e2, rfl⟩ := asPh_eq g w hw
      funext v
      rw [den_castC, den_castC, den_castC, ofPh_den]
    · cases h

/-- **Soundness of the concrete optimiser**: `simplifyQ c` has exactly the same
semantics (hence the same unitary) as `c`. -/
theorem simplifyQ_sound {n : Nat} (c : QCirc n) :
    den Gate.act (simplifyQ c) = den Gate.act c :=
  simplify_sound gate_local gateFuse_sound c

/-- The optimiser preserves the exact unitary matrix. -/
theorem unitary_simplifyQ {n : Nat} (c : QCirc n) : unitary (simplifyQ c) = unitary c := by
  have h := (equivExact_iff (simplifyQ c) c).2 (fun i j _ _ => by rw [simplifyQ_sound])
  simpa only [equivExact, beq_iff_eq] using h

end Qrig

end
