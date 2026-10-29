module

public import QrigProofs.ControlEquations
public import Qrig.Core.Simplify

/-!
# Soundness of the optimiser

`simplify_sound`: for every local interpretation of the base generators and every sound
fusion rule, the optimised circuit has exactly the same semantics as the original one:
`den act (simplify fuse c) = den act c`.

The rewrite rules are justified by the control equations proved in
`QrigProofs.ControlEquations` ((a), (b), (e), (f)), by the involutivity of `x` and `σ`,
and by the functoriality of `+` in each argument.
-/

@[expose] public section

namespace Qrig

variable {G : Type} [GateSig G] [DecidableEq G] {R : Type} {act : (g : G) → Vec R → Vec R}

open Circ

/-- A fusion rule is sound if every proposed replacement of `f ; g` has the semantics of
`f ; g`. -/
def FuseSound (fuse : FuseRule G) (act : (g : G) → Vec R → Vec R) : Prop :=
  ∀ {n : Nat} (f g r : Circ G n), fuse f g = some r → den act r = fun v => den act g (den act f v)

omit [DecidableEq G] in
theorem den_castC {m n : Nat} (h : m = n) (c : Circ G m) : den act (castC h c) = den act c := by
  subst h; rfl

theorem beq_eq : ∀ {m n : Nat} (f : Circ G m) (g : Circ G n), Circ.beq f g = true →
    ∃ h : m = n, castC h f = g := by
  intro m n f
  induction f generalizing n with
  | id a =>
    intro g h
    cases g <;> simp [Circ.beq] at h
    subst h; exact ⟨rfl, rfl⟩
  | x =>
    intro g h
    cases g <;> simp [Circ.beq, Circ.isX] at h
    exact ⟨rfl, rfl⟩
  | swap =>
    intro g h
    cases g <;> simp [Circ.beq, Circ.isSwap] at h
    exact ⟨rfl, rfl⟩
  | gen a =>
    intro g h
    cases g <;> simp [Circ.beq] at h
    subst h; exact ⟨rfl, rfl⟩
  | seq f₁ f₂ ih₁ ih₂ =>
    intro g h
    cases g <;> simp [Circ.beq] at h
    obtain ⟨h1, e1⟩ := ih₁ _ h.1
    obtain ⟨h2, e2⟩ := ih₂ _ h.2
    subst h1; cases e1; cases e2; exact ⟨rfl, rfl⟩
  | par f₁ f₂ ih₁ ih₂ =>
    intro g h
    cases g <;> simp [Circ.beq] at h
    obtain ⟨h1, e1⟩ := ih₁ _ h.1
    obtain ⟨h2, e2⟩ := ih₂ _ h.2
    subst h1; subst h2; cases e1; cases e2; exact ⟨rfl, rfl⟩
  | ctrl b f ih =>
    intro g h
    cases g <;> simp [Circ.beq] at h
    obtain ⟨hb, h2⟩ := h
    obtain ⟨h1, e1⟩ := ih _ h2
    subst h1; cases e1; subst hb; exact ⟨rfl, rfl⟩

theorem beq_den {m n : Nat} {f : Circ G m} {g : Circ G n} (h : Circ.beq f g = true) :
    den act f = den act g := by
  obtain ⟨hmn, rfl⟩ := beq_eq f g h
  exact (den_castC hmn f).symm

omit [DecidableEq G] in
theorem isId_den {n : Nat} {c : Circ G n} (h : c.isId = true) : den act c = fun v => v := by
  cases c <;> simp [Circ.isId] at h
  rfl

omit [DecidableEq G] in
theorem isX_den {n : Nat} {c : Circ G n} (h : c.isX = true) : den act c = den act (x (G := G)) := by
  cases c <;> simp [Circ.isX] at h
  rfl

omit [DecidableEq G] in
theorem isSwap_den {n : Nat} {c : Circ G n} (h : c.isSwap = true) :
    den act c = den act (swap (G := G)) := by
  cases c <;> simp [Circ.isSwap] at h
  rfl

omit [DecidableEq G] in
theorem viewPar_den {m n k : Nat} {g : Circ G k} {a : Circ G m} {b : Circ G n}
    (h : viewPar m n g = some (a, b)) : den act g = den act (par a b) := by
  cases g <;> simp [viewPar] at h
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
  rfl

omit [DecidableEq G] in
theorem viewCtrl_den {n k : Nat} {g : Circ G k} {b : Bool} {f : Circ G n}
    (h : viewCtrl n g = some (b, f)) : den act g = den act (ctrl b f) := by
  cases g <;> simp [viewCtrl] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

omit [DecidableEq G] in
theorem mkCtrl_den {n : Nat} (b : Bool) (f : Circ G n) :
    den act (mkCtrl b f) = den act (ctrl b f) := by
  cases f <;> try rfl
  funext v
  exact (ctrl_id b _ v).symm

omit [DecidableEq G] in
theorem mkPar_den {m n : Nat} (f : Circ G m) (g : Circ G n) :
    den act (mkPar f g) = den act (par f g) := by
  unfold mkPar
  split
  · funext v i
    rw [den_par]
    split
    · simp only [den_id]; congr 1; exact (Nat.div_add_mod' i _).symm
    · rfl
  · rfl

omit [DecidableEq G] in
theorem den_ctrl_congr {n : Nat} (b : Bool) {f f' : Circ G n} (h : den act f = den act f') :
    den act (ctrl b f) = den act (ctrl b f') := by
  funext v i
  simp only [den_ctrl, h]

omit [DecidableEq G] in
theorem den_par_congr {m n : Nat} {f f' : Circ G m} {g g' : Circ G n}
    (hf : den act f = den act f') (hg : den act g = den act g') :
    den act (par f g) = den act (par f' g') := by
  funext v i
  simp only [den_par, hf, hg]

omit [DecidableEq G] in
theorem x_x (v : Vec R) : den act (x (G := G)) (den act (x (G := G)) v) = v := by
  funext i
  simp only [den]
  split_ifs with h h'
  · congr 1; omega
  · omega
  · rfl

omit [DecidableEq G] in
theorem swap_swap (v : Vec R) :
    den act (swap (G := G)) (den act (swap (G := G)) v) = v := by
  funext i
  simp only [den]
  split_ifs <;> first | rfl | (subst_vars; rfl) | omega

omit [DecidableEq G] in
/-- Functoriality of `- + idₙ`. -/
theorem den_par_idR_seq (hact : LocalAct act) {m : Nat} (n : Nat) (a a' : Circ G m) :
    den act (par (seq a a') (Circ.id n)) =
      fun v => den act (par a' (Circ.id n)) (den act (par a (Circ.id n)) v) := by
  funext v i
  have hN : 0 < 2 ^ n := by positivity
  rw [den_par, den_par]
  by_cases hi : i < 2 ^ (m + n)
  · rw [if_pos hi, if_pos hi]
    simp only [den_id]
    have hq : i / 2 ^ n < 2 ^ m := by
      rw [Nat.div_lt_iff_lt_mul hN, ← Nat.pow_add]; exact hi
    have hr : i % 2 ^ n < 2 ^ n := Nat.mod_lt _ hN
    show den act a' (den act a _) _ = _
    apply den_local hact a' _ _ _ _ hq
    intro p hp
    rw [den_par, if_pos (mul_pow_add_lt hp hr)]
    simp only [den_id]
    have e1 : (p * 2 ^ n + i % 2 ^ n) / 2 ^ n = p := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hr, Nat.zero_add]
    have e2 : (p * 2 ^ n + i % 2 ^ n) % 2 ^ n = i % 2 ^ n := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    rw [e1, e2]
  · rw [if_neg hi, if_neg hi, den_par, if_neg hi]

omit [DecidableEq G] in
/-- Functoriality of `idₘ + -`. -/
theorem den_par_idL_seq (hact : LocalAct act) (m : Nat) {n : Nat} (b b' : Circ G n) :
    den act (par (Circ.id m) (seq b b')) =
      fun v => den act (par (Circ.id m) b') (den act (par (Circ.id m) b) v) := by
  funext v i
  have hN : 0 < 2 ^ n := by positivity
  rw [den_par, den_par]
  by_cases hi : i < 2 ^ (m + n)
  · rw [if_pos hi, if_pos hi]
    simp only [den_id]
    have hq : i / 2 ^ n < 2 ^ m := by
      rw [Nat.div_lt_iff_lt_mul hN, ← Nat.pow_add]; exact hi
    have hr : i % 2 ^ n < 2 ^ n := Nat.mod_lt _ hN
    show den act b' (den act b _) _ = _
    apply den_local hact b' _ _ _ _ hr
    intro t ht
    rw [den_par, if_pos (mul_pow_add_lt hq ht)]
    simp only [den_id]
    have e1 : (i / 2 ^ n * 2 ^ n + t) / 2 ^ n = i / 2 ^ n := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt ht, Nat.zero_add]
    have e2 : (i / 2 ^ n * 2 ^ n + t) % 2 ^ n = t := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
    rw [e1, e2]
  · rw [if_neg hi, if_neg hi, den_par, if_neg hi]

theorem getD_combine_den {n : Nat} {fuse : FuseRule G} {a a' : Circ G n}
    (ih : ∀ r, combine fuse a a' = some r → den act r = fun v => den act a' (den act a v)) :
    den act ((combine fuse a a').getD (seq a a')) = den act (seq a a') := by
  cases h : combine fuse a a' with
  | none => rfl
  | some r => simp only [Option.getD_some]; rw [ih r h]; rfl

/-- Every rewrite step performed by `combine` is sound. -/
theorem combine_sound (hact : LocalAct act) {fuse : FuseRule G} (hfuse : FuseSound fuse act) :
    ∀ {n : Nat} (f g r : Circ G n), combine fuse f g = some r →
      den act r = fun v => den act g (den act f v) := by
  intro n f
  induction f with
  | id k =>
    intro g r h
    simp only [combine, Option.some.injEq] at h
    subst h; rfl
  | x =>
    intro g r h
    simp only [combine] at h
    split_ifs at h with h1 h2
    · cases h; funext v; rw [isX_den h1, x_x]; rfl
    · cases h; funext v; rw [isId_den h2]
    · exact hfuse _ _ _ h
  | swap =>
    intro g r h
    simp only [combine] at h
    split_ifs at h with h1 h2
    · cases h; funext v; rw [isSwap_den h1, swap_swap]; rfl
    · cases h; funext v; rw [isId_den h2]
    · exact hfuse _ _ _ h
  | gen a =>
    intro g r h
    simp only [combine] at h
    split_ifs at h with h1
    · cases h; funext v; rw [isId_den h1]
    · exact hfuse _ _ _ h
  | seq f₁ f₂ _ _ =>
    intro g r h
    simp only [combine] at h
    split_ifs at h with h1
    · cases h; funext v; rw [isId_den h1]
    · exact hfuse _ _ _ h
  | @par m n a b iha ihb =>
    intro g r h
    simp only [combine] at h
    split_ifs at h with h1
    · cases h; funext v; rw [isId_den h1]
    · split at h
      · next a' b' hv =>
        rw [viewPar_den hv]
        split_ifs at h with h2 h3
        · cases h
          simp only [Bool.and_eq_true] at h2
          rw [mkPar_den, den_par_congr (getD_combine_den (iha a')) rfl,
            den_par_idR_seq hact n a a',
            den_par_congr rfl ((isId_den h2.1).trans rfl : den act b = den act (Circ.id n)),
            den_par_congr rfl ((isId_den h2.2).trans rfl : den act b' = den act (Circ.id n))]
        · cases h
          simp only [Bool.and_eq_true] at h3
          rw [mkPar_den, den_par_congr rfl (getD_combine_den (ihb b')),
            den_par_idL_seq hact m b b',
            den_par_congr ((isId_den h3.1).trans rfl : den act a = den act (Circ.id m)) rfl,
            den_par_congr ((isId_den h3.2).trans rfl : den act a' = den act (Circ.id m)) rfl]
        · rw [← viewPar_den hv]; exact hfuse _ _ _ h
      · exact hfuse _ _ _ h
  | @ctrl n b f ih =>
    intro g r h
    simp only [combine] at h
    split_ifs at h with h1
    · cases h; funext v; rw [isId_den h1]
    · split at h
      · next b' g' hv =>
        rw [viewCtrl_den hv]
        split_ifs at h with h2 h3
        · have hb : b' = b := ((by simpa using h2 : b = b')).symm
          subst hb
          have key : den act (ctrl b' (seq f g')) =
              fun v => den act (ctrl b' g') (den act (ctrl b' f) v) := by
            funext v; exact ctrl_seq hact b' f g' v
          split at h
          · next r0 hr0 =>
            cases h
            rw [mkCtrl_den, den_ctrl_congr b' ((ih g' r0 hr0).trans (show _ = den act (Circ.seq f g') from rfl)), ← key]
          · cases h; exact key
        · cases h
          have hf : den act f = den act g' := beq_den h3
          rw [den_castC]
          funext v
          rw [← den_ctrl_congr b' hf]
          cases b <;> cases b'
          · simp at h2
          · rw [← ctrl_comm hact f f v, complementarity hact f v]
          · rw [complementarity hact f v]
          · simp at h2
        · rw [← viewCtrl_den hv]; exact hfuse _ _ _ h
      · exact hfuse _ _ _ h

/-! ## Lists of sequentially composed circuits -/

/-- Semantics of a list of circuits composed in sequence. -/
def denL (act : (g : G) → Vec R → Vec R) {n : Nat} : List (Circ G n) → Vec R → Vec R
  | [], v => v
  | c :: cs, v => denL act cs (den act c v)

omit [DecidableEq G] in
theorem denL_append {n : Nat} (l₁ l₂ : List (Circ G n)) (v : Vec R) :
    denL act (l₁ ++ l₂) v = denL act l₂ (denL act l₁ v) := by
  induction l₁ generalizing v with
  | nil => rfl
  | cons c cs ih => exact ih _

omit [DecidableEq G] in
theorem flattenSeq_den : ∀ {n : Nat} (c : Circ G n) (v : Vec R),
    denL act (flattenSeq c) v = den act c v := by
  intro n c
  induction c with
  | seq f g ihf ihg => intro v; simp only [flattenSeq, denL_append, ihf, ihg]; rfl
  | _ => intro v; rfl

omit [DecidableEq G] in
theorem seqList_den {n : Nat} : ∀ (l : List (Circ G n)) (v : Vec R),
    den act (seqList l) v = denL act l v
  | [], _ => rfl
  | [_], _ => rfl
  | c :: d :: cs, v => by
    simp only [seqList, den]
    rw [seqList_den (d :: cs)]
    rfl

theorem pushSeq_den (hact : LocalAct act) {fuse : FuseRule G} (hfuse : FuseSound fuse act)
    {n : Nat} (acc : List (Circ G n)) (c : Circ G n) (v : Vec R) :
    denL act (pushSeq fuse acc c).reverse v = den act c (denL act acc.reverse v) := by
  unfold pushSeq
  split
  · split_ifs with h
    · simp [denL, isId_den h]
    · rfl
  · next t rest =>
    split
    · next r hr =>
      have hs := combine_sound hact hfuse t c r hr
      simp only [List.reverse_cons, denL_append]
      split_ifs with h
      · have e := congrFun hs (denL act rest.reverse v)
        simp only at e
        show _ = den act c (den act t _)
        rw [← e, isId_den h]
      · simp only [List.reverse_cons, denL_append]
        show den act r _ = _
        rw [hs]; rfl
    · split_ifs with h
      · rw [isId_den h]
      · simp only [List.reverse_cons, denL_append]; rfl

theorem foldl_pushSeq_den (hact : LocalAct act) {fuse : FuseRule G} (hfuse : FuseSound fuse act)
    {n : Nat} : ∀ (l acc : List (Circ G n)) (v : Vec R),
    denL act (l.foldl (pushSeq fuse) acc).reverse v = denL act l (denL act acc.reverse v)
  | [], _, _ => rfl
  | c :: cs, acc, v => by
    simp only [List.foldl_cons]
    rw [foldl_pushSeq_den hact hfuse cs, pushSeq_den hact hfuse]
    rfl

/-- One optimisation pass preserves the semantics. -/
theorem simplifyPass_den (hact : LocalAct act) {fuse : FuseRule G} (hfuse : FuseSound fuse act) :
    ∀ {n : Nat} (c : Circ G n), den act (simplifyPass fuse c) = den act c := by
  intro n c
  induction c with
  | id n => rfl
  | x => rfl
  | swap => rfl
  | gen g => rfl
  | seq f g ihf ihg =>
    funext v
    simp only [simplifyPass]
    rw [seqList_den, foldl_pushSeq_den hact hfuse, denL_append]
    simp only [List.reverse_nil, denL, flattenSeq_den, ihf, ihg]
    rfl
  | par f g ihf ihg =>
    simp only [simplifyPass]
    rw [mkPar_den, den_par_congr ihf ihg]
  | ctrl b f ih =>
    simp only [simplifyPass]
    rw [mkCtrl_den, den_ctrl_congr b ih]

theorem simplifyN_den (hact : LocalAct act) {fuse : FuseRule G} (hfuse : FuseSound fuse act) :
    ∀ (k : Nat) {n : Nat} (c : Circ G n), den act (simplifyN fuse k c) = den act c
  | 0, _, _ => rfl
  | k + 1, _, c => by
    simp only [simplifyN]
    split_ifs
    · rfl
    · rw [simplifyN_den hact hfuse k, simplifyPass_den hact hfuse]

/-- **Soundness of the optimiser**: `simplify` preserves the semantics of circuits, for
every local interpretation of the base generators and every sound fusion rule. -/
theorem simplify_sound (hact : LocalAct act) {fuse : FuseRule G} (hfuse : FuseSound fuse act)
    {n : Nat} (c : Circ G n) : den act (simplify fuse c) = den act c :=
  simplifyN_den hact hfuse 16 c

end Qrig

end
