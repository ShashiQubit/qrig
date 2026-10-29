module

public import Mathlib
public import Qrig.Core.Peephole

/-!
# Soundness of the DAG-level peephole optimiser

Semantics of multiply controlled gates on state vectors `Nat → R`: basis index `i`,
wire `w` is bit `w` of `i` (this is Qiskit's little-endian convention: qubit `k` is bit
`k`).  A gate `g` with matrix `M = mat g.op` maps `v` to

  `(apply g v) i = M(b,b) · v i + M(b,¬b) · v (i xor 2^t)`  if the controls hold at `i`
  `(apply g v) i = v i`                                      otherwise,

where `t = g.tgt` and `b` is bit `t` of `i`.  A gate list acts by applying the gates left
to right (`run`).

Main result: `optimize_sound`, the optimiser preserves `run` for every matrix
interpretation of the base gates over a commutative ring for which the syntactic
operations of `OpAlg` are sound (`OpSound`).  The rule lemmas are
`combine_sound` (equations (a), (b), (e)), `commutes_sound` (equation (f) and diagonal
commutation) and `xconj_sound` (equation (d)).
-/

@[expose] public section

namespace Qrig.Flat

variable {T : Type} {R : Type} [CommRing R]

/-- A `2 × 2` matrix indexed by booleans: `M r s` is the entry in row `r`, column `s`. -/
abbrev Mat (R : Type) := Bool → Bool → R

/-- The controls `cs` are satisfied by basis state `i`. -/
def ctrlOK (cs : List (Nat × Bool)) (i : Nat) : Bool := cs.all fun c => i.testBit c.1 == c.2

/-- Flip bit `t` of `i`. -/
def flip (i t : Nat) : Nat := i ^^^ 2 ^ t

/-- The action of a multiply controlled gate on a state vector. -/
def apply (mat : T → Mat R) (g : MCG T) (v : Nat → R) : Nat → R := fun i =>
  if ctrlOK g.ctrls i then
    mat g.op (i.testBit g.tgt) (i.testBit g.tgt) * v i +
      mat g.op (i.testBit g.tgt) (!i.testBit g.tgt) * v (flip i g.tgt)
  else v i

/-- The action of a gate list (first gate first). -/
def run (mat : T → Mat R) (gs : List (MCG T)) (v : Nat → R) : Nat → R :=
  gs.foldl (fun v g => apply mat g v) v

/-! ### Bits -/

theorem testBit_flip (i t w : Nat) : (flip i t).testBit w = (i.testBit w ^^ decide (t = w)) := by
  simp [flip, Nat.testBit_xor, Nat.testBit_two_pow]

@[simp] theorem flip_flip (i t : Nat) : flip (flip i t) t = i := by
  simp [flip]

theorem flip_comm (i s t : Nat) : flip (flip i s) t = flip (flip i t) s := by
  simp only [flip, Nat.xor_assoc, Nat.xor_comm (2 ^ s)]

@[simp] theorem testBit_flip_self (i t : Nat) : (flip i t).testBit t = !i.testBit t := by
  simp [testBit_flip]

theorem testBit_flip_ne {i t w : Nat} (h : t ≠ w) : (flip i t).testBit w = i.testBit w := by
  simp [testBit_flip, h]

theorem ctrlOK_iff (cs : List (Nat × Bool)) (i : Nat) :
    ctrlOK cs i = true ↔ ∀ c ∈ cs, i.testBit c.1 = c.2 := by
  simp [ctrlOK, List.all_eq_true]

/-- Flipping a bit that is not a control wire does not change whether controls hold. -/
theorem ctrlOK_flip {cs : List (Nat × Bool)} {t : Nat} (h : ∀ c ∈ cs, c.1 ≠ t) (i : Nat) :
    ctrlOK cs (flip i t) = ctrlOK cs i := by
  apply Bool.eq_iff_iff.2
  simp only [ctrlOK_iff]
  constructor <;> intro H c hc <;> have := H c hc <;>
    simpa [testBit_flip_ne (h c hc).symm] using this

/-! ### `run` -/

@[simp] theorem run_nil (mat : T → Mat R) (v : Nat → R) : run mat [] v = v := rfl

@[simp] theorem run_cons (mat : T → Mat R) (g : MCG T) (gs : List (MCG T)) (v : Nat → R) :
    run mat (g :: gs) v = run mat gs (apply mat g v) := rfl

theorem run_append (mat : T → Mat R) (a b : List (MCG T)) (v : Nat → R) :
    run mat (a ++ b) v = run mat b (run mat a v) := by
  simp [run, List.foldl_append]

theorem run_reverse_cons (mat : T → Mat R) (g : MCG T) (gs : List (MCG T)) (v : Nat → R) :
    run mat (g :: gs).reverse v = apply mat g (run mat gs.reverse v) := by
  simp [run_append]

variable [OpAlg T]

/-- Soundness of the syntactic operations on base gates w.r.t. a matrix interpretation. -/
structure OpSound (mat : T → Mat R) : Prop where
  fuse : ∀ a b c, OpAlg.fuse a b = some c → ∀ r s,
    mat c r s = mat b r false * mat a false s + mat b r true * mat a true s
  isId : ∀ a, OpAlg.isId a = true → ∀ r s, mat a r s = if r = s then 1 else 0
  isDiag : ∀ a, OpAlg.isDiag a = true → ∀ r, mat a r (!r) = 0
  isX : ∀ a, OpAlg.isX a = true → ∀ r s, mat a r s = if r = s then 0 else 1

omit [OpAlg T] in
theorem MCG.wf_iff (g : MCG T) : g.wf = true ↔ ∀ c ∈ g.ctrls, c.1 ≠ g.tgt := by
  simp only [MCG.wf, MCG.wires]
  simp
  constructor
  · rintro ⟨h1, h2⟩ a
    exact ⟨fun h e => h1 (e ▸ h), fun h e => h2 (e ▸ h)⟩
  · intro h
    exact ⟨fun m => (h _).1 m rfl, fun m => (h _).2 m rfl⟩

omit [OpAlg T] in
theorem MCG.mem_supp {g : MCG T} {w : Nat} :
    w ∈ g.supp ↔ w = g.tgt ∨ ∃ c ∈ g.ctrls, c.1 = w := by
  simp [MCG.supp, MCG.wires, eq_comm]

/-! ### Single gates -/

variable {mat : T → Mat R}

theorem apply_isId (hs : OpSound mat) {g : MCG T} (h : OpAlg.isId g.op = true) (v : Nat → R) :
    apply mat g v = v := by
  funext i
  simp only [apply, hs.isId _ h]
  split_ifs <;> simp_all

/-- A diagonal gate multiplies each amplitude by a factor. -/
theorem apply_diag (hs : OpSound mat) {g : MCG T} (h : OpAlg.isDiag g.op = true) (v : Nat → R)
    (i : Nat) : apply mat g v i =
      (if ctrlOK g.ctrls i then mat g.op (i.testBit g.tgt) (i.testBit g.tgt) else 1) * v i := by
  simp only [apply, hs.isDiag _ h]
  split_ifs <;> ring

/-- Uncontrolled NOT on wire `w`. -/
theorem apply_isXon (hs : OpSound mat) {w : Nat} {g : MCG T} (h : isXon w g = true)
    (v : Nat → R) : apply mat g v = fun i => v (flip i w) := by
  simp only [isXon, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  funext i
  simp [apply, h1, h2, ctrlOK, hs.isX _ h3]

/-- Two gates on the same target with the same controls fuse (equation (a)). -/
theorem apply_fuse (hs : OpSound mat) {h g : MCG T} {o : T} (ho : OpAlg.fuse h.op g.op = some o)
    (ht : h.tgt = g.tgt) (hwf : h.wf = true) (hc : ∀ i, ctrlOK h.ctrls i = ctrlOK g.ctrls i)
    (v : Nat → R) : apply mat g (apply mat h v) = apply mat { h with op := o } v := by
  funext i
  have hf := (MCG.wf_iff h).1 hwf
  have hflip : ctrlOK h.ctrls (flip i h.tgt) = ctrlOK h.ctrls i := ctrlOK_flip hf i
  simp only [apply, ← hc, ← ht, hflip, testBit_flip_self, flip_flip, hs.fuse _ _ _ ho]
  split_ifs
  · cases i.testBit h.tgt <;> simp <;> ring
  · rfl

omit [OpAlg T] in
/-- Equation (e): complementary controls. -/
theorem apply_compl {h g : MCG T} {w : Nat} {p : Bool} (hop : h.op = g.op) (ht : h.tgt = g.tgt)
    (hwf : h.wf = true)
    (hh : ∀ i, ctrlOK h.ctrls i = (ctrlOK (dropWire w h.ctrls) i && (i.testBit w == p)))
    (hg : ∀ i, ctrlOK g.ctrls i = (ctrlOK (dropWire w h.ctrls) i && (i.testBit w == !p)))
    (hwt : w ≠ h.tgt) (v : Nat → R) :
    apply mat g (apply mat h v) =
      apply mat { ctrls := dropWire w h.ctrls, tgt := h.tgt, op := h.op } v := by
  funext i
  have hf := (MCG.wf_iff h).1 hwf
  have hflip : ctrlOK h.ctrls (flip i h.tgt) = ctrlOK h.ctrls i := ctrlOK_flip hf i
  have hbw : (flip i h.tgt).testBit w = i.testBit w := testBit_flip_ne hwt.symm
  simp only [apply, hg, ← ht, ← hop, hflip, hh]
  by_cases h1 : ctrlOK (dropWire w h.ctrls) i = true
  · cases hb : i.testBit w <;> cases p <;> simp [h1]
  · simp [h1]

variable [DecidableEq T]

/-! ### Control sets -/

omit [DecidableEq T] [OpAlg T] [CommRing R] in
theorem ctrlOK_of_sub {a b : List (Nat × Bool)} (h : ctrlSub a b = true) {i : Nat}
    (hb : ctrlOK b i = true) : ctrlOK a i = true := by
  rw [ctrlOK_iff] at *
  simp only [ctrlSub, List.all_eq_true, List.contains_iff_mem] at h
  exact fun c hc => hb c (h c hc)

omit [DecidableEq T] [OpAlg T] [CommRing R] in
theorem ctrlOK_setEq {a b : List (Nat × Bool)} (h : ctrlSetEq a b = true) (i : Nat) :
    ctrlOK a i = ctrlOK b i := by
  simp only [ctrlSetEq, Bool.and_eq_true] at h
  apply Bool.eq_iff_iff.2
  exact ⟨ctrlOK_of_sub h.2, ctrlOK_of_sub h.1⟩

omit [DecidableEq T] [OpAlg T] [CommRing R] in
theorem ctrlOK_split {a : List (Nat × Bool)} {w : Nat} {p : Bool} (hmem : (w, p) ∈ a)
    (hall : allOn w p a = true) (i : Nat) :
    ctrlOK a i = (ctrlOK (dropWire w a) i && (i.testBit w == p)) := by
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, ctrlOK_iff, beq_iff_eq, dropWire, List.mem_filter, bne_iff_ne]
  simp only [allOn, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hall
  constructor
  · intro H
    exact ⟨fun c hc => H c hc.1, H _ hmem⟩
  · rintro ⟨H1, H2⟩ c hc
    by_cases hw : c.1 = w
    · rcases hall c hc with h | h
      · exact absurd hw h
      · rw [hw, h, H2]
    · exact H1 c ⟨hc, by simpa using hw⟩

omit [DecidableEq T] [OpAlg T] [CommRing R] in
theorem complWire_spec {a b : List (Nat × Bool)} {w : Nat} (h : complWire a b = some w) :
    ∃ p, (w, p) ∈ a ∧ (∀ i, ctrlOK a i = (ctrlOK (dropWire w a) i && (i.testBit w == p))) ∧
      ∀ i, ctrlOK b i = (ctrlOK (dropWire w a) i && (i.testBit w == !p)) := by
  obtain ⟨_, c, _, rfl, hc, _⟩ := List.findSome?_eq_some_iff.1 h
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true,
    List.contains_iff_mem] at hc
  obtain ⟨⟨⟨⟨hb, ha⟩, hb'⟩, hset⟩, rfl⟩ := hc
  refine ⟨c.2, by simp, fun i => ctrlOK_split (by simp) ha i, fun i => ?_⟩
  rw [ctrlOK_split hb hb' i, ctrlOK_setEq hset i]

/-! ### The rules -/

theorem combine_sound (hs : OpSound mat) {h g : MCG T} {r : Rule} {rs : List (MCG T)}
    (hc : combine h g = some (r, rs)) (v : Nat → R) :
    run mat rs v = apply mat g (apply mat h v) := by
  unfold combine at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  split_ifs at hc with h1 h2 h3
  · obtain ⟨⟨ht, hwh⟩, hwg⟩ := h1
    split at hc
    · rename_i o ho
      split_ifs at hc with hid
      · obtain ⟨rfl, rfl⟩ := hc
        rw [apply_fuse hs ho ht hwh (ctrlOK_setEq h2), apply_isId hs hid]; rfl
      · obtain ⟨rfl, rfl⟩ := hc
        rw [apply_fuse hs ho ht hwh (ctrlOK_setEq h2)]; rfl
    · simp at hc
  · obtain ⟨⟨ht, hwh⟩, hwg⟩ := h1
    split at hc
    · rename_i w hw
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨p, hmem, hh, hg⟩ := complWire_spec hw
      have hwt : w ≠ h.tgt := fun e => (MCG.wf_iff h).1 hwh _ hmem e
      rw [apply_compl (p := p) h3 ht hwh hh hg hwt]; rfl
    · simp at hc

omit [DecidableEq T] in
/-- Two diagonal gates commute. -/
theorem comm_dd (hs : OpSound mat) {g h : MCG T} (hg : OpAlg.isDiag g.op = true)
    (hh : OpAlg.isDiag h.op = true) (v : Nat → R) :
    apply mat h (apply mat g v) = apply mat g (apply mat h v) := by
  funext i
  simp only [apply_diag hs hg, apply_diag hs hh]
  ring

omit [DecidableEq T] in
/-- A diagonal gate commutes with a gate whose target it does not touch. -/
theorem comm_dn (hs : OpSound mat) {g h : MCG T} (hg : OpAlg.isDiag g.op = true)
    (h1 : ∀ c ∈ g.ctrls, c.1 ≠ h.tgt) (h2 : g.tgt ≠ h.tgt) (v : Nat → R) :
    apply mat h (apply mat g v) = apply mat g (apply mat h v) := by
  funext i
  have e1 : ctrlOK g.ctrls (flip i h.tgt) = ctrlOK g.ctrls i := ctrlOK_flip h1 i
  have e2 : (flip i h.tgt).testBit g.tgt = i.testBit g.tgt := testBit_flip_ne h2.symm
  simp only [apply, e1, e2, hs.isDiag _ hg]
  split_ifs <;> ring

omit [DecidableEq T] [OpAlg T] in
/-- Two gates commute if neither touches the other's target. -/
theorem comm_nn {g h : MCG T} (h1 : ∀ c ∈ g.ctrls, c.1 ≠ h.tgt) (h2 : g.tgt ≠ h.tgt)
    (h3 : ∀ c ∈ h.ctrls, c.1 ≠ g.tgt) (v : Nat → R) :
    apply mat h (apply mat g v) = apply mat g (apply mat h v) := by
  funext i
  have e1 : ctrlOK g.ctrls (flip i h.tgt) = ctrlOK g.ctrls i := ctrlOK_flip h1 i
  have e2 : (flip i h.tgt).testBit g.tgt = i.testBit g.tgt := testBit_flip_ne h2.symm
  have e3 : ctrlOK h.ctrls (flip i g.tgt) = ctrlOK h.ctrls i := ctrlOK_flip h3 i
  have e4 : (flip i g.tgt).testBit h.tgt = i.testBit h.tgt := testBit_flip_ne h2
  simp only [apply, e1, e2, e3, e4, flip_comm i h.tgt g.tgt]
  split_ifs <;> ring

omit [DecidableEq T] [OpAlg T] [CommRing R] in
theorem conflict_spec {g h : MCG T} (hc : conflict g h = true) :
    ∃ w b, (w, b) ∈ g.ctrls ∧ (w, !b) ∈ h.ctrls := by
  simp only [conflict, List.any_eq_true, List.contains_iff_mem] at hc
  obtain ⟨c, hc, hc'⟩ := hc
  exact ⟨c.1, c.2, hc, hc'⟩

omit [DecidableEq T] [OpAlg T] in
/-- An inactive gate does not change the amplitude. -/
theorem apply_inactive {g : MCG T} {i : Nat} (h : ctrlOK g.ctrls i = false) (v : Nat → R) :
    apply mat g v i = v i := by
  simp [apply, h]

omit [DecidableEq T] [OpAlg T] in
/-- Gates with contradictory controls commute (equation (f)). -/
theorem comm_conflict {g h : MCG T} (hwg : g.wf = true) (hwh : h.wf = true) {w : Nat} {b : Bool}
    (hg : (w, b) ∈ g.ctrls) (hh : (w, !b) ∈ h.ctrls) (v : Nat → R) :
    apply mat h (apply mat g v) = apply mat g (apply mat h v) := by
  have wg : w ≠ g.tgt := (MCG.wf_iff g).1 hwg _ hg
  have wh : w ≠ h.tgt := (MCG.wf_iff h).1 hwh _ hh
  funext i
  have kg : ∀ j, j.testBit w = !b → ctrlOK g.ctrls j = false := fun j hj => by
    cases hk : ctrlOK g.ctrls j
    · rfl
    · have := (ctrlOK_iff _ _).1 hk _ hg; simp_all
  have kh : ∀ j, j.testBit w = b → ctrlOK h.ctrls j = false := fun j hj => by
    cases hk : ctrlOK h.ctrls j
    · rfl
    · have := (ctrlOK_iff _ _).1 hk _ hh; simp_all
  have fg : (flip i g.tgt).testBit w = i.testBit w := testBit_flip_ne wg.symm
  have fh : (flip i h.tgt).testBit w = i.testBit w := testBit_flip_ne wh.symm
  by_cases hb : i.testBit w = b
  · have a1 := kh i hb
    have a2 := kh (flip i g.tgt) (fg.trans hb)
    rw [apply_inactive a1]
    conv_rhs => rw [apply]
    conv_lhs => rw [apply]
    simp only [apply_inactive a1, apply_inactive a2]
  · have hb' : i.testBit w = !b := by cases b <;> simp_all
    have a1 := kg i hb'
    have a2 := kg (flip i h.tgt) (fh.trans hb')
    rw [apply_inactive (g := g) a1]
    conv_lhs => rw [apply]
    simp only [apply_inactive a1, apply_inactive a2]
    rfl

omit [DecidableEq T] in
theorem commutes_sound (hs : OpSound mat) {g h : MCG T} (hc : commutes g h = true)
    (v : Nat → R) : apply mat h (apply mat g v) = apply mat g (apply mat h v) := by
  simp only [commutes, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
    Bool.not_eq_true'] at hc
  obtain ⟨⟨hwg, hwh⟩, hc | ⟨hm1, hm2⟩⟩ := hc
  · obtain ⟨w, b, hg, hh⟩ := conflict_spec hc
    exact comm_conflict hwg hwh hg hh v
  · have sg : ∀ c ∈ g.ctrls, c.1 ∈ g.supp := fun c hc => MCG.mem_supp.2 (Or.inr ⟨c, hc, rfl⟩)
    have sh : ∀ c ∈ h.ctrls, c.1 ∈ h.supp := fun c hc => MCG.mem_supp.2 (Or.inr ⟨c, hc, rfl⟩)
    have tg : g.tgt ∈ g.supp := MCG.mem_supp.2 (Or.inl rfl)
    have th : h.tgt ∈ h.supp := MCG.mem_supp.2 (Or.inl rfl)
    cases dg : OpAlg.isDiag g.op <;> cases dh : OpAlg.isDiag h.op
    · have ng : g.tgt ∉ h.supp := by simpa using hm1 g.tgt (by simp [MCG.moving, dg])
      have nh : h.tgt ∉ g.supp := by simpa using hm2 h.tgt (by simp [MCG.moving, dh])
      exact comm_nn (fun c hc e => nh (e ▸ sg c hc)) (fun e => nh (e ▸ tg))
        (fun c hc e => ng (e ▸ sh c hc)) v
    · have ng : g.tgt ∉ h.supp := by simpa using hm1 g.tgt (by simp [MCG.moving, dg])
      exact (comm_dn hs dh (fun c hc e => ng (e ▸ sh c hc)) (fun e => ng (e ▸ th)) v).symm
    · have nh : h.tgt ∉ g.supp := by simpa using hm2 h.tgt (by simp [MCG.moving, dh])
      exact comm_dn hs dg (fun c hc e => nh (e ▸ sg c hc)) (fun e => nh (e ▸ tg)) v
    · exact comm_dd hs dg dh v

omit [DecidableEq T] [OpAlg T] [CommRing R] in
theorem ctrlOK_flipW (w : Nat) (h : MCG T) (i : Nat) :
    ctrlOK (flipW w h).ctrls i = ctrlOK h.ctrls (flip i w) := by
  simp only [ctrlOK, flipW, List.all_map]
  congr 1
  funext c
  simp only [Function.comp, testBit_flip]
  by_cases hc : c.1 = w
  · simp [hc]
  · simp [hc, Ne.symm hc]

omit [DecidableEq T] in
/-- Equation (d), colour change: `x_w ; M ; x_w = M[w: 0 ↔ 1]`, stated as
`M ; x_w = x_w ; M[w: 0 ↔ 1]`. -/
theorem xconj_sound (hs : OpSound mat) {w : Nat} {x h : MCG T} (hx : isXon w x = true)
    (ht : transparent w h = true) (v : Nat → R) :
    apply mat x (apply mat h v) = apply mat (flipW w h) (apply mat x v) := by
  simp only [transparent, Bool.and_eq_true, bne_iff_ne] at ht
  rw [apply_isXon hs hx, apply_isXon hs hx]
  funext i
  have e : (flip i w).testBit h.tgt = i.testBit h.tgt := testBit_flip_ne (Ne.symm ht.1)
  simp only [apply, ctrlOK_flipW, e, flip_comm i w h.tgt]
  rfl

omit [DecidableEq T] in
theorem x_x (hs : OpSound mat) {w : Nat} {x y : MCG T} (hx : isXon w x = true)
    (hy : isXon w y = true) (v : Nat → R) : apply mat x (apply mat y v) = v := by
  rw [apply_isXon hs hx, apply_isXon hs hy]
  simp

/-! ### The optimiser -/

omit [DecidableEq T] in
theorem xScan_sound (hs : OpSound mat) {w : Nat} {x : MCG T} (hx : isXon w x = true) :
    ∀ (fuel : Nat) (acc acc' : List (MCG T)), xScan w fuel acc = some acc' →
      ∀ v, run mat acc'.reverse v = apply mat x (run mat acc.reverse v)
  | 0, _, _, h, _ => by simp [xScan] at h
  | _ + 1, [], _, h, _ => by simp [xScan] at h
  | fuel + 1, g :: rest, acc', h, v => by
    simp only [xScan] at h
    split_ifs at h with h1 h2
    · cases h
      rw [run_reverse_cons, x_x hs hx h1]
    · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [run_reverse_cons, run_reverse_cons, xconj_sound hs hx h2,
        ← xScan_sound hs hx fuel rest r hr v]

theorem insertAux_sound (hs : OpSound mat) (g : MCG T) :
    ∀ (fuel : Nat) (acc l : List (MCG T)) (r : Rule), insertAux g fuel acc = some (l, r) →
      ∀ v : Nat → R, run mat l.reverse v = apply mat g (run mat acc.reverse v)
  | 0, _, _, _, h, _ => by simp [insertAux] at h
  | _ + 1, [], _, _, h, _ => by simp [insertAux] at h
  | fuel + 1, h :: rest, l, r, hi, v => by
    simp only [insertAux] at hi
    split at hi
    · rename_i r' rs hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      simp only [List.reverse_append, List.reverse_reverse, run_append]
      rw [combine_sound hs hc, run_reverse_cons]
    · split_ifs at hi with hcomm
      obtain ⟨⟨l', r'⟩, hl, he⟩ := Option.map_eq_some_iff.1 hi
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [run_reverse_cons, insertAux_sound hs g fuel rest l' r' hl v, run_reverse_cons,
        commutes_sound hs hcomm]

theorem insert_sound (hs : OpSound mat) (g : MCG T) (fuel : Nat) (acc : List (MCG T))
    (v : Nat → R) : run mat (insert g fuel acc).1.reverse v = apply mat g (run mat acc.reverse v) := by
  unfold insert
  split
  · rename_i l r hi
    exact insertAux_sound hs g fuel acc l r hi v
  · exact run_reverse_cons mat g acc v

theorem pushGate_sound (hs : OpSound mat) (window : Nat) (acc : List (MCG T)) (g : MCG T)
    (v : Nat → R) : run mat (pushGate window acc g).1.reverse v = apply mat g (run mat acc.reverse v) := by
  simp only [pushGate]
  split_ifs with h1 h2
  · rw [apply_isId hs h1]
  · split
    · rename_i acc' hx
      have hxg : isXon g.tgt g = true := by
        simp only [isXon, Bool.and_eq_true, beq_self_eq_true, and_true] at h2 ⊢; exact h2
      exact xScan_sound hs hxg window acc acc' hx v
    · exact insert_sound hs g window acc v
  · exact insert_sound hs g window acc v

theorem passAux_sound (hs : OpSound mat) (window : Nat) :
    ∀ (gs : List (MCG T)) (st : List (MCG T) × Stats) (v : Nat → R),
      run mat (passAux window st gs).1.reverse v = run mat gs (run mat st.1.reverse v)
  | [], st, v => by simp [passAux]
  | g :: gs, (acc, s), v => by
    simp only [passAux, run_cons]
    rw [passAux_sound hs window gs, pushGate_sound hs]

theorem pass_sound (hs : OpSound mat) (window : Nat) (gs : List (MCG T)) (v : Nat → R) :
    run mat (pass window gs).1 v = run mat gs v := by
  have := passAux_sound hs window gs ([], {}) v
  simpa [pass] using this

/-- **Soundness of the optimiser**: the optimised gate list has exactly the same action
on every state vector as the original one. -/
theorem optimize_sound (hs : OpSound mat) (window : Nat) :
    ∀ (fuel : Nat) (gs : List (MCG T)) (v : Nat → R),
      run mat (optimize window fuel gs).1 v = run mat gs v
  | 0, gs, v => rfl
  | fuel + 1, gs, v => by
    simp only [optimize]
    split_ifs
    · rfl
    · simp only
      rw [optimize_sound hs window fuel, pass_sound hs]

end Qrig.Flat

end
