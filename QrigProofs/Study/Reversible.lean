module

public import Mathlib
public import QrigProofs.Study.Draper

/-!
# Classical reversible circuits: the model behind the study's classical kernels

Several application kernels of the study (`python/benchmarks/app_circuits.py`) are
reversible classical circuits built from multiply controlled NOT gates and NOT gates:
the incrementer, the Hamming-weight counter, the membership oracle and the QROM table
lookup.  On computational basis states such a circuit is a function of bit strings; this
file gives that semantics.

* `CGate` — a NOT on wire `tgt`, controlled by wires with polarities (`true` = fires on
  `1`, `false` = fires on `0`).  `X q` and `MCX cs t` are the gates Qiskit's `x` and
  `mcx` produce.
* `run` — apply a list of gates to a basis state `State = ℕ → Bool`.
* `regVal s b m` — the value of the little-endian register on wires `b, …, b + m - 1`
  (Qiskit's convention).

The main structural fact is **colour change** (control equation (d) of *One rig to control
them all*), the rewrite qrig applies to these kernels: conjugating a block of gates by NOT
gates on wires the block does not target is the same as flipping the polarity of those
controls (`run_xconj`).
-/

@[expose] public section

namespace Qrig.Study

open Finset

/-- A computational basis state: the value of every wire. -/
abbrev State := ℕ → Bool

/-- NOT on wire `tgt`, controlled by the wires in `ctrls` with the given polarities. -/
structure CGate where
  ctrls : List (ℕ × Bool)
  tgt : ℕ

/-- Do all controls of `g` match in state `s`? -/
def CGate.fires (g : CGate) (s : State) : Bool := g.ctrls.all fun c => s c.1 == c.2

/-- Effect of one gate on a basis state. -/
def CGate.apply (g : CGate) (s : State) : State :=
  Function.update s g.tgt (xor (s g.tgt) (g.fires s))

/-- Effect of a gate list (applied left to right) on a basis state. -/
def run (gs : List CGate) (s : State) : State := gs.foldl (fun s g => g.apply s) s

/-- Qiskit's `x(q)`. -/
def X (q : ℕ) : CGate := ⟨[], q⟩

/-- Qiskit's `mcx(cs, t)`: NOT on `t`, controlled positively by every wire of `cs`. -/
def MCX (cs : List ℕ) (t : ℕ) : CGate := ⟨cs.map fun c => (c, true), t⟩

/-- Value of the `m`-bit little-endian register on wires `b, …, b + m - 1`. -/
def regVal (s : State) (b m : ℕ) : ℕ := ∑ j ∈ range m, (s (b + j)).toNat * 2 ^ j

/-! ## Basic facts -/

@[simp] theorem run_nil (s : State) : run [] s = s := rfl

@[simp] theorem run_cons (g : CGate) (gs : List CGate) (s : State) :
    run (g :: gs) s = run gs (g.apply s) := rfl

theorem run_append (gs hs : List CGate) (s : State) :
    run (gs ++ hs) s = run hs (run gs s) := by
  simp [run, List.foldl_append]

theorem CGate.apply_of_ne {g : CGate} {s : State} {w : ℕ} (h : w ≠ g.tgt) :
    g.apply s w = s w := by
  simp [CGate.apply, Function.update_of_ne h]

theorem CGate.apply_tgt (g : CGate) (s : State) :
    g.apply s g.tgt = xor (s g.tgt) (g.fires s) := by
  simp [CGate.apply]

theorem MCX_fires (cs : List ℕ) (t : ℕ) (s : State) :
    (MCX cs t).fires s = true ↔ ∀ c ∈ cs, s c = true := by
  simp [CGate.fires, MCX]

/-- A wire that no gate targets keeps its value. -/
theorem run_of_not_tgt {gs : List CGate} {w : ℕ} (h : ∀ g ∈ gs, g.tgt ≠ w) (s : State) :
    run gs s w = s w := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg')),
      CGate.apply_of_ne (Ne.symm (h g (by simp)))]

theorem regVal_succ (s : State) (b m : ℕ) :
    regVal s b (m + 1) = regVal s b m + (s (b + m)).toNat * 2 ^ m := by
  simp [regVal, Finset.sum_range_succ]

theorem regVal_lt (s : State) (b m : ℕ) : regVal s b m < 2 ^ m := by
  induction m with
  | zero => simp [regVal]
  | succ m ih =>
    rw [regVal_succ, pow_succ]
    cases s (b + m) <;> simp <;> omega

theorem regVal_congr {s s' : State} {b m : ℕ} (h : ∀ j < m, s (b + j) = s' (b + j)) :
    regVal s b m = regVal s' b m :=
  Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]

/-- The register is all ones iff its value is `2ᵐ - 1`. -/
theorem regVal_eq_allOnes_iff (s : State) (b m : ℕ) :
    regVal s b m = 2 ^ m - 1 ↔ ∀ j < m, s (b + j) = true := by
  induction m with
  | zero => simp [regVal]
  | succ m ih =>
    have hr := regVal_lt s b m
    have hp : 0 < 2 ^ m := by positivity
    rw [regVal_succ, pow_succ]
    constructor
    · intro h
      cases hb : s (b + m) with
      | false => simp [hb] at h; omega
      | true =>
        simp [hb] at h
        have := ih.1 (by omega)
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact this j hj
        · exact hb
    · intro h
      have h1 := ih.2 fun j hj => h j (by omega)
      rw [h1, h m (by omega)]
      simp; omega

/-- Binary representations are unique. -/
theorem regVal_inj {s s' : State} {b m : ℕ} (h : regVal s b m = regVal s' b m) :
    ∀ j < m, s (b + j) = s' (b + j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hr := regVal_lt s b m
    have hr' := regVal_lt s' b m
    rw [regVal_succ, regVal_succ] at h
    have key : s (b + m) = s' (b + m) ∧ regVal s b m = regVal s' b m := by
      cases hb : s (b + m) <;> cases hb' : s' (b + m) <;> simp [hb, hb'] at h ⊢ <;> omega
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih key.2 j hj
    · exact key.1

/-- The register holds the value `c` iff its wires carry the bits of `c`. -/
theorem regVal_eq_iff (s : State) (m c : ℕ) (hc : c < 2 ^ m) :
    regVal s 0 m = c ↔ ∀ q < m, s q = c.testBit q := by
  have hv : regVal (fun q => c.testBit q) 0 m = c := by
    simpa [regVal] using sum_testBit_mul_pow hc
  constructor
  · intro h q hq
    simpa using regVal_inj (s' := fun q => c.testBit q) (h.trans hv.symm) q hq
  · intro h
    rw [← hv]
    exact regVal_congr fun j hj => by simpa using h j hj

/-! ## Colour change (control equation (d)) -/

/-- Flip the polarity of the controls on the wires of `zs`. -/
def CGate.flip (zs : List ℕ) (g : CGate) : CGate :=
  ⟨g.ctrls.map fun c => (c.1, xor c.2 (decide (c.1 ∈ zs))), g.tgt⟩

/-- NOT gates on the distinct wires `zs` flip exactly those wires. -/
theorem run_X_list {zs : List ℕ} (hz : zs.Nodup) (s : State) :
    run (zs.map X) s = fun w => xor (s w) (decide (w ∈ zs)) := by
  induction zs generalizing s with
  | nil => funext w; simp
  | cons z zs ih =>
    rw [List.nodup_cons] at hz
    rw [List.map_cons, run_cons, ih hz.2]
    funext w
    by_cases hw : w = z
    · subst hw
      simp [CGate.apply, X, CGate.fires, hz.1]
    · simp [CGate.apply, X, hw]

/-- Flip the wires of `zs`. -/
def xorSet (zs : List ℕ) (s : State) : State := fun w => xor (s w) (decide (w ∈ zs))

theorem xorSet_xorSet (zs : List ℕ) (s : State) : xorSet zs (xorSet zs s) = s := by
  funext w; simp [xorSet]

theorem CGate.flip_fires (zs : List ℕ) (g : CGate) (s : State) :
    (g.flip zs).fires s = g.fires (xorSet zs s) := by
  simp only [CGate.fires, CGate.flip, List.all_map]
  congr 1
  funext c
  simp only [Function.comp, xorSet]
  cases s c.1 <;> cases c.2 <;> cases decide (c.1 ∈ zs) <;> rfl

theorem CGate.apply_xorSet {zs : List ℕ} {g : CGate} (hg : g.tgt ∉ zs) (s : State) :
    g.apply (xorSet zs s) = xorSet zs ((g.flip zs).apply s) := by
  funext w
  have ht : (g.flip zs).tgt = g.tgt := rfl
  by_cases hw : w = g.tgt
  · subst hw
    have hf := CGate.flip_fires zs g s
    rw [CGate.apply_tgt, ← hf]
    simp [xorSet, CGate.apply, ht, hg]
    exact (Function.update_self (f := s) g.tgt _).symm
  · rw [CGate.apply_of_ne hw]
    simp only [xorSet]
    rw [CGate.apply_of_ne (by rwa [ht])]

theorem run_xorSet {zs : List ℕ} {M : List CGate} (hM : ∀ g ∈ M, g.tgt ∉ zs) (s : State) :
    run M (xorSet zs s) = xorSet zs (run (M.map (CGate.flip zs)) s) := by
  induction M generalizing s with
  | nil => rfl
  | cons g M ih =>
    rw [run_cons, CGate.apply_xorSet (hM g (by simp)),
      ih (fun g' hg' => hM g' (List.mem_cons_of_mem g hg'))]
    rfl

/-- **Colour change.**  Conjugating a block `M` of gates by NOT gates on distinct wires
`zs` that `M` does not target equals the block with the polarity of every control on a
wire of `zs` flipped.  (Control equation (d), used by qrig to remove the NOT gates around
the multiply controlled gates of oracles and table lookups.) -/
theorem run_xconj {zs : List ℕ} (hz : zs.Nodup) {M : List CGate}
    (hM : ∀ g ∈ M, g.tgt ∉ zs) (s : State) :
    run (zs.map X ++ M ++ zs.map X) s = run (M.map (CGate.flip zs)) s := by
  have hX : ∀ s', run (zs.map X) s' = xorSet zs s' := fun s' => run_X_list hz s'
  rw [run_append, run_append, hX, hX, run_xorSet hM, xorSet_xorSet]

private theorem incr_arith (r P : ℕ) (x : Bool) (hr : r < P) :
    (r + 1) % P + (xor x (decide (r = P - 1))).toNat * P = (r + x.toNat * P + 1) % (P * 2) := by
  by_cases h : r = P - 1
  · obtain rfl : P = r + 1 := by omega
    have h' : r = r + 1 - 1 := by omega
    rw [decide_eq_true h', Nat.mod_self]
    cases x
    · simp; rw [Nat.mod_eq_of_lt (by omega)]
    · simp
      have : r + (r + 1) + 1 = (r + 1) * 2 := by omega
      rw [this, Nat.mod_self]
  · have hP : r + 1 < P := by omega
    rw [Nat.mod_eq_of_lt hP]
    cases x <;> simp [h] <;> rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem MCX_fires_eq (cs : List ℕ) (t : ℕ) (s : State) :
    (MCX cs t).fires s = decide (∀ c ∈ cs, s c = true) := by
  rw [Bool.eq_iff_iff, MCX_fires]; simp

/-! ## Incrementer (`incrementer`, and the counter inside `hamming_weight`) -/

/-- Controlled increment of the `m`-bit register on wires `b, …`: for `t = m-1, …, 0`, a
NOT on wire `b + t` controlled by `ctrls` and the wires `b, …, b + t - 1`.  With
`ctrls = []`, `b = 0` this is the kernel `incrementer(m)`; with `ctrls = [i]` it is the
counter update of `hamming_weight`. -/
def incrGates (ctrls : List ℕ) (b : ℕ) : ℕ → List CGate
  | 0 => []
  | m + 1 => MCX (ctrls ++ (List.range m).map (b + ·)) (b + m) :: incrGates ctrls b m

/-- **The incrementer adds one modulo `2ᵐ`** (when its controls are all `1`), and touches
no wire outside the register. -/
theorem incr_spec (ctrls : List ℕ) (b m : ℕ) (hc : ∀ c ∈ ctrls, c < b ∨ b + m ≤ c)
    (s : State) :
    (∀ w, (w < b ∨ b + m ≤ w) → run (incrGates ctrls b m) s w = s w) ∧
    regVal (run (incrGates ctrls b m) s) b m =
      if ∀ c ∈ ctrls, s c = true then (regVal s b m + 1) % 2 ^ m else regVal s b m := by
  induction m generalizing s with
  | zero => simp [incrGates, regVal]
  | succ m ih =>
    set g := MCX (ctrls ++ (List.range m).map (b + ·)) (b + m) with hg
    set s1 := g.apply s with hs1
    have hc' : ∀ c ∈ ctrls, c < b ∨ b + m ≤ c := fun c h => (hc c h).imp id (by omega)
    obtain ⟨ih1, ih2⟩ := ih hc' s1
    have hs1_ne : ∀ w, w ≠ b + m → s1 w = s w := fun w hw => CGate.apply_of_ne hw
    have hctrl : (∀ c ∈ ctrls, s1 c = true) ↔ (∀ c ∈ ctrls, s c = true) := by
      apply forall₂_congr
      intro c hcm
      rw [hs1_ne c (by have := hc c hcm; omega)]
    have hreg : regVal s1 b m = regVal s b m := regVal_congr fun j hj => hs1_ne _ (by omega)
    have htop : s1 (b + m) =
        xor (s (b + m)) (decide ((∀ c ∈ ctrls, s c = true) ∧ regVal s b m = 2 ^ m - 1)) := by
      rw [hs1]
      refine (CGate.apply_tgt g s).trans ?_
      congr 1
      show (MCX (ctrls ++ (List.range m).map (b + ·)) (b + m)).fires s = _
      rw [MCX_fires_eq]
      simp only [decide_eq_decide, regVal_eq_allOnes_iff, List.mem_append, List.mem_map, List.mem_range]
      constructor
      · intro h
        exact ⟨fun c hc => h c (Or.inl hc), fun j hj => h _ (Or.inr ⟨j, hj, rfl⟩)⟩
      · rintro ⟨h1, h2⟩ c (hc | ⟨j, hj, rfl⟩)
        · exact h1 c hc
        · exact h2 j hj
    have hrun : run (incrGates ctrls b (m + 1)) s = run (incrGates ctrls b m) s1 := rfl
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [hrun, ih1 w (by omega), hs1_ne w (by omega)]
    · rw [hrun, regVal_succ, ih2, ih1 (b + m) (by omega), htop, hreg, regVal_succ, pow_succ]
      by_cases hA : ∀ c ∈ ctrls, s c = true
      · rw [if_pos (hctrl.2 hA), if_pos hA]
        simp only [and_iff_right hA]
        exact incr_arith _ _ _ (regVal_lt s b m)
      · rw [if_neg (mt hctrl.1 hA), if_neg hA]
        simp only [hA, false_and, decide_false, Bool.xor_false]

/-- The kernel `incrementer(n)` maps the basis state of `x` to that of `(x + 1) mod 2ⁿ`. -/
theorem incrementer_spec (n : ℕ) (s : State) :
    regVal (run (incrGates [] 0 n) s) 0 n = (regVal s 0 n + 1) % 2 ^ n := by
  simpa using (incr_spec [] 0 n (by simp) s).2

/-! ## Hamming weight (`hamming_weight`) -/

/-- The kernel `hamming_weight(nin)` with an `nout`-bit counter on wires `nin, …`: one
controlled increment per input wire. -/
def hammingGates (nin nout : ℕ) : List CGate :=
  (List.range nin).flatMap fun i => incrGates [i] nin nout

/-- Number of input wires `0, …, n - 1` that carry `1`. -/
def popcount (s : State) (n : ℕ) : ℕ := (List.range n).countP fun i => s i

/-- The counter width used by `hamming_weight`: `max(1, ⌈log₂(nin + 1)⌉)`. -/
def hammingOut (nin : ℕ) : ℕ := max 1 (Nat.clog 2 (nin + 1))

theorem hamming_aux (nin nout : ℕ) (L : List ℕ) (hL : ∀ i ∈ L, i < nin) (s : State) :
    (∀ i < nin, run (L.flatMap fun i => incrGates [i] nin nout) s i = s i) ∧
    regVal (run (L.flatMap fun i => incrGates [i] nin nout) s) nin nout =
      (regVal s nin nout + L.countP fun i => s i) % 2 ^ nout := by
  induction L generalizing s with
  | nil => simp [Nat.mod_eq_of_lt (regVal_lt s nin nout)]
  | cons i L ih =>
    have hi : i < nin := hL i (by simp)
    obtain ⟨h1, h2⟩ := incr_spec [i] nin nout (by simp [hi]) s
    set s1 := run (incrGates [i] nin nout) s
    obtain ⟨ih1, ih2⟩ := ih (fun j hj => hL j (List.mem_cons_of_mem i hj)) s1
    rw [List.flatMap_cons, run_append]
    have hcount : (L.countP fun j => s1 j) = L.countP fun j => s j :=
      List.countP_congr fun j hj => by
        rw [h1 j (Or.inl (hL j (List.mem_cons_of_mem i hj)))]
    refine ⟨fun j hj => by rw [ih1 j hj, h1 j (Or.inl hj)], ?_⟩
    rw [ih2, h2, hcount, List.countP_cons]
    by_cases hs : s i = true
    · simp only [List.mem_singleton, forall_eq, hs, if_true]
      rw [Nat.mod_add_mod]; ring_nf
    · simp only [List.mem_singleton, forall_eq, hs]
      simp

/-- The counter ends with its initial value plus the number of `1` inputs (mod `2^nout`),
and the inputs are unchanged. -/
theorem hamming_spec (nin nout : ℕ) (s : State) :
    (∀ i < nin, run (hammingGates nin nout) s i = s i) ∧
    regVal (run (hammingGates nin nout) s) nin nout = (regVal s nin nout + popcount s nin) % 2 ^ nout :=
  hamming_aux nin nout (List.range nin) (fun _ hi => List.mem_range.1 hi) s

theorem lt_two_pow_hammingOut (nin : ℕ) : nin < 2 ^ hammingOut nin := by
  have h1 := Nat.le_pow_clog (b := 2) (by norm_num) (nin + 1)
  have h2 : 2 ^ Nat.clog 2 (nin + 1) ≤ 2 ^ hammingOut nin :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  omega

/-- **`hamming_weight` computes the Hamming weight**: starting with a zero counter of the
width used by the kernel, the counter ends holding the number of `1` inputs. -/
theorem hamming_weight_correct (nin : ℕ) (s : State)
    (h0 : ∀ j < hammingOut nin, s (nin + j) = false) :
    regVal (run (hammingGates nin (hammingOut nin)) s) nin (hammingOut nin) = popcount s nin := by
  have hz : regVal s nin (hammingOut nin) = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [h0 j (Finset.mem_range.1 hj)]; simp
  have hp : popcount s nin ≤ nin := by
    simpa [popcount] using List.countP_le_length (l := List.range nin) (p := fun i => s i)
  rw [(hamming_spec nin _ s).2, hz, zero_add,
    Nat.mod_eq_of_lt (lt_of_le_of_lt hp (lt_two_pow_hammingOut nin))]

/-! ## Membership oracle (`membership_oracle`) -/

/-- The wires `q < n` on which the constant `c` has a `0` bit. -/
def zerosOf (n c : ℕ) : List ℕ := (List.range n).filter fun q => !c.testBit q

/-- Textbook comparison with a constant: NOTs on the `0` bits of `c`, an `n`-controlled
NOT onto wire `n`, NOTs back. -/
def memberBlock (n c : ℕ) : List CGate :=
  (zerosOf n c).map X ++ [MCX (List.range n) n] ++ (zerosOf n c).map X

/-- The kernel `membership_oracle`: one comparison block per element of `S`. -/
def memberOracle (n : ℕ) (S : List ℕ) : List CGate := S.flatMap (memberBlock n)

/-- After colour change, the multiply controlled NOT of a comparison block fires exactly when
the register on wires `0, …, n - 1` holds `c`. -/
theorem flip_MCX_fires (n c t : ℕ) (hc : c < 2 ^ n) (s : State) :
    ((MCX (List.range n) t).flip (zerosOf n c)).fires s = decide (regVal s 0 n = c) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, regVal_eq_iff s n c hc]
  simp only [CGate.fires, CGate.flip, MCX, zerosOf, List.map_map, List.all_eq_true,
    List.mem_map, List.mem_range, List.mem_filter, Function.comp, beq_iff_eq]
  constructor
  · intro h q hq
    have := h _ ⟨q, hq, rfl⟩
    cases hb : c.testBit q <;> simp_all
  · rintro h _ ⟨a, ha, rfl⟩
    have := h a ha
    cases hb : c.testBit a <;> simp_all

theorem zerosOf_nodup (n c : ℕ) : (zerosOf n c).Nodup := List.nodup_range.filter _

theorem lt_of_mem_zerosOf {n c q : ℕ} (h : q ∈ zerosOf n c) : q < n := by
  simp only [zerosOf, List.mem_filter, List.mem_range] at h
  exact h.1

/-- One block flips the target iff the input register equals `c`. -/
theorem memberBlock_spec (n c : ℕ) (hc : c < 2 ^ n) (s : State) :
    run (memberBlock n c) s = Function.update s n (xor (s n) (decide (regVal s 0 n = c))) := by
  rw [memberBlock, run_xconj (zerosOf_nodup n c)
    (by simp only [List.mem_singleton, forall_eq, MCX]; exact fun h => lt_irrefl _ (lt_of_mem_zerosOf h))]
  simp only [List.map_cons, List.map_nil, run_cons, run_nil, CGate.apply, flip_MCX_fires n c n hc]
  rfl

/-- **The membership oracle flips the target iff the input is in `S`** (`S` a list of
distinct `n`-bit constants), and changes no other wire. -/
theorem memberOracle_spec (n : ℕ) {S : List ℕ} (hS : S.Nodup) (hlt : ∀ c ∈ S, c < 2 ^ n)
    (s : State) :
    run (memberOracle n S) s = Function.update s n (xor (s n) (decide (regVal s 0 n ∈ S))) := by
  induction S generalizing s with
  | nil => simp [memberOracle]
  | cons c S ih =>
    rw [List.nodup_cons] at hS
    rw [memberOracle, List.flatMap_cons, run_append, memberBlock_spec n c (hlt c (by simp)) s]
    rw [← memberOracle, ih hS.2 (fun c' hc' => hlt c' (List.mem_cons_of_mem c hc'))]
    have hreg : regVal (Function.update s n (xor (s n) (decide (regVal s 0 n = c)))) 0 n =
        regVal s 0 n :=
      regVal_congr fun j hj => Function.update_of_ne (by omega) _ _
    rw [hreg, Function.update_idem, Function.update_self]
    congr 1
    by_cases hx : regVal s 0 n = c
    · rw [hx]; simp [hS.1]
    · simp [hx]

/-! ## QROM table lookup (`qrom`) -/

/-- Lookup block for address `a` and data word `word`: NOTs on the `0` bits of `a`, one
`addr`-controlled NOT onto data wire `addr + b` for every `1` bit `b` of `word`, NOTs back. -/
def qromBlock (addr data a word : ℕ) : List CGate :=
  (zerosOf addr a).map X ++
    ((List.range data).filter fun b => word.testBit b).map (fun b => MCX (List.range addr) (addr + b)) ++
    (zerosOf addr a).map X

/-- Gates with distinct targets that all fire under the same condition `F`, which none of
the targets influences, act in parallel. -/
theorem run_parallel (G : List CGate) (F : State → Bool) (hF : ∀ g ∈ G, g.fires = F)
    (hinv : ∀ s t v, t ∈ G.map CGate.tgt → F (Function.update s t v) = F s)
    (hnd : (G.map CGate.tgt).Nodup) (s : State) :
    run G s = fun w => xor (s w) (F s && decide (w ∈ G.map CGate.tgt)) := by
  induction G generalizing s with
  | nil => funext w; simp
  | cons g G ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [run_cons, ih (fun g' hg' => hF g' (List.mem_cons_of_mem g hg'))
      (fun s t v ht => hinv s t v (List.mem_cons_of_mem _ ht)) hnd.2]
    have hFg : F (g.apply s) = F s := hinv s g.tgt _ (by simp)
    rw [hFg]
    funext w
    by_cases hw : w = g.tgt
    · subst hw
      rw [CGate.apply_tgt, hF g (by simp)]
      simp [hnd.1]
    · rw [CGate.apply_of_ne hw]
      simp [hw]

/-- The data wires flipped by the block for the word `word`. -/
def qromTargets (addr data word : ℕ) : List ℕ :=
  ((List.range data).filter fun b => word.testBit b).map (addr + ·)

/-- One lookup block XORs `word` into the data register iff the address register holds `a`. -/
theorem qromBlock_spec (addr data a word : ℕ) (ha : a < 2 ^ addr) (s : State) :
    run (qromBlock addr data a word) s = fun w =>
      xor (s w) (decide (regVal s 0 addr = a) && decide (w ∈ qromTargets addr data word)) := by
  rw [qromBlock, run_xconj (zerosOf_nodup addr a)]
  · have hmap : List.map CGate.tgt ((((List.range data).filter fun b => word.testBit b).map
          (fun b => MCX (List.range addr) (addr + b))).map (CGate.flip (zerosOf addr a)))
          = qromTargets addr data word := by
      simp [qromTargets, List.map_map, Function.comp_def, CGate.flip, MCX]
    rw [run_parallel _ (fun s => decide (regVal s 0 addr = a)), hmap]
    · intro g hg
      simp only [List.map_map, List.mem_map, Function.comp] at hg
      obtain ⟨b, -, rfl⟩ := hg
      funext s
      exact flip_MCX_fires addr a _ ha s
    · intro s t v ht
      rw [hmap] at ht
      simp only [qromTargets, List.mem_map] at ht
      obtain ⟨b, -, rfl⟩ := ht
      rw [regVal_congr (s' := s) fun j hj => Function.update_of_ne (by omega) _ _]
    · rw [hmap]
      exact (List.nodup_range.filter _).map (fun x y h => by simpa using h)
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨b, -, rfl⟩ := hg
    exact fun h => by have := lt_of_mem_zerosOf h; simp [MCX] at this

theorem qrom_aux (addr data : ℕ) (table : ℕ → ℕ) (A : List ℕ) (hA : A.Nodup)
    (hlt : ∀ a ∈ A, a < 2 ^ addr) (s : State) :
    (∀ q < addr, run (A.flatMap fun a => qromBlock addr data a (table a)) s q = s q) ∧
    ∀ b < data, run (A.flatMap fun a => qromBlock addr data a (table a)) s (addr + b) =
      xor (s (addr + b)) (decide (regVal s 0 addr ∈ A) && (table (regVal s 0 addr)).testBit b) := by
  induction A generalizing s with
  | nil => simp
  | cons a A ih =>
    rw [List.nodup_cons] at hA
    rw [List.flatMap_cons, run_append, qromBlock_spec addr data a (table a) (hlt a (by simp)) s]
    set s1 : State := fun w =>
      xor (s w) (decide (regVal s 0 addr = a) && decide (w ∈ qromTargets addr data (table a)))
    have hs1 : ∀ q < addr, s1 q = s q := by
      intro q hq
      have : q ∉ qromTargets addr data (table a) := by
        simp only [qromTargets, List.mem_map]; omega
      simp [s1, this]
    have hreg : regVal s1 0 addr = regVal s 0 addr :=
      regVal_congr fun j hj => hs1 _ (by omega)
    obtain ⟨ih1, ih2⟩ := ih hA.2 (fun a' ha' => hlt a' (List.mem_cons_of_mem a ha')) s1
    refine ⟨fun q hq => by rw [ih1 q hq, hs1 q hq], fun b hb => ?_⟩
    rw [ih2 b hb, hreg]
    have hmem : (addr + b ∈ qromTargets addr data (table a)) ↔ (table a).testBit b := by
      simp [qromTargets, hb]
    simp only [s1]
    by_cases hx : regVal s 0 addr = a
    · rw [hx]; simp [hA.1, hmem]
    · simp [hx]

/-- The kernel `qrom(addr, data)` for the table `table`. -/
def qromGates (addr data : ℕ) (table : ℕ → ℕ) : List CGate :=
  (List.range (2 ^ addr)).flatMap fun a => qromBlock addr data a (table a)

/-- **QROM performs the table lookup**: every data wire `addr + b` (`b < data`) is XORed
with bit `b` of `table x`, where `x` is the address held in wires `0, …, addr - 1`; the
address wires are unchanged. -/
theorem qrom_spec (addr data : ℕ) (table : ℕ → ℕ) (s : State) :
    (∀ q < addr, run (qromGates addr data table) s q = s q) ∧
    ∀ b < data, run (qromGates addr data table) s (addr + b) =
      xor (s (addr + b)) ((table (regVal s 0 addr)).testBit b) := by
  obtain ⟨h1, h2⟩ := qrom_aux addr data table (List.range (2 ^ addr)) List.nodup_range
    (fun a ha => List.mem_range.1 ha) s
  refine ⟨h1, fun b hb => ?_⟩
  rw [qromGates, h2 b hb]
  simp [regVal_lt]

end Qrig.Study
