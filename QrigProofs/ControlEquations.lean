module

public import QrigProofs.Basic

/-!
# Soundness of the control equations (Definition 6 / Figure 1)

For every choice of (local) semantics of the base generators, the semantics `den`
(the functor `A : cP → P₂`) validates the eight control equations (a)–(h) of the paper.
This is the soundness half of Lemma 21.  Each equation is stated pointwise on vectors:
`den act c v` is the result of running circuit `c` on vector `v`, so e.g.
`den act g (den act f v)` is the semantics of `f ; g` (first `f`, then `g`).
-/

@[expose] public section

namespace Qrig

variable {G : Type} [GateSig G] {R : Type} {act : (g : G) → Vec R → Vec R}

open Circ

lemma den_ctrl {b : Bool} {n : Nat} (f : Circ G n) (v : Vec R) (i : Nat) :
    den act (ctrl b f) v i =
      if inHalf b n i then den act f (fun j => v (ctrlOff b n + j)) (i - ctrlOff b n)
      else v i := rfl

lemma den_ctrl_in {b : Bool} {n : Nat} {i : Nat} (h : inHalf b n i = true)
    (f : Circ G n) (v : Vec R) :
    den act (ctrl b f) v i = den act f (fun j => v (ctrlOff b n + j)) (i - ctrlOff b n) := by
  rw [den_ctrl, if_pos h]

lemma den_ctrl_out {b : Bool} {n : Nat} {i : Nat} (h : inHalf b n i = false)
    (f : Circ G n) (v : Vec R) : den act (ctrl b f) v i = v i := by
  rw [den_ctrl, if_neg (by simp [h])]

lemma den_id {n : Nat} (v : Vec R) : den act (Circ.id (G := G) n) v = v := rfl

lemma den_swap (w : Vec R) (i : Nat) :
    den act (swap (G := G)) w i = if i = 1 then w 2 else if i = 2 then w 1 else w i := rfl

lemma den_par {m n : Nat} (f : Circ G m) (g : Circ G n) (v : Vec R) (i : Nat) :
    den act (par f g) v i =
      if i < 2 ^ (m + n) then
        den act f (fun a => den act g (fun b => v (a * 2 ^ n + b)) (i % 2 ^ n)) (i / 2 ^ n)
      else v i := rfl

lemma den_par_x_id (n : Nat) (w : Vec R) (i : Nat) :
    den act (par (x (G := G)) (Circ.id n)) w i =
      if i < 2 ^ n then w (2 ^ n + i) else if i < 2 ^ n + 2 ^ n then w (i - 2 ^ n) else w i := by
  have hp : (0 : Nat) < 2 ^ n := by positivity
  have h2 : 2 ^ (1 + n) = 2 ^ n + 2 ^ n := by rw [Nat.add_comm, two_pow_succ']
  rw [den_par]
  by_cases hlo : i < 2 ^ n
  · rw [if_pos (by omega), if_pos hlo]
    simp [den, Nat.div_eq_of_lt hlo, Nat.mod_eq_of_lt hlo, Nat.add_comm]
  · by_cases hhi : i < 2 ^ n + 2 ^ n
    · have hd : i / 2 ^ n = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have hm : i % 2 ^ n = i - 2 ^ n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [if_pos (by omega), if_neg hlo, if_pos hhi]
      simp [den, hd, hm]
    · rw [if_neg (by omega), if_neg hlo, if_neg hhi]

lemma block_lt {A r P N : Nat} (hr : r < P) : A * P + r < N * P ↔ A < N := by
  constructor
  · intro h; by_contra h'; push_neg at h'; nlinarith
  · intro h; nlinarith

lemma block_le {A r P N : Nat} (hr : r < P) : N * P ≤ A * P + r ↔ N ≤ A := by
  constructor
  · intro h; by_contra h'; push_neg at h'; nlinarith
  · intro h; nlinarith

lemma den_par_swap_id (n : Nat) (w : Vec R) (i : Nat) :
    den act (par (swap (G := G)) (Circ.id n)) w i =
      if 2 ^ n ≤ i ∧ i < 2 * 2 ^ n then w (i + 2 ^ n)
      else if 2 * 2 ^ n ≤ i ∧ i < 3 * 2 ^ n then w (i - 2 ^ n) else w i := by
  have e1 : 2 ^ (2 + n) = 4 * 2 ^ n := by rw [Nat.pow_add]
  rw [den_par, e1]
  simp only [den_swap, den_id]
  have hP : (0 : Nat) < 2 ^ n := by positivity
  generalize 2 ^ n = N at *
  obtain ⟨A, r, hr, rfl⟩ : ∃ A r, r < N ∧ i = A * N + r :=
    ⟨i / N, i % N, Nat.mod_lt _ hP, (Nat.div_add_mod' i N).symm⟩
  have dm : ∀ B, (B * N + r) / N = B ∧ (B * N + r) % N = r := fun B =>
    ⟨by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr, Nat.zero_add],
     by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]⟩
  rw [(dm A).1, (dm A).2]
  rcases Nat.lt_or_ge A 4 with hA | hA
  · interval_cases A
    · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    · rw [if_pos (by omega), if_pos rfl, if_pos (by omega)]; congr 1; omega
    · rw [if_pos (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega),
        if_pos (by omega)]; congr 1; omega
    · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
  · have : 4 * N ≤ A * N := Nat.mul_le_mul_right N hA
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma den_ctrl_ctrl {n : Nat} (f : Circ G n) (w : Vec R) (i : Nat) :
    den act (ctrl true (ctrl true f)) w i =
      if 3 * 2 ^ n ≤ i ∧ i < 4 * 2 ^ n then den act f (fun j => w (3 * 2 ^ n + j)) (i - 3 * 2 ^ n)
      else w i := by
  have e2 : 2 ^ (n + 1 + 1) = 4 * 2 ^ n := by rw [Nat.pow_succ, Nat.pow_succ]; ring
  have e3 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
  rw [den_ctrl]
  simp only [den_ctrl, inHalf, ctrlOff, if_true, e2, e3, decide_eq_true_eq]
  by_cases h : 3 * 2 ^ n ≤ i ∧ i < 4 * 2 ^ n
  · rw [if_pos (by omega), if_pos (by omega), if_pos h]
    congr 1
    · funext j; congr 1; omega
    · omega
  · rw [if_neg h]
    split_ifs
    · omega
    · congr 1; omega
    · rfl

/-- (a) composition: `C^b(g ∘ f) = C^b(g) ∘ C^b(f)` (for both colours of control). -/
theorem ctrl_seq (hact : LocalAct act) (b : Bool) {n : Nat} (f g : Circ G n) (v : Vec R) :
    den act (ctrl b (seq f g)) v = den act (ctrl b g) (den act (ctrl b f) v) := by
  funext i
  simp only [den]
  split
  · next hh =>
    symm
    apply den_local hact g
    · intro j hj
      have h1 : inHalf b n (ctrlOff b n + j) = true := by rw [inHalf_true_iff]; omega
      simp only [h1, if_true, Nat.add_sub_cancel_left]
    · rw [inHalf_true_iff] at hh; omega
  · simp

/-- (b) identity: `C^b(idₙ) = idₙ₊₁`. -/
theorem ctrl_id (b : Bool) (n : Nat) (v : Vec R) :
    den act (ctrl b (Circ.id (G := G) n)) v = den act (Circ.id (G := G) (n + 1)) v := by
  funext i
  simp only [den]
  split
  · next hh => rw [inHalf_true_iff] at hh; congr 1; omega
  · rfl

/-- (c) strength: `C¹(f + idₘ) = C¹(f) + idₘ`. -/
theorem ctrl_par_id {n : Nat} (f : Circ G n) (m : Nat) (v : Vec R) :
    den act (ctrl true (par f (Circ.id m))) v = den act (par (ctrl true f) (Circ.id m)) v := by
  funext i
  have e1 : 2 ^ (n + m) = 2 ^ n * 2 ^ m := by rw [Nat.pow_add]
  have e2 : 2 ^ (n + 1 + m) = (2 ^ n + 2 ^ n) * 2 ^ m := by rw [Nat.pow_add, two_pow_succ']
  have e3 : 2 ^ (n + m + 1) = (2 ^ n + 2 ^ n) * 2 ^ m := by rw [two_pow_succ', e1, Nat.add_mul]
  rw [den_ctrl, den_par (ctrl true f)]
  simp only [den_par, den_ctrl, den_id, inHalf, ctrlOff, if_true, e1, e2, e3, two_pow_succ']
  have hP : (0 : Nat) < 2 ^ m := by positivity
  generalize 2 ^ m = P at *
  generalize 2 ^ n = N at *
  obtain ⟨A, r, hr, rfl⟩ : ∃ A r, r < P ∧ i = A * P + r :=
    ⟨i / P, i % P, Nat.mod_lt _ hP, (Nat.div_add_mod' i P).symm⟩
  have hdiv : (A * P + r) / P = A := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr, Nat.zero_add]
  have hmod : (A * P + r) % P = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  simp only [hdiv, hmod]
  have dm : ∀ B, (B * P + r) / P = B ∧ (B * P + r) % P = r := fun B =>
    ⟨by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr, Nat.zero_add],
     by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]⟩
  by_cases hin : N ≤ A ∧ A < N + N
  · have hsub : A * P + r - N * P = (A - N) * P + r := by
      have : N * P ≤ A * P := Nat.mul_le_mul_right P hin.1
      rw [Nat.sub_mul]; omega
    have c1 : N * P ≤ A * P + r ∧ A * P + r < (N + N) * P :=
      ⟨(block_le hr).mpr hin.1, (block_lt hr).mpr hin.2⟩
    have c2 : (A - N) * P + r < N * P := (block_lt hr).mpr (by omega)
    simp only [c1, c2, hsub, (dm _).1, (dm _).2, hin, decide_true, and_self, if_true]
    congr 1; funext a; congr 1; ring
  · have c1 : ¬ (N * P ≤ A * P + r ∧ A * P + r < (N + N) * P) := fun h =>
      hin ⟨(block_le hr).mp h.1, (block_lt hr).mp h.2⟩
    simp only [c1, hin, decide_false, if_false, Bool.false_eq_true]
    split_ifs <;> rfl

/-- (d) colour change: `(x + idₙ) ∘ C⁰(f) ∘ (x + idₙ) = C¹(f)`. -/
theorem colour_change (hact : LocalAct act) {n : Nat} (f : Circ G n) (v : Vec R) :
    den act (par x (Circ.id n)) (den act (ctrl false f) (den act (par x (Circ.id n)) v)) =
      den act (ctrl true f) v := by
  funext i
  have hp : (0 : Nat) < 2 ^ n := by positivity
  rw [den_par_x_id]
  by_cases hlo : i < 2 ^ n
  · rw [if_pos hlo, den_ctrl_out (by simp [inHalf]), den_par_x_id, if_neg (by omega),
      if_pos (by omega), den_ctrl_out (by simp [inHalf]; omega)]
    congr 1; omega
  · rw [if_neg hlo]
    by_cases hhi : i < 2 ^ n + 2 ^ n
    · rw [if_pos hhi, den_ctrl_in (by simp [inHalf]; omega),
        den_ctrl_in (by simp [inHalf, two_pow_succ']; omega)]
      simp only [ctrlOff, Bool.false_eq_true, if_false, if_true, Nat.sub_zero, Nat.zero_add]
      apply den_local hact _ _ _ _ _ (by omega)
      intro j hj
      rw [den_par_x_id, if_pos hj]
    · rw [if_neg hhi, den_ctrl_out (by simp [inHalf]; omega), den_par_x_id, if_neg hlo,
        if_neg hhi, den_ctrl_out (by simp [inHalf, two_pow_succ']; omega)]

/-- (e) complementarity: `C⁰(f) ∘ C¹(f) = id₁ + f`. -/
theorem complementarity (hact : LocalAct act) {n : Nat} (f : Circ G n) (v : Vec R) :
    den act (ctrl false f) (den act (ctrl true f) v) = den act (par (Circ.id 1) f) v := by
  funext i
  have hp : (0 : Nat) < 2 ^ n := by positivity
  have h2 : 2 ^ (1 + n) = 2 ^ n + 2 ^ n := by rw [Nat.add_comm, two_pow_succ']
  rw [den_par]
  by_cases hlo : i < 2 ^ n
  · rw [den_ctrl_in (by simp [inHalf]; omega), if_pos (by omega)]
    simp only [den_id, Nat.div_eq_of_lt hlo, Nat.mod_eq_of_lt hlo, ctrlOff]
    simp only [Bool.false_eq_true, if_false, Nat.sub_zero, Nat.zero_mul, Nat.zero_add]
    apply den_local hact _ _ _ _ _ hlo
    intro j hj
    rw [den_ctrl_out (by simp [inHalf]; omega)]
  · by_cases hhi : i < 2 ^ n + 2 ^ n
    · have hd : i / 2 ^ n = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have hm : i % 2 ^ n = i - 2 ^ n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [den_ctrl_out (by simp [inHalf]; omega), den_ctrl_in (by simp [inHalf, two_pow_succ']; omega),
        if_pos (by omega)]
      simp only [den_id, hd, hm, ctrlOff, if_true, Nat.one_mul]
    · rw [den_ctrl_out (by simp [inHalf]; omega),
        den_ctrl_out (by simp [inHalf, two_pow_succ']; omega), if_neg (by omega)]

/-- (f) commutativity: `C⁰(f₁) ∘ C¹(f₂) = C¹(f₂) ∘ C⁰(f₁)`. -/
theorem ctrl_comm (hact : LocalAct act) {n : Nat} (f₁ f₂ : Circ G n) (v : Vec R) :
    den act (ctrl false f₁) (den act (ctrl true f₂) v) =
      den act (ctrl true f₂) (den act (ctrl false f₁) v) := by
  funext i
  rw [den_ctrl (b := false) f₁, den_ctrl (b := true) f₂ (den act (ctrl false f₁) v)]
  by_cases h1 : inHalf false n i = true
  · have h2 : inHalf true n i = false := by
      simp [inHalf] at h1 ⊢; omega
    rw [if_pos h1, if_neg (by simp [h2]), den_ctrl_in h1]
    apply den_local hact
    · intro j hj
      rw [den_ctrl_out (by simp [inHalf, ctrlOff]; omega)]
    · simp [inHalf, ctrlOff] at h1 ⊢; omega
  · rw [if_neg h1]
    by_cases h2 : inHalf true n i = true
    · rw [if_pos h2, den_ctrl_in h2]
      symm
      apply den_local hact
      · intro j hj
        rw [den_ctrl_out (by simp [inHalf, ctrlOff])]
      · rw [inHalf_true_iff] at h2; omega
    · rw [if_neg h2, den_ctrl_out (by simpa using h2), den_ctrl_out (by simpa using h1)]

/-- (g) swap: `C¹(x) ∘ σ ∘ C¹(x) ∘ σ ∘ C¹(x) = σ`. -/
theorem swap_eq_cnots (v : Vec R) :
    den act (ctrl true (x (G := G)))
        (den act (swap (G := G)) (den act (ctrl true (x (G := G)))
          (den act (swap (G := G)) (den act (ctrl true (x (G := G))) v)))) =
      den act (swap (G := G)) v := by
  funext i
  rcases Nat.lt_or_ge i 4 with h | h
  · interval_cases i <;> simp [den, inHalf, ctrlOff]
  · have h1 : ∀ w : Vec R, den act (ctrl true (x (G := G))) w i = w i := fun w =>
      den_ctrl_out (by simp [inHalf]; omega) _ _
    have h2 : ∀ w : Vec R, den act (swap (G := G)) w i = w i := fun w =>
      den_out act _ _ _ (by simpa using h)
    simp only [h1, h2]

/-- (h) swap coherence: `(σ + idₙ) ∘ C¹(C¹(f)) = C¹(C¹(f)) ∘ (σ + idₙ)`. -/
theorem swap_ctrl_ctrl (hact : LocalAct act) {n : Nat} (f : Circ G n) (v : Vec R) :
    den act (par swap (Circ.id n)) (den act (ctrl true (ctrl true f)) v) =
      den act (ctrl true (ctrl true f)) (den act (par swap (Circ.id n)) v) := by
  funext i
  have hP : (0 : Nat) < 2 ^ n := by positivity
  rw [den_par_swap_id n (den act (ctrl true (ctrl true f)) v) i,
    den_ctrl_ctrl f (den act (par swap (Circ.id n)) v) i]
  simp only [den_ctrl_ctrl f v]
  by_cases h3 : 3 * 2 ^ n ≤ i ∧ i < 4 * 2 ^ n
  · rw [if_neg (by omega), if_neg (by omega), if_pos h3, if_pos h3]
    apply den_local hact _ _ _ _ _ (by omega)
    intro j hj
    rw [den_par_swap_id, if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h3, den_par_swap_id]
    split_ifs <;> first | (exfalso; omega) | rfl

end Qrig

end
