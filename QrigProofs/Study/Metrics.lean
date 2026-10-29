module

public import Mathlib

/-!
# The metrics of the qrig study (`report/qrig_results.md`)

The report compares *Qiskit alone* with *qrig + Qiskit* using a handful of scalar metrics.
This file defines them exactly as the report does and proves the properties the report's
reasoning relies on.

* `esp` — estimated success probability `ESP = ∏ (1 - e_g)` over the gates of a compiled
  circuit.  `esp_sublist_le`: removing gates never lowers it.
* `espUniform` — the same quantity on a target with one error rate per gate kind (the
  depolarizing target of the study).  `espUniform_robust`: if one compilation uses no
  more one- and two-qubit gates than another, its ESP is at least as high **at every
  noise strength** — the ESP form of the noise-strength robustness of Section 8.2.
  `espUniform_tradeoff_not_robust` shows that both counts are needed.
* `errorRemoved`, `fidelityRatio`, `shotSaving`, `shotsNeeded` — how a change of fidelity
  is reported, and why the shot saving is the square of the fidelity ratio.
* `geomean` — the per-circuit geometric mean of Section 4.1; `geomean_le_one`: if qrig
  never increases a circuit's gate count, the geometric mean ratio is at most `1`.

These are statements about the metrics, not about any particular simulation result: the
numbers in the report come from classical simulation and are not checked in Lean.
-/

@[expose] public section

namespace Qrig.Study

/-! ## Estimated success probability -/

/-- Estimated success probability of a compiled circuit whose gates have error rates
`errs`: `ESP = ∏ (1 - e)`. -/
noncomputable def esp (errs : List ℝ) : ℝ := (errs.map fun e => 1 - e).prod

theorem esp_nil : esp [] = 1 := rfl

theorem esp_cons (e : ℝ) (errs : List ℝ) : esp (e :: errs) = (1 - e) * esp errs := by
  simp [esp]

theorem esp_append (l₁ l₂ : List ℝ) : esp (l₁ ++ l₂) = esp l₁ * esp l₂ := by
  simp [esp]

theorem esp_nonneg {errs : List ℝ} (h : ∀ e ∈ errs, 0 ≤ e ∧ e ≤ 1) : 0 ≤ esp errs := by
  induction errs with
  | nil => simp [esp]
  | cons e l ih =>
    rw [esp_cons]
    have he := h e (by simp)
    exact mul_nonneg (by linarith [he.2]) (ih fun x hx => h x (by simp [hx]))

theorem esp_le_one {errs : List ℝ} (h : ∀ e ∈ errs, 0 ≤ e ∧ e ≤ 1) : esp errs ≤ 1 := by
  induction errs with
  | nil => simp [esp]
  | cons e l ih =>
    rw [esp_cons]
    have he := h e (by simp)
    have h1 := ih fun x hx => h x (by simp [hx])
    have h0 := esp_nonneg fun x hx => h x (List.mem_cons_of_mem e hx)
    nlinarith [he.1, he.2]

/-- **Removing gates never lowers the ESP.**  If the gates of one compilation are a
sub-list of the gates of another (every error rate in `[0, 1]`), its ESP is at least as
high. -/
theorem esp_sublist_le {l₁ l₂ : List ℝ} (hs : l₁.Sublist l₂)
    (h : ∀ e ∈ l₂, 0 ≤ e ∧ e ≤ 1) : esp l₂ ≤ esp l₁ := by
  induction hs with
  | slnil => exact le_rfl
  | cons a hs ih =>
    rename_i l₁ l₂
    rw [esp_cons]
    have ha := h a (by simp)
    have h1 := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    have h0 := esp_nonneg fun x hx => h x (List.mem_cons_of_mem a hx)
    nlinarith [ha.1, ha.2]
  | cons₂ a hs ih =>
    rw [esp_cons, esp_cons]
    have ha := h a (by simp)
    exact mul_le_mul_of_nonneg_left (ih fun x hx => h x (List.mem_cons_of_mem a hx))
      (by linarith [ha.2])

/-- ESP on a target with one error rate per gate kind: `n₁` one-qubit gates with error
`p₁` and `n₂` two-qubit gates with error `p₂`. -/
noncomputable def espUniform (p₁ p₂ : ℝ) (n₁ n₂ : ℕ) : ℝ := (1 - p₁) ^ n₁ * (1 - p₂) ^ n₂

theorem espUniform_eq_esp (p₁ p₂ : ℝ) (n₁ n₂ : ℕ) :
    espUniform p₁ p₂ n₁ n₂ = esp (List.replicate n₁ p₁ ++ List.replicate n₂ p₂) := by
  simp [espUniform, esp, List.map_replicate, List.prod_replicate]

/-- Fewer gates of each kind give an ESP at least as high. -/
theorem espUniform_anti {p₁ p₂ : ℝ} (h₁ : 0 ≤ p₁ ∧ p₁ ≤ 1) (h₂ : 0 ≤ p₂ ∧ p₂ ≤ 1)
    {m₁ m₂ n₁ n₂ : ℕ} (hm₁ : m₁ ≤ n₁) (hm₂ : m₂ ≤ n₂) :
    espUniform p₁ p₂ n₁ n₂ ≤ espUniform p₁ p₂ m₁ m₂ := by
  unfold espUniform
  have a : (1 - p₁) ^ n₁ ≤ (1 - p₁) ^ m₁ :=
    pow_le_pow_of_le_one (by linarith [h₁.2]) (by linarith [h₁.1]) hm₁
  have b : (1 - p₂) ^ n₂ ≤ (1 - p₂) ^ m₂ :=
    pow_le_pow_of_le_one (by linarith [h₂.2]) (by linarith [h₂.1]) hm₂
  exact mul_le_mul a b (pow_nonneg (by linarith [h₂.2]) _) (pow_nonneg (by linarith [h₁.2]) _)

/-- Strictly fewer two-qubit gates (and no more one-qubit gates) give a strictly higher
ESP whenever the two-qubit error rate lies strictly between `0` and `1` and the one-qubit
error rate is below `1`. -/
theorem espUniform_strictAnti {p₁ p₂ : ℝ} (h₁ : 0 ≤ p₁ ∧ p₁ < 1) (h₂ : 0 < p₂ ∧ p₂ < 1)
    {m₁ m₂ n₁ n₂ : ℕ} (hm₁ : m₁ ≤ n₁) (hm₂ : m₂ < n₂) :
    espUniform p₁ p₂ n₁ n₂ < espUniform p₁ p₂ m₁ m₂ := by
  unfold espUniform
  have a : (1 - p₁) ^ n₁ ≤ (1 - p₁) ^ m₁ :=
    pow_le_pow_of_le_one (by linarith [h₁.2]) (by linarith [h₁.1]) hm₁
  have b : (1 - p₂) ^ n₂ < (1 - p₂) ^ m₂ :=
    pow_lt_pow_right_of_lt_one₀ (by linarith [h₂.2]) (by linarith [h₂.1]) hm₂
  exact mul_lt_mul' a b (pow_nonneg (by linarith [h₂.2]) _) (pow_pos (by linarith [h₁.2]) _)

/-- **Robustness across noise strength (ESP model).**  If a compilation uses no more one-
and two-qubit gates than another, then for *every* scale factor `s` of the error rates
(as long as the scaled rates stay in `[0, 1]`) its ESP is at least as high.  The
advantage cannot be reversed by making the device noisier or cleaner. -/
theorem espUniform_robust {p₁ p₂ : ℝ} (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
    {m₁ m₂ n₁ n₂ : ℕ} (hm₁ : m₁ ≤ n₁) (hm₂ : m₂ ≤ n₂) :
    ∀ s : ℝ, 0 ≤ s → s * p₁ ≤ 1 → s * p₂ ≤ 1 →
      espUniform (s * p₁) (s * p₂) n₁ n₂ ≤ espUniform (s * p₁) (s * p₂) m₁ m₂ :=
  fun _ hs h₁ h₂ =>
    espUniform_anti ⟨mul_nonneg hs hp₁, h₁⟩ ⟨mul_nonneg hs hp₂, h₂⟩ hm₁ hm₂

/-- The robustness statement needs *both* counts to be no larger: trading two-qubit gates
for one-qubit gates can make the ESP comparison depend on the noise.  Compilation `A` has
one two-qubit gate, `B` has three one-qubit gates; with `p₁ = p₂ / 2`, `A` has the higher
ESP at `p₂ = 1/10` and the lower ESP at `p₂ = 9/10`. -/
theorem espUniform_tradeoff_not_robust :
    espUniform (1 / 20) (1 / 10) 3 0 < espUniform (1 / 20) (1 / 10) 0 1 ∧
    espUniform (9 / 20) (9 / 10) 0 1 < espUniform (9 / 20) (9 / 10) 3 0 := by
  unfold espUniform
  norm_num

/-! ## Reporting a change of fidelity -/

/-- Share of the error removed by qrig: `1 - (1 - F_qrig) / (1 - F_Qiskit)`. -/
noncomputable def errorRemoved (fQiskit fQrig : ℝ) : ℝ := 1 - (1 - fQrig) / (1 - fQiskit)

/-- Fidelity ratio `F_qrig / F_Qiskit`. -/
noncomputable def fidelityRatio (fQiskit fQrig : ℝ) : ℝ := fQrig / fQiskit

/-- Shot saving `(F_qrig / F_Qiskit)²`. -/
noncomputable def shotSaving (fQiskit fQrig : ℝ) : ℝ := fidelityRatio fQiskit fQrig ^ 2

/-- Shots needed to estimate a signal damped by the fidelity `F` to precision `ε`, up to
the constant `c` of the estimator: `c / (F² ε²)`. -/
noncomputable def shotsNeeded (c ε F : ℝ) : ℝ := c / (F ^ 2 * ε ^ 2)

theorem errorRemoved_eq {fQiskit fQrig : ℝ} (h : fQiskit < 1) :
    errorRemoved fQiskit fQrig = (fQrig - fQiskit) / (1 - fQiskit) := by
  have : (1 - fQiskit) ≠ 0 := by linarith
  unfold errorRemoved
  field_simp
  ring

theorem errorRemoved_pos_iff {fQiskit fQrig : ℝ} (h : fQiskit < 1) :
    0 < errorRemoved fQiskit fQrig ↔ fQiskit < fQrig := by
  rw [errorRemoved_eq h, div_pos_iff_of_pos_right (by linarith), sub_pos]

theorem errorRemoved_eq_zero_iff {fQiskit fQrig : ℝ} (h : fQiskit < 1) :
    errorRemoved fQiskit fQrig = 0 ↔ fQrig = fQiskit := by
  rw [errorRemoved_eq h, div_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro (h' | h')
    · exact h'
    · exact absurd h' (by linarith)
  · exact Or.inl

theorem errorRemoved_eq_one_iff {fQiskit fQrig : ℝ} (h : fQiskit < 1) :
    errorRemoved fQiskit fQrig = 1 ↔ fQrig = 1 := by
  rw [errorRemoved_eq h, div_eq_one_iff_eq (by linarith)]
  constructor <;> intro h' <;> linarith

theorem errorRemoved_le_one {fQiskit fQrig : ℝ} (h : fQiskit < 1) (h' : fQrig ≤ 1) :
    errorRemoved fQiskit fQrig ≤ 1 := by
  rw [errorRemoved_eq h, div_le_one (by linarith)]
  linarith

theorem one_le_fidelityRatio_iff {fQiskit fQrig : ℝ} (h : 0 < fQiskit) :
    1 ≤ fidelityRatio fQiskit fQrig ↔ fQiskit ≤ fQrig := by
  rw [fidelityRatio, one_le_div h]

theorem one_le_shotSaving_iff {fQiskit fQrig : ℝ} (h : 0 < fQiskit) (h' : 0 ≤ fQrig) :
    1 ≤ shotSaving fQiskit fQrig ↔ fQiskit ≤ fQrig := by
  rw [shotSaving, ← one_le_fidelityRatio_iff h]
  have hr : 0 ≤ fidelityRatio fQiskit fQrig := div_nonneg h' h.le
  constructor
  · intro h2
    by_contra hc
    push_neg at hc
    nlinarith
  · intro h1
    nlinarith

/-- The shot saving is exactly the ratio of the shots needed without and with qrig. -/
theorem shotsNeeded_div {c ε fQiskit fQrig : ℝ} (hc : c ≠ 0) (hε : ε ≠ 0)
    (h : fQiskit ≠ 0) (h' : fQrig ≠ 0) :
    shotsNeeded c ε fQiskit / shotsNeeded c ε fQrig = shotSaving fQiskit fQrig := by
  unfold shotsNeeded shotSaving fidelityRatio
  field_simp

/-! ## Per-circuit geometric mean -/

/-- Geometric mean of a list of positive numbers, `exp (mean (log x))`. -/
noncomputable def geomean (xs : List ℝ) : ℝ := Real.exp ((xs.map Real.log).sum / xs.length)

theorem sum_log_nonpos {xs : List ℝ} (h : ∀ x ∈ xs, 0 < x ∧ x ≤ 1) :
    (xs.map Real.log).sum ≤ 0 := by
  induction xs with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := h x (by simp)
    have := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    linarith [Real.log_nonpos hx.1.le hx.2]

/-- If qrig never increases the gate count of any circuit (every ratio in `(0, 1]`), the
geometric mean of the ratios is at most `1`. -/
theorem geomean_le_one {xs : List ℝ} (h : ∀ x ∈ xs, 0 < x ∧ x ≤ 1) : geomean xs ≤ 1 := by
  unfold geomean
  rw [Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (sum_log_nonpos h) (Nat.cast_nonneg _)

/-- … and strictly below `1` as soon as one circuit improves. -/
theorem geomean_lt_one {xs : List ℝ} (h : ∀ x ∈ xs, 0 < x ∧ x ≤ 1) (h' : ∃ x ∈ xs, x < 1) :
    geomean xs < 1 := by
  obtain ⟨x, hx, hx1⟩ := h'
  unfold geomean
  rw [Real.exp_lt_one_iff]
  have hlen : (0 : ℝ) < xs.length := by
    exact_mod_cast List.length_pos_of_mem hx
  apply div_neg_of_neg_of_pos _ hlen
  have hneg : Real.log x < 0 := Real.log_neg (h x hx).1 hx1
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
  have a := sum_log_nonpos (xs := l₁) fun y hy => h y (by simp [hy])
  have b := sum_log_nonpos (xs := l₂) fun y hy => h y (by simp [hy])
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  linarith

end Qrig.Study
