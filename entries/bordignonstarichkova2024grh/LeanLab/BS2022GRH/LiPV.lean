module

public import Mathlib

/-!
P0021, Bordignon-Starichkova 2022, arXiv 2211.08844 v1: the shared input
`li(y) ≤ ∫₂^y dt / log t + 1.046`, INPUTS.md, the item below the cut.

The paper's `li` is the principal value logarithmic integral
`li x = lim_{ε → 0+} (∫₀^{1-ε} dt / log t + ∫_{1+ε}^x dt / log t)`.
Here it is defined exactly that way, `liPV`, as a limit along `𝓝[>] 0`, and the limit is
proved to exist for every `x > 1`:

* `liPV_eq`: `li x = ∫₀ˣ g + log (x - 1)` with `g t = 1 / log t - 1 / (t - 1)`, a bounded
  integrand, `0 ≤ g ≤ 1` on `[0, ∞)`, `gli_bounds`.
* `liPV_two_le`: `0 ≤ li 2 ≤ 2`.
* `liPV_eq_add`: `li y = li 2 + ∫₂^y dt / log t` for `y ≥ 2`.
* `liPV_le`: `li y ≤ ∫₂^y dt / log t + 2` for `y ≥ 2`.

The true value is `li 2 = 1.04516...`, so the paper's form with `1.046` is also true, but
that numerical bound is NOT proved here; the weaker `+ 2` is what is proved, and it is
enough for the Section 5.4 margin, see `li_factor_le` in Thm7Factor.lean, where the `li`
constant enters multiplied by `log y / y ≤ 8·10⁻⁷`.

AI-written Lean code, Claude, run 20261019T0202Z-9877, unit U-0997. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH
open Real MeasureTheory Filter Topology Set intervalIntegral

/-- The regular part of `1 / log t`: `g t = 1 / log t - 1 / (t - 1)`. With Lean's
conventions `g 0 = 1` and `g 1 = 0`. -/
noncomputable def gli (t : ℝ) : ℝ := 1 / log t - 1 / (t - 1)

/-- `0 ≤ g t ≤ 1` for every `t ≥ 0`, from `1 - 1/t ≤ log t ≤ t - 1`. -/
lemma gli_bounds {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gli t ∧ gli t ≤ 1 := by
  unfold gli
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0; norm_num
  have h1 : log t ≤ t - 1 := log_le_sub_one_of_pos hpos
  have h2' : 1 - t⁻¹ ≤ log t := one_sub_inv_le_log_of_pos hpos
  have ht0 : t ≠ 0 := hpos.ne'
  have e : 1 - t⁻¹ = (t - 1) / t := by field_simp
  rw [e] at h2'
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · have hL : log t < 0 := log_neg hpos hlt
    have hs : t - 1 < 0 := by linarith
    have hs' : t - 1 ≠ 0 := hs.ne
    have a1 : 1 / (t - 1) ≤ 1 / log t := one_div_le_one_div_of_neg_of_le hs h1
    have a2 : 1 / log t ≤ 1 / ((t - 1) / t) := one_div_le_one_div_of_neg_of_le hL h2'
    have e2 : 1 / ((t - 1) / t) = 1 + 1 / (t - 1) := by field_simp; ring
    rw [e2] at a2
    constructor <;> linarith
  · subst heq; norm_num
  · have hL : 0 < log t := log_pos hgt
    have hs : 0 < t - 1 := by linarith
    have hs' : t - 1 ≠ 0 := hs.ne'
    have a1 : 1 / (t - 1) ≤ 1 / log t := one_div_le_one_div_of_le hL h1
    have a2 : 1 / log t ≤ 1 / ((t - 1) / t) := one_div_le_one_div_of_le (div_pos hs hpos) h2'
    have e2 : 1 / ((t - 1) / t) = 1 + 1 / (t - 1) := by field_simp; ring
    rw [e2] at a2
    constructor <;> linarith

lemma measurable_gli : Measurable gli := by
  unfold gli
  exact (measurable_const.div Real.measurable_log).sub
    (measurable_const.div (measurable_id.sub_const 1))

lemma gli_integrableOn {x : ℝ} : IntegrableOn gli (Icc 0 x) := by
  refine Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
    measurable_gli.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  obtain ⟨h0, h1⟩ := gli_bounds ht.1
  rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1

lemma gli_integrableOn_uIcc {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntegrableOn gli (uIcc a b) := by
  refine (gli_integrableOn (x := max a b)).mono_set ?_
  intro t ht
  rw [mem_uIcc] at ht
  constructor
  · rcases ht with h | h <;> linarith [h.1]
  · rcases ht with h | h <;> linarith [h.2, le_max_left a b, le_max_right a b]

lemma gli_ii {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : IntervalIntegrable gli volume a b :=
  (gli_integrableOn_uIcc ha hb).intervalIntegrable

/-- `1 / (t - 1)` is interval integrable on any interval avoiding `1`. -/
lemma inv_sub_one_ii {a b : ℝ} (h : (1 : ℝ) ∉ uIcc a b) :
    IntervalIntegrable (fun t : ℝ => 1 / (t - 1)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  refine continuousOn_const.div (continuousOn_id.sub continuousOn_const) (fun t ht => ?_)
  intro h0
  have h1 : t = 1 := sub_eq_zero.mp h0
  exact h (h1 ▸ ht)

/-- `∫ₐᵇ dt / (t - 1) = log ((b - 1) / (a - 1))` when `1 ∉ [a, b]`. -/
lemma integral_inv_sub_one {a b : ℝ} (h : (1 : ℝ) ∉ uIcc a b) :
    ∫ t in a..b, 1 / (t - 1) = log ((b - 1) / (a - 1)) := by
  have hc := intervalIntegral.integral_comp_sub_right (fun x : ℝ => 1 / x) (a := a) (b := b) 1
  rw [hc, integral_one_div]
  intro h0
  apply h
  rw [mem_uIcc] at h0 ⊢
  rcases h0 with h0 | h0
  · left; constructor <;> linarith [h0.1, h0.2]
  · right; constructor <;> linarith [h0.1, h0.2]

/-- `1 / log t = g t + 1 / (t - 1)` for every `t`. -/
lemma inv_log_eq (t : ℝ) : 1 / log t = gli t + 1 / (t - 1) := by
  unfold gli; ring

/-- The truncated principal value integral. -/
noncomputable def liPart (x e : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1 - e, 1 / log t) + ∫ t in 1 + e..x, 1 / log t

/-- **The principal value logarithmic integral**,
`li x = lim_{ε → 0+} (∫₀^{1-ε} + ∫_{1+ε}^x) dt / log t`. -/
noncomputable def liPV (x : ℝ) : ℝ := limUnder (𝓝[>] (0 : ℝ)) (liPart x)

/-- For `0 < e < 1` and `1 + e ≤ x` the truncated integral splits into regular parts. -/
lemma liPart_eq {x e : ℝ} (he : 0 < e) (he1 : e < 1) (hex : 1 + e ≤ x) :
    liPart x e = (∫ t in (0 : ℝ)..1 - e, gli t) + (∫ t in 1 + e..x, gli t) + log (x - 1) := by
  have hn1 : (1 : ℝ) ∉ uIcc 0 (1 - e) := by
    intro h; rw [mem_uIcc] at h
    rcases h with h | h <;> linarith [h.1, h.2]
  have hn2 : (1 : ℝ) ∉ uIcc (1 + e) x := by
    intro h; rw [mem_uIcc] at h
    rcases h with h | h <;> linarith [h.1, h.2]
  have hf : (fun t : ℝ => 1 / log t) = fun t => gli t + 1 / (t - 1) := funext inv_log_eq
  unfold liPart
  rw [hf, integral_add (gli_ii le_rfl (by linarith)) (inv_sub_one_ii hn1),
    integral_add (gli_ii (by linarith) (by linarith)) (inv_sub_one_ii hn2),
    integral_inv_sub_one hn1, integral_inv_sub_one hn2]
  have e1 : (1 - e - 1) / (0 - 1 : ℝ) = e := by ring
  have e2 : (1 + e - 1 : ℝ) = e := by ring
  rw [e1, e2, log_div (by linarith) he.ne']
  ring

/-- **The principal value exists**: for `x > 1` the truncated integrals tend to
`∫₀ˣ g + log (x - 1)`. -/
theorem tendsto_liPart {x : ℝ} (hx : 1 < x) :
    Tendsto (liPart x) (𝓝[>] 0) (𝓝 ((∫ t in (0 : ℝ)..x, gli t) + log (x - 1))) := by
  -- the two regular primitives
  have hF := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := 1)
    (gli_integrableOn_uIcc le_rfl zero_le_one)
  have hG := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) (a := 1) (b := x)
    (gli_integrableOn_uIcc zero_le_one (by linarith))
  have hev1 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 1 - e ∈ uIcc (0 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with e he
    rw [mem_uIcc]; left; constructor <;> linarith [he.1, he.2]
  have hev2 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 1 + e ∈ uIcc (1 : ℝ) x := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < x - 1 by linarith)] with e he
    rw [mem_uIcc]; left; constructor <;> linarith [he.1, he.2]
  have ht1 : Tendsto (fun e : ℝ => 1 - e) (𝓝[>] 0) (𝓝[uIcc 0 1] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hev1⟩
    have : Tendsto (fun e : ℝ => 1 - e) (𝓝 0) (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (fun e : ℝ => 1 + e) (𝓝[>] 0) (𝓝[uIcc 1 x] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hev2⟩
    have : Tendsto (fun e : ℝ => 1 + e) (𝓝 0) (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun e : ℝ => ∫ t in (0 : ℝ)..1 - e, gli t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, gli t)) :=
    (hF 1 right_mem_uIcc).tendsto.comp ht1
  have hB : Tendsto (fun e : ℝ => ∫ t in 1 + e..x, gli t) (𝓝[>] 0)
      (𝓝 (∫ t in (1 : ℝ)..x, gli t)) :=
    (hG 1 left_mem_uIcc).tendsto.comp ht2
  have hsum := (hA.add hB).add_const (log (x - 1))
  rw [integral_add_adjacent_intervals (gli_ii le_rfl zero_le_one)
    (gli_ii zero_le_one (by linarith))] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (x - 1) by
    simp only [lt_min_iff]; constructor <;> linarith)] with e he
  have he1 : e < 1 := lt_of_lt_of_le he.2 (min_le_left _ _)
  have he2 : e < x - 1 := lt_of_lt_of_le he.2 (min_le_right _ _)
  rw [liPart_eq he.1 he1 (by linarith)]

/-- `li x = ∫₀ˣ g + log (x - 1)` for `x > 1`. -/
theorem liPV_eq {x : ℝ} (hx : 1 < x) :
    liPV x = (∫ t in (0 : ℝ)..x, gli t) + log (x - 1) :=
  (tendsto_liPart hx).limUnder_eq

theorem liPV_two : liPV 2 = ∫ t in (0 : ℝ)..2, gli t := by
  rw [liPV_eq (by norm_num)]; norm_num

/-- `0 ≤ li 2 ≤ 2`. The true value is `1.04516...`; only this crude bound is proved. -/
theorem liPV_two_le : 0 ≤ liPV 2 ∧ liPV 2 ≤ 2 := by
  rw [liPV_two]
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht; exact (gli_bounds ht.1).1
  · have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 2 by norm_num)
      (gli_ii le_rfl (by norm_num)) (intervalIntegrable_const (c := (1 : ℝ)))
      (fun t ht => (gli_bounds ht.1).2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith

/-- `li y = li 2 + ∫₂^y dt / log t` for `y ≥ 2`. -/
theorem liPV_eq_add {y : ℝ} (hy : 2 ≤ y) :
    liPV y = liPV 2 + ∫ t in (2 : ℝ)..y, 1 / log t := by
  have hn : (1 : ℝ) ∉ uIcc 2 y := by
    intro h; rw [mem_uIcc] at h
    rcases h with h | h <;> linarith [h.1, h.2]
  have hf : (fun t : ℝ => 1 / log t) = fun t => gli t + 1 / (t - 1) := funext inv_log_eq
  rw [liPV_eq (by linarith), liPV_two, hf,
    integral_add (gli_ii (by norm_num) (by linarith)) (inv_sub_one_ii hn),
    integral_inv_sub_one hn,
    ← integral_add_adjacent_intervals (gli_ii (a := 0) (b := 2) le_rfl (by norm_num))
      (gli_ii (a := 2) (b := y) (by norm_num) (by linarith))]
  rw [show ((y - 1) / (2 - 1) : ℝ) = y - 1 by ring]
  ring

/-- **The shared input, weak form, PROVED**: `li y ≤ ∫₂^y dt / log t + 2` for `y ≥ 2`, `li` the
principal value logarithmic integral. -/
theorem liPV_le {y : ℝ} (hy : 2 ≤ y) : liPV y ≤ (∫ t in (2 : ℝ)..y, 1 / log t) + 2 := by
  rw [liPV_eq_add hy]; linarith [liPV_two_le.2]


end LeanLab.BS2022GRH
