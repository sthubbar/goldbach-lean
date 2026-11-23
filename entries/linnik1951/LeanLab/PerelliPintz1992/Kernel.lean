module

public import LeanLab.PerelliPintz1992.Orthogonality

/-!
P0070 Perelli-Pintz 1992, Section 3, p. 359, the step to (5): the mean square over `k` of
`∫_𝔪 |S|² e(-2kα)` is controlled by the kernel `K(x) = Σ_{k=V}^{V+H} e(2kx)`.

* `kernel_le`: `|K(x)| ≤ H + 1`.
* `abs_sin_pi_ge`: `|sin(π y)| ≥ 2 |y - j|` for the nearest integer `j`, Jordan's inequality.
* `kernel_far`: `|K(x)| ≤ 1/(4δ)` when `x` is at distance `≥ δ` from every half integer.
* `mean_square_kernel`: for any continuous `g ≥ 0`, bounded measurable `𝔪`, `δ > 0` and `B` with
  `∫_{𝔪 ∩ near(ξ, δ)} g ≤ B` for every `ξ ∈ 𝔪`:
  `Σ_{k=V}^{V+H} |∫_𝔪 g(α) e(-2kα) dα|² ≤ T ((H + 1) B + T/(4δ))`, `T = ∫_𝔪 g`.
* `eq5`: the case `g = |S|²`, the paper's (5) with explicit constants; with `T ≪ N L`
  and `δ = L^{A+2}/H` it is (5).

KNOWN mathematics. AI-written Lean code, Claude, PC run 20261020T0403Z-27388, unit U-1157.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.PerelliPintz1992
open Real ArithmeticFunction MeasureTheory Set

/-- The kernel `K(x) = Σ_{k=V}^{V+H} e(2kx)`. -/
noncomputable def Kk (V H : ℕ) (x : ℝ) : ℂ := ∑ k ∈ Finset.Icc V (V + H), e (2 * k * x)

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [show (2 * π * Complex.I * x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_Kk (V H : ℕ) : Continuous (Kk V H) := by
  unfold Kk
  exact continuous_finsetSum _ fun k _ => continuous_e.comp (continuous_const.mul continuous_id)

lemma kernel_le (V H : ℕ) (x : ℝ) : ‖Kk V H x‖ ≤ H + 1 := by
  unfold Kk
  calc ‖∑ k ∈ Finset.Icc V (V + H), e (2 * k * x)‖
      ≤ ∑ k ∈ Finset.Icc V (V + H), ‖e (2 * k * x)‖ := norm_sum_le _ _
    _ = H + 1 := by
        rw [Finset.sum_congr rfl (fun k _ => norm_e _), Finset.sum_const, nsmul_eq_mul, mul_one]
        have hc : (Finset.Icc V (V + H)).card = H + 1 := by rw [Nat.card_Icc]; omega
        rw [hc]; push_cast; ring

/-- Jordan: `2 |t| ≤ |sin(π t)|` for `|t| ≤ 1/2`. -/
lemma two_abs_le_abs_sin {t : ℝ} (ht : |t| ≤ 1 / 2) : 2 * |t| ≤ |sin (π * t)| := by
  have h0 : 0 ≤ π * |t| := mul_nonneg pi_pos.le (abs_nonneg t)
  have h1 : π * |t| ≤ π / 2 := by nlinarith [pi_pos]
  have hj := Real.mul_le_sin h0 h1
  have e1 : 2 / π * (π * |t|) = 2 * |t| := by field_simp
  rw [e1] at hj
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at hj ⊢
    calc 2 * t ≤ sin (π * t) := hj
      _ ≤ |sin (π * t)| := le_abs_self _
  · rw [abs_of_nonpos h] at hj ⊢
    have : sin (π * -t) = - sin (π * t) := by rw [mul_neg, Real.sin_neg]
    rw [this] at hj
    calc 2 * -t ≤ - sin (π * t) := hj
      _ ≤ |sin (π * t)| := neg_le_abs _

/-- `|sin(π y)| ≥ 2 |y - j|` for `j = round y`. -/
lemma abs_sin_pi_ge (y : ℝ) : 2 * |y - round y| ≤ |sin (π * y)| := by
  have ht : |y - round y| ≤ 1 / 2 := abs_sub_round y
  have h := two_abs_le_abs_sin ht
  have e1 : sin (π * y) = (-1) ^ (round y) * sin (π * (y - round y)) := by
    rw [← Real.sin_add_int_mul_pi]; congr 1; ring
  rw [e1, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  exact h

/-- `‖e(x) - 1‖ = 2 |sin(π x)|`. -/
lemma norm_e_sub_one (x : ℝ) : ‖e x - 1‖ = 2 * |sin (π * x)| := by
  unfold e
  rw [show (2 * π * Complex.I * x : ℂ) = Complex.I * ((2 * π * x : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [show 2 * π * x / 2 = π * x by ring]
  norm_num

/-- **The far bound**: if `|x - j/2| ≥ δ` for every integer `j`, then `|K(x)| ≤ 1/(4δ)`. -/
lemma kernel_far (V H : ℕ) {x δ : ℝ} (hδ : 0 < δ) (hfar : ∀ j : ℤ, δ ≤ |x - j / 2|) :
    ‖Kk V H x‖ ≤ 1 / (4 * δ) := by
  set r : ℂ := e (2 * x) with hr
  have hsin : 4 * δ ≤ |sin (π * (2 * x))| := by
    have h1 := abs_sin_pi_ge (2 * x)
    have h2 := hfar (round (2 * x))
    have : |2 * x - round (2 * x)| = 2 * |x - (round (2 * x) : ℝ) / 2| := by
      rw [← abs_two, ← abs_mul, abs_two]; congr 1; ring
    linarith
  have hr1 : ‖r - 1‖ = 2 * |sin (π * (2 * x))| := norm_e_sub_one _
  have hrpos : 0 < ‖r - 1‖ := by rw [hr1]; linarith
  have hK : Kk V H x = e (2 * V * x) * ∑ i ∈ Finset.range (H + 1), r ^ i := by
    unfold Kk
    rw [Finset.mul_sum]
    have : Finset.Icc V (V + H) = (Finset.range (H + 1)).map (addLeftEmbedding V) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply]
      constructor
      · intro hk; exact ⟨k - V, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩; omega
    rw [this, Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [addLeftEmbedding_apply, hr]
    rw [← (show ∀ n : ℕ, e (n * (2 * x)) = e (2 * x) ^ n from ?_), ← e_add]
    · congr 1; push_cast; ring
    · intro n
      induction n with
      | zero => simp [e]
      | succ n ih => rw [pow_succ, ← ih, ← e_add]; congr 1; push_cast; ring
  have hgeom : (∑ i ∈ Finset.range (H + 1), r ^ i) * (r - 1) = r ^ (H + 1) - 1 :=
    geom_sum_mul r (H + 1)
  have hnum : ‖r ^ (H + 1) - 1‖ ≤ 2 := by
    calc ‖r ^ (H + 1) - 1‖ ≤ ‖r ^ (H + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hr, norm_e, one_pow, norm_one]; norm_num
  have hsum : ‖∑ i ∈ Finset.range (H + 1), r ^ i‖ * ‖r - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]; exact hnum
  rw [hK, norm_mul, norm_e, one_mul]
  have hsum' : ‖∑ i ∈ Finset.range (H + 1), r ^ i‖ ≤ 2 / ‖r - 1‖ := by
    rw [le_div_iff₀ hrpos]; exact hsum
  calc ‖∑ i ∈ Finset.range (H + 1), r ^ i‖ ≤ 2 / ‖r - 1‖ := hsum'
    _ ≤ 1 / (4 * δ) := by
        rw [hr1, div_le_div_iff₀ (by linarith) (by linarith)]
        linarith

/-- The points within `δ` of `ξ + j/2` for some integer `j`. -/
def near (ξ δ : ℝ) : Set ℝ := ⋃ j : ℤ, Ioo (ξ + j / 2 - δ) (ξ + j / 2 + δ)

lemma measurableSet_near (ξ δ : ℝ) : MeasurableSet (near ξ δ) :=
  MeasurableSet.iUnion fun _ => measurableSet_Ioo

lemma far_of_not_near {ξ δ α : ℝ} (h : α ∉ near ξ δ) : ∀ j : ℤ, δ ≤ |α - ξ - j / 2| := by
  intro j
  by_contra hlt
  push Not at hlt
  apply h
  refine mem_iUnion.mpr ⟨j, ?_⟩
  rw [abs_lt] at hlt
  constructor <;> linarith [hlt.1, hlt.2]

/-- The kernel identity: `Σ_k e(-2kξ) e(2kα) = K(α - ξ)`. -/
lemma sum_e_eq_Kk (V H : ℕ) (ξ α : ℝ) :
    ∑ k ∈ Finset.Icc V (V + H), e (-(2 * k * ξ)) * e (2 * k * α) = Kk V H (α - ξ) := by
  unfold Kk
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← e_add]; congr 1; ring

/-- **The mean square kernel bound** behind (5). -/
theorem mean_square_kernel (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    {m : Set ℝ} (hm : MeasurableSet m) {a b : ℝ} (hmb : m ⊆ Icc a b) (V H : ℕ) {δ B : ℝ}
    (hδ : 0 < δ) (hB : ∀ ξ ∈ m, ∫ α in m ∩ near ξ δ, g α ≤ B) :
    ∑ k ∈ Finset.Icc V (V + H), ‖∫ α in m, (g α : ℂ) * e (-(2 * k * α))‖ ^ 2
      ≤ (∫ α in m, g α) * ((H + 1) * B + (∫ α in m, g α) / (4 * δ)) := by
  set μ : Measure ℝ := volume.restrict m with hμ
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact lt_of_le_of_lt (measure_mono hmb) measure_Icc_lt_top
  set T := ∫ α in m, g α with hT
  -- g is bounded on [a, b]
  obtain ⟨G, hG⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hg.continuousOn
  have hgm : ∀ᵐ x ∂μ, ‖g x‖ ≤ G := by
    rw [hμ, ae_restrict_iff' hm]
    exact Filter.Eventually.of_forall fun x hx => hG x (hmb hx)
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable G hgm
  have hgCi : ∀ c : ℝ, Integrable (fun α => (g α : ℂ) * e (c * α)) μ := by
    intro c
    refine Integrable.of_bound ((Complex.continuous_ofReal.comp hg).mul
      (continuous_e.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
      (C := G) ?_
    filter_upwards [hgm] with x hx
    rw [norm_mul, norm_e, mul_one, Complex.norm_real]; exact hx
  -- each square as a double integral
  have hsq : ∀ k : ℕ, ((‖∫ α in m, (g α : ℂ) * e (-(2 * k * α))‖ ^ 2 : ℝ) : ℂ) =
      ∫ z, ((g z.1 : ℂ) * e (-(2 * k * z.1))) * ((g z.2 : ℂ) * e (2 * k * z.2)) ∂(μ.prod μ) := by
    intro k
    rw [integral_prod_mul (μ := μ) (ν := μ) (fun α : ℝ => (g α : ℂ) * e (-(2 * k * α)))
      (fun α : ℝ => (g α : ℂ) * e (2 * k * α)), Complex.ofReal_pow, ← Complex.mul_conj',
      ← integral_conj]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, Complex.conj_ofReal, conj_e]
    congr 2; ring
  have hint_k : ∀ k : ℕ, Integrable
      (fun z : ℝ × ℝ => ((g z.1 : ℂ) * e (-(2 * k * z.1))) * ((g z.2 : ℂ) * e (2 * k * z.2)))
      (μ.prod μ) := by
    intro k
    have h1 := hgCi (-(2 * k))
    have h2 := hgCi (2 * k)
    have := h1.mul_prod h2
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only; congr 3; ring
  -- the kernel form
  have hsum : ((∑ k ∈ Finset.Icc V (V + H),
      ‖∫ α in m, (g α : ℂ) * e (-(2 * k * α))‖ ^ 2 : ℝ) : ℂ) =
      ∫ z, ((g z.1 * g z.2 : ℝ) : ℂ) * Kk V H (z.2 - z.1) ∂(μ.prod μ) := by
    push_cast
    simp_rw [← Complex.ofReal_pow] at hsq ⊢
    rw [Finset.sum_congr rfl (fun k _ => hsq k), ← integral_finsetSum _ (fun k _ => hint_k k)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [← sum_e_eq_Kk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  -- integrability of the norm integrand
  have hKc : Continuous (fun z : ℝ × ℝ => g z.1 * g z.2 * ‖Kk V H (z.2 - z.1)‖) :=
    ((hg.comp continuous_fst).mul (hg.comp continuous_snd)).mul
      ((continuous_Kk V H).comp (continuous_snd.sub continuous_fst)).norm
  have hNi : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2 * ‖Kk V H (z.2 - z.1)‖) (μ.prod μ) := by
    refine Integrable.of_bound hKc.aestronglyMeasurable (C := G * G * (H + 1)) ?_
    have hprod : ∀ᵐ z ∂(μ.prod μ), z.1 ∈ m ∧ z.2 ∈ m := by
      rw [hμ, Measure.prod_restrict, ae_restrict_iff' (hm.prod hm)]
      exact Filter.Eventually.of_forall fun z hz => hz
    filter_upwards [hprod] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hg0 _) (hg0 _)) (norm_nonneg _))]
    have h1 := hG z.1 (hmb hz.1); have h2 := hG z.2 (hmb hz.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] at h1 h2
    have hk := kernel_le V H (z.2 - z.1)
    have hG0 : 0 ≤ G := le_trans (hg0 _) h1
    exact mul_le_mul (mul_le_mul h1 h2 (hg0 _) hG0) hk (norm_nonneg _) (mul_nonneg hG0 hG0)
  -- inner bound
  have hinner : ∀ ξ ∈ m, ∫ α, g α * ‖Kk V H (α - ξ)‖ ∂μ ≤ (H + 1) * B + T / (4 * δ) := by
    intro ξ hξ
    have hc : Continuous (fun α => g α * ‖Kk V H (α - ξ)‖) :=
      hg.mul ((continuous_Kk V H).comp (continuous_id.sub continuous_const)).norm
    have hbd : ∀ α, g α * ‖Kk V H (α - ξ)‖
        ≤ (H + 1) * (near ξ δ).indicator g α + (1 / (4 * δ)) * g α := by
      intro α
      by_cases hα : α ∈ near ξ δ
      · rw [indicator_of_mem hα]
        have := mul_le_mul_of_nonneg_left (kernel_le V H (α - ξ)) (hg0 α)
        have h4 : 0 ≤ (1 / (4 * δ)) * g α := mul_nonneg (by positivity) (hg0 α)
        nlinarith
      · rw [indicator_of_notMem hα, mul_zero, zero_add]
        have hf := kernel_far V H hδ (fun j => by
          have := far_of_not_near hα j; rwa [show α - ξ - j / 2 = α - ξ - (j : ℝ) / 2 by ring]
            at this)
        have := mul_le_mul_of_nonneg_left hf (hg0 α)
        linarith
    have hii : Integrable (fun α => (H + 1) * (near ξ δ).indicator g α + (1 / (4 * δ)) * g α) μ :=
      ((hgi.indicator (measurableSet_near ξ δ)).const_mul _).add (hgi.const_mul _)
    have hci : Integrable (fun α => g α * ‖Kk V H (α - ξ)‖) μ := by
      refine Integrable.of_bound hc.aestronglyMeasurable (C := G * (H + 1)) ?_
      filter_upwards [hgm] with α hα
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 _) (norm_nonneg _))]
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] at hα
      exact mul_le_mul hα (kernel_le V H _) (norm_nonneg _) (le_trans (hg0 _) hα)
    calc ∫ α, g α * ‖Kk V H (α - ξ)‖ ∂μ
        ≤ ∫ α, ((H + 1) * (near ξ δ).indicator g α + (1 / (4 * δ)) * g α) ∂μ :=
          integral_mono hci hii hbd
      _ = (H + 1) * ∫ α, (near ξ δ).indicator g α ∂μ + (1 / (4 * δ)) * ∫ α, g α ∂μ := by
          rw [integral_add ((hgi.indicator (measurableSet_near ξ δ)).const_mul _)
            (hgi.const_mul _), integral_const_mul, integral_const_mul]
      _ ≤ (H + 1) * B + T / (4 * δ) := by
          have hH : (0 : ℝ) ≤ H + 1 := by positivity
          have h1 : ∫ α, (near ξ δ).indicator g α ∂μ ≤ B := by
            rw [integral_indicator (measurableSet_near ξ δ), hμ,
              Measure.restrict_restrict (measurableSet_near ξ δ), Set.inter_comm]
            exact hB ξ hξ
          have h2 : ∫ α, g α ∂μ = T := by rw [hμ]
          have := mul_le_mul_of_nonneg_left h1 hH
          rw [h2, one_div_mul_eq_div]
          linarith
  -- assemble
  have hreal : (∑ k ∈ Finset.Icc V (V + H), ‖∫ α in m, (g α : ℂ) * e (-(2 * k * α))‖ ^ 2)
      ≤ ∫ z, g z.1 * g z.2 * ‖Kk V H (z.2 - z.1)‖ ∂(μ.prod μ) := by
    have h1 := congrArg (fun w : ℂ => ‖w‖) hsum
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    calc _ ≤ |∑ k ∈ Finset.Icc V (V + H), ‖∫ α in m, (g α : ℂ) * e (-(2 * k * α))‖ ^ 2| :=
          le_abs_self _
      _ = ‖∫ z, ((g z.1 * g z.2 : ℝ) : ℂ) * Kk V H (z.2 - z.1) ∂(μ.prod μ)‖ := h1
      _ ≤ ∫ z, ‖((g z.1 * g z.2 : ℝ) : ℂ) * Kk V H (z.2 - z.1)‖ ∂(μ.prod μ) :=
          norm_integral_le_integral_norm _
      _ = ∫ z, g z.1 * g z.2 * ‖Kk V H (z.2 - z.1)‖ ∂(μ.prod μ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (hg0 _) (hg0 _))]
  rw [integral_prod _ hNi] at hreal
  refine le_trans hreal ?_
  have hpt : ∀ᵐ ξ ∂μ, (∫ α, g ξ * g α * ‖Kk V H (α - ξ)‖ ∂μ)
      ≤ g ξ * ((H + 1) * B + T / (4 * δ)) := by
    rw [hμ, ae_restrict_iff' hm]
    refine Filter.Eventually.of_forall fun ξ hξ => ?_
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hinner ξ hξ) (hg0 ξ)
  calc ∫ ξ, ∫ α, g (ξ, α).1 * g (ξ, α).2 * ‖Kk V H ((ξ, α).2 - (ξ, α).1)‖ ∂μ ∂μ
      ≤ ∫ ξ, g ξ * ((H + 1) * B + T / (4 * δ)) ∂μ := by
        refine integral_mono_ae hNi.integral_prod_left (hgi.mul_const _) ?_
        exact hpt
    _ = T * ((H + 1) * B + T / (4 * δ)) := by rw [integral_mul_const]

/-- **(5)** with explicit constants: `Σ₁ ≤ T ((H + 1) B + T/(4δ))` for `g = |S|²`, `T = ∫_𝔪 |S|²`,
and `B` any bound for `∫_{𝔪 ∩ near(ξ, δ)} |S|²` over `ξ ∈ 𝔪`. -/
theorem eq5 (N V H : ℕ) {m : Set ℝ} (hm : MeasurableSet m) {a b : ℝ} (hmb : m ⊆ Icc a b)
    {δ B : ℝ} (hδ : 0 < δ) (hB : ∀ ξ ∈ m, ∫ α in m ∩ near ξ δ, ‖S N α‖ ^ 2 ≤ B) :
    ∑ k ∈ Finset.Icc V (V + H), ‖∫ α in m, F N k α‖ ^ 2
      ≤ (∫ α in m, ‖S N α‖ ^ 2) * ((H + 1) * B + (∫ α in m, ‖S N α‖ ^ 2) / (4 * δ)) :=
  mean_square_kernel (fun α => ‖S N α‖ ^ 2) ((continuous_S N).norm.pow 2)
    (fun _ => sq_nonneg _) hm hmb V H hδ hB

/-- Vacuity: the hypotheses of `eq5` hold, for example with `𝔪 = ∅`. -/
example (N V H : ℕ) : ∑ k ∈ Finset.Icc V (V + H), ‖∫ α in (∅ : Set ℝ), F N k α‖ ^ 2
      ≤ (∫ α in (∅ : Set ℝ), ‖S N α‖ ^ 2) * ((H + 1) * 0 + (∫ α in (∅ : Set ℝ), ‖S N α‖ ^ 2) / (4 * 1)) :=
  eq5 N V H MeasurableSet.empty (a := 0) (b := 1) (empty_subset _) one_pos (fun ξ h => absurd h (notMem_empty ξ))


end LeanLab.PerelliPintz1992
