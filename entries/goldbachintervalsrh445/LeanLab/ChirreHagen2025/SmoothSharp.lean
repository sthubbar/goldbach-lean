module

public import Mathlib
public import LeanLab.ChirreHagen2025.SmoothTheorem2

/-!
P0075 line, T2, unit U-6361, I-5171, CLOUD 20261020T1125Z-cloud41, 2026-10-20.
The sharp diagonal: with the exact `|c_ρ|²` in place of Lemma 2.5's `min(δ, ℓ/|γ|)²`, the lab
derives `Σ_γ |c_γ|² log |γ| ≤ δ log²(2.0001/δ)` for `0 < δ ≤ 10^-13` from the density of zeros
and Trudgian's bound for `N(T)`; that bound is the named input `ZeroSumSharp`, CLAIMED by
numerics in gen/sharp_U6360, NOT a literature statement and NOT proved here. From it,
`J_ψ(x, δ) ≤ 1.0001 δ log²(2.0001/δ) x²`, by the proof of SmoothTheorem2.lean with
`diag_sharp` for `diag_bound`, made by a script.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.SmoothT2
open Complex MeasureTheory Set Filter Topology
open LeanLab.ChirreHagen2025.SmoothKernel
open LeanLab.ChirreHagen2025.Local36 (V ell small_range V_sq_ii log_ell_bounds)

variable {ι : Type*}

/-- Lab-derived, CLAIMED: the exact coefficients summed against `log |γ|`. -/
def ZeroSumSharp (γ : ι → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ∀ s : Finset ι,
    ∑ i ∈ s, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| ≤ δ * Real.log (2.0001 / δ) ^ 2

theorem diag_sharp {γ : ι → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13)
    (hH : HadamardK γ) (h14 : Ordinates14 γ) (hZ : ZeroSumSharp γ) (s : Finset ι) :
    ∑ i ∈ s, ‖cδ γ δ i‖ ^ 2 * ∑ j ∈ s, K (γ i - γ j) ≤ δ * Real.log (2.0001 / δ) ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hZ δ hδ hδ1 s)
  exact mul_le_mul_of_nonneg_left (hH s i) (sq_nonneg _)

/-- Fatou with the sharp diagonal: `∫_2^x A_δ² ≤ x² δ log²(2.0001/δ)`. -/
theorem A_sq_le_sharp {γ : ι → ℝ} {Z : ℕ → Finset ι} {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13)
    (hx : 2 ≤ x) (hE : ExplicitA γ Z δ) (hH : HadamardK γ) (h14 : Ordinates14 γ)
    (hZ : ZeroSumSharp γ) :
    ∫ y in Ioc 2 x, (V δ y - Bf δ y) ^ 2
      ≤ x ^ 2 * (δ * Real.log (2.0001 / δ) ^ 2) := by
  set M := x ^ 2 * (δ * Real.log (2.0001 / δ) ^ 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hx0 : 0 < x := by linarith
  set μ := volume.restrict (Ioc (2 : ℝ) x)
  set g : ℝ → ℝ := fun y => V δ y - Bf δ y with hg
  set f : ℕ → ℝ → ENNReal := fun n y => ENNReal.ofReal (‖P (Z n) (cδ γ δ) γ y‖ ^ 2) with hf
  -- each truncation
  have hn : ∀ n, ∫⁻ y, f n y ∂μ ≤ ENNReal.ofReal M := by
    intro n
    have hI := integrableOn_P_W (Z n) (cδ γ δ) γ hx0
    have hsub : Ioc (2 : ℝ) x ⊆ Ioi 0 := fun y hy => lt_trans (by norm_num) hy.1
    have hIoc : IntegrableOn (fun y => ‖P (Z n) (cδ γ δ) γ y‖ ^ 2) (Ioc 2 x) := by
      refine (hI.mono_set hsub).congr_fun (fun y hy => ?_) measurableSet_Ioc
      have : y / x ≤ 1 := (div_le_one hx0).mpr hy.2
      simp [W, this]
    rw [hf, ← ofReal_integral_eq_lintegral_ofReal hIoc
      (Filter.Eventually.of_forall fun y => sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hIoc1 : IntegrableOn (fun y => ‖P (Z n) (cδ γ δ) γ y‖ ^ 2) (Ioc 1 x) := by
      refine (hI.mono_set (fun y hy => lt_trans one_pos hy.1)).congr_fun (fun y hy => ?_)
        measurableSet_Ioc
      have : y / x ≤ 1 := (div_le_one hx0).mpr hy.2
      simp [W, this]
    have m1 : ∫ y in Ioc 2 x, ‖P (Z n) (cδ γ δ) γ y‖ ^ 2
        ≤ ∫ y in Ioc 1 x, ‖P (Z n) (cδ γ δ) γ y‖ ^ 2 :=
      setIntegral_mono_set hIoc1 (Filter.Eventually.of_forall fun y => sq_nonneg _)
        (Filter.Eventually.of_forall (Ioc_subset_Ioc_left (by norm_num)))
    have m2 := interval_P_le (Z n) (cδ γ δ) γ (show (1 : ℝ) ≤ x by linarith)
    rw [intervalIntegral.integral_of_le (by linarith)] at m2
    have m3 := diag_sharp hδ hδ1 hH h14 hZ (Z n)
    have m4 := mul_le_mul_of_nonneg_left m3 (sq_nonneg x)
    linarith
  -- a.e. convergence on μ
  have hae : ∀ᵐ y ∂μ, Tendsto (fun n => f n y) atTop (𝓝 (ENNReal.ofReal (g y ^ 2))) := by
    have h1 : ∀ᵐ y ∂μ, y ∈ Ioc (2 : ℝ) x := ae_restrict_mem measurableSet_Ioc
    have h2 : ∀ᵐ y ∂μ, 2 ≤ y →
        Tendsto (fun n => P (Z n) (cδ γ δ) γ y) atTop (𝓝 (-((V δ y - Bf δ y : ℝ) : ℂ))) :=
      ae_restrict_of_ae hE
    filter_upwards [h1, h2] with y hy hT
    have ht := hT hy.1.le
    have hn := (continuous_norm.tendsto _).comp ht
    have hsq := ((continuous_pow 2).tendsto _).comp hn
    have hof := (ENNReal.continuous_ofReal.tendsto _).comp hsq
    have e : ‖-((V δ y - Bf δ y : ℝ) : ℂ)‖ ^ 2 = g y ^ 2 := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [e] at hof
    exact hof
  have hmeas : ∀ n, Measurable (f n) := fun n =>
    ENNReal.measurable_ofReal.comp ((measurable_P _ _ _).norm.pow_const 2)
  have hlim : ∫⁻ y, ENNReal.ofReal (g y ^ 2) ∂μ ≤ ENNReal.ofReal M := by
    calc ∫⁻ y, ENNReal.ofReal (g y ^ 2) ∂μ = ∫⁻ y, liminf (fun n => f n y) atTop ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with y hy
          exact hy.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ y, f n y ∂μ) atTop := lintegral_liminf_le hmeas
      _ ≤ ENNReal.ofReal M := by
          refine liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
          obtain ⟨n, hn'⟩ := hb.exists
          exact hn'.trans (hn n)
  have hgm : AEStronglyMeasurable (fun y => g y ^ 2) μ :=
    (((measurable_V δ hδ.le).sub (measurable_Bf δ)).pow_const 2).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => sq_nonneg _) hgm]
  exact ENNReal.toReal_le_of_le_ofReal hM0 hlim

/-- Theorem 2 with the constant 1.0001, CONDITIONAL ON ExplicitA, HadamardK, Ordinates14 and
the lab-derived ZeroSumSharp. -/
theorem theorem2_sharp {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ) (hH : HadamardK γ)
    (h14 : Ordinates14 γ) (hZ : ZeroSumSharp γ) :
    ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0001 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2 := by
  intro x δ hx hδ hδ1
  have hδ1' : δ ≤ 1 := by linarith [show (1 / 10 ^ 13 : ℝ) ≤ 1 by norm_num]
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  set η : ℝ := 1 / 10 ^ 5 with hη
  obtain ⟨hl1, hl2⟩ := log_ell_bounds hδ hδ1
  set L := Real.log (ell δ / δ) with hL'
  set L2 := Real.log (2.0001 / δ) with hL2'
  have hA := A_sq_le_sharp hδ hδ1 hx2 (hE δ hδ hδ1) hH h14 hZ
  rw [← hL2'] at hA
  -- integrability on [2, x]
  have iV : IntegrableOn (fun y => V δ y ^ 2) (Ioc 2 x) := by
    have := V_sq_ii hδ (show (0 : ℝ) ≤ 2 by norm_num) hx2
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hx2] at this
  have hBb : ∀ y ∈ Ioc (2 : ℝ) x, Bf δ y ^ 2 ≤ δ ^ 2 := fun y hy => Bf_sq_le hδ hδ1' hy.1.le
  have iB : IntegrableOn (fun y => Bf δ y ^ 2) (Ioc 2 x) := by
    refine Measure.integrableOn_of_bounded (M := δ ^ 2) measure_Ioc_lt_top.ne
      ((measurable_Bf δ).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hBb y hy
  have iG : IntegrableOn (fun y => (V δ y - Bf δ y) ^ 2) (Ioc 2 x) := by
    refine Integrable.mono' ((iV.const_mul 2).add (iB.const_mul 2))
      (((measurable_V δ hδ.le).sub (measurable_Bf δ)).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (V δ y + Bf δ y)]
  -- pointwise (u + b)² ≤ (1+η)u² + (1+1/η)b²
  have hpt : ∀ y, V δ y ^ 2 ≤ (1 + η) * (V δ y - Bf δ y) ^ 2 + (1 + 1 / η) * Bf δ y ^ 2 := by
    intro y
    have := sq_nonneg (η * (V δ y - Bf δ y) - Bf δ y)
    have hη0 : 0 < η := by norm_num
    have e : V δ y = (V δ y - Bf δ y) + Bf δ y := by ring
    rw [e]
    set u := V δ y - Bf δ y
    set b := Bf δ y
    simp only [add_sub_cancel_right]
    rw [show (1 + 1 / η) * b ^ 2 = b ^ 2 + b ^ 2 / η by ring]
    have : 2 * u * b ≤ η * u ^ 2 + b ^ 2 / η := by
      have key : η * u ^ 2 + b ^ 2 / η - 2 * u * b = (η * u - b) ^ 2 / η := by
        field_simp; ring
      have : 0 ≤ (η * u - b) ^ 2 / η := by positivity
      linarith
    nlinarith
  have hupper : ∫ y in Ioc 2 x, V δ y ^ 2
      ≤ (1 + η) * (x ^ 2 * (δ * L2 ^ 2)) + (1 + 1 / η) * (δ ^ 2 * x) := by
    have s1 : ∫ y in Ioc 2 x, V δ y ^ 2
        ≤ ∫ y in Ioc 2 x, ((1 + η) * (V δ y - Bf δ y) ^ 2 + (1 + 1 / η) * Bf δ y ^ 2) :=
      setIntegral_mono_on iV ((iG.const_mul _).add (iB.const_mul _)) measurableSet_Ioc
        (fun y _ => hpt y)
    rw [integral_add (iG.const_mul _) (iB.const_mul _), integral_const_mul,
      integral_const_mul] at s1
    have s2 : ∫ y in Ioc 2 x, Bf δ y ^ 2 ≤ δ ^ 2 * x := by
      have := setIntegral_mono_on iB (integrableOn_const (C := δ ^ 2) measure_Ioc_lt_top.ne)
        measurableSet_Ioc hBb
      rw [setIntegral_const, Real.volume_real_Ioc_of_le hx2, smul_eq_mul] at this
      nlinarith [sq_nonneg δ]
    have hη1 : (0 : ℝ) ≤ 1 + η := by norm_num
    have hη2 : (0 : ℝ) ≤ 1 + 1 / η := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left hA hη1, mul_le_mul_of_nonneg_left s2 hη2]
  have hsmall := small_range (Y := 2) (by norm_num) (by norm_num) hδ hδ1'
  -- assemble
  have hsplit : Jpsi x δ = (∫ y in (1 : ℝ)..2, V δ y ^ 2) + ∫ y in Ioc 2 x, V δ y ^ 2 := by
    unfold Jpsi
    show (∫ y in (1 : ℝ)..x, V δ y ^ 2) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (V_sq_ii hδ (by norm_num) (by norm_num : (1 : ℝ) ≤ 2))
      (V_sq_ii hδ (by norm_num) hx2), intervalIntegral.integral_of_le hx2]
  rw [hsplit]
  have hLL : L ^ 2 ≤ L2 ^ 2 := by nlinarith
  have hL21 : 1 ≤ L2 ^ 2 := by nlinarith
  have hxx : (10 : ℝ) ^ 26 ≤ x ^ 2 := by nlinarith
  have hdx : δ * x ≤ x / 10 ^ 13 := by
    rw [le_div_iff₀ (by norm_num)]; rw [le_div_iff₀ (by norm_num)] at hδ1; nlinarith
  have hxle : x ≤ x ^ 2 / 10 ^ 13 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
  have k1 : (1 + η) * (x ^ 2 * (δ * L2 ^ 2))
      ≤ (1 + η) * 1 * δ * L2 ^ 2 * x ^ 2 := by
    have : 0 ≤ (1 + η) * 1 * δ * x ^ 2 := by positivity
    nlinarith
  have k2 : (1 + 1 / η) * (δ ^ 2 * x) ≤ 100001 * δ * (x ^ 2 / 10 ^ 26) := by
    have e : (1 + 1 / η) * (δ ^ 2 * x) = 100001 * δ * (δ * x) := by rw [hη]; ring
    rw [e]
    have : δ * x ≤ x ^ 2 / 10 ^ 26 := by
      calc δ * x ≤ x / 10 ^ 13 := hdx
        _ ≤ x ^ 2 / 10 ^ 13 / 10 ^ 13 := div_le_div_of_nonneg_right hxle (by norm_num)
        _ = x ^ 2 / 10 ^ 26 := by ring
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have k3 : 4 * 10 ^ 9 * δ ≤ 4 * 10 ^ 9 * δ * (x ^ 2 / 10 ^ 26) := by
    have : 1 ≤ x ^ 2 / 10 ^ 26 := by rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith
  have hfin : (1 + η) * 1 * δ * L2 ^ 2 * x ^ 2 + 100001 * δ * (x ^ 2 / 10 ^ 26)
      + 4 * 10 ^ 9 * δ * (x ^ 2 / 10 ^ 26) ≤ 1.0001 * δ * L2 ^ 2 * x ^ 2 := by
    have hd : 0 ≤ δ * x ^ 2 := by positivity
    have e : (1 + η) * 1 * δ * L2 ^ 2 * x ^ 2 + 100001 * δ * (x ^ 2 / 10 ^ 26)
        + 4 * 10 ^ 9 * δ * (x ^ 2 / 10 ^ 26)
        = (1 + η) * 1 * (δ * x ^ 2) * L2 ^ 2 + (100001 + 4 * 10 ^ 9) / 10 ^ 26 * (δ * x ^ 2) := by
      ring
    rw [e, hη]
    have : (100001 + 4 * 10 ^ 9) / 10 ^ 26 * (δ * x ^ 2)
        ≤ (1.0001 - (1 + 1 / 10 ^ 5) * 1) * (δ * x ^ 2) * L2 ^ 2 := by
      have hc : (100001 + 4 * 10 ^ 9 : ℝ) / 10 ^ 26 ≤ 1.0001 - (1 + 1 / 10 ^ 5) * 1 := by
        norm_num
      have := mul_le_mul_of_nonneg_right hc hd
      have h3 : 0 ≤ (1.0001 - (1 + 1 / 10 ^ 5) * 1 : ℝ) * (δ * x ^ 2) :=
        mul_nonneg (by norm_num) hd
      nlinarith
    nlinarith
  linarith

end LeanLab.ChirreHagen2025.SmoothT2

