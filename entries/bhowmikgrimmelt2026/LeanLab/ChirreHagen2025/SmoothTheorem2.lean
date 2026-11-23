module

public import Mathlib
public import LeanLab.ChirreHagen2025.SmoothY
public import LeanLab.ChirreHagen2025.Local36

/-!
P0075 line, T2, unit U-6356, I-5170, CLOUD 20261020T1125Z-cloud41, 2026-10-20.
Chirre-Hagen's Theorem 2 with 1.2913 in place of 2.2258, from named zero inputs:
* `ExplicitA`: the explicit formula as the paper writes it, `A_δ(y) = 𝒱(δ, y) - B_δ(y)` is
  the limit of `-Σ_{ρ ∈ Z_n} c_ρ y^ρ`, `c_ρ = ((1+δ)^ρ - 1)/ρ`, along truncations `Z_n`, for
  almost every `y ≥ 2`; under RH every `ρ = 1/2 + iγ`.
* `HadamardK`: `Σ_γ' 4/(4 + (γ - γ')²) ≤ log |γ|`, the analogue at `α = 5/2` of the paper's
  Lemma 2.2 part 1, for finite partial sums.
* `Lemma26`: the paper's Lemma 2.6 for both signs of `γ`, so with `1/Real.pi` for `1/(2Real.pi)`.
* `CoefBound`: the paper's Lemma 2.5, `|c_ρ| ≤ min(δ, ℓ/|γ|)`.
* `Ordinates14`: every `|γ| ≥ 14`.
The proof: the finite smoothed mean square `interval_P_le` for each truncation, Fatou, the
diagonal with `HadamardK`, the split at `T = ℓ/δ` with `Lemma26`, and `B_δ ≤ δ` on `y ≥ 2`;
the range `[1, 2]` by `Local36.small_range`.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.SmoothT2
open Complex MeasureTheory Set Filter Topology
open LeanLab.ChirreHagen2025.SmoothKernel
open LeanLab.ChirreHagen2025.Local36 (V ell small_range V_sq_ii log_ell_bounds)

/-- `B_δ(y) = -(1/2)(log(1 - ((1+δ)y)^-2) - log(1 - y^-2))`. -/
noncomputable def Bf (δ y : ℝ) : ℝ :=
  -(1 / 2) * (Real.log (1 - (((1 + δ) * y) ^ 2)⁻¹) - Real.log (1 - (y ^ 2)⁻¹))

variable {ι : Type*}

/-- `ρ = 1/2 + iγ`. -/
noncomputable def rho (γ : ι → ℝ) (i : ι) : ℂ := 1 / 2 + (γ i : ℂ) * I

/-- `c_ρ = ((1+δ)^ρ - 1)/ρ`. -/
noncomputable def cδ (γ : ι → ℝ) (δ : ℝ) (i : ι) : ℂ :=
  (((1 + δ : ℝ) : ℂ) ^ rho γ i - 1) / rho γ i

/-- The explicit formula, cited: MV (12.1) at `y` and `(1+δ)y`, as the paper's display for
`A_δ`, along truncations `Z n`, for almost every `y ≥ 2`. -/
def ExplicitA (γ : ι → ℝ) (Z : ℕ → Finset ι) (δ : ℝ) : Prop :=
  ∀ᵐ y ∂volume, 2 ≤ y →
    Tendsto (fun n => P (Z n) (cδ γ δ) γ y) atTop (𝓝 (-((V δ y - Bf δ y : ℝ) : ℂ)))

/-- Cited: `Σ_γ' 4/(4 + (γ - γ')²) ≤ log |γ|` over every finite set of zeros. -/
def HadamardK (γ : ι → ℝ) : Prop :=
  ∀ (s : Finset ι) (i : ι), ∑ j ∈ s, K (γ i - γ j) ≤ Real.log |γ i|

/-- Cited, the paper's Lemma 2.6 summed over both signs of the ordinates. -/
def Lemma26 (γ : ι → ℝ) : Prop :=
  ∀ T : ℝ, 10 ^ 13 ≤ T → ∀ s : Finset ι,
    (∑ i ∈ s.filter (fun i => |γ i| ≤ T), Real.log |γ i|) ≤ T * Real.log T ^ 2 / Real.pi ∧
    (∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), Real.log |γ i| / γ i ^ 2)
      ≤ 1.028 * Real.log T ^ 2 / (Real.pi * T)

/-- The paper's Lemma 2.5. -/
def CoefBound (γ : ι → ℝ) (δ : ℝ) : Prop := ∀ i, ‖cδ γ δ i‖ ≤ min δ (ell δ / |γ i|)

/-- Every ordinate has `|γ| ≥ 14`. -/
def Ordinates14 (γ : ι → ℝ) : Prop := ∀ i, 14 ≤ |γ i|

/-- The diagonal: `Σ_i |c_i|² Σ_j K(γ_i - γ_j) ≤ 1.29117 δ log²(ℓ/δ)`. -/
theorem diag_bound {γ : ι → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13)
    (hH : HadamardK γ) (h14 : Ordinates14 γ) (hC : CoefBound γ δ) (hL : Lemma26 γ)
    (s : Finset ι) :
    ∑ i ∈ s, ‖cδ γ δ i‖ ^ 2 * ∑ j ∈ s, K (γ i - γ j)
      ≤ 1.29117 * δ * Real.log (ell δ / δ) ^ 2 := by
  set ℓ := ell δ with hℓ
  have hs1 : 1 ≤ √(1 + δ) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + δ by linarith)
    simpa using this
  have hs : √(1 + δ) ≤ 1.0001 := by
    rw [show (1.0001 : ℝ) = √(1.0001 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hl2 : 2 ≤ ℓ := by rw [hℓ]; unfold ell; linarith
  have hl : ℓ ≤ 2.0001 := by rw [hℓ]; unfold ell; linarith
  set T := ℓ / δ with hT
  have hTpos : 0 < T := by positivity
  have hT13 : 10 ^ 13 ≤ T := by
    rw [hT, le_div_iff₀ hδ]; rw [le_div_iff₀ (by norm_num)] at hδ1; nlinarith
  have hlogpos : ∀ i, 0 ≤ Real.log |γ i| := fun i =>
    Real.log_nonneg (by linarith [h14 i])
  -- step 1: Hadamard
  have st1 : ∑ i ∈ s, ‖cδ γ δ i‖ ^ 2 * ∑ j ∈ s, K (γ i - γ j)
      ≤ ∑ i ∈ s, ‖cδ γ δ i‖ ^ 2 * Real.log |γ i| :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hH s i) (sq_nonneg _)
  -- step 2: the two coefficient bounds, split at T
  have hc1 : ∀ i, ‖cδ γ δ i‖ ^ 2 ≤ δ ^ 2 := fun i =>
    pow_le_pow_left₀ (norm_nonneg _) ((hC i).trans (min_le_left _ _)) 2
  have hc2 : ∀ i, ‖cδ γ δ i‖ ^ 2 ≤ ℓ ^ 2 / γ i ^ 2 := by
    intro i
    have h := (hC i).trans (min_le_right _ _)
    have hg : 0 < |γ i| := by linarith [h14 i]
    calc ‖cδ γ δ i‖ ^ 2 ≤ (ℓ / |γ i|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = ℓ ^ 2 / γ i ^ 2 := by rw [div_pow, sq_abs]
  have hsp := (Finset.sum_filter_add_sum_filter_not s (fun i => |γ i| ≤ T)
    (fun i => ‖cδ γ δ i‖ ^ 2 * Real.log |γ i|)).symm
  have p1 : ∑ i ∈ s.filter (fun i => |γ i| ≤ T), ‖cδ γ δ i‖ ^ 2 * Real.log |γ i|
      ≤ δ ^ 2 * ∑ i ∈ s.filter (fun i => |γ i| ≤ T), Real.log |γ i| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc1 i) (hlogpos i)
  have p2 : ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), ‖cδ γ δ i‖ ^ 2 * Real.log |γ i|
      ≤ ℓ ^ 2 * ∑ i ∈ s.filter (fun i => ¬ |γ i| ≤ T), Real.log |γ i| / γ i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_right (hc2 i) (hlogpos i)
    calc _ ≤ ℓ ^ 2 / γ i ^ 2 * Real.log |γ i| := this
      _ = ℓ ^ 2 * (Real.log |γ i| / γ i ^ 2) := by ring
  obtain ⟨q1, q2⟩ := hL T hT13 s
  set L := Real.log T with hLdef
  have hpi : (3.1415 : ℝ) ≤ Real.pi := le_of_lt (lt_trans (by norm_num) Real.pi_gt_d6)
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have r1 : δ ^ 2 * (T * L ^ 2 / Real.pi) = δ * ℓ * L ^ 2 / Real.pi := by
    rw [hT]; field_simp
  have r2 : ℓ ^ 2 * (1.028 * L ^ 2 / (Real.pi * T)) = 1.028 * (δ * ℓ * L ^ 2 / Real.pi) := by
    rw [hT]; field_simp
  have k1 := mul_le_mul_of_nonneg_left q1 (sq_nonneg δ)
  have k2 := mul_le_mul_of_nonneg_left q2 (sq_nonneg ℓ)
  have hfin : (1 + 1.028) * (δ * ℓ * L ^ 2 / Real.pi) ≤ 1.29117 * δ * L ^ 2 := by
    have hd : 0 ≤ δ * L ^ 2 := by positivity
    have e : (1 + 1.028) * (δ * ℓ * L ^ 2 / Real.pi) = (2.028 * ℓ / Real.pi) * (δ * L ^ 2) := by ring
    rw [e]
    have : 2.028 * ℓ / Real.pi ≤ 1.29117 := by
      rw [div_le_iff₀ hpi0]; nlinarith
    nlinarith
  linarith

/-- `0 ≤ -B_δ(y) ≤ δ` for `y ≥ 2` and `0 < δ ≤ 1`, so `B_δ(y)² ≤ δ²`. -/
theorem Bf_sq_le {δ y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hy : 2 ≤ y) : Bf δ y ^ 2 ≤ δ ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hy2 : 4 ≤ y ^ 2 := by nlinarith
  have hky : y ≤ (1 + δ) * y := by nlinarith
  have hk2 : y ^ 2 ≤ ((1 + δ) * y) ^ 2 := by nlinarith
  set a := 1 - (((1 + δ) * y) ^ 2)⁻¹ with ha
  set b := 1 - (y ^ 2)⁻¹ with hb
  have hinv : (y ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hy2
  have hinv2 : (((1 + δ) * y) ^ 2)⁻¹ ≤ (y ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) hk2
  have hb0 : 3 / 4 ≤ b := by rw [hb]; linarith
  have hab : b ≤ a := by rw [ha, hb]; linarith
  have hdiff : a - b ≤ 2 * δ * (y ^ 2)⁻¹ := by
    rw [ha, hb]
    have e : (((1 + δ) * y) ^ 2)⁻¹ = (y ^ 2)⁻¹ * ((1 + δ) ^ 2)⁻¹ := by
      rw [mul_pow, mul_inv, mul_comm]
    rw [e]
    have hk : 1 - 2 * δ ≤ ((1 + δ) ^ 2)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg δ]
    have hy20 : 0 ≤ (y ^ 2)⁻¹ := by positivity
    nlinarith
  have hlog0 : 0 ≤ Real.log a - Real.log b := by
    have := Real.log_le_log (by linarith) hab; linarith
  have hlog1 : Real.log a - Real.log b ≤ a / b - 1 := by
    rw [← Real.log_div (by linarith) (by linarith)]
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
  have hq : a / b - 1 ≤ 2 * δ := by
    rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  have hB : Bf δ y = -(1 / 2) * (Real.log a - Real.log b) := rfl
  rw [hB]
  have h1 : 0 ≤ (1 / 2) * (Real.log a - Real.log b) := by linarith
  have h2 : (1 / 2) * (Real.log a - Real.log b) ≤ δ := by linarith
  nlinarith

theorem measurable_V (δ : ℝ) (hδ : 0 ≤ δ) : Measurable (V δ) := by
  have hm : Monotone (fun t : ℝ => Chebyshev.psi t) := fun a b h => Chebyshev.psi_mono h
  have h1 : Measurable (fun y : ℝ => Chebyshev.psi ((1 + δ) * y)) :=
    hm.measurable.comp (measurable_const.mul measurable_id)
  unfold V
  exact (h1.sub hm.measurable).sub (measurable_const.mul measurable_id)

theorem measurable_Bf (δ : ℝ) : Measurable (Bf δ) := by
  unfold Bf; fun_prop

theorem measurable_P (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) : Measurable (P s c γ) := by
  unfold P
  refine Finset.measurable_sum _ fun i _ => ?_
  exact measurable_const.mul (Complex.measurable_ofReal.pow_const _)

/-- Fatou: `∫_2^x A_δ² ≤ x² · 1.29117 δ log²(ℓ/δ)`. -/
theorem A_sq_le {γ : ι → ℝ} {Z : ℕ → Finset ι} {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10 ^ 13)
    (hx : 2 ≤ x) (hE : ExplicitA γ Z δ) (hH : HadamardK γ) (h14 : Ordinates14 γ)
    (hC : CoefBound γ δ) (hL : Lemma26 γ) :
    ∫ y in Ioc 2 x, (V δ y - Bf δ y) ^ 2
      ≤ x ^ 2 * (1.29117 * δ * Real.log (ell δ / δ) ^ 2) := by
  set M := x ^ 2 * (1.29117 * δ * Real.log (ell δ / δ) ^ 2) with hM
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
    have m3 := diag_bound hδ hδ1 hH h14 hC hL (Z n)
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

/-- Theorem 2 with the constant 1.2913, from the cited zero inputs. -/
theorem theorem2_smooth {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ) (hH : HadamardK γ)
    (h14 : Ordinates14 γ) (hC : ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → CoefBound γ δ)
    (hL : Lemma26 γ) :
    ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.2913 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2 := by
  intro x δ hx hδ hδ1
  have hδ1' : δ ≤ 1 := by linarith [show (1 / 10 ^ 13 : ℝ) ≤ 1 by norm_num]
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  set η : ℝ := 1 / 10 ^ 5 with hη
  obtain ⟨hl1, hl2⟩ := log_ell_bounds hδ hδ1
  set L := Real.log (ell δ / δ) with hL'
  set L2 := Real.log (2.0001 / δ) with hL2'
  have hA := A_sq_le hδ hδ1 hx2 (hE δ hδ hδ1) hH h14 (hC δ hδ hδ1) hL
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
      ≤ (1 + η) * (x ^ 2 * (1.29117 * δ * L ^ 2)) + (1 + 1 / η) * (δ ^ 2 * x) := by
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
  have k1 : (1 + η) * (x ^ 2 * (1.29117 * δ * L ^ 2))
      ≤ (1 + η) * 1.29117 * δ * L2 ^ 2 * x ^ 2 := by
    have : 0 ≤ (1 + η) * 1.29117 * δ * x ^ 2 := by positivity
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
  have hfin : (1 + η) * 1.29117 * δ * L2 ^ 2 * x ^ 2 + 100001 * δ * (x ^ 2 / 10 ^ 26)
      + 4 * 10 ^ 9 * δ * (x ^ 2 / 10 ^ 26) ≤ 1.2913 * δ * L2 ^ 2 * x ^ 2 := by
    have hd : 0 ≤ δ * x ^ 2 := by positivity
    have e : (1 + η) * 1.29117 * δ * L2 ^ 2 * x ^ 2 + 100001 * δ * (x ^ 2 / 10 ^ 26)
        + 4 * 10 ^ 9 * δ * (x ^ 2 / 10 ^ 26)
        = (1 + η) * 1.29117 * (δ * x ^ 2) * L2 ^ 2 + (100001 + 4 * 10 ^ 9) / 10 ^ 26 * (δ * x ^ 2) := by
      ring
    rw [e, hη]
    have : (100001 + 4 * 10 ^ 9) / 10 ^ 26 * (δ * x ^ 2)
        ≤ (1.2913 - (1 + 1 / 10 ^ 5) * 1.29117) * (δ * x ^ 2) * L2 ^ 2 := by
      have hc : (100001 + 4 * 10 ^ 9 : ℝ) / 10 ^ 26 ≤ 1.2913 - (1 + 1 / 10 ^ 5) * 1.29117 := by
        norm_num
      have := mul_le_mul_of_nonneg_right hc hd
      have h3 : 0 ≤ (1.2913 - (1 + 1 / 10 ^ 5) * 1.29117 : ℝ) * (δ * x ^ 2) :=
        mul_nonneg (by norm_num) hd
      nlinarith
    nlinarith
  linarith

end LeanLab.ChirreHagen2025.SmoothT2

