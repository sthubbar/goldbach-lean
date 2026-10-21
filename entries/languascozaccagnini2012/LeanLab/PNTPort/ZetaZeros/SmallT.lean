module

public import LeanLab.PNTPort.ZetaZeros.RH

/-!
# `ζ'/ζ` at small heights, through the entire function `(s - 1) ζ(s)`

Lab proof, unit U-5266, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics, no
cited input except where RH is marked.

* `gζ`, `(s - 1) ζ(s)` with the value `1` at `s = 1`, is analytic everywhere, by Mathlib's
  `riemannZeta_residue_one` and the removable singularity theorem.
* `logDeriv_small`: an absolute `K` with, for `|t| ≤ 5`, `‖s - (3/2 + it)‖ ≤ 1`, `s ≠ 1`,
  `ζ s ≠ 0`: `‖ζ'/ζ(s) + 1/(s - 1) - Σ_{ρ} m(ρ)/(s - ρ)‖ ≤ K`, the sum over the zeros of `ζ`
  within `27/25` of `3/2 + it`, which number at most `K` with multiplicity.
* `logDeriv_small_RH`: assuming RH, `‖ζ'/ζ(σ + it)‖ ≤ K (1 + 1/(σ - 1/2))` for `|t| ≤ 5` and
  `1/2 < σ ≤ 3/4`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric Topology MeasureTheory

local notation "ζ" => riemannZeta

/-- `(s - 1) ζ(s)`, with the value `1` at `s = 1`. -/
noncomputable def gζ : ℂ → ℂ := Function.update (fun s => (s - 1) * ζ s) 1 1

lemma gζ_of_ne {s : ℂ} (h : s ≠ 1) : gζ s = (s - 1) * ζ s := by
  simp [gζ, Function.update_of_ne h]

lemma gζ_one : gζ 1 = 1 := by simp [gζ]

lemma gζ_eventuallyEq {s : ℂ} (h : s ≠ 1) : gζ =ᶠ[𝓝 s] fun w => (w - 1) * ζ w := by
  filter_upwards [isOpen_compl_singleton.mem_nhds h] with w hw
  exact gζ_of_ne hw

lemma gζ_analyticAt (s : ℂ) : AnalyticAt ℂ gζ s := by
  rcases eq_or_ne s 1 with rfl | h
  · apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w ≠ 1 := hw
      have hd : DifferentiableAt ℂ (fun w => (w - 1) * ζ w) w :=
        (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hw')
      exact hd.congr_of_eventuallyEq (gζ_eventuallyEq hw')
    · unfold gζ
      rw [continuousAt_update_same]
      exact riemannZeta_residue_one
  · have hA : AnalyticAt ℂ (fun w => (w - 1) * ζ w) s :=
      (analyticAt_id.sub analyticAt_const).mul (analyticAt_riemannZeta h)
    exact hA.congr (gζ_eventuallyEq h).symm

lemma gζ_eq_zero_iff {s : ℂ} : gζ s = 0 ↔ s ≠ 1 ∧ ζ s = 0 := by
  rcases eq_or_ne s 1 with rfl | h
  · simp [gζ_one]
  · rw [gζ_of_ne h, mul_eq_zero, sub_eq_zero]; simp [h]

lemma ord_gζ {s : ℂ} (h : s ≠ 1) : analyticOrderNatAt gζ s = analyticOrderNatAt ζ s := by
  have hev := gζ_eventuallyEq h
  have hz : AnalyticAt ℂ ζ s := analyticAt_riemannZeta h
  have hl : AnalyticAt ℂ (fun w : ℂ => w - 1) s := analyticAt_id.sub analyticAt_const
  have : analyticOrderAt gζ s = analyticOrderAt ζ s := by
    rw [analyticOrderAt_congr hev]
    rw [show (fun w : ℂ => (w - 1) * ζ w) = (fun w : ℂ => w - 1) * ζ from rfl,
      analyticOrderAt_mul hl hz]
    rw [show analyticOrderAt (fun w : ℂ => w - 1) s = 0 from
      analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr h)), zero_add]
  simp only [analyticOrderNatAt, this]

/-- The integral of the ported formula is at most `1 / Re s`. -/
lemma norm_zetaInt_le {s : ℂ} (hs : 0 < s.re) :
    ‖∫ (u : ℝ) in Ioi 1, (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ 1 / s.re := by
  have domBound {x : ℝ} (hu : x ∈ Ioi 1) : |Int.fract x| * ‖(x : ℂ) ^ (-s - 1)‖
      ≤ x ^ (-s.re - 1) := by
    rw [mem_Ioi] at hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [sub_re, neg_re, one_re, Int.abs_fract]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) (Int.fract_lt_one x).le
  have domIntegral : Integrable (fun x : ℝ => x ^ (-s.re - 1)) (volume.restrict (Set.Ioi 1)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hI := integral_Ioi_rpow_of_lt (a := -s.re - 1) (by linarith) one_pos
  simp only [sub_add_cancel, Real.one_rpow, neg_div_neg_eq] at hI
  simp only [Complex.norm_mul, norm_real, Real.norm_eq_abs, ← hI]
  refine integral_mono_ae (domIntegral.mono' (((measurable_fract.abs).mul
    ((Complex.measurable_ofReal.pow_const _).norm)).aestronglyMeasurable) ?_) domIntegral
    (by filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx using domBound hx)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, Real.norm_eq_abs, abs_abs, norm_norm]
  exact domBound hx

/-- `‖(s - 1) ζ(s)‖ ≤ ‖s - 1‖ + 1 + ‖s‖ ‖s - 1‖ / Re s` for `Re s > 0`, `s ≠ 1`. -/
lemma norm_gζ_le {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    ‖gζ s‖ ≤ ‖s - 1‖ + 1 + ‖s‖ * ‖s - 1‖ / s.re := by
  rw [gζ_of_ne h1, ZetaAltFormula hs h1, riemannZeta1]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have e : (s - 1) * (1 + 1 / (s - 1) - s * ∫ (u : ℝ) in Ioi 1,
      (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1)) =
      (s - 1) + 1 - s * (s - 1) * ∫ (u : ℝ) in Ioi 1,
      (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    field_simp
  rw [e]
  have hI := norm_zetaInt_le hs
  calc ‖(s - 1) + 1 - s * (s - 1) * ∫ (u : ℝ) in Ioi 1, (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1)‖
      ≤ ‖(s - 1) + 1‖ + ‖s * (s - 1) * ∫ (u : ℝ) in Ioi 1,
          (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1)‖ := norm_sub_le _ _
    _ ≤ (‖s - 1‖ + 1) + ‖s‖ * ‖s - 1‖ * (1 / s.re) := by
        gcongr
        · exact (norm_add_le _ _).trans (by rw [norm_one])
        · rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by ring

/-- The normalized shift `g z = gζ(c + 3z/2) / gζ(c)`. -/
noncomputable def gz (t : ℝ) (z : ℂ) : ℂ := gζ (aff t z) / gζ (cen t)

lemma cen_ne_one (t : ℝ) : cen t ≠ 1 := by
  intro h; have := congr_arg Complex.re h; simp [cen] at this; norm_num at this

lemma gζ_cen_ne (t : ℝ) : gζ (cen t) ≠ 0 := by
  rw [ne_eq, gζ_eq_zero_iff]; push_neg; intro _; exact zeta_cen_ne t

lemma gz_analyticAt (t : ℝ) (z : ℂ) : AnalyticAt ℂ (gz t) z := by
  unfold gz
  exact (AnalyticAt.fun_comp (gζ_analyticAt _)
    (analyticAt_const.fun_add (analyticAt_const.fun_mul analyticAt_id))).div_const

lemma gz_zero (t : ℝ) : gz t 0 = 1 := by
  have := gζ_cen_ne t
  simp [gz, aff, this]

lemma gz_finite_zeros (t : ℝ) : (SetOfZeros 1 (gz t)).Finite := by
  by_contra hinf; rw [Set.not_finite] at hinf
  have zerosSubset : SetOfZeros 1 (gz t) ⊆ Metric.closedBall (0 : ℂ) 1 := fun _ hx => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
  obtain ⟨x, hxK, hacc⟩ :=
    hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall 0 1) zerosSubset
  have hfAnalytic : AnalyticOnNhd ℂ (gz t) (Metric.ball (0 : ℂ) 2) :=
    fun z _ => gz_analyticAt t z
  have hfeq : Set.EqOn (gz t) 0 (Metric.ball (0 : ℂ) 2) := by
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hfAnalytic
      Metric.isPreconnected_ball (z₀ := x) ?_ ?_
    · simp only [Metric.mem_ball, Metric.mem_closedBall, dist_zero_right] at hxK ⊢
      linarith
    · simp only [mem_closure_iff_clusterPt, ← accPt_principal_iff_clusterPt]
      exact hacc.mono (principal_mono.mpr fun _ h => h.2)
  have h0 := hfeq (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 2))
  rw [gz_zero] at h0
  exact one_ne_zero h0

/-- The bound `B₀ = 2900 / m₀` for `gz` on `‖z‖ ≤ 29/30`, `|t| ≤ 5`. -/
noncomputable def B0 : ℝ := 2900 / m0

lemma gz_bound {t : ℝ} (ht : |t| ≤ 5) {z : ℂ} (hz : ‖z‖ ≤ 29 / 30) : ‖gz t z‖ ≤ B0 := by
  have hre := Complex.abs_re_le_norm z
  have hm := m0_pos
  have hc : m0 / 2 ≤ ‖gζ (cen t)‖ := by
    rw [gζ_of_ne (cen_ne_one t), norm_mul]
    have h1 : 1 / 2 ≤ ‖cen t - 1‖ := by
      have := Complex.abs_re_le_norm (cen t - 1)
      have e : (cen t - 1).re = 1 / 2 := by simp [cen]; norm_num
      rw [e] at this; norm_num at this; linarith
    have h2 := m0_le t
    nlinarith [norm_nonneg (ζ (cen t))]
  have hnum : ‖gζ (aff t z)‖ ≤ 1450 := by
    rcases eq_or_ne (aff t z) 1 with h1 | h1
    · rw [h1, gζ_one, norm_one]; norm_num
    have sre : 1 / 20 ≤ (aff t z).re := by
      rw [aff_re]; cases abs_cases z.re <;> linarith
    have snorm : ‖aff t z‖ ≤ 8 := by
      unfold aff cen
      calc ‖3 / 2 + I * t + 3 / 2 * z‖ ≤ ‖(3 / 2 : ℂ)‖ + ‖I * (t : ℂ)‖ + ‖(3 / 2 : ℂ) * z‖ :=
            norm_add₃_le
        _ = 3 / 2 + |t| + 3 / 2 * ‖z‖ := by
            rw [norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
            norm_num
        _ ≤ 8 := by linarith
    have s1 : ‖aff t z - 1‖ ≤ 9 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    have hb := norm_gζ_le (by linarith) h1
    have hq : ‖aff t z‖ * ‖aff t z - 1‖ / (aff t z).re ≤ 8 * 9 * 20 := by
      rw [div_le_iff₀ (by linarith)]
      have : ‖aff t z‖ * ‖aff t z - 1‖ ≤ 8 * 9 :=
        mul_le_mul snorm s1 (norm_nonneg _) (by norm_num)
      nlinarith [norm_nonneg (aff t z), norm_nonneg (aff t z - 1)]
    linarith
  unfold gz B0
  rw [norm_div, div_le_div_iff₀ (by linarith) hm]
  nlinarith [norm_nonneg (gζ (aff t z))]

lemma one_lt_B0 : 1 < B0 := by
  have hm := m0_pos
  have hm1 : m0 < 1 := by
    unfold m0
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))]
    have := norm_zeta_strict_mono_ofReal (a := 3) (b := 3 / 2) (by norm_num) (by norm_num)
    simpa using this
  unfold B0; rw [one_lt_div hm]; linarith

/-- The zeros of `ζ` other than `1` within `27/25` of `3/2 + it`. -/
def Zsm (t : ℝ) : Set ℂ := {ρ : ℂ | ζ ρ = 0 ∧ ρ ≠ 1 ∧ ‖ρ - cen t‖ ≤ 27 / 25}

lemma mem_gz_zeros_iff {t : ℝ} (z : ℂ) :
    z ∈ SetOfZeros (18 / 25) (gz t) ↔ aff t z ∈ Zsm t := by
  have hc := gζ_cen_ne t
  have hn : ‖aff t z - cen t‖ = 3 / 2 * ‖z‖ := by
    unfold aff; rw [add_sub_cancel_left, norm_mul]; norm_num
  simp only [SetOfZeros, Zsm, Set.mem_setOf_eq, gz, div_eq_zero_iff, hc, or_false, hn,
    gζ_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h3, h2, by linarith⟩
  · rintro ⟨h3, h2, h1⟩; exact ⟨by linarith, h2, h3⟩

lemma ord_gz (t : ℝ) (z : ℂ) :
    analyticOrderNatAt (gz t) z = analyticOrderNatAt gζ (aff t z) := by
  have hA : AnalyticAt ℂ (fun w => gζ (aff t w)) z :=
    AnalyticAt.fun_comp (gζ_analyticAt _)
      (analyticAt_const.fun_add (analyticAt_const.fun_mul analyticAt_id))
  have h1 : analyticOrderNatAt (gz t) z = analyticOrderNatAt (fun w => gζ (aff t w)) z :=
    analyticOrderNatAt_fun_div_const (gζ_cen_ne t) hA
  rw [h1]
  have asComp : analyticOrderAt (gζ ∘ aff t) z = analyticOrderAt gζ (aff t z) := by
    have hAff : AnalyticAt ℂ (aff t) z := by
      unfold aff; exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    apply analyticOrderAt_comp_of_deriv_ne_zero hAff
    have : deriv (aff t) z = 3 / 2 := by
      have hd : HasDerivAt (aff t) (3 / 2) z := by
        unfold aff
        simpa using ((hasDerivAt_id z).const_mul (3 / 2 : ℂ)).const_add (cen t)
      exact hd.deriv
    rw [this]; norm_num
  simp only [analyticOrderNatAt, ← asComp, Function.comp_def]

lemma deriv_gζ {s : ℂ} (h : s ≠ 1) : deriv gζ s = ζ s + (s - 1) * deriv ζ s := by
  have hd : HasDerivAt (fun w => (w - 1) * ζ w) (1 * ζ s + (s - 1) * deriv ζ s) s :=
    ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta h).hasDerivAt
  rw [(hd.congr_of_eventuallyEq (gζ_eventuallyEq h)).deriv]; ring

/-- **`ζ'/ζ` at small heights**, no RH. -/
theorem logDeriv_small : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, |t| ≤ 5 →
    ∃ hfin : (Zsm t).Finite,
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) ≤ K ∧
      ∀ s : ℂ, ‖s - cen t‖ ≤ 1 → s ≠ 1 → ζ s ≠ 0 →
        ‖deriv ζ s / ζ s + 1 / (s - 1) -
          ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ ≤ K := by
  set KF : ℝ := 16 * (18 / 25) ^ 2 / (18 / 25 - 2 / 3) ^ 3 +
    1 / (((29 / 30) ^ 2 / (17 / 20) - 17 / 20) * Real.log ((29 / 30) / (17 / 20))) with hKF
  have hlr : 0 < Real.log ((29 / 30 : ℝ) / (17 / 20)) := Real.log_pos (by norm_num)
  have hKF0 : 0 < KF := by rw [hKF]; positivity
  have hlB : 0 < Real.log B0 := Real.log_pos one_lt_B0
  have hl2 : 0 < Real.log ((29 / 30 : ℝ) / (18 / 25)) := Real.log_pos (by norm_num)
  refine ⟨KF * Real.log B0 + Real.log B0 / Real.log ((29 / 30 : ℝ) / (18 / 25)),
    by positivity, fun t ht => ?_⟩
  have hfZ := finiteSetOfZeros_mono (by norm_num : (18 / 25 : ℝ) < 1) (gz_finite_zeros t)
  have hfin : (Zsm t).Finite := by
    apply (hfZ.image (aff t)).subset
    intro ρ hρ
    refine ⟨affInv t ρ, ?_, aff_affInv t ρ⟩
    rw [mem_gz_zeros_iff, aff_affInv]; exact hρ
  have gA : AnalyticOnNhd ℂ (gz t) (closedBall (0 : ℂ) 1) := fun z _ => gz_analyticAt t z
  have hinj : Set.InjOn (aff t) (hfZ.toFinset : Set ℂ) := by
    intro a _ b _ hab
    have := congr_arg (affInv t) hab
    rwa [affInv_aff, affInv_aff] at this
  have himg : hfZ.toFinset.image (aff t) = hfin.toFinset := by
    ext ρ
    rw [Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Set.Finite.mem_toFinset, mem_gz_zeros_iff] at hw; exact hw
    · intro hρ
      refine ⟨affInv t ρ, ?_, aff_affInv t ρ⟩
      rw [Set.Finite.mem_toFinset, mem_gz_zeros_iff, aff_affInv]; exact hρ
  have hordz : ∀ w ∈ hfZ.toFinset, analyticOrderNatAt (gz t) w = analyticOrderNatAt ζ (aff t w) := by
    intro w hw
    rw [Set.Finite.mem_toFinset, mem_gz_zeros_iff] at hw
    rw [ord_gz, ord_gζ hw.2.1]
  refine ⟨hfin, ?_, ?_⟩
  · -- the count, by Jensen
    have key := ZerosBound (by norm_num : (0 : ℝ) < 18 / 25) (by norm_num : (18 / 25 : ℝ) < 1)
      (by norm_num : (18 / 25 : ℝ) < 29 / 30) (by norm_num : (29 / 30 : ℝ) < 1) gA (gz_zero t)
      (gz_finite_zeros t) (fun z hz => gz_bound ht hz)
    have hsum : (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) =
        ∑ w ∈ hfZ.toFinset, (analyticOrderNatAt (gz t) w : ℝ) := by
      rw [← himg, Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro w hw; rw [hordz w hw]
    rw [hsum]
    push_cast at key
    have : (∑ w ∈ hfZ.toFinset, (analyticOrderNatAt (gz t) w : ℝ)) ≤
        Real.log B0 / Real.log ((29 / 30 : ℝ) / (18 / 25)) := by
      calc _ ≤ 1 / Real.log ((29 / 30 : ℝ) / (18 / 25)) * Real.log B0 := key
        _ = _ := by ring
    have h0 : 0 ≤ KF * Real.log B0 := by positivity
    linarith
  · intro s hs hs1 hζs
    set z := affInv t s with hzdef
    have hzn : ‖z‖ ≤ 2 / 3 := by rw [hzdef, norm_affInv]; linarith
    have hsz : aff t z = s := aff_affInv t s
    have hgs : gζ s ≠ 0 := by rw [ne_eq, gζ_eq_zero_iff]; push_neg; intro _; exact hζs
    have hzmem : z ∈ Metric.closedBall (0 : ℂ) (2 / 3) \ SetOfZeros (17 / 20) (gz t) := by
      refine ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hzn, ?_⟩
      rintro ⟨_, h0⟩
      unfold gz at h0
      rw [hsz, div_eq_zero_iff] at h0
      exact h0.elim hgs (gζ_cen_ne t)
    have key := FinalBound one_lt_B0 (by norm_num : (0 : ℝ) < 2 / 3)
      (by norm_num : (2 / 3 : ℝ) < 18 / 25) (by norm_num : (18 / 25 : ℝ) < 1)
      (by norm_num : (18 / 25 : ℝ) < 17 / 20) (by norm_num : (17 / 20 : ℝ) < 29 / 30)
      (by norm_num : (29 / 30 : ℝ) < 1) gA (gz_zero t) (gz_finite_zeros t)
      (fun w hw => gz_bound ht hw) hzmem
    have hc := gζ_cen_ne t
    have hderiv : deriv (gz t) z = 3 / 2 * deriv gζ s / gζ (cen t) := by
      have haff : HasDerivAt (aff t) (3 / 2) z := by
        unfold aff
        simpa using ((hasDerivAt_id z).const_mul (3 / 2 : ℂ)).const_add (cen t)
      have h := (((gζ_analyticAt (aff t z)).differentiableAt.hasDerivAt).comp z haff).div_const
        (gζ (cen t))
      unfold gz
      rw [show (fun w => gζ (aff t w) / gζ (cen t)) = fun w => (gζ ∘ aff t) w / gζ (cen t)
        from rfl, h.deriv, hsz]
      ring
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hlhs : deriv (gz t) z / gz t z = 3 / 2 * (deriv ζ s / ζ s + 1 / (s - 1)) := by
      rw [hderiv]
      unfold gz; rw [hsz, deriv_gζ hs1, gζ_of_ne hs1]
      field_simp
      ring
    have hsum : (∑ ρ ∈ hfZ.toFinset, (analyticOrderNatAt (gz t) ρ : ℂ) / (z - ρ)) =
        3 / 2 * ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ) := by
      rw [← himg, Finset.sum_image hinj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [hordz w hw]
      have hdiff : z - w = 2 / 3 * (s - aff t w) := by
        rw [← hsz]; unfold aff; ring
      rw [hdiff]
      by_cases hsw : s - aff t w = 0
      · rw [hsw]; simp
      · field_simp
    rw [hlhs, hsum, ← mul_sub, norm_mul] at key
    have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    rw [h32] at key
    have hKF' : 16 * (18 / 25 : ℝ) ^ 2 / (18 / 25 - 2 / 3) ^ 3 +
        1 / (((29 / 30) ^ 2 / (17 / 20) - 17 / 20) * Real.log ((29 / 30) / (17 / 20))) = KF := by
      rw [hKF]
    rw [hKF'] at key
    have h0 : 0 ≤ Real.log B0 / Real.log ((29 / 30 : ℝ) / (18 / 25)) := by positivity
    nlinarith [norm_nonneg (deriv ζ s / ζ s + 1 / (s - 1) -
      ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ))]

end LeanLab.PNTPort.ZetaZeros

