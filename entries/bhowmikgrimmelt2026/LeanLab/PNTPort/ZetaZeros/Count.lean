module

public import LeanLab.PNTPort.StrongPNT.StrongPNT

/-!
# Zeros of `ζ` near height `t` with `Re ρ ≥ 1/2` number `O(log |t|)`

Lab proof, unit U-5262, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics,
Davenport ch. 15, no cited input. The first brick of an explicit formula with sums over zeros,
which P0058 Lemma 7, the GoldbachAverage zero sums, Dudek2014 and RH ⇒ Schoenfeld all need.

* `norm_zeta_le`: `‖ζ s‖ ≤ 2 + ‖s‖ / Re s` for `Re s > 0` and `‖s - 1‖ ≥ 1`, from the ported
  formula `ζ s = 1 + 1/(s - 1) - s ∫₁^∞ {u} u^{-s-1} du`, Apache-2.0, PrimeNumberTheoremAnd.
* `fz_count`: Jensen's bound, the ported `ZerosBound`, for `f z = ζ(3/2 + it + 3z/2) / ζ(3/2 + it)`
  on the disc `‖z‖ ≤ 11/15`, with `‖f‖ ≤ B(t)` on `‖z‖ ≤ 29/30`, where `Re s ≥ 1/20`.
* `zero_window_count`: an absolute `C` such that for `|t| ≥ 3` the zeros `ρ` of `ζ` with
  `1/2 ≤ Re ρ` and `|Im ρ - t| ≤ 2/5` form a finite set and, with multiplicity, number at most
  `C log |t|`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric MeasureTheory

local notation "ζ" => riemannZeta

/-- `‖ζ s‖ ≤ 2 + ‖s‖ / Re s` for `0 < Re s` and `‖s - 1‖ ≥ 1`. -/
theorem norm_zeta_le {s : ℂ} (hs : 0 < s.re) (h1 : 1 ≤ ‖s - 1‖) :
    ‖ζ s‖ ≤ 2 + ‖s‖ / s.re := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at h1; linarith
  have leading : ‖1 + 1 / (s - 1)‖ ≤ 2 := by
    calc ‖1 + 1 / (s - 1)‖ ≤ ‖(1 : ℂ)‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by
        rw [norm_one, norm_div, norm_one]
        gcongr
        rw [div_le_one (by linarith)]; exact h1
      _ = 2 := by norm_num
  have domBound {x : ℝ} (hu : x ∈ Ioi 1) : |Int.fract x| * ‖(x : ℂ) ^ (-s - 1)‖
      ≤ x ^ (-s.re - 1) := by
    rw [mem_Ioi] at hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [sub_re, neg_re, one_re, Int.abs_fract]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) (Int.fract_lt_one x).le
  have domIntegral : Integrable (fun x : ℝ => x ^ (-s.re - 1)) (volume.restrict (Set.Ioi 1)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hint : ‖∫ (u : ℝ) in Ioi 1, (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ 1 / s.re := by
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
  have hmul : ‖s * ∫ (u : ℝ) in Ioi 1, (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤
      ‖s‖ / s.re := by
    rw [norm_mul, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hint (norm_nonneg _)
  rw [ZetaAltFormula hs hs1, riemannZeta1]
  exact (norm_sub_le_of_le leading hmul)

/-- The centre `c = 3/2 + it`. -/
noncomputable def cen (t : ℝ) : ℂ := 3 / 2 + I * t

/-- The affine map `z ↦ c + 3z/2`. -/
noncomputable def aff (t : ℝ) (z : ℂ) : ℂ := cen t + 3 / 2 * z

/-- The normalized shift `f z = ζ(c + 3z/2) / ζ(c)`. -/
noncomputable def fz (t : ℝ) (z : ℂ) : ℂ := ζ (aff t z) / ζ (cen t)

lemma aff_re (t : ℝ) (z : ℂ) : (aff t z).re = 3 / 2 + 3 / 2 * z.re := by
  simp [aff, cen]

lemma aff_im (t : ℝ) (z : ℂ) : (aff t z).im = t + 3 / 2 * z.im := by
  simp [aff, cen]

lemma zeta_cen_ne (t : ℝ) : ζ (cen t) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by simp [cen]; norm_num)

lemma aff_ne_one {t : ℝ} (ht : 3 ≤ |t|) {z : ℂ} (hz : ‖z‖ < 4 / 3) : aff t z ≠ 1 := by
  intro h
  have him := congr_arg Complex.im h
  rw [aff_im] at him
  simp at him
  have := Complex.abs_im_le_norm z
  cases abs_cases t <;> cases abs_cases z.im <;> linarith

lemma fz_analyticAt {t : ℝ} (ht : 3 ≤ |t|) {z : ℂ} (hz : ‖z‖ < 4 / 3) : AnalyticAt ℂ (fz t) z := by
  unfold fz
  refine AnalyticAt.div_const ?_
  exact AnalyticAt.fun_comp (analyticAt_riemannZeta (aff_ne_one ht hz))
    (analyticAt_const.fun_add (analyticAt_const.fun_mul analyticAt_id))

lemma fz_zero (t : ℝ) : fz t 0 = 1 := by
  simp [fz, aff, zeta_cen_ne t]

lemma fz_finite_zeros {t : ℝ} (ht : 3 ≤ |t|) : (SetOfZeros 1 (fz t)).Finite := by
  by_contra hinf; rw [Set.not_finite] at hinf
  have zerosSubset : SetOfZeros 1 (fz t) ⊆ Metric.closedBall (0 : ℂ) 1 := fun _ hx => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
  obtain ⟨x, hxK, hacc⟩ :=
    hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall 0 1) zerosSubset
  have hfAnalytic : AnalyticOnNhd ℂ (fz t) (Metric.ball (0 : ℂ) (4 / 3)) := by
    intro z hz; simp only [Metric.mem_ball, dist_zero_right] at hz
    exact fz_analyticAt ht hz
  have hfeq : Set.EqOn (fz t) 0 (Metric.ball (0 : ℂ) (4 / 3)) := by
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hfAnalytic
      Metric.isPreconnected_ball (z₀ := x) ?_ ?_
    · simp only [Metric.mem_ball, Metric.mem_closedBall, dist_zero_right] at hxK ⊢
      linarith
    · simp only [mem_closure_iff_clusterPt, ← accPt_principal_iff_clusterPt]
      exact hacc.mono (principal_mono.mpr fun _ h => h.2)
  have h0 := hfeq (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 4 / 3))
  rw [fz_zero] at h0
  exact one_ne_zero h0

/-- The positive constant `m₀ = ‖ζ 3 / ζ (3/2)‖`, a lower bound for `‖ζ(3/2 + it)‖`. -/
noncomputable def m0 : ℝ := ‖ζ 3 / ζ (3 / 2)‖

lemma m0_pos : 0 < m0 := by
  unfold m0
  apply norm_pos_iff.mpr
  apply div_ne_zero
  · exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  · exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)

lemma m0_le (t : ℝ) : m0 ≤ ‖ζ (cen t)‖ := by
  have h := ZetaFixedLowerBound t
  have : (‖ζ 3 / ζ (3 / 2)‖₊ : ℝ) ≤ (‖ζ (3 / 2 + I * t)‖₊ : ℝ) := by exact_mod_cast h
  simpa [m0, cen] using this

/-- `B(t) = (62 + 20|t|) / m₀`. -/
noncomputable def Bz (t : ℝ) : ℝ := (62 + 20 * |t|) / m0

lemma fz_bound {t : ℝ} (ht : 3 ≤ |t|) {z : ℂ} (hz : ‖z‖ ≤ 29 / 30) : ‖fz t z‖ ≤ Bz t := by
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have sre : 1 / 20 ≤ (aff t z).re := by
    rw [aff_re]; cases abs_cases z.re <;> linarith
  have s1 : 1 ≤ ‖aff t z - 1‖ := by
    have : |(aff t z - 1).im| ≤ ‖aff t z - 1‖ := Complex.abs_im_le_norm _
    have e : (aff t z - 1).im = t + 3 / 2 * z.im := by simp [aff_im]
    rw [e] at this
    cases abs_cases t <;> cases abs_cases z.im <;> cases abs_cases (t + 3 / 2 * z.im) <;> linarith
  have snorm : ‖aff t z‖ ≤ |t| + 3 := by
    unfold aff cen
    calc ‖3 / 2 + I * t + 3 / 2 * z‖ ≤ ‖(3 / 2 : ℂ)‖ + ‖I * (t : ℂ)‖ + ‖(3 / 2 : ℂ) * z‖ :=
          norm_add₃_le
      _ = 3 / 2 + |t| + 3 / 2 * ‖z‖ := by
          rw [norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
          norm_num
      _ ≤ |t| + 3 := by linarith
  have hzeta := norm_zeta_le (by linarith) s1
  have hq : ‖aff t z‖ / (aff t z).re ≤ 20 * (|t| + 3) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (aff t z), abs_nonneg t]
  have hc := m0_le t
  have hm := m0_pos
  unfold fz Bz
  rw [norm_div, div_le_div_iff₀ (lt_of_lt_of_le hm hc) hm]
  calc ‖ζ (aff t z)‖ * m0 ≤ (62 + 20 * |t|) * m0 := by
        apply mul_le_mul_of_nonneg_right _ hm.le; linarith
    _ ≤ (62 + 20 * |t|) * ‖ζ (cen t)‖ := by
        apply mul_le_mul_of_nonneg_left hc; positivity

/-- Jensen for `fz`: the zeros in `‖z‖ ≤ 11/15`, with multiplicity, number at most
`log B(t) / log(29/22)`. -/
theorem fz_count {t : ℝ} (ht : 3 ≤ |t|) :
    (∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (11 / 15 : ℝ) < 1) (fz_finite_zeros ht)).toFinset,
      (analyticOrderNatAt (fz t) ρ : ℝ)) ≤ Real.log (Bz t) / Real.log (29 / 22) := by
  have gA : AnalyticOnNhd ℂ (fz t) (closedBall (0 : ℂ) 1) := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    exact fz_analyticAt ht (by linarith)
  have key := ZerosBound (by norm_num : (0 : ℝ) < 11 / 15) (by norm_num : (11 / 15 : ℝ) < 1)
    (by norm_num : (11 / 15 : ℝ) < 29 / 30) (by norm_num : (29 / 30 : ℝ) < 1) gA (fz_zero t)
    (fz_finite_zeros ht) (fun z hz => fz_bound ht hz)
  have e : (29 / 30 : ℝ) / (11 / 15) = 29 / 22 := by norm_num
  rw [e] at key
  push_cast at key
  calc _ ≤ 1 / Real.log (29 / 22) * Real.log (Bz t) := key
    _ = Real.log (Bz t) / Real.log (29 / 22) := by ring

/-- The window: zeros `ρ` of `ζ` with `1/2 ≤ Re ρ` and `|Im ρ - t| ≤ 2/5`. -/
def ZW (t : ℝ) : Set ℂ := {ρ : ℂ | ζ ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ |ρ.im - t| ≤ 2 / 5}

/-- The inverse affine map `ρ ↦ (ρ - c) · 2/3`. -/
noncomputable def affInv (t : ℝ) (ρ : ℂ) : ℂ := (ρ - cen t) * (2 / 3)

lemma aff_affInv (t : ℝ) (ρ : ℂ) : aff t (affInv t ρ) = ρ := by
  unfold aff affInv; ring

lemma affInv_mem {t : ℝ} (ht : 3 ≤ |t|) {ρ : ℂ} (hρ : ρ ∈ ZW t) :
    affInv t ρ ∈ SetOfZeros (11 / 15) (fz t) := by
  obtain ⟨hz, hre, him⟩ := hρ
  have hlt : ρ.re < 1 := by
    by_contra h; push_neg at h
    exact riemannZeta_ne_zero_of_one_le_re h hz
  refine ⟨?_, ?_⟩
  · have e : affInv t ρ = (2 / 3 : ℂ) * (ρ - cen t) := by unfold affInv; ring
    rw [e, norm_mul]
    have h23 : ‖(2 / 3 : ℂ)‖ = 2 / 3 := by norm_num
    rw [h23]
    have hn : ‖ρ - cen t‖ ≤ 11 / 10 := by
      rw [Complex.norm_def, Real.sqrt_le_left (by norm_num)]
      simp only [Complex.normSq_apply, sub_re, sub_im, cen]
      simp
      have h1 : (ρ.im - t) ^ 2 ≤ (2 / 5) ^ 2 :=
        sq_le_sq' (by linarith [(abs_le.mp him).1]) (by linarith [(abs_le.mp him).2])
      nlinarith
    linarith
  · unfold fz; rw [aff_affInv, hz, zero_div]

lemma ord_fz {t : ℝ} (ht : 3 ≤ |t|) {z : ℂ} (hz : ‖z‖ < 4 / 3) :
    analyticOrderNatAt (fz t) z = analyticOrderNatAt ζ (aff t z) := by
  have hA : AnalyticAt ℂ (fun w => ζ (aff t w)) z :=
    AnalyticAt.fun_comp (analyticAt_riemannZeta (aff_ne_one ht hz))
      (analyticAt_const.fun_add (analyticAt_const.fun_mul analyticAt_id))
  have h1 : analyticOrderNatAt (fz t) z = analyticOrderNatAt (fun w => ζ (aff t w)) z :=
    analyticOrderNatAt_fun_div_const (zeta_cen_ne t) hA
  rw [h1]
  have asComp : analyticOrderAt (ζ ∘ aff t) z = analyticOrderAt ζ (aff t z) := by
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

/-- **Zeros of `ζ` near height `t` on the right of the critical line number `O(log |t|)`.** -/
theorem zero_window_count : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
    ∃ hfin : (ZW t).Finite,
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) ≤ C * Real.log |t| := by
  set K := |Real.log (41 / m0)|
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl22 : 0 < Real.log (29 / 22) := Real.log_pos (by norm_num)
  refine ⟨(1 + K / Real.log 3) / Real.log (29 / 22), by positivity, fun t ht => ?_⟩
  have hfinZ := finiteSetOfZeros_mono (by norm_num : (11 / 15 : ℝ) < 1) (fz_finite_zeros ht)
  have hfin : (ZW t).Finite := by
    apply (hfinZ.image (aff t)).subset
    intro ρ hρ
    exact ⟨affInv t ρ, affInv_mem ht hρ, aff_affInv t ρ⟩
  refine ⟨hfin, ?_⟩
  -- injective transfer to the zeros of `fz`
  have hinj : Set.InjOn (affInv t) (hfin.toFinset : Set ℂ) := by
    intro a _ b _ hab
    have := congr_arg (aff t) hab
    rwa [aff_affInv, aff_affInv] at this
  have hsub : hfin.toFinset.image (affInv t) ⊆ hfinZ.toFinset := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨ρ, hρ, rfl⟩ := hz
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    exact affInv_mem ht hρ
  have hsum : (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) =
      ∑ z ∈ hfin.toFinset.image (affInv t), (analyticOrderNatAt (fz t) z : ℝ) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have hm := (affInv_mem ht hρ).1
    rw [ord_fz ht (by linarith), aff_affInv]
  rw [hsum]
  have hcount := fz_count ht
  have hle : (∑ z ∈ hfin.toFinset.image (affInv t), (analyticOrderNatAt (fz t) z : ℝ)) ≤
      ∑ z ∈ hfinZ.toFinset, (analyticOrderNatAt (fz t) z : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  refine hle.trans (hcount.trans ?_)
  -- `log B(t) ≤ (1 + K / log 3) log |t|`
  have ht0 : 0 < |t| := by linarith
  have hlt : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
  have hm := m0_pos
  have hB : Real.log (Bz t) ≤ Real.log |t| + K := by
    have h1 : Bz t ≤ |t| * (41 / m0) := by
      unfold Bz
      rw [div_le_iff₀ hm]
      field_simp
      linarith
    have hBpos : 0 < Bz t := by unfold Bz; positivity
    calc Real.log (Bz t) ≤ Real.log (|t| * (41 / m0)) := Real.log_le_log hBpos h1
      _ = Real.log |t| + Real.log (41 / m0) := Real.log_mul ht0.ne' (by positivity)
      _ ≤ Real.log |t| + K := by gcongr; exact le_abs_self _
  have hK : K ≤ K / Real.log 3 * Real.log |t| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl3]
    exact mul_le_mul_of_nonneg_left hlt (abs_nonneg _)
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hl22]
  nlinarith
end LeanLab.PNTPort.ZetaZeros

