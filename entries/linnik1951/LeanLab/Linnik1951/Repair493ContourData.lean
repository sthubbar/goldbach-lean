module

public import LeanLab.Linnik1951.Decomp442b
public import LeanLab.Linnik1951.Decomp487a
public import LeanLab.Linnik1951.SPLIT_abstract_outer_kernels442

/-!
P0093 route supplies for Assembly376.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 157 truncation before equation 4.4. The signed Mellin integral on the finite frequency interval of radius N over R times log cubed N. -/
noncomputable def truncatedMellin487 (N : ℕ) (R : ℝ) (M : ℝ → ℂ) (α : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
      mellinKernel442 N α t * M t

/-- P0093 page 157 equation 4.4. The signed kernel with a continuous coefficient is jointly continuous in alpha and the finite line parameter. -/
theorem continuous_mellin_integrand487 (N : ℕ) (hN : 3 ≤ N)
    (M : ℝ → ℂ) (hM : Continuous M) :
    Continuous (fun p : ℝ × ℝ => mellinKernel442 N p.1 p.2 * M p.2) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hNr
  let Z : ℝ → ℂ := fun α => ((1 / (N : ℝ) : ℝ) : ℂ) +
    ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hZ : Continuous Z := by dsimp [Z]; fun_prop
  have hline : Continuous (fun t : ℝ => mellinLine1622 N t) := by
    dsimp [mellinLine1622]; fun_prop
  have hGamma : Continuous (fun t : ℝ => Complex.Gamma (mellinLine1622 N t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp hline.continuousAt
    intro m hm
    have hh := congrArg Complex.re hm
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.neg_re, Complex.natCast_re] at hh
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hinv : 0 < 1 / Real.log N := by positivity
    linarith
  have hslit (p : ℝ × ℝ) : Z p.1 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    positivity
  exact (((hZ.comp continuous_fst).cpow (hline.comp continuous_snd).neg hslit).mul
    (hGamma.comp continuous_snd)).mul (hM.comp continuous_snd)

/-- P0093 page 157 finite contour before equation 4.4. Its Mellin value is continuous in alpha. -/
theorem continuous_truncatedMellin487 (N : ℕ) (hN : 3 ≤ N) (R : ℝ)
    (M : ℝ → ℂ) (hM : Continuous M) :
    Continuous (truncatedMellin487 N R M) := by
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_mellin_integrand487 N hN M hM) _ _)

/-- P0093 page 156 equation 4.1. Parameter integration of the continuous signed kernel makes the full Mellin value strongly measurable. -/
theorem stronglyMeasurable_mellinU487 (N : ℕ) (hN : 3 ≤ N)
    (M : ℝ → ℂ) (hM : Continuous M) :
    StronglyMeasurable (mellinU1622 N M) := by
  exact stronglyMeasurable_const.mul
    (continuous_mellin_integrand487 N hN M hM).stronglyMeasurable.integral_prod_right

/-- P0093 page 157 equation 4.4. The square of the finite Mellin integral is exactly its signed double kernel. No absolute value is inserted into either line integral. -/
theorem truncated_signed_square487 (N : ℕ) (R : ℝ) (M : ℝ → ℂ) (α : ℝ) :
    ‖truncatedMellin487 N R M α‖ ^ 2 = (1 / (2 * Real.pi)) ^ 2 *
      (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
        ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          (mellinKernel442 N α t * M t) *
            (starRingEnd ℂ) (mellinKernel442 N α u * M u)).re := by
  let f : ℝ → ℂ := fun t => mellinKernel442 N α t * M t
  let T : ℝ := (N : ℝ) / R * Real.log N ^ 3
  have hprod : (∫ t in -T..T, ∫ u in -T..T, f t * (starRingEnd ℂ) (f u)) =
      ((‖∫ t in -T..T, f t‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.intervalIntegral_conj, intervalIntegral.integral_mul_const,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t in -T..T, f t)‖ ^ 2 =
    (1 / (2 * Real.pi)) ^ 2 * (∫ t in -T..T, ∫ u in -T..T, f t * (starRingEnd ℂ) (f u)).re
  rw [hprod, Complex.ofReal_re, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)), mul_pow]

/-- P0093 page 157 equation 4.4. On the finite contour the alpha integral can be moved inside both signed frequency integrals. All exchanges follow from continuity on compact rectangles. -/
theorem truncated_signed_fubini487 (N : ℕ) (hN : 3 ≤ N) (R : ℝ)
    (M : ℝ → ℂ) (hM : Continuous M) (a b : ℝ) :
    let T : ℝ := (N : ℝ) / R * Real.log N ^ 3
    (∫ α in a..b, ‖truncatedMellin487 N R M α‖ ^ 2) =
      (1 / (2 * Real.pi)) ^ 2 *
        (∫ t in -T..T, ∫ u in -T..T, ∫ α in a..b,
          (mellinKernel442 N α t * M t) *
            (starRingEnd ℂ) (mellinKernel442 N α u * M u)).re := by
  let T : ℝ := (N : ℝ) / R * Real.log N ^ 3
  let F : ℝ → ℝ → ℝ → ℂ := fun α t u =>
    (mellinKernel442 N α t * M t) *
      (starRingEnd ℂ) (mellinKernel442 N α u * M u)
  have hK := continuous_mellin_integrand487 N hN M hM
  have hF : Continuous (fun p : (ℝ × ℝ) × ℝ => F p.1.1 p.1.2 p.2) := by
    exact (hK.comp (continuous_fst.fst.prodMk continuous_fst.snd)).mul
      ((hK.comp (continuous_fst.fst.prodMk continuous_snd)).star)
  have hFi : Continuous (fun p : ℝ × ℝ => ∫ u in -T..T, F p.1 p.2 u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF (-T) T
  have hFii : Continuous (fun α : ℝ => ∫ t in -T..T, ∫ u in -T..T, F α t u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hFi (-T) T
  have hswap1 : (∫ α in a..b, ∫ t in -T..T, ∫ u in -T..T, F α t u) =
      ∫ t in -T..T, ∫ α in a..b, ∫ u in -T..T, F α t u := by
    apply intervalIntegral_intervalIntegral_swap
    exact (hFi.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hswap2 (t : ℝ) : (∫ α in a..b, ∫ u in -T..T, F α t u) =
      ∫ u in -T..T, ∫ α in a..b, F α t u := by
    have hFc : Continuous (fun p : ℝ × ℝ => F p.1 t p.2) := by
      exact (hK.comp (continuous_fst.prodMk continuous_const)).mul hK.star
    apply intervalIntegral_intervalIntegral_swap
    exact (hFc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  change (∫ α in a..b, ‖truncatedMellin487 N R M α‖ ^ 2) =
    (1 / (2 * Real.pi)) ^ 2 * (∫ t in -T..T, ∫ u in -T..T, ∫ α in a..b, F α t u).re
  calc
    _ = (1 / (2 * Real.pi)) ^ 2 *
        (∫ α in a..b, (∫ t in -T..T, ∫ u in -T..T, F α t u).re) := by
      simp_rw [truncated_signed_square487]
      rw [intervalIntegral.integral_const_mul]
    _ = (1 / (2 * Real.pi)) ^ 2 *
        (∫ α in a..b, ∫ t in -T..T, ∫ u in -T..T, F α t u).re := by
      congr 1
      exact intervalIntegral.intervalIntegral_re (hFii.intervalIntegrable a b)
    _ = _ := by rw [hswap1]; simp_rw [hswap2]

/-- P0093 page 157 argument identity before equation 4.4. On the positive outer interval the angular gap has the quantitative lower bound R over ten N. Its dependence on N is retained. -/
theorem outer_angular_gap_scaled487 (N R α : ℝ) (hR : 0 < R) (hRN : R ≤ N)
    (hα : 0 ≤ α) (hcap : α ≤ 1 / R) :
    R / (10 * N) ≤ Real.pi / 2 -
      (((1 / N : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I).arg := by
  have hN : 0 < N := hR.trans_le hRN
  let z : ℂ := ((1 / N : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hre : z.re = 1 / N := by simp [z]
  have him : z.im = 2 * Real.pi * α := by simp [z]
  have hzre : 0 < z.re := by rw [hre]; positivity
  have hz : z ≠ 0 := by intro hh; simp [hh] at hzre
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnorm : ‖z‖ ≤ 10 / R := by
    calc
      _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ = 1 / N + 2 * Real.pi * α := by
        rw [hre, him, abs_of_pos (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ 1 / R + 2 * Real.pi * (1 / R) :=
        add_le_add (one_div_le_one_div_of_le hR hRN)
          (mul_le_mul_of_nonneg_left hcap (by positivity))
      _ = (1 + 2 * Real.pi) / R := by ring
      _ ≤ 10 / R := div_le_div_of_nonneg_right (by linarith [Real.pi_lt_four]) hR.le
  have hnormR : R * ‖z‖ ≤ 10 := by
    have hh := (le_div_iff₀ hR).mp hnorm
    nlinarith
  have hratio : R / (10 * N) ≤ z.re / ‖z‖ := by
    rw [div_le_div_iff₀ (by positivity : 0 < 10 * N) hn, hre]
    have he : 1 / N * (10 * N) = 10 := by field_simp
    rw [he]
    exact hnormR
  have harg : z.arg ≤ Real.pi / 2 :=
    Complex.arg_le_pi_div_two_iff.mpr (Or.inl hzre.le)
  have hs := Real.sin_le (sub_nonneg.mpr harg)
  rw [Real.sin_pi_div_two_sub, Complex.cos_arg hz] at hs
  exact hratio.trans hs

/-- P0093 page 157 power factor before equation 4.4. For real part of z equal to one over N, the shifted power has norm at most exp one times square root N times exp of absolute t times absolute argument. -/
theorem mellin_power_factor487 (N : ℕ) (hN : 2 ≤ N) (z : ℂ)
    (hzre : z.re = 1 / (N : ℝ)) (t : ℝ) :
    ‖z ^ (-(mellinLine1622 N t))‖ ≤
      Real.exp 1 * Real.sqrt N * Real.exp (|t| * |z.arg|) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  set σ : ℝ := 1 / 2 + 1 / Real.log N with hσdef
  have hσpos : 0 < σ := by
    have : 0 < 1 / Real.log N := div_pos one_pos hlog
    rw [hσdef]; linarith
  have hre : (-(mellinLine1622 N t)).re = -σ := by
    simp only [mellinLine1622, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, hσdef]
  have him : (-(mellinLine1622 N t)).im = -t := by
    simp only [mellinLine1622, Complex.neg_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul,
      add_zero, zero_add]
  have h := Complex.norm_cpow_le z (-(mellinLine1622 N t))
  rw [hre, him] at h
  have hznorm : (1 / (N : ℝ)) ≤ ‖z‖ := by
    have h1 := Complex.abs_re_le_norm z
    rw [hzre] at h1
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))] at h1
    exact h1
  have h1 : ‖z‖ ^ (-σ) ≤ (N : ℝ) ^ σ := by
    have hstep := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < 1 / (N:ℝ)) hznorm
      (show -σ ≤ 0 from by linarith)
    have hbase : ((1 : ℝ) / (N : ℝ)) ^ (-σ) = (N : ℝ) ^ σ := by
      rw [one_div, Real.inv_rpow hNpos.le, ← Real.rpow_neg]
      · ring_nf
      · exact hNpos.le
    rwa [hbase] at hstep
  have hNpow : (N : ℝ) ^ σ = Real.exp 1 * Real.sqrt N := by
    have hadd : (N : ℝ) ^ σ = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / Real.log N) := by
      rw [hσdef, Real.rpow_add hNpos]
    rw [hadd, ← Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos,
      show Real.log (N : ℝ) * (1 / Real.log (N : ℝ)) = 1 from by field_simp]
    ring
  have h3 : (Real.exp (z.arg * -t))⁻¹ ≤ Real.exp (|t| * |z.arg|) := by
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [le_abs_self t, neg_abs_le z.arg, le_abs_self z.arg, neg_abs_le t,
      mul_le_mul_of_nonneg_left (le_abs_self t) (abs_nonneg z.arg)]
  calc ‖z ^ (-(mellinLine1622 N t))‖
      ≤ ‖z‖ ^ (-σ) / Real.exp (z.arg * -t) := h
    _ = ‖z‖ ^ (-σ) * (Real.exp (z.arg * -t))⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (N : ℝ) ^ σ * Real.exp (|t| * |z.arg|) :=
        mul_le_mul h1 h3 (by positivity) (Real.rpow_nonneg hNpos.le σ)
    _ = Real.exp 1 * Real.sqrt N * Real.exp (|t| * |z.arg|) := by rw [hNpow]

/-- P0093 page 157 Gamma and power factors before equation 4.4. On the positive outer alpha interval the full signed kernel has decay rate R over ten N. This retains the shrinking angular gap. -/
theorem outer_kernel_scaled_decay487 (N : ℕ) (hN : 3 ≤ N) (R α t : ℝ)
    (hR : 0 < R) (hRN : R ≤ (N : ℝ)) (hα : 0 ≤ α) (hcap : α ≤ 1 / R) :
    ‖mellinKernel442 N α t‖ ≤
      (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)) *
        (3 + |t|) * Real.exp (-(R / (10 * (N : ℝ))) * |t|) := by
  let z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) +
    ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hre : z.re = 1 / (N : ℝ) := by simp [z]
  have him : z.im = 2 * Real.pi * α := by simp [z]
  have harg : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr (by rw [him]; positivity)
  have hp := mellin_power_factor487 N (by omega) z hre t
  rw [abs_of_nonneg harg] at hp
  have hg := gamma_mellin_line442 N hN t
  have hgap : R / (10 * (N : ℝ)) ≤ Real.pi / 2 - z.arg :=
    outer_angular_gap_scaled487 (N : ℝ) R α hR hRN hα hcap
  have he : Real.exp (|t| * (z.arg - Real.pi / 2)) ≤
      Real.exp (-(R / (10 * (N : ℝ))) * |t|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hgap (abs_nonneg t)]
  calc
    _ = ‖z ^ (-(mellinLine1622 N t))‖ * ‖Complex.Gamma (mellinLine1622 N t)‖ := norm_mul _ _
    _ ≤ (Real.exp 1 * Real.sqrt N * Real.exp (|t| * z.arg)) *
        (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) :=
      mul_le_mul hp hg (norm_nonneg _) (by positivity)
    _ = (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)) *
        (3 + |t|) * Real.exp (|t| * (z.arg - Real.pi / 2)) := by
      rw [show |t| * (z.arg - Real.pi / 2) = |t| * z.arg + -(Real.pi * |t| / 2) by ring,
        Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

/-- P0093 page 157 truncation remainder. An auxiliary scalar absorption step for the scaled Gamma tail: every fixed positive C times N to power ten times exp of negative log cubed N over twenty is eventually at most one. -/
theorem outer_tail_polynomial_absorption487 (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C * (N : ℝ) ^ 10 * Real.exp (-(Real.log N ^ 3 / 20)) ≤ 1 := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt (max C (Real.exp 20))
  refine ⟨N0, ?_⟩
  intro N hN
  have hNr : (N0 : ℝ) < N := by exact_mod_cast hN
  have hCN : C ≤ (N : ℝ) := (le_max_left _ _).trans (hN0.trans hNr).le
  have hexp : Real.exp 20 ≤ (N : ℝ) := (le_max_right _ _).trans (hN0.trans hNr).le
  have hNp : (0 : ℝ) < N := (Real.exp_pos 20).trans_le hexp
  have hlog : 20 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 20) hexp
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hsq : (220 : ℝ) ≤ Real.log N ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq hlog0
  have hcube : 11 * Real.log N ≤ Real.log N ^ 3 / 20 := by nlinarith
  have hp : (N : ℝ) ^ 10 = Real.exp (10 * Real.log N) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hNp] using
      (Real.exp_nat_mul (Real.log (N : ℝ)) 10).symm
  calc
    _ = C * Real.exp (10 * Real.log N - Real.log N ^ 3 / 20) := by
      rw [hp, mul_assoc, ← Real.exp_add]
      congr 2
    _ ≤ C * Real.exp (-Real.log N) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC.le
    _ = C / (N : ℝ) := by rw [Real.exp_neg, Real.exp_log hNp]; ring
    _ ≤ 1 := (div_le_one hNp).mpr hCN

/-- P0093 page 157 truncation remainder, auxiliary scalar estimate. The quartic exponential tail on the positive half line is bounded by its half rate full Gamma moment times the cutoff exponential. -/
theorem quartic_exponential_tail487 (c T : ℝ) (hc : 0 < c) (hT : 0 ≤ T) :
    (∫ x in Set.Ioi T, x ^ 4 * Real.exp (-(c * x))) ≤
      (24 / (c / 2) ^ 5) * Real.exp (-(c / 2 * T)) := by
  have hfull (d : ℝ) (hd : 0 < d) :
      (∫ x in Set.Ioi (0 : ℝ), x ^ 4 * Real.exp (-(d * x))) = 24 / d ^ 5 := by
    have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (5 : ℝ)) (r := d) (by norm_num) hd
    have hg : Real.Gamma (5 : ℝ) = 24 := by
      norm_num [Real.Gamma_nat_eq_factorial]
    norm_num only at hh
    rw [hg] at hh
    simpa [div_pow, div_eq_mul_inv, mul_comm] using hh
  have hIfull (d : ℝ) (hd : 0 < d) :
      IntegrableOn (fun x : ℝ => x ^ 4 * Real.exp (-(d * x))) (Set.Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hfull d hd]
    positivity
  have hd : 0 < c / 2 := by positivity
  have hI := (hIfull c hc).mono_set (Set.Ioi_subset_Ioi hT)
  have hIhalf := (hIfull (c / 2) hd).mono_set (Set.Ioi_subset_Ioi hT)
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioi T) :
      x ^ 4 * Real.exp (-(c * x)) ≤
        Real.exp (-(c / 2 * T)) * (x ^ 4 * Real.exp (-(c / 2 * x))) := by
    have he : Real.exp (-(c / 2 * x)) ≤ Real.exp (-(c / 2 * T)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left (le_of_lt hx) hd.le)
    calc
      _ = (x ^ 4 * Real.exp (-(c / 2 * x))) * Real.exp (-(c / 2 * x)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ (x ^ 4 * Real.exp (-(c / 2 * x))) * Real.exp (-(c / 2 * T)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ x in Set.Ioi T,
        Real.exp (-(c / 2 * T)) * (x ^ 4 * Real.exp (-(c / 2 * x))) :=
      setIntegral_mono_on hI (hIhalf.const_mul _) measurableSet_Ioi hpoint
    _ = Real.exp (-(c / 2 * T)) * ∫ x in Set.Ioi T,
        x ^ 4 * Real.exp (-(c / 2 * x)) := integral_const_mul _ _
    _ ≤ Real.exp (-(c / 2 * T)) * ∫ x in Set.Ioi (0 : ℝ),
        x ^ 4 * Real.exp (-(c / 2 * x)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply setIntegral_mono_set (hIfull (c / 2) hd)
        (ae_of_all _ (fun x => by positivity))
      exact (Set.Ioi_subset_Ioi hT).eventuallySubset
    _ = _ := by rw [hfull (c / 2) hd]; ring

end LeanLab.Linnik1951
