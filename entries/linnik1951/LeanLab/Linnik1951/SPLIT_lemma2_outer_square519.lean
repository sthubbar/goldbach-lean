module

public import LeanLab.Linnik1951.Decomp519a
public import LeanLab.Linnik1951.Decomp501a

/-!
Split of lemma2_outer_square519 of Decomp519a into three leaves.  The signed
outer square estimate of Lemma 2 is cut in two ways.  One leaf carries the
measure theoretic half alone, that the square of the Mellin transform is
integrable on the outer interval; it asks for no constant and no size.  The
other two carry the mass bound itself, one on the range of the inverse radius
below the seventh root of N and one on the range above it.  The assembly at the
end has no placeholder proof, splits on which range the inverse radius lies in and keeps the
larger of the two constants; it does not use the split theorem itself.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

set_option maxHeartbeats 1600000

/-- The outer margin `arctan (1 / (4 pi N))` is positive for `N ≥ 1`. -/
private lemma delta519_pos (N : ℕ) (hN : 1 ≤ N) :
    0 < Real.arctan (1 / (4 * Real.pi * (N : ℝ))) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  exact Real.arctan_pos.mpr (by positivity)

private lemma four_piN_pos (N : ℕ) (hN : 1 ≤ N) :
    (0 : ℝ) < 4 * Real.pi * (N : ℝ) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have := Real.pi_pos
  positivity

/-- `sin (arctan (1 / (4 pi N))) = 1 / sqrt (1 + (4 pi N) ^ 2)`. -/
private lemma sin_delta519 (N : ℕ) (hN : 1 ≤ N) :
    Real.sin (Real.arctan (1 / (4 * Real.pi * (N : ℝ)))) =
      1 / Real.sqrt (1 + (4 * Real.pi * (N : ℝ)) ^ 2) := by
  have ha : (0 : ℝ) < 4 * Real.pi * (N : ℝ) := four_piN_pos N hN
  rw [Real.sin_arctan]
  have h2 : (1 : ℝ) + (1 / (4 * Real.pi * (N : ℝ))) ^ 2 =
      ((4 * Real.pi * (N : ℝ)) ^ 2 + 1) / (4 * Real.pi * (N : ℝ)) ^ 2 := by
    field_simp
  rw [h2, Real.sqrt_div' _ (by positivity), Real.sqrt_sq ha.le]
  field_simp
  congr 1
  ring

/-- The base `1 / N + 2 pi i alpha` of the outer Mellin power has argument at most
`pi / 2 - arctan (1 / (4 pi N))` when `4 / N ≤ alpha ≤ 2`. -/
private lemma outer_arg519 (N : ℕ) (hN : 2 ≤ N) (α : ℝ)
    (hα0 : 4 / (N : ℝ) ≤ α) (hα2 : α ≤ 2) :
    |Complex.arg (((1 / (N : ℝ) : ℝ) : ℂ) +
        ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I)| ≤
      Real.pi / 2 - Real.arctan (1 / (4 * Real.pi * (N : ℝ))) := by
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set δ := Real.arctan (1 / (4 * Real.pi * (N : ℝ))) with hδdef
  have hδpos : 0 < δ := delta519_pos N hN1
  have hδlt : δ < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzim : z.im = 2 * Real.pi * α := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hzpos : 0 < ‖z‖ := by
    have h2 : 0 < ‖z‖ ^ 2 := by rw [hsq]; positivity
    nlinarith [norm_nonneg z]
  have himlo : 8 * Real.pi / (N : ℝ) ≤ z.im := by
    rw [hzim]
    calc 8 * Real.pi / (N : ℝ) = 2 * Real.pi * (4 / (N : ℝ)) := by field_simp; ring
      _ ≤ 2 * Real.pi * α := by
          apply mul_le_mul_of_nonneg_left hα0 (by positivity)
  have himhi : z.im ≤ 4 * Real.pi := by
    rw [hzim]
    have h := mul_le_mul_of_nonneg_left hα2 (by positivity : (0:ℝ) ≤ 2 * Real.pi)
    nlinarith [h]
  -- modulus bound
  have himpos : 0 < z.im := lt_of_lt_of_le (by positivity) himlo
  have h1 : z.im ^ 2 ≤ (4 * Real.pi) ^ 2 := pow_le_pow_left₀ himpos.le himhi 2
  have hsqle : ‖z‖ ^ 2 ≤ (1 / (N : ℝ)) ^ 2 + (4 * Real.pi) ^ 2 := by
    rw [hsq, hzre]
    nlinarith [h1]
  have hnorm_le : ‖z‖ ≤ Real.sqrt ((1 / (N : ℝ)) ^ 2 + (4 * Real.pi) ^ 2) := by
    calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsqle
  -- divide
  have hA : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hfac : (1 / (N : ℝ)) ^ 2 + (4 * Real.pi) ^ 2 =
      (1 / (N : ℝ)) ^ 2 * (1 + (4 * Real.pi * (N : ℝ)) ^ 2) := by
    field_simp
  have hsqrt_eq : Real.sqrt ((1 / (N : ℝ)) ^ 2 + (4 * Real.pi) ^ 2) =
      (1 / (N : ℝ)) * Real.sqrt (1 + (4 * Real.pi * (N : ℝ)) ^ 2) := by
    rw [hfac, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hdiv : 1 / Real.sqrt (1 + (4 * Real.pi * (N : ℝ)) ^ 2) ≤ z.re / ‖z‖ := by
    rw [hzre]
    have h2 : (1 / (N : ℝ)) / Real.sqrt ((1 / (N : ℝ)) ^ 2 + (4 * Real.pi) ^ 2) =
        1 / Real.sqrt (1 + (4 * Real.pi * (N : ℝ)) ^ 2) := by
      rw [hsqrt_eq]
      field_simp
    rw [← h2]
    exact div_le_div_of_nonneg_left hA.le (by positivity) hnorm_le
  have hcos : Real.sin δ ≤ z.re / ‖z‖ := by
    rw [hδdef, sin_delta519 N hN1]
    exact hdiv
  have hθmem : Real.pi / 2 - δ ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hargmem : |Complex.arg z| ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩
  have hcosarg : Real.cos |Complex.arg z| = z.re / ‖z‖ := by
    rw [Real.cos_abs, Complex.cos_arg hz]
  rw [← Real.cos_pi_div_two_sub δ, ← hcosarg] at hcos
  exact (Real.strictAntiOn_cos.le_iff_ge hθmem hargmem).mp hcos

/-- On the outer range the power factor of the Mellin kernel gains the exponential
decay of the normal direction: its modulus is at most `e sqrt N exp (-delta |t|)`. -/
private lemma outer_cpow_bound519 (N : ℕ) (hN : 3 ≤ N) (α t : ℝ)
    (hα0 : 4 / (N : ℝ) ≤ α) (hα2 : α ≤ 2) :
    ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine519 N t))‖ ≤
      Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - Real.arctan (1 / (4 * Real.pi * (N : ℝ))))) := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set δ := Real.arctan (1 / (4 * Real.pi * (N : ℝ))) with hδdef
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  have hnorm_ge : 1 / (N : ℝ) ≤ ‖z‖ := by
    calc 1 / (N : ℝ) = |z.re| := by
          rw [hzre, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have harg : |Complex.arg z| ≤ Real.pi / 2 - δ := by
    rw [hδdef, hzdef]
    exact outer_arg519 N hN2 α hα0 hα2
  have hsre : (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsim : (mellinLine519 N t).im = t := by
    simp only [mellinLine519, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hσ : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := by positivity
  have hmul : (1 / 2 + 1 / Real.log N) * Real.log N = Real.log N / 2 + 1 := by
    field_simp
  have hlogz : -(1 / 2 + 1 / Real.log N) * Real.log ‖z‖ ≤ Real.log N / 2 + 1 := by
    have h1 : Real.log (1 / (N : ℝ)) ≤ Real.log ‖z‖ :=
      Real.log_le_log (by positivity) hnorm_ge
    have h2 : Real.log (1 / (N : ℝ)) = -Real.log N := by
      rw [Real.log_div one_ne_zero hNr.ne']; simp
    have hσ' : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := hσ
    nlinarith [h1, h2, hmul]
  have hargpos : 0 ≤ Complex.arg z := by
    rw [Complex.arg_nonneg_iff]
    rw [hzdef]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero]
    have h4 : (0 : ℝ) < 4 / (N : ℝ) := by positivity
    nlinarith [Real.pi_pos, hα0, h4]
  have htarg : t * Complex.arg z ≤ |t| * (Real.pi / 2 - δ) := by
    have hupper : Complex.arg z ≤ Real.pi / 2 - δ := (abs_le.mp harg).2
    rcases lt_or_ge t 0 with ht | ht
    · rw [abs_of_neg ht]
      have h3 : t * Complex.arg z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht.le hargpos
      nlinarith [h3]
    · rw [abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left hupper ht
  have hkey : (Complex.log z * (-(mellinLine519 N t))).re ≤
      Real.log N / 2 + 1 + |t| * (Real.pi / 2 - δ) := by
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im,
      hsre, hsim]
    nlinarith [hlogz, htarg]
  rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp]
  refine (Real.exp_le_exp.mpr hkey).trans (le_of_eq ?_)
  have hexp_logN : Real.exp (Real.log N / 2) = Real.sqrt N := by
    rw [← Real.log_sqrt hNr.le, Real.exp_log (Real.sqrt_pos.mpr hNr)]
  rw [Real.exp_add, Real.exp_add, hexp_logN]
  ring

/-- The outer kernel is dominated by the exponential of the normal direction with the
arithmetic weight: `sqrt (2 pi) (3 + |t|) exp (-delta |t|)`. -/
private lemma outer_kernel_bound519 (N : ℕ) (hN : 3 ≤ N) (α t : ℝ)
    (hα0 : 4 / (N : ℝ) ≤ α) (hα2 : α ≤ 2) :
    ‖mellinKernel519 N α t‖ ≤
      Real.exp 1 * Real.sqrt N * (Real.sqrt (2 * Real.pi) * (3 + |t|)) *
        Real.exp (-(Real.arctan (1 / (4 * Real.pi * (N : ℝ))) * |t|)) := by
  set δ := Real.arctan (1 / (4 * Real.pi * (N : ℝ))) with hδdef
  have hcp := outer_cpow_bound519 N hN α t hα0 hα2
  have hg := gamma_mellin_line519 N hN t
  have hExp : Real.exp (|t| * (Real.pi / 2 - δ)) * Real.exp (-(Real.pi * |t| / 2)) =
      Real.exp (-(δ * |t|)) := by
    rw [← Real.exp_add, show |t| * (Real.pi / 2 - δ) + -(Real.pi * |t| / 2) = -(δ * |t|) by
      ring]
  unfold mellinKernel519
  rw [norm_mul]
  calc ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine519 N t))‖ * ‖Complex.Gamma (mellinLine519 N t)‖
      ≤ (Real.exp 1 * Real.sqrt N * Real.exp (|t| * (Real.pi / 2 - δ))) *
          (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) := by
        apply mul_le_mul hcp hg (norm_nonneg _) (by positivity)
    _ = Real.exp 1 * Real.sqrt N * (Real.sqrt (2 * Real.pi) * (3 + |t|)) *
          Real.exp (-(δ * |t|)) := by
        rw [← hExp]
        ring

/-- `exp (-b |t|)` is integrable on the line. -/
private lemma exp_neg_abs_integrable519 (b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * |t|)) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -b) (by linarith) (0 : ℝ)).congr_fun ?_
      measurableSet_Ioi
    intro t ht
    show Real.exp (-b * t) = Real.exp (-b * |t|)
    rw [abs_of_pos ht]
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := b) hb (0 : ℝ)).congr_fun ?_ measurableSet_Iic
    intro t ht
    show Real.exp (b * t) = Real.exp (-b * |t|)
    rw [abs_of_nonpos ht]
    ring_nf
  have h3 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0 ∪ Set.Iic 0) :=
    integrableOn_union.mpr ⟨h1, h2⟩
  rw [Set.Ioi_union_Iic] at h3
  exact integrableOn_univ.mp h3

/-- A fifth power is dominated by `exp (e |t|)` for every `e > 0`. -/
private lemma pow_five_le_exp519 (e : ℝ) (he : 0 < e) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, (|t| + 4) ^ 5 ≤ K * Real.exp (e * |t|) := by
  refine ⟨120 * (1 / e) ^ 5 * Real.exp (4 * e), by positivity, fun t => ?_⟩
  have hv : (0 : ℝ) ≤ e * (|t| + 4) := by positivity
  have h1 : (e * (|t| + 4)) ^ 5 ≤ 120 * Real.exp (e * (|t| + 4)) := by
    have h := Real.pow_div_factorial_le_exp (x := e * (|t| + 4)) hv 5
    norm_num at h
    calc (e * (|t| + 4)) ^ 5 = (e * (|t| + 4)) ^ 5 / 120 * 120 := by ring
      _ ≤ Real.exp (e * (|t| + 4)) * 120 := by
          exact mul_le_mul_of_nonneg_right h (by norm_num)
      _ = 120 * Real.exp (e * (|t| + 4)) := by ring
  have h2 : (|t| + 4) ^ 5 = (1 / e) ^ 5 * (e * (|t| + 4)) ^ 5 := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hExp : Real.exp (e * (|t| + 4)) = Real.exp (4 * e) * Real.exp (e * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h2]
  calc (1 / e) ^ 5 * (e * (|t| + 4)) ^ 5
      ≤ (1 / e) ^ 5 * (120 * Real.exp (e * (|t| + 4))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 120 * (1 / e) ^ 5 * Real.exp (4 * e) * Real.exp (e * |t|) := by
        rw [hExp]; ring

/-- The arithmetic weight of the outer kernel is integrable on the line. -/
private lemma outer_weight_integrable519 (N : ℕ) (hN : 2 ≤ N) :
    Integrable (fun t : ℝ => (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
      Real.exp (-(Real.arctan (1 / (4 * Real.pi * (N : ℝ))) * |t|))) := by
  set δ := Real.arctan (1 / (4 * Real.pi * (N : ℝ))) with hδdef
  have hδpos : 0 < δ := delta519_pos N (by omega)
  obtain ⟨K, hK0, hK⟩ := pow_five_le_exp519 (δ / 2) (by linarith)
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hNr
  have hbase : Integrable (fun t : ℝ => Real.exp (-(δ / 2) * |t|)) :=
    exp_neg_abs_integrable519 _ (by linarith)
  refine Integrable.mono' (hbase.const_mul (16 * (Real.log N ^ 3 + 1) * K)) ?_ ?_
  · have hcont : Continuous fun t : ℝ => (3 + |t|) *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3 * Real.exp (-(δ * |t|)) := by
      have harg : Continuous fun t : ℝ => (N : ℝ) * (|t| + 2) :=
        continuous_const.mul (continuous_abs.add continuous_const)
      have hlog : Continuous fun t : ℝ => Real.log ((N : ℝ) * (|t| + 2)) :=
        harg.log (fun t => ne_of_gt (by positivity))
      have hexp : Continuous fun t : ℝ => Real.exp (-(δ * |t|)) :=
        Real.continuous_exp.comp (by fun_prop)
      exact ((continuous_const.add continuous_abs).mul (hlog.pow 3)).mul hexp
    exact hcont.aestronglyMeasurable
  · filter_upwards with t
    have hlogpos : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by
        have h2 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
        nlinarith [hNr, abs_nonneg t]
      have h3 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
        Real.log_nonneg h1
      positivity
    have hsplit := log_cube_split519 N t hN
    have ht4 : (0 : ℝ) < |t| + 4 := by linarith [abs_nonneg t]
    have hlog2 : Real.log (|t| + 2) ^ 3 ≤ (|t| + 4) ^ 3 := by
      have h1 : Real.log (|t| + 2) ≤ |t| + 4 :=
        (Real.log_le_self (by linarith [abs_nonneg t])).trans (by linarith)
      have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      exact pow_le_pow_left₀ h2 h1 3
    have h17 : (1 : ℝ) ≤ |t| + 4 := by linarith [abs_nonneg t]
    have hcube : (1 : ℝ) ≤ (|t| + 4) ^ 3 := by
      calc (1 : ℝ) = 1 ^ 3 := by ring
        _ ≤ (|t| + 4) ^ 3 := pow_le_pow_left₀ (by norm_num) h17 3
    have hkey : (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
        16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 := by
      have h3 : (0 : ℝ) ≤ 3 + |t| := by linarith [abs_nonneg t]
      have h4 : Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
          8 * (Real.log N ^ 3 + 1) * (1 + Real.log (|t| + 2) ^ 3) := by
        have h5 : 8 * Real.log N ^ 3 ≤ 8 * (Real.log N ^ 3 + 1) := by linarith
        have h6 : 8 * Real.log (|t| + 2) ^ 3 ≤
            8 * (Real.log N ^ 3 + 1) * Real.log (|t| + 2) ^ 3 := by
          have h7 : (1 : ℝ) ≤ Real.log N ^ 3 + 1 := by linarith [pow_nonneg hlogN 3]
          have h8 : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
            have h9 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
            exact pow_nonneg (Real.log_nonneg h9) 3
          nlinarith [h7, h8]
        linarith [hsplit, h5, h6]
      have h11 : Real.log (|t| + 2) ^ 3 ≤ (|t| + 4) ^ 3 := hlog2
      have h12 : (1 : ℝ) + Real.log (|t| + 2) ^ 3 ≤ 2 * (|t| + 4) ^ 3 := by linarith
      have hlog3nn : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
        have h9 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
        exact pow_nonneg (Real.log_nonneg h9) 3
      have h13 : (3 + |t|) * (1 + Real.log (|t| + 2) ^ 3) ≤
          2 * (|t| + 4) * (|t| + 4) ^ 3 := by
        have h14 : (3 + |t|) ≤ (|t| + 4) := by linarith [abs_nonneg t]
        calc (3 + |t|) * (1 + Real.log (|t| + 2) ^ 3)
            ≤ (|t| + 4) * (2 * (|t| + 4) ^ 3) :=
              mul_le_mul h14 h12
                (by linarith : (0 : ℝ) ≤ 1 + Real.log (|t| + 2) ^ 3)
                (by linarith [abs_nonneg t] : (0 : ℝ) ≤ |t| + 4)
          _ = 2 * (|t| + 4) * (|t| + 4) ^ 3 := by ring
      have h15 : (0 : ℝ) ≤ 8 * (Real.log N ^ 3 + 1) := by positivity
      calc (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3
          ≤ (3 + |t|) * (8 * (Real.log N ^ 3 + 1) * (1 + Real.log (|t| + 2) ^ 3)) := by
            exact mul_le_mul_of_nonneg_left h4 h3
        _ = 8 * (Real.log N ^ 3 + 1) * ((3 + |t|) * (1 + Real.log (|t| + 2) ^ 3)) := by
            ring
        _ ≤ 8 * (Real.log N ^ 3 + 1) * (2 * (|t| + 4) * (|t| + 4) ^ 3) := by
            exact mul_le_mul_of_nonneg_left h13 h15
        _ = 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 := by ring
    have h16 : (|t| + 4) ^ 4 ≤ (|t| + 4) ^ 5 := by
      have h18 : (|t| + 4) ^ 4 * 1 ≤ (|t| + 4) ^ 4 * (|t| + 4) :=
        mul_le_mul_of_nonneg_left h17 (by positivity)
      calc (|t| + 4) ^ 4 = (|t| + 4) ^ 4 * 1 := by ring
        _ ≤ (|t| + 4) ^ 4 * (|t| + 4) := h18
        _ = (|t| + 4) ^ 5 := by ring
    have hexp1 : Real.exp (-(δ * |t|)) = Real.exp (-(δ / 2) * |t|) * Real.exp (-(δ / 2) * |t|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hC2 : (0 : ℝ) ≤ 16 * (Real.log N ^ 3 + 1) * K := by positivity
    have hexpbound : Real.exp (-(δ * |t|)) ≤ Real.exp (-(δ / 2) * |t|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg t, hδpos]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith [abs_nonneg t]) hlogpos)
        (Real.exp_pos _).le)]
    calc (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 * Real.exp (-(δ * |t|))
        ≤ 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 * Real.exp (-(δ * |t|)) := by
          apply mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
      _ ≤ (16 * (Real.log N ^ 3 + 1) * K * Real.exp (δ / 2 * |t|)) * Real.exp (-(δ * |t|)) := by
          have hp : (0 : ℝ) ≤ Real.exp (-(δ * |t|)) := (Real.exp_pos _).le
          have hq : (|t| + 4) ^ 4 ≤ (|t| + 4) ^ 5 := h16
          have hr : (|t| + 4) ^ 5 ≤ K * Real.exp (δ / 2 * |t|) := hK t
          have hs : 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 ≤
              16 * (Real.log N ^ 3 + 1) * (K * Real.exp (δ / 2 * |t|)) := by
            have h0 : (0 : ℝ) ≤ 16 * (Real.log N ^ 3 + 1) := by positivity
            calc 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4
                ≤ 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 5 := by
                  exact mul_le_mul_of_nonneg_left hq h0
              _ ≤ 16 * (Real.log N ^ 3 + 1) * (K * Real.exp (δ / 2 * |t|)) := by
                  exact mul_le_mul_of_nonneg_left hr h0
          calc 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 * Real.exp (-(δ * |t|))
              ≤ 16 * (Real.log N ^ 3 + 1) * (K * Real.exp (δ / 2 * |t|)) *
                  Real.exp (-(δ * |t|)) := by
                exact mul_le_mul_of_nonneg_right hs hp
            _ = (16 * (Real.log N ^ 3 + 1) * K * Real.exp (δ / 2 * |t|)) *
                  Real.exp (-(δ * |t|)) := by ring
      _ = 16 * (Real.log N ^ 3 + 1) * K * Real.exp (-(δ / 2) * |t|) := by
          rw [mul_assoc (16 * (Real.log N ^ 3 + 1) * K), ← Real.exp_add]
          congr 1
          ring

/-- On the outer range up to two the Mellin transform is continuous in the outer
variable, by dominated convergence against the outer kernel majorant. -/
private lemma outer_continuousOn519 (N : ℕ) (hN : 3 ≤ N) (M : ℝ → ℂ) (hM : Continuous M)
    (B0 : ℝ) (hB0 : 0 ≤ B0)
    (hbound : ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :
    ContinuousOn (fun α => mellinU519 N M α) (Set.Icc (4 / (N : ℝ)) 2) := by
  set δ := Real.arctan (1 / (4 * Real.pi * (N : ℝ))) with hδdef
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hW := outer_weight_integrable519 N hN2
  simp only [← hδdef] at hW
  have hBint : Integrable (fun t : ℝ => B0 * (Real.exp 1 * Real.sqrt N *
      Real.sqrt (2 * Real.pi)) * ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
        Real.exp (-(δ * |t|)))) := by
    have := hW.const_mul (B0 * (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using this
  have hmain : ContinuousOn (fun α => ∫ t : ℝ, mellinKernel519 N α t * M t)
      (Set.Icc (4 / (N : ℝ)) 2) := by
    refine MeasureTheory.continuousOn_of_dominated (μ := volume) ?_ ?_ hBint ?_
    · intro α _
      exact ((continuous_mellin_integrand519 N hN M hM).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro α hα
      filter_upwards with t
      have hk := outer_kernel_bound519 N hN α t hα.1 hα.2
      rw [norm_mul]
      have hlog3 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
        have h5 : (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by
          have h6 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
          have h7 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
          nlinarith [h6, h7, abs_nonneg t]
        exact pow_nonneg (Real.log_nonneg h5) 3
      have hstep := mul_le_mul hk (hbound t) (norm_nonneg (M t)) (by positivity)
      calc ‖mellinKernel519 N α t‖ * ‖M t‖
          ≤ (Real.exp 1 * Real.sqrt N * (Real.sqrt (2 * Real.pi) * (3 + |t|)) *
              Real.exp (-(δ * |t|))) *
            (B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := hstep
        _ = B0 * (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)) *
              ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
                Real.exp (-(δ * |t|))) := by
            rw [hδdef]; ring
    · filter_upwards with t
      exact ((continuous_mellin_integrand519 N hN M hM).comp
        (continuous_id.prodMk continuous_const)).continuousOn
  have heq : (fun α => mellinU519 N M α) = fun α =>
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, mellinKernel519 N α t * M t := by
    funext α
    simp only [mellinU519, mellinKernel519]
  rw [heq]
  exact hmain.const_mul _

/-- LEAF. Integrability half of the outer interval.  For a positive line constant
B0, once N is large enough, and for every inverse radius R between one and the
two sevenths power of N, every continuous coefficient obeying the cubic
logarithmic line bound has square norm integrable over the outer interval from
four over N to one over R.  This is the first conjunct alone: it carries no
constant, no factor of N over R and no power of the logarithm, so it is strictly
weaker than the sealed estimate. -/
theorem outer_square_integrable519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
            (Set.Icc (4 / (N : ℝ)) (1 / R)) := by
  refine ⟨127, ?_⟩
  intro N hN R hR _ M hM
  have hN3 : 3 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hcont := outer_continuousOn519 N hN3 M hM.1 B0 hB0.le hM.2
  have hcont2 : ContinuousOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      (Set.Icc (4 / (N : ℝ)) 2) := hcont.norm.pow 2
  have hint : IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      (Set.Icc (4 / (N : ℝ)) 2) := hcont2.integrableOn_compact isCompact_Icc
  refine hint.mono_set ?_
  apply Set.Icc_subset_Icc le_rfl
  have hR1 : 1 / R ≤ 1 := by
    rw [div_le_one (by linarith : (0 : ℝ) < R)]
    exact hR
  linarith


/-! ### The 519 and 442 objects are the same objects -/

private lemma mellinLine519_eq1622 (N : ℕ) (t : ℝ) :
    mellinLine519 N t = LeanLab.Linnik1951.mellinLine1622 N t := rfl

private lemma mellinKernel519_eq442 (N : ℕ) (α t : ℝ) :
    mellinKernel519 N α t = LeanLab.Linnik1951.mellinKernel442 N α t := rfl

private lemma mellinU519_eq1622 (N : ℕ) (M : ℝ → ℂ) (α : ℝ) :
    mellinU519 N M α = LeanLab.Linnik1951.mellinU1622 N M α := rfl

private lemma truncated519_eq487 (N : ℕ) (R : ℝ) (M : ℝ → ℂ) (α : ℝ) :
    LeanLab.Linnik1951.truncatedMellin487 N R M α =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          mellinKernel519 N α t * M t := rfl

/-! ### The sharp polar bound for the Mellin kernel -/

/-- `sin (arctan (1 / c)) = 1 / sqrt (1 + c ^ 2)` for positive `c`. -/
private lemma sin_arctan_inv_f673 {c : ℝ} (hc : 0 < c) :
    Real.sin (Real.arctan (1 / c)) = 1 / Real.sqrt (1 + c ^ 2) := by
  rw [Real.sin_arctan]
  have h2 : (1 : ℝ) + (1 / c) ^ 2 = (c ^ 2 + 1) / c ^ 2 := by
    field_simp
  rw [h2, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hc.le]
  field_simp
  ring

/-- On the outer range the argument of the Mellin base is at most
`pi / 2 - arctan (1 / (2 pi N alpha))`. -/
private lemma arg_base_bound_f673 (N : ℕ) (hN : 2 ≤ N) (α : ℝ)
    (hα0 : 4 / (N : ℝ) ≤ α) :
    |Complex.arg (((1 / (N : ℝ) : ℝ) : ℂ) +
        ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I)| ≤
      Real.pi / 2 - Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hc : (0 : ℝ) < 2 * Real.pi * (N : ℝ) * α := by
    have h1 : (0 : ℝ) < 2 * Real.pi * (N : ℝ) := by positivity
    have h2 : (0 : ℝ) < α := lt_of_lt_of_le (by positivity) hα0
    exact mul_pos h1 h2
  set c : ℝ := 2 * Real.pi * (N : ℝ) * α with hcdef
  set δ : ℝ := Real.arctan (1 / c) with hδdef
  have hδpos : 0 < δ := Real.arctan_pos.mpr (by positivity)
  have hδlt : δ < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzim : z.im = 2 * Real.pi * α := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  -- `‖z‖ = (1/N) sqrt (1 + c^2)`
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hIm : z.im = c / (N : ℝ) := by
    rw [hzim, hcdef]; field_simp
  have hnorm : ‖z‖ = (1 / (N : ℝ)) * Real.sqrt (1 + c ^ 2) := by
    have h2 : ‖z‖ ^ 2 = ((1 / (N : ℝ)) * Real.sqrt (1 + c ^ 2)) ^ 2 := by
      rw [hsq, hzre, hIm, mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
    calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
      _ = _ := by rw [h2, Real.sqrt_sq (by positivity)]
  have hcos : Real.sin δ ≤ z.re / ‖z‖ := by
    rw [hδdef, sin_arctan_inv_f673 hc, hzre, hnorm]
    have hsimp : (1 / (N : ℝ)) / ((1 / (N : ℝ)) * Real.sqrt (1 + c ^ 2)) =
        1 / Real.sqrt (1 + c ^ 2) := by
      field_simp
    rw [hsimp]
  have hθmem : Real.pi / 2 - δ ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hargmem : |Complex.arg z| ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩
  have hcosarg : Real.cos |Complex.arg z| = z.re / ‖z‖ := by
    rw [Real.cos_abs, Complex.cos_arg hz]
  rw [← Real.cos_pi_div_two_sub δ, ← hcosarg] at hcos
  exact (Real.strictAntiOn_cos.le_iff_ge hθmem hargmem).mp hcos

/-- The power factor of the Mellin kernel decays with the sharp outer rate. -/
private lemma cpow_bound_f673 (N : ℕ) (hN : 3 ≤ N) (α t : ℝ)
    (hα0 : 4 / (N : ℝ) ≤ α) :
    ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine519 N t))‖ ≤
      Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)))) := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set δ : ℝ := Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) with hδdef
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  have hnorm_ge : 1 / (N : ℝ) ≤ ‖z‖ := by
    calc 1 / (N : ℝ) = |z.re| := by
          rw [hzre, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have harg : |Complex.arg z| ≤ Real.pi / 2 - δ := by
    rw [hδdef, hzdef]
    exact arg_base_bound_f673 N hN2 α hα0
  have hsre : (mellinLine519 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine519, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsim : (mellinLine519 N t).im = t := by
    simp only [mellinLine519, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hσ : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := by positivity
  have hmul : (1 / 2 + 1 / Real.log N) * Real.log N = Real.log N / 2 + 1 := by
    field_simp
  have hlogz : -(1 / 2 + 1 / Real.log N) * Real.log ‖z‖ ≤ Real.log N / 2 + 1 := by
    have h1 : Real.log (1 / (N : ℝ)) ≤ Real.log ‖z‖ :=
      Real.log_le_log (by positivity) hnorm_ge
    have h2 : Real.log (1 / (N : ℝ)) = -Real.log N := by
      rw [Real.log_div one_ne_zero hNr.ne']; simp
    nlinarith [h1, h2, hmul, hσ]
  have hargpos : 0 ≤ Complex.arg z := by
    rw [Complex.arg_nonneg_iff]
    rw [hzdef]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero]
    have h4 : (0 : ℝ) < 4 / (N : ℝ) := by positivity
    nlinarith [Real.pi_pos, hα0, h4]
  have htarg : t * Complex.arg z ≤ |t| * (Real.pi / 2 - δ) := by
    have hupper : Complex.arg z ≤ Real.pi / 2 - δ := (abs_le.mp harg).2
    rcases lt_or_ge t 0 with ht | ht
    · rw [abs_of_neg ht]
      have h3 : t * Complex.arg z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht.le hargpos
      nlinarith [h3]
    · rw [abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left hupper ht
  have hkey : (Complex.log z * (-(mellinLine519 N t))).re ≤
      Real.log N / 2 + 1 + |t| * (Real.pi / 2 - δ) := by
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im,
      hsre, hsim]
    nlinarith [hlogz, htarg]
  rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp]
  refine (Real.exp_le_exp.mpr hkey).trans (le_of_eq ?_)
  have hexp_logN : Real.exp (Real.log N / 2) = Real.sqrt N := by
    rw [← Real.log_sqrt hNr.le, Real.exp_log (Real.sqrt_pos.mpr hNr)]
  rw [Real.exp_add, Real.exp_add, hexp_logN]
  ring

/-- The sharp kernel bound on the outer range. -/
private lemma kernel_bound_f673 (N : ℕ) (hN : 3 ≤ N) (α t : ℝ)
    (hα0 : 4 / (N : ℝ) ≤ α) :
    ‖mellinKernel519 N α t‖ ≤
      Real.exp 1 * Real.sqrt N * (Real.sqrt (2 * Real.pi) * (3 + |t|)) *
        Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|)) := by
  have hcp := cpow_bound_f673 N hN α t hα0
  have hg := gamma_mellin_line519 N hN t
  have hExp : Real.exp (|t| * (Real.pi / 2 - Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)))) *
      Real.exp (-(Real.pi * |t| / 2)) =
      Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold mellinKernel519
  rw [norm_mul]
  calc ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine519 N t))‖ * ‖Complex.Gamma (mellinLine519 N t)‖
      ≤ (Real.exp 1 * Real.sqrt N *
            Real.exp (|t| * (Real.pi / 2 - Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α))))) *
          (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) := by
        apply mul_le_mul hcp hg (norm_nonneg _) (by positivity)
    _ = Real.exp 1 * Real.sqrt N * (Real.sqrt (2 * Real.pi) * (3 + |t|)) *
          Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|)) := by
        rw [← hExp]
        ring

/-! ### The arithmetic weight: domination by a fourth power -/

/-- The cubic logarithmic weight is dominated by a fourth power. -/
private lemma log_weight_le_f673 (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hNr
  have hsplit := log_cube_split519 N t hN
  have hlog2 : Real.log (|t| + 2) ^ 3 ≤ (|t| + 4) ^ 3 := by
    have h1 : Real.log (|t| + 2) ≤ |t| + 4 :=
      (Real.log_le_self (by linarith [abs_nonneg t])).trans (by linarith)
    have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
    exact pow_le_pow_left₀ h2 h1 3
  have h4 : Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      8 * (Real.log N ^ 3 + 1) * (1 + Real.log (|t| + 2) ^ 3) := by
    have h5 : 8 * Real.log N ^ 3 ≤ 8 * (Real.log N ^ 3 + 1) := by linarith
    have h8 : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 :=
      pow_nonneg (Real.log_nonneg (by linarith [abs_nonneg t])) 3
    have h7 : (1 : ℝ) ≤ Real.log N ^ 3 + 1 := by linarith [pow_nonneg hlogN 3]
    have h6 : 8 * Real.log (|t| + 2) ^ 3 ≤
        8 * (Real.log N ^ 3 + 1) * Real.log (|t| + 2) ^ 3 := by nlinarith [h7, h8]
    linarith [hsplit, h5, h6]
  have h12 : (1 : ℝ) + Real.log (|t| + 2) ^ 3 ≤ 2 * (|t| + 4) ^ 3 := by
    have h9 : (1 : ℝ) ≤ (|t| + 4) ^ 3 := by
      have h17 : (1 : ℝ) ≤ |t| + 4 := by linarith [abs_nonneg t]
      calc (1 : ℝ) = 1 ^ 3 := by ring
        _ ≤ (|t| + 4) ^ 3 := pow_le_pow_left₀ (by norm_num) h17 3
    linarith [hlog2, h9]
  have hlog3nn : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 :=
    pow_nonneg (Real.log_nonneg (by linarith [abs_nonneg t])) 3
  have h13 : (3 + |t|) * (1 + Real.log (|t| + 2) ^ 3) ≤ 2 * (|t| + 4) * (|t| + 4) ^ 3 := by
    have h14 : (3 + |t|) ≤ (|t| + 4) := by linarith [abs_nonneg t]
    have h15 : (0 : ℝ) ≤ 1 + Real.log (|t| + 2) ^ 3 := by linarith
    calc (3 + |t|) * (1 + Real.log (|t| + 2) ^ 3)
        ≤ (|t| + 4) * (2 * (|t| + 4) ^ 3) :=
          mul_le_mul h14 h12 h15
            (by linarith [abs_nonneg t] : (0 : ℝ) ≤ |t| + 4)
      _ = 2 * (|t| + 4) * (|t| + 4) ^ 3 := by ring
  have h3 : (0 : ℝ) ≤ 3 + |t| := by linarith [abs_nonneg t]
  have h15 : (0 : ℝ) ≤ 8 * (Real.log N ^ 3 + 1) := by positivity
  calc (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3
      ≤ (3 + |t|) * (8 * (Real.log N ^ 3 + 1) * (1 + Real.log (|t| + 2) ^ 3)) :=
        mul_le_mul_of_nonneg_left h4 h3
    _ = 8 * (Real.log N ^ 3 + 1) * ((3 + |t|) * (1 + Real.log (|t| + 2) ^ 3)) := by ring
    _ ≤ 8 * (Real.log N ^ 3 + 1) * (2 * (|t| + 4) * (|t| + 4) ^ 3) :=
        mul_le_mul_of_nonneg_left h13 h15
    _ = 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 := by ring

/-- A fourth power is dominated by `exp (e |t|)` for every `e > 0`, with an
explicit constant. -/
private lemma pow_four_le_exp_f673 (e : ℝ) (he : 0 < e) (t : ℝ) :
    (|t| + 4) ^ 4 ≤ (24 * (1 / e) ^ 4 * Real.exp (4 * e)) * Real.exp (e * |t|) := by
  have hv : (0 : ℝ) ≤ e * (|t| + 4) := by positivity
  have h1 : (e * (|t| + 4)) ^ 4 ≤ 24 * Real.exp (e * (|t| + 4)) := by
    have h := Real.pow_div_factorial_le_exp (x := e * (|t| + 4)) hv 4
    norm_num at h
    calc (e * (|t| + 4)) ^ 4 = (e * (|t| + 4)) ^ 4 / 24 * 24 := by ring
      _ ≤ Real.exp (e * (|t| + 4)) * 24 :=
          mul_le_mul_of_nonneg_right h (by norm_num)
      _ = 24 * Real.exp (e * (|t| + 4)) := by ring
  have h2 : (|t| + 4) ^ 4 = (1 / e) ^ 4 * (e * (|t| + 4)) ^ 4 := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hExp : Real.exp (e * (|t| + 4)) = Real.exp (4 * e) * Real.exp (e * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h2]
  calc (1 / e) ^ 4 * (e * (|t| + 4)) ^ 4
      ≤ (1 / e) ^ 4 * (24 * Real.exp (e * (|t| + 4))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 24 * (1 / e) ^ 4 * Real.exp (4 * e) * Real.exp (e * |t|) := by rw [hExp]; ring

/-- `exp (-b |t|)` is integrable on the line. -/
private lemma exp_neg_abs_integrable_f673 (b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * |t|)) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -b) (by linarith) (0 : ℝ)).congr_fun ?_
      measurableSet_Ioi
    intro t ht
    show Real.exp (-b * t) = Real.exp (-b * |t|)
    rw [abs_of_pos ht]
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := b) hb (0 : ℝ)).congr_fun ?_ measurableSet_Iic
    intro t ht
    show Real.exp (b * t) = Real.exp (-b * |t|)
    rw [abs_of_nonpos ht]
    ring_nf
  have h3 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0 ∪ Set.Iic 0) :=
    integrableOn_union.mpr ⟨h1, h2⟩
  rw [Set.Ioi_union_Iic] at h3
  exact integrableOn_univ.mp h3

/-- The arithmetic weight of the kernel is integrable for every positive rate. -/
private lemma weight_integrable_f673 (N : ℕ) (hN : 2 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
      Real.exp (-(δ * |t|))) := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hNr
  have hbase : Integrable (fun t : ℝ => Real.exp (-(δ / 2) * |t|)) :=
    exp_neg_abs_integrable_f673 _ (by linarith)
  refine Integrable.mono' (hbase.const_mul
    (16 * (Real.log N ^ 3 + 1) * (24 * (1 / (δ / 2)) ^ 4 * Real.exp (4 * (δ / 2))))) ?_ ?_
  · have harg : Continuous fun t : ℝ => (N : ℝ) * (|t| + 2) :=
      continuous_const.mul (continuous_abs.add continuous_const)
    have hlog : Continuous fun t : ℝ => Real.log ((N : ℝ) * (|t| + 2)) :=
      harg.log (fun t => ne_of_gt (by positivity))
    have hexp : Continuous fun t : ℝ => Real.exp (-(δ * |t|)) :=
      Real.continuous_exp.comp (by fun_prop)
    exact (((continuous_const.add continuous_abs).mul (hlog.pow 3)).mul hexp).aestronglyMeasurable
  · filter_upwards with t
    have hlog3 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
      have h5 : (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by
        have h6 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
        nlinarith [h6, hNr, abs_nonneg t]
      exact pow_nonneg (Real.log_nonneg h5) 3
    have hnn : (0 : ℝ) ≤ (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
        Real.exp (-(δ * |t|)) := by
      exact mul_nonneg (mul_nonneg (by linarith [abs_nonneg t]) hlog3) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hkey := log_weight_le_f673 N hN t
    have hKt := pow_four_le_exp_f673 (δ / 2) (by linarith) t
    have hfac : (0 : ℝ) ≤ 16 * (Real.log N ^ 3 + 1) := by
      have h3 : (0 : ℝ) ≤ Real.log N ^ 3 := pow_nonneg hlogN 3
      linarith
    have hstep : (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 * Real.exp (-(δ * |t|)) ≤
        16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 * Real.exp (-(δ * |t|)) :=
      mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
    have hstep2 : 16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4 * Real.exp (-(δ * |t|)) ≤
        16 * (Real.log N ^ 3 + 1) *
          ((24 * (1 / (δ / 2)) ^ 4 * Real.exp (4 * (δ / 2))) * Real.exp (δ / 2 * |t|)) *
          Real.exp (-(δ * |t|)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left hKt hfac
    refine hstep.trans (hstep2.trans (le_of_eq ?_))
    have hex : Real.exp (δ / 2 * |t|) * Real.exp (-(δ * |t|)) =
        Real.exp (-(δ / 2 * |t|)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc 16 * (Real.log N ^ 3 + 1) *
          ((24 * (1 / (δ / 2)) ^ 4 * Real.exp (4 * (δ / 2))) * Real.exp (δ / 2 * |t|)) *
          Real.exp (-(δ * |t|))
        = 16 * (Real.log N ^ 3 + 1) * (24 * (1 / (δ / 2)) ^ 4 * Real.exp (4 * (δ / 2))) *
            (Real.exp (δ / 2 * |t|) * Real.exp (-(δ * |t|))) := by ring
      _ = 16 * (Real.log N ^ 3 + 1) * (24 * (1 / (δ / 2)) ^ 4 * Real.exp (4 * (δ / 2))) *
            Real.exp (-(δ / 2) * |t|) := by
          rw [hex]
          congr 1
          ring

/-- The half line integral of the weight with the sharp rate, for a rate at most two. -/
private lemma half_line_bound_f673 (N : ℕ) (hN : 2 ≤ N) {c T u : ℝ} (hc : 0 < c)
    (hc2 : c ≤ 2) (hT : 0 ≤ T) (hu : 1 / c ≤ u) :
    (∫ t in Set.Ioi T, (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
        Real.exp (-(c * |t|))) ≤
      10 ^ 8 * (Real.log N ^ 3 + 1) * u ^ 5 * Real.exp (-(c * T / 2)) := by
  have hc4 : (0 : ℝ) < c / 4 := by linarith
  have hlogN : (0 : ℝ) ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlog1 : (0 : ℝ) ≤ Real.log N ^ 3 := pow_nonneg hlogN 3
  set K : ℝ := 24 * (1 / (c / 4)) ^ 4 * Real.exp (4 * (c / 4)) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  have hK : ∀ t : ℝ, (|t| + 4) ^ 4 ≤ K * Real.exp (c / 4 * |t|) := by
    intro t
    rw [hKdef]
    exact pow_four_le_exp_f673 (c / 4) (by linarith) t
  -- pointwise domination on the tail
  have hpoint : ∀ t ∈ Set.Ioi T,
      (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 * Real.exp (-(c * |t|)) ≤
        16 * (Real.log N ^ 3 + 1) * K * Real.exp (-(c * T / 2)) *
          Real.exp (-(c / 4) * |t|) := by
    intro t ht
    have htT : T ≤ t := le_of_lt ht
    have ht0 : (0 : ℝ) ≤ t := le_trans hT htT
    have habs : |t| = t := abs_of_nonneg ht0
    have hkey := log_weight_le_f673 N hN t
    have hKt : (|t| + 4) ^ 4 ≤ K * Real.exp (c / 4 * |t|) := hK t
    have hfac : (0 : ℝ) ≤ 16 * (Real.log N ^ 3 + 1) := by positivity
    have hexpstep : Real.exp (-(c * |t|)) * Real.exp (c / 4 * |t|) ≤
        Real.exp (-(c * T / 2)) * Real.exp (-(c / 4) * |t|) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : T ≤ |t| := by rw [habs]; exact htT
      nlinarith [hc, h1]
    calc (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 * Real.exp (-(c * |t|))
        ≤ (16 * (Real.log N ^ 3 + 1) * (|t| + 4) ^ 4) * Real.exp (-(c * |t|)) :=
          mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
      _ ≤ (16 * (Real.log N ^ 3 + 1) * (K * Real.exp (c / 4 * |t|))) *
            Real.exp (-(c * |t|)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left hKt hfac
      _ = 16 * (Real.log N ^ 3 + 1) * K *
            (Real.exp (-(c * |t|)) * Real.exp (c / 4 * |t|)) := by ring
      _ ≤ 16 * (Real.log N ^ 3 + 1) * K *
            (Real.exp (-(c * T / 2)) * Real.exp (-(c / 4) * |t|)) :=
          mul_le_mul_of_nonneg_left hexpstep (by positivity)
      _ = 16 * (Real.log N ^ 3 + 1) * K * Real.exp (-(c * T / 2)) *
            Real.exp (-(c / 4) * |t|) := by ring
  have hIntW : IntegrableOn (fun t : ℝ => (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
      Real.exp (-(c * |t|))) (Set.Ioi T) := (weight_integrable_f673 N hN hc).integrableOn
  have hbase : IntegrableOn (fun t : ℝ => Real.exp (-(c / 4) * |t|)) (Set.Ioi T) := by
    have h := (integrableOn_exp_mul_Ioi (a := -(c / 4)) (by linarith) T :
      IntegrableOn (fun t : ℝ => Real.exp (-(c / 4) * t)) (Set.Ioi T))
    refine h.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [abs_of_pos (lt_of_le_of_lt hT ht)]
  have hIntG : IntegrableOn (fun t : ℝ => 16 * (Real.log N ^ 3 + 1) * K *
      Real.exp (-(c * T / 2)) * Real.exp (-(c / 4) * |t|)) (Set.Ioi T) :=
    hbase.const_mul _
  have hmono := setIntegral_mono_on hIntW hIntG measurableSet_Ioi hpoint
  have hIoi : (∫ t in Set.Ioi T, Real.exp (-(c / 4) * |t|)) ≤ 4 / c := by
    have hcongr : (∫ t in Set.Ioi T, Real.exp (-(c / 4) * |t|)) =
        (∫ t in Set.Ioi T, Real.exp (-(c / 4) * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      simp only [abs_of_pos (lt_of_le_of_lt hT ht)]
    rw [hcongr]
    have hbase0 : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(c / 4) * t)) = 4 / c := by
      have h := integral_exp_mul_Ioi (a := -(c / 4)) (by linarith : -(c / 4) < 0) (0 : ℝ)
      have h1 : Real.exp (-(c / 4) * 0) = 1 := by simp
      rw [h, h1]
      field_simp
    rw [← hbase0]
    have hi1 : IntegrableOn (fun t : ℝ => Real.exp (-(c / 4) * t)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (a := -(c / 4)) (by linarith) 0
    have hi2 : IntegrableOn (fun t : ℝ => Real.exp (-(c / 4) * t)) (Set.Ioi T) :=
      integrableOn_exp_mul_Ioi (a := -(c / 4)) (by linarith) T
    have hadd := intervalIntegral.integral_interval_add_Ioi
      (f := fun t : ℝ => Real.exp (-(c / 4) * t)) (a := (0 : ℝ)) (b := T) hi1 hi2
    have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..T, Real.exp (-(c / 4) * t) :=
      intervalIntegral.integral_nonneg hT (fun t _ => (Real.exp_pos _).le)
    linarith [hadd, hnonneg]
  have hKg : (∫ t in Set.Ioi T, 16 * (Real.log N ^ 3 + 1) * K *
        Real.exp (-(c * T / 2)) * Real.exp (-(c / 4) * |t|)) =
      16 * (Real.log N ^ 3 + 1) * K * Real.exp (-(c * T / 2)) *
        (∫ t in Set.Ioi T, Real.exp (-(c / 4) * |t|)) := by
    rw [← integral_const_mul]
  refine hmono.trans ?_
  rw [hKg]
  -- the explicit constant
  have hlog1 : (0 : ℝ) ≤ Real.log N ^ 3 + 1 := by
    have h0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have : (0 : ℝ) ≤ Real.log N ^ 3 := by positivity
    linarith
  have hexp9 : Real.exp (4 * (c / 4)) ≤ 9 := by
    have hc4 : 4 * (c / 4) = c := by ring
    rw [hc4]
    have h1 : Real.exp c ≤ Real.exp 2 := Real.exp_le_exp.mpr hc2
    have h2 : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    have h1p : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    nlinarith [h1, h2, h3, h1p]
  have hscale : (1 : ℝ) / (c / 4) = 4 * (1 / c) := by field_simp
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le (by positivity) hu
  have h4c : 4 * (1 / c) ≤ 4 * u := by
    have : (0 : ℝ) < 4 := by norm_num
    nlinarith [hu, hc]
  have h4c0 : (0 : ℝ) ≤ 4 * (1 / c) := by positivity
  have hpow : (4 * (1 / c)) ^ 4 ≤ (4 * u) ^ 4 := pow_le_pow_left₀ h4c0 h4c 4
  have hKle : 16 * K * (4 / c) ≤ 3538944 * u ^ 5 := by
    rw [hKdef, hscale]
    have h4c' : (4:ℝ) / c = 4 * (1 / c) := by field_simp
    rw [h4c']
    have h384 : (0 : ℝ) ≤ 384 := by norm_num
    have hmul : 16 * (24 * (4 * (1 / c)) ^ 4 * Real.exp (4 * (c / 4))) * (4 * (1 / c)) =
        384 * ((4 * (1 / c)) ^ 4 * (4 * (1 / c))) * Real.exp (4 * (c / 4)) := by ring
    rw [hmul]
    have h1 : (4 * (1 / c)) ^ 4 * (4 * (1 / c)) ≤ (4 * u) ^ 4 * (4 * u) := by
      have h2 : (0 : ℝ) ≤ 4 * u := by positivity
      exact mul_le_mul hpow h4c (by positivity) (by positivity)
    have h2 : (0 : ℝ) ≤ (4 * u) ^ 4 * (4 * u) := by positivity
    have h3 : 384 * ((4 * u) ^ 4 * (4 * u)) * 9 = 3538944 * u ^ 5 := by ring
    have h4 : 384 * ((4 * (1 / c)) ^ 4 * (4 * (1 / c))) * Real.exp (4 * (c / 4)) ≤
        384 * ((4 * u) ^ 4 * (4 * u)) * 9 := by
      have h5 : (0 : ℝ) ≤ 384 * ((4 * (1 / c)) ^ 4 * (4 * (1 / c))) := by positivity
      have h6 : (0 : ℝ) ≤ 384 * ((4 * u) ^ 4 * (4 * u)) := by positivity
      nlinarith [h1, h2, hexp9, h5, h6]
    linarith [h4, h3]
  have hmul2 : 16 * (Real.log N ^ 3 + 1) * K * Real.exp (-(c * T / 2)) * (4 / c) ≤
      3538944 * u ^ 5 * ((Real.log N ^ 3 + 1) * Real.exp (-(c * T / 2))) := by
    have h4cpos : (0 : ℝ) < 4 / c := by positivity
    have hgroup : 16 * (Real.log N ^ 3 + 1) * K * Real.exp (-(c * T / 2)) * (4 / c) =
        (16 * K * (4 / c)) * ((Real.log N ^ 3 + 1) * Real.exp (-(c * T / 2))) := by ring
    rw [hgroup]
    exact mul_le_mul_of_nonneg_right hKle (by positivity)
  refine (mul_le_mul_of_nonneg_left hIoi (by positivity)).trans ?_
  refine hmul2.trans ?_
  have hfin : 3538944 * u ^ 5 * ((Real.log N ^ 3 + 1) * Real.exp (-(c * T / 2))) ≤
      10 ^ 8 * (Real.log N ^ 3 + 1) * u ^ 5 * Real.exp (-(c * T / 2)) := by
    have hu5 : (0 : ℝ) ≤ u ^ 5 := by positivity
    have hnn : (0 : ℝ) ≤ (Real.log N ^ 3 + 1) * Real.exp (-(c * T / 2)) := by positivity
    have hnum : (3538944 : ℝ) ≤ 10 ^ 8 := by norm_num
    calc 3538944 * u ^ 5 * ((Real.log N ^ 3 + 1) * Real.exp (-(c * T / 2)))
        = 3538944 * (u ^ 5 * ((Real.log N ^ 3 + 1) * Real.exp (-(c * T / 2)))) := by ring
      _ ≤ 10 ^ 8 * (u ^ 5 * ((Real.log N ^ 3 + 1) * Real.exp (-(c * T / 2)))) :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = 10 ^ 8 * (Real.log N ^ 3 + 1) * u ^ 5 * Real.exp (-(c * T / 2)) := by ring
  exact hfin

/-! ### The sharp rate and its size on the outer range -/

/-- `arctan y` is at least `y / 2` on `(0, 1]`. -/
private lemma arctan_ge_self_div_two_f673 {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    y / 2 ≤ Real.arctan y := by
  have hsin : Real.sin (Real.arctan y) = y / Real.sqrt (1 + y ^ 2) := Real.sin_arctan y
  have h1 : (0 : ℝ) < Real.arctan y := Real.arctan_pos.mpr hy0
  have h3 : Real.sin (Real.arctan y) ≤ Real.arctan y := (Real.sin_lt h1).le
  have h4 : y / 2 ≤ Real.sin (Real.arctan y) := by
    rw [hsin]
    have hpos : (0 : ℝ) < Real.sqrt (1 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
    rw [le_div_iff₀ hpos]
    have h5 : Real.sqrt (1 + y ^ 2) ≤ 2 := by
      have h6 : 1 + y ^ 2 ≤ 4 := by nlinarith [sq_nonneg y, hy0, hy1]
      calc Real.sqrt (1 + y ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h6
        _ = 2 := by norm_num
    nlinarith [h5, hy0]
  linarith

/-- On the outer range the sharp rate is at least `R / (4 pi N)`. -/
private lemma delta_lower_f673 (N : ℕ) (hN : 3 ≤ N) {R α : ℝ} (hR : 1 ≤ R)
    (hα0 : 4 / (N : ℝ) ≤ α) (hαR : α ≤ 1 / R) (hRN : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) :
    R / (4 * Real.pi * (N : ℝ)) ≤ Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hRpos : 0 < R := by linarith
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hα0
  have hRN' : R ≤ (N : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (2:ℝ)/7 ≤ 1)
    rw [Real.rpow_one] at h
    exact hRN.trans h
  have hy0 : (0 : ℝ) < R / (2 * Real.pi * (N : ℝ)) := by positivity
  have hy1 : R / (2 * Real.pi * (N : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h2 : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith [hRN', h2, Real.pi_pos, hNpos]
  have hRα : R ≤ 1 / α := by
    rw [le_div_iff₀ hαpos]
    rw [mul_comm]
    exact (le_div_iff₀ hRpos).mp hαR
  have hyα : R / (2 * Real.pi * (N : ℝ)) ≤ 1 / (2 * Real.pi * (N : ℝ) * α) := by
    have h1 : (0 : ℝ) < 2 * Real.pi * (N : ℝ) := by positivity
    have h2 : (1 : ℝ) / (2 * Real.pi * (N : ℝ) * α) = (1 / α) / (2 * Real.pi * (N : ℝ)) := by
      field_simp
    rw [h2]
    exact div_le_div_of_nonneg_right hRα h1.le
  calc R / (4 * Real.pi * (N : ℝ)) = R / (2 * Real.pi * (N : ℝ)) / 2 := by
        field_simp
        ring
    _ ≤ Real.arctan (R / (2 * Real.pi * (N : ℝ))) := arctan_ge_self_div_two_f673 hy0 hy1
    _ ≤ Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) :=
        (Real.arctan_le_arctan_iff).mpr hyα

/-- The rate times the truncation radius is at least `log N ^ 3 / (4 pi)`. -/
private lemma deltaT_f673 (N : ℕ) (hN : 3 ≤ N) {R α : ℝ} (hR : 1 ≤ R)
    (hα0 : 4 / (N : ℝ) ≤ α) (hαR : α ≤ 1 / R) (hRN : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) :
    Real.log N ^ 3 / (4 * Real.pi) ≤
      Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * ((N : ℝ) / R * Real.log N ^ 3) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hRpos : 0 < R := by linarith
  have hδ := delta_lower_f673 N hN hR hα0 hαR hRN
  have hT : (0 : ℝ) ≤ (N : ℝ) / R * Real.log N ^ 3 := by
    have : (0 : ℝ) ≤ Real.log N ^ 3 := by
      have h1 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
      positivity
    positivity
  have hkey : R / (4 * Real.pi * (N : ℝ)) * ((N : ℝ) / R * Real.log N ^ 3) =
      Real.log N ^ 3 / (4 * Real.pi) := by
    field_simp
  rw [← hkey]
  exact mul_le_mul_of_nonneg_right hδ hT

/-- The Mellin integrand is dominated by the arithmetic weight. -/
private lemma integrand_le_weight_f673 (N : ℕ) (hN : 3 ≤ N) {α B0 : ℝ}
    {M : ℝ → ℂ} (hα0 : 4 / (N : ℝ) ≤ α)
    (hM : Continuous M ∧ ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3)
    (t : ℝ) :
    ‖mellinKernel519 N α t * M t‖ ≤
      (B0 * (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi))) *
        ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
          Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))) := by
  have hk := kernel_bound_f673 N hN α t hα0
  have hstep := mul_le_mul hk (hM.2 t) (norm_nonneg (M t)) (by positivity)
  calc ‖mellinKernel519 N α t * M t‖
      = ‖mellinKernel519 N α t‖ * ‖M t‖ := norm_mul _ _
    _ ≤ (Real.exp 1 * Real.sqrt N * (Real.sqrt (2 * Real.pi) * (3 + |t|)) *
          Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))) *
          (B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := hstep
    _ = (B0 * (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi))) *
          ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
            Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))) := by ring

/-- The signed Mellin integrand is integrable on the line. -/
private lemma integrable_integrand_f673 (N : ℕ) (hN : 3 ≤ N) {α B0 : ℝ}
    {M : ℝ → ℂ} (hα0 : 4 / (N : ℝ) ≤ α)
    (hM : Continuous M ∧ ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :
    Integrable (fun t : ℝ => mellinKernel519 N α t * M t) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hα0
  have hδ : 0 < Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) :=
    Real.arctan_pos.mpr
      (div_pos one_pos (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 * Real.pi) hNpos) hαpos))
  refine Integrable.mono'
    (f := fun t : ℝ => mellinKernel519 N α t * M t)
    (g := fun t : ℝ => (B0 * (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi))) *
        ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
          Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))))
    ?_ ?_ ?_
  · exact (weight_integrable_f673 N (by omega) hδ).const_mul _
  · exact ((continuous_mellin_integrand519 N hN M hM.1).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => integrand_le_weight_f673 N hN hα0 hM t)

/-- An exponential lower bound for the constant part of the truncation majorant. -/
private lemma exp_const_lower_f673 {A : ℝ} (hA : 30 ≤ A) :
    (6 * 10 ^ 14 : ℝ) ≤ Real.exp (A ^ 3 / 104) := by
  have h2 : (900 : ℝ) ≤ A ^ 2 := by nlinarith [hA]
  have h3 : (27000 : ℝ) ≤ A ^ 3 := by nlinarith [h2, hA]
  have hx : (250 : ℝ) ≤ A ^ 3 / 104 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 104)]
    linarith
  have hexp : Real.exp (250 : ℝ) ≤ Real.exp (A ^ 3 / 104) := Real.exp_le_exp.mpr hx
  have hpow : (250 : ℝ) ^ 10 / (Nat.factorial 10) ≤ Real.exp (250 : ℝ) :=
    Real.pow_div_factorial_le_exp (x := (250 : ℝ)) (by norm_num) 10
  have hbig : (6 * 10 ^ 14 : ℝ) ≤ (250 : ℝ) ^ 10 / (Nat.factorial 10) := by
    norm_num [Nat.factorial]
  linarith

/-- The cube of the logarithm plus one is below a hundred-and-fourth of its
exponential. -/
private lemma exp_logcube_lower_f673 {A : ℝ} (hA : 30 ≤ A) :
    A ^ 3 + 1 ≤ Real.exp (A ^ 3 / 104) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have h13 : (1 : ℝ) ≤ A ^ 3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ A)
  have hle : A ^ 3 + 1 ≤ 2 * A ^ 3 := by linarith
  have hpos : (0 : ℝ) < A ^ 3 + 1 := by linarith
  have hlog1 : Real.log (A ^ 3 + 1) ≤ Real.log (2 * A ^ 3) := Real.log_le_log hpos hle
  have hlog2 : Real.log (2 * A ^ 3) = Real.log 2 + 3 * Real.log A := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlogA : Real.log A ≤ A := Real.log_le_self hA0.le
  have hlog2le : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
    linarith [Real.exp_one_gt_d9]
  have hmain : Real.log 2 + 3 * Real.log A ≤ A ^ 3 / 104 := by
    have h1 : Real.log 2 + 3 * Real.log A ≤ 1 + 3 * A := by linarith
    have h2 : (1 : ℝ) + 3 * A ≤ A ^ 3 / 104 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 104)]
      nlinarith [hA, sq_nonneg A]
    linarith
  have hfin : Real.log (A ^ 3 + 1) ≤ A ^ 3 / 104 := by
    rw [hlog2] at hlog1
    linarith
  exact (Real.log_le_iff_le_exp hpos).mp hfin

/-- The fifth power of `N` is below the same exponential. -/
private lemma exp_pow_lower_f673 (N : ℕ) (hN : (30 : ℝ) ≤ Real.log N) :
    (N : ℝ) ^ 5 ≤ Real.exp ((Real.log N) ^ 3 / 104) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h] at hN
      simp at hN
      linarith
    · exact_mod_cast h
  have hexp : (N : ℝ) ^ 5 = Real.exp (5 * Real.log N) := by
    have h1 : (N : ℝ) ^ 5 = (Real.exp (Real.log N)) ^ 5 := by
      rw [Real.exp_log hNpos]
    rw [h1, show 5 * Real.log N = ((5 : ℕ) : ℝ) * Real.log N by norm_num,
      Real.exp_nat_mul]
  have h5A : 5 * Real.log N ≤ (Real.log N) ^ 3 / 104 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 104)]
    nlinarith [hN, sq_nonneg (Real.log N)]
  rw [hexp]
  exact Real.exp_le_exp.mpr h5A

/-- The numerical constant of the truncation majorant is at most a third. -/
private lemma truncation_numeric_f673 (N : ℕ) (hN : (30 : ℝ) ≤ Real.log N) :
    3 * (10 ^ 8 * (Real.log N ^ 3 + 1) * (2 * 10 ^ 6 * (N : ℝ) ^ 5) *
      Real.exp (-(Real.log N ^ 3 / (8 * Real.pi)))) ≤ 1 := by
  have h1 := exp_const_lower_f673 (A := Real.log N) hN
  have h2 := exp_logcube_lower_f673 (A := Real.log N) hN
  have h5 := exp_pow_lower_f673 N hN
  have hEpos : (0 : ℝ) < Real.exp ((Real.log N) ^ 3 / 104) := Real.exp_pos _
  have h2pos : (0 : ℝ) ≤ (Real.log N) ^ 3 + 1 := by positivity
  have h5pos : (0 : ℝ) ≤ (N : ℝ) ^ 5 := by positivity
  have hcomp : (6 * 10 ^ 14 : ℝ) * ((Real.log N ^ 3 + 1) * (N : ℝ) ^ 5) ≤
      Real.exp ((Real.log N) ^ 3 / 104) *
        (Real.exp ((Real.log N) ^ 3 / 104) * Real.exp ((Real.log N) ^ 3 / 104)) := by
    have hthis : ((Real.log N ^ 3 + 1) * (N : ℝ) ^ 5) ≤
        Real.exp ((Real.log N) ^ 3 / 104) * Real.exp ((Real.log N) ^ 3 / 104) :=
      mul_le_mul h2 h5 h5pos hEpos.le
    exact mul_le_mul h1 hthis (by positivity) hEpos.le
  have hEmono : Real.exp ((Real.log N) ^ 3 / 104) *
        (Real.exp ((Real.log N) ^ 3 / 104) * Real.exp ((Real.log N) ^ 3 / 104)) ≤
      Real.exp ((Real.log N) ^ 3 / (8 * Real.pi)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hA3 : (0 : ℝ) ≤ (Real.log N) ^ 3 := by positivity
    have hp : 3 * ((Real.log N) ^ 3 / 104) ≤ (Real.log N) ^ 3 / (8 * Real.pi) := by
      have hrw : 3 * ((Real.log N) ^ 3 / 104) = (3 * (Real.log N) ^ 3) / 104 := by ring
      rw [hrw]
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 104)
        (by positivity : (0 : ℝ) < 8 * Real.pi)]
      nlinarith [Real.pi_lt_four, hA3]
    linarith
  calc 3 * (10 ^ 8 * (Real.log N ^ 3 + 1) * (2 * 10 ^ 6 * (N : ℝ) ^ 5) *
        Real.exp (-(Real.log N ^ 3 / (8 * Real.pi))))
      = (6 * 10 ^ 14) * ((Real.log N ^ 3 + 1) * (N : ℝ) ^ 5) *
          Real.exp (-(Real.log N ^ 3 / (8 * Real.pi))) := by ring
    _ ≤ Real.exp ((Real.log N) ^ 3 / (8 * Real.pi)) *
          Real.exp (-(Real.log N ^ 3 / (8 * Real.pi))) := by
        refine mul_le_mul (hcomp.trans hEmono) le_rfl (Real.exp_pos _).le (by positivity)
    _ = 1 := by
        rw [← Real.exp_add]
        simp

/-- The full Mellin integral is the truncated one plus the two tails. -/
private lemma mellinU_sub_truncated_f673 (N : ℕ) (R : ℝ) (M : ℝ → ℂ) (α : ℝ)
    (hint : Integrable (fun t : ℝ => mellinKernel519 N α t * M t)) :
    mellinU519 N M α - LeanLab.Linnik1951.truncatedMellin487 N R M α =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t in Set.Ioi ((N : ℝ) / R * Real.log N ^ 3), mellinKernel519 N α t * M t) +
         (∫ t in Set.Iic (-((N : ℝ) / R * Real.log N ^ 3)),
           mellinKernel519 N α t * M t)) := by
  have hU : mellinU519 N M α = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, mellinKernel519 N α t * M t := rfl
  have hT : LeanLab.Linnik1951.truncatedMellin487 N R M α =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          mellinKernel519 N α t * M t := rfl
  rw [hU, hT]
  have h1 := intervalIntegral.integral_Iic_add_Ioi
    (f := fun t : ℝ => mellinKernel519 N α t * M t)
    (b := (N : ℝ) / R * Real.log N ^ 3) hint.integrableOn hint.integrableOn
  have h2 := intervalIntegral.integral_Iic_sub_Iic
    (f := fun t : ℝ => mellinKernel519 N α t * M t)
    (a := -((N : ℝ) / R * Real.log N ^ 3)) (b := (N : ℝ) / R * Real.log N ^ 3)
    hint.integrableOn hint.integrableOn
  rw [← h1, ← h2]
  ring

/-- The truncation error of the outer Mellin integral on the outer range. -/
private lemma truncation_error_f673 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
      ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
      ∀ α : ℝ, 4 / (N : ℝ) ≤ α → α ≤ 1 / R →
        ‖mellinU519 N M α - LeanLab.Linnik1951.truncatedMellin487 N R M α‖ ≤ B0 * Real.sqrt N := by
  refine ⟨10 ^ 15, ?_⟩
  intro N hN R hR hRN M hM α hα0 hαR
  have hNlog : (30 : ℝ) ≤ Real.log N := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have h : (10 : ℝ) ^ 15 < (N : ℝ) := by exact_mod_cast hN
      linarith
    rw [Real.le_log_iff_exp_le hNpos]
    calc Real.exp 30 = (Real.exp 1) ^ 30 := by
          rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3 ^ 30 := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 30
      _ ≤ (10 : ℝ) ^ 15 := by norm_num
      _ ≤ (N : ℝ) := by
          have h16 : (10 : ℝ) ^ 15 = (1000000000000000 : ℝ) := by norm_num
          rw [h16]
          have h17 : (1000000000000000 : ℕ) ≤ N := by
            have h := hN
            norm_num at h
            exact le_of_lt h
          exact_mod_cast h17
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : (10 : ℝ) ^ 15 < (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN3 : 3 ≤ N := by
    have h : (3 : ℕ) < 10 ^ 14 := by norm_num
    omega
  have hRpos : (0 : ℝ) < R := by linarith
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hα0
  have hc0 : 0 < Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) :=
    Real.arctan_pos.mpr
      (div_pos one_pos (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 * Real.pi) hNpos) hαpos))
  have hc2 : Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) ≤ 2 := by
    have h1 := Real.arctan_lt_pi_div_two (1 / (2 * Real.pi * (N : ℝ) * α))
    nlinarith [Real.pi_lt_four]
  have hT0 : (0 : ℝ) ≤ (N : ℝ) / R * Real.log N ^ 3 :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg N) hRpos.le)
      (pow_nonneg (by linarith : (0 : ℝ) ≤ Real.log N) 3)
  have hu : 1 / Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) ≤ 4 * Real.pi * (N : ℝ) / R := by
    have hδ := delta_lower_f673 N hN3 hR hα0 hαR hRN
    have hpos : (0 : ℝ) < R / (4 * Real.pi * (N : ℝ)) := by positivity
    calc 1 / Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α))
        ≤ 1 / (R / (4 * Real.pi * (N : ℝ))) := one_div_le_one_div_of_le hpos hδ
      _ = 4 * Real.pi * (N : ℝ) / R := by field_simp
  -- the truncated-weight tail bound
  have hhalf := half_line_bound_f673 N (by omega) hc0 hc2 hT0 hu
  -- the rate times the truncation radius
  have hdecay : Real.exp
      (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * ((N : ℝ) / R * Real.log N ^ 3) / 2)) ≤
      Real.exp (-(Real.log N ^ 3 / (8 * Real.pi))) := by
    apply Real.exp_le_exp.mpr
    have hδ := delta_lower_f673 N hN3 hR hα0 hαR hRN
    have hprod : Real.log N ^ 3 / (4 * Real.pi) ≤
        Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * ((N : ℝ) / R * Real.log N ^ 3) := by
      have hkey : R / (4 * Real.pi * (N : ℝ)) * ((N : ℝ) / R * Real.log N ^ 3) =
          Real.log N ^ 3 / (4 * Real.pi) := by
        field_simp
      rw [← hkey]
      exact mul_le_mul_of_nonneg_right hδ (by positivity)
    have h8 : Real.log N ^ 3 / (8 * Real.pi) = Real.log N ^ 3 / (4 * Real.pi) / 2 := by
      field_simp
      ring
    rw [h8]
    linarith
  set C0 : ℝ := B0 * (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)) with hC0
  have hC00 : (0 : ℝ) ≤ C0 := by rw [hC0]; positivity
  have hKint := integrable_integrand_f673 N hN3 hα0 hM
  have hWint := weight_integrable_f673 N (by omega) hc0
  have hpt : ∀ t : ℝ, ‖mellinKernel519 N α t * M t‖ ≤
      C0 * ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
        Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))) := by
    intro t
    rw [hC0]
    exact integrand_le_weight_f673 N hN3 hα0 hM t
  have htailU : (∫ t in Set.Ioi ((N : ℝ) / R * Real.log N ^ 3),
      ‖mellinKernel519 N α t * M t‖) ≤
      C0 * (10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
        Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
          ((N : ℝ) / R * Real.log N ^ 3) / 2))) := by
    have hInt2 : IntegrableOn (fun t : ℝ =>
        C0 * ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
          Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))))
        (Set.Ioi ((N : ℝ) / R * Real.log N ^ 3)) := (hWint.const_mul C0).integrableOn
    have hmono := setIntegral_mono_on (f := fun t : ℝ => ‖mellinKernel519 N α t * M t‖)
      (g := fun t : ℝ => C0 * ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
        Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))))
      hKint.norm.integrableOn hInt2 measurableSet_Ioi (fun t _ => hpt t)
    refine hmono.trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hhalf hC00
  have htailWL : (∫ t in Set.Iic (-((N : ℝ) / R * Real.log N ^ 3)),
      (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
        Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))) =
      (∫ t in Set.Ioi ((N : ℝ) / R * Real.log N ^ 3),
        (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
          Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))) := by
    rw [← integral_comp_neg_Ioi ((N : ℝ) / R * Real.log N ^ 3)
      (fun y : ℝ => (3 + |y|) * Real.log ((N : ℝ) * (|y| + 2)) ^ 3 *
        Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |y|)))]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by rw [abs_neg])
  -- the numerical bound on the localised majorant
  have hnum := truncation_numeric_f673 N hNlog
  have hfourpi : (4 * Real.pi * (N : ℝ) / R) ^ 5 ≤ 2 * (10 : ℝ) ^ 6 * (N : ℝ) ^ 5 := by
    have hNR : (N : ℝ) / R ≤ (N : ℝ) := by
      rw [div_le_iff₀ hRpos]
      nlinarith [hR, hNpos]
    have h1 : 4 * Real.pi * (N : ℝ) / R = (4 * Real.pi) * ((N : ℝ) / R) := by ring
    have h2 : (4 * Real.pi) ^ 5 ≤ 2 * (10 : ℝ) ^ 6 := by
      have h3 : 4 * Real.pi ≤ 16 := by nlinarith [Real.pi_lt_four]
      calc (4 * Real.pi) ^ 5 ≤ 16 ^ 5 := pow_le_pow_left₀ (by positivity) h3 5
        _ ≤ 2 * (10 : ℝ) ^ 6 := by norm_num
    have h3 : ((N : ℝ) / R) ^ 5 ≤ (N : ℝ) ^ 5 := pow_le_pow_left₀ (by positivity) hNR 5
    rw [h1, mul_pow]
    exact mul_le_mul h2 h3 (by positivity) (by positivity)
  have hZsmall : 3 * (10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
      Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
        ((N : ℝ) / R * Real.log N ^ 3) / 2))) ≤ 1 := by
    have hstep : 10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
        Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
          ((N : ℝ) / R * Real.log N ^ 3) / 2)) ≤
        10 ^ 8 * (Real.log N ^ 3 + 1) * (2 * 10 ^ 6 * (N : ℝ) ^ 5) *
          Real.exp (-(Real.log N ^ 3 / (8 * Real.pi))) := by
      have h1 : (0 : ℝ) ≤ 10 ^ 8 * (Real.log N ^ 3 + 1) := by positivity
      have hexp2 : Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
          ((N : ℝ) / R * Real.log N ^ 3) / 2)) ≤
          Real.exp (-(Real.log N ^ 3 / (8 * Real.pi))) := hdecay
      have h2 := mul_le_mul hfourpi hexp2 (Real.exp_pos _).le (by positivity)
      have h3 := mul_le_mul_of_nonneg_left h2 h1
      calc 10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
            Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
              ((N : ℝ) / R * Real.log N ^ 3) / 2))
          = (10 ^ 8 * (Real.log N ^ 3 + 1)) *
              ((4 * Real.pi * (N : ℝ) / R) ^ 5 *
                Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
                  ((N : ℝ) / R * Real.log N ^ 3) / 2))) := by ring
        _ ≤ (10 ^ 8 * (Real.log N ^ 3 + 1)) *
              (2 * (10 : ℝ) ^ 6 * (N : ℝ) ^ 5 *
                Real.exp (-(Real.log N ^ 3 / (8 * Real.pi)))) := h3
        _ = 10 ^ 8 * (Real.log N ^ 3 + 1) * (2 * 10 ^ 6 * (N : ℝ) ^ 5) *
              Real.exp (-(Real.log N ^ 3 / (8 * Real.pi))) := by ring
    linarith [hstep, hnum]
  -- assemble the truncation error
  have hdiff := mellinU_sub_truncated_f673 N R M α hKint
  have hcoef : (1 / Real.pi) * Real.exp 1 * Real.sqrt (2 * Real.pi) ≤ 3 := by
    have h1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    have h2 : Real.sqrt (2 * Real.pi) ≤ 3 := by
      have h3 : 2 * Real.pi ≤ 9 := by nlinarith [Real.pi_lt_four]
      calc Real.sqrt (2 * Real.pi) ≤ Real.sqrt 9 := Real.sqrt_le_sqrt h3
        _ = 3 := by norm_num
    have h4 : (1 / Real.pi) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num) (by nlinarith [Real.pi_gt_three])
    have h5 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    have h6 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have h7 : (1 / Real.pi) * Real.exp 1 ≤ (1 / 3) * 3 :=
      mul_le_mul h4 h1 h5 (by norm_num)
    have h8 : (1 / Real.pi) * Real.exp 1 * Real.sqrt (2 * Real.pi) ≤ ((1 / 3) * 3) * 3 :=
      mul_le_mul h7 h2 h6 (by norm_num)
    linarith [h8]
  have hsum : ‖(∫ t in Set.Ioi ((N : ℝ) / R * Real.log N ^ 3), mellinKernel519 N α t * M t) +
      (∫ t in Set.Iic (-((N : ℝ) / R * Real.log N ^ 3)), mellinKernel519 N α t * M t)‖ ≤
      2 * (C0 * (10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
        Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
          ((N : ℝ) / R * Real.log N ^ 3) / 2)))) := by
    have h1 : ‖(∫ t in Set.Ioi ((N : ℝ) / R * Real.log N ^ 3), mellinKernel519 N α t * M t)‖ ≤
        C0 * (10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
          Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
            ((N : ℝ) / R * Real.log N ^ 3) / 2))) :=
      (norm_integral_le_integral_norm (f := fun t : ℝ => mellinKernel519 N α t * M t)).trans htailU
    have h2 : ‖(∫ t in Set.Iic (-((N : ℝ) / R * Real.log N ^ 3)), mellinKernel519 N α t * M t)‖ ≤
        C0 * (10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
          Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
            ((N : ℝ) / R * Real.log N ^ 3) / 2))) := by
      have h3 : ‖(∫ t in Set.Iic (-((N : ℝ) / R * Real.log N ^ 3)),
          mellinKernel519 N α t * M t)‖ ≤
          (∫ t in Set.Iic (-((N : ℝ) / R * Real.log N ^ 3)),
            ‖mellinKernel519 N α t * M t‖) :=
        norm_integral_le_integral_norm (f := fun t : ℝ => mellinKernel519 N α t * M t)
      have hInt2 : IntegrableOn (fun t : ℝ =>
          C0 * ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
            Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))))
          (Set.Iic (-((N : ℝ) / R * Real.log N ^ 3))) := (hWint.const_mul C0).integrableOn
      have hmono := setIntegral_mono_on (f := fun t : ℝ => ‖mellinKernel519 N α t * M t‖)
        (g := fun t : ℝ => C0 * ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
          Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))))
        hKint.norm.integrableOn hInt2 measurableSet_Iic (fun t _ => hpt t)
      have h4 : (∫ t in Set.Iic (-((N : ℝ) / R * Real.log N ^ 3)),
          ‖mellinKernel519 N α t * M t‖) ≤
          C0 * (∫ t in Set.Ioi ((N : ℝ) / R * Real.log N ^ 3),
            (3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
              Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|))) := by
        refine hmono.trans ?_
        rw [integral_const_mul, htailWL]
      exact h3.trans (h4.trans (mul_le_mul_of_nonneg_left hhalf hC00))
    linarith [norm_add_le ((∫ t in Set.Ioi ((N : ℝ) / R * Real.log N ^ 3),
        mellinKernel519 N α t * M t))
      ((∫ t in Set.Iic (-((N : ℝ) / R * Real.log N ^ 3)), mellinKernel519 N α t * M t)), h1, h2]
  have hfinal : (1 / (2 * Real.pi)) *
      (2 * (C0 * (10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
        Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
          ((N : ℝ) / R * Real.log N ^ 3) / 2))))) ≤ B0 * Real.sqrt N := by
    have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hNpos.le
    have hrew : (1 / (2 * Real.pi)) *
        (2 * (C0 * (10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
          Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
            ((N : ℝ) / R * Real.log N ^ 3) / 2))))) =
        (B0 * Real.sqrt N) * ((1 / Real.pi) * Real.exp 1 * Real.sqrt (2 * Real.pi)) *
          (10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
            Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
              ((N : ℝ) / R * Real.log N ^ 3) / 2))) := by
      rw [hC0]
      field_simp
      try ring
    rw [hrew]
    have hpos : (0 : ℝ) ≤ B0 * Real.sqrt N := by positivity
    have hZ0 : (0 : ℝ) ≤ 10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
        Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
          ((N : ℝ) / R * Real.log N ^ 3) / 2)) := by positivity
    have hcoef0 : (0 : ℝ) ≤ (1 / Real.pi) * Real.exp 1 * Real.sqrt (2 * Real.pi) := by positivity
    calc (B0 * Real.sqrt N) * ((1 / Real.pi) * Real.exp 1 * Real.sqrt (2 * Real.pi)) *
          (10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
            Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
              ((N : ℝ) / R * Real.log N ^ 3) / 2)))
        = (B0 * Real.sqrt N) * (((1 / Real.pi) * Real.exp 1 * Real.sqrt (2 * Real.pi)) *
            (10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
              Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
                ((N : ℝ) / R * Real.log N ^ 3) / 2)))) := by ring
      _ ≤ (B0 * Real.sqrt N) * (3 * (10 ^ 8 * (Real.log N ^ 3 + 1) *
            (4 * Real.pi * (N : ℝ) / R) ^ 5 *
            Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
              ((N : ℝ) / R * Real.log N ^ 3) / 2)))) := by
          apply mul_le_mul_of_nonneg_left _ hpos
          exact mul_le_mul_of_nonneg_right hcoef hZ0
      _ ≤ (B0 * Real.sqrt N) * 1 := by
          apply mul_le_mul_of_nonneg_left _ hpos
          exact hZsmall
      _ = B0 * Real.sqrt N := by ring
  have hstep : (1 / (2 * Real.pi)) *
      ‖(∫ t in Set.Ioi ((N : ℝ) / R * Real.log N ^ 3), mellinKernel519 N α t * M t) +
        (∫ t in Set.Iic (-((N : ℝ) / R * Real.log N ^ 3)),
          mellinKernel519 N α t * M t)‖ ≤
      (1 / (2 * Real.pi)) *
        (2 * (C0 * (10 ^ 8 * (Real.log N ^ 3 + 1) * (4 * Real.pi * (N : ℝ) / R) ^ 5 *
          Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) *
            ((N : ℝ) / R * Real.log N ^ 3) / 2))))) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  linarith [hstep, hfinal]

/-! ### Continuity of the Mellin transform on the outer range -/

/-- The kernel bound with a rate that is uniform on the outer range up to two. -/
private lemma kernel_bound_uniform_f673 (N : ℕ) (hN : 3 ≤ N) {α t : ℝ}
    (hα : α ∈ Set.Icc (4 / (N : ℝ)) 2) :
    ‖mellinKernel519 N α t‖ ≤
      Real.exp 1 * Real.sqrt N * (Real.sqrt (2 * Real.pi) * (3 + |t|)) *
        Real.exp (-(Real.arctan (1 / (4 * Real.pi * (N : ℝ))) * |t|)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hα0 : 4 / (N : ℝ) ≤ α := hα.1
  have hα2 : α ≤ 2 := hα.2
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hα0
  have hk := kernel_bound_f673 N hN α t hα0
  have hden1 : (0 : ℝ) < 4 * Real.pi * (N : ℝ) := by positivity
  have hden2 : (0 : ℝ) < 2 * Real.pi * (N : ℝ) * α := by positivity
  have hmono : Real.arctan (1 / (4 * Real.pi * (N : ℝ))) ≤
      Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) := by
    apply Real.arctan_le_arctan_iff.mpr
    rw [div_le_div_iff₀ hden1 hden2]
    nlinarith [hα2, Real.pi_pos, hNpos, hαpos]
  have hexp : Real.exp (-(Real.arctan (1 / (2 * Real.pi * (N : ℝ) * α)) * |t|)) ≤
      Real.exp (-(Real.arctan (1 / (4 * Real.pi * (N : ℝ))) * |t|)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg t, hmono]
  exact hk.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- The Mellin transform of a line bounded coefficient is continuous in the outer
variable on the outer range up to two. -/
private lemma outer_continuous_f673 (N : ℕ) (hN : 3 ≤ N) (M : ℝ → ℂ) (hM : Continuous M)
    (B0 : ℝ) (hB0 : 0 ≤ B0)
    (hbound : ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :
    ContinuousOn (fun α => mellinU519 N M α) (Set.Icc (4 / (N : ℝ)) 2) := by
  set δ : ℝ := Real.arctan (1 / (4 * Real.pi * (N : ℝ))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact Real.arctan_pos.mpr (by positivity)
  have hN2 : 2 ≤ N := by omega
  have hW := weight_integrable_f673 N hN2 (δ := δ) hδpos
  have hBint : Integrable (fun t : ℝ => B0 * (Real.exp 1 * Real.sqrt N *
      Real.sqrt (2 * Real.pi)) * ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
        Real.exp (-(δ * |t|)))) := by
    have := hW.const_mul (B0 * (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using this
  have hmain : ContinuousOn (fun α => ∫ t : ℝ, mellinKernel519 N α t * M t)
      (Set.Icc (4 / (N : ℝ)) 2) := by
    refine MeasureTheory.continuousOn_of_dominated (μ := volume) ?_ ?_ hBint ?_
    · intro α _
      exact ((continuous_mellin_integrand519 N hN M hM).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro α hα
      filter_upwards with t
      have hk := kernel_bound_uniform_f673 N hN (α := α) (t := t) hα
      rw [norm_mul]
      have hlog3 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
        have h5 : (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by
          have h6 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
          have h7 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
          nlinarith [h6, h7, abs_nonneg t]
        exact pow_nonneg (Real.log_nonneg h5) 3
      have hstep := mul_le_mul hk (hbound t) (norm_nonneg (M t)) (by positivity)
      calc ‖mellinKernel519 N α t‖ * ‖M t‖
          ≤ (Real.exp 1 * Real.sqrt N * (Real.sqrt (2 * Real.pi) * (3 + |t|)) *
              Real.exp (-(δ * |t|))) * (B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := hstep
        _ = B0 * (Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)) *
              ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 * Real.exp (-(δ * |t|))) := by
            ring
    · filter_upwards with t
      exact ((continuous_mellin_integrand519 N hN M hM).comp
        (continuous_id.prodMk continuous_const)).continuousOn
  have heq : (fun α => mellinU519 N M α) = fun α =>
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, mellinKernel519 N α t * M t := by
    funext α
    simp only [mellinU519, mellinKernel519]
  rw [heq]
  exact hmain.const_mul _

/-- The square of the Mellin transform is interval integrable on the outer
interval, from continuity in the outer variable. -/
private lemma intervalIntegrable_norm_sq_f673 (N : ℕ) (hN : 3 ≤ N) {R : ℝ}
    (M : ℝ → ℂ) (hM : Continuous M) (B0 : ℝ) (hB0 : 0 ≤ B0)
    (hbound : ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3)
    (hR : 1 ≤ R) (hab : 4 / (N : ℝ) ≤ 1 / R) :
    IntervalIntegrable (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2) volume
      (4 / (N : ℝ)) (1 / R) := by
  have hcont := outer_continuous_f673 N hN M hM B0 hB0 hbound
  have h1R : 1 / R ≤ 2 := by
    have hRp : (0 : ℝ) < R := by linarith
    rw [div_le_iff₀ hRp]
    nlinarith
  have hmono : ContinuousOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      (Set.uIcc (4 / (N : ℝ)) (1 / R)) := by
    rw [Set.uIcc_of_le hab]
    exact (hcont.norm.pow 2).mono (fun x hx => ⟨hx.1, le_trans hx.2 h1R⟩)
  exact hmono.intervalIntegrable

/-- `log N` is at least one on the range. -/
private lemma logN_one_le_f673 (N : ℕ) (hN : 3 ≤ N) : (1 : ℝ) ≤ Real.log N := by
  have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 3 ≤ N by omega)
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log N := by
        apply Real.log_le_log (Real.exp_pos 1)
        exact le_trans Real.exp_one_lt_three.le h3

/-- The outer square mass bound over the whole inverse radius range, from one up
to the two sevenths power of N.  This is the estimate of the sealed statement
with its inverse radius range extended to the full admissible range; the
truncation at radius N over R times the cube of the logarithm of N and the two
kernel estimates of the finite square are the only inputs, and the lower bound
on the inverse radius is not needed. -/
private lemma outer_square_whole_R_core_f673 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  obtain ⟨C1, hC1, N1, h1⟩ := LeanLab.Linnik1951.outer_finite_square487_split B0 hB0
  obtain ⟨Ntr, htr⟩ := truncation_error_f673 B0 hB0
  refine ⟨128 * C1 + 2 * B0 ^ 2, by positivity, max Ntr (max N1 16384), ?_⟩
  intro N hN R hR hRhi M hM
  have hNtr : Ntr < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN1 : N1 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN16 : 16384 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN3 : 3 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hRp : (0 : ℝ) < R := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log N := logN_one_le_f673 N hN3
  have hlog0 : (0 : ℝ) ≤ Real.log N := le_trans (by norm_num) hlog1
  have hRN : R ≤ (N : ℝ) := by
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hrw : (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by norm_num)
    rw [Real.rpow_one] at hrw
    exact hRhi.trans hrw
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) / R := by
    rw [le_div_iff₀ hRp]
    simpa using hRN
  obtain ⟨hintT, hboundT⟩ := h1 N hN1 R hR hRhi M ⟨hM.1, hM.2⟩
  set T : ℝ := (N : ℝ) / R * Real.log N ^ 3 with hTdef
  have hlog3one : (1 : ℝ) ≤ Real.log N ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := by ring
      _ ≤ Real.log N ^ 3 := pow_le_pow_left₀ (by norm_num) hlog1 3
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hTdef]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (N : ℝ) / R * Real.log N ^ 3 :=
          mul_le_mul hNR1 hlog3one (by norm_num) (by positivity)
  have hT0 : (0 : ℝ) ≤ T := le_trans (by norm_num) hT1
  have hdiff := LeanLab.Linnik1951.difference_kernel_le376 T hT1
  have hsum := LeanLab.Linnik1951.sum_kernel_le376 T hT1
  have hloglin : Real.log (2 * T + 1) ≤ 5 * Real.log N := by
    have hTle : T ≤ (N : ℝ) * Real.log N ^ 3 := by
      rw [hTdef]
      have h1' : (N : ℝ) / R ≤ (N : ℝ) := by
        rw [div_le_iff₀ hRp]; nlinarith [hRN, hRp]
      exact mul_le_mul_of_nonneg_right h1' (by positivity)
    have harg1 : (1 : ℝ) ≤ (N : ℝ) * Real.log N ^ 3 := by
      nlinarith [hNpos, hlog3one]
    have htpos : (0 : ℝ) < 2 * T + 1 := by linarith
    have hTle2 : 2 * T + 1 ≤ 3 * ((N : ℝ) * Real.log N ^ 3) := by nlinarith [hTle, harg1]
    have hlog3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 3 ≤ N by omega)
    calc Real.log (2 * T + 1) ≤ Real.log (3 * ((N : ℝ) * Real.log N ^ 3)) :=
          Real.log_le_log htpos hTle2
      _ = Real.log 3 + Real.log N + 3 * Real.log (Real.log N) := by
          rw [Real.log_mul (by norm_num) (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_pow]
          push_cast
          ring
      _ ≤ 5 * Real.log N := by
          have h4 : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) hlog3
          have h5 : Real.log (Real.log N) ≤ Real.log N := by
            have h6 := Real.log_le_self (le_trans (by norm_num) hlog1)
            linarith
          linarith
  have hsumT : (∫ α in (4 / (N : ℝ))..(1 / R),
      ‖LeanLab.Linnik1951.truncatedMellin487 N R M α‖ ^ 2)
      ≤ 56 * C1 * ((N : ℝ) / R * Real.log N ^ 10) := by
    refine hboundT.trans ?_
    have e1 : C1 * Real.log N ^ 6 *
        LeanLab.Linnik1951.differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) ≤
        40 * C1 * ((N : ℝ) / R * Real.log N ^ 10) := by
      have hd1 : C1 * Real.log N ^ 6 *
          LeanLab.Linnik1951.differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) ≤
          C1 * Real.log N ^ 6 * (8 * T * Real.log (2 * T + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hTdef]
        exact hdiff
      refine hd1.trans ?_
      have hstep : C1 * Real.log N ^ 6 * (8 * T * Real.log (2 * T + 1)) ≤
          C1 * Real.log N ^ 6 * (8 * T * (5 * Real.log N)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hloglin (by linarith)
      refine hstep.trans ?_
      have heq : C1 * Real.log N ^ 6 * (8 * T * (5 * Real.log N)) =
          40 * C1 * ((N : ℝ) / R * Real.log N ^ 10) := by
        rw [hTdef]; ring
      rw [heq]
    have e2 : C1 * Real.log N ^ 7 *
        LeanLab.Linnik1951.sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) ≤
        16 * C1 * ((N : ℝ) / R * Real.log N ^ 10) := by
      have hs1 : C1 * Real.log N ^ 7 *
          LeanLab.Linnik1951.sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) ≤
          C1 * Real.log N ^ 7 * (16 * T) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hTdef]
        exact hsum
      refine hs1.trans ?_
      have heq : C1 * Real.log N ^ 7 * (16 * T) =
          16 * C1 * ((N : ℝ) / R * Real.log N ^ 10) := by
        rw [hTdef]; ring
      rw [heq]
    linarith [e1, e2]
  have hpt : ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
      ‖mellinU519 N M α‖ ^ 2 ≤
        2 * ‖LeanLab.Linnik1951.truncatedMellin487 N R M α‖ ^ 2 +
          2 * (B0 * Real.sqrt N) ^ 2 := by
    intro α hα
    have hα0 : 4 / (N : ℝ) ≤ α := hα.1
    have hαR : α ≤ 1 / R := hα.2
    have he := htr N hNtr R hR hRhi M hM α hα0 hαR
    have hsub : mellinU519 N M α =
        LeanLab.Linnik1951.truncatedMellin487 N R M α +
          (mellinU519 N M α - LeanLab.Linnik1951.truncatedMellin487 N R M α) := by ring
    have hpt1 : ‖mellinU519 N M α‖ ≤
        ‖LeanLab.Linnik1951.truncatedMellin487 N R M α‖ + B0 * Real.sqrt N := by
      rw [hsub]
      exact (norm_add_le _ _).trans (add_le_add le_rfl he)
    have hsq : (‖LeanLab.Linnik1951.truncatedMellin487 N R M α‖ + B0 * Real.sqrt N) ^ 2 ≤
        2 * ‖LeanLab.Linnik1951.truncatedMellin487 N R M α‖ ^ 2 +
          2 * (B0 * Real.sqrt N) ^ 2 := by
      nlinarith [sq_nonneg (‖LeanLab.Linnik1951.truncatedMellin487 N R M α‖ - B0 * Real.sqrt N)]
    exact (pow_le_pow_left₀ (norm_nonneg _) hpt1 2).trans hsq
  have hX0 : (0 : ℝ) ≤ (N : ℝ) / R * Real.log N ^ 10 := by positivity
  have hC : (0 : ℝ) < 128 * C1 + 2 * B0 ^ 2 := by positivity
  rcases le_or_gt (4 / (N : ℝ)) (1 / R) with hab | hba
  · have hintU := intervalIntegrable_norm_sq_f673 N hN3 M hM.1 B0 hB0.le hM.2 hR hab
    have hintG : IntervalIntegrable (fun α : ℝ =>
        2 * ‖LeanLab.Linnik1951.truncatedMellin487 N R M α‖ ^ 2 +
          2 * (B0 * Real.sqrt N) ^ 2) volume (4 / (N : ℝ)) (1 / R) :=
      (hintT.const_mul 2).add intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hab hintU hintG hpt
    have hsplit : (∫ α in (4 / (N : ℝ))..(1 / R),
        2 * ‖LeanLab.Linnik1951.truncatedMellin487 N R M α‖ ^ 2 +
          2 * (B0 * Real.sqrt N) ^ 2) =
        2 * (∫ α in (4 / (N : ℝ))..(1 / R),
          ‖LeanLab.Linnik1951.truncatedMellin487 N R M α‖ ^ 2) +
          (1 / R - 4 / (N : ℝ)) * (2 * (B0 * Real.sqrt N) ^ 2) := by
      rw [intervalIntegral.integral_add (hintT.const_mul 2) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    have hlen : (1 / R - 4 / (N : ℝ)) ≤ 1 / R := by
      have h4 : (0 : ℝ) ≤ 4 / (N : ℝ) := by positivity
      linarith
    have hconst0 : (0 : ℝ) ≤ 2 * (B0 * Real.sqrt N) ^ 2 := by positivity
    have hsqN : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hNpos.le
    have hkey : (1 / R) * (2 * (B0 * Real.sqrt N) ^ 2) =
        2 * B0 ^ 2 * ((N : ℝ) / R) := by
      have hsq2 : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
      rw [mul_pow, hsq2]
      field_simp
      try ring
    have hl10 : (1 : ℝ) ≤ Real.log N ^ 10 := by
      calc (1 : ℝ) = 1 ^ 10 := by ring
        _ ≤ Real.log N ^ 10 := pow_le_pow_left₀ (by norm_num) hlog1 10
    have hL0 : (0 : ℝ) ≤ (N : ℝ) / R := by positivity
    have hX1 : (N : ℝ) / R ≤ (N : ℝ) / R * Real.log N ^ 10 := by
      calc (N : ℝ) / R = (N : ℝ) / R * 1 := by ring
        _ ≤ (N : ℝ) / R * Real.log N ^ 10 := mul_le_mul_of_nonneg_left hl10 hL0
    calc (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2)
        ≤ 2 * (∫ α in (4 / (N : ℝ))..(1 / R),
            ‖LeanLab.Linnik1951.truncatedMellin487 N R M α‖ ^ 2) +
            (1 / R - 4 / (N : ℝ)) * (2 * (B0 * Real.sqrt N) ^ 2) := by
          rw [← hsplit]; exact hmono
      _ ≤ 2 * (56 * C1 * ((N : ℝ) / R * Real.log N ^ 10)) +
            (1 / R) * (2 * (B0 * Real.sqrt N) ^ 2) := by
          have h1' : (1 / R - 4 / (N : ℝ)) * (2 * (B0 * Real.sqrt N) ^ 2) ≤
              (1 / R) * (2 * (B0 * Real.sqrt N) ^ 2) :=
            mul_le_mul_of_nonneg_right hlen hconst0
          have h2' : 2 * (∫ α in (4 / (N : ℝ))..(1 / R),
              ‖LeanLab.Linnik1951.truncatedMellin487 N R M α‖ ^ 2) ≤
              2 * (56 * C1 * ((N : ℝ) / R * Real.log N ^ 10)) := by linarith
          linarith [h1', h2']
      _ = 112 * C1 * ((N : ℝ) / R * Real.log N ^ 10) + 2 * B0 ^ 2 * ((N : ℝ) / R) := by
          rw [hkey]; ring
      _ ≤ (128 * C1 + 2 * B0 ^ 2) * ((N : ℝ) / R * Real.log N ^ 10) := by
          nlinarith [hX1, hC1.le, sq_nonneg B0, hX0, hL0]
  · have hsym := intervalIntegral.integral_symm (μ := volume) (a := (1 / R))
        (b := (4 / (N : ℝ))) (f := fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
    have hnn : (0 : ℝ) ≤ ∫ α in (1 / R)..(4 / (N : ℝ)), ‖mellinU519 N M α‖ ^ 2 :=
      intervalIntegral.integral_nonneg (le_of_lt hba) (fun u _ => by positivity)
    have hzero : (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤ 0 := by
      rw [hsym]
      linarith
    have hprod : (0 : ℝ) ≤ (128 * C1 + 2 * B0 ^ 2) * ((N : ℝ) / R * Real.log N ^ 10) :=
      mul_nonneg hC.le hX0
    linarith [hzero, hprod]


/-- LEAF. Mass bound on the small inverse radius range, from one up to the seventh
root of N.  Here the outer interval is at least as long as the central one, so
this is the case of the estimate in which the inverse radius is short and the
interval reaches back to the central scale four over N.  It is one case of the
sealed mass bound, with the same conclusion and a restricted range of R, and it
says nothing about the complementary range nor about integrability. -/
theorem outer_square_small_R519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  obtain ⟨C, hC, N0, h⟩ := outer_square_whole_R_core_f673 B0 hB0
  refine ⟨C, hC, max N0 1, ?_⟩
  intro N hN R hR hR17 M hM
  have hN1 : 1 ≤ N := by omega
  have hRhi : R ≤ (N : ℝ) ^ (2 / 7 : ℝ) :=
    hR17.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num))
  exact h N (by omega) R hR hRhi M hM

/-- LEAF. Mass bound on the large inverse radius range, from the seventh root of N
up to the two sevenths power of N.  Here the outer interval lies far from the
central scale, which is the case in which the double frequency calculation is
cut off only by the two sevenths power of N in the statement of Lemma 2.  It is
the complementary case of the sealed mass bound, again with the same conclusion
and a restricted range of R, and it carries no integrability claim. -/
theorem outer_square_large_R519 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      (N : ℝ) ^ (1 / 7 : ℝ) ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  obtain ⟨C, hC, N0, h⟩ := outer_square_whole_R_core_f673 B0 hB0
  refine ⟨C, hC, max N0 1, ?_⟩
  intro N hN R hR hR17 hR27 M hM
  exact h N (by omega) R hR hR27 M hM

/-- The three leaves together give the outer square estimate: the square of the
Mellin transform is integrable on the outer interval, and its mass there is at
most the larger of the two range constants times N over R times the tenth power
of the logarithm of N. -/
theorem lemma2_outer_square519_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
            (Set.Icc (4 / (N : ℝ)) (1 / R)) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 10) := by
  obtain ⟨Ni, hi⟩ := outer_square_integrable519 B0 hB0
  obtain ⟨C1, hC1, N1, h1⟩ := outer_square_small_R519 B0 hB0
  obtain ⟨C2, hC2, N2, h2⟩ := outer_square_large_R519 B0 hB0
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 (le_max_left C1 C2),
    max Ni (max N1 N2), ?_⟩
  intro N hN R hR hRN M hM
  have hNi : Ni < N := lt_of_le_of_lt (le_max_left Ni (max N1 N2)) hN
  have hN1 : N1 < N :=
    lt_of_le_of_lt ((le_max_left N1 N2).trans (le_max_right Ni (max N1 N2))) hN
  have hN2 : N2 < N :=
    lt_of_le_of_lt ((le_max_right N1 N2).trans (le_max_right Ni (max N1 N2))) hN
  refine ⟨hi N hNi R hR hRN M hM, ?_⟩
  have hRp : (0 : ℝ) < R := by linarith
  have hX : 0 ≤ (N : ℝ) / R * Real.log N ^ 10 := by
    have hNR : (0 : ℝ) ≤ (N : ℝ) / R := div_nonneg (Nat.cast_nonneg N) hRp.le
    have hlog : (0 : ℝ) ≤ Real.log N ^ 10 := by
      have he : Real.log N ^ 10 = (Real.log N ^ 5) ^ 2 := by ring
      rw [he]
      exact sq_nonneg _
    exact mul_nonneg hNR hlog
  rcases le_or_gt R ((N : ℝ) ^ (1 / 7 : ℝ)) with hs | hl
  · exact (h1 N hN1 R hR hs M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hX)
  · exact (h2 N hN2 R hR hl.le hRN M hM).trans
      (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hX)

end LeanLab.Linnik1951.Task519
