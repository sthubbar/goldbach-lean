module

public import LeanLab.Linnik1951.Repair493KernelData
public import LeanLab.Linnik1951.Gamma442

/-!
Split of the absolute central Mellin kernel mass of Decomp442a.lean.
The parent statement central_kernel_mass442 asks for an integrable
absolute Gamma weighted kernel on the central interval and for its mass
to be at most a constant times square root N times the cube of log N.
The leaves below are the steps of that computation and nothing else:
the modulus of the power factor, the split of a logarithm of a product,
the twisted Gamma mass, the integrability of the weighted kernel, and the
bookkeeping of the constant. central_kernel_mass442_split reassembles
them into the parent statement without using the parent theorem.

The only point of care is the power factor. The base of the kernel power
has real part one over N and imaginary part at most eight pi over N, so
the ratio of its parts is at most eight pi and the imaginary part of its
logarithm is bounded away from pi over two by a fixed gap. That gap is
what keeps the exponential of the Gamma factor away from the Gamma decay,
and it is the reason the mass is finite at all.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory

/-- The gap in the principal argument: `pi / 2 - 1 / (16 * pi)` is strictly positive. -/
private lemma pi_gap442 : (0 : ℝ) < Real.pi / 2 - 1 / (16 * Real.pi) := by
  have h16 : (0 : ℝ) < 16 * Real.pi := by positivity
  have h : (1 : ℝ) < Real.pi / 2 * (16 * Real.pi) := by nlinarith [Real.pi_gt_three]
  have h2 : 1 / (16 * Real.pi) < Real.pi / 2 := (div_lt_iff₀ h16).mpr h
  linarith

/-- The principal argument of the base `1 / N + 2 pi alpha i` of the Mellin power factor
stays `1 / (16 * pi)` away from `pi / 2` when `|alpha| ≤ 4 / N`: the modulus of the base is at
most `(1 / N) sqrt (1 + (8 pi) ^ 2)`, so its cosine is at least `1 / sqrt (1 + (8 pi) ^ 2)`,
which is at least `1 / (16 pi)`, which is at least `sin (1 / (16 pi))`. -/
private lemma arg_base_bound442 (N : ℕ) (α : ℝ) (hN : 2 ≤ N) (hα : |α| ≤ 4 / (N : ℝ)) :
    |Complex.arg ((((1 / (N : ℝ) : ℝ) : ℂ) +
        ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I))| ≤
      Real.pi / 2 - 1 / (16 * Real.pi) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzim : z.im = 2 * Real.pi * α := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  have him : |z.im| ≤ 8 * Real.pi / (N : ℝ) := by
    rw [hzim, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
    calc 2 * Real.pi * |α| ≤ 2 * Real.pi * (4 / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hα (by positivity)
      _ = 8 * Real.pi / (N : ℝ) := by field_simp; ring
  have hnorm_ge : 1 / (N : ℝ) ≤ ‖z‖ := by
    calc 1 / (N : ℝ) = |z.re| := by
          rw [hzre, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnorm_le : ‖z‖ ≤ (1 / (N : ℝ)) * Real.sqrt (1 + 64 * Real.pi ^ 2) := by
    have hz2 : ‖z‖ ^ 2 ≤ (1 / (N : ℝ)) ^ 2 * (1 + 64 * Real.pi ^ 2) := by
      have hsqim : z.im ^ 2 ≤ (8 * Real.pi / (N : ℝ)) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg z.im) him 2
        rwa [sq_abs] at h
      have expand : (1 / (N : ℝ)) ^ 2 * (1 + 64 * Real.pi ^ 2) =
          (1 / (N : ℝ)) ^ 2 + (8 * Real.pi / (N : ℝ)) ^ 2 := by
        field_simp; ring
      rw [hsq, hzre, expand]
      linarith
    calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
      _ ≤ Real.sqrt ((1 / (N : ℝ)) ^ 2 * (1 + 64 * Real.pi ^ 2)) := Real.sqrt_le_sqrt hz2
      _ = (1 / (N : ℝ)) * Real.sqrt (1 + 64 * Real.pi ^ 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by positivity) hnorm_ge
  have hcos : Real.sin (1 / (16 * Real.pi)) ≤ z.re / ‖z‖ := by
    have h16 : (1 : ℝ) / (16 * Real.pi) ≤ 1 / Real.sqrt (1 + 64 * Real.pi ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have h1 : 1 + 64 * Real.pi ^ 2 ≤ (16 * Real.pi) ^ 2 := by
        nlinarith [Real.pi_gt_three, Real.pi_pos]
      calc Real.sqrt (1 + 64 * Real.pi ^ 2) ≤ Real.sqrt ((16 * Real.pi) ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = 16 * Real.pi := Real.sqrt_sq (by positivity)
    have hsin : Real.sin (1 / (16 * Real.pi)) ≤ 1 / (16 * Real.pi) :=
      (Real.sin_lt (by positivity)).le
    have hstep : 1 / Real.sqrt (1 + 64 * Real.pi ^ 2) ≤ z.re / ‖z‖ := by
      rw [hzre]
      have heq : 1 / Real.sqrt (1 + 64 * Real.pi ^ 2) =
          (1 / (N : ℝ)) / ((1 / (N : ℝ)) * Real.sqrt (1 + 64 * Real.pi ^ 2)) := by
        field_simp
      rw [heq]
      exact div_le_div_of_nonneg_left (by positivity) hzpos hnorm_le
    exact hsin.trans (h16.trans hstep)
  have hθmem : Real.pi / 2 - 1 / (16 * Real.pi) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨(pi_gap442).le, by
      have h1 : (0 : ℝ) < 1 / (16 * Real.pi) := by positivity
      linarith [Real.pi_pos]⟩
  have hargmem : |Complex.arg z| ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩
  have hcosarg : Real.cos |Complex.arg z| = z.re / ‖z‖ := by
    rw [Real.cos_abs, Complex.cos_arg hz]
  rw [← Real.cos_pi_div_two_sub (1 / (16 * Real.pi)), ← hcosarg] at hcos
  exact (Real.strictAntiOn_cos.le_iff_ge hθmem hargmem).mp hcos

/-- LEAF. First step of the parent proof, the modulus of the power factor.
For N at least two and alpha at most four over N the base of the power has
real part one over N and imaginary part at most eight pi over N, so the
imaginary part of its logarithm is at most pi over two minus one over
sixteen pi; its modulus is at least one over N, and N to the power a half
plus one over log N is at most e times the square root of N. No Gamma
factor, no logarithm of N, no integral here. -/
theorem mellin_base_bound442 (N : ℕ) (α t : ℝ) (hN : 2 ≤ N)
    (hα : |α| ≤ 4 / (N : ℝ)) :
    ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine1622 N t))‖ ≤
      Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  have hnorm_ge : 1 / (N : ℝ) ≤ ‖z‖ := by
    calc 1 / (N : ℝ) = |z.re| := by
          rw [hzre, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have harg : |Complex.arg z| ≤ Real.pi / 2 - 1 / (16 * Real.pi) :=
    arg_base_bound442 N α hN hα
  have hsre : (mellinLine1622 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsim : (mellinLine1622 N t).im = t := by
    simp only [mellinLine1622, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hσ : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := by positivity
  have hmul : (1 / 2 + 1 / Real.log N) * Real.log N = Real.log N / 2 + 1 := by
    field_simp
    try ring
  have hlogz : -(1 / 2 + 1 / Real.log N) * Real.log ‖z‖ ≤ Real.log N / 2 + 1 := by
    have h1 : Real.log (1 / (N : ℝ)) ≤ Real.log ‖z‖ :=
      Real.log_le_log (by positivity) hnorm_ge
    have h2 : Real.log (1 / (N : ℝ)) = -Real.log N := by
      rw [Real.log_div one_ne_zero hNr.ne']; simp
    have hσ' : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := hσ
    nlinarith [h1, h2, hmul]
  have htarg : t * Complex.arg z ≤ |t| * (Real.pi / 2 - 1 / (16 * Real.pi)) := by
    have hlow : -(Real.pi / 2 - 1 / (16 * Real.pi)) ≤ Complex.arg z := (abs_le.mp harg).1
    have hhigh : Complex.arg z ≤ Real.pi / 2 - 1 / (16 * Real.pi) := (abs_le.mp harg).2
    rcases lt_or_ge t 0 with ht | ht
    · rw [abs_of_neg ht]
      have h : t * (Complex.arg z + (Real.pi / 2 - 1 / (16 * Real.pi))) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ht.le (by linarith)
      nlinarith [h]
    · rw [abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left hhigh ht
  have hkey : (Complex.log z * (-(mellinLine1622 N t))).re ≤
      Real.log N / 2 + 1 + |t| * (Real.pi / 2 - 1 / (16 * Real.pi)) := by
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im,
      hsre, hsim]
    nlinarith [hlogz, htarg]
  rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp]
  refine (Real.exp_le_exp.mpr hkey).trans (le_of_eq ?_)
  have hexp_logN : Real.exp (Real.log N / 2) = Real.sqrt N := by
    rw [← Real.log_sqrt hNr.le, Real.exp_log (Real.sqrt_pos.mpr hNr)]
  rw [Real.exp_add, Real.exp_add, hexp_logN]
  try ring

/-- LEAF. Second step of the parent proof, the split of the logarithm.
For N at least two the logarithm of N times the sum of absolute t and two
is the sum of two nonnegative logarithms, so its cube is at most eight
cubes of log N plus eight cubes of the logarithm of the sum. -/
theorem log_cube_split442 (N : ℕ) (t : ℝ) (hN : 2 ≤ N) :
    Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      8 * Real.log N ^ 3 + 8 * Real.log (|t| + 2) ^ 3 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hu : (0 : ℝ) < |t| + 2 := by positivity
  have hu1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hsplit : Real.log ((N : ℝ) * (|t| + 2)) =
      Real.log N + Real.log (|t| + 2) := Real.log_mul hNr.ne' hu.ne'
  have hA : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  have hB : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg hu1
  rw [hsplit]
  set a := Real.log N with ha
  set b := Real.log (|t| + 2) with hb
  have hA' : 0 ≤ a := by rw [ha]; exact hA
  have hB' : 0 ≤ b := by rw [hb]; exact hB
  have h1 : 0 ≤ 2 * a ^ 3 + b ^ 3 - 3 * a ^ 2 * b := by
    rw [show 2 * a ^ 3 + b ^ 3 - 3 * a ^ 2 * b = (a - b) ^ 2 * (2 * a + b) by ring]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : 0 ≤ a ^ 3 + 2 * b ^ 3 - 3 * a * b ^ 2 := by
    rw [show a ^ 3 + 2 * b ^ 3 - 3 * a * b ^ 2 = (a - b) ^ 2 * (a + 2 * b) by ring]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have h3 : 0 ≤ a ^ 3 := pow_nonneg hA' 3
  have h4 : 0 ≤ b ^ 3 := pow_nonneg hB' 3
  nlinarith [h1, h2, h3, h4]

/-- `exp (-b * |t|)` is integrable on the line for `b > 0`. -/
private lemma integrable_exp_neg_abs442 (b : ℝ) (hb : 0 < b) :
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

/-- A fifth power is dominated by a constant times `exp (e * |t|)` for every `e > 0`: this is
Taylor's inequality `v ^ 5 ≤ 5 ! exp v` at `v = e * (|t| + 4)`, together with
`e * (|t| + 4) = e * |t| + 4 * e`. -/
private lemma shift_pow_five_le_exp442 (e : ℝ) (he : 0 < e) :
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

/-- The majorant `(|t| + 4) ^ 5 exp (-|t| / (16 pi))` of the twisted Gamma mass is
integrable on the line. -/
private lemma integrable_majorant442 :
    Integrable (fun t : ℝ => (|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
  obtain ⟨K, hK, hKle⟩ := shift_pow_five_le_exp442 (1 / (16 * Real.pi) / 2) (by positivity)
  have hbase : Integrable (fun t : ℝ => Real.exp (-(1 / (16 * Real.pi) / 2) * |t|)) :=
    integrable_exp_neg_abs442 _ (by positivity)
  refine Integrable.mono' (hbase.const_mul K) (by fun_prop) ?_
  filter_upwards with t
  have h1 : (|t| + 4) ^ 5 ≤ K * Real.exp (1 / (16 * Real.pi) / 2 * |t|) := hKle t
  have h2 : (0 : ℝ) ≤ (|t| + 4) ^ 5 := by positivity
  have h3 : (0 : ℝ) ≤ Real.exp (-(1 / (16 * Real.pi)) * |t|) := (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h2 h3)]
  calc (|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)
      ≤ (K * Real.exp (1 / (16 * Real.pi) / 2 * |t|)) *
          Real.exp (-(1 / (16 * Real.pi)) * |t|) :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = K * Real.exp (-(1 / (16 * Real.pi) / 2) * |t|) := by
        rw [mul_assoc, ← Real.exp_add,
          show 1 / (16 * Real.pi) / 2 * |t| + -(1 / (16 * Real.pi)) * |t| =
            -(1 / (16 * Real.pi) / 2) * |t| by ring]

/-- `mellinLine1622 N` is continuous in `t`. -/
private lemma continuous_mellinLine442 (N : ℕ) :
    Continuous fun t : ℝ => mellinLine1622 N t := by
  have h : (fun t : ℝ => mellinLine1622 N t) =
      fun t : ℝ => (((1 / 2 + 1 / Real.log N : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
    funext t
    simp [mellinLine1622]
  rw [h]
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- The Gamma factor on the shifted Mellin line decays exponentially in `|t|` for every
`N ≥ 2`. For a line with real part at most `3 / 2` this is `gamma_absolute_decay442`; otherwise
the real part is at most `5 / 2` and `Gamma s = (s - 1) Gamma (s - 1)` moves it into the strip. -/
private theorem gamma_line_uniform442 (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2)) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hinv : 1 / Real.log N ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hlog2 hlogle
  have hlog2' : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hre : (mellinLine1622 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (mellinLine1622 N t).im = t := by
    simp only [mellinLine1622, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hinvle : 1 / Real.log N ≤ 3 / 2 := by
    have h2 : 1 / Real.log 2 ≤ 3 / 2 := by
      rw [div_le_iff₀ hlog2]
      linarith
    linarith
  have hquad : ∀ x : ℝ, |x| + 4 ≤ (|x| + 4) ^ 2 := by
    intro x
    have h : (1 : ℝ) ≤ |x| + 4 := by linarith [abs_nonneg x]
    nlinarith [h, abs_nonneg x]
  have hsp : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by positivity
  by_cases hcase : (mellinLine1622 N t).re ≤ 3 / 2
  · have hlo : (1 : ℝ) / 2 ≤ (mellinLine1622 N t).re := by
      rw [hre]
      have hp : (0 : ℝ) < 1 / Real.log N := by positivity
      linarith
    have h := gamma_absolute_decay442 (mellinLine1622 N t) hlo hcase
    rw [him] at h
    have hnorm : ‖mellinLine1622 N t + 1‖ ≤ |t| + 4 := by
      have hb := Complex.norm_le_abs_re_add_abs_im (mellinLine1622 N t + 1)
      have hr : (mellinLine1622 N t + 1).re = 1 / 2 + 1 / Real.log N + 1 := by
        rw [Complex.add_re, Complex.one_re, hre]
      have hi : (mellinLine1622 N t + 1).im = t := by
        rw [Complex.add_im, Complex.one_im, him]; ring
      rw [hr, hi] at hb
      have hre2 : |1 / 2 + 1 / Real.log N + 1| ≤ 4 := by
        rw [abs_of_pos (by positivity)]
        linarith
      linarith [abs_nonneg t]
    have he : (0 : ℝ) ≤ Real.exp (-(Real.pi * |t| / 2)) := (Real.exp_pos _).le
    have hnorm2 : ‖mellinLine1622 N t + 1‖ ≤ (|t| + 4) ^ 2 := le_trans hnorm (hquad t)
    have hstep : Real.sqrt (2 * Real.pi) * ‖mellinLine1622 N t + 1‖ *
        Real.exp (-(Real.pi * |t| / 2)) ≤
        Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2)) := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul_of_nonneg_left hnorm2 hsp
    exact h.trans hstep
  · push_neg at hcase
    have hσle : (mellinLine1622 N t).re ≤ 5 / 2 := by rw [hre]; linarith
    have hre1 : (mellinLine1622 N t - 1).re = 1 / 2 + 1 / Real.log N - 1 := by
      rw [Complex.sub_re, Complex.one_re, hre]
    have him1 : (mellinLine1622 N t - 1).im = t := by
      rw [Complex.sub_im, Complex.one_im, him]; ring
    have hne : mellinLine1622 N t - 1 ≠ 0 := by
      intro h
      have h' := congr_arg Complex.re h
      rw [hre1] at h'
      simp only [Complex.zero_re] at h'
      linarith [hlog]
    have hGam : Complex.Gamma (mellinLine1622 N t) =
        (mellinLine1622 N t - 1) * Complex.Gamma (mellinLine1622 N t - 1) := by
      have h := Complex.Gamma_add_one (mellinLine1622 N t - 1) hne
      rwa [sub_add_cancel] at h
    have hpos1 : (1 : ℝ) / 2 ≤ (mellinLine1622 N t - 1).re := by rw [hre1]; linarith
    have hle1 : (mellinLine1622 N t - 1).re ≤ 3 / 2 := by rw [hre1]; linarith
    have hbound := gamma_absolute_decay442 (mellinLine1622 N t - 1) hpos1 hle1
    rw [him1] at hbound
    have hb2 : ‖Complex.Gamma (mellinLine1622 N t - 1)‖ ≤
        Real.sqrt (2 * Real.pi) * ‖mellinLine1622 N t‖ * Real.exp (-(Real.pi * |t| / 2)) := by
      have h := hbound
      rwa [sub_add_cancel] at h
    have hn1 : ‖mellinLine1622 N t - 1‖ ≤ |t| + 2 := by
      have hb := Complex.norm_le_abs_re_add_abs_im (mellinLine1622 N t - 1)
      rw [hre1, him1] at hb
      have hre2 : |1 / 2 + 1 / Real.log N - 1| ≤ 2 := by
        rw [abs_le]
        constructor <;> linarith
      linarith [abs_nonneg t]
    have hn0 : ‖mellinLine1622 N t‖ ≤ |t| + 3 := by
      have hb := Complex.norm_le_abs_re_add_abs_im (mellinLine1622 N t)
      rw [hre, him] at hb
      have hre2 : |1 / 2 + 1 / Real.log N| ≤ 3 := by
        rw [abs_of_pos (by positivity)]
        linarith
      linarith [abs_nonneg t]
    rw [hGam, norm_mul]
    have he : (0 : ℝ) ≤ Real.exp (-(Real.pi * |t| / 2)) := (Real.exp_pos _).le
    have hstep1 : ‖mellinLine1622 N t - 1‖ *
        ‖Complex.Gamma (mellinLine1622 N t - 1)‖ ≤
        (|t| + 2) * (Real.sqrt (2 * Real.pi) * ‖mellinLine1622 N t‖ *
          Real.exp (-(Real.pi * |t| / 2))) :=
      mul_le_mul hn1 hb2 (norm_nonneg _) (by positivity)
    refine hstep1.trans ?_
    have hinner : Real.sqrt (2 * Real.pi) * ‖mellinLine1622 N t‖ *
        Real.exp (-(Real.pi * |t| / 2)) ≤
        Real.sqrt (2 * Real.pi) * (|t| + 3) * Real.exp (-(Real.pi * |t| / 2)) := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul_of_nonneg_left hn0 hsp
    have hstep2 : (|t| + 2) * (Real.sqrt (2 * Real.pi) * ‖mellinLine1622 N t‖ *
        Real.exp (-(Real.pi * |t| / 2))) ≤
        (|t| + 2) * (Real.sqrt (2 * Real.pi) * (|t| + 3) *
          Real.exp (-(Real.pi * |t| / 2))) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    refine hstep2.trans ?_
    have hq2 : (|t| + 2) * (|t| + 3) ≤ (|t| + 4) ^ 2 := by nlinarith [abs_nonneg t]
    calc (|t| + 2) * (Real.sqrt (2 * Real.pi) * (|t| + 3) * Real.exp (-(Real.pi * |t| / 2)))
        = ((|t| + 2) * (|t| + 3)) *
            (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 2))) := by ring
      _ ≤ ((|t| + 4) ^ 2) * (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |t| / 2))) :=
          mul_le_mul_of_nonneg_right hq2 (by positivity)
      _ = Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2)) := by ring

/-- Pointwise domination of the twisted Gamma mass with a logarithm factor. -/
private lemma gamma_twist_pointwise442 (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine1622 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) ≤
      Real.sqrt (2 * Real.pi) * 2 *
        ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
  have hg := gamma_line_uniform442 N hN t
  have hfac : (0 : ℝ) ≤ Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) :=
    (Real.exp_pos _).le
  have h1 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2))) :=
    mul_le_mul_of_nonneg_left hg hfac
  have hee : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      Real.exp (-(Real.pi * |t| / 2)) = Real.exp (-(1 / (16 * Real.pi)) * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmid : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (Real.sqrt (2 * Real.pi) * (|t| + 4) ^ 2 * Real.exp (-(Real.pi * |t| / 2))) =
      Real.sqrt (2 * Real.pi) * ((|t| + 4) ^ 2 *
        (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          Real.exp (-(Real.pi * |t| / 2)))) := by ring
  have h2 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
      Real.sqrt (2 * Real.pi) *
        ((|t| + 4) ^ 2 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
    rw [hmid, hee] at h1
    exact h1
  have hlogp0 : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
    have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
    positivity
  have hlogp1 : (1 : ℝ) ≤ 1 + Real.log (|t| + 2) ^ 3 := by linarith
  have hlog3 : (1 : ℝ) + Real.log (|t| + 2) ^ 3 ≤ 2 * (|t| + 4) ^ 3 := by
    have h1' : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    have h2' : Real.log (|t| + 2) ≤ |t| + 2 := Real.log_le_self (by linarith)
    have h3' : Real.log (|t| + 2) ≤ |t| + 4 := by linarith
    have h4' : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1'
    have h5' : Real.log (|t| + 2) ^ 3 ≤ (|t| + 4) ^ 3 := pow_le_pow_left₀ h4' h3' 3
    have h6' : (1 : ℝ) ≤ (|t| + 4) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg t])
    linarith
  have h4 : (0 : ℝ) ≤ (|t| + 4) ^ 2 := by positivity
  have h5 : (0 : ℝ) ≤ Real.exp (-(1 / (16 * Real.pi)) * |t|) := (Real.exp_pos _).le
  have h3 : (|t| + 4) ^ 2 * (1 + Real.log (|t| + 2) ^ 3) ≤ 2 * (|t| + 4) ^ 5 := by
    have := mul_le_mul_of_nonneg_left hlog3 h4
    calc (|t| + 4) ^ 2 * (1 + Real.log (|t| + 2) ^ 3) ≤
        (|t| + 4) ^ 2 * (2 * (|t| + 4) ^ 3) := this
      _ = 2 * (|t| + 4) ^ 5 := by ring
  calc Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine1622 N t)‖ * (1 + Real.log (|t| + 2) ^ 3)
      = (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) * (1 + Real.log (|t| + 2) ^ 3) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi) *
          ((|t| + 4) ^ 2 * Real.exp (-(1 / (16 * Real.pi)) * |t|))) *
          (1 + Real.log (|t| + 2) ^ 3) := by
        exact mul_le_mul_of_nonneg_right h2 (by linarith)
    _ = Real.sqrt (2 * Real.pi) *
          ((|t| + 4) ^ 2 * (1 + Real.log (|t| + 2) ^ 3)) *
          Real.exp (-(1 / (16 * Real.pi)) * |t|) := by ring
    _ ≤ Real.sqrt (2 * Real.pi) * (2 * (|t| + 4) ^ 5) *
          Real.exp (-(1 / (16 * Real.pi)) * |t|) := by
        apply mul_le_mul_of_nonneg_right _ h5
        apply mul_le_mul_of_nonneg_left h3
        exact Real.sqrt_nonneg _
    _ = Real.sqrt (2 * Real.pi) * 2 *
          ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by ring

/-- `Gamma` composed with the shifted Mellin line is continuous: the line has positive real
part, so it stays away from the poles of `Gamma`. -/
private lemma continuous_gamma_mellin442 (N : ℕ) (hN : 2 ≤ N) :
    Continuous fun t : ℝ => Complex.Gamma (mellinLine1622 N t) := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hre : ∀ t : ℝ, (mellinLine1622 N t).re = 1 / 2 + 1 / Real.log N := by
    intro t
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hpos : (0 : ℝ) < 1 / 2 + 1 / Real.log N := by positivity
  have hne : ∀ t : ℝ, ∀ m : ℕ, mellinLine1622 N t ≠ -(m : ℂ) := by
    intro t m h
    have h1 := congr_arg Complex.re h
    rw [hre t] at h1
    have h3 : (-(m : ℂ)).re = -(m : ℝ) := by push_cast; simp
    rw [h3] at h1
    have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith [hpos]
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  exact ((Complex.differentiableAt_Gamma _ (hne t)).continuousAt).comp
    (continuous_mellinLine442 N).continuousAt

/-- LEAF. Third step of the parent proof, the twisted Gamma mass. The
Gamma factor on the line, weighted by the exponential gap of the power
factor and by the cube of the logarithm of the sum of absolute t and two,
is integrable for every N at least two, and both of its integrals are at
most one constant independent of N and of alpha. This is the analytic core
of the parent proof and the only place where the decay of Gamma is used. -/
theorem gamma_twist_mass442 :
    ∃ G : ℝ, 0 < G ∧ ∀ N : ℕ, 2 ≤ N →
      Integrable (fun t : ℝ =>
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) ∧
      Integrable (fun t : ℝ =>
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3)) ∧
      (∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine1622 N t)‖) ≤ G ∧
      (∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log (|t| + 2) ^ 3)) ≤ G := by
  have hM : Integrable (fun t : ℝ =>
      (|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := integrable_majorant442
  have h2pi : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) * 2 := by positivity
  have hMc : Integrable (fun t : ℝ => Real.sqrt (2 * Real.pi) * 2 *
      ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|))) := hM.const_mul _
  have hInt_nonneg : (0 : ℝ) ≤ ∫ t : ℝ, Real.sqrt (2 * Real.pi) * 2 *
      ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) :=
    integral_nonneg (fun t => by positivity)
  refine ⟨(∫ t : ℝ, Real.sqrt (2 * Real.pi) * 2 *
    ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|))) + 1, by linarith, ?_⟩
  intro N hN
  have hpt := gamma_twist_pointwise442 N hN
  have hApt : ∀ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * 2 *
        ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
    intro t
    have h := hpt t
    have hlogp1 : (1 : ℝ) ≤ 1 + Real.log (|t| + 2) ^ 3 := by
      have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
      have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
      have h3 : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by positivity
      linarith
    have h3 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) := by
      calc Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine1622 N t)‖
          = Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine1622 N t)‖ * 1 := by ring
        _ ≤ Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine1622 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) := by
            apply mul_le_mul_of_nonneg_left hlogp1
            positivity
    exact h3.trans h
  have hBpt : ∀ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
      (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3) ≤
      Real.sqrt (2 * Real.pi) * 2 *
        ((|t| + 4) ^ 5 * Real.exp (-(1 / (16 * Real.pi)) * |t|)) := by
    intro t
    have h := hpt t
    have hlogp : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
      have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
      have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
      positivity
    have h3 : Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3) ≤
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖ * (1 + Real.log (|t| + 2) ^ 3) := by
      rw [show Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine1622 N t)‖ * (1 + Real.log (|t| + 2) ^ 3)
          = Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine1622 N t)‖ * (1 + Real.log (|t| + 2) ^ 3)) by ring]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      linarith
    exact h3.trans h
  have hGamma_cont : Continuous fun t : ℝ => Complex.Gamma (mellinLine1622 N t) :=
    continuous_gamma_mellin442 N hN
  have hAcont : Continuous fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine1622 N t)‖ :=
    (Real.continuous_exp.comp (continuous_abs.mul continuous_const)).mul hGamma_cont.norm
  have hBcont : Continuous fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3) :=
    (Real.continuous_exp.comp (continuous_abs.mul continuous_const)).mul
      (hGamma_cont.norm.mul (((continuous_abs.add continuous_const).log
        (fun t => ne_of_gt (by positivity : (0 : ℝ) < |t| + 2))).pow 3))
  have hAi : Integrable (fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine1622 N t)‖) := by
    refine Integrable.mono' hMc hAcont.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    exact hApt t
  have hBi : Integrable (fun t : ℝ =>
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
    refine Integrable.mono' hMc hBcont.aestronglyMeasurable ?_
    filter_upwards with t
    have hlogp : (0 : ℝ) ≤ Real.log (|t| + 2) ^ 3 := by
      have h1 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
      have h2 : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg h1
      positivity
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (norm_nonneg _) hlogp))]
    exact hBpt t
  exact ⟨hAi, hBi, (integral_mono hAi hMc hApt).trans (by linarith),
    (integral_mono hBi hMc hBpt).trans (by linarith)⟩


/-- LEAF. Fourth step of the parent proof, the integrability half of the
parent conclusion. The modulus of the kernel times the cube of the
logarithm of N times the sum of absolute t and two is integrable, for N at
least thirty two and alpha at most four over N. This is the first
conjunct of the parent statement on its own, without any estimate of the
integral. -/
theorem kernel_mass_integrable442 (N : ℕ) (α : ℝ) (hN : 32 ≤ N)
    (hα : |α| ≤ 4 / (N : ℝ)) :
    Integrable (fun t : ℝ => ‖mellinKernel442 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNr2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hzre : z.re = 1 / (N : ℝ) := by simp [hzdef]
  have hzrepos : 0 < z.re := by rw [hzre]; positivity
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzrepos; simp at hzrepos
  obtain ⟨G, hGpos, hG⟩ := gamma_twist_mass442
  obtain ⟨hAi, hBi, -, -⟩ := hG N hN2
  have hdomint : Integrable (fun t : ℝ => 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3))) := by
    have h1 : Integrable (fun t : ℝ => Real.log N ^ 3 *
        (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖)) := hAi.const_mul _
    exact (h1.add hBi).const_mul _
  have hcont : Continuous fun t : ℝ => ‖mellinKernel442 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
    have hg : Continuous fun t : ℝ => Complex.Gamma (mellinLine1622 N t) :=
      continuous_gamma_mellin442 N hN2
    have he : Continuous fun t : ℝ =>
        Complex.exp (Complex.log z * (-(mellinLine1622 N t))) :=
      Complex.continuous_exp.comp (continuous_const.mul (continuous_mellinLine442 N).neg)
    have h1 : Continuous fun t : ℝ => mellinKernel442 N α t := by
      have hfun : (fun t : ℝ => mellinKernel442 N α t) =
          fun t => Complex.exp (Complex.log z * (-(mellinLine1622 N t))) *
            Complex.Gamma (mellinLine1622 N t) := by
        funext t
        unfold mellinKernel442
        rw [Complex.cpow_def_of_ne_zero hz]
      rw [hfun]
      exact he.mul hg
    have harg : Continuous fun t : ℝ => (N : ℝ) * (|t| + 2) :=
      continuous_const.mul (continuous_abs.add continuous_const)
    have h2 : Continuous fun t : ℝ => Real.log ((N : ℝ) * (|t| + 2)) :=
      harg.log (fun t => ne_of_gt (by positivity))
    exact h1.norm.mul (h2.pow 3)
  refine Integrable.mono' hdomint hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hbase := mellin_base_bound442 N α t hN2 hα
  have hlog := log_cube_split442 N t hN2
  have hk : ‖mellinKernel442 N α t‖ ≤ Real.exp 1 * Real.sqrt N *
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine1622 N t)‖ := by
    unfold mellinKernel442
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
  have hpos : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
    have h1 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
      Real.log_nonneg (by nlinarith [abs_nonneg t, hNr2])
    positivity
  have hf : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt N *
      Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine1622 N t)‖ := by positivity
  have h1 := mul_le_mul hk hlog hpos hf
  have hEq : (Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) *
      (8 * Real.log N ^ 3 + 8 * Real.log (|t| + 2) ^ 3) =
      8 * Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine1622 N t)‖) +
          Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
    ring
  rw [hEq] at h1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hpos)]
  exact h1
/-- LEAF. Fifth step of the parent proof, the bookkeeping of the constant.
For N at least thirty two and a positive constant G, eight e times the
square root of N times the cube of log N times G plus G is at most the
cube of log N times the square root of N times the constant eight e G
times one plus the inverse cube of log two. The last factor absorbs the
additive G because the cube of log N is at least the cube of log two. -/
theorem mass_constant442 (N : ℕ) (G : ℝ) (hN : 32 ≤ N) (hG : 0 < G) :
    8 * Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G) ≤
      8 * Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3) * Real.sqrt N *
        Real.log N ^ 3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have hlr : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hlogN : 0 < Real.log N := lt_of_lt_of_le hlog2 hlr
  have hl3 : Real.log 2 ^ 3 ≤ Real.log N ^ 3 := pow_le_pow_left₀ hlog2.le hlr 3
  have h19 : (1 : ℝ) ≤ Real.log N ^ 3 / Real.log 2 ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    simpa using hl3
  have hGeq : G ≤ G * (Real.log N ^ 3 / Real.log 2 ^ 3) := by
    simpa using mul_le_mul_of_nonneg_left h19 hG.le
  have hc : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt N := by positivity
  have hkey : Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G) ≤
      Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * G + G * (Real.log N ^ 3 / Real.log 2 ^ 3)) := by
    apply mul_le_mul_of_nonneg_left _ hc
    nlinarith [hGeq]
  have hEq : Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * G + G * (Real.log N ^ 3 / Real.log 2 ^ 3)) =
      Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3) * Real.sqrt N *
        Real.log N ^ 3 := by
    field_simp
    try ring
  calc 8 * Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G)
      = 8 * (Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G)) := by ring
    _ ≤ 8 * (Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * G + G * (Real.log N ^ 3 / Real.log 2 ^ 3))) := by
        linarith [hkey]
    _ = 8 * Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3) * Real.sqrt N *
        Real.log N ^ 3 := by
        rw [hEq]; try ring

/-- The parent statement central_kernel_mass442, reassembled from the five
leaves above. No use of the parent theorem, no placeholder proof. -/
theorem central_kernel_mass442_split :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, |α| ≤ 4 / (N : ℝ) →
        Integrable (fun t : ℝ => ‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧
        (∫ t : ℝ, ‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
            C * Real.sqrt N * Real.log N ^ 3 := by
  obtain ⟨G, hGpos, hG⟩ := gamma_twist_mass442
  refine ⟨8 * Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3), ?_, 31, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < 1 + 1 / Real.log 2 ^ 3 := by positivity
    positivity
  intro N hN α hα
  have hN32 : 32 ≤ N := hN
  have hN2 : 2 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  obtain ⟨hAi, hBi, hA, hB⟩ := hG N hN2
  have hdomint : Integrable (fun t : ℝ => 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3))) := by
    have h1 : Integrable (fun t : ℝ => Real.log N ^ 3 *
        (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖)) := hAi.const_mul _
    exact (h1.add hBi).const_mul _
  have hpoint : ∀ t : ℝ, ‖mellinKernel442 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      8 * Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine1622 N t)‖) +
          Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
    intro t
    have hbase := mellin_base_bound442 N α t hN2 hα
    have hlog := log_cube_split442 N t hN2
    have hk : ‖mellinKernel442 N α t‖ ≤ Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖ := by
      unfold mellinKernel442
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
    have hpos : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
      have h1 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
        Real.log_nonneg (by nlinarith [abs_nonneg t, hNr])
      positivity
    have hf : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖ := by positivity
    have h1 := mul_le_mul hk hlog hpos hf
    have hEq : (Real.exp 1 * Real.sqrt N *
          Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine1622 N t)‖) *
        (8 * Real.log N ^ 3 + 8 * Real.log (|t| + 2) ^ 3) =
        8 * Real.exp 1 * Real.sqrt N *
          (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine1622 N t)‖) +
            Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
      ring
    rw [hEq] at h1
    exact h1
  have hval : (∫ t : ℝ, 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3))) =
      8 * Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * (∫ t : ℝ,
            Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine1622 N t)‖) +
          ∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine1622 N t)‖ *
              Real.log (|t| + 2) ^ 3)) := by
    rw [integral_const_mul, integral_add (hAi.const_mul _) hBi, integral_const_mul]
  have hub : (∫ t : ℝ, 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3))) ≤
      8 * Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G) := by
    rw [hval]
    have hc : (0 : ℝ) ≤ 8 * Real.exp 1 * Real.sqrt N := by positivity
    have hl : (0 : ℝ) ≤ Real.log N ^ 3 := pow_nonneg hlogN.le 3
    have h1 : Real.log N ^ 3 * (∫ t : ℝ,
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) ≤ Real.log N ^ 3 * G :=
      mul_le_mul_of_nonneg_left hA hl
    have h2 : (∫ t : ℝ,
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine1622 N t)‖ *
            Real.log (|t| + 2) ^ 3)) ≤ G := hB
    exact mul_le_mul_of_nonneg_left (by linarith) hc
  exact ⟨kernel_mass_integrable442 N α hN32 hα,
    (integral_mono (kernel_mass_integrable442 N α hN32 hα) hdomint hpoint).trans
      (hub.trans (mass_constant442 N G hN32 hGpos))⟩

end LeanLab.Linnik1951
