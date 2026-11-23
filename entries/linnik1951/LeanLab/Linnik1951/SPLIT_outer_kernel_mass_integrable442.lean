module

public import LeanLab.Linnik1951.SPLIT_abstract_outer_kernels442

/-!
Split of the outer frequency square integrability `outer_kernel_mass_integrable442`.

The target asks that the square of the absolute log weighted Mellin kernel mass be
interval integrable in the frequency over the outer interval from 4 over N to 1 over R.
That is a compactness statement about a parametric integral, and it is proved here in
three steps.

Step 1 dominates the line integrand by one integrable function of the line variable,
uniformly over the whole outer frequency interval. The real part of the shifted line is
fixed, the base has real part 1 over N and the frequency is at least 4 over N, so the
ratio of the imaginary part of the base to its real part stays at least 8 pi and the
Gamma decay against the exponential of the complex power leaves an integrable weight.
Step 2 and step 3 record the two continuities the parametric integral needs: in the
frequency at fixed line point, and along the line at fixed frequency, the second giving
measurability in the line variable.

Nothing here changes the sealed statement: `outer_kernel_mass_integrable442_split`
restates the target character for character and derives it from the three leaves
without using the original theorem.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory Filter
open scoped Topology

private lemma exp_neg_abs_le_inv_sq (c : ℝ) (hc : 0 < c) (t : ℝ) :
    Real.exp (-(c * |t|)) ≤ (2 + 12 / c ^ 3) * (1 + t ^ 2)⁻¹ := by
  have hc3 : (0 : ℝ) < c ^ 3 := by positivity
  rcases le_total |t| 1 with h1 | h1
  · have hL : Real.exp (-(c * |t|)) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg t]
    have hR : (1 : ℝ) ≤ (2 + 12 / c ^ 3) * (1 + t ^ 2)⁻¹ := by
      have h2 : (2 : ℝ) ≤ 2 + 12 / c ^ 3 := by
        have hpos12 : (0 : ℝ) < 12 / c ^ 3 := by positivity
        linarith
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t, h1]
      have hinv : (1 / 2 : ℝ) ≤ (1 + t ^ 2)⁻¹ := by
        have hle : 1 + t ^ 2 ≤ 2 := by linarith
        calc (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
          _ ≤ (1 + t ^ 2)⁻¹ := inv_anti₀ (by nlinarith [sq_nonneg t]) hle
      calc (1 : ℝ) = 2 * (1 / 2) := by norm_num
        _ ≤ (2 + 12 / c ^ 3) * (1 + t ^ 2)⁻¹ :=
            mul_le_mul h2 hinv (by norm_num) (by linarith)
    linarith
  · have ht1 : (1 : ℝ) ≤ |t| := h1
    have hpos : (0 : ℝ) < c * |t| := by positivity
    have hfac := Real.pow_div_factorial_le_exp (x := c * |t|) hpos.le 3
    norm_num at hfac
    have h3 : (c * |t|) ^ 3 / 6 ≤ Real.exp (c * |t|) := hfac
    have hexp : Real.exp (-(c * |t|)) = (Real.exp (c * |t|))⁻¹ := by
      rw [← Real.exp_neg]
    rw [hexp]
    have hinv : (Real.exp (c * |t|))⁻¹ ≤ 6 / (c * |t|) ^ 3 := by
      have hcube : (0 : ℝ) < (c * |t|) ^ 3 := by positivity
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 6)] at h3
      rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
      have h4 : (1 : ℝ) ≤ Real.exp (c * |t|) * 6 / (c * |t|) ^ 3 := (one_le_div hcube).mpr h3
      have he : 6 / (c * |t|) ^ 3 * Real.exp (c * |t|) =
          Real.exp (c * |t|) * 6 / (c * |t|) ^ 3 := by ring
      rw [he]
      exact h4
    have hbound : 6 / (c * |t|) ^ 3 ≤ (2 + 12 / c ^ 3) * (1 + t ^ 2)⁻¹ := by
      have ht3 : (1 : ℝ) ≤ |t| ^ 3 := by
        calc (1:ℝ) = 1 ^ 3 := by norm_num
          _ ≤ |t| ^ 3 := pow_le_pow_left₀ (by norm_num) ht1 3
      have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      have hden : (c * |t|) ^ 3 = c ^ 3 * |t| ^ 3 := by ring
      rw [hden, ht2]
      have hA : (0 : ℝ) < c ^ 3 * |t| ^ 3 := by positivity
      have hB : (0 : ℝ) < 1 + |t| ^ 2 := by positivity
      rw [div_le_iff₀ hA]
      have hpoly : 6 * (1 + |t| ^ 2) ≤ (2 + 12 / c ^ 3) * (c ^ 3 * |t| ^ 3) := by
        have e1 : (2 + 12 / c ^ 3) * (c ^ 3 * |t| ^ 3) =
            2 * c ^ 3 * |t| ^ 3 + 12 * |t| ^ 3 := by
          field_simp
        rw [e1]
        have h12 : 12 * |t| ^ 2 ≤ 12 * |t| ^ 3 := by nlinarith [ht3, sq_nonneg |t|, ht1]
        have hone : 1 + |t| ^ 2 ≤ 2 * |t| ^ 2 := by nlinarith [ht1]
        have hpos2 : (0 : ℝ) ≤ 2 * c ^ 3 * |t| ^ 3 := by positivity
        nlinarith [h12, hone, hpos2]
      have e : (2 + 12 / c ^ 3) * (1 + |t| ^ 2)⁻¹ * (c ^ 3 * |t| ^ 3) =
          (2 + 12 / c ^ 3) * (c ^ 3 * |t| ^ 3) / (1 + |t| ^ 2) := by
        rw [inv_eq_one_div]; ring
      rw [e]
      have e2 : (6 : ℝ) = 6 * (1 + |t| ^ 2) / (1 + |t| ^ 2) := by
        field_simp
      rw [e2]
      exact div_le_div_of_nonneg_right hpoly hB.le
    exact hinv.trans hbound

/-- `exp (-(c * |t|))` is integrable for `c > 0`. -/
private lemma integrable_exp_neg_abs_mul (c : ℝ) (hc : 0 < c) :
    Integrable (fun t : ℝ => Real.exp (-(c * |t|))) := by
  have hdom : Integrable (fun t : ℝ =>
      (2 + 12 / c ^ 3) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hdom (by fun_prop) (Filter.Eventually.of_forall (fun t => ?_))
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact exp_neg_abs_le_inv_sq c hc t

/-- `(s + 3) ^ k` is dominated by a half exponential. -/
private lemma poly_pow_le_exp (c : ℝ) (hc : 0 < c) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (s + 3) ^ k ≤ (6 ^ k + (4 / c) ^ k * (k.factorial : ℝ)) * Real.exp (c * s / 2) := by
  have hpos : (0 : ℝ) ≤ 6 ^ k + (4 / c) ^ k * (k.factorial : ℝ) := by positivity
  rcases le_total s 3 with h3 | h3
  · have h6 : s + 3 ≤ 6 := by linarith
    have h0 : (0 : ℝ) ≤ s + 3 := by linarith
    have hp : (s + 3) ^ k ≤ 6 ^ k := pow_le_pow_left₀ h0 h6 k
    have he : (1 : ℝ) ≤ Real.exp (c * s / 2) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      positivity
    have hmul : (6 : ℝ) ^ k ≤ (6 ^ k + (4 / c) ^ k * (k.factorial : ℝ)) *
        Real.exp (c * s / 2) := by
      have hle : (6 : ℝ) ^ k ≤ 6 ^ k + (4 / c) ^ k * (k.factorial : ℝ) := by
        have : (0 : ℝ) ≤ (4 / c) ^ k * (k.factorial : ℝ) := by positivity
        linarith
      calc (6 : ℝ) ^ k ≤ 6 ^ k + (4 / c) ^ k * (k.factorial : ℝ) := hle
        _ = (6 ^ k + (4 / c) ^ k * (k.factorial : ℝ)) * 1 := by ring
        _ ≤ (6 ^ k + (4 / c) ^ k * (k.factorial : ℝ)) * Real.exp (c * s / 2) :=
            mul_le_mul_of_nonneg_left he hpos
    exact hp.trans hmul
  · have h2 : s + 3 ≤ 2 * s := by linarith
    have h0 : (0 : ℝ) ≤ s + 3 := by linarith
    have hp : (s + 3) ^ k ≤ (2 * s) ^ k := pow_le_pow_left₀ h0 h2 k
    have hx : (0 : ℝ) ≤ c * s / 2 := by positivity
    have hfac := Real.pow_div_factorial_le_exp (x := c * s / 2) hx k
    have hc2 : (0 : ℝ) < (c / 2) ^ k := by positivity
    have hkey : s ^ k ≤ (2 / c) ^ k * (k.factorial : ℝ) * Real.exp (c * s / 2) := by
      have hcalc : (c * s / 2) ^ k / (k.factorial : ℝ) = (c / 2) ^ k * s ^ k / (k.factorial : ℝ) := by
        ring
      rw [hcalc, div_le_iff₀ (by positivity : (0:ℝ) < (k.factorial : ℝ))] at hfac
      have hstep : s ^ k ≤ (Real.exp (c * s / 2) * (k.factorial : ℝ)) / ((c / 2) ^ k) := by
        rw [le_div_iff₀ hc2]
        linarith [hfac]
      have h4c : (2 / c) ^ k * (k.factorial : ℝ) * Real.exp (c * s / 2) =
          (Real.exp (c * s / 2) * (k.factorial : ℝ)) / ((c / 2) ^ k) := by
        rw [eq_div_iff (ne_of_gt hc2)]
        have hone : (2 / c) ^ k * (c / 2) ^ k = 1 := by
          rw [← mul_pow]
          have h1 : 2 / c * (c / 2) = 1 := by field_simp
          rw [h1, one_pow]
        calc (2 / c) ^ k * (k.factorial : ℝ) * Real.exp (c * s / 2) * (c / 2) ^ k
            = ((2 / c) ^ k * (c / 2) ^ k) * ((k.factorial : ℝ) * Real.exp (c * s / 2)) := by
              ring
          _ = (k.factorial : ℝ) * Real.exp (c * s / 2) := by rw [hone]; ring
          _ = Real.exp (c * s / 2) * (k.factorial : ℝ) := by ring
      rw [h4c]
      exact hstep
    have hp2 : (2 * s) ^ k = 2 ^ k * s ^ k := by ring
    have h26 : 2 ^ k * (2 / c) ^ k = (4 / c) ^ k := by
      have h24 : 2 * (2 / c) = 4 / c := by
        field_simp
        norm_num
      rw [← mul_pow, h24]
    calc (s + 3) ^ k ≤ (2 * s) ^ k := hp
      _ = 2 ^ k * s ^ k := hp2
      _ ≤ 2 ^ k * ((2 / c) ^ k * (k.factorial : ℝ) * Real.exp (c * s / 2)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = ((4 / c) ^ k * (k.factorial : ℝ)) * Real.exp (c * s / 2) := by
          rw [show 2 ^ k * ((2 / c) ^ k * (k.factorial : ℝ) * Real.exp (c * s / 2)) =
              (2 ^ k * (2 / c) ^ k * (k.factorial : ℝ)) * Real.exp (c * s / 2) from by ring, h26]
      _ ≤ (6 ^ k + (4 / c) ^ k * (k.factorial : ℝ)) * Real.exp (c * s / 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have h6k : (0 : ℝ) ≤ 6 ^ k := by positivity
          have hnk : (0 : ℝ) ≤ (4 / c) ^ k * (k.factorial : ℝ) := by positivity
          linarith



open MeasureTheory

/-- Gamma decay on the shifted Mellin line (adapted from
`LeanLab.Linnik1951.Gamma442.gamma_mellin_line442`, restated here so that
this file needs only the Mathlib-clean `GammaBounds` module). -/
private theorem gamma_line_decay442 (N : ℕ) (hN : 3 ≤ N) (t : ℝ) :
    ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2)) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.le.trans hNr)
  have hlog : 0 < Real.log N := by linarith
  have hinv : 1 / Real.log N ≤ 1 := (div_le_one hlog).mpr hl
  have hre : (mellinLine1622 N t).re = 1 / 2 + 1 / Real.log N := by
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (mellinLine1622 N t).im = t := by
    simp only [mellinLine1622, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hinvpos : 0 < 1 / Real.log N := div_pos one_pos hlog
  have hlo : 1 / 2 ≤ (mellinLine1622 N t).re := by rw [hre]; linarith
  have hhi : (mellinLine1622 N t).re ≤ 3 / 2 := by rw [hre]; linarith
  have hnorm : ‖mellinLine1622 N t + 1‖ ≤ 3 + |t| := by
    have hh := Complex.norm_le_abs_re_add_abs_im (mellinLine1622 N t + 1)
    have hr : (mellinLine1622 N t + 1).re = 1 / 2 + 1 / Real.log N + 1 := by simp [hre]
    have hi : (mellinLine1622 N t + 1).im = t := by simp [him]
    rw [hr, hi, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 + 1 / Real.log N + 1)] at hh
    linarith
  rcases lt_or_ge t 0 with ht | ht
  · have h2 := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL (s := star (mellinLine1622 N t))
      (by simpa using hlo) (by simpa using hhi)
    have hg : ‖Complex.Gamma (star (mellinLine1622 N t))‖ =
        ‖Complex.Gamma (mellinLine1622 N t)‖ := by
      simp only [Complex.star_def, Complex.Gamma_conj, Complex.norm_conj]
    have hn : ‖star (mellinLine1622 N t) + 1‖ = ‖mellinLine1622 N t + 1‖ := by
      simpa using norm_star (mellinLine1622 N t + 1)
    have hi2 : (star (mellinLine1622 N t)).im = -t := by simp [him]
    rw [hg, hn, hi2] at h2
    have h2' : ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
        Real.sqrt (2 * Real.pi) * ‖mellinLine1622 N t + 1‖ *
          Real.exp (-(Real.pi * |t| / 2)) := by
      rw [abs_of_neg ht]; exact h2
    exact h2'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm (by positivity)) (Real.exp_pos _).le)
  · have h := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL (s := mellinLine1622 N t) hlo hhi
    rw [him] at h
    have h' : ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
        Real.sqrt (2 * Real.pi) * ‖mellinLine1622 N t + 1‖ *
          Real.exp (-(Real.pi * |t| / 2)) := by
      rw [abs_of_nonneg ht]; exact h
    exact h'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm (by positivity)) (Real.exp_pos _).le)


/-- The absolute Mellin weight `(3 + |t|) * log (N (|t| + 2)) ^ m * exp (-c |t|)` is integrable. -/
private theorem integrable_weight_log (N : ℕ) (hN : 2 ≤ N) (c : ℝ) (hc : 0 < c) (m : ℕ) :
    Integrable (fun t : ℝ =>
      (3 + |t|) * Real.exp (-(c * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ m) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hC : (0 : ℝ) ≤ 6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ) := by positivity
  have hdom : Integrable (fun t : ℝ =>
      (N : ℝ) ^ m * (6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
        Real.exp (-(c / 2 * |t|))) :=
    (integrable_exp_neg_abs_mul (c / 2) (by linarith)).const_mul _
  refine Integrable.mono' hdom (by fun_prop) (Filter.Eventually.of_forall (fun t => ?_))
  have hlog0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
    apply Real.log_nonneg
    have hm2 : (2 * 2 : ℝ) ≤ (N : ℝ) * (|t| + 2) :=
      mul_le_mul hNr (by linarith [abs_nonneg t] : (2 : ℝ) ≤ |t| + 2)
        (by norm_num) (by linarith : (0 : ℝ) ≤ (N : ℝ))
    linarith
  have h5 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ m := pow_nonneg hlog0 m
  have hnonneg : (0 : ℝ) ≤ (3 + |t|) * Real.exp (-(c * |t|)) *
      Real.log ((N : ℝ) * (|t| + 2)) ^ m :=
    mul_nonneg (mul_nonneg (by linarith [abs_nonneg t]) (Real.exp_pos _).le) h5
  rw [Real.norm_of_nonneg hnonneg]
  have hx : (0 : ℝ) < (N : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have h1 : Real.log ((N : ℝ) * (|t| + 2)) ≤ (N : ℝ) * (|t| + 2) := by
    have := Real.log_le_sub_one_of_pos hx
    linarith
  have h2 : Real.log ((N : ℝ) * (|t| + 2)) ^ m ≤ ((N : ℝ) * (|t| + 2)) ^ m :=
    pow_le_pow_left₀ hlog0 h1 m
  have h3 : ((N : ℝ) * (|t| + 2)) ^ m ≤ N ^ m * (|t| + 3) ^ m := by
    have hle : (N : ℝ) * (|t| + 2) ≤ N * (|t| + 3) := by nlinarith [abs_nonneg t]
    calc ((N : ℝ) * (|t| + 2)) ^ m ≤ (N * (|t| + 3)) ^ m := pow_le_pow_left₀ hx.le hle m
      _ = N ^ m * (|t| + 3) ^ m := by rw [mul_pow]
  have hpoly := poly_pow_le_exp c hc (m + 1) |t| (abs_nonneg t)
  have hexp : Real.exp (c * |t| / 2) * Real.exp (-(c * |t|)) = Real.exp (-(c / 2 * |t|)) := by
    rw [← Real.exp_add, show c * |t| / 2 + -(c * |t|) = -(c / 2 * |t|) from by ring]
  have hmain : (3 + |t|) * Real.exp (-(c * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ m ≤
      (3 + |t|) * Real.exp (-(c * |t|)) * (N ^ m * (|t| + 3) ^ m) := by
    exact mul_le_mul_of_nonneg_left (h2.trans h3)
      (mul_nonneg (by linarith [abs_nonneg t]) (Real.exp_pos _).le)
  have hstep : (3 + |t|) * Real.exp (-(c * |t|)) * (N ^ m * (|t| + 3) ^ m) ≤
      N ^ m * (6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
        Real.exp (-(c / 2 * |t|)) := by
    have hq : (3 + |t|) * (|t| + 3) ^ m = (|t| + 3) ^ (m + 1) := by
      rw [pow_succ]
      ring
    calc (3 + |t|) * Real.exp (-(c * |t|)) * (N ^ m * (|t| + 3) ^ m)
        = N ^ m * ((|t| + 3) ^ (m + 1) * Real.exp (-(c * |t|))) := by rw [← hq]; ring
      _ ≤ N ^ m * ((6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
            Real.exp (c * |t| / 2) * Real.exp (-(c * |t|))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = N ^ m * (6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
            Real.exp (-(c / 2 * |t|)) := by
          rw [show (6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
              Real.exp (c * |t| / 2) * Real.exp (-(c * |t|)) =
              (6 ^ (m + 1) + (4 / c) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
                (Real.exp (c * |t| / 2) * Real.exp (-(c * |t|))) from by ring, hexp]
          ring
  exact hmain.trans hstep

/-- The power factor of the kernel, with the absolute value of the argument. -/
private theorem cpow_line_bound_abs442 (N : ℕ) (hN : 2 ≤ N) (z : ℂ)
    (hzre : z.re = 1 / (N : ℝ)) (t : ℝ) :
    ‖z ^ (-(mellinLine1622 N t))‖ ≤
      Real.exp 1 * Real.sqrt N * Real.exp (|t| * |z.arg|) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  set σ : ℝ := 1 / 2 + 1 / Real.log N with hσr
  have hσpos : 0 < σ := by
    have : 0 < 1 / Real.log N := div_pos one_pos hlog
    rw [hσr]; linarith
  have hre : (-(mellinLine1622 N t)).re = -σ := by
    simp only [mellinLine1622, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, hσr]
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
      rw [hσr, Real.rpow_add hNpos]
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

/-- The absolute kernel weight, logarithmic factor included, is continuous in the
line variable. -/
private theorem kernel_continuous_line442 (N : ℕ) (hN : 1 ≤ N) (z : ℂ)
    (hzre : z.re = 1 / (N : ℝ)) :
    Continuous (fun t : ℝ =>
      ‖z ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hNr0 : (0 : ℝ) < (N : ℝ) := by
    have h : (0 : ℕ) < N := by omega
    exact_mod_cast h
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hz0 : z ≠ 0 := by
    intro h0
    have hz : z.re = 0 := by rw [h0]; simp
    rw [hzre] at hz
    have h1 : (0 : ℝ) < 1 / (N : ℝ) := div_pos one_pos hNr0
    linarith
  have hmc : Continuous (fun t : ℝ => mellinLine1622 N t) := by
    simp only [mellinLine1622]
    fun_prop
  have hmre : ∀ t : ℝ, (mellinLine1622 N t).re = 1 / 2 + 1 / Real.log N := by
    intro t
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hGamma : Continuous (fun t : ℝ => Complex.Gamma (mellinLine1622 N t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : ∀ m : ℕ, mellinLine1622 N t ≠ -m := by
      intro m hm
      have hrev := congr_arg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re, hmre] at hrev
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hinvpos : 0 ≤ 1 / Real.log N := one_div_nonneg.mpr hlog0
      linarith
    exact ((Complex.differentiableAt_Gamma _ hne).continuousAt).comp hmc.continuousAt
  have hpow : Continuous (fun t : ℝ => z ^ (-(mellinLine1622 N t))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hinner : Continuous (fun t : ℝ => -(mellinLine1622 N t)) := hmc.neg
    exact (continuousAt_const_cpow hz0).comp hinner.continuousAt
  apply Continuous.mul
  · exact (hpow.mul hGamma).norm
  · have h1 : Continuous (fun t : ℝ => (N : ℝ) * (|t| + 2)) := by fun_prop
    refine (h1.log ?_).pow 3
    intro t
    have ht : (0 : ℝ) ≤ |t| := abs_nonneg t
    have := hNr0
    positivity

/-- LEAF. Step 1 of 3 of the outer kernel mass integrability: the line integrand of
the absolute kernel mass is dominated by one integrable function of the line
variable, uniformly over the whole outer frequency interval. -/
theorem outer_kernel_weight_dominated442 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) :
    ∃ g : ℝ → ℝ, (∀ t : ℝ, 0 ≤ g t) ∧ Integrable g ∧
      ∀ α : ℝ, α ∈ Set.uIcc (4 / (N : ℝ)) (1 / R) → ∀ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤ g t := by
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hRp : (0 : ℝ) < R := by linarith
  have h1N : (0 : ℝ) < 1 / (N : ℝ) := div_pos one_pos hNr
  have h1R : (0 : ℝ) < 1 / R := div_pos one_pos hRp
  set K : ℝ := 8 * Real.pi + 2 * Real.pi * ((N : ℝ) / R) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have h1 : 0 ≤ 2 * Real.pi * ((N : ℝ) / R) :=
      mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (le_of_lt (div_pos hNr hRp))
    linarith [Real.pi_pos]
  set d : ℝ := 1 / (1 + K) with hd
  have hdpos : 0 < d := by
    rw [hd]
    exact div_pos one_pos (by linarith)
  refine ⟨fun t : ℝ => (Real.exp 1 * Real.sqrt (N : ℝ) * Real.sqrt (2 * Real.pi)) *
      ((3 + |t|) * Real.exp (-(d * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3),
    ?_, ?_, ?_⟩
  · intro t
    have h1 : (0 : ℝ) ≤ 3 + |t| := by linarith [abs_nonneg t]
    have hx : (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by
      have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      nlinarith [abs_nonneg t]
    have h2 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 :=
      pow_nonneg (Real.log_nonneg hx) 3
    have h3 : (0 : ℝ) ≤ Real.exp (-(d * |t|)) := (Real.exp_pos _).le
    have h4 : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt (N : ℝ) * Real.sqrt (2 * Real.pi) :=
      mul_nonneg (mul_nonneg (Real.exp_pos 1).le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    exact mul_nonneg h4 (mul_nonneg (mul_nonneg h1 h3) h2)
  · have h := (integrable_weight_log N hN2 d hdpos 3).const_mul
      (Real.exp 1 * Real.sqrt (N : ℝ) * Real.sqrt (2 * Real.pi))
    exact h
  · intro α hα t
    have hmem := Set.mem_uIcc.mp hα
    have h4N : (0 : ℝ) < 4 / (N : ℝ) := div_pos (by norm_num) hNr
    have hαlo : min (4 / (N : ℝ)) (1 / R) ≤ α := by
      rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact le_trans (min_le_left (4 / (N : ℝ)) (1 / R)) h1
      · exact le_trans (min_le_right (4 / (N : ℝ)) (1 / R)) h1
    have hαhi : α ≤ max (4 / (N : ℝ)) (1 / R) := by
      rcases hmem with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact le_trans h2 (le_max_right (4 / (N : ℝ)) (1 / R))
      · exact le_trans h2 (le_max_left (4 / (N : ℝ)) (1 / R))
    have hαpos : 0 < α := lt_of_lt_of_le (lt_min h4N h1R) hαlo
    set zb : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzb
    have hzre : zb.re = 1 / (N : ℝ) := by
      rw [hzb]
      simp
    have hzim : zb.im = 2 * Real.pi * α := by
      rw [hzb]
      simp
    have hzim0 : 0 ≤ zb.im := by
      rw [hzim]
      exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (le_of_lt hαpos)
    have hz0 : zb ≠ 0 := by
      intro h0
      have hz : zb.re = 0 := by rw [h0]; simp
      rw [hzre] at hz
      linarith
    have hsum : α ≤ 4 / (N : ℝ) + 1 / R :=
      le_trans hαhi (max_le (le_add_of_nonneg_right (le_of_lt h1R))
        (le_add_of_nonneg_left (le_of_lt h4N)))
    have hratio : 2 * Real.pi * α ≤ K / (N : ℝ) := by
      rw [le_div_iff₀ hNr]
      have hcoef : (0 : ℝ) ≤ 2 * Real.pi * (N : ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (le_of_lt hNr)
      have h1 : 2 * Real.pi * α * (N : ℝ) ≤ 2 * Real.pi * (N : ℝ) * (4 / (N : ℝ) + 1 / R) := by
        calc 2 * Real.pi * α * (N : ℝ) = 2 * Real.pi * (N : ℝ) * α := by ring
          _ ≤ 2 * Real.pi * (N : ℝ) * (4 / (N : ℝ) + 1 / R) :=
              mul_le_mul_of_nonneg_left hsum hcoef
      have h2 : 2 * Real.pi * (N : ℝ) * (4 / (N : ℝ) + 1 / R) = K := by
        rw [hK]
        field_simp
        ring
      linarith [h1, h2]
    have harg0 : 0 ≤ zb.arg := Complex.arg_nonneg_iff.mpr hzim0
    have hnorm : ‖zb‖ ≤ 1 / (N : ℝ) + 2 * Real.pi * α := by
      have hb := Complex.norm_le_abs_re_add_abs_im zb
      rw [hzre, hzim] at hb
      rw [abs_of_pos h1N, abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        Real.pi_pos.le) (le_of_lt hαpos))] at hb
      exact hb
    have hden : ‖zb‖ ≤ (1 + K) / (N : ℝ) := by
      have he : 1 / (N : ℝ) + K / (N : ℝ) = (1 + K) / (N : ℝ) := by ring
      linarith [hnorm, hratio, he]
    have hnormpos : 0 < ‖zb‖ := norm_pos_iff.mpr hz0
    have hinv : ((1 + K) / (N : ℝ))⁻¹ ≤ ‖zb‖⁻¹ := inv_anti₀ hnormpos hden
    have hcosge : d ≤ zb.re / ‖zb‖ := by
      rw [hzre]
      calc d = (1 / (N : ℝ)) * ((1 + K) / (N : ℝ))⁻¹ := by
            rw [hd, inv_div]
            field_simp
        _ ≤ (1 / (N : ℝ)) * ‖zb‖⁻¹ := mul_le_mul_of_nonneg_left hinv (le_of_lt h1N)
        _ = (1 / (N : ℝ)) / ‖zb‖ := by rw [div_eq_mul_inv]; ring
    have hcos : Real.cos zb.arg = zb.re / ‖zb‖ := Complex.cos_arg hz0
    have hpi2 : zb.arg ≤ Real.pi / 2 :=
      Complex.arg_le_pi_div_two_iff.mpr (Or.inl (by rw [hzre]; exact (le_of_lt h1N)))
    have hlt : zb.arg < Real.pi / 2 := by
      rcases lt_or_eq_of_le hpi2 with h | h
      · exact h
      · exfalso
        have hc0 : Real.cos zb.arg = 0 := by rw [h, Real.cos_pi_div_two]
        have hzero : zb.re / ‖zb‖ = 0 := by rw [← hcos]; exact hc0
        linarith [hcosge, hzero]
    have hypos : 0 < Real.pi / 2 - zb.arg := by linarith
    have hsin : Real.sin (Real.pi / 2 - zb.arg) = zb.re / ‖zb‖ := by
      rw [Real.sin_pi_div_two_sub]
      exact hcos
    have hargle : zb.arg ≤ Real.pi / 2 - d := by
      have h1 : Real.sin (Real.pi / 2 - zb.arg) < Real.pi / 2 - zb.arg := Real.sin_lt hypos
      have h2 : d ≤ Real.sin (Real.pi / 2 - zb.arg) := by rw [hsin]; exact hcosge
      linarith
    have hb1 : ‖zb ^ (-(mellinLine1622 N t))‖ ≤
        Real.exp 1 * Real.sqrt (N : ℝ) * Real.exp (|t| * (Real.pi / 2 - d)) := by
      have hb := cpow_line_bound_abs442 N hN2 zb hzre t
      rw [abs_of_nonneg harg0] at hb
      refine hb.trans (mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (Real.exp_pos 1).le (Real.sqrt_nonneg _)))
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hargle (abs_nonneg t))
    have hb2 : ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
        Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2)) :=
      gamma_line_decay442 N hN t
    have hx1 : (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by
      have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      nlinarith [abs_nonneg t]
    have hL3 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 :=
      pow_nonneg (Real.log_nonneg hx1) 3
    have hp1 : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt (N : ℝ) *
        Real.exp (|t| * (Real.pi / 2 - d)) :=
      mul_nonneg (mul_nonneg (Real.exp_pos 1).le (Real.sqrt_nonneg _)) (Real.exp_pos _).le
    have hp2 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) * (3 + |t|) *
        Real.exp (-(Real.pi * |t| / 2)) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith [abs_nonneg t]))
        (Real.exp_pos _).le
    have hprod : ‖zb ^ (-(mellinLine1622 N t))‖ * ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
        (Real.exp 1 * Real.sqrt (N : ℝ) * Real.exp (|t| * (Real.pi / 2 - d))) *
          (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) :=
      mul_le_mul hb1 hb2 (norm_nonneg _) hp1
    have hstep : ‖zb ^ (-(mellinLine1622 N t))‖ * ‖Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
        (Real.exp 1 * Real.sqrt (N : ℝ) * Real.exp (|t| * (Real.pi / 2 - d))) *
          (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
            Real.log ((N : ℝ) * (|t| + 2)) ^ 3 :=
      mul_le_mul_of_nonneg_right hprod hL3
    have hexp : Real.exp (|t| * (Real.pi / 2 - d)) * Real.exp (-(Real.pi * |t| / 2)) =
        Real.exp (-(d * |t|)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hshape : (Real.exp 1 * Real.sqrt (N : ℝ) * Real.exp (|t| * (Real.pi / 2 - d))) *
          (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
            Real.log ((N : ℝ) * (|t| + 2)) ^ 3 =
        (Real.exp 1 * Real.sqrt (N : ℝ) * Real.sqrt (2 * Real.pi)) *
          ((3 + |t|) * Real.exp (-(d * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
      rw [show (Real.exp 1 * Real.sqrt (N : ℝ) * Real.exp (|t| * (Real.pi / 2 - d))) *
            (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3 =
          (Real.exp 1 * Real.sqrt (N : ℝ) * Real.sqrt (2 * Real.pi)) *
            ((Real.exp (|t| * (Real.pi / 2 - d)) * Real.exp (-(Real.pi * |t| / 2))) *
              ((3 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) from by ring,
        hexp]
      ring
    have hfin : ‖zb ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
        (Real.exp 1 * Real.sqrt (N : ℝ) * Real.sqrt (2 * Real.pi)) *
          ((3 + |t|) * Real.exp (-(d * |t|)) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
      rw [norm_mul]
      exact hstep.trans (le_of_eq hshape)
    simpa only [hzb] using hfin

/-- LEAF. Step 2 of 3: at a fixed line point the absolute kernel weight, logarithmic
factor included, is continuous in the frequency. -/
theorem outer_kernel_weight_continuous_alpha442 (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    Continuous (fun α : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hNr0 : (0 : ℝ) < (N : ℝ) := by
    have h : (0 : ℕ) < N := by omega
    exact_mod_cast h
  have hcont : Continuous (fun α : ℝ =>
      ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) := by fun_prop
  have hcpow : Continuous (fun α : ℝ =>
      (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine1622 N t))) := by
    rw [continuous_iff_continuousAt]
    intro α
    have hslit : (((1 / (N : ℝ) : ℝ) : ℂ) +
        ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ∈ Complex.slitPlane :=
      Or.inl (by
        show 0 < (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I).re
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        exact div_pos one_pos hNr0)
    have hcst : Tendsto (fun _ : ℝ => (-(mellinLine1622 N t))) (𝓝 α) (𝓝 (-(mellinLine1622 N t))) :=
      tendsto_const_nhds
    exact hcont.continuousAt.cpow hcst hslit
  have h2 : Continuous (fun α : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t))‖ * ‖Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
    (hcpow.norm.mul continuous_const).mul continuous_const
  simpa only [norm_mul] using h2

/-- LEAF. Step 3 of 3: at a fixed frequency the absolute kernel weight is continuous
along the line. -/
theorem outer_kernel_weight_continuous_line442 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    Continuous (fun t : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hNr0 : (0 : ℝ) < (N : ℝ) := by
    have h : (0 : ℕ) < N := by omega
    exact_mod_cast h
  refine kernel_continuous_line442 N hN _ ?_
  rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- Assembly from the three leaves. Step 1 gives the dominating integrable function,
step 3 makes each frequency slice measurable, step 2 gives continuity in the frequency,
so the mass is continuous on the compact outer interval; its square is then interval
integrable there. -/
theorem outer_kernel_mass_integrable442_split (N : ℕ) (hN : 3 ≤ N) (R : ℝ)
    (hR : 1 ≤ R) (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) :
    IntervalIntegrable (fun α : ℝ =>
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) volume
      (4 / (N : ℝ)) (1 / R) := by
  have hN1 : 1 ≤ N := by omega
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  obtain ⟨g, hg0, hgint, hgb⟩ := outer_kernel_weight_dominated442 N hN R hR hR2
  have hmeas : ∀ α ∈ Set.uIcc (4 / (N : ℝ)) (1 / R),
      AEStronglyMeasurable (fun t : ℝ => ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) volume :=
    fun α _ => (outer_kernel_weight_continuous_line442 N hN1 α).aestronglyMeasurable
  have hbound : ∀ α ∈ Set.uIcc (4 / (N : ℝ)) (1 / R),
      ∀ᵐ t ∂volume, ‖‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3‖ ≤ g t := by
    intro α hα
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h0 : 0 ≤ ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
      have h1 : (1 : ℝ) < (N : ℝ) * (|t| + 2) := by
        nlinarith [abs_nonneg t]
      have h2 : 0 < Real.log ((N : ℝ) * (|t| + 2)) := Real.log_pos h1
      exact mul_nonneg (norm_nonneg _) (pow_pos h2 3).le
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hgb α hα t
  have hcont : ContinuousOn (fun α : ℝ =>
      ∫ t : ℝ, ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) (Set.uIcc (4 / (N : ℝ)) (1 / R)) :=
    continuousOn_of_dominated hmeas hbound hgint
      (Filter.Eventually.of_forall
        (fun t => (outer_kernel_weight_continuous_alpha442 N hN1 t).continuousOn))
  exact (hcont.pow 2).intervalIntegrable


end LeanLab.Linnik1951
