module

public import LeanLab.Linnik1951.Repair493KernelData
public import LeanLab.PNTPort.ZetaZeros.GammaBounds

/-!
P0093 page 157 Gamma decay for the Mellin kernel.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- P0093 page 157 Gamma asymptotic used before equation 4.4.
The existing PNTPort strip bound gives exponential decay in the
absolute imaginary part by conjugation. -/
theorem gamma_absolute_decay442 (s : ℂ) (hlo : 1 / 2 ≤ s.re) (hhi : s.re ≤ 3 / 2) :
    ‖Complex.Gamma s‖ ≤ Real.sqrt (2 * Real.pi) * ‖s + 1‖ *
      Real.exp (-(Real.pi * |s.im| / 2)) := by
  by_cases hs : 0 ≤ s.im
  · simpa only [abs_of_nonneg hs] using
      LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL hlo hhi
  · have hh := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL
      (s := star s) (by simpa using hlo) (by simpa using hhi)
    have hn : ‖star s + 1‖ = ‖s + 1‖ := by
      simpa using norm_star (s + 1)
    have hgamma : ‖Complex.Gamma (star s)‖ = ‖Complex.Gamma s‖ := by
      simp only [Complex.star_def, Complex.Gamma_conj, Complex.norm_conj]
    have him : (star s).im = -s.im := by simp
    rw [hgamma, hn, him] at hh
    simpa only [abs_of_neg (lt_of_not_ge hs)] using hh

/-- P0093 page 157 shifted Mellin line. For N at least three the
Gamma factor is bounded by square root of two pi times three plus
absolute t times exp of negative pi absolute t over two. -/
theorem gamma_mellin_line442 (N : ℕ) (hN : 3 ≤ N) (t : ℝ) :
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
  have hg := gamma_absolute_decay442 (mellinLine1622 N t)
    (by rw [hre]; exact le_add_of_nonneg_right (by positivity))
    (by rw [hre]; linarith)
  have hn : ‖mellinLine1622 N t + 1‖ ≤ 3 + |t| := by
    have hh := Complex.norm_le_abs_re_add_abs_im (mellinLine1622 N t + 1)
    have hr : (mellinLine1622 N t + 1).re = 1 / 2 + 1 / Real.log N + 1 := by simp [hre]
    have hi : (mellinLine1622 N t + 1).im = t := by simp [him]
    rw [hr, hi, abs_of_pos (by positivity : 0 < 1 / 2 + 1 / Real.log N + 1)] at hh
    linarith
  rw [him] at hg
  exact hg.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hn (by positivity)) (Real.exp_pos _).le)

end LeanLab.Linnik1951
