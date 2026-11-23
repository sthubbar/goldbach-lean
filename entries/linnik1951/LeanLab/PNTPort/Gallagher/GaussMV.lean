module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# A Gaussian mean value theorem for exponential polynomials with real frequencies

Lab proof, unit U-5854, CLOUD 20261020T0014Z-cloud30. AI wrote this file. Known mathematics,
the almost orthogonality step of Selberg's 1943 mean square of primes in short intervals, in
the Gaussian form; no cited input.

For complex `a j`, real frequencies `γ j`, `j` in a finite set, and any centre `U`,

  `∫_ℝ ‖∑_j a j e^{i γ_j u}‖² e^{-(u - U)²/2} du ≤ √(2π) ∑_j ‖a j‖² ∑_k e^{-(γ_j - γ_k)²/2}`.

With `γ` the ordinates of the zeta zeros and `u = log x`, the inner sum is `≪ log(|γ_j| + 2)`
by the lab's zero window count, which is how the zero sum in the explicit formula has mean square
`≪ ∑ |a_γ|² log |γ|` instead of `(∑ |a_γ|)²`; see IDEAS I-5100.

* `integral_gauss_char`: `∫ e^{iku} e^{-(u - U)²/2} du = (π/(1/2))^{1/2} e^{ikU - k²/2}`.
* `gauss_mean_value`: the inequality above.
-/

@[expose] public section


namespace LeanLab.PNTPort.Gallagher

open Complex MeasureTheory Finset

/-- The Gaussian weight centred at `U`. -/
noncomputable def gw (U u : ℝ) : ℝ := Real.exp (-(u - U) ^ 2 / 2)

lemma gw_eq (U k u : ℝ) : cexp (k * u * I) * (gw U u : ℂ)
    = cexp ((-1 / 2 : ℂ) * (u : ℂ) ^ 2 + (U + k * I) * u + (-(U : ℂ) ^ 2 / 2)) := by
  unfold gw
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma integrable_gauss_char (U k : ℝ) :
    Integrable (fun u : ℝ => cexp (k * u * I) * (gw U u : ℂ)) := by
  simp_rw [gw_eq]
  exact integrable_cexp_quadratic' (by norm_num) _ _

/-- `∫ e^{iku} e^{-(u - U)²/2} du = (π/(1/2))^{1/2} e^{ikU - k²/2}`. -/
theorem integral_gauss_char (U k : ℝ) :
    ∫ u : ℝ, cexp (k * u * I) * (gw U u : ℂ)
      = ((Real.pi : ℂ) / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ) * cexp (k * U * I - (k : ℂ) ^ 2 / 2) := by
  simp_rw [gw_eq]
  rw [integral_cexp_quadratic (by norm_num)]
  rw [show -(-1 / 2 : ℂ) = 1 / 2 by ring]
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

lemma norm_const : ‖((Real.pi : ℂ) / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ)‖ = (2 * Real.pi) ^ (1 / 2 : ℝ) := by
  have h : ((Real.pi : ℂ) / (1 / 2 : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  norm_num

/-- **Gaussian mean value theorem.** -/
theorem gauss_mean_value {ι : Type*} (s : Finset ι) (a : ι → ℂ) (γ : ι → ℝ) (U : ℝ) :
    ∫ u : ℝ, ‖∑ j ∈ s, a j * cexp (γ j * u * I)‖ ^ 2 * gw U u
      ≤ (2 * Real.pi) ^ (1 / 2 : ℝ) *
          ∑ j ∈ s, ‖a j‖ ^ 2 * ∑ k ∈ s, Real.exp (-(γ j - γ k) ^ 2 / 2) := by
  set κ : ℂ := ((Real.pi : ℂ) / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ)
  -- expand the square and integrate term by term
  have hterm : ∀ j k : ι, ∫ u : ℝ, a j * (starRingEnd ℂ) (a k) *
      (cexp (((γ j - γ k : ℝ) : ℂ) * u * I) * (gw U u : ℂ))
      = a j * (starRingEnd ℂ) (a k) * (κ * cexp (((γ j - γ k : ℝ) : ℂ) * U * I
          - (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2)) := by
    intro j k
    rw [integral_const_mul, integral_gauss_char]
  have hint : ∀ j k : ι, Integrable (fun u : ℝ => a j * (starRingEnd ℂ) (a k) *
      (cexp (((γ j - γ k : ℝ) : ℂ) * u * I) * (gw U u : ℂ))) :=
    fun j k => (integrable_gauss_char U (γ j - γ k)).const_mul _
  have hexp : ∀ u : ℝ, ((‖∑ j ∈ s, a j * cexp (γ j * u * I)‖ ^ 2 * gw U u : ℝ) : ℂ)
      = ∑ j ∈ s, ∑ k ∈ s, a j * (starRingEnd ℂ) (a k) *
          (cexp (((γ j - γ k : ℝ) : ℂ) * u * I) * (gw U u : ℂ)) := by
    intro u
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum,
      sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    have : (starRingEnd ℂ) ((γ k : ℂ) * u * I) = -((γ k : ℂ) * u * I) := by
      simp [Complex.conj_ofReal]
    rw [this]
    have h2 : cexp (((γ j - γ k : ℝ) : ℂ) * u * I)
        = cexp ((γ j : ℂ) * u * I) * cexp (-((γ k : ℂ) * u * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h2]; ring
  -- the real integral is the real part of the complex one
  have hC : ((∫ u : ℝ, ‖∑ j ∈ s, a j * cexp (γ j * u * I)‖ ^ 2 * gw U u : ℝ) : ℂ)
      = ∑ j ∈ s, ∑ k ∈ s, a j * (starRingEnd ℂ) (a k) * (κ * cexp (((γ j - γ k : ℝ) : ℂ) * U * I
          - (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2)) := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => hint j k]
    refine sum_congr rfl fun j _ => ?_
    rw [integral_finset_sum _ fun k _ => hint j k]
    exact sum_congr rfl fun k _ => hterm j k
  have hle : (∫ u : ℝ, ‖∑ j ∈ s, a j * cexp (γ j * u * I)‖ ^ 2 * gw U u)
      ≤ ‖((∫ u : ℝ, ‖∑ j ∈ s, a j * cexp (γ j * u * I)‖ ^ 2 * gw U u : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  refine hle.trans ?_
  rw [hC]
  -- each term has norm `√(2π) ‖a j‖ ‖a k‖ e^{-(γ_j - γ_k)²/2}`
  have hnorm : ∀ j k : ι, ‖a j * (starRingEnd ℂ) (a k) * (κ * cexp (((γ j - γ k : ℝ) : ℂ) * U * I
      - (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2))‖
      = (2 * Real.pi) ^ (1 / 2 : ℝ) * (‖a j‖ * ‖a k‖ * Real.exp (-(γ j - γ k) ^ 2 / 2)) := by
    intro j k
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, norm_const, Complex.norm_exp]
    have : (((γ j - γ k : ℝ) : ℂ) * U * I - (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2).re
        = -(γ j - γ k) ^ 2 / 2 := by
      rw [show (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2 = (((γ j - γ k) ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.sub_re, Complex.ofReal_re]
      simp
      ring
    rw [this]; ring
  calc ‖∑ j ∈ s, ∑ k ∈ s, a j * (starRingEnd ℂ) (a k) * (κ * cexp (((γ j - γ k : ℝ) : ℂ) * U * I
          - (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2))‖
      ≤ ∑ j ∈ s, ∑ k ∈ s, (2 * Real.pi) ^ (1 / 2 : ℝ) *
          (‖a j‖ * ‖a k‖ * Real.exp (-(γ j - γ k) ^ 2 / 2)) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => hnorm j k))
    _ = (2 * Real.pi) ^ (1 / 2 : ℝ) *
          ∑ j ∈ s, ∑ k ∈ s, ‖a j‖ * ‖a k‖ * Real.exp (-(γ j - γ k) ^ 2 / 2) := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by rw [mul_sum]
    _ ≤ (2 * Real.pi) ^ (1 / 2 : ℝ) *
          ∑ j ∈ s, ‖a j‖ ^ 2 * ∑ k ∈ s, Real.exp (-(γ j - γ k) ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        -- `xy ≤ (x² + y²)/2` and the symmetry of the kernel in `j, k`
        have hsym : ∑ j ∈ s, ∑ k ∈ s, ‖a k‖ ^ 2 * Real.exp (-(γ j - γ k) ^ 2 / 2)
            = ∑ j ∈ s, ∑ k ∈ s, ‖a j‖ ^ 2 * Real.exp (-(γ j - γ k) ^ 2 / 2) := by
          rw [sum_comm]
          refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
          rw [show (γ k - γ j) ^ 2 = (γ j - γ k) ^ 2 by ring]
        have hpt : ∀ j k : ι, ‖a j‖ * ‖a k‖ * Real.exp (-(γ j - γ k) ^ 2 / 2)
            ≤ (‖a j‖ ^ 2 * Real.exp (-(γ j - γ k) ^ 2 / 2)
              + ‖a k‖ ^ 2 * Real.exp (-(γ j - γ k) ^ 2 / 2)) / 2 := by
          intro j k
          have he := Real.exp_pos (-(γ j - γ k) ^ 2 / 2)
          nlinarith [sq_nonneg (‖a j‖ - ‖a k‖)]
        calc ∑ j ∈ s, ∑ k ∈ s, ‖a j‖ * ‖a k‖ * Real.exp (-(γ j - γ k) ^ 2 / 2)
            ≤ ∑ j ∈ s, ∑ k ∈ s, (‖a j‖ ^ 2 * Real.exp (-(γ j - γ k) ^ 2 / 2)
                + ‖a k‖ ^ 2 * Real.exp (-(γ j - γ k) ^ 2 / 2)) / 2 :=
              sum_le_sum fun j _ => sum_le_sum fun k _ => hpt j k
          _ = (∑ j ∈ s, ∑ k ∈ s, ‖a j‖ ^ 2 * Real.exp (-(γ j - γ k) ^ 2 / 2)
                + ∑ j ∈ s, ∑ k ∈ s, ‖a k‖ ^ 2 * Real.exp (-(γ j - γ k) ^ 2 / 2)) / 2 := by
              rw [← sum_add_distrib, sum_div]
              exact sum_congr rfl fun j _ => by rw [← sum_add_distrib, sum_div]
          _ = ∑ j ∈ s, ‖a j‖ ^ 2 * ∑ k ∈ s, Real.exp (-(γ j - γ k) ^ 2 / 2) := by
              rw [hsym]; ring_nf
              exact sum_congr rfl fun j _ => by rw [mul_sum]

end LeanLab.PNTPort.Gallagher

