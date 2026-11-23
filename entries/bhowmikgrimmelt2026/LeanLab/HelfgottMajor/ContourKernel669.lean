module

public import LeanLab.HelfgottMajor.Decomp511b
public import LeanLab.HelfgottMajor.BookL1523
public import Mathlib

/-!
P0014 pages 17 to 25, displays 3.30, 3.34, 3.56 and 3.58 to 3.64.
The main path is the limacon of Pascal of display 3.30.
Source: https://arxiv.org/abs/1305.2897
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Decomp511a
open Real

/-- The exact main coefficient of Theorem 3.1, page 10, display 3.2. -/
noncomputable def mainCoefficient (σ t d : ℝ) : ℝ :=
  min 2 (3.3 * sqrt t / (2 * π * |d|)) *
    (1 + max ((7.83 : ℝ) ^ (1 - σ)) ((1.63 : ℝ) ^ (σ - 1))) *
    ((3 / 2 : ℝ) / min (t / (2 * π * |d|)) (sqrt t)) ^ (1 - σ)

/-- The first error coefficient of Theorem 3.1, page 10, display 3.2. -/
noncomputable def firstCoefficient (σ t : ℝ) : ℝ :=
  (1 + (1 + sqrt 2) / t) * t ^ (σ / 2)

end LeanLab.HelfgottMajor.Decomp511a

namespace LeanLab.HelfgottMajor.Decomp639Contour
open Real MeasureTheory Set SplitGaussian123 Decomp511a Filter
open scoped Topology

/-- The direction parameter Upsilon of P0014 page 16, display 3.25. -/
noncomputable def upsilon (ρ : ℝ) : ℝ :=
  tan (arctan (2 * BookE.ups ρ * (BookE.ups ρ + sqrt (1 + ρ ^ 2)) / ρ) / 2)

/-- The first limacon coefficient of P0014 page 18, display 3.34. -/
noncomputable def c0 (ρ : ℝ) : ℝ :=
  sqrt (1 / 2 + 1 / (2 * BookE.ups ρ)) * upsilon ρ +
    sqrt (1 / 2 - 1 / (2 * BookE.ups ρ))

/-- The second limacon coefficient of P0014 page 18, display 3.34. -/
noncomputable def c1 (ρ : ℝ) : ℝ :=
  sqrt ((1 + 1 / BookE.ups ρ) / (BookE.ups ρ ^ 2 - BookE.ups ρ)) * upsilon ρ

/-- The positive frequency scale ell of P0014 page 13. -/
noncomputable def ell (δ : ℝ) : ℝ := 2 * π * |δ|

/-- The shape parameter rho of P0014 page 14, display 3.15. -/
noncomputable def rho (δ τ : ℝ) : ℝ := |τ| / (π * δ) ^ 2

/-- The initial radius of P0014 page 24, display 3.58. -/
noncomputable def initialRadius (δ τ : ℝ) : ℝ :=
  ell δ / c1 (rho δ τ) * (c0 (rho δ τ) - 1 / sqrt 2)

/-- The real endpoint of P0014 page 25, display 3.64. -/
noncomputable def realEndpoint (δ τ : ℝ) : ℝ :=
  ell δ * (c0 (rho δ τ) / c1 (rho δ τ))

/-- The initial unit direction on page 24 and its conjugate for negative height. -/
noncomputable def rayDirection (τ : ℝ) : ℂ :=
  (1 + (if 0 ≤ τ then (1 : ℂ) else -1) * Complex.I) / (sqrt 2 : ℝ)

/-- The limacon of display 3.30 with reflection for negative height. -/
noncomputable def saddlePath (δ τ r : ℝ) : ℂ :=
  let y := (-c1 (rho δ τ) * r / ell δ + c0 (rho δ τ)) * r
  (sqrt (r ^ 2 - y ^ 2) : ℂ) +
    (if 0 ≤ τ then (y : ℂ) else -y) * Complex.I

/-- The holomorphic twisted Mellin kernel of P0014 pages 18 and 24. -/
noncomputable def contourKernel (δ : ℝ) (s z : ℂ) : ℂ :=
  z ^ (s - 1) * Complex.exp (-z ^ 2 / 2 + 2 * π * Complex.I * δ * z)

/-- The parametrized C1 integral in P0014 page 24, display 3.59. -/
noncomputable def initialIntegral (δ : ℝ) (s : ℂ) : ℂ :=
  ∫ r : ℝ in Ioo 0 (initialRadius δ s.im),
    contourKernel δ s (r * rayDirection s.im) * rayDirection s.im

/-- The parametrized C2 integral in P0014 page 23, display 3.56. -/
noncomputable def saddleIntegral (δ : ℝ) (s : ℂ) : ℂ :=
  ∫ r : ℝ in (initialRadius δ s.im)..(realEndpoint δ s.im),
    contourKernel δ s (saddlePath δ s.im r) * deriv (saddlePath δ s.im) r

/-- Positive scale for the nonzero twist in P0014 page 13. -/
theorem ell_pos (δ : ℝ) (hδ : δ ≠ 0) : 0 < ell δ := by
  unfold ell
  positivity

/-- Positive shape parameter for the opposite sign case on P0014 page 14. -/
theorem rho_pos (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) : 0 < rho δ τ := by
  unfold rho
  exact div_pos hτ (sq_pos_of_ne_zero (mul_ne_zero pi_ne_zero hδ))

/-- Scale identity of P0014 page 14, display 3.15. -/
theorem ell_sq_mul_rho (δ τ : ℝ) (hδ : δ ≠ 0) :
    (ell δ) ^ 2 * rho δ τ = 4 * |τ| := by
  unfold ell rho
  simp only [mul_pow, sq_abs]
  field_simp
  <;> ring

/-- Square root scale conversion used after A.36 on P0014 page 25. -/
theorem ell_mul_sqrt_rho (δ τ : ℝ) (hδ : δ ≠ 0) :
    ell δ * sqrt (rho δ τ) = 2 * sqrt |τ| := by
  have he := ell_sq_mul_rho δ τ hδ
  have hp := (ell_pos δ hδ).le
  have hr : 0 ≤ rho δ τ := by unfold rho; positivity
  have hs := sq_sqrt hr
  have ht := sq_sqrt (abs_nonneg τ)
  have ha : 0 ≤ ell δ * sqrt (rho δ τ) := by positivity
  have hb : 0 ≤ 2 * sqrt |τ| := by positivity
  nlinarith [sq_nonneg (ell δ * sqrt (rho δ τ) - 2 * sqrt |τ|)]

/-- Holomorphy of the kernel on the right half plane used for the contour shift.
P0014 pages 18 and 24, displays 3.36 and 3.59. -/
theorem contourKernel_differentiable (δ : ℝ) (s : ℂ) :
    DifferentiableOn ℂ (contourKernel δ s) {z : ℂ | 0 < z.re} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold contourKernel
  apply DifferentiableAt.mul
  · exact (differentiableAt_id.cpow_const (Or.inl hz))
  · fun_prop

/-- The saddle scale v exceeds one at positive shape. P0014 page 16. -/
theorem ups_gt_one (ρ : ℝ) (hρ : 0 < ρ) : 1 < BookE.ups ρ := by
  have hj : 1 < sqrt (1 + ρ ^ 2) := lt_sqrt_of_sq_lt (by nlinarith)
  unfold BookE.ups
  exact lt_sqrt_of_sq_lt (by linarith)

/-- Positivity of upsilon pos for the contour in P0014 pages 16 to 18. -/
theorem upsilon_pos (ρ : ℝ) (hρ : 0 < ρ) : 0 < upsilon ρ := by
  have hv := ups_gt_one ρ hρ
  have ha : 0 < arctan (2 * BookE.ups ρ * (BookE.ups ρ + sqrt (1 + ρ ^ 2)) / ρ) := by
    apply arctan_pos.mpr
    exact div_pos (by positivity) hρ
  unfold upsilon
  apply tan_pos_of_pos_of_lt_pi_div_two (by linarith)
  have := arctan_lt_pi_div_two (2 * BookE.ups ρ * (BookE.ups ρ + sqrt (1 + ρ ^ 2)) / ρ)
  linarith [pi_pos]

/-- Positivity of c1 pos for the contour in P0014 pages 16 to 18. -/
theorem c1_pos (ρ : ℝ) (hρ : 0 < ρ) : 0 < c1 ρ := by
  have hv := ups_gt_one ρ hρ
  have hd : 0 < BookE.ups ρ ^ 2 - BookE.ups ρ := by nlinarith
  unfold c1
  exact mul_pos (sqrt_pos.mpr (div_pos (by positivity) hd)) (upsilon_pos ρ hρ)

/-- Positivity of c0 pos for the contour in P0014 pages 16 to 18. -/
theorem c0_pos (ρ : ℝ) (hρ : 0 < ρ) : 0 < c0 ρ := by
  have hv := ups_gt_one ρ hρ
  have hmain : 0 < sqrt (1 / 2 + 1 / (2 * BookE.ups ρ)) * upsilon ρ :=
    mul_pos (sqrt_pos.mpr (by positivity)) (upsilon_pos ρ hρ)
  unfold c0
  positivity

/-- P0014 pages 18 and 25, displays 3.36 and 3.64. delta minus one, s one half plus 100 i and x one. -/
theorem contourKernel_real (δ : ℝ) (s : ℂ) (x : ℝ) :
    contourKernel δ s x = (x : ℂ) ^ (s - 1) *
      ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x)) := by
  unfold contourKernel LeanLab.HelfgottArcs.e
  rw [Complex.exp_add]
  congr 2
  · norm_cast
  · congr 1
    push_cast
    ring

/-- P0014 page 24 before display 3.59 and reflection on page 23. tau 100 and minus 100. -/
theorem rayDirection_norm (τ : ℝ) : ‖rayDirection τ‖ = 1 := by
  unfold rayDirection
  split_ifs <;>
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sqrt_pos.mpr (by norm_num : (0:ℝ)<2))]
  all_goals norm_num [Complex.norm_def, Complex.normSq_apply]

/-- P0014 page 24 after display 3.60. tau 100, ell zero and r one. -/
theorem initial_phase_cost (τ L r : ℝ) (hτ : 0 ≤ τ)
    (hphase : L * r / sqrt 2 ≤ 0.30556 * τ) :
    exp (L * r / sqrt 2 - π / 4 * τ) ≤ exp (-0.4798 * τ) := by
  apply exp_le_exp.mpr
  have hp := mul_le_mul_of_nonneg_right pi_gt_d6.le hτ
  nlinarith

/-- P0014 page 25 after display 3.63, using 3.61. sigma one half, tau 100 and radius one. -/
theorem initial_radius_prefactor (σ τ r : ℝ) (hσ : 0 ≤ σ)
    (hτ : 0 < τ) (hr : 0 < r) (hrτ : r ≤ sqrt τ) :
    (r ^ (σ + 2) + (1 + sqrt 2) * r ^ σ) / τ ≤ firstCoefficient σ τ := by
  have hpow : r ^ σ ≤ τ ^ (σ / 2) := by
    have h := rpow_le_rpow hr.le hrτ hσ
    rw [sqrt_eq_rpow, ← rpow_mul hτ.le] at h
    simpa only [show (1 / 2 : ℝ) * σ = σ / 2 by ring] using h
  have hs : r ^ 2 ≤ τ := by nlinarith [sq_sqrt hτ.le]
  have hprod := mul_le_mul hpow hs (sq_nonneg r) (rpow_nonneg hτ.le (σ / 2))
  have hlin := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 1 + sqrt (2:ℝ) by positivity)
  calc
    _ = (r ^ σ * r ^ 2 + (1 + sqrt 2) * r ^ σ) / τ := by
      rw [rpow_add hr, rpow_two]
    _ ≤ (τ ^ (σ / 2) * τ + (1 + sqrt 2) * τ ^ (σ / 2)) / τ := by
      exact div_le_div_of_nonneg_right (add_le_add hprod hlin) hτ.le
    _ = _ := by
      unfold firstCoefficient
      field_simp
      <;> ring

/-- Derived small origin limit for the contour completion on pages 18 and 24. sigma one half and ell one. -/
theorem small_origin_limit (σ L : ℝ) (hσ : 0 < σ) :
    Filter.Tendsto (fun ε : ℝ => ε ^ σ * exp (L * ε)) (nhds 0) (nhds 0) := by
  have hp := (continuousAt_rpow_const 0 σ (Or.inr hσ.le)).tendsto
  have he : ContinuousAt (fun ε : ℝ => exp (L * ε)) 0 := by fun_prop
  simpa [zero_rpow hσ.ne'] using hp.mul he.tendsto

/-- P0014 pages 17, 24 and 25, displays 3.30, 3.58 and 3.64. delta minus one and tau 100 satisfy the hypotheses. -/
theorem realEndpoint_pos (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    0 < realEndpoint δ τ := by
  unfold realEndpoint
  exact mul_pos (ell_pos δ hδ) (div_pos (c0_pos _ (rho_pos δ τ hδ hτ))
    (c1_pos _ (rho_pos δ τ hδ hτ)))

/-- P0014 pages 17, 24 and 25, displays 3.30, 3.58 and 3.64. delta minus one and tau 100 satisfy the hypotheses. -/
theorem initialRadius_lt_realEndpoint (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    initialRadius δ τ < realEndpoint δ τ := by
  have hc := c1_pos _ (rho_pos δ τ hδ hτ)
  have hL := ell_pos δ hδ
  have hs : 0 < sqrt (2:ℝ) := by positivity
  have he : realEndpoint δ τ - initialRadius δ τ = ell δ / (c1 (rho δ τ) * sqrt 2) := by
    unfold realEndpoint initialRadius
    field_simp
    <;> ring
  have hp : 0 < ell δ / (c1 (rho δ τ) * sqrt 2) := by positivity
  linarith

/-- P0014 pages 17, 24 and 25, displays 3.30, 3.58 and 3.64. delta minus one and tau 100 satisfy the hypotheses. -/
theorem saddlePath_realEndpoint (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    saddlePath δ τ (realEndpoint δ τ) = (realEndpoint δ τ : ℂ) := by
  have hc := c1_pos _ (rho_pos δ τ hδ hτ)
  have hL := ell_pos δ hδ
  have hp := realEndpoint_pos δ τ hδ hτ
  have hy : (-c1 (rho δ τ) * realEndpoint δ τ / ell δ + c0 (rho δ τ)) *
      realEndpoint δ τ = 0 := by
    unfold realEndpoint
    field_simp
    <;> ring
  dsimp only [saddlePath]
  rw [hy]
  simp [sqrt_sq_eq_abs, abs_of_pos hp]

/-- P0014 pages 16 and 68, displays 3.25 and A.35. rho one. -/
theorem upsilon_lt_one (ρ : ℝ) (hρ : 0 < ρ) : upsilon ρ < 1 := by
  have hv := ups_gt_one ρ hρ
  let A := 2 * BookE.ups ρ * (BookE.ups ρ + sqrt (1 + ρ ^ 2)) / ρ
  have ha : 0 < arctan A := arctan_pos.mpr (div_pos (by positivity) hρ)
  have hu := arctan_lt_pi_div_two A
  have h := tan_lt_tan_of_nonneg_of_lt_pi_div_two (by linarith : 0 ≤ arctan A / 2)
    (by linarith [pi_pos] : π / 4 < π / 2) (by linarith : arctan A / 2 < π / 4)
  simpa only [tan_pi_div_four, A, upsilon] using h

/-- Derived tangent double angle identity for display 3.25 on page 16. rho one. -/
theorem upsilon_quadratic (ρ : ℝ) (hρ : 0 < ρ) :
    (2 * BookE.ups ρ * (BookE.ups ρ + sqrt (1 + ρ ^ 2)) / ρ) *
      (1 - upsilon ρ ^ 2) = 2 * upsilon ρ := by
  have hw := upsilon_pos ρ hρ
  have hw1 := upsilon_lt_one ρ hρ
  have hd : 1 - upsilon ρ ^ 2 ≠ 0 := by nlinarith
  have h := @tan_two_mul (arctan
    (2 * BookE.ups ρ * (BookE.ups ρ + sqrt (1 + ρ ^ 2)) / ρ) / 2)
  rw [show 2 * (arctan
    (2 * BookE.ups ρ * (BookE.ups ρ + sqrt (1 + ρ ^ 2)) / ρ) / 2) = arctan
    (2 * BookE.ups ρ * (BookE.ups ρ + sqrt (1 + ρ ^ 2)) / ρ) by ring, tan_arctan] at h
  exact (eq_div_iff hd).mp h

/-- Derived algebra for the coefficient in display 3.34 and A.14. a four fifths, b three fifths, A four thirds and w one half. -/
theorem c0_ge_one_of_quadratic (a b A w : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hb1 : b < 1)
    (hA : 0 < A) (hw : 0 < w) (hab : a ^ 2 + b ^ 2 = 1)
    (hroot : A * (1 - w ^ 2) = 2 * w) (hAb : a ≤ A * b) :
    1 ≤ a * w + b := by
  by_contra h
  have hn : a * w + b - 1 < 0 := by linarith
  have hs : 0 < (1 - b) ^ 2 - (a * w) ^ 2 := by
    have := mul_pos (by linarith : 0 < 1 - b - a * w)
      (by positivity : 0 < 1 - b + a * w)
    nlinarith only [this]
  have he : A * ((1 - b) ^ 2 - (a * w) ^ 2) =
      2 * a * (a * w + b - 1) + 2 * (1 - b) * (a - A * b) := by
    have hr := congrArg (fun x : ℝ => a ^ 2 * x) hroot
    have hc := congrArg (fun x : ℝ => A * x) hab
    nlinarith only [hr, hc]
  have hp := mul_pos hA hs
  have ht := mul_neg_of_pos_of_neg (by positivity : 0 < 2 * a) hn
  have ht2 := mul_nonpos_of_nonneg_of_nonpos
    (by positivity : 0 ≤ 2 * (1 - b)) (by linarith : a - A * b ≤ 0)
  linarith


/-- P0014 Appendix A, display A.14, with the formulas of displays 3.25 and 3.34. rho one. -/
theorem c0_ge_one (ρ : ℝ) (hρ : 0 < ρ) : 1 ≤ c0 ρ := by
  let v := BookE.ups ρ
  let j := sqrt (1 + ρ ^ 2)
  let a := sqrt (1 / 2 + 1 / (2 * v))
  let b := sqrt (1 / 2 - 1 / (2 * v))
  let A := 2 * v * (v + j) / ρ
  have hv : 1 < v := ups_gt_one ρ hρ
  have hvp : 0 < v := by linarith
  have hj : 1 < j := lt_sqrt_of_sq_lt (by nlinarith)
  have hi : 1 / (2 * v) < 1 / 2 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  have harp : 0 < 1 / 2 + 1 / (2 * v) := by positivity
  have hbrp : 0 < 1 / 2 - 1 / (2 * v) := by linarith
  have ha : 0 < a := sqrt_pos.mpr harp
  have hb : 0 < b := sqrt_pos.mpr hbrp
  have ha2 : a ^ 2 = 1 / 2 + 1 / (2 * v) := sq_sqrt harp.le
  have hb2 : b ^ 2 = 1 / 2 - 1 / (2 * v) := sq_sqrt hbrp.le
  have ha2s : 2 * v * a ^ 2 = v + 1 := by rw [ha2]; field_simp <;> ring
  have hb2s : 2 * v * b ^ 2 = v - 1 := by rw [hb2]; field_simp <;> ring
  have hab : a ^ 2 + b ^ 2 = 1 := by rw [ha2, hb2]; ring
  have hb1 : b < 1 := by nlinarith
  have hv2 : v ^ 2 = (1 + j) / 2 := sq_sqrt (by positivity)
  have hjv : j = 2 * v ^ 2 - 1 := by linarith
  have hj2 : j ^ 2 = 1 + ρ ^ 2 := sq_sqrt (by positivity)
  have hρv : ρ ^ 2 = 4 * v ^ 2 * (v ^ 2 - 1) := by
    rw [hjv] at hj2
    nlinarith only [hj2]
  have hs : (ρ * a) ^ 2 = (2 * v * b * (v + 1)) ^ 2 := by
    calc
      _ = 2 * v * (v - 1) * (v + 1) * (2 * v * a ^ 2) := by
        rw [mul_pow, hρv]
        ring
      _ = 2 * v * (v - 1) * (v + 1) * (v + 1) := by rw [ha2s]
      _ = _ := by rw [← hb2s]; ring
  have hra : ρ * a = 2 * v * b * (v + 1) :=
    (sq_eq_sq₀ (by positivity) (by positivity)).mp hs
  have hAb : a ≤ A * b := by
    apply (mul_le_mul_iff_right₀ hρ).mp
    calc
      _ = 2 * v * b * (v + 1) := hra
      _ ≤ 2 * v * b * (v + j) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by dsimp [A]; field_simp <;> ring
  have hAp : 0 < A := div_pos (by positivity) hρ
  exact c0_ge_one_of_quadratic a b A (upsilon ρ) ha hb.le hb1 hAp (upsilon_pos ρ hρ)
    hab (upsilon_quadratic ρ hρ) hAb

/-- P0014 page 24, display 3.58, using the non-strict consequence of A.14 on page 63. delta minus one and tau 100. -/
theorem initialRadius_pos (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    0 < initialRadius δ τ := by
  have hc := c1_pos _ (rho_pos δ τ hδ hτ)
  have h0 := c0_ge_one _ (rho_pos δ τ hδ hτ)
  have hi : 1 / sqrt (2:ℝ) < 1 := (div_lt_one (by positivity)).mpr
    (lt_sqrt_of_sq_lt (by norm_num))
  unfold initialRadius
  exact mul_pos (div_pos (ell_pos δ hδ) hc) (by linarith)

/-- P0014 pages 17 and 24, displays 3.30 and 3.58. delta minus one and tau 100. -/
theorem saddlePath_initialRadius (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    saddlePath δ τ (initialRadius δ τ) = (initialRadius δ τ : ℂ) * rayDirection τ := by
  let R := initialRadius δ τ
  have hR : 0 < R := initialRadius_pos δ τ hδ hτ
  have hc := c1_pos _ (rho_pos δ τ hδ hτ)
  have hL := ell_pos δ hδ
  have hs : 0 < sqrt (2:ℝ) := by positivity
  have hcr : c1 (rho δ τ) * R / ell δ = c0 (rho δ τ) - 1 / sqrt 2 := by
    dsimp [R, initialRadius]
    field_simp
    <;> ring
  have hy : (-c1 (rho δ τ) * R / ell δ + c0 (rho δ τ)) * R = R / sqrt 2 := by
    rw [neg_mul, neg_div, hcr]
    ring
  have hsq : (R / sqrt 2) ^ 2 = R ^ 2 / 2 := by
    rw [div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hx : sqrt (R ^ 2 - (R / sqrt 2) ^ 2) = R / sqrt 2 := by
    rw [show R ^ 2 - (R / sqrt 2) ^ 2 = (R / sqrt 2) ^ 2 by nlinarith,
      sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  change saddlePath δ τ R = (R : ℂ) * rayDirection τ
  dsimp only [saddlePath]
  rw [hy, hx]
  unfold rayDirection
  have hsc : (sqrt (2:ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  split_ifs <;> push_cast <;> field_simp [hsc] <;> ring

/-- Derived Cauchy input for P0014 pages 18 and 24, displays 3.36 and 3.59. delta minus one, s one half plus 100 i and domain point one. -/
theorem contourKernel_hasPrimitive (δ : ℝ) (s : ℂ) :
    Complex.IsExactOn (contourKernel δ s) Complex.slitPlane := by
  let c : ℂ := 2 * Real.pi * Complex.I * δ
  let g : ℂ → ℂ := fun w => Complex.exp ((s - 1) * w) *
    Complex.exp (-Complex.exp w ^ 2 / 2 + c * Complex.exp w) * Complex.exp w
  have hg : Differentiable ℂ g := by dsimp [g]; fun_prop
  obtain ⟨G, hG⟩ := hg.isExactOn_univ
  refine ⟨fun z => G (Complex.log z), ?_⟩
  intro z hz
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hp : Complex.exp ((s - 1) * Complex.log z) = z ^ (s - 1) := by
    rw [Complex.cpow_def_of_ne_zero hz0]
    congr 1
    ring
  have h := (hG (Complex.log z) (mem_univ _)).comp z (Complex.hasDerivAt_log hz)
  simpa [g, c, contourKernel, Complex.exp_log hz0, hp, mul_assoc, hz0, Function.comp_def] using h

/-- Derived geometry of P0014 pages 17 and 24, displays 3.30 and 3.58. delta minus one, tau 100 and radius at the real endpoint. -/
theorem saddlePath_height_bounds (δ τ r : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|)
    (hr : r ∈ Icc (initialRadius δ τ) (realEndpoint δ τ)) :
    let y := (-c1 (rho δ τ) * r / ell δ + c0 (rho δ τ)) * r
    0 < r ∧ 0 ≤ y ∧ y ≤ r / sqrt 2 := by
  have hc := c1_pos _ (rho_pos δ τ hδ hτ)
  have hL := ell_pos δ hδ
  have hrp : 0 < r := (initialRadius_pos δ τ hδ hτ).trans_le hr.1
  have hx : c1 (rho δ τ) * realEndpoint δ τ / ell δ = c0 (rho δ τ) := by
    unfold realEndpoint
    field_simp
    <;> ring
  have ha : c1 (rho δ τ) * initialRadius δ τ / ell δ =
      c0 (rho δ τ) - 1 / sqrt 2 := by
    unfold initialRadius
    field_simp
    <;> ring
  have hu : c1 (rho δ τ) * r / ell δ ≤ c0 (rho δ τ) := by
    rw [← hx]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr.2 hc.le) hL.le
  have hl : c0 (rho δ τ) - 1 / sqrt 2 ≤ c1 (rho δ τ) * r / ell δ := by
    rw [← ha]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr.1 hc.le) hL.le
  have ht0 : 0 ≤ -c1 (rho δ τ) * r / ell δ + c0 (rho δ τ) := by rw [neg_mul, neg_div]; linarith
  have ht1 : -c1 (rho δ τ) * r / ell δ + c0 (rho δ τ) ≤ 1 / sqrt 2 := by rw [neg_mul, neg_div]; linarith
  refine ⟨hrp, mul_nonneg ht0 hrp.le, ?_⟩
  calc
    _ ≤ (1 / sqrt 2) * r := mul_le_mul_of_nonneg_right ht1 hrp.le
    _ = _ := by ring

/-- Derived domain check for P0014 page 17, display 3.30. delta minus one, tau 100 and radius at the real endpoint. -/
theorem saddlePath_re_pos (δ τ r : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|)
    (hr : r ∈ Icc (initialRadius δ τ) (realEndpoint δ τ)) :
    0 < (saddlePath δ τ r).re := by
  let y := (-c1 (rho δ τ) * r / ell δ + c0 (rho δ τ)) * r
  have hb := saddlePath_height_bounds δ τ r hδ hτ hr
  have hy0 : 0 ≤ y := hb.2.1
  have hyr : y ≤ r / sqrt 2 := hb.2.2
  have hysq := pow_le_pow_left₀ hy0 hyr 2
  rw [div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hysq
  have hsub : 0 < r ^ 2 - y ^ 2 := by nlinarith [hb.1]
  have he : (saddlePath δ τ r).re = sqrt (r ^ 2 - y ^ 2) := by
    dsimp [saddlePath, y]
    split_ifs <;> simp
  rw [he]
  exact sqrt_pos.mpr hsub

/-- P0014 page 17, display 3.30. delta minus one, tau 100 and radius at the real endpoint. -/
theorem saddlePath_norm (δ τ r : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|)
    (hr : r ∈ Icc (initialRadius δ τ) (realEndpoint δ τ)) :
    ‖saddlePath δ τ r‖ = r := by
  let y := (-c1 (rho δ τ) * r / ell δ + c0 (rho δ τ)) * r
  have hb := saddlePath_height_bounds δ τ r hδ hτ hr
  have hy0 : 0 ≤ y := hb.2.1
  have hyr : y ≤ r / sqrt 2 := hb.2.2
  have hysq := pow_le_pow_left₀ hy0 hyr 2
  rw [div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hysq
  have hsub : 0 ≤ r ^ 2 - y ^ 2 := by nlinarith [hb.1]
  have he : Complex.normSq (saddlePath δ τ r) = r ^ 2 := by
    change Complex.normSq ((sqrt (r ^ 2 - y ^ 2) : ℂ) +
      (if 0 ≤ τ then (y : ℂ) else -y) * Complex.I) = r ^ 2
    split_ifs <;> norm_num [Complex.normSq_apply] <;> nlinarith [sq_sqrt hsub]
  rw [Complex.norm_def, he, sqrt_sq_eq_abs, abs_of_pos hb.1]

/-- Derived regularity of P0014 page 17, display 3.30, on the segment in page 24, display 3.58. delta minus one, tau 100 and the real endpoint radius. -/
theorem saddlePath_contDiffAt (δ τ r : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|)
    (hr : r ∈ Icc (initialRadius δ τ) (realEndpoint δ τ)) :
    ContDiffAt ℝ 2 (saddlePath δ τ) r := by
  let y := (-c1 (rho δ τ) * r / ell δ + c0 (rho δ τ)) * r
  have hb := saddlePath_height_bounds δ τ r hδ hτ hr
  have hy0 : 0 ≤ y := hb.2.1
  have hyr : y ≤ r / sqrt 2 := hb.2.2
  have hysq := pow_le_pow_left₀ hy0 hyr 2
  rw [div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hysq
  have hsub : 0 < r ^ 2 - y ^ 2 := by nlinarith [hb.1]
  let Y : ℝ → ℝ := fun t => (-c1 (rho δ τ) * t / ell δ + c0 (rho δ τ)) * t
  have hycd : ContDiffAt ℝ 2 Y r := by dsimp [Y]; fun_prop
  have hrad : ContDiffAt ℝ 2 (fun t => t ^ 2 - Y t ^ 2) r := by fun_prop
  have hxcd := hrad.sqrt (show r ^ 2 - Y r ^ 2 ≠ 0 from hsub.ne')
  have hxc : ContDiffAt ℝ 2 (fun t => (sqrt (t ^ 2 - Y t ^ 2) : ℂ)) r :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp r hxcd
  have hyc : ContDiffAt ℝ 2 (fun t => (Y t : ℂ)) r :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp r hycd
  unfold saddlePath
  split_ifs
  · exact hxc.add (hyc.mul contDiffAt_const)
  · exact hxc.add (hyc.neg.mul contDiffAt_const)

/-- Derived finite Cauchy identity for P0014 pages 18 and 24, displays 3.30 and 3.59. delta minus one and s one half plus 100 i. -/
theorem saddleIntegral_eq_sub (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0) (hτ : 0 < |s.im|) :
    ∃ F : ℂ → ℂ, (∀ z ∈ Complex.slitPlane, HasDerivAt F (contourKernel δ s z) z) ∧
      saddleIntegral δ s = F (realEndpoint δ s.im) -
        F ((initialRadius δ s.im : ℂ) * rayDirection s.im) := by
  obtain ⟨F, hF⟩ := contourKernel_hasPrimitive δ s
  refine ⟨F, hF, ?_⟩
  let a := initialRadius δ s.im
  let b := realEndpoint δ s.im
  let γ := saddlePath δ s.im
  have hab : a < b := initialRadius_lt_realEndpoint δ s.im hδ hτ
  have hcd : ∀ r ∈ Icc a b, ContDiffAt ℝ 2 γ r := fun r hr =>
    saddlePath_contDiffAt δ s.im r hδ hτ hr
  have hγc : ContinuousOn γ (Icc a b) := fun r hr =>
    (hcd r hr).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv γ) (Icc a b) := fun r hr =>
    ((hcd r hr).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hkc : ContinuousOn (fun r => contourKernel δ s (γ r)) (Icc a b) :=
    (contourKernel_differentiable δ s).continuousOn.comp hγc
      (fun r hr => saddlePath_re_pos δ s.im r hδ hτ hr)
  have hint : IntervalIntegrable (fun r => contourKernel δ s (γ r) * deriv γ r)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab.le]
    exact hkc.mul hdc
  have hderiv : ∀ r ∈ uIcc a b, HasDerivAt (fun r => F (γ r))
      (contourKernel δ s (γ r) * deriv γ r) r := by
    intro r hr
    rw [uIcc_of_le hab.le] at hr
    exact (hF (γ r) (Or.inl (saddlePath_re_pos δ s.im r hδ hτ hr))).comp r
      ((hcd r hr).differentiableAt (by norm_num)).hasDerivAt
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa only [a, b, γ, saddleIntegral, saddlePath_realEndpoint δ s.im hδ hτ,
    saddlePath_initialRadius δ s.im hδ hτ] using ht

/-- P0014 page 24 before display 3.59 and reflection. tau 100 and minus 100. -/
theorem rayDirection_re (τ : ℝ) : (rayDirection τ).re = 1 / sqrt 2 := by
  unfold rayDirection
  rw [Complex.div_ofReal_re]
  split_ifs <;> simp

/-- Derived uniform finite contour completion for P0014 pages 18 and 24, before display 3.59. delta minus one and s one half plus 100 i. The same primitive works for every admissible epsilon. -/
theorem finite_contour_identity_uniform (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0) (hτ : 0 < |s.im|) :
    ∃ F : ℂ → ℂ, (∀ z ∈ Complex.slitPlane, HasDerivAt F (contourKernel δ s z) z) ∧
      ∀ ε : ℝ, 0 < ε → ε < initialRadius δ s.im →
        (∫ t : ℝ in ε..(realEndpoint δ s.im), contourKernel δ s t) =
          (∫ t : ℝ in ε..(initialRadius δ s.im),
            contourKernel δ s (t * rayDirection s.im) * rayDirection s.im) +
          saddleIntegral δ s + (F (ε * rayDirection s.im) - F ε) := by
  obtain ⟨F, hF, hc2⟩ := saddleIntegral_eq_sub δ s hδ hτ
  refine ⟨F, hF, ?_⟩
  intro ε hε hεa
  let a := initialRadius δ s.im
  let b := realEndpoint δ s.im
  let w := rayDirection s.im
  have hab : a < b := initialRadius_lt_realEndpoint δ s.im hδ hτ
  have hεb : ε < b := hεa.trans hab
  have hw : 0 < w.re := by dsimp [w]; rw [rayDirection_re]; positivity
  have hrealc : ContinuousOn (fun t : ℝ => contourKernel δ s t) (uIcc ε b) := by
    apply (contourKernel_differentiable δ s).continuousOn.comp Complex.continuous_ofReal.continuousOn
    intro t ht
    rw [uIcc_of_le hεb.le] at ht
    exact hε.trans_le ht.1
  have hrealD : ∀ t ∈ uIcc ε b, HasDerivAt (fun t : ℝ => F t) (contourKernel δ s t) t := by
    intro t ht
    rw [uIcc_of_le hεb.le] at ht
    have htpos := hε.trans_le ht.1
    simpa [Function.comp_def] using
      (hF (t:ℂ) (Or.inl htpos)).comp t (hasDerivAt_id t).ofReal_comp
  have hreal := intervalIntegral.integral_eq_sub_of_hasDerivAt hrealD hrealc.intervalIntegrable
  have hmap : ∀ t ∈ uIcc ε a, 0 < ((t : ℂ) * w).re := by
    intro t ht
    rw [uIcc_of_le hεa.le] at ht
    have htpos := hε.trans_le ht.1
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_pos htpos hw
  have hrayc : ContinuousOn (fun t : ℝ => contourKernel δ s (t * w)) (uIcc ε a) :=
    (contourKernel_differentiable δ s).continuousOn.comp (by fun_prop) hmap
  have hrayD : ∀ t ∈ uIcc ε a, HasDerivAt (fun t : ℝ => F (t * w))
      (contourKernel δ s (t * w) * w) t := by
    intro t ht
    have hvel : HasDerivAt (fun t : ℝ => (t : ℂ) * w) w t := by
      simpa using (hasDerivAt_id t).ofReal_comp.mul_const w
    exact (hF (t * w) (Or.inl (hmap t ht))).comp t hvel
  have hray := intervalIntegral.integral_eq_sub_of_hasDerivAt hrayD (hrayc.mul_const w).intervalIntegrable
  change (∫ t : ℝ in ε..b, contourKernel δ s t) =
    (∫ t : ℝ in ε..a, contourKernel δ s (t * w) * w) +
      saddleIntegral δ s + (F (ε * w) - F ε)
  rw [hreal, hray, hc2]
  dsimp only [a, b, w]
  ring

/-- Derived finite contour completion for P0014 pages 18 and 24, before display 3.59. delta minus one, s one half plus 100 i and epsilon half the positive initial radius. -/
theorem finite_contour_identity (δ : ℝ) (s : ℂ) (ε : ℝ)
    (hδ : δ ≠ 0) (hτ : 0 < |s.im|) (hε : 0 < ε) (hεa : ε < initialRadius δ s.im) :
    ∃ F : ℂ → ℂ, (∀ z ∈ Complex.slitPlane, HasDerivAt F (contourKernel δ s z) z) ∧
      (∫ t : ℝ in ε..(realEndpoint δ s.im), contourKernel δ s t) =
        (∫ t : ℝ in ε..(initialRadius δ s.im),
          contourKernel δ s (t * rayDirection s.im) * rayDirection s.im) +
        saddleIntegral δ s + (F (ε * rayDirection s.im) - F ε) := by
  obtain ⟨F, hF, hfinite⟩ := finite_contour_identity_uniform δ s hδ hτ
  exact ⟨F, hF, hfinite ε hε hεa⟩

/-- Derived origin arc majorant for the Cauchy shift on P0014 pages 18 and 24. delta minus one, s one half plus 100 i and z one. -/
theorem kernel_radius_majorant (δ : ℝ) (s z : ℂ) (hz : z ≠ 0) :
    ‖contourKernel δ s z * z‖ ≤ ‖z‖ ^ s.re *
      exp (|s.im| * π + ‖z‖ ^ 2 / 2 + ell δ * ‖z‖) := by
  let c : ℂ := 2 * π * Complex.I * δ
  let W : ℂ := -z ^ 2 / 2 + c * z
  have hc : ‖c‖ = ell δ := by
    dsimp [c, ell]
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  have hp : z ^ (s - 1) * z = z ^ s := by
    simpa using (Complex.cpow_add (s - 1) 1 hz).symm
  have he : contourKernel δ s z * z = z ^ s * Complex.exp W := by
    change z ^ (s - 1) * Complex.exp W * z = z ^ s * Complex.exp W
    calc
      _ = (z ^ (s - 1) * z) * Complex.exp W := by ring
      _ = _ := by rw [hp]
  have hw : W.re ≤ ‖z‖ ^ 2 / 2 + ell δ * ‖z‖ := by
    calc
      _ ≤ ‖W‖ := Complex.re_le_norm W
      _ ≤ ‖-z ^ 2 / 2‖ + ‖c * z‖ := norm_add_le _ _
      _ = _ := by rw [norm_div, norm_neg, norm_pow, norm_mul, hc]; norm_num
  have ha : -(Complex.arg z * s.im) ≤ |s.im| * π := by
    calc
      _ ≤ |-(Complex.arg z * s.im)| := le_abs_self _
      _ = |s.im| * |Complex.arg z| := by rw [abs_neg, abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi z) (abs_nonneg _)
  rw [he]
  calc
    _ = ‖z‖ ^ s.re * exp (-(Complex.arg z * s.im) + W.re) := by
      rw [norm_mul, Complex.norm_cpow_of_ne_zero hz, Complex.norm_exp, exp_add, exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith))
      positivity

/-- Derived small arc estimate for the contour completion on P0014 pages 18 and 24. Take delta minus one, s one half plus 100 i, a primitive from contourKernel_hasPrimitive, epsilon one and alpha pi over four. -/
theorem primitive_origin_arc_bound (δ : ℝ) (s : ℂ) (F : ℂ → ℂ)
    (hF : ∀ z ∈ Complex.slitPlane, HasDerivAt F (contourKernel δ s z) z)
    (ε α : ℝ) (hε : 0 < ε) (hα : α ∈ Icc (-(π / 4)) (π / 4)) :
    ‖F (ε * Complex.exp ((α : ℂ) * Complex.I)) - F ε‖ ≤
      |α| * (ε ^ s.re * exp (|s.im| * π + ε ^ 2 / 2 + ell δ * ε)) := by
  let γ : ℝ → ℂ := fun φ => ε * Complex.exp ((φ : ℂ) * Complex.I)
  have hγnorm : ∀ φ : ℝ, ‖γ φ‖ = ε := by
    intro φ
    simp [γ, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε]
  have hγre : ∀ φ : ℝ, (γ φ).re = ε * cos φ := by
    intro φ
    simp [γ, Complex.mul_re, Complex.exp_re, Complex.exp_im]
  have hbounds : ∀ φ ∈ uIcc 0 α, φ ∈ Ioo (-(π / 2)) (π / 2) := by
    intro φ hφ
    rcases le_total 0 α with hp | hn
    · rw [uIcc_of_le hp] at hφ
      rcases hφ with ⟨hlo, hhi⟩
      constructor <;> linarith [hα.1, hα.2, pi_pos]
    · rw [uIcc_of_ge hn] at hφ
      rcases hφ with ⟨hlo, hhi⟩
      constructor <;> linarith [hα.1, hα.2, pi_pos]
  have hmap : ∀ φ ∈ uIcc 0 α, 0 < (γ φ).re := by
    intro φ hφ
    rw [hγre]
    exact mul_pos hε (cos_pos_of_mem_Ioo (hbounds φ hφ))
  have hγD : ∀ φ : ℝ, HasDerivAt γ (Complex.I * γ φ) φ := by
    intro φ
    have h := (((hasDerivAt_id φ).ofReal_comp.mul_const Complex.I).cexp).const_mul (ε : ℂ)
    convert h using 1 <;> simp only [γ, id_eq, Complex.ofReal_one, one_mul] <;> ring
  have hγc : Continuous γ := by dsimp [γ]; fun_prop
  have hkc : ContinuousOn (fun φ => contourKernel δ s (γ φ) * (Complex.I * γ φ)) (uIcc 0 α) :=
    ((contourKernel_differentiable δ s).continuousOn.comp hγc.continuousOn hmap).mul
      (continuous_const.mul hγc).continuousOn
  have hderiv : ∀ φ ∈ uIcc 0 α, HasDerivAt (fun φ => F (γ φ))
      (contourKernel δ s (γ φ) * (Complex.I * γ φ)) φ := by
    intro φ hφ
    exact (hF (γ φ) (Or.inl (hmap φ hφ))).comp φ (hγD φ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hkc.intervalIntegrable
  have hbound : ∀ φ : ℝ, ‖contourKernel δ s (γ φ) * (Complex.I * γ φ)‖ ≤
      ε ^ s.re * exp (|s.im| * π + ε ^ 2 / 2 + ell δ * ε) := by
    intro φ
    have hz : γ φ ≠ 0 := by
      intro hz
      have h := hγnorm φ
      rw [hz, norm_zero] at h
      linarith
    have h := kernel_radius_majorant δ s (γ φ) hz
    have he : contourKernel δ s (γ φ) * (Complex.I * γ φ) =
        Complex.I * (contourKernel δ s (γ φ) * γ φ) := by ring
    rw [he, norm_mul, Complex.norm_I, one_mul]
    simpa only [hγnorm] using h
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := α)
    (fun φ _ => hbound φ)
  rw [hFTC] at hn
  simpa [γ, mul_comm] using hn

/-- P0014 page 24 before display 3.59 and reflection. tau 100 or minus 100. -/
theorem rayDirection_eq_exp (τ : ℝ) :
    rayDirection τ = Complex.exp (((if 0 ≤ τ then π / 4 else -(π / 4) : ℝ) : ℂ) * Complex.I) := by
  have hs : sqrt (2:ℝ) ≠ 0 := (sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  unfold rayDirection
  split_ifs <;> apply Complex.ext <;>
    simp [Complex.exp_re, Complex.exp_im, cos_pi_div_four, sin_pi_div_four]
  all_goals field_simp <;> nlinarith [sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- Derived singular endpoint limit for the contour completion on P0014 pages 18 and 24. delta minus one and s one half plus 100 i, with the primitive supplied by contourKernel_hasPrimitive. -/
theorem primitive_origin_defect_tendsto (δ : ℝ) (s : ℂ) (F : ℂ → ℂ)
    (hF : ∀ z ∈ Complex.slitPlane, HasDerivAt F (contourKernel δ s z) z)
    (hσ : 0 < s.re) :
    Tendsto (fun ε : ℝ => F (ε * rayDirection s.im) - F ε) (𝓝[>] 0) (𝓝 0) := by
  let α : ℝ := if 0 ≤ s.im then π / 4 else -(π / 4)
  have hα : α ∈ Icc (-(π / 4)) (π / 4) := by
    dsimp [α]
    split_ifs <;> constructor <;> linarith [pi_pos]
  have hbound : ∀ ε : ℝ, 0 < ε → ‖F (ε * rayDirection s.im) - F ε‖ ≤
      |α| * (ε ^ s.re * exp (|s.im| * π + ε ^ 2 / 2 + ell δ * ε)) := by
    intro ε hε
    rw [rayDirection_eq_exp]
    exact primitive_origin_arc_bound δ s F hF ε α hε hα
  have hp := (continuousAt_rpow_const 0 s.re (Or.inr hσ.le)).tendsto
  have hc : ContinuousAt (fun ε : ℝ => exp (|s.im| * π + ε ^ 2 / 2 + ell δ * ε)) 0 := by fun_prop
  have hpoly : Tendsto (fun ε : ℝ => ε ^ s.re *
      exp (|s.im| * π + ε ^ 2 / 2 + ell δ * ε)) (𝓝 0) (𝓝 0) := by
    simpa [zero_rpow hσ.ne'] using hp.mul hc.tendsto
  have hK : Tendsto (fun ε : ℝ => |α| * (ε ^ s.re *
      exp (|s.im| * π + ε ^ 2 / 2 + ell δ * ε))) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hpoly.const_mul |α|).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hεevent : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hn : Tendsto (fun ε : ℝ => ‖F (ε * rayDirection s.im) - F ε‖) (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun ε => norm_nonneg _))
      (hεevent.mono (fun ε hε => hbound ε hε)) hK
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

/-- Convergence step for P0014 page 24, display 3.59. delta minus one, tau 100, s one half plus 100 i and endpoint one. -/
theorem ray_kernel_integrable (δ τ : ℝ) (s : ℂ) (a : ℝ)
    (hσ : 0 < s.re) (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => contourKernel δ s (r * rayDirection τ) * rayDirection τ) (Ioo 0 a) := by
  let w := rayDirection τ
  let K := exp (|s.im| * π + a ^ 2 / 2 + ell δ * a)
  have hw : ‖w‖ = 1 := rayDirection_norm τ
  have hwr : 0 < w.re := by dsimp [w]; rw [rayDirection_re]; positivity
  have hg : IntegrableOn (fun r : ℝ => r ^ (s.re - 1) * K) (Ioo 0 a) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff ha).mpr (by linarith : -1 < s.re - 1)).mul_const K
  have hbound : ∀ r ∈ Ioo 0 a, ‖contourKernel δ s (r * w) * w‖ ≤ r ^ (s.re - 1) * K := by
    intro r hr
    have hn : ‖(r : ℂ) * w‖ = r := by simp [norm_mul, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    have hz : (r : ℂ) * w ≠ 0 := by intro hz; rw [hz, norm_zero] at hn; linarith [hr.1]
    have h := kernel_radius_majorant δ s (r * w) hz
    have hs : r ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hr.1.le hr.2.le 2
    have hL : 0 ≤ ell δ := by unfold ell; positivity
    have hlin := mul_le_mul_of_nonneg_left hr.2.le hL
    have hcost : exp (|s.im| * π + r ^ 2 / 2 + ell δ * r) ≤ K :=
      exp_le_exp.mpr (by linarith)
    have hm : ‖contourKernel δ s (r * w) * w‖ * r =
        ‖contourKernel δ s (r * w) * (r * w)‖ := by
      simp [norm_mul, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    rw [hn] at h
    have hp : r ^ (s.re - 1) * r = r ^ s.re := by
      simpa using (rpow_add_one hr.1.ne' (s.re - 1)).symm
    have hfinal : ‖contourKernel δ s (r * w) * w‖ * r ≤ (r ^ (s.re - 1) * K) * r := by
      rw [hm]
      calc
        _ ≤ r ^ s.re * exp (|s.im| * π + r ^ 2 / 2 + ell δ * r) := h
        _ ≤ r ^ s.re * K := mul_le_mul_of_nonneg_left hcost (rpow_nonneg hr.1.le _)
        _ = _ := by rw [← hp]; ring
    exact le_of_mul_le_mul_right hfinal hr.1
  have hc : ContinuousOn (fun r : ℝ => contourKernel δ s (r * w) * w) (Ioo 0 a) := by
    apply ContinuousOn.mul_const _ w
    apply (contourKernel_differentiable δ s).continuousOn.comp (by fun_prop)
    intro r hr
    change 0 < ((r : ℂ) * w).re
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_pos hr.1 hwr
  exact hg.mono' (hc.aestronglyMeasurable measurableSet_Ioo)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr; exact hbound r hr)

/-- Derived endpoint integration step for P0014 pages 18 and 24. The zero function and endpoint one satisfy the hypotheses. -/
theorem truncated_integral_tendsto (f : ℝ → ℂ) (a : ℝ) (ha : 0 < a)
    (hf : IntegrableOn f (Ioo 0 a)) :
    Tendsto (fun ε : ℝ => ∫ r : ℝ in ε..a, f r) (𝓝[>] 0) (𝓝 (∫ r : ℝ in Ioo 0 a, f r)) := by
  have hcc : IntegrableOn f (uIcc 0 a) := by
    rw [uIcc_of_le ha.le, integrableOn_Icc_iff_integrableOn_Ioo]
    exact hf
  have hc := (intervalIntegral.continuousOn_primitive_interval_left hcc) 0 (left_mem_uIcc)
  have hm : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝[uIcc 0 a] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with ε hε hεa
    rw [uIcc_of_le ha.le]
    exact ⟨hε.le, hεa.le⟩
  have h := hc.tendsto.comp hm
  have he : (∫ r : ℝ in (0:ℝ)..a, f r) = ∫ r : ℝ in Ioo 0 a, f r := by
    rw [intervalIntegral.integral_of_le ha.le, integral_Ioc_eq_integral_Ioo]
  simpa only [Function.comp_def, he] using h

/-- Derived contour shift for P0014 pages 18 and 24 to 25, displays 3.59 and 3.64. delta minus one and s one half plus 100 i satisfy the convergence and nonzero conditions. -/
theorem contour_shift_positive_re (δ : ℝ) (s : ℂ)
    (hσ : 0 < s.re) (hδ : δ ≠ 0) (hτ : 0 < |s.im|) :
    gaussianMellin δ s = initialIntegral δ s + saddleIntegral δ s +
      (∫ x : ℝ in Ioi (realEndpoint δ s.im), (x : ℂ) ^ (s - 1) *
        ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))) := by
  let a := initialRadius δ s.im
  let b := realEndpoint δ s.im
  have ha : 0 < a := initialRadius_pos δ s.im hδ hτ
  have hb : 0 < b := realEndpoint_pos δ s.im hδ hτ
  have hf : IntegrableOn (fun x : ℝ => contourKernel δ s x) (Ioi 0) := by
    simpa only [contourKernel_real, smul_eq_mul] using
      LeanLab.HelfgottMajor.Decomp511b.twisted_mellin_integrable δ s hσ
  have hfi : IntegrableOn (fun x : ℝ => contourKernel δ s x) (Ioo 0 b) :=
    hf.mono_set (fun _ hx => hx.1)
  have hfc : IntegrableOn (fun x : ℝ => contourKernel δ s x) (Ici b) :=
    hf.mono_set (fun _ hx => hb.trans_le hx)
  have hU : Ioi (0:ℝ) = Ioo 0 b ∪ Ici b := by
    ext x
    constructor
    · intro hx
      by_cases hxb : x < b
      · exact Or.inl ⟨hx, hxb⟩
      · exact Or.inr (le_of_not_gt hxb)
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · exact hb.trans_le hx
  have hD : Disjoint (Ioo (0:ℝ) b) (Ici b) :=
    disjoint_left.mpr (fun _ hx hy => not_lt_of_ge hy hx.2)
  have hpart : (∫ x : ℝ in Ioi 0, contourKernel δ s x) =
      (∫ x : ℝ in Ioo 0 b, contourKernel δ s x) +
      (∫ x : ℝ in Ioi b, contourKernel δ s x) := by
    rw [hU, setIntegral_union hD measurableSet_Ici hfi hfc, integral_Ici_eq_integral_Ioi]
  have hcut : (∫ x : ℝ in Ioo 0 b, contourKernel δ s x) =
      initialIntegral δ s + saddleIntegral δ s := by
    obtain ⟨F, hF, hfinite⟩ := finite_contour_identity_uniform δ s hδ hτ
    have hL := truncated_integral_tendsto (fun x : ℝ => contourKernel δ s x) b hb hfi
    have hRray := truncated_integral_tendsto
      (fun r : ℝ => contourKernel δ s (r * rayDirection s.im) * rayDirection s.im) a ha
      (ray_kernel_integrable δ s.im s a hσ ha)
    have hDef := primitive_origin_defect_tendsto δ s F hF hσ
    have hR := (hRray.add (tendsto_const_nhds : Tendsto (fun _ : ℝ => saddleIntegral δ s)
      (𝓝[>] 0) (𝓝 (saddleIntegral δ s)))).add hDef
    have hevent : (fun ε : ℝ => ∫ x : ℝ in ε..b, contourKernel δ s x) =ᶠ[𝓝[>] 0]
        (fun ε : ℝ => (∫ r : ℝ in ε..a,
          contourKernel δ s (r * rayDirection s.im) * rayDirection s.im) +
          saddleIntegral δ s + (F (ε * rayDirection s.im) - F ε)) := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with ε hε hεa
      exact hfinite ε hε hεa
    have h := tendsto_nhds_unique (hL.congr' hevent) hR
    simpa only [a, initialIntegral, add_zero] using h
  have hmellin : gaussianMellin δ s = ∫ x : ℝ in Ioi 0, contourKernel δ s x := by
    simp only [gaussianMellin, mellin, smul_eq_mul, contourKernel_real]
  rw [hmellin, hpart, hcut]
  simp only [contourKernel_real, b]

/-- Derived normalization of P0014 pages 14 and 16, displays 3.15 and 3.25, using the existing BookL1523 parameterization. t one half. -/
theorem shape_Rt (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    sqrt (1 + BookL1523.Rt t ^ 2) = (1 + 6 * t ^ 2 + t ^ 4) / (1 - t ^ 2) ^ 2 ∧
      BookE.ups (BookL1523.Rt t) = (1 + t ^ 2) / (1 - t ^ 2) := by
  have hq : 0 < 1 - t ^ 2 := by nlinarith
  have hs : sqrt (1 + BookL1523.Rt t ^ 2) = (1 + 6 * t ^ 2 + t ^ 4) / (1 - t ^ 2) ^ 2 := by
    rw [show 1 + BookL1523.Rt t ^ 2 = ((1 + 6 * t ^ 2 + t ^ 4) / (1 - t ^ 2) ^ 2) ^ 2 by
      unfold BookL1523.Rt; field_simp; ring]
    exact sqrt_sq (by positivity)
  refine ⟨hs, ?_⟩
  unfold BookE.ups
  rw [hs]
  rw [show (1 + (1 + 6 * t ^ 2 + t ^ 4) / (1 - t ^ 2) ^ 2) / 2 =
    ((1 + t ^ 2) / (1 - t ^ 2)) ^ 2 by field_simp; ring]
  exact sqrt_sq (by positivity)

/-- Derived forms of P0014 pages 16 and 18, displays 3.25 and 3.34. t one half. -/
theorem coefficients_Rt (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    c0 (BookL1523.Rt t) = (upsilon (BookL1523.Rt t) + t) / sqrt (1 + t ^ 2) ∧
      c1 (BookL1523.Rt t) = upsilon (BookL1523.Rt t) * (1 - t ^ 2) / (t * (1 + t ^ 2)) ∧
      2 * BookE.ups (BookL1523.Rt t) *
        (BookE.ups (BookL1523.Rt t) + sqrt (1 + BookL1523.Rt t ^ 2)) / BookL1523.Rt t =
          (1 + 3 * t ^ 2) / (t * (1 - t ^ 2)) := by
  have hq : 0 < 1 - t ^ 2 := by nlinarith
  have hu : 0 < 1 + t ^ 2 := by positivity
  have hd : 0 < BookL1523.Rt t := by unfold BookL1523.Rt; positivity
  obtain ⟨hj, hv⟩ := shape_Rt t h0 h1
  have ha : sqrt (1 / 2 + 1 / (2 * BookE.ups (BookL1523.Rt t))) = 1 / sqrt (1 + t ^ 2) := by
    rw [hv, show 1 / 2 + 1 / (2 * ((1 + t ^ 2) / (1 - t ^ 2))) = (1 + t ^ 2)⁻¹ by field_simp; ring,
      sqrt_inv]
    simp only [one_div]
  have hb : sqrt (1 / 2 - 1 / (2 * BookE.ups (BookL1523.Rt t))) = t / sqrt (1 + t ^ 2) := by
    rw [hv, show 1 / 2 - 1 / (2 * ((1 + t ^ 2) / (1 - t ^ 2))) = t ^ 2 / (1 + t ^ 2) by field_simp; ring,
      sqrt_div (sq_nonneg t), sqrt_sq h0.le]
  have hc : sqrt ((1 + 1 / BookE.ups (BookL1523.Rt t)) /
      (BookE.ups (BookL1523.Rt t) ^ 2 - BookE.ups (BookL1523.Rt t))) =
      (1 - t ^ 2) / (t * (1 + t ^ 2)) := by
    have hx := ups_gt_one (BookL1523.Rt t) hd
    have hden : BookE.ups (BookL1523.Rt t) ^ 2 - BookE.ups (BookL1523.Rt t) ≠ 0 := by nlinarith
    rw [hv] at hden ⊢
    rw [show (1 + 1 / ((1 + t ^ 2) / (1 - t ^ 2))) /
      (((1 + t ^ 2) / (1 - t ^ 2)) ^ 2 - (1 + t ^ 2) / (1 - t ^ 2)) =
      ((1 - t ^ 2) / (t * (1 + t ^ 2))) ^ 2 by field_simp; ring]
    exact sqrt_sq (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · unfold c0
    rw [ha, hb]
    ring
  · unfold c1
    rw [hc]
    ring
  · rw [hv, hj]
    unfold BookL1523.Rt
    field_simp
    <;> ring

/-- Derived rational support for P0014 page 68, display A.36. t one half. -/
theorem param_denominator_lower (t : ℝ) (hlo : 1 / 2 ≤ t) (hhi : t ≤ 5 / 8) :
    3 / 8 ≤ t * (1 - t ^ 2) := by
  have ht : 0 ≤ t := by linarith
  have hs : t ^ 2 ≤ (5 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ ht hhi 2
  have hb : 0 ≤ 3 / 4 - t ^ 2 - t / 2 := by linarith
  have hp := mul_nonneg (show 0 ≤ t - 1 / 2 by linarith) hb
  nlinarith only [hp]

/-- Derived rational support for P0014 page 68, display A.36. These are proof bounds, not quoted paper constants. t one half and w Upsilon of Rt one half. -/
theorem param_direction_upper (t w : ℝ) (hlo : 1 / 2 ≤ t) (hhi : t ≤ 5 / 8)
    (hw0 : 0 < w) (hw1 : w < 1)
    (hq : ((1 + 3 * t ^ 2) / (t * (1 - t ^ 2))) * (1 - w ^ 2) = 2 * w) :
    (t ≤ 9 / 16 → w ≤ 827 / 1000) ∧ w ≤ 27 / 32 := by
  have hd := param_denominator_lower t hlo hhi
  have hdpos : 0 < t * (1 - t ^ 2) := by linarith
  have hw : 0 ≤ 1 - w ^ 2 := by nlinarith
  constructor
  · intro ht
    have hs : t ^ 2 ≤ (9 / 16 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) ht 2
    have hA : (1 + 3 * t ^ 2) / (t * (1 - t ^ 2)) ≤ 499 / 96 := by
      rw [div_le_iff₀ hdpos]
      nlinarith only [hs, hd]
    have hp := mul_nonneg (sub_nonneg.mpr hA) hw
    have hq' : 2 * w ≤ (499 / 96 : ℝ) * (1 - w ^ 2) := by nlinarith only [hq, hp]
    nlinarith only [hq', sq_nonneg (w - 827 / 1000)]
  · have hs : t ^ 2 ≤ (5 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hhi 2
    have hA : (1 + 3 * t ^ 2) / (t * (1 - t ^ 2)) ≤ 139 / 24 := by
      rw [div_le_iff₀ hdpos]
      nlinarith only [hs, hd]
    have hp := mul_nonneg (sub_nonneg.mpr hA) hw
    have hq' : 2 * w ≤ (139 / 24 : ℝ) * (1 - w ^ 2) := by nlinarith only [hq, hp]
    nlinarith only [hq', sq_nonneg (w - 27 / 32)]

/-- Derived small parameter branch for P0014 page 68, display A.36. t one half and w Upsilon of Rt one half. -/
theorem param_endpoint_small (t w : ℝ) (h0 : 0 < t) (ht : t ≤ 9 / 16)
    (hw0 : 0 < w) (hw1 : w < 1)
    (hq : ((1 + 3 * t ^ 2) / (t * (1 - t ^ 2))) * (1 - w ^ 2) = 2 * w) :
    w * sqrt (1 + t ^ 2) ≤ (w + t) * (1 - t ^ 2) := by
  have htsq : t ^ 2 ≤ (9 / 16 : ℝ) ^ 2 := pow_le_pow_left₀ h0.le ht 2
  by_cases hhalf : t ≤ 1 / 2
  · have hslo : 1 ≤ sqrt (1 + t ^ 2) := le_sqrt_of_sq_le (by nlinarith)
    have hs : sqrt (1 + t ^ 2) ≤ 1 + t ^ 2 / 2 := by
      apply sqrt_le_iff.mpr
      exact ⟨by positivity, by nlinarith only [sq_nonneg (t ^ 2)]⟩
    have hp := mul_nonneg (show 0 ≤ 1 - 2 * t by linarith) (show 0 ≤ 1 + t / 2 by positivity)
    have htp := mul_nonneg h0.le hp
    have hwp := mul_le_mul_of_nonneg_right hw1.le
      (show 0 ≤ sqrt (1 + t ^ 2) - 1 + t ^ 2 by nlinarith only [hslo, sq_nonneg t])
    nlinarith only [htp, hwp, hs]
  · have hlo : 1 / 2 ≤ t := le_of_not_ge hhalf
    have hupper := (param_direction_upper t w hlo (by linarith) hw0 hw1 hq).1 ht
    let P := 1 + t ^ 2 / 2 - t ^ 4 / 10
    have h4 : t ^ 4 ≤ t ^ 2 := by
      have hp := mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - t ^ 2 by nlinarith only [htsq])
      nlinarith only [hp]
    have hP : 0 ≤ P := by dsimp [P]; nlinarith only [h4, sq_nonneg t]
    have hb : 0 ≤ 1 / 20 - t ^ 2 / 10 + t ^ 4 / 100 := by
      nlinarith only [htsq, sq_nonneg (t ^ 2)]
    have hp := mul_nonneg (show 0 ≤ t ^ 4 by positivity) hb
    have hs : sqrt (1 + t ^ 2) ≤ P := sqrt_le_iff.mpr ⟨hP, by dsimp [P]; nlinarith only [hp]⟩
    have hbr : 0 ≤ 3 / 2 - ((9 / 16 : ℝ) ^ 2 + 9 / 16 * t + t ^ 2) / 10 := by
      nlinarith only [htsq, ht]
    have hgp := mul_nonneg (show 0 ≤ 9 / 16 - t by linarith) hbr
    have hg : 3 / 2 * t - t ^ 3 / 10 ≤ 3 / 2 * (9 / 16 : ℝ) - (9 / 16 : ℝ) ^ 3 / 10 := by
      nlinarith only [hgp]
    have hD : sqrt (1 + t ^ 2) - 1 + t ^ 2 ≤
        t * (3 / 2 * (9 / 16 : ℝ) - (9 / 16 : ℝ) ^ 3 / 10) := by
      have hh := mul_le_mul_of_nonneg_left hg h0.le
      dsimp [P] at hs
      nlinarith only [hs, hh]
    have hf : w * (sqrt (1 + t ^ 2) - 1 + t ^ 2) ≤ t * (1 - t ^ 2) := by
      calc
        _ ≤ w * (t * (3 / 2 * (9 / 16 : ℝ) - (9 / 16 : ℝ) ^ 3 / 10)) :=
          mul_le_mul_of_nonneg_left hD hw0.le
        _ ≤ (827 / 1000) * (t * (3 / 2 * (9 / 16 : ℝ) - (9 / 16 : ℝ) ^ 3 / 10)) :=
          mul_le_mul_of_nonneg_right hupper (mul_nonneg h0.le (by norm_num))
        _ ≤ t * (1 - (9 / 16 : ℝ) ^ 2) := by
          have hh := mul_le_mul_of_nonneg_left (show (827 / 1000 : ℝ) *
            (3 / 2 * (9 / 16 : ℝ) - (9 / 16 : ℝ) ^ 3 / 10) ≤ 1 - (9 / 16 : ℝ) ^ 2 by norm_num) h0.le
          nlinarith only [hh]
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [htsq]) h0.le
    nlinarith only [hf]

/-- Derived large parameter branch for P0014 page 68, display A.36. t three quarters and w Upsilon of Rt three quarters. -/
theorem param_endpoint_large (t w : ℝ) (hlo : 9 / 16 ≤ t) (h1 : t < 1)
    (hw0 : 0 < w) (hw1 : w < 1)
    (hq : ((1 + 3 * t ^ 2) / (t * (1 - t ^ 2))) * (1 - w ^ 2) = 2 * w) :
    (25 / 16 : ℝ) * w ^ 2 ≤ t * (w + t) ^ 2 := by
  by_cases ht : t ≤ 5 / 8
  · have hw := (param_direction_upper t w (by linarith) ht hw0 hw1 hq).2
    have hr : (5 / 3 : ℝ) * w ≤ w + t := by linarith
    have hs : (25 / 9 : ℝ) * w ^ 2 ≤ (w + t) ^ 2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ w + t + 5 / 3 * w by positivity)
      nlinarith only [hp]
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ t by linarith)
    have hT := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 25 / 9 * w ^ 2 by positivity)
    nlinarith only [hm, hT]
  · have ht0 : 5 / 8 ≤ t := le_of_not_ge ht
    have hr : (13 / 8 : ℝ) * w ≤ w + t := by linarith
    have hs : (169 / 64 : ℝ) * w ^ 2 ≤ (w + t) ^ 2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ w + t + 13 / 8 * w by positivity)
      nlinarith only [hp]
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ t by linarith)
    have hT := mul_le_mul_of_nonneg_right ht0 (show 0 ≤ 169 / 64 * w ^ 2 by positivity)
    nlinarith only [hm, hT, sq_nonneg w]


/-- P0014 page 68, display A.36, under the proved rational parameterization. t one half. -/
theorem endpoint_ratio_Rt (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    min (BookL1523.Rt t / 4) (5 / 8 * sqrt (BookL1523.Rt t)) ≤
      c0 (BookL1523.Rt t) / c1 (BookL1523.Rt t) := by
  have hq : 0 < 1 - t ^ 2 := by nlinarith
  have hu : 0 < 1 + t ^ 2 := by positivity
  have hR : 0 < BookL1523.Rt t := by unfold BookL1523.Rt; positivity
  let w := upsilon (BookL1523.Rt t)
  have hw0 : 0 < w := upsilon_pos _ hR
  have hw1 : w < 1 := upsilon_lt_one _ hR
  obtain ⟨hc0, hc1, hA⟩ := coefficients_Rt t h0 h1
  have hquad : ((1 + 3 * t ^ 2) / (t * (1 - t ^ 2))) * (1 - w ^ 2) = 2 * w := by
    have h := upsilon_quadratic (BookL1523.Rt t) hR
    rw [hA] at h
    exact h
  by_cases ht : t ≤ 9 / 16
  · apply (min_le_left _ _).trans
    apply (le_div_iff₀ (c1_pos _ hR)).mpr
    rw [hc0, hc1]
    change BookL1523.Rt t / 4 * (w * (1 - t ^ 2) / (t * (1 + t ^ 2))) ≤
      (w + t) / sqrt (1 + t ^ 2)
    have he : BookL1523.Rt t / 4 * (w * (1 - t ^ 2) / (t * (1 + t ^ 2))) = w / (1 - t ^ 2) := by
      unfold BookL1523.Rt
      field_simp
      <;> ring
    rw [he]
    exact (div_le_div_iff₀ hq (sqrt_pos.mpr hu)).mpr
      (param_endpoint_small t w h0 ht hw0 hw1 hquad)
  · apply (min_le_right _ _).trans
    have hpq : 0 < c0 (BookL1523.Rt t) / c1 (BookL1523.Rt t) :=
      div_pos (c0_pos _ hR) (c1_pos _ hR)
    have he : (c0 (BookL1523.Rt t) / c1 (BookL1523.Rt t)) ^ 2 =
        BookL1523.Rt t * t * (w + t) ^ 2 / (4 * w ^ 2) := by
      rw [hc0, hc1]
      change (((w + t) / sqrt (1 + t ^ 2)) / (w * (1 - t ^ 2) / (t * (1 + t ^ 2)))) ^ 2 = _
      simp only [div_pow, mul_pow, sq_sqrt hu.le]
      unfold BookL1523.Rt
      field_simp
      <;> ring
    have hh := param_endpoint_large t w (le_of_not_ge ht) h1 hw0 hw1 hquad
    have hs : (25 / 64 : ℝ) * BookL1523.Rt t ≤
        (c0 (BookL1523.Rt t) / c1 (BookL1523.Rt t)) ^ 2 := by
      rw [he]
      apply (le_div_iff₀ (show 0 < 4 * w ^ 2 by positivity)).mpr
      have h := mul_le_mul_of_nonneg_left hh hR.le
      nlinarith only [h]
    apply (sq_le_sq₀ (by positivity : 0 ≤ 5 / 8 * sqrt (BookL1523.Rt t)) hpq.le).mp
    calc
      _ = (25 / 64 : ℝ) * BookL1523.Rt t := by rw [mul_pow, sq_sqrt hR.le]; ring
      _ ≤ _ := hs

/-- Derived dimensionless radius bound for P0014 page 24, display 3.61. rho one. -/
theorem initial_ratio_le_sqrt (ρ : ℝ) (hρ : 0 < ρ) :
    (c0 ρ - 1 / sqrt 2) / c1 ρ ≤ sqrt ρ / 2 := by
  obtain ⟨t, ht, he⟩ := BookL1523.Rt_surj hρ
  rw [← he]
  have hρ : 0 < BookL1523.Rt t := by simpa only [he] using hρ
  have ht0 := ht.1
  have ht1 := ht.2
  have ha : 0 < sqrt (1 + t ^ 2) := sqrt_pos.2 (by positivity)
  have ha2 := sq_sqrt (show 0 ≤ 1 + t ^ 2 by positivity)
  have hb : 0 < sqrt (2 : ℝ) := by positivity
  have hb2 := sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hw := upsilon_pos _ hρ
  have hc := c1_pos _ hρ
  have hcoef := coefficients_Rt t ht0 ht1
  have hta : t / sqrt (1 + t ^ 2) ≤ 1 / sqrt 2 := by
    rw [div_le_div_iff₀ ha hb]
    have hs : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (sqrt (1 + t ^ 2) - t * sqrt 2)]
  have hD0 : 0 ≤ c0 (BookL1523.Rt t) - 1 / sqrt 2 := by
    have h := c0_ge_one _ hρ
    have hb1 : 1 ≤ sqrt (2:ℝ) := by nlinarith
    have hi : 1 / sqrt (2:ℝ) ≤ 1 := (div_le_one hb).2 hb1
    linarith
  have hD : c0 (BookL1523.Rt t) - 1 / sqrt 2 ≤ upsilon (BookL1523.Rt t) / sqrt (1 + t ^ 2) := by
    rw [hcoef.1, add_div]
    linarith
  have hid : BookL1523.Rt t * c1 (BookL1523.Rt t) ^ 2 * t =
      (2 * upsilon (BookL1523.Rt t) / sqrt (1 + t ^ 2)) ^ 2 := by
    rw [hcoef.2.1]
    unfold BookL1523.Rt
    have htq : 1 - t ^ 2 ≠ 0 := by nlinarith
    field_simp
    nlinarith [ha2]
  have hX : 0 ≤ BookL1523.Rt t * c1 (BookL1523.Rt t) ^ 2 := by positivity
  have hupper : (2 * upsilon (BookL1523.Rt t) / sqrt (1 + t ^ 2)) ^ 2 ≤
      BookL1523.Rt t * c1 (BookL1523.Rt t) ^ 2 := by nlinarith [mul_nonneg hX (le_of_lt (sub_pos.mpr ht1))]
  have hsq := mul_self_le_mul_self hD0 hD
  have hs := sq_sqrt hρ.le
  rw [div_le_div_iff₀ hc (by norm_num : (0:ℝ) < 2)]
  have hright : 0 ≤ sqrt (BookL1523.Rt t) * c1 (BookL1523.Rt t) := by positivity
  have hsq' : (2 * (c0 (BookL1523.Rt t) - 1 / sqrt 2)) ^ 2 ≤
      BookL1523.Rt t * c1 (BookL1523.Rt t) ^ 2 := by
    calc
      _ ≤ (2 * (upsilon (BookL1523.Rt t) / sqrt (1 + t ^ 2))) ^ 2 := by nlinarith only [hsq]
      _ = (2 * upsilon (BookL1523.Rt t) / sqrt (1 + t ^ 2)) ^ 2 := by ring
      _ ≤ _ := hupper
  have hsqright : (sqrt (BookL1523.Rt t) * c1 (BookL1523.Rt t)) ^ 2 =
      BookL1523.Rt t * c1 (BookL1523.Rt t) ^ 2 := by rw [mul_pow, hs]
  nlinarith only [hsq', hsqright, hright, hD0]

/-- P0014 page 24, display 3.61. delta minus one and tau 100. -/
theorem initialRadius_le_sqrt_height (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    initialRadius δ τ ≤ sqrt |τ| := by
  have h := initial_ratio_le_sqrt _ (rho_pos δ τ hδ hτ)
  have hm := mul_le_mul_of_nonneg_left h (ell_pos δ hδ).le
  have hs := ell_mul_sqrt_rho δ τ hδ
  unfold initialRadius
  nlinarith [show ell δ / c1 (rho δ τ) * (c0 (rho δ τ) - 1 / sqrt 2) =
    ell δ * ((c0 (rho δ τ) - 1 / sqrt 2) / c1 (rho δ τ)) by ring]

/-- P0014 page 24, display 3.63, in derivative form. delta minus one, s one half plus 100 i and z one. -/
theorem contour_power_derivative (δ : ℝ) (s z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (fun u : ℂ => u ^ s * Complex.exp (-u ^ 2 / 2 + 2 * π * Complex.I * δ * u))
      (s * contourKernel δ s z - contourKernel δ (s + 2) z +
        (2 * π * Complex.I * δ) * contourKernel δ (s + 1) z) z := by
  let c : ℂ := 2 * π * Complex.I * δ
  have hz0 := Complex.slitPlane_ne_zero hz
  have hp : HasDerivAt (fun u : ℂ => u ^ s) (s * z ^ (s - 1)) z :=
    (Complex.hasStrictDerivAt_cpow_const hz).hasDerivAt
  have he : HasDerivAt (fun u : ℂ => -u ^ 2 / 2 + c * u) (-z + c) z := by
    convert (((hasDerivAt_id z).pow 2).neg.div_const 2).add ((hasDerivAt_id z).const_mul c) using 1
    · funext u
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, id_eq]
    · simp only [id_eq]
      ring
  have h := hp.mul he.cexp
  have hp1 : z ^ (s + 1) = z ^ s * z := by
    simpa using Complex.cpow_add s 1 hz0
  convert h using 1 <;>
    simp only [contourKernel, show (s + 2) - 1 = s + 1 by ring,
      add_sub_cancel_right, hp1] <;> dsimp [c] <;> ring

/-- P0014 pages 24 to 25, display 3.63 and its integration by parts boundary. delta minus one, tau 100, s one half plus 100 i and endpoint one. -/
theorem finite_ray_recurrence (δ τ : ℝ) (s : ℂ) (a : ℝ) (hσ : 0 < s.re) (ha : 0 < a) :
    s * (∫ r : ℝ in Ioo 0 a, contourKernel δ s (r * rayDirection τ) * rayDirection τ) =
      contourKernel δ s (a * rayDirection τ) * (a * rayDirection τ) +
      (∫ r : ℝ in Ioo 0 a, contourKernel δ (s + 2) (r * rayDirection τ) * rayDirection τ) -
      (2 * π * Complex.I * δ) *
        (∫ r : ℝ in Ioo 0 a, contourKernel δ (s + 1) (r * rayDirection τ) * rayDirection τ) := by
  let w := rayDirection τ
  let c : ℂ := 2 * π * Complex.I * δ
  let A : ℂ → ℝ → ℂ := fun z r => contourKernel δ z (r * w) * w
  let Q : ℝ → ℂ := fun r => (r * w) ^ s * Complex.exp (-(r * w) ^ 2 / 2 + c * (r * w))
  have hw : 0 < w.re := by dsimp [w]; rw [rayDirection_re]; positivity
  have hγ : Continuous (fun r : ℝ => (r : ℂ) * w) := by fun_prop
  have hzpos : ∀ r : ℝ, 0 < r → 0 < ((r:ℂ) * w).re := by
    intro r hr
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using mul_pos hr hw
  have hA (z : ℂ) (hz : 0 < z.re) : IntegrableOn (A z) (Ioo 0 a) := ray_kernel_integrable δ τ z a hz ha
  have h0 := hA s hσ
  have h1 := hA (s + 1) (by simp; linarith)
  have h2 := hA (s + 2) (by simp; linarith)
  have hi : IntegrableOn (fun r => s * A s r - A (s + 2) r + c * A (s + 1) r) (Ioo 0 a) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using! ((h0.const_mul s).sub h2).add (h1.const_mul c)
  have hInt : IntervalIntegrable (fun r => s * A s r - A (s + 2) r + c * A (s + 1) r)
      volume 0 a := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le ha.le, integrableOn_Icc_iff_integrableOn_Ioo]
    exact hi
  have hQ : ContinuousOn Q (Icc 0 a) := by
    apply ContinuousOn.mul
    · intro r hr
      have hp : 0 ≤ ((r : ℂ) * w).re := by
        simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
          mul_nonneg hr.1 hw.le
      have hpow : ContinuousAt (fun z : ℂ => z ^ s) ((r : ℂ) * w) :=
        Complex.continuousAt_cpow_const_of_re_pos (Or.inl hp) hσ
      have hcomp : ContinuousAt (fun r : ℝ => ((r : ℂ) * w) ^ s) r := hpow.comp (f := fun r : ℝ => (r : ℂ) * w) (x := r) hγ.continuousAt
      exact hcomp.continuousWithinAt
    · exact (show Continuous (fun r : ℝ => Complex.exp (-(r * w) ^ 2 / 2 + c * (r * w))) by fun_prop).continuousOn
  have hD : ∀ r ∈ Ioo 0 a, HasDerivAt Q (s * A s r - A (s + 2) r + c * A (s + 1) r) r := by
    intro r hr
    have hγD : HasDerivAt (fun r : ℝ => (r:ℂ) * w) w r := by
      simpa using (hasDerivAt_id r).ofReal_comp.mul_const w
    have h := (contour_power_derivative δ s (r * w) (Or.inl (hzpos r hr.1))).comp r hγD
    convert h using 1
    · rfl
    · dsimp [A, c]
      ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.le hQ hD hInt
  have hs0 : s ≠ 0 := by intro hs; simp [hs] at hσ
  have hQ0 : Q 0 = 0 := by simp [Q, hs0]
  rw [hQ0, sub_zero, intervalIntegral.integral_of_le ha.le, integral_Ioc_eq_integral_Ioo] at hFTC
  have hadd : (∫ r in Ioo 0 a, s * A s r - A (s + 2) r + c * A (s + 1) r) =
      (∫ r in Ioo 0 a, s * A s r - A (s + 2) r) + (∫ r in Ioo 0 a, c * A (s + 1) r) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using integral_add ((h0.const_mul s).sub h2) (h1.const_mul c)
  have hsub : (∫ r in Ioo 0 a, s * A s r - A (s + 2) r) =
      (∫ r in Ioo 0 a, s * A s r) - (∫ r in Ioo 0 a, A (s + 2) r) := by
    simpa only [Pi.sub_apply] using integral_sub (h0.const_mul s) h2
  rw [hadd, hsub, integral_const_mul, integral_const_mul] at hFTC
  have hz0 : (a : ℂ) * w ≠ 0 := Complex.slitPlane_ne_zero (Or.inl (hzpos a ha))
  have hp : ((a : ℂ) * w) ^ (s - 1) * (a * w) = (a * w) ^ s := by
    simpa using (Complex.cpow_add (s - 1) 1 hz0).symm
  have hQa : Q a = contourKernel δ s (a * w) * (a * w) := by
    dsimp [Q, contourKernel, c]
    rw [show (a * w) ^ (s - 1) * Complex.exp (-(a * w) ^ 2 / 2 + 2 * π * Complex.I * δ * (a * w)) * (a * w) =
      ((a * w) ^ (s - 1) * (a * w)) * Complex.exp (-(a * w) ^ 2 / 2 + 2 * π * Complex.I * δ * (a * w)) by ring, hp]
  rw [hQa] at hFTC
  dsimp only [A, c, w] at hFTC
  linear_combination hFTC

/-- LEAF: P0014 Appendix A, page 68, display A.36.
This is the dimensionless real endpoint lower bound for the actual limacon.
The proof uses algebraic inequalities in the rational half angle parameter. -/
theorem endpoint_ratio (ρ : ℝ) (hρ : 0 < ρ) :
    min (ρ / 4) (5 / 8 * sqrt ρ) ≤ c0 ρ / c1 ρ := by
  obtain ⟨t, ht, he⟩ := BookL1523.Rt_surj hρ
  rw [← he]
  exact endpoint_ratio_Rt t ht.1 ht.2

/-- Endpoint scaling of A.36 in P0014 page 25 after display 3.64.
This scales the proved endpoint ratio. The scale algebra is exact. -/
theorem realEndpoint_lower (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    min (|τ| / (2 * π * |δ|)) (5 / 4 * sqrt |τ|) ≤ realEndpoint δ τ := by
  have h := mul_le_mul_of_nonneg_left (endpoint_ratio (rho δ τ) (rho_pos δ τ hδ hτ))
    (ell_pos δ hδ).le
  have ha : ell δ * (rho δ τ / 4) = |τ| / (2 * π * |δ|) := by
    unfold ell rho
    simp only [mul_pow]
    field_simp
    nlinarith [sq_abs δ]
  have hb : ell δ * (5 / 8 * sqrt (rho δ τ)) = 5 / 4 * sqrt |τ| := by
    nlinarith [ell_mul_sqrt_rho δ τ hδ]
  rw [mul_min_of_nonneg _ _ (ell_pos δ hδ).le, ha, hb] at h
  exact h

/-- LEAF: P0014 pages 18 and 24 to 25, the contour partition before display 3.59.
Cauchy deformation from the real ray to C1, the limacon C2 and the final real ray.
The primitive and the vanishing origin defect prove the shift for positive real part. -/
theorem contour_shift (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    gaussianMellin δ s = initialIntegral δ s + saddleIntegral δ s +
      (∫ x : ℝ in Ioi (realEndpoint δ s.im), (x : ℂ) ^ (s - 1) *
        ((exp (-x ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * x))) := by
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  exact contour_shift_positive_re δ s hσ0 hd (by linarith)

end LeanLab.HelfgottMajor.Decomp639Contour
