module

public import LeanLab.HelfgottMajor.ContourKernel669
public import LeanLab.HelfgottMajor.DQPhaseLowerBound

/-!
CITED WALL, session CLOUD-cited-saddle_segment_bound, 2026-11-20.
Target: `Decomp639Contour.saddle_segment_bound`, P0014 page 23, displays 3.56 and 3.57.

DECISION: FORMALIZE. The leaf is not a result cited from elsewhere: it is Helfgott's own
argument of Section 3.7, pages 18 to 23. Its only outside inputs are the rigorous numerical
bounds of Appendix A, displays A.2, A.14, A.29 and A.32. `DQ6Decisions.lean` already holds
the whole bound as the named hypothesis `SaddleSegmentBoundDQ6`. This file splits the proof
into six steps, each tied to a page and display, and assembles the exact sealed
statement from them with no further unproved step. Four steps are LEAF lemmas; the two radius
facts, displays 3.50 and 3.53, are PROVED. The Gaussian half line integral, the splitting
of the contour at the saddle radius, the power bounds of display 3.48 and every constant of
display 3.57 are PROVED below. The leaves were tested numerically, see
notes/burst-20261120/saddle_segment_bound.md.

Source: https://arxiv.org/abs/1305.2897, the copy papers/P0014.pdf.
Update, burst 2026-11-20b: all four LEAF lemmas are now PROVED, so the assembly
`saddle_segment_bound_of_leaves` has no unproved step. See notes/burst-20261120b/.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.DQSaddleSegmentBound
open Real MeasureTheory Set Decomp511a Decomp639Contour

/-- The saddle radius r0 = |u0,+| of P0014 page 17, display 3.32:
r0 = ell / sqrt 2 * sqrt (ups rho ^ 2 - ups rho). -/
noncomputable def saddleRadius (δ τ : ℝ) : ℝ :=
  ell δ / sqrt 2 * sqrt (BookE.ups (rho δ τ) ^ 2 - BookE.ups (rho δ τ))

/-- The curvature eta of P0014 page 21, display 3.46, with j rho = sqrt (1 + rho ^ 2) as in
display A.15 and Upsilon as in display 3.25. -/
noncomputable def eta (ρ : ℝ) : ℝ :=
  1 / 2 * sqrt (2 * sqrt (1 + ρ ^ 2) / (BookE.ups ρ ^ 2 - BookE.ups ρ)) *
      (1 + upsilon ρ ^ 2) - upsilon ρ ^ 2 / 2 + 1 / 2 - 1 / (2 * BookE.ups ρ) -
    ρ / (sqrt (1 + ρ ^ 2) + 1) * upsilon ρ

/-! ## The six steps: four LEAF lemmas and two proved radius facts -/

/-- P0014 page 21 and Appendix A, display A.2, in the weak form used here: Upsilon is at
least 1/2. From the tangent double angle relation of display 3.25, with the argument of the
arctan above 2. PROVED. -/
theorem upsilon_ge_half (ρ : ℝ) (hρ : 0 < ρ) : 1 / 2 ≤ upsilon ρ := by
  have hU := upsilon_pos ρ hρ
  have hU1 := upsilon_lt_one ρ hρ
  have hq := upsilon_quadratic ρ hρ
  have hv := ups_gt_one ρ hρ
  have hj : ρ ≤ sqrt (1 + ρ ^ 2) := le_sqrt_of_sq_le (by nlinarith)
  have hA : 2 ≤ 2 * BookE.ups ρ * (BookE.ups ρ + sqrt (1 + ρ ^ 2)) / ρ := by
    rw [le_div_iff₀ hρ]; nlinarith
  set A := 2 * BookE.ups ρ * (BookE.ups ρ + sqrt (1 + ρ ^ 2)) / ρ
  have h1 : 0 < 1 - upsilon ρ ^ 2 := by nlinarith
  nlinarith

/-- P0014 pages 20 and 21, displays 3.41 to 3.44: on the contour, s = y / r lies in
[0, 1 / sqrt 2], so the cubic and quartic rest R (nu) - R (sin theta0 / (c1 rho)) =
s (2 c1 rho nu0 - s) is nonnegative, since c1 rho nu0 = cos theta0 Upsilon is at least
1 / (2 sqrt 2). PROVED. -/
theorem rest_nonneg (ρ s : ℝ) (hρ : 0 < ρ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / sqrt 2) :
    0 ≤ s * (2 * sqrt (1 / 2 + 1 / (2 * BookE.ups ρ)) * upsilon ρ - s) := by
  have hv := ups_gt_one ρ hρ
  have hU := upsilon_ge_half ρ hρ
  have hC : 1 / sqrt 2 ≤ sqrt (1 / 2 + 1 / (2 * BookE.ups ρ)) := by
    rw [show (1 : ℝ) / sqrt 2 = sqrt (1 / 2) by rw [sqrt_div zero_le_one, sqrt_one]]
    apply sqrt_le_sqrt
    have : 0 < 1 / (2 * BookE.ups ρ) := by positivity
    linarith
  have h2 : 0 < 1 / sqrt 2 := by positivity
  apply mul_nonneg hs0
  nlinarith

/-- PROVED: P0014 pages 18 to 21, displays 3.37, 3.39, 3.42 to 3.46, and the value of
exp of minus Re phi at u0,+ after display 3.47. On the limacon C2 the kernel is at most
r ^ (sigma - 1) times exp of minus E rho times the height times the Gaussian factor
exp of minus eta times (r - r0) ^ 2, the form eta ell^2 rho^2 nu^2 with nu = (r - r0) / (ell rho)
of display 3.38. The phase lower bound of display 3.44 is the content.
Proved from the three lemmas of `DQPhaseLowerBound`, displays 3.37, page 20 and
3.42 to 3.46, with `rest_nonneg` for displays 3.41 to 3.44. -/
theorem phase_lower_bound (δ : ℝ) (s : ℂ) (hsign : δ * s.im < 0) (r : ℝ)
    (hr : r ∈ Icc (initialRadius δ s.im) (realEndpoint δ s.im)) :
    ‖contourKernel δ s (saddlePath δ s.im r)‖ ≤
      r ^ (s.re - 1) * exp (-BookE.E (rho δ s.im) * |s.im|) *
        exp (-eta (rho δ s.im) * (r - saddleRadius δ s.im) ^ 2) := by
  have hδ : δ ≠ 0 := by intro h; simp [h] at hsign
  have hτ : 0 < |s.im| := abs_pos.mpr (by intro h; simp [h] at hsign)
  have hρ := rho_pos δ s.im hδ hτ
  have hv := ups_gt_one (rho δ s.im) hρ
  have hnorm : ‖contourKernel δ s (saddlePath δ s.im r)‖ = r ^ (s.re - 1) *
      exp (-((r ^ 2 - 2 * ((-c1 (rho δ s.im) * r / ell δ + c0 (rho δ s.im)) * r) ^ 2) / 2 -
        ell δ * ((-c1 (rho δ s.im) * r / ell δ + c0 (rho δ s.im)) * r) +
        |s.im| * arcsin ((-c1 (rho δ s.im) * r / ell δ + c0 (rho δ s.im)) * r / r))) :=
    DQPhaseLowerBound.kernel_norm_saddlePath δ s hsign r hr
  have hid : (r ^ 2 - 2 * ((-c1 (rho δ s.im) * r / ell δ + c0 (rho δ s.im)) * r) ^ 2) / 2 -
      ell δ * ((-c1 (rho δ s.im) * r / ell δ + c0 (rho δ s.im)) * r) +
      |s.im| * (arcsin (sqrt (1 / 2 - 1 / (2 * BookE.ups (rho δ s.im)))) +
        ((-c1 (rho δ s.im) * r / ell δ + c0 (rho δ s.im)) -
          sqrt (1 / 2 - 1 / (2 * BookE.ups (rho δ s.im)))) /
          sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ s.im)))) =
      BookE.E (rho δ s.im) * |s.im| + eta (rho δ s.im) * (r - saddleRadius δ s.im) ^ 2 +
        (r - saddleRadius δ s.im) ^ 2 * ((-c1 (rho δ s.im) * r / ell δ + c0 (rho δ s.im)) *
          (2 * sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ s.im))) * upsilon (rho δ s.im) -
            (-c1 (rho δ s.im) * r / ell δ + c0 (rho δ s.im)))) :=
    DQPhaseLowerBound.phase_expansion_identity δ s.im r hδ hτ
  have hb := saddlePath_height_bounds δ s.im r hδ hτ hr
  simp only at hb
  obtain ⟨hr0, hy0, hy1⟩ := hb
  generalize -c1 (rho δ s.im) * r / ell δ + c0 (rho δ s.im) = w at hnorm hid hy0 hy1
  generalize hSdef : sqrt (1 / 2 - 1 / (2 * BookE.ups (rho δ s.im))) = S at hid
  generalize hCdef : sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ s.im))) = C at hid
  -- s = y / r lies in [0, 1 / sqrt 2]
  have hw0 : 0 ≤ w := by
    by_contra h; push Not at h; nlinarith
  have hs2 : (1 : ℝ) < sqrt 2 := by
    rw [show (1 : ℝ) = sqrt 1 by rw [sqrt_one]]; exact sqrt_lt_sqrt zero_le_one one_lt_two
  have hw1 : w ≤ 1 / sqrt 2 := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hy1
    nlinarith
  have hw1' : w < 1 := by
    have : 1 / sqrt 2 < 1 := by rw [div_lt_one (by positivity)]; exact hs2
    linarith
  have hyr : w * r / r = w := by field_simp
  rw [hyr] at hnorm
  -- the tangent bound for arcsin at S
  have hvi : 1 / (2 * BookE.ups (rho δ s.im)) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hvi0 : 0 < 1 / (2 * BookE.ups (rho δ s.im)) := by positivity
  have hS2 : S ^ 2 = 1 / 2 - 1 / (2 * BookE.ups (rho δ s.im)) := by
    rw [← hSdef]; exact sq_sqrt (by linarith)
  have hCS : sqrt (1 - S ^ 2) = C := by rw [hS2, ← hCdef]; congr 1; ring
  have hS0 : 0 ≤ S := by rw [← hSdef]; exact sqrt_nonneg _
  have hS1 : S < 1 := by nlinarith
  have htan := DQPhaseLowerBound.arcsin_tangent_le S w hS0 hS1 hw0 hw1'
  rw [hCS] at htan
  have hrest := rest_nonneg (rho δ s.im) w hρ hw0 hw1
  rw [hCdef] at hrest
  have h1 : 0 ≤ |s.im| * (arcsin w - (arcsin S + (w - S) / C)) :=
    mul_nonneg hτ.le (by linarith)
  have h2 : 0 ≤ (r - saddleRadius δ s.im) ^ 2 * (w * (2 * C * upsilon (rho δ s.im) - w)) :=
    mul_nonneg (sq_nonneg _) hrest
  rw [hnorm, mul_assoc, ← exp_add]
  apply mul_le_mul_of_nonneg_left _ (rpow_nonneg hr0.le _)
  apply exp_le_exp.mpr
  nlinarith

/-- Helper for `arc_length_bound`, P0014 page 22 after display 3.48: with k = c r at most c0,
y = (c0 - k) r and 2 y^2 at most r^2, the squared speed of the limacon, written as
x'^2 + y'^2 with x = sqrt (r^2 - y^2), equals 1 + k^2 r^2 / x^2 and is at most 1 + 2 c0^2.
PROVED. -/
theorem arcLength_speed_sq_le (r c0 c y x : ℝ) (hk0 : 0 ≤ c * r) (hk1 : c * r ≤ c0)
    (hy : y = (-c * r + c0) * r) (hyr : 2 * y ^ 2 ≤ r ^ 2) (hx : 0 < x) (hx2 : x ^ 2 = r ^ 2 - y ^ 2) :
    (2 * r - 2 * y * (-2 * c * r + c0)) ^ 2 / (2 * x) ^ 2 + (-2 * c * r + c0) ^ 2 ≤ 1 + 2 * c0 ^ 2 := by
  have hx2' : 0 < (2 * x) ^ 2 := by positivity
  rw [div_add' _ _ _ hx2'.ne', div_le_iff₀ hx2']
  have hid : (2 * r - 2 * y * (-2 * c * r + c0)) ^ 2 + (-2 * c * r + c0) ^ 2 * (2 * x) ^ 2 =
      4 * (x ^ 2 + (c * r) ^ 2 * r ^ 2) := by
    rw [mul_pow, hx2, hy]; ring
  rw [hid]
  have h1 : (c * r) ^ 2 ≤ c0 ^ 2 := pow_le_pow_left₀ hk0 hk1 2
  nlinarith [sq_nonneg r]

/-- LEAF: P0014 page 22, the arc length bound after display 3.48, from display 3.35 and the
choice theta minus = pi / 4 of display 3.55: |du/dr| is at most sqrt (1 + 2 c0 ^ 2). PROVED,
session CLOUD-burst20261120b-arc_length, through `arcLength_speed_sq_le`. -/
theorem arc_length_bound (δ τ r : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|)
    (hr : r ∈ Icc (initialRadius δ τ) (realEndpoint δ τ)) :
    ‖deriv (saddlePath δ τ) r‖ ≤ sqrt (1 + 2 * c0 (rho δ τ) ^ 2) := by
  set c := c1 (rho δ τ) / ell δ with hcdef
  set C0 := c0 (rho δ τ) with hC0
  have hb := saddlePath_height_bounds δ τ r hδ hτ hr
  set Y : ℝ → ℝ := fun t => (-c * t + C0) * t with hYdef
  have hYe : ∀ t, (-c1 (rho δ τ) * t / ell δ + c0 (rho δ τ)) * t = Y t := by
    intro t; simp only [hYdef, hcdef, hC0]; ring
  simp only [hYe] at hb
  obtain ⟨hrp, hy0, hyr⟩ := hb
  have hysq := pow_le_pow_left₀ hy0 hyr 2
  rw [div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hysq
  have hsub : 0 < r ^ 2 - Y r ^ 2 := by nlinarith
  have hpath : saddlePath δ τ = fun t => (sqrt (t ^ 2 - Y t ^ 2) : ℂ) +
      (if 0 ≤ τ then (Y t : ℂ) else -(Y t : ℂ)) * Complex.I := by
    funext t; unfold saddlePath; simp only [hYe]
  have hYd : HasDerivAt Y (-2 * c * r + C0) r := by
    have h1 : HasDerivAt (fun t : ℝ => -c * t + C0) (-c) r := by
      simpa using ((hasDerivAt_id' r).const_mul (-c)).add_const C0
    have := h1.mul (hasDerivAt_id' r)
    convert this using 1
    ring
  have hQd : HasDerivAt (fun t => t ^ 2 - Y t ^ 2)
      (2 * r - 2 * Y r * (-2 * c * r + C0)) r := by
    have := (hasDerivAt_pow 2 r).sub (hYd.pow 2)
    convert this using 1; push_cast; ring
  have hXd := (hQd.sqrt hsub.ne').ofReal_comp
  have hYc := hYd.ofReal_comp
  set X' := (2 * r - 2 * Y r * (-2 * c * r + C0)) / (2 * sqrt (r ^ 2 - Y r ^ 2))
  set Y' := -2 * c * r + C0
  have hD : HasDerivAt (saddlePath δ τ) ((X' : ℂ) +
      (if 0 ≤ τ then (Y' : ℂ) else -(Y' : ℂ)) * Complex.I) r := by
    rw [hpath]
    split_ifs
    · exact hXd.add (hYc.mul_const _)
    · exact hXd.add (hYc.neg.mul_const _)
  rw [hD.deriv, Complex.norm_def]
  apply sqrt_le_sqrt
  have hns : Complex.normSq ((X' : ℂ) +
      (if 0 ≤ τ then (Y' : ℂ) else -(Y' : ℂ)) * Complex.I) = X' ^ 2 + Y' ^ 2 := by
    split_ifs <;> simp [Complex.normSq_apply] <;> ring
  rw [hns]
  have hc1 := c1_pos _ (rho_pos δ τ hδ hτ)
  have hL := ell_pos δ hδ
  have hcpos : 0 ≤ c := by positivity
  have hk1 : c * r ≤ C0 := by
    have hx : c * realEndpoint δ τ = C0 := by
      simp only [hcdef, hC0]; unfold realEndpoint; field_simp
    rw [← hx]; exact mul_le_mul_of_nonneg_left hr.2 hcpos
  have hX2 : X' ^ 2 = (2 * r - 2 * Y r * Y') ^ 2 / (2 * sqrt (r ^ 2 - Y r ^ 2)) ^ 2 := by
    simp only [X', Y', div_pow]
  rw [hX2]
  exact arcLength_speed_sq_le r C0 c (Y r) _ (by positivity) hk1 rfl (by nlinarith)
    (sqrt_pos.mpr hsub) (sq_sqrt hsub.le)

/-- P0014 page 18, displays 3.33 and 3.34, with page 20: c1 r0 / ell equals
Upsilon cos theta0 = sqrt (1/2 + 1/(2 upsilon)) Upsilon. PROVED. -/
theorem c1_mul_radius (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    c1 (rho δ τ) * saddleRadius δ τ / ell δ =
      sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ τ))) * upsilon (rho δ τ) := by
  have hρ := rho_pos δ τ hδ hτ
  have hυ : 1 < BookE.ups (rho δ τ) := ups_gt_one _ hρ
  have hL := ell_pos δ hδ
  have hY : 0 < BookE.ups (rho δ τ) ^ 2 - BookE.ups (rho δ τ) := by nlinarith
  have hX : 0 ≤ 1 + 1 / BookE.ups (rho δ τ) := by positivity
  have hsY : sqrt (BookE.ups (rho δ τ) ^ 2 - BookE.ups (rho δ τ)) ≠ 0 :=
    (sqrt_pos.mpr hY).ne'
  have hs2 : sqrt 2 ≠ 0 := by positivity
  have hhalf : 1 / 2 + 1 / (2 * BookE.ups (rho δ τ)) = (1 + 1 / BookE.ups (rho δ τ)) / 2 := by
    ring
  unfold c1 saddleRadius
  rw [hhalf, sqrt_div hX, sqrt_div hX]
  field_simp
  exact mul_div_cancel_left₀ _
    (sqrt_pos.mpr (mul_pos (by linarith) (by linarith))).ne'

/-- P0014 pages 17 and 20, displays 3.31, 3.41 and 3.50: the saddle radius r0 lies
between the radius r minus of display 3.58 and the real endpoint c0 ell / c1, that is
alpha0 is at most 0 and 0 is at most alpha1. PROVED from display 3.34. -/
theorem saddleRadius_mem (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    initialRadius δ τ ≤ saddleRadius δ τ ∧ saddleRadius δ τ ≤ realEndpoint δ τ := by
  have hρ := rho_pos δ τ hδ hτ
  have hυ : 1 < BookE.ups (rho δ τ) := ups_gt_one _ hρ
  have hL := ell_pos δ hδ
  have hc1 := c1_pos _ hρ
  have hk := c1_mul_radius δ τ hδ hτ
  have hr0 : saddleRadius δ τ = ell δ / c1 (rho δ τ) *
      (sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ τ))) * upsilon (rho δ τ)) := by
    rw [← hk]; field_simp
  have hpos : 0 < ell δ / c1 (rho δ τ) := div_pos hL hc1
  have hsin : sqrt (1 / 2 - 1 / (2 * BookE.ups (rho δ τ))) ≤ 1 / sqrt 2 := by
    rw [show (1 : ℝ) / sqrt 2 = sqrt (1 / 2) by rw [sqrt_div zero_le_one, sqrt_one]]
    apply sqrt_le_sqrt
    have : 0 < 1 / (2 * BookE.ups (rho δ τ)) := by positivity
    linarith
  have hsin0 : 0 ≤ sqrt (1 / 2 - 1 / (2 * BookE.ups (rho δ τ))) := sqrt_nonneg _
  unfold initialRadius realEndpoint
  rw [hr0]
  unfold c0
  constructor
  · apply mul_le_mul_of_nonneg_left _ hpos.le
    linarith
  · rw [mul_div_assoc', div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hc1.le
    apply mul_le_mul_of_nonneg_left _ hL.le
    linarith

/-- P0014 page 23, display 3.53 with A.14: nu0 / (alpha0 + nu0) = r0 / r minus is
at most 7.83, the constant printed in display 3.57. PROVED from c0 at least 1 and
Upsilon below 1; the true ratio is at most 1 / (1 - 1 / sqrt 2), about 3.42. -/
theorem saddleRadius_le_initial (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    saddleRadius δ τ ≤ 7.83 * initialRadius δ τ := by
  have hρ := rho_pos δ τ hδ hτ
  have hυ : 1 < BookE.ups (rho δ τ) := ups_gt_one _ hρ
  have hL := ell_pos δ hδ
  have hc1 := c1_pos _ hρ
  have hk := c1_mul_radius δ τ hδ hτ
  have hr0 : saddleRadius δ τ = ell δ / c1 (rho δ τ) *
      (sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ τ))) * upsilon (rho δ τ)) := by
    rw [← hk]; field_simp
  have hpos : 0 < ell δ / c1 (rho δ τ) := div_pos hL hc1
  have hcos : sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ τ))) ≤ 1 := by
    rw [show (1 : ℝ) = sqrt 1 by rw [sqrt_one]]
    apply sqrt_le_sqrt
    have : 1 / (2 * BookE.ups (rho δ τ)) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hU0 := (upsilon_pos _ hρ).le
  have hU1 := (upsilon_lt_one _ hρ).le
  have hk1 : sqrt (1 / 2 + 1 / (2 * BookE.ups (rho δ τ))) * upsilon (rho δ τ) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul hcos hU1 hU0 zero_le_one
      _ = 1 := one_mul 1
  have hc0 := c0_ge_one _ hρ
  have hs2 : (1.414 : ℝ) ≤ sqrt 2 := by
    rw [show (1.414 : ℝ) = sqrt (1.414 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num)
  have hinv : 1 / sqrt 2 ≤ 0.7073 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  unfold initialRadius
  rw [hr0, show 7.83 * (ell δ / c1 (rho δ τ) * (c0 (rho δ τ) - 1 / sqrt 2)) =
    ell δ / c1 (rho δ τ) * (7.83 * (c0 (rho δ τ) - 1 / sqrt 2)) by ring]
  apply mul_le_mul_of_nonneg_left _ hpos.le
  linarith

/-! ### Helpers for `eta_bound`, P0014 Appendix A displays A.24 to A.29. AI wrote this code. -/

/-- Bernstein certificate on [0.0, 0.1] for the polynomial of `eta_small_alg`. PROVED. -/
theorem etaNum_nonneg_0 (t : ℝ) (ha : (0:ℝ) ≤ t) (hb : t ≤ (1/10:ℝ)) :
    0 ≤ (22:ℝ) + (-258:ℝ) * t^1 + (1243:ℝ) * t^2 + (-4541:ℝ) * t^3 + (14883:ℝ) * t^4 + (-27264:ℝ) * t^5 + (71660:ℝ) * t^6 + (-61179:ℝ) * t^7 + (160213:ℝ) * t^8 + (-19230:ℝ) * t^9 + (180404:ℝ) * t^10 + (66785:ℝ) * t^11 + (111993:ℝ) * t^12 + (53524:ℝ) * t^13 + (-7720:ℝ) * t^14 + (6995:ℝ) * t^15 + (-31963:ℝ) * t^16 + (-13172:ℝ) * t^17 + (-16211:ℝ) * t^18 + (-1660:ℝ) * t^19 + (-172:ℝ) * t^20 := by
  have h1 : 0 ≤ t - (0:ℝ) := by linarith
  have h2 : 0 ≤ (1/10:ℝ) - t := by linarith
  have f0 : 0 ≤ (t - (0:ℝ)) ^ 0 * ((1/10:ℝ) - t) ^ 20 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f1 : 0 ≤ (t - (0:ℝ)) ^ 1 * ((1/10:ℝ) - t) ^ 19 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f2 : 0 ≤ (t - (0:ℝ)) ^ 2 * ((1/10:ℝ) - t) ^ 18 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f3 : 0 ≤ (t - (0:ℝ)) ^ 3 * ((1/10:ℝ) - t) ^ 17 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f4 : 0 ≤ (t - (0:ℝ)) ^ 4 * ((1/10:ℝ) - t) ^ 16 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f5 : 0 ≤ (t - (0:ℝ)) ^ 5 * ((1/10:ℝ) - t) ^ 15 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f6 : 0 ≤ (t - (0:ℝ)) ^ 6 * ((1/10:ℝ) - t) ^ 14 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f7 : 0 ≤ (t - (0:ℝ)) ^ 7 * ((1/10:ℝ) - t) ^ 13 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f8 : 0 ≤ (t - (0:ℝ)) ^ 8 * ((1/10:ℝ) - t) ^ 12 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f9 : 0 ≤ (t - (0:ℝ)) ^ 9 * ((1/10:ℝ) - t) ^ 11 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f10 : 0 ≤ (t - (0:ℝ)) ^ 10 * ((1/10:ℝ) - t) ^ 10 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f11 : 0 ≤ (t - (0:ℝ)) ^ 11 * ((1/10:ℝ) - t) ^ 9 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f12 : 0 ≤ (t - (0:ℝ)) ^ 12 * ((1/10:ℝ) - t) ^ 8 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f13 : 0 ≤ (t - (0:ℝ)) ^ 13 * ((1/10:ℝ) - t) ^ 7 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f14 : 0 ≤ (t - (0:ℝ)) ^ 14 * ((1/10:ℝ) - t) ^ 6 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f15 : 0 ≤ (t - (0:ℝ)) ^ 15 * ((1/10:ℝ) - t) ^ 5 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f16 : 0 ≤ (t - (0:ℝ)) ^ 16 * ((1/10:ℝ) - t) ^ 4 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f17 : 0 ≤ (t - (0:ℝ)) ^ 17 * ((1/10:ℝ) - t) ^ 3 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f18 : 0 ≤ (t - (0:ℝ)) ^ 18 * ((1/10:ℝ) - t) ^ 2 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f19 : 0 ≤ (t - (0:ℝ)) ^ 19 * ((1/10:ℝ) - t) ^ 1 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f20 : 0 ≤ (t - (0:ℝ)) ^ 20 * ((1/10:ℝ) - t) ^ 0 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  linear_combination (2200000000000000000000:ℝ) * f0 + (41420000000000000000000:ℝ) * f1 + (370223000000000000000000:ℝ) * f2 + (2088739900000000000000000:ℝ) * f3 + (8341588130000000000000000:ℝ) * f4 + (25063604416000000000000000:ℝ) * f5 + (58784009806000000000000000:ℝ) * f6 + (110193287792210000000000000:ℝ) * f7 + (167657150992943000000000000:ℝ) * f8 + (209063167105013000000000000:ℝ) * f9 + (214804782796769040000000000:ℝ) * f10 + (182152351941352185000000000:ℝ) * f11 + (127245272454204064300000000:ℝ) * f12 + (72819696913445189640000000:ℝ) * f13 + (33802541919521659360000000:ℝ) * f14 + (12530514270211345219500000:ℝ) * f15 + (3622212035060881777870000:ℝ) * f16 + (786888284365485503308000:ℝ) * f17 + (120853218583769676082900:ℝ) * f18 + (11700910867761936205200:ℝ) * f19 + (537180382552185060128:ℝ) * f20

/-- Bernstein certificate on [0.1, 0.2] for the polynomial of `eta_small_alg`. PROVED. -/
theorem etaNum_nonneg_1 (t : ℝ) (ha : (1/10:ℝ) ≤ t) (hb : t ≤ (1/5:ℝ)) :
    0 ≤ (22:ℝ) + (-258:ℝ) * t^1 + (1243:ℝ) * t^2 + (-4541:ℝ) * t^3 + (14883:ℝ) * t^4 + (-27264:ℝ) * t^5 + (71660:ℝ) * t^6 + (-61179:ℝ) * t^7 + (160213:ℝ) * t^8 + (-19230:ℝ) * t^9 + (180404:ℝ) * t^10 + (66785:ℝ) * t^11 + (111993:ℝ) * t^12 + (53524:ℝ) * t^13 + (-7720:ℝ) * t^14 + (6995:ℝ) * t^15 + (-31963:ℝ) * t^16 + (-13172:ℝ) * t^17 + (-16211:ℝ) * t^18 + (-1660:ℝ) * t^19 + (-172:ℝ) * t^20 := by
  have h1 : 0 ≤ t - (1/10:ℝ) := by linarith
  have h2 : 0 ≤ (1/5:ℝ) - t := by linarith
  have f0 : 0 ≤ (t - (1/10:ℝ)) ^ 0 * ((1/5:ℝ) - t) ^ 20 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f1 : 0 ≤ (t - (1/10:ℝ)) ^ 1 * ((1/5:ℝ) - t) ^ 19 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f2 : 0 ≤ (t - (1/10:ℝ)) ^ 2 * ((1/5:ℝ) - t) ^ 18 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f3 : 0 ≤ (t - (1/10:ℝ)) ^ 3 * ((1/5:ℝ) - t) ^ 17 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f4 : 0 ≤ (t - (1/10:ℝ)) ^ 4 * ((1/5:ℝ) - t) ^ 16 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f5 : 0 ≤ (t - (1/10:ℝ)) ^ 5 * ((1/5:ℝ) - t) ^ 15 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f6 : 0 ≤ (t - (1/10:ℝ)) ^ 6 * ((1/5:ℝ) - t) ^ 14 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f7 : 0 ≤ (t - (1/10:ℝ)) ^ 7 * ((1/5:ℝ) - t) ^ 13 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f8 : 0 ≤ (t - (1/10:ℝ)) ^ 8 * ((1/5:ℝ) - t) ^ 12 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f9 : 0 ≤ (t - (1/10:ℝ)) ^ 9 * ((1/5:ℝ) - t) ^ 11 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f10 : 0 ≤ (t - (1/10:ℝ)) ^ 10 * ((1/5:ℝ) - t) ^ 10 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f11 : 0 ≤ (t - (1/10:ℝ)) ^ 11 * ((1/5:ℝ) - t) ^ 9 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f12 : 0 ≤ (t - (1/10:ℝ)) ^ 12 * ((1/5:ℝ) - t) ^ 8 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f13 : 0 ≤ (t - (1/10:ℝ)) ^ 13 * ((1/5:ℝ) - t) ^ 7 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f14 : 0 ≤ (t - (1/10:ℝ)) ^ 14 * ((1/5:ℝ) - t) ^ 6 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f15 : 0 ≤ (t - (1/10:ℝ)) ^ 15 * ((1/5:ℝ) - t) ^ 5 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f16 : 0 ≤ (t - (1/10:ℝ)) ^ 16 * ((1/5:ℝ) - t) ^ 4 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f17 : 0 ≤ (t - (1/10:ℝ)) ^ 17 * ((1/5:ℝ) - t) ^ 3 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f18 : 0 ≤ (t - (1/10:ℝ)) ^ 18 * ((1/5:ℝ) - t) ^ 2 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f19 : 0 ≤ (t - (1/10:ℝ)) ^ 19 * ((1/5:ℝ) - t) ^ 1 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f20 : 0 ≤ (t - (1/10:ℝ)) ^ 20 * ((1/5:ℝ) - t) ^ 0 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  linear_combination (537180382552185060128:ℝ) * f0 + (9786304434325466199920:ℝ) * f1 + (84475696348476745982580:ℝ) * f2 + (459489639976986219686960:ℝ) * f3 + (1766942348456272826544960:ℝ) * f4 + (5109395531487437151460384:ℝ) * f5 + (11539219479033692521686720:ℝ) * f6 + (20872892396624179420708480:ℝ) * f7 + (30777281652893570898562560:ℝ) * f8 + (37464072402590160145704960:ℝ) * f9 + (37992118612757508739858432:ℝ) * f10 + (32295126947995145483427840:ℝ) * f11 + (23082448598489572318248960:ℝ) * f12 + (13860506822741642593566720:ℝ) * f13 + (6949368029151675653816320:ℝ) * f14 + (2869650870579680395657216:ℝ) * f15 + (952612974423213248348160:ℝ) * f16 + (244356520638275009904640:ℝ) * f17 + (45374726170217419898880:ℝ) * f18 + (5412272113908690452480:ℝ) * f19 + (310411074988018761728:ℝ) * f20

/-- Bernstein certificate on [0.2, 0.3] for the polynomial of `eta_small_alg`. PROVED. -/
theorem etaNum_nonneg_2 (t : ℝ) (ha : (1/5:ℝ) ≤ t) (hb : t ≤ (3/10:ℝ)) :
    0 ≤ (22:ℝ) + (-258:ℝ) * t^1 + (1243:ℝ) * t^2 + (-4541:ℝ) * t^3 + (14883:ℝ) * t^4 + (-27264:ℝ) * t^5 + (71660:ℝ) * t^6 + (-61179:ℝ) * t^7 + (160213:ℝ) * t^8 + (-19230:ℝ) * t^9 + (180404:ℝ) * t^10 + (66785:ℝ) * t^11 + (111993:ℝ) * t^12 + (53524:ℝ) * t^13 + (-7720:ℝ) * t^14 + (6995:ℝ) * t^15 + (-31963:ℝ) * t^16 + (-13172:ℝ) * t^17 + (-16211:ℝ) * t^18 + (-1660:ℝ) * t^19 + (-172:ℝ) * t^20 := by
  have h1 : 0 ≤ t - (1/5:ℝ) := by linarith
  have h2 : 0 ≤ (3/10:ℝ) - t := by linarith
  have f0 : 0 ≤ (t - (1/5:ℝ)) ^ 0 * ((3/10:ℝ) - t) ^ 20 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f1 : 0 ≤ (t - (1/5:ℝ)) ^ 1 * ((3/10:ℝ) - t) ^ 19 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f2 : 0 ≤ (t - (1/5:ℝ)) ^ 2 * ((3/10:ℝ) - t) ^ 18 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f3 : 0 ≤ (t - (1/5:ℝ)) ^ 3 * ((3/10:ℝ) - t) ^ 17 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f4 : 0 ≤ (t - (1/5:ℝ)) ^ 4 * ((3/10:ℝ) - t) ^ 16 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f5 : 0 ≤ (t - (1/5:ℝ)) ^ 5 * ((3/10:ℝ) - t) ^ 15 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f6 : 0 ≤ (t - (1/5:ℝ)) ^ 6 * ((3/10:ℝ) - t) ^ 14 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f7 : 0 ≤ (t - (1/5:ℝ)) ^ 7 * ((3/10:ℝ) - t) ^ 13 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f8 : 0 ≤ (t - (1/5:ℝ)) ^ 8 * ((3/10:ℝ) - t) ^ 12 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f9 : 0 ≤ (t - (1/5:ℝ)) ^ 9 * ((3/10:ℝ) - t) ^ 11 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f10 : 0 ≤ (t - (1/5:ℝ)) ^ 10 * ((3/10:ℝ) - t) ^ 10 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f11 : 0 ≤ (t - (1/5:ℝ)) ^ 11 * ((3/10:ℝ) - t) ^ 9 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f12 : 0 ≤ (t - (1/5:ℝ)) ^ 12 * ((3/10:ℝ) - t) ^ 8 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f13 : 0 ≤ (t - (1/5:ℝ)) ^ 13 * ((3/10:ℝ) - t) ^ 7 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f14 : 0 ≤ (t - (1/5:ℝ)) ^ 14 * ((3/10:ℝ) - t) ^ 6 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f15 : 0 ≤ (t - (1/5:ℝ)) ^ 15 * ((3/10:ℝ) - t) ^ 5 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f16 : 0 ≤ (t - (1/5:ℝ)) ^ 16 * ((3/10:ℝ) - t) ^ 4 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f17 : 0 ≤ (t - (1/5:ℝ)) ^ 17 * ((3/10:ℝ) - t) ^ 3 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f18 : 0 ≤ (t - (1/5:ℝ)) ^ 18 * ((3/10:ℝ) - t) ^ 2 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f19 : 0 ≤ (t - (1/5:ℝ)) ^ 19 * ((3/10:ℝ) - t) ^ 1 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f20 : 0 ≤ (t - (1/5:ℝ)) ^ 20 * ((3/10:ℝ) - t) ^ 0 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  linear_combination (310411074988018761728:ℝ) * f0 + (7004170885612060016640:ℝ) * f1 + (75620802832581441617920:ℝ) * f2 + (518088499466738943918080:ℝ) * f3 + (2520956794945969911234560:ℝ) * f4 + (9246387918415280380837888:ℝ) * f5 + (26494515217843225846087680:ℝ) * f6 + (60682602886651528707440640:ℝ) * f7 + (112768819811166401187676160:ℝ) * f8 + (171646683853440079098961920:ℝ) * f9 + (215118049234693758245715968:ℝ) * f10 + (222343201312090115957790720:ℝ) * f11 + (189189737971269007978216960:ℝ) * f12 + (131805532493998647809581440:ℝ) * f13 + (74454258834077764649196480:ℝ) * f14 + (33578519538129768273867488:ℝ) * f15 + (11808255113548682610184960:ℝ) * f16 + (3120849956960377424054480:ℝ) * f17 + (583231900863768029716820:ℝ) * f18 + (68726296269529566187040:ℝ) * f19 + (3840833991530304246928:ℝ) * f20

/-- Bernstein certificate on [0.3, 0.55] for the polynomial of `eta_small_alg`. PROVED. -/
theorem etaNum_nonneg_3 (t : ℝ) (ha : (3/10:ℝ) ≤ t) (hb : t ≤ (11/20:ℝ)) :
    0 ≤ (22:ℝ) + (-258:ℝ) * t^1 + (1243:ℝ) * t^2 + (-4541:ℝ) * t^3 + (14883:ℝ) * t^4 + (-27264:ℝ) * t^5 + (71660:ℝ) * t^6 + (-61179:ℝ) * t^7 + (160213:ℝ) * t^8 + (-19230:ℝ) * t^9 + (180404:ℝ) * t^10 + (66785:ℝ) * t^11 + (111993:ℝ) * t^12 + (53524:ℝ) * t^13 + (-7720:ℝ) * t^14 + (6995:ℝ) * t^15 + (-31963:ℝ) * t^16 + (-13172:ℝ) * t^17 + (-16211:ℝ) * t^18 + (-1660:ℝ) * t^19 + (-172:ℝ) * t^20 := by
  have h1 : 0 ≤ t - (3/10:ℝ) := by linarith
  have h2 : 0 ≤ (11/20:ℝ) - t := by linarith
  have f0 : 0 ≤ (t - (3/10:ℝ)) ^ 0 * ((11/20:ℝ) - t) ^ 20 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f1 : 0 ≤ (t - (3/10:ℝ)) ^ 1 * ((11/20:ℝ) - t) ^ 19 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f2 : 0 ≤ (t - (3/10:ℝ)) ^ 2 * ((11/20:ℝ) - t) ^ 18 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f3 : 0 ≤ (t - (3/10:ℝ)) ^ 3 * ((11/20:ℝ) - t) ^ 17 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f4 : 0 ≤ (t - (3/10:ℝ)) ^ 4 * ((11/20:ℝ) - t) ^ 16 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f5 : 0 ≤ (t - (3/10:ℝ)) ^ 5 * ((11/20:ℝ) - t) ^ 15 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f6 : 0 ≤ (t - (3/10:ℝ)) ^ 6 * ((11/20:ℝ) - t) ^ 14 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f7 : 0 ≤ (t - (3/10:ℝ)) ^ 7 * ((11/20:ℝ) - t) ^ 13 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f8 : 0 ≤ (t - (3/10:ℝ)) ^ 8 * ((11/20:ℝ) - t) ^ 12 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f9 : 0 ≤ (t - (3/10:ℝ)) ^ 9 * ((11/20:ℝ) - t) ^ 11 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f10 : 0 ≤ (t - (3/10:ℝ)) ^ 10 * ((11/20:ℝ) - t) ^ 10 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f11 : 0 ≤ (t - (3/10:ℝ)) ^ 11 * ((11/20:ℝ) - t) ^ 9 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f12 : 0 ≤ (t - (3/10:ℝ)) ^ 12 * ((11/20:ℝ) - t) ^ 8 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f13 : 0 ≤ (t - (3/10:ℝ)) ^ 13 * ((11/20:ℝ) - t) ^ 7 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f14 : 0 ≤ (t - (3/10:ℝ)) ^ 14 * ((11/20:ℝ) - t) ^ 6 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f15 : 0 ≤ (t - (3/10:ℝ)) ^ 15 * ((11/20:ℝ) - t) ^ 5 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f16 : 0 ≤ (t - (3/10:ℝ)) ^ 16 * ((11/20:ℝ) - t) ^ 4 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f17 : 0 ≤ (t - (3/10:ℝ)) ^ 17 * ((11/20:ℝ) - t) ^ 3 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f18 : 0 ≤ (t - (3/10:ℝ)) ^ 18 * ((11/20:ℝ) - t) ^ 2 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f19 : 0 ≤ (t - (3/10:ℝ)) ^ 19 * ((11/20:ℝ) - t) ^ 1 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  have f20 : 0 ≤ (t - (3/10:ℝ)) ^ 20 * ((11/20:ℝ) - t) ^ 0 := mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)
  linear_combination (4027406343502880306026774528/95367431640625:ℝ) * f0 + (20351316390481207087304015872/19073486328125:ℝ) * f1 + (243058604166567520760683823104/19073486328125:ℝ) * f2 + (1825281625477886950216007942144/19073486328125:ℝ) * f3 + (9670718766497279523497315663872/19073486328125:ℝ) * f4 + (192214883624803299318445256998912/95367431640625:ℝ) * f5 + (119019211212463450018614717710336/19073486328125:ℝ) * f6 + (293985409961277112969662910431232/19073486328125:ℝ) * f7 + (588607336164617798731348450803712/19073486328125:ℝ) * f8 + (964962477234015090415606278455296/19073486328125:ℝ) * f9 + (6513790969135392796394731686125568/95367431640625:ℝ) * f10 + (1451264300874678003658625508089856/19073486328125:ℝ) * f11 + (1331938010765767191034582711703552/19073486328125:ℝ) * f12 + (1001800864318767218953651222843392/19073486328125:ℝ) * f13 + (611559964844573111862084836043776/19073486328125:ℝ) * f14 + (1491920632768481125020958585792512/95367431640625:ℝ) * f15 + (113640808567114623323706977211392/19073486328125:ℝ) * f16 + (32562686260524666882864893479424/19073486328125:ℝ) * f17 + (6604448851665144582530678247824/19073486328125:ℝ) * f18 + (845458907131680129188510486352/19073486328125:ℝ) * f19 + (256883458532981510049210383828/95367431640625:ℝ) * f20

/-- The polynomial of `eta_small_alg` is nonnegative on [0, 0.55]. PROVED. -/
theorem etaNum_nonneg (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 0.55) :
    0 ≤ (22:ℝ) + (-258:ℝ) * t^1 + (1243:ℝ) * t^2 + (-4541:ℝ) * t^3 + (14883:ℝ) * t^4 + (-27264:ℝ) * t^5 + (71660:ℝ) * t^6 + (-61179:ℝ) * t^7 + (160213:ℝ) * t^8 + (-19230:ℝ) * t^9 + (180404:ℝ) * t^10 + (66785:ℝ) * t^11 + (111993:ℝ) * t^12 + (53524:ℝ) * t^13 + (-7720:ℝ) * t^14 + (6995:ℝ) * t^15 + (-31963:ℝ) * t^16 + (-13172:ℝ) * t^17 + (-16211:ℝ) * t^18 + (-1660:ℝ) * t^19 + (-172:ℝ) * t^20 := by
  rcases le_total t 0.1 with ha | ha
  · exact etaNum_nonneg_0 t (by linarith) (by linarith)
  rcases le_total t 0.2 with hb | hb
  · exact etaNum_nonneg_1 t (by linarith) (by linarith)
  rcases le_total t 0.3 with hc | hc
  · exact etaNum_nonneg_2 t (by linarith) (by linarith)
  · exact etaNum_nonneg_3 t (by linarith) (by linarith)

/-- The rational identity behind `eta_small_alg`. PROVED. -/
theorem etaNum_eq (t B u Rl : ℝ) (ht0 : 0 < t) (hB : B = t * (1 - t ^ 2) / (1 + 3 * t ^ 2))
    (hu : u = 1 - B + B ^ 2 / 2)
    (hRl : Rl = 2 * (1 + 2 * t ^ 2) * (1 + 6 * t ^ 2 + t ^ 4) /
      (1 + 6 * t ^ 2 + t ^ 4 + (1 + 2 * t ^ 2) ^ 2 * (1 + t ^ 2))) :
    43 / 25 * (1 + t ^ 2) * (Rl * (1 + t ^ 2) * (2 - 2 * B * u) - t * (1 + t ^ 2) *
        (1 - 2 * B * u) + 2 * t ^ 3 - 4 * t ^ 2 * u) -
        (1 + 3 * t ^ 2 + 2 * (1 - 2 * B * u) + 4 * t * u) * (1 - t ^ 2) ^ 2 =
      ((22:ℝ) + (-258:ℝ) * t^1 + (1243:ℝ) * t^2 + (-4541:ℝ) * t^3 + (14883:ℝ) * t^4 + (-27264:ℝ) * t^5 + (71660:ℝ) * t^6 + (-61179:ℝ) * t^7 + (160213:ℝ) * t^8 + (-19230:ℝ) * t^9 + (180404:ℝ) * t^10 + (66785:ℝ) * t^11 + (111993:ℝ) * t^12 + (53524:ℝ) * t^13 + (-7720:ℝ) * t^14 + (6995:ℝ) * t^15 + (-31963:ℝ) * t^16 + (-13172:ℝ) * t^17 + (-16211:ℝ) * t^18 + (-1660:ℝ) * t^19 + (-172:ℝ) * t^20) / (25 * (3 * t ^ 2 + 1) ^ 3 * (4 * t ^ 6 + 9 * t ^ 4 + 11 * t ^ 2 + 2)) := by
  subst hu hRl
  subst hB
  have h3 : (1 + 3 * t ^ 2) ≠ 0 := by positivity
  have h4 : (1 + 6 * t ^ 2 + t ^ 4 + (1 + 2 * t ^ 2) ^ 2 * (1 + t ^ 2)) ≠ 0 := by positivity
  have hD : (25 * (3 * t ^ 2 + 1) ^ 3 * (4 * t ^ 6 + 9 * t ^ 4 + 11 * t ^ 2 + 2)) ≠ 0 := by positivity
  rw [eq_div_iff hD]
  field_simp
  ring

set_option maxHeartbeats 4000000 in
/-- The polynomial inequality behind the bound 0.86 rho of A.29 for small rho, in the
parameter t = tan (theta0 / 2): with R = t sqrt (2 j / (upsilon^2 - upsilon)) and U = Upsilon,
0.86 rho eta minus (1 + 2 c0^2), times (1 + t^2) (1 - t^2)^2, is nonnegative. PROVED. -/
theorem eta_small_alg (t R U : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 0.55) (hR0 : 0 < R)
    (hR2 : R ^ 2 * (1 + t ^ 2) = 1 + 6 * t ^ 2 + t ^ 4) (hU0 : 0 < U)
    (hUc : (1 + 3 * t ^ 2) * (1 - U ^ 2) = 2 * t * (1 - t ^ 2) * U) :
    0 ≤ 43 / 25 * (1 + t ^ 2) * (R * (1 + t ^ 2) * (1 + U ^ 2) - t * (1 + t ^ 2) * U ^ 2 +
      2 * t ^ 3 - 4 * t ^ 2 * U) - (1 + 3 * t ^ 2 + 2 * U ^ 2 + 4 * t * U) * (1 - t ^ 2) ^ 2 := by
  have ht1' : t < 1 := by linarith
  have h3 : 0 < 1 + 3 * t ^ 2 := by positivity
  set B := t * (1 - t ^ 2) / (1 + 3 * t ^ 2) with hBdef
  have hB : B * (1 + 3 * t ^ 2) = t * (1 - t ^ 2) := by rw [hBdef]; field_simp
  have hB0 : 0 ≤ B := by
    rw [hBdef]; apply div_nonneg _ h3.le; apply mul_nonneg ht0.le; nlinarith
  have hBt : B ≤ t := by
    refine le_of_mul_le_mul_right ?_ h3
    rw [hB]; nlinarith [pow_pos ht0 3]
  have hU2 : U ^ 2 = 1 - 2 * B * U := by
    refine mul_left_cancel₀ h3.ne' ?_
    linear_combination (-1 : ℝ) * hUc + 2 * U * hB
  set u := 1 - B + B ^ 2 / 2 with hudef
  have hu0 : 0 < u := by
    have : u = ((1 - B) ^ 2 + 1) / 2 := by rw [hudef]; ring
    rw [this]; positivity
  have hu1 : u ≤ 1 := by
    have : 0 ≤ B * (1 - B / 2) := mul_nonneg hB0 (by linarith)
    rw [hudef]; linarith
  have hUu : U ≤ u := by
    have hid : (U - u) * (U + u + 2 * B) = -(B ^ 4 / 4) := by
      rw [hudef]; linear_combination hU2
    have hpos : 0 < U + u + 2 * B := by linarith
    by_contra hc
    push Not at hc
    have : 0 < (U - u) * (U + u + 2 * B) := mul_pos (by linarith) hpos
    nlinarith [pow_nonneg hB0 4]
  have hden : 0 < 1 + 6 * t ^ 2 + t ^ 4 + (1 + 2 * t ^ 2) ^ 2 * (1 + t ^ 2) := by positivity
  set Rl := 2 * (1 + 2 * t ^ 2) * (1 + 6 * t ^ 2 + t ^ 4) /
      (1 + 6 * t ^ 2 + t ^ 4 + (1 + 2 * t ^ 2) ^ 2 * (1 + t ^ 2)) with hRldef
  have hRl : Rl ≤ R := by
    rw [hRldef, div_le_iff₀ hden]
    have : R * (1 + 6 * t ^ 2 + t ^ 4 + (1 + 2 * t ^ 2) ^ 2 * (1 + t ^ 2)) -
        2 * (1 + 2 * t ^ 2) * (1 + 6 * t ^ 2 + t ^ 4) =
        (1 + t ^ 2) * (R * (R - (1 + 2 * t ^ 2)) ^ 2) := by
      rw [← hR2]; ring
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 1 + t ^ 2)
      (mul_nonneg hR0.le (sq_nonneg (R - (1 + 2 * t ^ 2))))]
  -- the form linear in U after U^2 = 1 - 2 B U
  have hlin : 43 / 25 * (1 + t ^ 2) * (R * (1 + t ^ 2) * (1 + U ^ 2) - t * (1 + t ^ 2) * U ^ 2 +
      2 * t ^ 3 - 4 * t ^ 2 * U) - (1 + 3 * t ^ 2 + 2 * U ^ 2 + 4 * t * U) * (1 - t ^ 2) ^ 2 =
      43 / 25 * (1 + t ^ 2) * (R * (1 + t ^ 2) * (2 - 2 * B * U) - t * (1 + t ^ 2) *
        (1 - 2 * B * U) + 2 * t ^ 3 - 4 * t ^ 2 * U) -
        (1 + 3 * t ^ 2 + 2 * (1 - 2 * B * U) + 4 * t * U) * (1 - t ^ 2) ^ 2 := by
    rw [hU2]; ring
  have hsplit : 43 / 25 * (1 + t ^ 2) * (R * (1 + t ^ 2) * (2 - 2 * B * U) - t * (1 + t ^ 2) *
        (1 - 2 * B * U) + 2 * t ^ 3 - 4 * t ^ 2 * U) -
        (1 + 3 * t ^ 2 + 2 * (1 - 2 * B * U) + 4 * t * U) * (1 - t ^ 2) ^ 2 =
      (43 / 25 * (1 + t ^ 2) * (Rl * (1 + t ^ 2) * (2 - 2 * B * u) - t * (1 + t ^ 2) *
        (1 - 2 * B * u) + 2 * t ^ 3 - 4 * t ^ 2 * u) -
        (1 + 3 * t ^ 2 + 2 * (1 - 2 * B * u) + 4 * t * u) * (1 - t ^ 2) ^ 2) +
      (U - u) * (43 / 25 * (1 + t ^ 2) * (-2 * R * (1 + t ^ 2) * B + 2 * t * (1 + t ^ 2) * B -
        4 * t ^ 2) - (-4 * B + 4 * t) * (1 - t ^ 2) ^ 2) +
      (R - Rl) * (43 / 25 * (1 + t ^ 2) * ((1 + t ^ 2) * (2 - 2 * B * u))) := by
    ring
  rw [hlin, hsplit]
  have hbeta : 43 / 25 * (1 + t ^ 2) * (-2 * R * (1 + t ^ 2) * B + 2 * t * (1 + t ^ 2) * B -
        4 * t ^ 2) - (-4 * B + 4 * t) * (1 - t ^ 2) ^ 2 ≤ 0 := by
    have e1 : 0 ≤ R * (1 + t ^ 2) * B := by positivity
    have e2 : (1 + t ^ 2) * B ≤ 2 * t := by nlinarith
    have e3 : 0 ≤ (t - B) * (1 - t ^ 2) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have e4 : 0 ≤ t * (2 * t - (1 + t ^ 2) * B) := mul_nonneg ht0.le (by linarith)
    nlinarith
  have hgamma : 0 ≤ 43 / 25 * (1 + t ^ 2) * ((1 + t ^ 2) * (2 - 2 * B * u)) := by
    have hBu : B * u ≤ t * 1 := mul_le_mul hBt hu1 hu0.le ht0.le
    have h2 : 0 ≤ 2 - 2 * B * u := by linarith
    have h1 : (0:ℝ) ≤ 1 + t ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (by norm_num) h1) (mul_nonneg h1 h2)
  have hmain : 0 ≤ 43 / 25 * (1 + t ^ 2) * (Rl * (1 + t ^ 2) * (2 - 2 * B * u) - t * (1 + t ^ 2) *
        (1 - 2 * B * u) + 2 * t ^ 3 - 4 * t ^ 2 * u) -
        (1 + 3 * t ^ 2 + 2 * (1 - 2 * B * u) + 4 * t * u) * (1 - t ^ 2) ^ 2 := by
    have hD : 0 < 25 * (3 * t ^ 2 + 1) ^ 3 * (4 * t ^ 6 + 9 * t ^ 4 + 11 * t ^ 2 + 2) := by positivity
    have hN := etaNum_nonneg t ht0.le ht1
    have heq := etaNum_eq t B u Rl ht0 hBdef hudef hRldef
    rw [heq]
    exact div_nonneg hN hD.le
  have k1 := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hUu) hbeta
  have k2 := mul_nonneg (sub_nonneg.mpr hRl) hgamma
  linarith

/-- P0014 Appendix A, page 65, display A.24 in the weak form eta at least 1, for all rho > 0,
with v = upsilon, j = j rho and Q = sqrt (2 j / (v^2 - v)) as in display 3.46. The proof
completes the square in U = Upsilon instead of the bisection of the paper: the discriminant
condition reduces to the polynomial w (w + 1) (w^4 + w^3 - 5 w^2 - 3 w + 8) at least 0
with w = 1 / v. PROVED. -/
theorem eta_ge_one_vars (ρ v j U Q : ℝ) (hv1 : 1 < v) (hj0 : 0 ≤ j)
    (hj2 : j ^ 2 = 1 + ρ ^ 2) (hv2 : v ^ 2 = (1 + j) / 2) (hQ0 : 0 ≤ Q)
    (hQ2 : Q ^ 2 = 2 * j / (v ^ 2 - v)) :
    1 ≤ 1 / 2 * Q * (1 + U ^ 2) - U ^ 2 / 2 + 1 / 2 - 1 / (2 * v) - ρ / (j + 1) * U := by
  have hv0 : 0 < v := by linarith
  have hj : j = 2 * v ^ 2 - 1 := by linarith
  have hvv : 0 < v ^ 2 - v := by nlinarith
  obtain ⟨w, hwdef⟩ : ∃ w, w = 1 / v := ⟨_, rfl⟩
  have hw : w * v = 1 := by rw [hwdef]; field_simp
  have hw0 : 0 < w := by rw [hwdef]; positivity
  have hw1 : w < 1 := by rw [hwdef, div_lt_one hv0]; exact hv1
  have hQv : Q ^ 2 * (v ^ 2 - v) = 2 * j := by
    rw [hQ2]; field_simp; exact mul_div_cancel_right₀ _ (by linarith)
  have hQw : Q ^ 2 * (1 - w) = 2 * (2 - w ^ 2) := by
    have e : Q ^ 2 * (1 - w) = Q ^ 2 * (v ^ 2 - v) * w ^ 2 := by
      rw [hwdef]; field_simp
    rw [e, hQv, hj, hwdef]; field_simp
  have hρ2 : ρ ^ 2 = 4 * v ^ 4 - 4 * v ^ 2 := by
    linear_combination (-1 : ℝ) * hj2 + (j + 2 * v ^ 2 - 1) * hj
  obtain ⟨m, hmdef⟩ : ∃ m, m = ρ / (j + 1) := ⟨_, rfl⟩
  have hm2 : m ^ 2 = 1 - w ^ 2 := by
    rw [hmdef, div_pow, hρ2, show j + 1 = 2 * v ^ 2 by rw [hj]; ring, hwdef]
    field_simp; ring
  have h1w : 0 < 1 - w := by linarith
  have hsq : ((2 + w) * Q) ^ 2 ≤ (Q ^ 2 + w + w ^ 2) ^ 2 := by
    refine le_of_mul_le_mul_right ?_ (pow_pos h1w 2)
    have e1 : ((2 + w) * Q) ^ 2 * (1 - w) ^ 2 = (2 + w) ^ 2 * (1 - w) * (Q ^ 2 * (1 - w)) := by
      ring
    have e2 : (Q ^ 2 + w + w ^ 2) ^ 2 * (1 - w) ^ 2 =
        (Q ^ 2 * (1 - w) + (w + w ^ 2) * (1 - w)) ^ 2 := by ring
    rw [e1, e2, hQw]
    have hp : 0 ≤ w * (w + 1) * (w ^ 4 + w ^ 3 + (1 - w) * (8 + 5 * w)) := by
      apply mul_nonneg (mul_nonneg hw0.le (by linarith))
      have := mul_nonneg h1w.le (by linarith : (0:ℝ) ≤ 8 + 5 * w)
      positivity
    nlinarith [hp]
  have hkey : (2 + w) * Q ≤ Q ^ 2 + w + w ^ 2 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have hQ4 : 4 ≤ Q ^ 2 := by nlinarith
  have hQ1 : 0 < Q - 1 := by nlinarith
  have hdisc : m ^ 2 ≤ (Q - 1) * (Q - 1 - w) := by nlinarith
  have hexpr : 2 * (1 / 2 * Q * (1 + U ^ 2) - U ^ 2 / 2 + 1 / 2 - 1 / (2 * v) - ρ / (j + 1) * U) - 2 =
      (Q - 1) * U ^ 2 - 2 * m * U + (Q - 1 - w) := by
    rw [← hmdef, show 1 / (2 * v) = w / 2 by rw [hwdef]; ring]; ring
  have hprod : 0 ≤ (Q - 1) * ((Q - 1) * U ^ 2 - 2 * m * U + (Q - 1 - w)) := by
    nlinarith [sq_nonneg ((Q - 1) * U - m)]
  have := (mul_nonneg_iff_of_pos_left hQ1).mp hprod
  linarith

/-- P0014 Appendix A, page 65, display A.26: c0 = Upsilon cos theta0 + sin theta0 is at most
sqrt 2, in squared form. PROVED. -/
theorem c0_sq_le_two_vars (a b U : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1)
    (hU0 : 0 < U) (hU1 : U < 1) : (a * U + b) ^ 2 ≤ 2 := by
  have h1 : a * U + b ≤ a + b := by nlinarith [mul_le_mul_of_nonneg_left hU1.le ha]
  have h2 : 0 ≤ a * U + b := by positivity
  have h3 : (a * U + b) ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ h2 h1 2
  nlinarith [sq_nonneg (a - b)]

set_option maxHeartbeats 4000000 in
/-- P0014 Appendix A, page 66, the bound (1 + 2 c0^2) / eta at most 0.86 rho for rho
below 5 / 0.86, which the paper checks by bisection. Here it is reduced through the
parameter t = tan (theta0 / 2) = sqrt ((v - 1) / (v + 1)) to `eta_small_alg`. PROVED. -/
theorem eta_small_vars (ρ v j U Q a b : ℝ) (hρ : 0 < ρ) (hv1 : 1 < v)
    (hj2 : j ^ 2 = 1 + ρ ^ 2) (hv2 : v ^ 2 = (1 + j) / 2) (hQ0 : 0 ≤ Q)
    (hQ2 : Q ^ 2 = 2 * j / (v ^ 2 - v)) (hU0 : 0 < U)
    (hUq : 2 * v * (v + j) / ρ * (1 - U ^ 2) = 2 * U)
    (ha0 : 0 ≤ a) (ha2 : a ^ 2 = 1 / 2 + 1 / (2 * v))
    (hb0 : 0 ≤ b) (hb2 : b ^ 2 = 1 / 2 - 1 / (2 * v)) (hρ6 : 0.86 * ρ < 5) :
    1 + 2 * (a * U + b) ^ 2 ≤
      0.86 * ρ * (1 / 2 * Q * (1 + U ^ 2) - U ^ 2 / 2 + 1 / 2 - 1 / (2 * v) - ρ / (j + 1) * U) := by
  have hv0 : 0 < v := by linarith
  have hj : j = 2 * v ^ 2 - 1 := by linarith
  have hvv : 0 < v ^ 2 - v := by nlinarith
  obtain ⟨t, htdef⟩ : ∃ t, t = sqrt ((v - 1) / (v + 1)) := ⟨_, rfl⟩
  have ht2 : t ^ 2 = (v - 1) / (v + 1) := by
    rw [htdef, sq_sqrt (div_nonneg (by linarith) (by linarith))]
  have ht0 : 0 < t := by rw [htdef]; exact sqrt_pos.mpr (div_pos (by linarith) (by linarith))
  have htv : t ^ 2 * (v + 1) = v - 1 := by rw [ht2]; field_simp
  have ht1 : t < 1 := by
    have h : t ^ 2 < 1 := by rw [ht2, div_lt_one (by linarith)]; linarith
    nlinarith
  have hD : 0 < 1 - t ^ 2 := by nlinarith
  have hvt : v = (1 + t ^ 2) / (1 - t ^ 2) := by
    rw [eq_div_iff hD.ne']; linarith
  have hρ2 : ρ ^ 2 = 4 * v ^ 4 - 4 * v ^ 2 := by
    linear_combination (-1 : ℝ) * hj2 + (j + 2 * v ^ 2 - 1) * hj
  have hρt : ρ = 4 * t * (1 + t ^ 2) / (1 - t ^ 2) ^ 2 := by
    refine (pow_left_inj₀ hρ.le (by positivity) two_ne_zero).mp ?_
    rw [hρ2, hvt]; field_simp; ring
  have e2 : ρ / (j + 1) = 2 * t / (1 + t ^ 2) := by
    rw [show j + 1 = 2 * v ^ 2 by rw [hj]; ring, hρt, hvt]; field_simp; ring
  have e1 : 1 / (2 * v) = (1 - t ^ 2) / (2 * (1 + t ^ 2)) := by
    rw [hvt]; field_simp
  have hQv : Q ^ 2 * (v ^ 2 - v) = 2 * j := by
    rw [hQ2]; field_simp; exact mul_div_cancel_right₀ _ (by linarith)
  have evv : v ^ 2 - v = 2 * t ^ 2 * (1 + t ^ 2) / (1 - t ^ 2) ^ 2 := by
    rw [hvt]; field_simp; ring
  have ejj : 2 * j = 2 * (1 + 6 * t ^ 2 + t ^ 4) / (1 - t ^ 2) ^ 2 := by
    rw [hj, hvt]; field_simp; ring
  rw [evv, ejj] at hQv
  have hQt : Q ^ 2 * t ^ 2 * (1 + t ^ 2) = 1 + 6 * t ^ 2 + t ^ 4 := by
    field_simp at hQv; linarith
  obtain ⟨R, hRdef⟩ : ∃ R, R = Q * t := ⟨_, rfl⟩
  have hR2 : R ^ 2 * (1 + t ^ 2) = 1 + 6 * t ^ 2 + t ^ 4 := by rw [hRdef]; linarith
  have hQpos : 0 < Q := by
    rcases hQ0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hQt; nlinarith
  have hR0 : 0 < R := by rw [hRdef]; positivity
  have eQ : Q = R / t := by rw [hRdef]; field_simp
  have hA : 2 * v * (v + j) / ρ = (1 + 3 * t ^ 2) / (t * (1 - t ^ 2)) := by
    rw [hj, hρt, hvt]; field_simp; ring
  rw [hA] at hUq
  have hUc : (1 + 3 * t ^ 2) * (1 - U ^ 2) = 2 * t * (1 - t ^ 2) * U := by
    field_simp at hUq; linarith
  have ha2' : a ^ 2 = 1 / (1 + t ^ 2) := by rw [ha2, hvt]; field_simp; ring
  have hb2' : b ^ 2 = t ^ 2 / (1 + t ^ 2) := by rw [hb2, hvt]; field_simp; ring
  have hab : a * b = t / (1 + t ^ 2) := by
    refine (pow_left_inj₀ (mul_nonneg ha0 hb0) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, ha2', hb2']; field_simp
  have hc : (a * U + b) ^ 2 = (U ^ 2 + 2 * t * U + t ^ 2) / (1 + t ^ 2) := by
    rw [show (a * U + b) ^ 2 = a ^ 2 * U ^ 2 + 2 * (a * b) * U + b ^ 2 by ring, ha2', hb2', hab]
    field_simp
  have ht55 : t ≤ 0.55 := by
    by_contra h
    push Not at h
    have h1 : 0.3025 < t ^ 2 := by
      have := mul_lt_mul'' h h (by norm_num) (by norm_num)
      rw [sq]; norm_num at this ⊢; linarith
    have hq : (1 - t ^ 2) ^ 2 ≤ 0.48651 := by
      have := pow_le_pow_left₀ hD.le (by linarith : 1 - t ^ 2 ≤ 0.6975) 2
      norm_num at this ⊢; linarith
    have hp : 2.8655 ≤ 4 * t * (1 + t ^ 2) := by
      have := mul_le_mul (by linarith : (4 * 0.55 : ℝ) ≤ 4 * t)
        (by linarith : (1.3025 : ℝ) ≤ 1 + t ^ 2) (by norm_num) (by positivity)
      norm_num at this ⊢; linarith
    have hρe : ρ * (1 - t ^ 2) ^ 2 = 4 * t * (1 + t ^ 2) := by
      rw [hρt]; field_simp
    have h5 : 0.86 * ρ * (1 - t ^ 2) ^ 2 ≤ 5 * 0.48651 := by
      calc 0.86 * ρ * (1 - t ^ 2) ^ 2 ≤ 5 * (1 - t ^ 2) ^ 2 :=
            mul_le_mul_of_nonneg_right hρ6.le (by positivity)
        _ ≤ 5 * 0.48651 := by linarith
    linarith
  have key := eta_small_alg t R U ht0 ht55 hR0 hR2 hU0 hUc
  rw [e2, e1, hc, eQ, hρt, show (0.86 : ℝ) = 43 / 50 by norm_num, ← sub_nonneg]
  have hfin : 43 / 50 * (4 * t * (1 + t ^ 2) / (1 - t ^ 2) ^ 2) *
      (1 / 2 * (R / t) * (1 + U ^ 2) - U ^ 2 / 2 + 1 / 2 - (1 - t ^ 2) / (2 * (1 + t ^ 2)) -
        2 * t / (1 + t ^ 2) * U) - (1 + 2 * ((U ^ 2 + 2 * t * U + t ^ 2) / (1 + t ^ 2))) =
      (43 / 25 * (1 + t ^ 2) * (R * (1 + t ^ 2) * (1 + U ^ 2) - t * (1 + t ^ 2) * U ^ 2 +
        2 * t ^ 3 - 4 * t ^ 2 * U) - (1 + 3 * t ^ 2 + 2 * U ^ 2 + 4 * t * U) * (1 - t ^ 2) ^ 2) /
        ((1 + t ^ 2) * (1 - t ^ 2) ^ 2) := by
    field_simp; ring
  rw [hfin]
  exact div_nonneg key (by positivity)

/-- P0014 page 23, the bound after display 3.55, by A.29: eta is positive and
(1 + 2 c0 ^ 2) / eta is at most min 5 (0.86 rho). Appendix A, page 66, display A.29.
PROVED, formerly a LEAF: the 5 from eta at least 1 and c0 at most sqrt 2 as in A.28, and
0.86 rho from `eta_small_vars` in place of the bisection of the paper. -/
theorem eta_bound (ρ : ℝ) (hρ : 0 < ρ) :
    0 < eta ρ ∧ (1 + 2 * c0 ρ ^ 2) / eta ρ ≤ min 5 (0.86 * ρ) := by
  have hv1 : 1 < BookE.ups ρ := ups_gt_one ρ hρ
  have hv0 : 0 < BookE.ups ρ := by linarith
  have hj0 : 0 ≤ sqrt (1 + ρ ^ 2) := sqrt_nonneg _
  have hj2 : sqrt (1 + ρ ^ 2) ^ 2 = 1 + ρ ^ 2 := sq_sqrt (by positivity)
  have hv2 : BookE.ups ρ ^ 2 = (1 + sqrt (1 + ρ ^ 2)) / 2 := by
    unfold BookE.ups; rw [sq_sqrt (by positivity)]
  have hvv : 0 < BookE.ups ρ ^ 2 - BookE.ups ρ := by nlinarith
  have hQ0 := sqrt_nonneg (2 * sqrt (1 + ρ ^ 2) / (BookE.ups ρ ^ 2 - BookE.ups ρ))
  have hQ2 : sqrt (2 * sqrt (1 + ρ ^ 2) / (BookE.ups ρ ^ 2 - BookE.ups ρ)) ^ 2 =
      2 * sqrt (1 + ρ ^ 2) / (BookE.ups ρ ^ 2 - BookE.ups ρ) :=
    sq_sqrt (div_nonneg (by positivity) hvv.le)
  have hU0 := upsilon_pos ρ hρ
  have hU1 := upsilon_lt_one ρ hρ
  have hUq := upsilon_quadratic ρ hρ
  have hi : 1 / (2 * BookE.ups ρ) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have ha2 : sqrt (1 / 2 + 1 / (2 * BookE.ups ρ)) ^ 2 = 1 / 2 + 1 / (2 * BookE.ups ρ) :=
    sq_sqrt (by positivity)
  have hb2 : sqrt (1 / 2 - 1 / (2 * BookE.ups ρ)) ^ 2 = 1 / 2 - 1 / (2 * BookE.ups ρ) :=
    sq_sqrt (by linarith)
  have hη1 : 1 ≤ eta ρ :=
    eta_ge_one_vars ρ (BookE.ups ρ) (sqrt (1 + ρ ^ 2)) (upsilon ρ) _ hv1 hj0 hj2 hv2 hQ0 hQ2
  have hη : 0 < eta ρ := by linarith
  have hc0 : c0 ρ ^ 2 ≤ 2 :=
    c0_sq_le_two_vars _ _ _ (sqrt_nonneg _) (sqrt_nonneg _) (by rw [ha2, hb2]; ring) hU0 hU1
  have h5 : (1 + 2 * c0 ρ ^ 2) / eta ρ ≤ 5 := by
    rw [div_le_iff₀ hη]; linarith
  refine ⟨hη, le_min h5 ?_⟩
  by_cases hs : 0.86 * ρ < 5
  · rw [div_le_iff₀ hη]
    exact eta_small_vars ρ (BookE.ups ρ) (sqrt (1 + ρ ^ 2)) (upsilon ρ) _ _ _ hρ hv1 hj2 hv2
      hQ0 hQ2 hU0 hUq (sqrt_nonneg _) ha2 (sqrt_nonneg _) hb2 hs
  · push Not at hs
    linarith

/-- P0014 page 23, A.32 in the form needed for the radius bound: with upsilon = ups rho,
rho ^ 2 = 4 upsilon ^ 2 (upsilon ^ 2 - 1) by display 3.25, and then
min (rho ^ 2 / 18) (2 rho / 9) is at most upsilon ^ 2 - upsilon, split at rho = 4. PROVED. -/
theorem ups_sq_sub_ups_lower (ρ : ℝ) (hρ : 0 < ρ) :
    (ρ ≤ 4 → ρ ^ 2 / 18 ≤ BookE.ups ρ ^ 2 - BookE.ups ρ) ∧
      (4 ≤ ρ → 2 * ρ / 9 ≤ BookE.ups ρ ^ 2 - BookE.ups ρ) := by
  have hu1 : 1 < BookE.ups ρ := ups_gt_one _ hρ
  set u := BookE.ups ρ with hu
  set j := sqrt (1 + ρ ^ 2) with hj
  have hj0 : 0 ≤ j := sqrt_nonneg _
  have hj2 : j ^ 2 = 1 + ρ ^ 2 := sq_sqrt (by positivity)
  have hu2 : u ^ 2 = (1 + j) / 2 := by
    rw [hu, BookE.ups, sq_sqrt (by positivity)]
  have hρ2 : ρ ^ 2 = 4 * u ^ 2 * (u ^ 2 - 1) := by
    have : j = 2 * u ^ 2 - 1 := by linarith
    rw [this] at hj2; nlinarith
  constructor
  · intro h4
    have hsq : ρ ^ 2 ≤ 16 := by nlinarith
    have hu2b : u ^ 2 ≤ 2.57 := by nlinarith
    have hub : u ≤ 1.61 := by nlinarith
    have key : 2 * u * (u + 1) ≤ 9 := by nlinarith
    rw [hρ2]
    have hpos : 0 ≤ u * (u - 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left key hpos]
  · intro h4
    have hsq : 16 ≤ ρ ^ 2 := by nlinarith
    have hu15 : 1.5 ≤ u := by
      by_contra hc
      push Not at hc
      have : u ^ 2 < 2.25 := by nlinarith
      nlinarith
    have hA : 0 ≤ u ^ 2 - u := by nlinarith
    have hsq2 : (2 * ρ / 9) ^ 2 ≤ (u ^ 2 - u) ^ 2 := by
      have e1 : (2 * ρ / 9) ^ 2 = 16 * u ^ 2 * (u ^ 2 - 1) / 81 := by
        rw [div_pow, mul_pow, hρ2]; ring
      have e2 : (u ^ 2 - u) ^ 2 = u ^ 2 * (u - 1) ^ 2 := by ring
      rw [e1, e2]
      have h16 : 16 * (u ^ 2 - 1) ≤ 81 * (u - 1) ^ 2 := by nlinarith
      have hu0 : 0 ≤ u ^ 2 := sq_nonneg u
      nlinarith [mul_le_mul_of_nonneg_left h16 hu0]
    exact (pow_le_pow_iff_left₀ (by positivity) hA (by norm_num)).mp hsq2

/-- LEAF: P0014 page 23, the bound on r0 from A.32 and display 3.32:
r0 is at least 2/3 times min (tau / ell) (sqrt tau). -/
theorem saddleRadius_lower (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    2 / 3 * min (|τ| / ell δ) (sqrt |τ|) ≤ saddleRadius δ τ := by
  have hρ := rho_pos δ τ hδ hτ
  have hυ : 1 < BookE.ups (rho δ τ) := ups_gt_one _ hρ
  have hL := ell_pos δ hδ
  obtain ⟨hA, hB⟩ := ups_sq_sub_ups_lower (rho δ τ) hρ
  set ρ := rho δ τ with hρdef
  set L := ell δ with hLdef
  set Y := BookE.ups ρ ^ 2 - BookE.ups ρ with hY
  set m := min (|τ| / L) (sqrt |τ|) with hm
  have hY0 : 0 < Y := by nlinarith
  have hpd : (π * δ) ^ 2 ≠ 0 := by positivity
  have hτρ : |τ| = ρ * L ^ 2 / 4 := by
    rw [hρdef, hLdef, rho, ell, mul_pow, mul_pow, sq_abs]
    field_simp
    ring
  have hm0 : 0 ≤ m := le_min (by positivity) (sqrt_nonneg _)
  have hr0sq : saddleRadius δ τ ^ 2 = L ^ 2 / 2 * Y := by
    rw [saddleRadius, ← hLdef, ← hρdef, ← hY, mul_pow, div_pow, sq_sqrt hY0.le,
      sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hr0 : 0 ≤ saddleRadius δ τ := by
    rw [saddleRadius]; positivity
  have hsq : (2 / 3 * m) ^ 2 ≤ saddleRadius δ τ ^ 2 := by
    rw [hr0sq]
    rcases le_total ρ 4 with h4 | h4
    · have hm1 : m ≤ |τ| / L := min_le_left _ _
      have hm1' : m ≤ ρ * L / 4 := by
        rw [hτρ] at hm1; rw [show ρ * L / 4 = ρ * L ^ 2 / 4 / L by field_simp]; exact hm1
      have hmsq : m ^ 2 ≤ (ρ * L / 4) ^ 2 := pow_le_pow_left₀ hm0 hm1' 2
      have := hA h4
      have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
      nlinarith [mul_le_mul_of_nonneg_left this hL2]
    · have hm1 : m ≤ sqrt |τ| := min_le_right _ _
      have hmsq : m ^ 2 ≤ |τ| := by
        calc m ^ 2 ≤ sqrt |τ| ^ 2 := pow_le_pow_left₀ hm0 hm1 2
          _ = |τ| := sq_sqrt (abs_nonneg τ)
      have := hB h4
      have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
      rw [hτρ] at hmsq
      nlinarith [mul_le_mul_of_nonneg_left this hL2]
  exact (pow_le_pow_iff_left₀ (by positivity) hr0 (by norm_num)).mp hsq

/-! ## Proved steps -/

/-- P0014 page 22 before display 3.49: the Gaussian over a half line,
the integral of exp of minus eta x ^ 2 over 0 to w is at most sqrt pi / (2 sqrt eta). PROVED. -/
theorem gaussian_initial_le (η w : ℝ) (hη : 0 < η) (hw : 0 ≤ w) :
    ∫ x in (0 : ℝ)..w, exp (-η * x ^ 2) ≤ sqrt π / (2 * sqrt η) := by
  rw [intervalIntegral.integral_of_le hw]
  have hint : IntegrableOn (fun x : ℝ => exp (-η * x ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hη).integrableOn
  have hle : ∫ x in Ioc 0 w, exp (-η * x ^ 2) ≤ ∫ x in Ioi (0 : ℝ), exp (-η * x ^ 2) :=
    setIntegral_mono_set hint
      (Filter.Eventually.of_forall (fun x => (exp_pos _).le))
      (Filter.Eventually.of_forall (fun x hx => hx.1))
  rw [integral_gaussian_Ioi, sqrt_div pi_pos.le] at hle
  calc _ ≤ _ := hle
    _ = sqrt π / (2 * sqrt η) := by ring

/-- The right half of the split in display 3.49. PROVED. -/
theorem gaussian_right_le (η c v : ℝ) (hη : 0 < η) (hcv : c ≤ v) :
    ∫ r in c..v, exp (-η * (r - c) ^ 2) ≤ sqrt π / (2 * sqrt η) := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => exp (-η * x ^ 2)) c, sub_self]
  exact gaussian_initial_le η _ hη (by linarith)

/-- The left half of the split in display 3.49. PROVED. -/
theorem gaussian_left_le (η c u : ℝ) (hη : 0 < η) (huc : u ≤ c) :
    ∫ r in u..c, exp (-η * (r - c) ^ 2) ≤ sqrt π / (2 * sqrt η) := by
  have h : ∀ r : ℝ, exp (-η * (r - c) ^ 2) = exp (-η * (c - r) ^ 2) := by
    intro r; congr 2; ring
  simp_rw [h]
  rw [intervalIntegral.integral_comp_sub_left (fun x => exp (-η * x ^ 2)) c, sub_self]
  exact gaussian_initial_le η _ hη (by linarith)

/-- P0014 page 22, display 3.49 bounds: one half of the contour with a constant times the
Gaussian majorant. PROVED. -/
theorem piece_bound (f : ℝ → ℂ) (K η c u v : ℝ) (hη : 0 < η) (hK : 0 ≤ K) (huv : u ≤ v)
    (hside : v = c ∨ u = c)
    (hpt : ∀ r ∈ Icc u v, ‖f r‖ ≤ K * exp (-η * (r - c) ^ 2)) :
    ‖∫ r in u..v, f r‖ ≤ K * (sqrt π / (2 * sqrt η)) := by
  have hg : IntervalIntegrable (fun r => K * exp (-η * (r - c) ^ 2)) volume u v :=
    (by fun_prop : Continuous fun r : ℝ => K * exp (-η * (r - c) ^ 2)).intervalIntegrable _ _
  have h1 := intervalIntegral.norm_integral_le_of_norm_le huv
    (Filter.Eventually.of_forall (fun r hr => hpt r (Ioc_subset_Icc_self hr))) hg
  rw [intervalIntegral.integral_const_mul] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hK)
  rcases hside with h | h
  · subst h; exact gaussian_left_le η v u hη huv
  · subst h; exact gaussian_right_le η u v hη huv

/-- The constant of display 3.57: sqrt pi / 2 times sqrt (min 5 (0.86 rho)) is at most
min 2 (3.3 sqrt tau / ell). PROVED from the A.29 leaf. -/
theorem constant_le (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0) (hτ : 0 < |s.im|) :
    sqrt (1 + 2 * c0 (rho δ s.im) ^ 2) * (sqrt π / (2 * sqrt (eta (rho δ s.im)))) ≤
      min 2 (3.3 * sqrt |s.im| / (2 * π * |δ|)) := by
  set ρ := rho δ s.im with hρdef
  have hρ : 0 < ρ := rho_pos δ s.im hδ hτ
  obtain ⟨hη, hA⟩ := eta_bound ρ hρ
  set X := sqrt ((1 + 2 * c0 ρ ^ 2) / eta ρ)
  have hX : sqrt (1 + 2 * c0 ρ ^ 2) * (sqrt π / (2 * sqrt (eta ρ))) = sqrt π / 2 * X := by
    simp only [X]
    rw [sqrt_div (by positivity)]
    field_simp
  rw [hX]
  have hpi : sqrt π ≤ 1.78 := by
    rw [show (1.78 : ℝ) = sqrt (1.78 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by have := pi_lt_d2; norm_num at this ⊢; linarith)
  have hX0 : 0 ≤ X := sqrt_nonneg _
  have hX5 : X ≤ sqrt 5 := sqrt_le_sqrt (hA.trans (min_le_left _ _))
  have hXr : X ≤ sqrt (0.86 * ρ) := sqrt_le_sqrt (hA.trans (min_le_right _ _))
  have hs5 : sqrt 5 ≤ 2.237 := by
    rw [show (2.237 : ℝ) = sqrt (2.237 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num)
  have hs86 : sqrt 0.86 ≤ 0.93 := by
    rw [show (0.93 : ℝ) = sqrt (0.93 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num)
  have hpd : 0 < π * |δ| := mul_pos pi_pos (abs_pos.mpr hδ)
  have hsρ : sqrt ρ = sqrt |s.im| / (π * |δ|) := by
    rw [hρdef, rho, sqrt_div (abs_nonneg _), show (π * δ) ^ 2 = (π * |δ|) ^ 2 by
      rw [mul_pow, mul_pow, sq_abs], sqrt_sq hpd.le]
  have hsp : 0 ≤ sqrt π := sqrt_nonneg _
  apply le_min
  · nlinarith
  · have h1 : X ≤ 0.93 * (sqrt |s.im| / (π * |δ|)) := by
      rw [← hsρ, sqrt_mul (by norm_num)] at *
      exact hXr.trans (mul_le_mul_of_nonneg_right hs86 (sqrt_nonneg _))
    have h2 : 3.3 * sqrt |s.im| / (2 * π * |δ|) = 1.65 * (sqrt |s.im| / (π * |δ|)) := by
      field_simp; ring
    rw [h2]
    have hq : 0 ≤ sqrt |s.im| / (π * |δ|) := div_nonneg (sqrt_nonneg _) hpd.le
    nlinarith

/-- P0014 page 23: r0 ^ (sigma - 1) is at most ((3/2) / min (tau / ell) (sqrt tau)) ^ (1 - sigma)
for sigma at most 1. PROVED from the A.32 leaf. -/
theorem radius_power_le (δ : ℝ) (s : ℂ) (hδ : δ ≠ 0) (hτ : 0 < |s.im|) (hσ1 : s.re ≤ 1) :
    saddleRadius δ s.im ^ (s.re - 1) ≤
      ((3 / 2 : ℝ) / min (|s.im| / (2 * π * |δ|)) (sqrt |s.im|)) ^ (1 - s.re) := by
  set m := min (|s.im| / (2 * π * |δ|)) (sqrt |s.im|)
  have hm : 0 < m := lt_min (div_pos hτ (by positivity)) (sqrt_pos.mpr hτ)
  have hlow : 2 / 3 * m ≤ saddleRadius δ s.im := saddleRadius_lower δ s.im hδ hτ
  have h1 : saddleRadius δ s.im ^ (s.re - 1) ≤ (2 / 3 * m) ^ (s.re - 1) :=
    rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
  have h2 : (2 / 3 * m) ^ (s.re - 1) = ((3 / 2 : ℝ) / m) ^ (1 - s.re) := by
    rw [show s.re - 1 = -(1 - s.re) by ring, rpow_neg (by positivity),
      ← inv_rpow (by positivity)]
    congr 1
    field_simp
  exact h1.trans h2.le

/-! ## Assembly -/

/-- P0014 page 23, displays 3.56 and 3.57, exactly the statement of
`Decomp639Contour.saddle_segment_bound`, assembled from the steps above with no further
unproved step. CONDITIONAL ON the four leaves phase_lower_bound, arc_length_bound, eta_bound and
saddleRadius_lower. -/
theorem saddle_segment_bound_of_leaves (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖saddleIntegral δ s‖ ≤ mainCoefficient s.re |s.im| δ *
      exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) := by
  have hδ : δ ≠ 0 := by intro h; simp [h] at hsign
  have hτ : 0 < |s.im| := by linarith
  set σ := s.re with hσdef
  set a := initialRadius δ s.im
  set b := realEndpoint δ s.im
  set r0 := saddleRadius δ s.im
  set ρ := rho δ s.im with hρdef
  set η := eta ρ
  set γ := saddlePath δ s.im
  set B := exp (-BookE.E ρ * |s.im|)
  set Λ := sqrt (1 + 2 * c0 ρ ^ 2)
  set G := sqrt π / (2 * sqrt η)
  set P := (7.83 : ℝ) ^ (1 - σ)
  have hρ : 0 < ρ := rho_pos δ s.im hδ hτ
  have hη : 0 < η := (eta_bound ρ hρ).1
  have ha0 : 0 < a := initialRadius_pos δ s.im hδ hτ
  obtain ⟨har0, hr0b⟩ := saddleRadius_mem δ s.im hδ hτ
  have hr0 : 0 < r0 := ha0.trans_le har0
  have hab : a ≤ b := har0.trans hr0b
  -- integrability, as in `saddleIntegral_eq_sub`
  have hcd : ∀ r ∈ Icc a b, ContDiffAt ℝ 2 γ r := fun r hr =>
    saddlePath_contDiffAt δ s.im r hδ hτ hr
  have hγc : ContinuousOn γ (Icc a b) := fun r hr =>
    (hcd r hr).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv γ) (Icc a b) := fun r hr =>
    ((hcd r hr).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  have hkc : ContinuousOn (fun r => contourKernel δ s (γ r)) (Icc a b) :=
    (contourKernel_differentiable δ s).continuousOn.comp hγc
      (fun r hr => saddlePath_re_pos δ s.im r hδ hτ hr)
  have hint : IntervalIntegrable (fun r => contourKernel δ s (γ r) * deriv γ r) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hkc.mul hdc
  have hint1 : IntervalIntegrable (fun r => contourKernel δ s (γ r) * deriv γ r) volume a r0 :=
    hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le har0]; exact Icc_subset_Icc le_rfl hr0b)
  have hint2 : IntervalIntegrable (fun r => contourKernel δ s (γ r) * deriv γ r) volume r0 b :=
    hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hr0b]; exact Icc_subset_Icc har0 le_rfl)
  have hsplit : saddleIntegral δ s =
      (∫ r in a..r0, contourKernel δ s (γ r) * deriv γ r) +
        ∫ r in r0..b, contourKernel δ s (γ r) * deriv γ r :=
    (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  -- pointwise bound
  have hpt : ∀ r ∈ Icc a b, ‖contourKernel δ s (γ r) * deriv γ r‖ ≤
      r ^ (σ - 1) * B * exp (-η * (r - r0) ^ 2) * Λ := by
    intro r hr
    rw [norm_mul]
    exact mul_le_mul (phase_lower_bound δ s hsign r hr) (arc_length_bound δ s.im r hδ hτ hr)
      (norm_nonneg _) (by have := ha0.trans_le hr.1; positivity)
  -- power bounds of display 3.48
  have h783 : r0 ≤ 7.83 * a := saddleRadius_le_initial δ s.im hδ hτ
  have hpow1 : ∀ r ∈ Icc a r0, r ^ (σ - 1) ≤ P * r0 ^ (σ - 1) := by
    intro r hr
    have hlow : r0 / 7.83 ≤ r := by
      rw [div_le_iff₀ (by norm_num)]; linarith [hr.1]
    have h1 : r ^ (σ - 1) ≤ (r0 / 7.83) ^ (σ - 1) :=
      rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
    have h2 : (r0 / 7.83) ^ (σ - 1) = P * r0 ^ (σ - 1) := by
      rw [div_rpow hr0.le (by norm_num), show σ - 1 = -(1 - σ) by ring,
        rpow_neg (by norm_num : (0 : ℝ) ≤ 7.83)]
      simp only [P]
      field_simp
    exact h1.trans h2.le
  have hpow2 : ∀ r ∈ Icc r0 b, r ^ (σ - 1) ≤ r0 ^ (σ - 1) := fun r hr =>
    rpow_le_rpow_of_nonpos hr0 hr.1 (by linarith)
  -- the two halves
  have hI1 : ‖∫ r in a..r0, contourKernel δ s (γ r) * deriv γ r‖ ≤
      (P * r0 ^ (σ - 1) * B * Λ) * G := by
    apply piece_bound _ _ η r0 a r0 hη (by positivity) har0 (Or.inl rfl)
    intro r hr
    have hrab : r ∈ Icc a b := ⟨hr.1, hr.2.trans hr0b⟩
    have hrp : 0 < r := ha0.trans_le hr.1
    calc _ ≤ r ^ (σ - 1) * B * exp (-η * (r - r0) ^ 2) * Λ := hpt r hrab
      _ ≤ P * r0 ^ (σ - 1) * B * exp (-η * (r - r0) ^ 2) * Λ := by
        gcongr
        exact hpow1 r hr
      _ = _ := by ring
  have hI2 : ‖∫ r in r0..b, contourKernel δ s (γ r) * deriv γ r‖ ≤
      (r0 ^ (σ - 1) * B * Λ) * G := by
    apply piece_bound _ _ η r0 r0 b hη (by positivity) hr0b (Or.inr rfl)
    intro r hr
    have hrab : r ∈ Icc a b := ⟨har0.trans hr.1, hr.2⟩
    have hrp : 0 < r := hr0.trans_le hr.1
    calc _ ≤ r ^ (σ - 1) * B * exp (-η * (r - r0) ^ 2) * Λ := hpt r hrab
      _ ≤ r0 ^ (σ - 1) * B * exp (-η * (r - r0) ^ 2) * Λ := by
        have hB0 : 0 ≤ B := (exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        exact mul_le_mul_of_nonneg_right (hpow2 r hr) hB0
      _ = _ := by ring
  -- constants of display 3.57
  have hK : Λ * G ≤ min 2 (3.3 * sqrt |s.im| / (2 * π * |δ|)) := constant_le δ s hδ hτ
  have hR := radius_power_le δ s hδ hτ hσ1
  have hM : P + 1 ≤ 1 + max ((7.83 : ℝ) ^ (1 - σ)) ((1.63 : ℝ) ^ (σ - 1)) := by
    simp only [P]; linarith [le_max_left ((7.83 : ℝ) ^ (1 - σ)) ((1.63 : ℝ) ^ (σ - 1))]
  have hE : exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) = B := rfl
  rw [hE, hsplit]
  unfold mainCoefficient
  have hB : 0 ≤ B := (exp_pos _).le
  have hP : 0 ≤ P := by positivity
  have hR0 : 0 ≤ r0 ^ (σ - 1) := by positivity
  have hΛG : 0 ≤ Λ * G := by positivity
  calc _ ≤ ‖∫ r in a..r0, contourKernel δ s (γ r) * deriv γ r‖ +
        ‖∫ r in r0..b, contourKernel δ s (γ r) * deriv γ r‖ := norm_add_le _ _
    _ ≤ (P * r0 ^ (σ - 1) * B * Λ) * G + (r0 ^ (σ - 1) * B * Λ) * G := add_le_add hI1 hI2
    _ = (P + 1) * r0 ^ (σ - 1) * (B * (Λ * G)) := by ring
    _ ≤ (1 + max ((7.83 : ℝ) ^ (1 - σ)) ((1.63 : ℝ) ^ (σ - 1))) *
          ((3 / 2 : ℝ) / min (|s.im| / (2 * π * |δ|)) (sqrt |s.im|)) ^ (1 - σ) *
          (B * min 2 (3.3 * sqrt |s.im| / (2 * π * |δ|))) := by
        gcongr ?_ * ?_ * (B * ?_)
    _ = _ := by ring

/-- Twin check: the assembled theorem has exactly the type of the sealed leaf. -/
theorem saddle_segment_bound_twin :
    (∀ (δ : ℝ) (s : ℂ), 0 < s.re → s.re ≤ 1 → 100 ≤ |s.im| → δ * s.im < 0 →
      ‖saddleIntegral δ s‖ ≤ mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|)) :=
  fun δ s h0 h1 ht hs => saddle_segment_bound_of_leaves δ s h0 h1 ht hs

end LeanLab.HelfgottMajor.DQSaddleSegmentBound
