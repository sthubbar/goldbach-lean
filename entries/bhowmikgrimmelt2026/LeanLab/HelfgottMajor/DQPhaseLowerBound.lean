module

public import LeanLab.HelfgottMajor.ContourKernel669

/-!
Proof of the leaf `DQSaddleSegmentBound.phase_lower_bound`, session
CLOUD-burst20261120b-phase_lower, 2026-11-21.
Target: P0014 pages 18 to 21, displays 3.37 to 3.47. On the limacon C2 the kernel norm is at
most r ^ (sigma - 1) exp (- E rho |tau|) exp (- eta (r - r0) ^ 2).

The proof of the paper has three analytic steps, each a PROVED lemma below:
1. display 3.37, the kernel norm on the path is r ^ (sigma - 1) exp (- Re phi);
2. page 20, the arcsin series is cut after its linear term, by convexity of arcsin on [0, 1);
3. displays 3.42 to 3.46, the exact expansion of the remaining polynomial around nu = 0:
   constant term Re phi (u0,+), linear term zero, quadratic coefficient eta, and the rest
   nu ^ 2 (R(nu) - R(sin theta0 / (c1 rho))), written here in the variable r.
The step R(nu) at least R(sin theta0 / (c1 rho)), displays 3.41 to 3.44, is proved in
`DQSaddleSegmentBound.rest_nonneg` from Upsilon at least 1/2, and the assembly is
`DQSaddleSegmentBound.phase_lower_bound`.

Source: https://arxiv.org/abs/1305.2897, the copy papers/P0014.pdf.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.DQPhaseLowerBound
open Real Set Decomp639Contour

/-- PROVED: P0014 page 18, display 3.37, with display 3.36: for u = x + i y on the limacon,
|u ^ (s - 1) e ^ (- u ^ 2 / 2 + 2 pi i delta u)| = r ^ (sigma - 1) e ^ (- Re phi (u)), where
Re phi (u) = (r ^ 2 - 2 y ^ 2) / 2 - ell y + tau arcsin (y / r). Here y is the height of
`saddlePath` and the sign condition delta tau < 0 is the case tau > 0, ell > 0 of the paper,
with its mirror image. -/
theorem kernel_norm_saddlePath (δ : ℝ) (s : ℂ) (hsign : δ * s.im < 0) (r : ℝ)
    (hr : r ∈ Icc (initialRadius δ s.im) (realEndpoint δ s.im)) :
    let y := (-c1 (rho δ s.im) * r / ell δ + c0 (rho δ s.im)) * r
    ‖contourKernel δ s (saddlePath δ s.im r)‖ =
      r ^ (s.re - 1) * exp (-((r ^ 2 - 2 * y ^ 2) / 2 - ell δ * y + |s.im| * arcsin (y / r))) := by
  intro y
  have hδ : δ ≠ 0 := by intro h; simp [h] at hsign
  have hτ : 0 < |s.im| := abs_pos.mpr (by intro h; simp [h] at hsign)
  have hb := saddlePath_height_bounds δ s.im r hδ hτ hr
  simp only at hb
  obtain ⟨hr0, hy0, hy1⟩ := hb
  have hysq := pow_le_pow_left₀ hy0 hy1 2
  rw [div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hysq
  have hsub : 0 ≤ r ^ 2 - y ^ 2 := by nlinarith
  set z := saddlePath δ s.im r with hz
  have hzn : ‖z‖ = r := saddlePath_norm δ s.im r hδ hτ hr
  have hzre : z.re = sqrt (r ^ 2 - y ^ 2) := by
    rw [hz]; dsimp [saddlePath]; split_ifs <;> simp [y]
  have hzim : z.im = if 0 ≤ s.im then y else -y := by
    rw [hz]; dsimp [saddlePath]; split_ifs <;> simp [y]
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hzn; linarith
  have hre2 : z.re ^ 2 = r ^ 2 - y ^ 2 := by rw [hzre, sq_sqrt hsub]
  have harg : Complex.arg z = arcsin (z.im / r) := by
    rw [Complex.arg_of_re_nonneg (by rw [hzre]; exact sqrt_nonneg _), hzn]
  unfold contourKernel
  rw [norm_mul, Complex.norm_cpow_of_ne_zero hz0, Complex.norm_exp, hzn, harg]
  have hW : (-z ^ 2 / 2 + 2 * π * Complex.I * δ * z).re =
      -(z.re ^ 2 - z.im ^ 2) / 2 - 2 * π * δ * z.im := by
    simp [Complex.add_re, Complex.mul_re, pow_two]
    ring
  rw [hW, hre2]
  have hell : ell δ = 2 * π * |δ| := rfl
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  rw [div_eq_mul_inv, ← exp_neg, mul_assoc, ← exp_add]
  congr 2
  rw [hzim, hell]
  split_ifs with h
  · have hτp : 0 < s.im := by
      rcases h.lt_or_eq with h' | h'
      · exact h'
      · rw [← h'] at hτ; simp at hτ
    have hδn : δ < 0 := by nlinarith
    rw [abs_of_pos hτp, abs_of_neg hδn]
    ring
  · push Not at h
    have hδp : 0 < δ := by nlinarith
    rw [abs_of_neg h, abs_of_pos hδp, neg_div, arcsin_neg]
    ring

/-- The derivative 1 / sqrt (1 - x ^ 2) of arcsin is monotone on [0, 1). PROVED. -/
theorem inv_sqrt_mono (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    1 / sqrt (1 - x ^ 2) ≤ 1 / sqrt (1 - y ^ 2) := by
  apply one_div_le_one_div_of_le (sqrt_pos.mpr (by nlinarith))
  apply sqrt_le_sqrt; nlinarith

/-- PROVED: P0014 page 20, after display 3.46's preparation: the Taylor series of
arcsin (sin theta0 - c1 rho nu) is cut at k = 2 with a remainder at theta1 in [0, pi/2], whose
quadratic term is nonnegative, so arcsin b is at least arcsin a + (b - a) / cos theta0 with
cos theta0 = sqrt (1 - a ^ 2). Stated for a and b in [0, 1). -/
theorem arcsin_tangent_le (a b : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b) (hb1 : b < 1) :
    arcsin a + (b - a) / sqrt (1 - a ^ 2) ≤ arcsin b := by
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt arcsin (1 / sqrt (1 - x ^ 2)) x := fun x hx =>
    hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])
  have hpa : 0 < sqrt (1 - a ^ 2) := sqrt_pos.mpr (by nlinarith)
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope arcsin (fun x => 1 / sqrt (1 - x ^ 2))
      hab continuous_arcsin.continuousOn
      (fun x hx => hd x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have hm := inv_sqrt_mono a c ha hc.1.le (by linarith [hc.2])
    rw [hce, le_div_iff₀ (by linarith)] at hm
    rw [div_eq_mul_one_div]
    nlinarith
  · subst hab; simp
  · obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope arcsin (fun x => 1 / sqrt (1 - x ^ 2))
      hab continuous_arcsin.continuousOn
      (fun x hx => hd x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have hm := inv_sqrt_mono c a (by linarith [hc.1]) hc.2.le ha1
    rw [hce, div_le_iff₀ (by linarith)] at hm
    rw [div_eq_mul_one_div]
    nlinarith

set_option maxHeartbeats 4000000 in
/-- The polynomial core of displays 3.42 to 3.46 after clearing denominators, with
C = cos theta0, S = sin theta0 of display 3.28 and the relation of display 3.25 for Upsilon:
the numerator of the identity of `phase_expansion_identity` vanishes. The coefficients
were found by pseudo division in sympy. PROVED. -/
theorem phase_poly_core (l r v C S U : ℝ) (hv : 1 < v)
    (hC : 2 * v * C ^ 2 - (v + 1) = 0) (hS : 2 * v * S ^ 2 - (v - 1) = 0)
    (hU : (2 * v - 1) * (v + 1) * (1 - U ^ 2) - 4 * v * C * S * U = 0) :
    -4*C^3*S^4*U^2*l^4*v^4 + 8*C^3*S^3*U^2*l^3*r*v^3 - 4*C^3*S^2*U^2*l^2*r^2*v^2 + 8*C^2*S^5*U*l^4*v^4 - 24*C^2*S^4*U*l^3*r*v^3 + 4*C^2*S^3*U*l^4*v^4 + 16*C^2*S^3*U*l^2*r^2*v^2 - 4*C^2*S^2*U*l^3*r*v^3 - 4*C^2*S^2*U*l^3*r*v^2 + 4*C^2*S*U*l^2*r^2*v + 4*C*S^6*l^4*v^4 - 8*C*S^5*l^3*r*v^3 + 2*C*S^4*U^2*l^4*v^4 - 2*C*S^4*U^2*l^4*v^3 - 2*C*S^4*l^4*v^4 - 4*C*S^3*U^2*l^3*r*v^3 + 4*C*S^3*U^2*l^3*r*v^2 + 4*C*S^3*l^3*r*v^3 - 4*C*S^3*l^3*r*v^2 + 2*C*S^2*U^2*l^2*r^2*v^2 - 2*C*S^2*U^2*l^2*r^2*v + C*S^2*l^4*v^3 - C*S^2*l^4*v^2 - 2*S^3*U^3*l^4*v^4 - S^3*U^3*l^4*v^3 + S^3*U^3*l^4*v^2 - 2*S^3*U*l^4*v^4 - S^3*U*l^4*v^3 + S^3*U*l^4*v^2 + 4*S^2*U^3*l^3*r*v^3 + 2*S^2*U^3*l^3*r*v^2 - 2*S^2*U^3*l^3*r*v + 4*S^2*U*l^3*r*v^3 + 2*S^2*U*l^3*r*v^2 - 2*S^2*U*l^3*r*v - 2*S*U^3*l^2*r^2*v^2 - S*U^3*l^2*r^2*v + S*U^3*l^2*r^2 - 2*S*U*l^2*r^2*v^2 - S*U*l^2*r^2*v + S*U*l^2*r^2 = 0 := by
  have hL : (8 * v ^ 3) * (32 * v ^ 5) * ((v + 1) ^ 2 * (2 * v - 1) ^ 2) ≠ 0 := by
    have : 0 < v := by linarith
    have : 0 < 2 * v - 1 := by linarith
    positivity
  have key : (8 * v ^ 3) * (32 * v ^ 5) * ((v + 1) ^ 2 * (2 * v - 1) ^ 2) * (-4*C^3*S^4*U^2*l^4*v^4 + 8*C^3*S^3*U^2*l^3*r*v^3 - 4*C^3*S^2*U^2*l^2*r^2*v^2 + 8*C^2*S^5*U*l^4*v^4 - 24*C^2*S^4*U*l^3*r*v^3 + 4*C^2*S^3*U*l^4*v^4 + 16*C^2*S^3*U*l^2*r^2*v^2 - 4*C^2*S^2*U*l^3*r*v^3 - 4*C^2*S^2*U*l^3*r*v^2 + 4*C^2*S*U*l^2*r^2*v + 4*C*S^6*l^4*v^4 - 8*C*S^5*l^3*r*v^3 + 2*C*S^4*U^2*l^4*v^4 - 2*C*S^4*U^2*l^4*v^3 - 2*C*S^4*l^4*v^4 - 4*C*S^3*U^2*l^3*r*v^3 + 4*C*S^3*U^2*l^3*r*v^2 + 4*C*S^3*l^3*r*v^3 - 4*C*S^3*l^3*r*v^2 + 2*C*S^2*U^2*l^2*r^2*v^2 - 2*C*S^2*U^2*l^2*r^2*v + C*S^2*l^4*v^3 - C*S^2*l^4*v^2 - 2*S^3*U^3*l^4*v^4 - S^3*U^3*l^4*v^3 + S^3*U^3*l^4*v^2 - 2*S^3*U*l^4*v^4 - S^3*U*l^4*v^3 + S^3*U*l^4*v^2 + 4*S^2*U^3*l^3*r*v^3 + 2*S^2*U^3*l^3*r*v^2 - 2*S^2*U^3*l^3*r*v + 4*S^2*U*l^3*r*v^3 + 2*S^2*U*l^3*r*v^2 - 2*S^2*U*l^3*r*v - 2*S*U^3*l^2*r^2*v^2 - S*U^3*l^2*r^2*v + S*U^3*l^2*r^2 - 2*S*U*l^2*r^2*v^2 - S*U*l^2*r^2*v + S*U*l^2*r^2) = 0 := by
    linear_combination (8 * v ^ 3) * (32 * v ^ 5) * (8*C^3*S^4*l^4*v^6 + 4*C^3*S^4*l^4*v^5 - 4*C^3*S^4*l^4*v^4 - 16*C^3*S^3*l^3*r*v^5 - 8*C^3*S^3*l^3*r*v^4 + 8*C^3*S^3*l^3*r*v^3 + 8*C^3*S^2*l^2*r^2*v^4 + 4*C^3*S^2*l^2*r^2*v^3 - 4*C^3*S^2*l^2*r^2*v^2 - 4*C*S^4*l^4*v^6 - 6*C*S^4*l^4*v^5 + 2*C*S^4*l^4*v^3 + 8*C*S^3*l^3*r*v^5 + 12*C*S^3*l^3*r*v^4 - 4*C*S^3*l^3*r*v^2 - 4*C*S^2*l^2*r^2*v^4 - 6*C*S^2*l^2*r^2*v^3 + 2*C*S^2*l^2*r^2*v + 4*S^3*U*l^4*v^6 + 4*S^3*U*l^4*v^5 - 3*S^3*U*l^4*v^4 - 2*S^3*U*l^4*v^3 + S^3*U*l^4*v^2 - 8*S^2*U*l^3*r*v^5 - 8*S^2*U*l^3*r*v^4 + 6*S^2*U*l^3*r*v^3 + 4*S^2*U*l^3*r*v^2 - 2*S^2*U*l^3*r*v + 4*S*U*l^2*r^2*v^4 + 4*S*U*l^2*r^2*v^3 - 3*S*U*l^2*r^2*v^2 - 2*S*U*l^2*r^2*v + S*U*l^2*r^2) * hU +
      (32 * v ^ 5) * (128*C^2*S^5*U*l^4*v^9 + 64*C^2*S^5*U*l^4*v^8 - 64*C^2*S^5*U*l^4*v^7 - 256*C^2*S^4*U*l^3*r*v^8 - 128*C^2*S^4*U*l^3*r*v^7 + 128*C^2*S^4*U*l^3*r*v^6 + 128*C^2*S^3*U*l^2*r^2*v^7 + 64*C^2*S^3*U*l^2*r^2*v^6 - 64*C^2*S^3*U*l^2*r^2*v^5 - 64*C*S^4*l^4*v^10 - 64*C*S^4*l^4*v^9 + 48*C*S^4*l^4*v^8 + 32*C*S^4*l^4*v^7 - 16*C*S^4*l^4*v^6 + 128*C*S^3*l^3*r*v^9 + 128*C*S^3*l^3*r*v^8 - 96*C*S^3*l^3*r*v^7 - 64*C*S^3*l^3*r*v^6 + 32*C*S^3*l^3*r*v^5 - 64*C*S^2*l^2*r^2*v^8 - 64*C*S^2*l^2*r^2*v^7 + 48*C*S^2*l^2*r^2*v^6 + 32*C*S^2*l^2*r^2*v^5 - 16*C*S^2*l^2*r^2*v^4 + 128*S^5*U*l^4*v^10 + 128*S^5*U*l^4*v^9 - 96*S^5*U*l^4*v^8 - 64*S^5*U*l^4*v^7 + 32*S^5*U*l^4*v^6 - 384*S^4*U*l^3*r*v^9 - 384*S^4*U*l^3*r*v^8 + 288*S^4*U*l^3*r*v^7 + 192*S^4*U*l^3*r*v^6 - 96*S^4*U*l^3*r*v^5 + 64*S^3*U*l^4*v^10 + 64*S^3*U*l^4*v^9 - 48*S^3*U*l^4*v^8 - 32*S^3*U*l^4*v^7 + 16*S^3*U*l^4*v^6 + 256*S^3*U*l^2*r^2*v^8 + 256*S^3*U*l^2*r^2*v^7 - 192*S^3*U*l^2*r^2*v^6 - 128*S^3*U*l^2*r^2*v^5 + 64*S^3*U*l^2*r^2*v^4 - 64*S^2*U*l^3*r*v^9 - 128*S^2*U*l^3*r*v^8 - 16*S^2*U*l^3*r*v^7 + 80*S^2*U*l^3*r*v^6 + 16*S^2*U*l^3*r*v^5 - 16*S^2*U*l^3*r*v^4 + 64*S*U*l^2*r^2*v^7 + 64*S*U*l^2*r^2*v^6 - 48*S*U*l^2*r^2*v^5 - 32*S*U*l^2*r^2*v^4 + 16*S*U*l^2*r^2*v^3) * hC + (2048*C*S^4*l^4*v^15 + 2048*C*S^4*l^4*v^14 - 1536*C*S^4*l^4*v^13 - 1024*C*S^4*l^4*v^12 + 512*C*S^4*l^4*v^11 - 4096*C*S^3*l^3*r*v^14 - 4096*C*S^3*l^3*r*v^13 + 3072*C*S^3*l^3*r*v^12 + 2048*C*S^3*l^3*r*v^11 - 1024*C*S^3*l^3*r*v^10 - 1024*C*S^2*l^4*v^14 - 1024*C*S^2*l^4*v^13 + 768*C*S^2*l^4*v^12 + 512*C*S^2*l^4*v^11 - 256*C*S^2*l^4*v^10 + 2048*S^3*U*l^4*v^15 + 4096*S^3*U*l^4*v^14 + 512*S^3*U*l^4*v^13 - 2560*S^3*U*l^4*v^12 - 512*S^3*U*l^4*v^11 + 512*S^3*U*l^4*v^10 - 6144*S^2*U*l^3*r*v^14 - 12288*S^2*U*l^3*r*v^13 - 1536*S^2*U*l^3*r*v^12 + 7680*S^2*U*l^3*r*v^11 + 1536*S^2*U*l^3*r*v^10 - 1536*S^2*U*l^3*r*v^9 + 4096*S*U*l^2*r^2*v^13 + 8192*S*U*l^2*r^2*v^12 + 1024*S*U*l^2*r^2*v^11 - 5120*S*U*l^2*r^2*v^10 - 1024*S*U*l^2*r^2*v^9 + 1024*S*U*l^2*r^2*v^8) * hS
  exact (mul_eq_zero.mp key).resolve_left hL

set_option maxHeartbeats 4000000 in
/-- PROVED: P0014 pages 18 to 21, displays 3.37 to 3.46, the expansion of psi0 around the saddle
point times ell ^ 2 rho ^ 2, after the arcsin term is replaced by its tangent at theta0:
with s = y / r = sin theta0 - c1 rho nu of display 3.39, sin theta0 = sqrt (1/2 - 1/(2 v)),
cos theta0 = sqrt (1/2 + 1/(2 v)) of display 3.28, r0 = ell / sqrt 2 * sqrt (v ^ 2 - v) of
display 3.32 and eta of display 3.46,
(r ^ 2 - 2 y ^ 2) / 2 - ell y + tau (theta0 + (s - sin theta0) / cos theta0)
equals E rho tau + eta (r - r0) ^ 2 + (r - r0) ^ 2 s (2 cos theta0 Upsilon - s).
The constant term is Re phi (u0,+) = E rho tau, display 3.47 and the line after it; the linear
term vanishes, a1 = 0 on page 19; the quadratic coefficient is eta, displays 3.43 to 3.46; the
cubic and quartic terms are nu ^ 2 (R (nu) - R (sin theta0 / (c1 rho))) of page 20, using
c1 rho nu0 = cos theta0 Upsilon. -/
theorem phase_expansion_identity (δ τ r : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    let ρ := rho δ τ
    let v := BookE.ups ρ
    let C := sqrt (1 / 2 + 1 / (2 * v))
    let S := sqrt (1 / 2 - 1 / (2 * v))
    let U := upsilon ρ
    let s := -c1 ρ * r / ell δ + c0 ρ
    let y := s * r
    let r0 := ell δ / sqrt 2 * sqrt (v ^ 2 - v)
    let η := 1 / 2 * sqrt (2 * sqrt (1 + ρ ^ 2) / (v ^ 2 - v)) * (1 + U ^ 2) - U ^ 2 / 2 +
      1 / 2 - 1 / (2 * v) - ρ / (sqrt (1 + ρ ^ 2) + 1) * U
    (r ^ 2 - 2 * y ^ 2) / 2 - ell δ * y + |τ| * (arcsin S + (s - S) / C) =
      BookE.E ρ * |τ| + η * (r - r0) ^ 2 + (r - r0) ^ 2 * (s * (2 * C * U - s)) := by
  intro ρ v C S U s y r0 η
  have hρ : 0 < ρ := rho_pos δ τ hδ hτ
  have hv : 1 < v := ups_gt_one ρ hρ
  have hv0 : 0 < v := by linarith
  have hv1 : v - 1 ≠ 0 := by linarith
  have hvv : v ^ 2 - v ≠ 0 := by nlinarith
  have hL := ell_pos δ hδ
  have hU0 : 0 < U := upsilon_pos ρ hρ
  have hvi : 1 / (2 * v) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hC2 : C ^ 2 = 1 / 2 + 1 / (2 * v) := sq_sqrt (by positivity)
  have hS2 : S ^ 2 = 1 / 2 - 1 / (2 * v) := sq_sqrt (by linarith)
  have hC0 : 0 < C := sqrt_pos.mpr (by positivity)
  have hS0 : 0 < S := sqrt_pos.mpr (by linarith)
  have hj2 : sqrt (1 + ρ ^ 2) ^ 2 = 1 + ρ ^ 2 := sq_sqrt (by positivity)
  have hv2 : v ^ 2 = (1 + sqrt (1 + ρ ^ 2)) / 2 := by
    show BookE.ups ρ ^ 2 = _
    unfold BookE.ups
    exact sq_sqrt (by positivity)
  have hj : sqrt (1 + ρ ^ 2) = 2 * v ^ 2 - 1 := by linarith
  have hρv : ρ = 4 * v ^ 2 * C * S := by
    have h1 : ρ ^ 2 = (4 * v ^ 2 * C * S) ^ 2 := by
      have : ρ ^ 2 = (2 * v ^ 2 - 1) ^ 2 - 1 := by rw [← hj]; linarith
      rw [this, show (4 * v ^ 2 * C * S) ^ 2 = 16 * v ^ 4 * C ^ 2 * S ^ 2 by ring, hC2, hS2]
      field_simp; ring
    exact (sq_eq_sq₀ hρ.le (by positivity)).mp h1
  have hc1 : c1 ρ = C * U / (v * S) := by
    show sqrt ((1 + 1 / v) / (v ^ 2 - v)) * U = _
    have : sqrt ((1 + 1 / v) / (v ^ 2 - v)) = C / (v * S) := by
      rw [show (1 + 1 / v) / (v ^ 2 - v) = (C / (v * S)) ^ 2 by
        rw [div_pow, mul_pow, hC2, hS2]; field_simp]
      exact sqrt_sq (by positivity)
    rw [this]; ring
  have hr0 : r0 = ell δ * v * S := by
    show ell δ / sqrt 2 * sqrt (v ^ 2 - v) = _
    have : sqrt (v ^ 2 - v) = sqrt 2 * (v * S) := by
      rw [show v ^ 2 - v = (sqrt 2 * (v * S)) ^ 2 by
        rw [mul_pow, sq_sqrt (by norm_num), mul_pow, hS2]; field_simp]
      exact sqrt_sq (by positivity)
    rw [this]; field_simp
  have hτρ : |τ| = ell δ ^ 2 * ρ / 4 := by have := ell_sq_mul_rho δ τ hδ; linarith
  have hθ : BookE.E ρ = arcsin S - (v - 1) / ρ := by
    show arccos (1 / v) / 2 - (v - 1) / ρ = _
    have hcos : cos (2 * arcsin S) = 1 / v := by
      rw [cos_two_mul, cos_arcsin, sq_sqrt (by nlinarith), hS2]; ring
    have h0 : 0 ≤ arcsin S := arcsin_nonneg.mpr hS0.le
    have h1 : arcsin S ≤ π / 2 := arcsin_le_pi_div_two S
    rw [← hcos, arccos_cos (by linarith) (by linarith)]
    ring
  have hA : 2 * v * (v + sqrt (1 + ρ ^ 2)) / ρ = (2 * v - 1) * (v + 1) / (2 * v * C * S) := by
    rw [hj, hρv]; field_simp; ring
  have hq : 2 * v * (v + sqrt (1 + ρ ^ 2)) / ρ * (1 - U ^ 2) = 2 * U := upsilon_quadratic ρ hρ
  rw [hA] at hq
  have hU' : (2 * v - 1) * (v + 1) * (1 - U ^ 2) - 4 * v * C * S * U = 0 := by
    rw [div_mul_eq_mul_div, div_eq_iff (by positivity)] at hq
    linarith
  have hC' : 2 * v * C ^ 2 - (v + 1) = 0 := by rw [hC2]; field_simp; ring
  have hS' : 2 * v * S ^ 2 - (v - 1) = 0 := by rw [hS2]; field_simp; ring
  have hW : sqrt (2 * sqrt (1 + ρ ^ 2) / (v ^ 2 - v)) =
      (1 + (2 * v - 1) * (v + 1) / (2 * v * C * S) * U) / v := by
    set A := (2 * v - 1) * (v + 1) / (2 * v * C * S) with hAdef
    have hA0 : 0 < A := by
      have : 0 < 2 * v - 1 := by linarith
      positivity
    have hsq : (1 + A * U) ^ 2 = 1 + A ^ 2 := by linear_combination (-A) * hq
    have hCS : 4 * v ^ 2 * C ^ 2 * S ^ 2 = v ^ 2 - 1 := by
      rw [hC2, hS2]; field_simp; ring
    have hA2 : 1 + A ^ 2 = v ^ 2 * (2 * (2 * v ^ 2 - 1) / (v ^ 2 - v)) := by
      rw [hAdef, div_pow, show (2 * v * C * S) ^ 2 = 4 * v ^ 2 * C ^ 2 * S ^ 2 by ring, hCS]
      have : v ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp; ring
    rw [hj, show 2 * (2 * v ^ 2 - 1) / (v ^ 2 - v) = ((1 + A * U) / v) ^ 2 by
      rw [div_pow, hsq, hA2]; field_simp]
    exact sqrt_sq (by positivity)
  have hη : η = 1 / 2 * ((1 + (2 * v - 1) * (v + 1) / (2 * v * C * S) * U) / v) * (1 + U ^ 2) -
      U ^ 2 / 2 + 1 / 2 - 1 / (2 * v) - 2 * C * S * U := by
    show 1 / 2 * sqrt (2 * sqrt (1 + ρ ^ 2) / (v ^ 2 - v)) * (1 + U ^ 2) - U ^ 2 / 2 +
      1 / 2 - 1 / (2 * v) - ρ / (sqrt (1 + ρ ^ 2) + 1) * U = _
    rw [hW, hj]
    have : ρ / (2 * v ^ 2 - 1 + 1) = 2 * C * S := by
      rw [hρv, show 2 * v ^ 2 - 1 + 1 = 2 * v ^ 2 by ring]; field_simp; ring
    rw [this]
  have hs : s = -(C * U / (v * S)) * r / ell δ + (C * U + S) := by
    show -c1 ρ * r / ell δ + c0 ρ = _
    rw [hc1]; rfl
  have hy : y = s * r := rfl
  rw [hy, hη, hθ, hr0, hτρ, hs]
  have key := phase_poly_core (ell δ) r v C S U hv hC' hS' hU'
  rw [← sub_eq_zero]
  generalize arcsin S = θ
  generalize ell δ = l at key hL ⊢
  rw [hρv]
  calc _ = (-4*C^3*S^4*U^2*l^4*v^4 + 8*C^3*S^3*U^2*l^3*r*v^3 - 4*C^3*S^2*U^2*l^2*r^2*v^2 + 8*C^2*S^5*U*l^4*v^4 - 24*C^2*S^4*U*l^3*r*v^3 + 4*C^2*S^3*U*l^4*v^4 + 16*C^2*S^3*U*l^2*r^2*v^2 - 4*C^2*S^2*U*l^3*r*v^3 - 4*C^2*S^2*U*l^3*r*v^2 + 4*C^2*S*U*l^2*r^2*v + 4*C*S^6*l^4*v^4 - 8*C*S^5*l^3*r*v^3 + 2*C*S^4*U^2*l^4*v^4 - 2*C*S^4*U^2*l^4*v^3 - 2*C*S^4*l^4*v^4 - 4*C*S^3*U^2*l^3*r*v^3 + 4*C*S^3*U^2*l^3*r*v^2 + 4*C*S^3*l^3*r*v^3 - 4*C*S^3*l^3*r*v^2 + 2*C*S^2*U^2*l^2*r^2*v^2 - 2*C*S^2*U^2*l^2*r^2*v + C*S^2*l^4*v^3 - C*S^2*l^4*v^2 - 2*S^3*U^3*l^4*v^4 - S^3*U^3*l^4*v^3 + S^3*U^3*l^4*v^2 - 2*S^3*U*l^4*v^4 - S^3*U*l^4*v^3 + S^3*U*l^4*v^2 + 4*S^2*U^3*l^3*r*v^3 + 2*S^2*U^3*l^3*r*v^2 - 2*S^2*U^3*l^3*r*v + 4*S^2*U*l^3*r*v^3 + 2*S^2*U*l^3*r*v^2 - 2*S^2*U*l^3*r*v - 2*S*U^3*l^2*r^2*v^2 - S*U^3*l^2*r^2*v + S*U^3*l^2*r^2 - 2*S*U*l^2*r^2*v^2 - S*U*l^2*r^2*v + S*U*l^2*r^2) / (4 * C * S ^ 2 * l ^ 2 * v ^ 2) := by field_simp; ring
    _ = 0 := by rw [key, zero_div]

end LeanLab.HelfgottMajor.DQPhaseLowerBound
