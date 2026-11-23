module

public import LeanLab.HelfgottArcs.Statements
public import Mathlib

/-!
Gamma function estimates supporting the zero shift case of P0014 Theorem 3.1.
The scalar Gamma bounds occur in the derivation of display 3.3 on page 27.
Source: https://arxiv.org/abs/1305.2897
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real LeanLab.HelfgottArcs

/-- The Mellin transform F_delta used on page 43 in the proof of display 4.43. -/
noncomputable def gaussianMellin (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) s

end LeanLab.HelfgottMajor.SplitGaussian123

namespace LeanLab.HelfgottMajor.Gamma503
open Real MeasureTheory LeanLab.HelfgottArcs SplitGaussian123

/-- The Gamma bound used after display 3.67 on page 27. -/
theorem gamma_le_one (a : ℝ) (ha : 1 ≤ a) (hb : a ≤ 2) : Gamma a ≤ 1 := by
  have h := convexOn_Gamma.le_max_of_mem_Icc
    (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) ⟨ha, hb⟩
  simpa only [Gamma_one, Gamma_two, max_self] using h

/-- A positive lower bound for the real Gamma factors in the reflection route.
Derived supporting estimate for display 3.3, using the real Gamma bounds on page 27. -/
theorem gamma_three_quarters_le (a : ℝ) (ha : 1 ≤ a) (hb : a ≤ 2) :
    (3 / 4 : ℝ) ≤ Gamma a := by
  have hu := gamma_le_one (3 - a) (by linarith) (by linarith)
  have hm := convexOn_Gamma.2
    (by change (0 : ℝ) < a; linarith)
    (by change (0 : ℝ) < 3 - a; linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hmid : (1 / 2 : ℝ) * a + (1 / 2) * (3 - a) = 3 / 2 := by ring
  simp only [smul_eq_mul, hmid] at hm
  have hhalf : Gamma (3 / 2) = sqrt π / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Gamma_one_half_eq]
    ring
  rw [hhalf] at hm
  have hs : (7 / 4 : ℝ) ≤ sqrt π := le_sqrt_of_sq_le (by linarith [pi_gt_d2])
  linarith only [hu, hm, hs]

/-- A vertical Gamma ratio comparison from Euler's finite products.
Derived support for the Gamma reflection route to display 3.3 on page 10. -/
theorem gamma_vertical_ratio (a b y : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ‖Complex.Gamma ((a : ℂ) + y * Complex.I)‖ * Gamma b ≤
      ‖Complex.Gamma ((b : ℂ) + y * Complex.I)‖ * Gamma a := by
  have hb : 0 < b := ha.trans_le hab
  let z (u v : ℝ) : ℂ := (u : ℂ) + v * Complex.I
  let P (u v : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range (n + 1), ‖z u v + j‖
  have hpoint (u v : ℝ) (j : ℕ) : z u v + j = ((u + j : ℝ) : ℂ) + v * Complex.I := by
    dsimp [z]
    push_cast
    ring
  have hfactor (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) :
      ‖(B : ℂ) + y * Complex.I‖ * A ≤ ‖(A : ℂ) + y * Complex.I‖ * B := by
    have hB : 0 ≤ B := hA.trans hAB
    have hna : ‖(A : ℂ) + y * Complex.I‖ ^ 2 = A ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq]
      ring
    have hnb : ‖(B : ℂ) + y * Complex.I‖ ^ 2 = B ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq]
      ring
    apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hA)
      (mul_nonneg (norm_nonneg _) hB)).mp
    rw [mul_pow, mul_pow, hna, hnb]
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAB 2) (sq_nonneg y)
    nlinarith only [hh]
  have hPpos (u v : ℝ) (hu : 0 < u) (n : ℕ) : 0 < P u v n := by
    dsimp [P]
    apply Finset.prod_pos
    intro j hj
    apply norm_pos_iff.mpr
    intro hh
    have hre := congrArg Complex.re hh
    simp [z] at hre
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hformula (u v : ℝ) (n : ℕ) (hn : 0 < n) :
      ‖Complex.GammaSeq (z u v) n‖ =
        ((n : ℝ) ^ u * (n.factorial : ℝ)) / P u v n := by
    rw [Complex.GammaSeq, norm_div, norm_mul, norm_prod,
      Complex.norm_natCast_cpow_of_pos hn]
    simp [z, P]
  have hfinite (n : ℕ) (hn : 0 < n) :
      ‖Complex.GammaSeq (z a y) n‖ * ‖Complex.GammaSeq (z b 0) n‖ ≤
        ‖Complex.GammaSeq (z b y) n‖ * ‖Complex.GammaSeq (z a 0) n‖ := by
    have hprod : P b y n * P a 0 n ≤ P a y n * P b 0 n := by
      dsimp [P]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod₀
      · intro j hj
        positivity
      · intro j hj
        rw [hpoint b y j, hpoint a 0 j, hpoint a y j, hpoint b 0 j]
        simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < a + j),
          abs_of_pos (by positivity : (0 : ℝ) < b + j)]
        exact hfactor (a + j) (b + j) (by positivity) (by linarith)
    rw [hformula a y n hn, hformula b 0 n hn, hformula b y n hn, hformula a 0 n hn,
      div_mul_div_comm, div_mul_div_comm,
      div_le_div_iff₀ (mul_pos (hPpos a y ha n) (hPpos b 0 hb n))
        (mul_pos (hPpos b y hb n) (hPpos a 0 ha n))]
    have hN : 0 ≤ ((n : ℝ) ^ a * (n.factorial : ℝ)) *
        ((n : ℝ) ^ b * (n.factorial : ℝ)) := by positivity
    convert mul_le_mul_of_nonneg_left hprod hN using 1 <;> ring
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Complex.GammaSeq (z a y) n‖ * ‖Complex.GammaSeq (z b 0) n‖ ≤
        ‖Complex.GammaSeq (z b y) n‖ * ‖Complex.GammaSeq (z a 0) n‖ := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact hfinite n hn
  have h := le_of_tendsto_of_tendsto
    ((Complex.GammaSeq_tendsto_Gamma (z a y)).norm.mul
      (Complex.GammaSeq_tendsto_Gamma (z b 0)).norm)
    ((Complex.GammaSeq_tendsto_Gamma (z b y)).norm.mul
      (Complex.GammaSeq_tendsto_Gamma (z a 0)).norm) hevent
  simpa only [z, Complex.ofReal_zero, zero_mul, add_zero, Complex.Gamma_ofReal,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Gamma_pos_of_pos ha),
    abs_of_pos (Gamma_pos_of_pos hb)] using h

/-- A coarse exponential lower bound for sine away from the real axis.
Derived support for the Gamma reflection estimate in display 3.3 on page 10. -/
theorem sin_norm_exp_lower (z : ℂ) (hz : 1 ≤ |z.im|) :
    exp |z.im| / 3 ≤ ‖Complex.sin z‖ := by
  let v := |z.im|
  let A := Complex.exp (-z * Complex.I)
  let B := Complex.exp (z * Complex.I)
  have hA : ‖A‖ = exp z.im := by simp [A, Complex.norm_exp, Complex.mul_re]
  have hB : ‖B‖ = exp (-z.im) := by simp [B, Complex.norm_exp, Complex.mul_re]
  have hn : exp v - exp (-v) ≤ ‖A - B‖ := by
    by_cases hy : 0 ≤ z.im
    · have h := norm_sub_norm_le A B
      rw [hA, hB] at h
      simpa only [v, abs_of_nonneg hy] using h
    · have h := norm_sub_norm_le B A
      rw [hB, hA, norm_sub_rev] at h
      simpa only [v, abs_of_neg (lt_of_not_ge hy), neg_neg] using h
  have hs : ‖Complex.sin z‖ = ‖A - B‖ / 2 := by
    simp [A, B, Complex.sin, norm_div, norm_mul]
  have hlarge : (3 : ℝ) ≤ exp (2 * v) := by
    calc
      _ ≤ (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) exp_one_gt_two.le 2
      _ = exp 2 := by rw [← exp_nat_mul]; norm_num
      _ ≤ _ := exp_le_exp.mpr (by change 1 ≤ v at hz; linarith)
  have hsmall : 3 * exp (-v) ≤ exp v := by
    calc
      _ ≤ exp (2 * v) * exp (-v) := mul_le_mul_of_nonneg_right hlarge (exp_nonneg _)
      _ = _ := by rw [← exp_add]; congr 1; ring
  change exp v / 3 ≤ _
  rw [hs]
  linarith only [hn, hsmall]

/-- A uniform coarse vertical Gamma bound on the shifted half strip.
Derived supply for the zero shift estimate in display 3.3, pages 10 and 27. -/
theorem gamma_shifted_decay (a y : ℝ) (ha : 1 ≤ a) (hb : a ≤ 3 / 2)
    (hy : 1 ≤ |y|) :
    ‖Complex.Gamma ((a : ℂ) + y * Complex.I)‖ ≤
      4 * (|y| + 1) * exp (-(π / 2) * |y|) := by
  let z : ℂ := (a : ℂ) + y * Complex.I
  let v := π * |y|
  have ha0 : 0 < a := by linarith
  have hy0 : y ≠ 0 := abs_pos.mp (by linarith)
  have hΓa := gamma_le_one a ha (by linarith)
  have hΓb := gamma_three_quarters_le (3 - a) (by linarith) (by linarith)
  have hratio := gamma_vertical_ratio a (3 - a) y ha0 (by linarith)
  have hc : (starRingEnd ℂ) (3 - z) = (((3 - a : ℝ) : ℂ) + y * Complex.I) := by
    apply Complex.ext <;> simp [z]
  have hnorm : ‖Complex.Gamma (((3 - a : ℝ) : ℂ) + y * Complex.I)‖ =
      ‖Complex.Gamma (3 - z)‖ := by
    rw [← hc, Complex.Gamma_conj]
    simp
  rw [hnorm] at hratio
  change ‖Complex.Gamma z‖ * Gamma (3 - a) ≤ ‖Complex.Gamma (3 - z)‖ * Gamma a at hratio
  have hr : (3 / 4 : ℝ) * ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (3 - z)‖ := by
    have h1 := mul_le_mul_of_nonneg_left hΓb (norm_nonneg (Complex.Gamma z))
    have h2 := mul_le_mul_of_nonneg_left hΓa (norm_nonneg (Complex.Gamma (3 - z)))
    nlinarith only [h1, h2, hratio]
  have h1 : ‖(1 : ℂ) - z‖ ≤ |y| + 1 := by
    have h := Complex.norm_le_abs_re_add_abs_im ((1 : ℂ) - z)
    simp [z] at h
    have hh : |1 - a| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith only [h, hh]
  have h2 : ‖(2 : ℂ) - z‖ ≤ |y| + 1 := by
    have h := Complex.norm_le_abs_re_add_abs_im ((2 : ℂ) - z)
    simp [z] at h
    have hh : |2 - a| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith only [h, hh]
  have hn1 : (1 : ℂ) - z ≠ 0 := by
    intro hh
    have hi := congrArg Complex.im hh
    simp [z] at hi
    exact hy0 hi
  have hn2 : (2 : ℂ) - z ≠ 0 := by
    intro hh
    have hi := congrArg Complex.im hh
    simp [z] at hi
    exact hy0 hi
  have hg2 : Complex.Gamma (3 - z) = (2 - z) * Complex.Gamma (2 - z) := by
    convert Complex.Gamma_add_one (2 - z) hn2 using 1 <;> congr 1 <;> ring
  have hg1 : Complex.Gamma (2 - z) = (1 - z) * Complex.Gamma (1 - z) := by
    convert Complex.Gamma_add_one (1 - z) hn1 using 1 <;> congr 1 <;> ring
  have heq : Complex.Gamma z * Complex.Gamma (3 - z) =
      (2 - z) * (1 - z) * ((π : ℂ) / Complex.sin (π * z)) := by
    calc
      _ = (2 - z) * (1 - z) * (Complex.Gamma z * Complex.Gamma (1 - z)) := by
        rw [hg2, hg1]
        ring
      _ = _ := by rw [Complex.Gamma_mul_Gamma_one_sub]
  have hprod : ‖Complex.Gamma z‖ * ‖Complex.Gamma (3 - z)‖ =
      π * ‖1 - z‖ * ‖2 - z‖ / ‖Complex.sin (π * z)‖ := by
    rw [← norm_mul, heq, norm_mul, norm_mul, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos pi_pos]
    ring
  have him : ((π : ℂ) * z).im = π * y := by simp [z, Complex.mul_im]
  have himabs : |((π : ℂ) * z).im| = v := by
    rw [him, abs_mul, abs_of_pos pi_pos]
  have hv : 1 ≤ v := by dsimp [v]; nlinarith [pi_gt_three]
  have hs := sin_norm_exp_lower ((π : ℂ) * z) (by rw [himabs]; exact hv)
  rw [himabs] at hs
  have hsinv : 1 / ‖Complex.sin (π * z)‖ ≤ 3 * exp (-v) := by
    calc
      _ ≤ 1 / (exp v / 3) := one_div_le_one_div_of_le (by positivity) hs
      _ = _ := by rw [one_div_div, exp_neg]; ring
  have hp : ‖Complex.Gamma z‖ * ‖Complex.Gamma (3 - z)‖ ≤
      3 * π * (|y| + 1) ^ 2 * exp (-v) := by
    calc
      _ = π * ‖1 - z‖ * ‖2 - z‖ * (1 / ‖Complex.sin (π * z)‖) := by rw [hprod]; ring
      _ ≤ π * (|y| + 1) * (|y| + 1) * (3 * exp (-v)) := by gcongr
      _ = _ := by ring
  have hsquare : ‖Complex.Gamma z‖ ^ 2 ≤ 4 * π * (|y| + 1) ^ 2 * exp (-v) := by
    have hh := mul_le_mul_of_nonneg_left hr (norm_nonneg (Complex.Gamma z))
    nlinarith only [hh, hp]
  change ‖Complex.Gamma z‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hexp : exp (-(π / 2) * |y|) ^ 2 = exp (-v) := by
    rw [← exp_nat_mul]
    congr 1
    dsimp [v]
    ring
  rw [mul_pow, mul_pow, hexp]
  norm_num only [show (4 : ℝ) ^ 2 = 16 by norm_num]
  calc
    _ ≤ 4 * π * (|y| + 1) ^ 2 * exp (-v) := hsquare
    _ ≤ _ := by gcongr; linarith [pi_lt_four]

/-- The regularized Gaussian Mellin identity on the convergent half plane.
Source P0014 pages 31 to 33, the Gaussian factor of display 4.6.
The Gamma integral calculation follows Gaussian309 without its import cycle. -/
theorem gaussian_mellin_regularized (s : ℂ) (hs : 0 < s.re) :
    s * gaussianMellin 0 s = (2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2 + 1) := by
  have hclosed : gaussianMellin 0 s =
      (1 / 2 : ℂ) * (2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2) := by
    have hcomp := mellin_comp_rpow
      (fun t : ℝ => (exp (-(t / 2)) : ℂ)) s 2
    have hbase : mellin (fun t : ℝ => (exp (-(t / 2)) : ℂ)) (s / 2) =
        (2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2) := by
      have hg := Complex.integral_cpow_mul_exp_neg_mul_Ioi
        (a := s / 2) (r := (1 / 2 : ℝ)) (by simpa using half_pos hs) (by norm_num)
      simpa [mellin, smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg,
        Complex.ofReal_div, Complex.ofReal_mul, div_eq_mul_inv, mul_comm] using hg
    norm_num only [Complex.ofReal_ofNat] at hcomp
    rw [hbase] at hcomp
    have heq : gaussianMellin 0 s =
        mellin (fun t : ℝ => (exp (-(t ^ (2 : ℝ) / 2)) : ℂ)) s := by
      simp [gaussianMellin, e]
      congr 1
      funext t
      congr 1
      ring
    rw [heq, hcomp]
    norm_num [smul_eq_mul, mul_assoc]
  rw [hclosed, Complex.Gamma_add_one _ (by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith)]
  ring

/-- The raw Gaussian Mellin integral is not absolutely integrable on the boundary Re s = 0.
Source the convergence convention of Section 2.3 on page 8.
This states no value for its analytic continuation. -/
theorem gaussian_zero_re_not_integrable (s : ℂ) (hs : s.re = 0) :
    ¬ IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (s - 1) * (exp (-t ^ 2 / 2) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  intro hi
  have hsmall : IntegrableOn (fun t : ℝ => exp (-(1 / 2 : ℝ)) * t⁻¹)
      (Set.Ioo (0 : ℝ) 1) := by
    apply (hi.mono Set.Ioo_subset_Ioi_self le_rfl).norm.mono'
    · exact (measurable_const.mul measurable_id.inv).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1,
        Complex.norm_real]
      simp only [norm_inv, Real.norm_eq_abs,
        abs_of_pos (exp_pos (-(1 / 2 : ℝ))), abs_of_pos (exp_pos (-t ^ 2 / 2)),
        abs_of_pos ht.1, Complex.sub_re, Complex.one_re, hs, zero_sub, rpow_neg_one]
      have hsq : t ^ 2 ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ ht.1.le ht.2.le 2
      have he : exp (-(1 / 2 : ℝ)) ≤ exp (-t ^ 2 / 2) :=
        exp_le_exp.mpr (by linarith)
      calc
        _ = t⁻¹ * exp (-(1 / 2 : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr ht.1.le)
  have hpower : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioo (0 : ℝ) 1) :=
    (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (exp_pos _).ne') _).mp hsmall
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Set.Ioo (0 : ℝ) 1) := by
    simpa only [rpow_neg_one] using hpower
  have hfalse := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp hrpow
  exact (lt_irrefl (-1 : ℝ)) hfalse

end LeanLab.HelfgottMajor.Gamma503
