module

public import Mathlib
public import LeanLab.ChirreHagen2025.Bilinear128

/-!
P0075 line, T2, unit U-6352, CLOUD 20261020T1125Z-cloud41, 2026-10-20. The downstream half of
I-5170: if, under RH, `J_ψ(x, δ) ≤ 1.2913 δ log²(2.0001/δ) x²` for `x ≥ 10^13` and
`0 < δ ≤ 10^-13`, Chirre-Hagen's Theorem 2 with 1.2913 in place of 2.2258, then the lab's
bilinear Section 5 gives a Goldbach number in `(x, x + 5.78 log² x)` for every `x ≥ 3`; at `x = 2` it fails,
since 6 is the least sum of two odd primes and 2 + 5.78 log² 2 < 4.78.
`Jtheta_le_of_c` is `Jtheta_le_223` of ThetaPsi.lean with the constant as a parameter, and
`goldbach_578_of_smooth` is `goldbach_995` of Bilinear128.lean with H = 5.77, by a script.
The J_ψ input is NOT proved here; I-5170 derives it on paper from the same zero inputs as
the paper with the weight W(u) = min(1, u^-4) in place of the averaging over ν.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025
open Real Chebyshev Finset

theorem Jtheta_le_of_c {c X δ : ℝ} (hc : 0 ≤ c)
    (h2 : Jpsi X δ ≤ c * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2)
    (hX : 5 * 10 ^ 17 ≤ X) (hδ : 0 < δ) (hδ13 : δ ≤ 1 / 10 ^ 13) (hs : δ * √X < 1) :
    Jtheta X δ ≤ (1.001 * c + 0.0019) * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2 := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hk : 1 + δ ≤ 2 := by linarith
  have hstep1 := Jtheta_le_Jpsi (η := 1 / 1000) hX1 hδ (by norm_num)
  set M := Real.log ((1 + δ) * X) ^ 2 / Real.log 2 with hM
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDle : ∀ y, 1 ≤ y → y ≤ X → Dpt δ y ≤ M := by
    intro y hy1 hyX
    have hsy : δ * √y < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hyX) hδ.le) hs
    refine (Dpt_le hy1 hδ hsy).trans ?_
    apply div_le_div_of_nonneg_right _ hl2.le
    apply pow_le_pow_left₀ (Real.log_nonneg (by nlinarith))
    exact Real.log_le_log (by nlinarith) (by nlinarith)
  have hD2 : ∫ y in (1 : ℝ)..X, Dpt δ y ^ 2 ≤ ∫ y in (1 : ℝ)..X, M * Dpt δ y := by
    apply intervalIntegral.integral_mono_on hX1 (Dpt_sq_ii hδ zero_le_one hX1)
      ((Dpt_ii hδ 1 X).const_mul M)
    intro y hy
    have h0 := Dpt_nonneg hδ.le (by linarith [hy.1] : (0 : ℝ) ≤ y)
    have h1 := hDle y hy.1 hy.2
    nlinarith
  rw [intervalIntegral.integral_const_mul] at hD2
  have hID := intD_le (by linarith : (2 : ℝ) ≤ X) hδ (by linarith)
  have hkX1 : 1 ≤ (1 + δ) * X := by nlinarith
  have hf := psi_sub_theta_le hkX1
  have hfpt : fpt ((1 + δ) * X) ≤ 2 * √((1 + δ) * X) * Real.log ((1 + δ) * X) := hf
  -- bound everything by y = 2X
  set y := 2 * X with hy
  have hkXy : (1 + δ) * X ≤ y := by nlinarith
  have hly : Real.log ((1 + δ) * X) ≤ Real.log y := Real.log_le_log (by linarith) hkXy
  have hl0 : 0 ≤ Real.log ((1 + δ) * X) := Real.log_nonneg hkX1
  have hsqy : √((1 + δ) * X) ≤ √y := Real.sqrt_le_sqrt hkXy
  have hM0 : 0 ≤ M := by positivity
  have hMy : M ≤ Real.log y ^ 2 / Real.log 2 :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hl0 hly 2) hl2.le
  have hfy : fpt ((1 + δ) * X) ≤ 2 * √y * Real.log y := by
    refine hfpt.trans ?_
    have : 0 ≤ √((1 + δ) * X) := Real.sqrt_nonneg _
    have hly0 : 0 ≤ Real.log y := le_trans hl0 hly
    nlinarith [mul_le_mul hsqy hly hl0 (Real.sqrt_nonneg _)]
  have hint0 : 0 ≤ ∫ y in (1 : ℝ)..X, Dpt δ y :=
    intervalIntegral.integral_nonneg hX1 (fun t ht => Dpt_nonneg hδ.le (by linarith [ht.1]))
  -- ∫ D² ≤ (log² y / log 2) · δ X · 2 √y log y
  have hD2' : ∫ y in (1 : ℝ)..X, Dpt δ y ^ 2
      ≤ Real.log y ^ 2 / Real.log 2 * (δ * X * (2 * √y * Real.log y)) := by
    have a1 : M * (∫ y in (1 : ℝ)..X, Dpt δ y) ≤ M * (δ * X * fpt ((1 + δ) * X)) :=
      mul_le_mul_of_nonneg_left hID hM0
    have a2 : δ * X * fpt ((1 + δ) * X) ≤ δ * X * (2 * √y * Real.log y) :=
      mul_le_mul_of_nonneg_left hfy (by positivity)
    have a3 : 0 ≤ δ * X * (2 * √y * Real.log y) := le_trans
      (mul_nonneg (by positivity) (fpt_nonneg _)) a2
    have a4 := mul_le_mul hMy a2 (mul_nonneg (by positivity) (fpt_nonneg _))
      (by positivity : (0 : ℝ) ≤ Real.log y ^ 2 / Real.log 2)
    linarith
  -- numerics: log³ y / √y ≤ 7.5e-5, log 2 ≥ 0.69, L ≥ 30
  have hcube := log_cube_div_sqrt (by rw [hy]; linarith : (10 : ℝ) ^ 18 ≤ y)
  have hy0 : 0 < y := by linarith
  have hsy0 : 0 < √y := Real.sqrt_pos.mpr hy0
  have hcube' : Real.log y ^ 3 ≤ 7.5 / 10 ^ 5 * √y := by rwa [div_le_iff₀ hsy0] at hcube
  have hsyy : √y * √y = y := Real.mul_self_sqrt hy0.le
  have hl2' : 0.69 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  set L := Real.log (2.0001 / δ) with hL
  have hL30 : 30 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 30 ≤ 2 * 10 ^ 13 := by
      have h1 : Real.exp 1 ^ 30 ≤ (2.7182818286 : ℝ) ^ 30 := by
        gcongr; exact Real.exp_one_lt_d9.le
      rw [← Real.exp_nat_mul] at h1; norm_num at h1 ⊢; linarith
    have : 2 * 10 ^ 13 ≤ 2.0001 / δ := by
      rw [le_div_iff₀ hδ]; nlinarith
    linarith
  -- the D² part is at most 0.0019 δ L² X²
  have hpart : (1 + 1 / (1 / 1000)) * (Real.log y ^ 2 / Real.log 2 * (δ * X * (2 * √y * Real.log y)))
      ≤ 0.0019 * δ * L ^ 2 * X ^ 2 := by
    have e : (1 + 1 / (1 / 1000)) * (Real.log y ^ 2 / Real.log 2 * (δ * X * (2 * √y * Real.log y)))
        = 2002 * δ * X * (Real.log y ^ 3 * √y) / Real.log 2 := by
      field_simp; ring
    rw [e, div_le_iff₀ hl2]
    have h1 : Real.log y ^ 3 * √y ≤ 7.5 / 10 ^ 5 * y := by
      have := mul_le_mul_of_nonneg_right hcube' hsy0.le
      rw [mul_assoc, hsyy] at this; exact this
    have h2' : 2002 * δ * X * (Real.log y ^ 3 * √y) ≤ 2002 * δ * X * (7.5 / 10 ^ 5 * y) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have hL2 : 900 ≤ L ^ 2 := by nlinarith
    have hdX0 : 0 ≤ δ * X ^ 2 := by positivity
    have h3a : 900 * 0.69 ≤ L ^ 2 * Real.log 2 :=
      mul_le_mul hL2 hl2' (by norm_num) (by positivity)
    have h5 := mul_le_mul_of_nonneg_left h3a (by positivity : (0 : ℝ) ≤ 0.0019 * (δ * X ^ 2))
    have h3 : 0.0019 * δ * L ^ 2 * X ^ 2 * Real.log 2 = 0.0019 * (δ * X ^ 2) * (L ^ 2 * Real.log 2) := by
      ring
    have h4 : 2002 * δ * X * (7.5 / 10 ^ 5 * (2 * X)) = 0.3003 * (δ * X ^ 2) := by ring
    rw [hy] at h2'
    rw [h3]
    linarith
  have hJ1 : (1 + 1 / 1000) * Jpsi X δ ≤ (1 + 1 / 1000) * (c * δ * L ^ 2 * X ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  have hD2'' := mul_le_mul_of_nonneg_left hD2' (by norm_num : (0 : ℝ) ≤ 1 + 1 / (1 / 1000))
  have e1 : (1 + 1 / 1000) * (c * δ * L ^ 2 * X ^ 2) + 0.0019 * δ * L ^ 2 * X ^ 2
      = (1.001 * c + 0.0019) * δ * L ^ 2 * X ^ 2 := by ring
  linarith


theorem goldbach_578_of_smooth
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.2913 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 5.78 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2'⟩ := small_of hE x (by linarith) hs
    exact ⟨n, hn, h1, by nlinarith⟩
  · have hx' : 1.1 * 10 ^ 18 ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hL : 41 ≤ Real.log x := log_ge_41 hx'
    set δ := 5.77 * Real.log x ^ 2 / x with hδ
    have hδpos : 0 < δ := by positivity
    have hδ13 : δ ≤ 1 / 10 ^ 13 := by
      have := threshold2 hx'
      have : δ ≤ 61.5 * Real.log x ^ 2 / x := by
        rw [hδ]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
      linarith
    have hsx : δ * √x < 1 := by
      have hc := log_cube_div_sqrt (by linarith : (10 : ℝ) ^ 18 ≤ x)
      have hsx0 : 0 < √x := Real.sqrt_pos.mpr hxpos
      have hss : √x * √x = x := Real.mul_self_sqrt hxpos.le
      have e0 : δ * √x * √x = 5.77 * Real.log x ^ 2 := by
        rw [mul_assoc, hss, hδ]; field_simp
      have e : δ * √x = 5.77 * (Real.log x ^ 2 / √x) := by
        rw [show 5.77 * (Real.log x ^ 2 / √x) = 5.77 * Real.log x ^ 2 / √x by ring,
          eq_div_iff hsx0.ne']
        exact e0
      have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith
      have : Real.log x ^ 2 / √x ≤ 7.5 / 10 ^ 5 :=
        le_trans (div_le_div_of_nonneg_right h23 hsx0.le) hc
      rw [e]; linarith
    obtain ⟨n, hn, h1, h2'⟩ := large_c_of128 (c := 1.001 * 1.2913 + 0.0019) (H := 5.77) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (thetaRel_of_schoenfeld (hS hRH)) x hx'
      (fun X hX1 hX2 => by
        rw [← hδ]
        have hX : 5 * 10 ^ 17 ≤ X := by linarith
        have hsX : δ * √X < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX2) hδpos.le) hsx
        exact Jtheta_le_of_c (by norm_num) (h2 hRH X δ (by linarith) hδpos hδ13) hX hδpos hδ13 hsX)
    exact ⟨n, hn, h1, by nlinarith⟩

end LeanLab.ChirreHagen2025

