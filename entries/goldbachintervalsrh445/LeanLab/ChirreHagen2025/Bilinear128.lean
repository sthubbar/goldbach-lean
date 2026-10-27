module

public import Mathlib
public import LeanLab.ChirreHagen2025.ThetaPsi

/-!
T2, unit U-1145, PC run 20261020T0202Z-8791. Bilinear64.lean with 128 scales
`s_j = 1/2 + 7j/2048` in place of 64: the Abel constant drops from below 0.2312 to below 0.2300,
so under RH a Goldbach number lies in `(x, x + 9.95 log² x)` for every `x ≥ 2`, improving the
lab's 10. The proofs are the 64-scale proofs with the scales renamed, made by a script from
Bilinear64.lean. The continuous limit of this argument is about 9.89 with the 2.23 J_θ constant.
CONDITIONAL ON Chirre-Hagen Theorem 2, Schoenfeld 1976 under RH and the 4 · 10^18 even check.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025
open Real Chebyshev

/-- The scales: `s_j = 1/2 + 7 j / 2048` for `j ≤ 128`, then constant `15/16`. -/
noncomputable def s128 (j : ℕ) : ℝ := 1 / 2 + 7 * ((min j 128 : ℕ) : ℝ) / 2048

theorem s128_mono : Monotone s128 := by
  intro i j hij
  unfold s128
  have : ((min i 128 : ℕ) : ℝ) ≤ ((min j 128 : ℕ) : ℝ) := by exact_mod_cast min_le_min_right 128 hij
  linarith

theorem s128_bounds (j : ℕ) : 1 / 2 ≤ s128 j ∧ s128 j ≤ 15 / 16 := by
  unfold s128
  have h1 : ((min j 128 : ℕ) : ℝ) ≤ 128 := by exact_mod_cast min_le_right j 128
  have h0 : (0 : ℝ) ≤ ((min j 128 : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

/-- The step weights `2 (1 - s_j)²`. -/
noncomputable def wb128 (j : ℕ) : ℝ := 2 * (1 - s128 j) ^ 2

theorem wb128_antitone : Antitone wb128 := by
  intro i j hij
  unfold wb128
  have hi := s128_bounds i
  have hj := s128_bounds j
  have hm := s128_mono hij
  have : (1 - s128 j) ^ 2 ≤ (1 - s128 i) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  linarith

set_option maxRecDepth 4000 in
theorem Ub128_lt : abelSum wb128 (fun j => s128 j ^ 2) 128 < 0.2300 := by
  simp only [abelSum, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, s128, wb128]
  norm_num

theorem rhs_le_abel128 {x δ : ℝ} (hx : 32 ≤ x) (hδ : 0 < δ) :
    (∫ t in x / 16..x / 2, F δ t) / 2 + ∫ u in x / 2..15 * x / 16, 2 * ((x - u) / x) ^ 2 * F δ u
      ≤ abelSum wb128 (Gs δ x s128) 128 := by
  have hxpos : 0 < x := by linarith
  have iF : ∀ c d : ℝ, 0 ≤ c → c ≤ d → IntervalIntegrable (F δ) MeasureTheory.volume c d :=
    fun c d hc hcd => integrand_intervalIntegrable hδ hc hcd
  have hsb : ∀ j, 0 ≤ s128 j * x := fun j => by nlinarith [(s128_bounds j).1]
  have hsj : ∀ j, s128 j * x ≤ s128 (j + 1) * x := fun j => by
    nlinarith [s128_mono (Nat.le_succ j)]
  have hcw : Continuous fun u : ℝ => 2 * ((x - u) / x) ^ 2 := by fun_prop
  have iW : ∀ j, IntervalIntegrable (fun u => 2 * ((x - u) / x) ^ 2 * F δ u)
      MeasureTheory.volume (s128 j * x) (s128 (j + 1) * x) := fun j =>
    (iF _ _ (hsb j) (hsj j)).continuousOn_mul hcw.continuousOn
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun j => s128 j * x)
    (f := fun u => 2 * ((x - u) / x) ^ 2 * F δ u) (n := 128) (fun j _ => iW j)
  have e0 : s128 0 * x = x / 2 := by simp [s128]; ring
  have e128 : s128 128 * x = 15 * x / 16 := by simp [s128]; norm_num; ring
  simp only [e0, e128] at hsum
  have hpieces : (∫ u in x / 2..15 * x / 16, 2 * ((x - u) / x) ^ 2 * F δ u)
      ≤ ∑ j ∈ Finset.range 128, wb128 j * (Gs δ x s128 (j + 1) - Gs δ x s128 j) := by
    rw [← hsum]
    apply Finset.sum_le_sum
    intro j _
    have hb := s128_bounds j
    have hb1 := s128_bounds (j + 1)
    have hG : Gs δ x s128 (j + 1) - Gs δ x s128 j = ∫ u in s128 j * x..s128 (j + 1) * x, F δ u := by
      unfold Gs
      exact intervalIntegral.integral_interval_sub_left (iF 1 _ zero_le_one (by nlinarith))
        (iF 1 _ zero_le_one (by nlinarith))
    rw [hG, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (hsj j) (iW j) ((iF _ _ (hsb j) (hsj j)).const_mul _)
    intro u hu
    have hF0 : 0 ≤ F δ u := sq_nonneg _
    have h1 : (x - u) / x ≤ 1 - s128 j := by
      rw [div_le_iff₀ hxpos]; nlinarith [hu.1]
    have h0 : 0 ≤ (x - u) / x := div_nonneg (by nlinarith [hu.2]) hxpos.le
    have : ((x - u) / x) ^ 2 ≤ (1 - s128 j) ^ 2 := pow_le_pow_left₀ h0 h1 2
    unfold wb128
    nlinarith
  have hR1 : (∫ t in x / 16..x / 2, F δ t) / 2 ≤ wb128 0 * Gs δ x s128 0 := by
    have e : wb128 0 = 1 / 2 := by simp [wb128, s128]; norm_num
    rw [e]; unfold Gs; rw [e0]
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (iF 1 (x / 16) zero_le_one (by linarith)) (iF (x / 16) (x / 2) (by positivity) (by linarith))
    have h0 : 0 ≤ ∫ y in (1 : ℝ)..x / 16, F δ y :=
      intervalIntegral.integral_nonneg (by linarith) (fun y _ => sq_nonneg _)
    linarith
  unfold abelSum
  linarith


set_option maxHeartbeats 1000000 in
/-- The bilinear argument with any mean-square constant `c` at the scales `x/2 ≤ X ≤ x`. -/
theorem large_c_of128 {c H : ℝ} (hc0 : 0 ≤ c) (hH1 : 1 / 10 ≤ H) (hH : H ≤ 61.5)
    (hHc : c * 0.2300 < H * (20419 / 393216 - 123 / 400000)) (hT : ThetaRel)
    (x : ℝ) (hx : 1.1 * 10 ^ 18 ≤ x)
    (hJ : ∀ X : ℝ, x / 2 ≤ X → X ≤ x → Jtheta X (H * Real.log x ^ 2 / x)
      ≤ c * (H * Real.log x ^ 2 / x) * Real.log (2.0001 / (H * Real.log x ^ 2 / x)) ^ 2 * X ^ 2) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + H * Real.log x ^ 2 := by
  by_contra hno
  have hL : 41 ≤ Real.log x := log_ge_41 hx
  have hxpos : 0 < x := by linarith
  set h := H * Real.log x ^ 2 with hh
  have hδpos : 0 < h / x := div_pos (mul_pos (by linarith) (by positivity)) hxpos
  have hδle : h / x ≤ 1 / 10 ^ 13 := by
    have := threshold2 hx
    have : h / x ≤ 61.5 * Real.log x ^ 2 / x := by
      rw [hh]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
    linarith
  have hδx : h / x * x = h := by field_simp
  set δ := h / x with hδ
  have hint := bil_integrated (by linarith) hδpos hδx.le hno
  have hrhs := rhs_le_abel128 (x := x) (by linarith) hδpos
  -- Theorem 3 at the scales, Abel summation
  set K := c * δ * Real.log (2.0001 / δ) ^ 2 with hK
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hc0 hδpos.le) (sq_nonneg _)
  have hGB : ∀ j, Gs δ x s128 j ≤ x ^ 2 * K * s128 j ^ 2 := by
    intro j
    have hb := s128_bounds j
    have hX : 10 ^ 13 ≤ s128 j * x := by nlinarith
    have := hJ (s128 j * x) (by nlinarith) (by nlinarith)
    have e : Jtheta (s128 j * x) δ = Gs δ x s128 j := rfl
    rw [e] at this
    calc Gs δ x s128 j ≤ c * δ * Real.log (2.0001 / δ) ^ 2 * (s128 j * x) ^ 2 := this
      _ = x ^ 2 * K * s128 j ^ 2 := by rw [hK]; ring
  have hup := abelSum_mono wb128 (Gs δ x s128) (fun j => x ^ 2 * K * s128 j ^ 2)
    wb128_antitone (fun j => by unfold wb128; positivity) hGB 128
  have hfac : abelSum wb128 (fun j => x ^ 2 * K * s128 j ^ 2) 128
      = x ^ 2 * K * abelSum wb128 (fun j => s128 j ^ 2) 128 := by
    simp only [abelSum]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hfac] at hup
  have hxK : 0 ≤ x ^ 2 * K := mul_nonneg (by positivity) hK0
  have hup2 : abelSum wb128 (Gs δ x s128) 128 ≤ x ^ 2 * K * 0.2300 := by
    have := mul_le_mul_of_nonneg_left Ub128_lt.le hxK
    linarith
  -- the cross terms
  have hδ1 : δ ≤ 1 / 16 := by linarith
  have hδxle : δ * x ≤ x / 16 := by nlinarith
  have hA1 : (1 + δ) * (x / 16) ≤ x / 2 := by nlinarith
  have hA2 : (1 + δ) * (x / 2) ≤ 15 * x / 16 := by nlinarith
  have hA3 : (1 + δ) * (15 * x / 16) ≤ 2 * x := by nlinarith
  have hρ : ∀ u, x / 16 ≤ u → u ≤ (1 + δ) * (15 * x / 16) → |Rθ u| ≤ 2 * x / 10 ^ 5 := by
    intro u h1 h2
    have := hT u (by linarith)
    have hu2 : u ≤ 2 * x := by linarith
    unfold Rθ
    linarith [div_le_div_of_nonneg_right hu2 (by norm_num : (0 : ℝ) ≤ 10 ^ 5)]
  have hδs : δ ≤ 1 / 10 ^ 13 := hδle
  have hc1 := cross_bound (g := g1f x) (by unfold g1f; fun_prop) hδpos
    (by positivity : (0 : ℝ) < x / 16) hA1
    (fun u h1 h2 => hρ u h1 (by linarith)) (D := 10 * δ * x) (Gm := 2 * x)
    (fun u h1 h2 => g1_D hxpos hδpos (by nlinarith) (by linarith))
    (fun u h1 h2 => g1_abs hxpos (by linarith) (by linarith))
    (fun u h1 h2 => gk_abs hxpos hδpos (by linarith) (by linarith) h2 (g1f x)
      (fun t ht0 ht1 => g1_abs hxpos ht0 ht1))
  have hc2 := cross_bound (g := g2f x) (by unfold g2f; fun_prop) hδpos
    (by positivity : (0 : ℝ) < x / 2) hA2
    (fun u h1 h2 => hρ u (by linarith) h2) (D := 16 * δ * x) (Gm := 2 * x)
    (fun u h1 h2 => g2_D hxpos hδpos (by nlinarith) (by linarith))
    (fun u h1 h2 => g2_abs hxpos (by linarith) (by linarith))
    (fun u h1 h2 => gk_abs hxpos hδpos (by linarith) (by linarith) h2 (g2f x)
      (fun t ht0 ht1 => g2_abs hxpos ht0 ht1))
  have a1' := neg_abs_le (∫ t in x / 16..x / 2, g1f x t * Eθ δ t)
  have a2' := neg_abs_le (∫ u in x / 2..15 * x / 16, g2f x u * Eθ δ u)
  have b1 := mul_le_mul_of_nonneg_left hc1 hδpos.le
  have b2 := mul_le_mul_of_nonneg_left hc2 hδpos.le
  have c1 := mul_le_mul_of_nonneg_left a1' hδpos.le
  have c2 := mul_le_mul_of_nonneg_left a2' hδpos.le
  -- numerics, everything divided by δ x²
  set L := Real.log x with hLdef
  set u := Real.log (2.0001 / δ) with hu
  have hu0 : 0 ≤ u := Real.log_nonneg (by rw [le_div_iff₀ hδpos]; nlinarith)
  have huL : u ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [hδ, hh, div_div_eq_mul_div, div_le_iff₀ (mul_pos (by linarith) (by positivity))]
    have : (2.0001 : ℝ) ≤ H * L ^ 2 := by nlinarith
    nlinarith
  have hu2 : u ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hu0 huL 2
  have hdx : δ * x = H * L ^ 2 := by rw [hδ, hh]; field_simp
  have hD : 0 < δ * x ^ 2 := mul_pos hδpos (by positivity)
  have em : δ ^ 2 * (2 * ((x / 2) ^ 3 - (x / 16) ^ 3) / 3 - 2 / x * (((x / 2) ^ 4 - (x / 16) ^ 4) / 4))
      = (δ * x ^ 2) * (δ * x * (2 * ((1 / 2) ^ 3 - (1 / 16) ^ 3) / 3
        - 2 * (((1 / 2) ^ 4 - (1 / 16) ^ 4) / 4))) := by
    field_simp
  have ec : δ * (10 * δ * x * (2 * x / 10 ^ 5) * (x / 2 - x / 16)
        + 2 * x * (2 * x / 10 ^ 5) * (δ * (x / 2)) + 2 * x * (2 * x / 10 ^ 5) * (δ * (x / 16)))
      + δ * (16 * δ * x * (2 * x / 10 ^ 5) * (15 * x / 16 - x / 2)
        + 2 * x * (2 * x / 10 ^ 5) * (δ * (15 * x / 16)) + 2 * x * (2 * x / 10 ^ 5) * (δ * (x / 2)))
      = (δ * x ^ 2) * (δ * x * ((10 * 2 * (7 / 16) + 2 * 2 * (1 / 2) + 2 * 2 * (1 / 16)
        + 16 * 2 * (7 / 16) + 2 * 2 * (15 / 16) + 2 * 2 * (1 / 2)) / 10 ^ 5)) := by ring
  have hKx : x ^ 2 * K * 0.2300 = (δ * x ^ 2) * (c * 0.2300 * u ^ 2) := by rw [hK]; ring
  have key : (δ * x ^ 2) * (δ * x * (2 * ((1 / 2) ^ 3 - (1 / 16) ^ 3) / 3
        - 2 * (((1 / 2) ^ 4 - (1 / 16) ^ 4) / 4)))
      ≤ (δ * x ^ 2) * (c * 0.2300 * u ^ 2 + δ * x * ((10 * 2 * (7 / 16) + 2 * 2 * (1 / 2)
        + 2 * 2 * (1 / 16) + 16 * 2 * (7 / 16) + 2 * 2 * (15 / 16) + 2 * 2 * (1 / 2)) / 10 ^ 5)) := by
    rw [mul_add, ← em, ← hKx, ← ec]
    linarith only [hint, hrhs, hup2, b1, b2, c1, c2]
  have k2 := le_of_mul_le_mul_left key hD
  rw [hdx] at k2
  have hm : (2 * ((1 / 2 : ℝ) ^ 3 - (1 / 16) ^ 3) / 3 - 2 * (((1 / 2) ^ 4 - (1 / 16) ^ 4) / 4))
      = 20419 / 393216 := by norm_num
  have hc : ((10 * 2 * (7 / 16) + 2 * 2 * (1 / 2) + 2 * 2 * (1 / 16) + 16 * 2 * (7 / 16)
      + 2 * 2 * (15 / 16) + 2 * 2 * (1 / 2)) / 10 ^ 5 : ℝ) = 123 / 400000 := by norm_num
  rw [hm, hc] at k2
  have hL2 : 0 < L ^ 2 := by positivity
  have hfin : c * 0.2300 * u ^ 2 ≤ c * 0.2300 * L ^ 2 :=
    mul_le_mul_of_nonneg_left hu2 (mul_nonneg hc0 (by norm_num))
  nlinarith [k2, hfin, hL2, hHc]


theorem goldbach_995
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 9.95 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 0.69 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2'⟩ := small_of hE x hx hs
    exact ⟨n, hn, h1, by nlinarith⟩
  · have hx' : 1.1 * 10 ^ 18 ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hL : 41 ≤ Real.log x := log_ge_41 hx'
    set δ := 9.94 * Real.log x ^ 2 / x with hδ
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
      have e0 : δ * √x * √x = 9.94 * Real.log x ^ 2 := by
        rw [mul_assoc, hss, hδ]; field_simp
      have e : δ * √x = 9.94 * (Real.log x ^ 2 / √x) := by
        rw [show 9.94 * (Real.log x ^ 2 / √x) = 9.94 * Real.log x ^ 2 / √x by ring,
          eq_div_iff hsx0.ne']
        exact e0
      have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith
      have : Real.log x ^ 2 / √x ≤ 7.5 / 10 ^ 5 :=
        le_trans (div_le_div_of_nonneg_right h23 hsx0.le) hc
      rw [e]; linarith
    obtain ⟨n, hn, h1, h2'⟩ := large_c_of128 (c := 2.23) (H := 9.94) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (thetaRel_of_schoenfeld (hS hRH)) x hx'
      (fun X hX1 hX2 => by
        rw [← hδ]
        have hX : 5 * 10 ^ 17 ≤ X := by linarith
        have hsX : δ * √X < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX2) hδpos.le) hsx
        exact Jtheta_le_223 (h2 hRH X δ (by linarith) hδpos hδ13) hX hδpos hδ13 hsX)
    exact ⟨n, hn, h1, by nlinarith⟩

end LeanLab.ChirreHagen2025

