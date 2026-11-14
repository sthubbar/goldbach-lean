module

public import Mathlib

/-!
P0083, pages 483 and 484. Explicit finite exponential kernel bounds.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Kernel
open Finset Complex Real

noncomputable section

/-- The paper uses e x = exp 2 pi i x. -/
def e (x : ℝ) : ℂ := Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ))

/-- The kernel on M consecutive integers starting at a. -/
def T (a M : ℕ) (x : ℝ) : ℂ := ∑ n ∈ range M, e (((a + n : ℕ) : ℝ) * x)

/-- The trivial kernel bound with explicit constant one, page 484. -/
theorem norm_T_le (a M : ℕ) (x : ℝ) : ‖T a M x‖ ≤ M := by
  calc ‖T a M x‖ ≤ ∑ n ∈ range M, ‖e (((a + n : ℕ) : ℝ) * x)‖ := norm_sum_le _ _
    _ = M := by simp [e, Complex.norm_exp]

/-- The reciprocal kernel bound on the central half period, page 484. -/
theorem norm_T_le_inv (a M : ℕ) {x : ℝ} (hx : x ≠ 0) (hhalf : |x| ≤ 1 / 2) :
    ‖T a M x‖ ≤ 1 / (2 * |x|) := by
  have he (n : ℕ) : e (((a + n : ℕ) : ℝ) * x) = e ((a : ℝ) * x) * e x ^ n := by
    unfold e
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hT : ‖T a M x‖ = ‖∑ n ∈ range M, e x ^ n‖ := by
    unfold T
    simp_rw [he]
    rw [← Finset.mul_sum, norm_mul]
    simp [e, Complex.norm_exp]
  have hden : 4 * |x| ≤ ‖e x - 1‖ := by
    unfold e
    rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hs := Real.mul_abs_le_abs_sin (x := Real.pi * x) (by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos])
    have hs' : 2 * |x| ≤ |Real.sin (Real.pi * x)| := by
      have heq : 2 / Real.pi * |Real.pi * x| = 2 * |x| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp
      rwa [heq] at hs
    have harg : 2 * Real.pi * x / 2 = Real.pi * x := by ring
    rw [harg]
    linarith
  have hnorm : ‖e x‖ = 1 := by simp [e, Complex.norm_exp]
  have hgeom : ‖∑ n ∈ range M, e x ^ n‖ * ‖e x - 1‖ ≤ 2 := by
    rw [← norm_mul, geom_sum_mul]
    calc ‖e x ^ M - 1‖ ≤ ‖e x ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hnorm]; norm_num
  rw [hT]
  apply (le_div_iff₀ (by positivity : 0 < 2 * |x|)).2
  have hn := norm_nonneg (∑ n ∈ range M, e x ^ n)
  have hmul := mul_le_mul_of_nonneg_left hden hn
  nlinarith

/-- The complete pointwise kernel bound using distance to the nearest integer. -/
theorem norm_T_le_min (a M : ℕ) {x : ℝ} (hx : x ≠ (round x : ℝ)) :
    ‖T a M x‖ ≤ min (M : ℝ) (1 / (2 * |x - (round x : ℝ)|)) := by
  have hp (n : ℕ) : e ((n : ℝ) * (x - (round x : ℝ))) = e ((n : ℝ) * x) := by
    have hi : Complex.exp (Complex.I * ((2 * Real.pi * ((n : ℝ) * (round x : ℝ)) : ℝ) : ℂ)) = 1 := by
      have harg : Complex.I * ((2 * Real.pi * ((n : ℝ) * (round x : ℝ)) : ℝ) : ℂ) =
          (((n : ℤ) * round x : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    unfold e
    have hsub : Complex.I * ((2 * Real.pi * ((n : ℝ) * (x - (round x : ℝ))) : ℝ) : ℂ) =
        Complex.I * ((2 * Real.pi * ((n : ℝ) * x) : ℝ) : ℂ) -
        Complex.I * ((2 * Real.pi * ((n : ℝ) * (round x : ℝ)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hsub, Complex.exp_sub, hi, div_one]
  have hperiod : T a M (x - (round x : ℝ)) = T a M x := by
    unfold T
    exact Finset.sum_congr rfl (fun n _ => hp (a + n))
  apply le_min (norm_T_le a M x)
  rw [← hperiod]
  exact norm_T_le_inv a M (sub_ne_zero.mpr hx) (abs_sub_round x)

/-- A one sided squared kernel tail with explicit constant, equation 17. -/
theorem integral_norm_T_sq_tail (a M : ℕ) {δ : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    (∫ x in δ..(1 / 2 : ℝ), ‖T a M x‖ ^ 2) ≤ 1 / (4 * δ) := by
  have hc : Continuous (fun x : ℝ => ‖T a M x‖ ^ 2) := by
    unfold T e
    fun_prop
  have hnz : (0 : ℝ) ∉ Set.uIcc δ (1 / 2) := by
    rw [Set.uIcc_of_le hhalf]
    simp only [Set.mem_Icc, not_and]
    intro h
    linarith
  have hg : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) MeasureTheory.volume δ (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    have hx0 : x ≠ 0 := by
      intro hz
      subst x
      exact hnz hx
    exact pow_ne_zero _ hx0
  have hb : (∫ x in δ..(1 / 2 : ℝ), ‖T a M x‖ ^ 2) ≤
      ∫ x in δ..(1 / 2 : ℝ), (1 / 4 : ℝ) * (x ^ 2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hhalf (hc.intervalIntegrable _ _) (hg.const_mul _)
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hδ hx.1
    have hkernel := norm_T_le_inv a M (ne_of_gt hx0) (by
      rw [abs_of_pos hx0]
      exact hx.2)
    have hsq := pow_le_pow_left₀ (norm_nonneg (T a M x)) hkernel 2
    rw [abs_of_pos hx0] at hsq
    convert hsq using 1
    field_simp
    norm_num
  have hz := integral_zpow (a := δ) (b := (1 / 2 : ℝ)) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, hnz⟩)
  norm_num [zpow_neg, zpow_ofNat] at hz
  rw [intervalIntegral.integral_const_mul, hz] at hb
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  calc (∫ x in δ..(1 / 2 : ℝ), ‖T a M x‖ ^ 2)
      ≤ 1 / 4 * (δ⁻¹ - 2) := by nlinarith [hb]
    _ ≤ 1 / (4 * δ) := by
      have heq : 1 / (4 * δ) = (1 / 4 : ℝ) * δ⁻¹ := by field_simp
      rw [heq]
      linarith

/-- The symmetric tail bound needed for the punctured major arcs, equation 17. -/
theorem integral_norm_T_sq_two_tails (a M : ℕ) {δ : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    (∫ x in (-1 / 2 : ℝ)..(-δ), ‖T a M x‖ ^ 2) +
      (∫ x in δ..(1 / 2 : ℝ), ‖T a M x‖ ^ 2) ≤ 1 / (2 * δ) := by
  have he (y : ℝ) : e (-y) = (starRingEnd ℂ) (e y) := by
    unfold e
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  have hnorm (x : ℝ) : ‖T a M (-x)‖ = ‖T a M x‖ := by
    have hconj : T a M (-x) = (starRingEnd ℂ) (T a M x) := by
      unfold T
      simp_rw [mul_neg, he]
      rw [map_sum]
    rw [hconj, Complex.norm_conj]
  have hsym : (∫ x in (-1 / 2 : ℝ)..(-δ), ‖T a M x‖ ^ 2) =
      ∫ x in δ..(1 / 2 : ℝ), ‖T a M x‖ ^ 2 := by
    have hc := intervalIntegral.integral_comp_neg (a := δ) (b := (1 / 2 : ℝ))
      (fun x => ‖T a M x‖ ^ 2)
    simp only [hnorm] at hc
    convert hc.symm using 1
    norm_num
  rw [hsym]
  have hb := integral_norm_T_sq_tail a M hδ hhalf
  have heq : 1 / (2 * δ) = 2 * (1 / (4 * δ)) := by ring
  rw [heq]
  linarith

/-- A full period squared kernel bound with explicit constant two, equation 17. -/
theorem integral_norm_T_sq_le_two_mul (a M : ℕ) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), ‖T a M x‖ ^ 2) ≤ 2 * M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [T]
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  let δ : ℝ := 1 / (2 * M)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith
  have hc : Continuous (fun x : ℝ => ‖T a M x‖ ^ 2) := by unfold T e; fun_prop
  have hcenter : (∫ x in (-δ)..δ, ‖T a M x‖ ^ 2) ≤ (M : ℝ) := by
    calc (∫ x in (-δ)..δ, ‖T a M x‖ ^ 2)
        ≤ ∫ _x in (-δ)..δ, (M : ℝ) ^ 2 := by
          apply intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
            intervalIntegrable_const
          intro x _
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_T_le a M x) 2
      _ = M := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        dsimp [δ]
        field_simp
        ring
  have ht := integral_norm_T_sq_two_tails a M hδ hhalf
  have heq : 1 / (2 * δ) = (M : ℝ) := by dsimp [δ]; field_simp
  rw [heq] at ht
  have hsplit : (∫ x in (-1 / 2 : ℝ)..(-δ), ‖T a M x‖ ^ 2) +
      (∫ x in (-δ)..δ, ‖T a M x‖ ^ 2) +
      (∫ x in δ..(1 / 2 : ℝ), ‖T a M x‖ ^ 2) =
      ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), ‖T a M x‖ ^ 2 := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  linarith

end
end LeanLab.Perelli1996.Kernel
