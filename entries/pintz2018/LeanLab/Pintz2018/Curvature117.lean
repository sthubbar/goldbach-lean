module

public import LeanLab.Pintz2018.Ordered117

/-!
Curvature inputs in Pintz 2018, pages 34 and 35, displays 8.10 to 8.13.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.Pintz2018.Curvature117
open MeasureTheory

/-- Nonnegative continuous weights of the powers y to v give a concave cost.
Source: page 35, display 8.11. The weight absorbs T f of v T and exp of minus d0 v T. -/
theorem integral_cost_concave (w : ℝ → ℝ)
    (hw : ContinuousOn w (Set.Icc 0 1)) (hw0 : ∀ v ∈ Set.Icc 0 1, 0 ≤ w v) :
    ConcaveOn ℝ (Set.Ici 1) (fun y : ℝ => ∫ v in Set.Icc (0 : ℝ) 1, w v * y ^ v) := by
  apply integral_concaveOn_of_integrand_ae (convex_Ici _)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hc := (Real.concaveOn_rpow hv.1 hv.2).subset
      (show Set.Ici (1 : ℝ) ⊆ Set.Ici 0 by intro x hx; exact le_trans zero_le_one (Set.mem_Ici.mp hx))
      (convex_Ici _)
    simpa only [smul_eq_mul] using ConcaveOn.smul (hw0 v hv) hc
  · intro y hy
    have hy1 : (1 : ℝ) ≤ y := Set.mem_Ici.mp hy
    exact (hw.mul (Real.continuous_const_rpow (by linarith : y ≠ 0)).continuousOn).integrableOn_Icc

/-- The second derivative in display 8.13 is positive for the strict range b greater than one.
Source: page 35, display 8.13, using B greater than T from page 17, display 4.35. -/
theorem objective_second_derivative_pos (b c y : ℝ) (hb : 1 < b)
    (hc : 0 ≤ c) (hcb : c < b) (hy : 1 ≤ y) :
    0 < b * (b - 1) * y ^ (b - 2) - c * (c - 1) * y ^ (c - 2) := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hpow : 0 < y ^ (b - 2) := Real.rpow_pos_of_pos hy0 _
  by_cases hc1 : c ≤ 1
  · have hmain : 0 < b * (b - 1) * y ^ (b - 2) := by positivity
    have hsub : c * (c - 1) * y ^ (c - 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hc (by linarith)) (Real.rpow_nonneg hy0.le _)
    linarith
  · have hc1' : 1 < c := lt_of_not_ge hc1
    have hcoeff : c * (c - 1) < b * (b - 1) := by nlinarith
    have hexp : y ^ (c - 2) ≤ y ^ (b - 2) :=
      Real.rpow_le_rpow_of_exponent_le hy (by linarith)
    have h1 := mul_lt_mul_of_pos_right hcoeff hpow
    have h2 := mul_le_mul_of_nonneg_left hexp (mul_nonneg hc (by linarith : 0 ≤ c - 1))
    linarith

/-- Strict convexity of the objective in the range B greater than T.
Source: page 35, display 8.13, with page 17, display 4.35. -/
theorem objective_strictConvex (b c : ℝ) (hb : 1 < b) (hc : 0 ≤ c) (hcb : c < b) :
    StrictConvexOn ℝ (Set.Ici 1) (fun y : ℝ => y ^ b - y ^ c) := by
  have hfirst : ∀ x ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun y : ℝ => y ^ b - y ^ c)
        (b * x ^ (b - 1) - c * x ^ (c - 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by have : (1 : ℝ) ≤ x := hx; linarith
    exact (Real.hasDerivAt_rpow_const (p := b) (Or.inl hx0)).sub
      (Real.hasDerivAt_rpow_const (p := c) (Or.inl hx0))
  have hsecond : ∀ x ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun y : ℝ => b * y ^ (b - 1) - c * y ^ (c - 1))
        (b * (b - 1) * x ^ (b - 2) - c * (c - 1) * x ^ (c - 2)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by have : (1 : ℝ) ≤ x := hx; linarith
    convert ((Real.hasDerivAt_rpow_const (p := b - 1) (Or.inl hx0)).const_mul b).sub
      ((Real.hasDerivAt_rpow_const (p := c - 1) (Or.inl hx0)).const_mul c) using 1; ring_nf
  have hm : StrictMonoOn (fun y : ℝ => b * y ^ (b - 1) - c * y ^ (c - 1)) (Set.Ici 1) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici _)
      (fun x hx => (hsecond x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hsecond x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    exact objective_second_derivative_pos b c x hb hc hcb (interior_subset hx)
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici _)
    (fun x hx => (hfirst x hx).continuousAt.continuousWithinAt)
  intro x hx y hy hxy
  rw [(hfirst x (interior_subset hx)).deriv, (hfirst y (interior_subset hy)).deriv]
  exact hm (interior_subset hx) (interior_subset hy) hxy

/-- The continuous weighted integral cost is continuous at every y at least one.
Source: page 35, display 8.11, with the continuous weight from Condition 1 on page 14. -/
theorem integral_cost_continuousAt (w : ℝ → ℝ) (hw : Continuous w) (y : ℝ) (hy : 1 ≤ y) :
    ContinuousAt (fun x : ℝ => ∫ v in Set.Icc (0 : ℝ) 1, w v * x ^ v) y := by
  have hc : Continuous (fun x : ℝ => ∫ v in Set.Icc (0 : ℝ) 1,
      w v * (max (1 / 2 : ℝ) x) ^ v) := by
    apply continuous_parametric_integral_of_continuous ?_ isCompact_Icc
    change Continuous (fun p : ℝ × ℝ => w p.2 * (max (1 / 2 : ℝ) p.1) ^ p.2)
    apply (hw.comp continuous_snd).mul
    apply (continuous_const.max continuous_fst).rpow continuous_snd
    intro p
    left
    have := le_max_left (1 / 2 : ℝ) p.1
    linarith
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (1 / 2 : ℝ) < y by linarith)] with x hx
  rw [max_eq_right hx.le]

/-- The objective in 8.10 is strictly increasing on the positive box.
Source: page 35, the maximizing argument after display 8.16. -/
theorem objective_strictMono (b c : ℝ) (hb : 1 < b) (hc : 0 ≤ c) (hcb : c < b) :
    StrictMonoOn (fun y : ℝ => y ^ b - y ^ c) (Set.Ici 1) := by
  have hd : ∀ x ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun y : ℝ => y ^ b - y ^ c)
        (b * x ^ (b - 1) - c * x ^ (c - 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by have : (1 : ℝ) ≤ x := hx; linarith
    exact (Real.hasDerivAt_rpow_const (p := b) (Or.inl hx0)).sub
      (Real.hasDerivAt_rpow_const (p := c) (Or.inl hx0))
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici _)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := interior_subset hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hp := Real.rpow_le_rpow_of_exponent_le hx1 (show c - 1 ≤ b - 1 by linarith)
  have h1 := mul_lt_mul_of_pos_right hcb (Real.rpow_pos_of_pos hx0 (b - 1))
  have h2 := mul_le_mul_of_nonneg_left hp hc
  linarith

end LeanLab.Pintz2018.Curvature117
