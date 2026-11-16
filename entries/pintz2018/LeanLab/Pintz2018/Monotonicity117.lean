module

public import LeanLab.Pintz2018.Statements

/-!
Monotonicity statements in Pintz 2018, page 25 and page 43.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.Pintz2018.Monotonicity117

/-- Display 5.31 on page 25 and the comparison in 9.37 on page 43.
The normalized exponential tail is decreasing on the positive half line. -/
theorem exp_tail_antitone :
    AntitoneOn (fun x : ℝ => (1 - Real.exp (-x)) / x) (Set.Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  have h := convexOn_exp.secant_mono (a := 0) (x := -y) (y := -x)
    (by trivial) (by trivial) (by trivial) (by linarith : -y ≠ 0)
    (by linarith : -x ≠ 0) (neg_le_neg hxy)
  simpa only [Real.exp_zero, sub_zero, div_neg, ← neg_div, neg_sub] using h

/-- Display 5.33 on page 25. The normalized symmetric exponential difference is increasing.
The positive domain avoids the removable singularity at zero. -/
theorem exp_symmetric_monotone :
    MonotoneOn (fun x : ℝ => (Real.exp x - Real.exp (-x)) / x) (Set.Ioi 0) := by
  have hc : ConvexOn ℝ (Set.Ici 0) Real.sinh := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici _)
      Real.continuous_sinh.continuousOn
      (fun x hx => (Real.hasDerivAt_sinh x).hasDerivWithinAt)
      (fun x hx => (Real.hasDerivAt_cosh x).hasDerivWithinAt)
    intro x hx
    exact Real.sinh_nonneg_iff.mpr (interior_subset hx)
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  have h := hc.secant_mono (a := 0) (x := x) (y := y)
    (by simp) hx.le hy.le hx.ne' hy.ne' hxy
  simp only [Real.sinh_zero, sub_zero, Real.sinh_eq] at h
  convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

end LeanLab.Pintz2018.Monotonicity117
