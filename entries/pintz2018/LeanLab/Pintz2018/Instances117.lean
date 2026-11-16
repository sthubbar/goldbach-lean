module

public import LeanLab.Pintz2018.Density117
public import LeanLab.Pintz2018.Residual117

/-!
Nonempty instances for the task117 proof models.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.Pintz2018.Instances117

/-- A nonempty feasible instance of the Theorem J algebra, page 33, display 8.2. -/
theorem vacuityJ_nonempty : TheoremJ_bound (fun _ => (1 / 2 : ℝ)) 0 0 (1 / 2) := by
  apply Decomp117.theoremJ_bound_of_leaves
    (fun _ => (1 / 2 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (1 / 2 : ℝ)) 0 0 (1 / 2) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro L; norm_num
  · intro L; norm_num
  · intro L; norm_num

/-- A genuine two-coordinate capped maximum in the original exponential coordinates.
Source: Theorem K model, pages 34 and 35. -/
theorem vacuityK_original : TheoremK_OptimalChoice 2
    (fun _ => Real.log 2) (fun _ => Real.log 2) := by
  apply Greedy117.theoremK_ordered_integral 2 2
    (fun _ => Real.log 2) (fun _ => Real.log 2) (fun _ => 0) 1 2 0 0
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · fun_prop
  · intro v hv; norm_num
  · norm_num
  · intro i hi j hj hij; exact le_rfl
  · intro i hi j hj hij; exact le_rfl
  · intro j hj
    exact ⟨Real.log_nonneg (by norm_num), le_rfl⟩
  · exact Real.log_pos (by norm_num)
  · intro j hj hrj; simp only [Set.mem_Icc] at hj; omega
  · simp
  · intro x hx hxm hxb
    apply Finset.sum_le_sum
    intro j hj
    simp only [zero_mul, Real.exp_zero]
    exact sub_le_sub_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hx j hj).2 (by norm_num : (0 : ℝ) ≤ 2))) 1

/-- A nonempty scalar instance of the full prefix and residual assembly.
Source: page 18, displays 4.41 and 4.42. -/
theorem vacuity_residual :
    TheoremK_OptimalChoice 1 (fun _ => (2 : ℝ)) (fun _ => (3 : ℝ)) ∧
      (∑ j ∈ Finset.Icc 1 1, ((2 : ℝ) - 1)) = 1 ∧
      (2 : ℝ) - 1 = 1 - ∑ j ∈ Finset.Icc 1 (1 - 1), ((3 : ℝ) - 1) := by
  apply Residual117.saturation_and_residual 1 1 (fun _ => (2 : ℝ)) (fun _ => (3 : ℝ))
    (fun x => x - 1) (fun x => x ^ (2 : ℝ) - x ^ (0 : ℝ)) 1
  · norm_num
  · norm_num
  · refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith
  · intro x hx; fun_prop
  · exact Curvature117.objective_strictConvex 2 0 (by norm_num) (by norm_num) (by norm_num)
  · exact Curvature117.objective_strictMono 2 0 (by norm_num) (by norm_num) (by norm_num)
  · intro i hi j hj hij; exact le_rfl
  · intro i hi j hj hij; exact le_rfl
  · intro j hj; norm_num
  · norm_num
  · intro j hj hjr; simp only [Set.mem_Icc] at hj; omega
  · exact ⟨1, by norm_num, by norm_num⟩
  · norm_num
  · intro z hz hzm hzb
    have hz1 : 1 ≤ z 1 := (hz 1 (by norm_num)).1
    have hz2 : z 1 ≤ 2 := by
      have h : z 1 - 1 ≤ 1 := by simpa using hzb
      linarith
    have hsq : (z 1) ^ 2 ≤ (2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (by linarith) (by norm_num)).mpr hz2
    norm_num at hsq ⊢
    linarith

end LeanLab.Pintz2018.Instances117
