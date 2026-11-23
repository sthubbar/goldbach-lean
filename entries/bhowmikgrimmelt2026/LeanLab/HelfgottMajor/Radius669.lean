module

public import LeanLab.HelfgottMajor.DQSaddleSegmentBound

/-!
The second bound of P0014 Appendix A.33 follows from the saddle radius comparison.
Source P0014 pages 17 and 24, displays 3.32 and 3.61, and page 67, display A.33.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Radius669
open Real Decomp511a Decomp639Contour DQSaddleSegmentBound

/-- P0014 displays 3.32 and 3.61. The central saddle radius is at most the square root
of the absolute height, for every nonzero shift and height. -/
theorem saddleRadius_le_sqrt (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : 0 < |τ|) :
    saddleRadius δ τ ≤ sqrt |τ| := by
  set ρ := rho δ τ with hρdef
  have hρ : 0 < ρ := rho_pos δ τ hδ hτ
  have hu := ups_gt_one ρ hρ
  have hj : sqrt (1 + ρ ^ 2) ≤ 1 + ρ := by
    simpa only [Real.norm_eq_abs, abs_of_pos hρ] using sqrt_one_add_norm_sq_le ρ
  have hU : BookE.ups ρ ^ 2 = (1 + sqrt (1 + ρ ^ 2)) / 2 := by
    unfold BookE.ups
    rw [sq_sqrt (by positivity)]
  have hY0 : 0 ≤ BookE.ups ρ ^ 2 - BookE.ups ρ := by nlinarith
  have hY : 2 * (BookE.ups ρ ^ 2 - BookE.ups ρ) ≤ ρ := by nlinarith
  have hr0sq : saddleRadius δ τ ^ 2 =
      ell δ ^ 2 / 2 * (BookE.ups ρ ^ 2 - BookE.ups ρ) := by
    rw [saddleRadius, ← hρdef, mul_pow, div_pow, sq_sqrt hY0,
      sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hM := mul_le_mul_of_nonneg_left hY (sq_nonneg (ell δ))
  have hell := ell_sq_mul_rho δ τ hδ
  rw [← hρdef] at hell
  apply le_sqrt_of_sq_le
  rw [hr0sq]
  nlinarith only [hM, hell]

/-- P0014 page 67, second bound of display A.33. This half of the named numerical
input is elementary and needs no interval computation. -/
theorem a33_second (ρ : ℝ) (hρ : 0 < ρ) :
    (c0 ρ - 1 / sqrt 2) / (c1 ρ * sqrt ρ) ≤ 1 / 2 := by
  let τ : ℝ := π ^ 2 * ρ
  have ht : 0 < τ := mul_pos (sq_pos_of_pos pi_pos) hρ
  have hτ : 0 < |τ| := abs_pos.mpr ht.ne'
  have hd : (1 : ℝ) ≠ 0 := by norm_num
  have hρid : rho 1 τ = ρ := by
    simp only [rho, mul_one, abs_of_pos ht]
    dsimp only [τ]
    field_simp
  have hi : initialRadius 1 τ ≤ sqrt |τ| :=
    (saddleRadius_mem 1 τ hd hτ).1.trans (saddleRadius_le_sqrt 1 τ hd hτ)
  have hE := ell_mul_sqrt_rho 1 τ hd
  rw [hρid] at hE
  have hc := c1_pos ρ hρ
  have hL := ell_pos 1 hd
  have hs : 0 < sqrt ρ := sqrt_pos.mpr hρ
  have hst : sqrt |τ| ≠ 0 := (sqrt_pos.mpr hτ).ne'
  calc
    (c0 ρ - 1 / sqrt 2) / (c1 ρ * sqrt ρ) =
        initialRadius 1 τ / (ell 1 * sqrt ρ) := by
      rw [initialRadius, hρid]
      field_simp
      <;> ring
    _ ≤ sqrt |τ| / (ell 1 * sqrt ρ) := div_le_div_of_nonneg_right hi (by positivity)
    _ = 1 / 2 := by
      rw [hE]
      field_simp

end LeanLab.HelfgottMajor.Radius669
