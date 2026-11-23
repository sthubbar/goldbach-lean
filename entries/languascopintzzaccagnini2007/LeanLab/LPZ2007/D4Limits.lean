module

public import Mathlib

/-!
P0045, preprint page 8, displays 20 and 21.
The period count has the same leading term with L replaced by floor of L minus sqrt L.
AI wrote this Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.LPZ2007.D4Limits

open Filter Topology Real

noncomputable section

/-- The square root is negligible relative to L. -/
theorem sqrt_div_tendsto : Tendsto (fun L : ℝ => √L / L) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hs : √L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  change (√L)⁻¹ = √L / L
  rw [inv_eq_one_div, div_eq_div_iff hs hL.ne']
  nlinarith [Real.sq_sqrt hL.le]

/-- The number of full periods divided by L tends to the reciprocal period. -/
theorem period_ratio_tendsto (ξ : ℕ) (hξ : 0 < ξ) :
    Tendsto (fun L : ℝ => ((⌊L - √L⌋₊ / ξ : ℕ) : ℝ) / L) atTop (𝓝 (1 / (ξ : ℝ))) := by
  have hξr : (0 : ℝ) < ξ := by exact_mod_cast hξ
  have hlo : Tendsto (fun L : ℝ => 1 / (ξ : ℝ) - (√L / L) / ξ - 1 / L)
      atTop (𝓝 (1 / (ξ : ℝ))) := by
    simpa only [zero_div, sub_zero] using
      ((tendsto_const_nhds (x := 1 / (ξ : ℝ))).sub
        (sqrt_div_tendsto.div_const (ξ : ℝ))).sub
        (show Tendsto (fun L : ℝ => 1 / L) atTop (𝓝 0) from
          tendsto_const_nhds.div_atTop tendsto_id)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hL0 : 0 < L := by linarith
    rw [← Nat.floor_div_natCast]
    have hf := Nat.lt_floor_add_one ((L - √L) / ξ)
    rw [le_div_iff₀ hL0]
    have he : (1 / (ξ : ℝ) - √L / L / ξ - 1 / L) * L = (L - √L) / ξ - 1 := by
      field_simp
    rw [he]; linarith
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hL0 : 0 < L := by linarith
    have hs : √L ≤ L := (Real.sqrt_le_left (by positivity)).2 (by nlinarith)
    rw [← Nat.floor_div_natCast, div_le_iff₀ hL0]
    calc (⌊(L - √L) / ξ⌋₊ : ℝ) ≤ (L - √L) / ξ := Nat.floor_le (by positivity)
      _ ≤ L / ξ := div_le_div_of_nonneg_right (by linarith [Real.sqrt_nonneg L]) hξr.le
      _ = 1 / (ξ : ℝ) * L := by ring

/-- Adding the final partial period does not change the limit. -/
theorem period_succ_ratio_tendsto (ξ : ℕ) (hξ : 0 < ξ) :
    Tendsto (fun L : ℝ => (((⌊L - √L⌋₊ / ξ : ℕ) : ℝ) + 1) / L)
      atTop (𝓝 (1 / (ξ : ℝ))) := by
  simpa only [add_div, add_zero] using
    (period_ratio_tendsto ξ hξ).add (show Tendsto (fun L : ℝ => 1 / L) atTop (𝓝 0) from
      tendsto_const_nhds.div_atTop tendsto_id)

/-- The two period endpoints give an error envelope independent of the residue. -/
theorem between_mul_error {a b c t j J : ℝ} (hj : 0 ≤ j) (hJ : j ≤ J)
    (hlo : a * j ≤ c) (hhi : c ≤ b * j) :
    |c - t * j| ≤ J * (|a - t| + |b - t|) := by
  have ha := neg_abs_le (a - t)
  have hb := le_abs_self (b - t)
  have h1 : -(j * (|a - t| + |b - t|)) ≤ c - t * j := by
    nlinarith [mul_nonneg hj (abs_nonneg (b - t)),
      mul_nonneg hj (show 0 ≤ a - t + |a - t| by linarith)]
  have h2 : c - t * j ≤ j * (|a - t| + |b - t|) := by
    nlinarith [mul_nonneg hj (abs_nonneg (a - t)),
      mul_nonneg hj (show 0 ≤ |b - t| - (b - t) by linarith)]
  exact (abs_le.2 ⟨h1, h2⟩).trans
    (mul_le_mul_of_nonneg_right hJ (by positivity))

/-- The error envelope for k periods tends to zero. -/
theorem period_error_tendsto (ξ k : ℕ) (hξ : 0 < ξ) :
    Tendsto (fun L : ℝ =>
      |(((⌊L - √L⌋₊ / ξ : ℕ) : ℝ) / L) ^ k - (1 / (ξ : ℝ)) ^ k| +
      |((((⌊L - √L⌋₊ / ξ : ℕ) : ℝ) + 1) / L) ^ k - (1 / (ξ : ℝ)) ^ k|)
      atTop (𝓝 0) := by
  simpa using (((period_ratio_tendsto ξ hξ).pow k).sub_const ((1 / (ξ : ℝ)) ^ k)).abs.add
    (((period_succ_ratio_tendsto ξ hξ).pow k).sub_const ((1 / (ξ : ℝ)) ^ k)).abs

end
end LeanLab.LPZ2007.D4Limits

