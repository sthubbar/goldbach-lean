module

public import Mathlib
public import LeanLab.ChirreHagen2025.Weighted

/-!
P0075 line, T2, unit U-1348, I-5171, PC run 20261021T0403Z-14344, 2026-10-21.
The Abel step of the new Section 5 weight of U1348Bilinear.lean: scales
`s_j = 6/11 + (309/704) j/256` from `6/11` to `63/64`, step weights `(121/50)(1 - s_j)²`, which is
the weight `ψ(x - u)²/2` of `ψ(t) = 11 t/(5 x)` at the left end of each step, and `1/2` at `s_0`.
The Abel constant is below `0.24922`. Pure arithmetic, no hypothesis.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.U1348
open Real

/-- The scales `s_j = 6/11 + 309 j / 180224` for `j ≤ 256`, then constant `63/64`. -/
noncomputable def sc (j : ℕ) : ℝ := 6 / 11 + 309 * ((min j 256 : ℕ) : ℝ) / 180224

theorem sc_mono : Monotone sc := by
  intro i j hij
  unfold sc
  have : ((min i 256 : ℕ) : ℝ) ≤ ((min j 256 : ℕ) : ℝ) := by
    exact_mod_cast min_le_min_right 256 hij
  linarith

theorem sc_bounds (j : ℕ) : 6 / 11 ≤ sc j ∧ sc j ≤ 63 / 64 := by
  unfold sc
  have h1 : ((min j 256 : ℕ) : ℝ) ≤ 256 := by exact_mod_cast min_le_right j 256
  have h0 : (0 : ℝ) ≤ ((min j 256 : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor <;> nlinarith

theorem sc_zero : sc 0 = 6 / 11 := by norm_num [sc]

theorem sc_top : sc 256 = 63 / 64 := by norm_num [sc]

/-- The step weights `(121/50) (1 - s_j)²`. -/
noncomputable def wc (j : ℕ) : ℝ := 121 / 50 * (1 - sc j) ^ 2

theorem wc_zero : wc 0 = 1 / 2 := by rw [wc, sc_zero]; norm_num

theorem wc_nonneg (j : ℕ) : 0 ≤ wc j := by unfold wc; positivity

theorem wc_antitone : Antitone wc := by
  intro i j hij
  unfold wc
  have hi := sc_bounds i
  have hj := sc_bounds j
  have hm := sc_mono hij
  have : (1 - sc j) ^ 2 ≤ (1 - sc i) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  linarith

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Uc_lt : abelSum wc (fun j => sc j ^ 2) 256 < 0.24922 := by
  simp only [abelSum, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, sc, wc]
  norm_num

end LeanLab.ChirreHagen2025.U1348
