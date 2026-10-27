module

public import LeanLab.HardyLittlewood1923.U1438TheoremA

/-!
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T1603Z-28836, unit U-1444, paper P0004.

# Hardy-Littlewood 1923, Theorem A as printed, p. 21 to 22, eq. (3.113) and (3.114)

Printed: if `r ≥ 3` then, on Hypothesis R with its `Θ < 3/4`,
`ν_r(n) = n^{r-1}/(r-1)! S_r + O(n^{r-1+(Θ-3/4)} (log n)^B)`,
`S_r = Σ_{q ≥ 1} (μ(q)/φ(q))^r c_q(-n)`, the `O` constants depending on `r` alone.

* `singR r n`: the printed `S_r`, with `c_q(-n) = c_q(n)`, (3.212), in the divisor form (3.214);
  `singR_three : singR 3 = sing3`.
* `printedA3Bound Θ`: the printed error bound for `r = 3` at level `Θ`.
* `printedA3_stmt`: Theorem A for `r = 3` exactly as printed, conditional on `NoZerosRight Θ`.
* `printedA_stmt r`: the same for general `r`, the main term `n^{r-1}/(r-1)! S_r`.
* `theoremA3_of_printed`: `printedA3_stmt → HypothesisR → theoremA3_stmt`, PROVED.
* `printedA3Bound_form`: the bound form holds at `Θ = 7/4`, from `theoremA3_main`, PROVED.

Every proof is complete. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1444

open Real Filter Asymptotics
open scoped ArithmeticFunction.Moebius
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1438

/-- The printed singular series (3.114), `S_r = Σ_q (μ(q)/φ(q))^r c_q(n)`. -/
noncomputable def singR (r n : ℕ) : ℝ :=
  ∑' q : ℕ, ((μ q : ℝ) / (q.totient : ℝ)) ^ r * LeanLab.HeathBrown1985.ramanujan q n

theorem singR_three : singR 3 = sing3 := by
  funext n; rfl

/-- The printed error bound of (3.113) for `r = 3`:
`|ν₃(n) - n²/2 · S₃| ≤ C n^{2 + (Θ - 3/4)} (log n)^B` for all large `n`. -/
def printedA3Bound (Θ : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    |nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n| ≤ C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B

/-- **Theorem A, r = 3, as printed**, on Hypothesis R at level `Θ < 3/4`. -/
def printedA3_stmt : Prop :=
  ∀ Θ : ℝ, Θ < 3 / 4 → NoZerosRight Θ → printedA3Bound Θ

/-- **Theorem A as printed, every `r ≥ 3`**, (3.113). -/
def printedA_stmt (r : ℕ) : Prop :=
  ∀ Θ : ℝ, Θ < 3 / 4 → NoZerosRight Θ →
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur r n - (n : ℝ) ^ (r - 1) / ((r - 1).factorial : ℝ) * singR r n| ≤
        C * (n : ℝ) ^ ((r : ℝ) - 1 + (Θ - 3 / 4)) * Real.log n ^ B

theorem printedA_three_iff : printedA_stmt 3 ↔ printedA3_stmt := by
  unfold printedA_stmt printedA3_stmt printedA3Bound
  rw [singR_three]
  norm_num

/-- The printed form implies the lab's weaker `theoremA3_stmt`, on Hypothesis R. -/
theorem theoremA3_of_printed (hP : printedA3_stmt) (hR : HypothesisR) : theoremA3_stmt := by
  obtain ⟨Θ, hΘ, hZ⟩ := hR
  obtain ⟨B, -, C, n₀, h⟩ := hP Θ hΘ hZ
  set ε : ℝ := (3 / 4 - Θ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hlo := (isLittleO_log_rpow_rpow_atTop B hε0).bound (c := 1) one_pos
  have hlo' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlo
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hlo'
  refine ⟨ε, hε0, |C|, max (max n₀ N) 1, fun n hn => ?_⟩
  have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN : N ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hL := hN n hnN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 _),
    Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _), one_mul] at hL
  have hmain := h n hn0
  have e1 : (n : ℝ) ^ 2 / 2 * sing3 n = sing3 n * (n : ℝ) ^ 2 / 2 := by ring
  rw [e1] at hmain
  have hX0 : 0 ≤ (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B :=
    mul_nonneg (Real.rpow_nonneg hnpos.le _) (Real.rpow_nonneg hlog0 _)
  have hexp : (n : ℝ) ^ (2 + (Θ - 3 / 4)) * (n : ℝ) ^ ε = (n : ℝ) ^ (2 - ε) := by
    rw [← Real.rpow_add hnpos]; congr 1; rw [hε]; ring
  calc |nur 3 n - sing3 n * (n : ℝ) ^ 2 / 2|
      ≤ C * ((n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B) := by rw [← mul_assoc]; exact hmain
    _ ≤ |C| * ((n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hX0
    _ ≤ |C| * ((n : ℝ) ^ (2 + (Θ - 3 / 4)) * (n : ℝ) ^ ε) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        exact mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hnpos.le _)
    _ = |C| * (n : ℝ) ^ (2 - ε) := by rw [hexp]

/-- Vacuity of the bound form: it holds at `Θ = 7/4`, exponent `3`, from `theoremA3_main`.
This `Θ` is outside Hypothesis R; it only shows the shape of `printedA3Bound` can hold. -/
theorem printedA3Bound_form : printedA3Bound (7 / 4) := by
  obtain ⟨n₀, h⟩ := theoremA3_main 1 one_pos
  refine ⟨0, le_rfl, 1, max n₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hm := h n (le_trans (le_max_left _ _) hn)
  have e1 : (n : ℝ) ^ 2 / 2 * sing3 n = sing3 n * (n : ℝ) ^ 2 / 2 := by ring
  rw [e1]
  have h3 : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ (2 + ((7 : ℝ) / 4 - 3 / 4)) :=
    Real.rpow_le_rpow_of_exponent_le hn1' (by norm_num)
  rw [Real.rpow_two] at h3
  simp only [Real.rpow_zero, mul_one, one_mul]
  linarith

end LeanLab.HardyLittlewood1923.U1444

