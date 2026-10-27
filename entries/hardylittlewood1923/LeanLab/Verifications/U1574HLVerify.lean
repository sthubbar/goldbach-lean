module

public import LeanLab.HardyLittlewood1923.U1503Endpoint

/-!
AI-written Lean code, Claude, 2026-10-27, PC run 20261027T0807Z-9485, unit U-1574, paper P0004.

# Falsifier checks for U-1503's printed Theorem A, eq. 3.113 p. 21

* `hyps_satisfiable`: the hypotheses of `printedA_form_all_U1503_closed` other than
  `NoZerosRight Θ`, namely `3 ≤ r`, `47/64 ≤ Θ`, `Θ < 3/4`, hold together.
* `GRH`: the textbook generalized Riemann hypothesis for every Dirichlet `L`, every modulus,
  primitive or not, as zeros in the open strip `0 < Re s < 1` lying on `Re s = 1/2`. This is
  Hardy and Littlewood's Hypothesis R* of p. 4.
* `noZerosRight_of_GRH`: `GRH` gives `NoZerosRight Θ` for every `Θ ≥ 1/2`, so the zero-free
  hypothesis of the headline is implied by Hypothesis R* at every level of the headline range.
* `printedA_form_all_of_GRH`: on `GRH`, the headline at `Θ = 47/64`, with no other hypothesis.
* `singR_pos`, `singR_summable`: for `r ≥ 3`, `n ≥ 1`, `n ≡ r mod 2`, the printed `S_r(n)` is
  positive and its defining series is summable, so the `tsum` in `singR` is the true sum and
  the main term is not a junk zero.

Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1574

open Real
open scoped ArithmeticFunction.Moebius
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1438 (NoZerosRight)
open LeanLab.HardyLittlewood1923.U1444 (singR)

/-- The non-zero-free hypotheses of the headline are jointly satisfiable. -/
theorem hyps_satisfiable : ∃ r : ℕ, ∃ Θ : ℝ, 3 ≤ r ∧ 47 / 64 ≤ Θ ∧ Θ < 3 / 4 :=
  ⟨3, 47 / 64, le_rfl, le_rfl, by norm_num⟩

/-- **GRH**, Hardy and Littlewood's Hypothesis R* of p. 4, for every Dirichlet `L`. -/
def GRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- GRH gives the headline's zero-free hypothesis at every level `Θ ≥ 1/2`. -/
theorem noZerosRight_of_GRH (h : GRH) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) : NoZerosRight Θ := by
  intro q _ χ s hs hs1 hL
  by_cases h1 : 1 ≤ s.re
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) h1 hL
  · have := h q χ s hL (by linarith) (by linarith)
    linarith

/-- On GRH, the headline at `Θ = 47/64`, every `r ≥ 3`, with no further hypothesis. -/
theorem printedA_form_all_of_GRH (h : GRH) :
    ∀ r : ℕ, 3 ≤ r → ∃ B : ℕ, ∃ K : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur r n - (n : ℝ) ^ (r - 1) / ((r - 1).factorial : ℝ) * singR r n| ≤
        K * (n : ℝ) ^ ((r : ℝ) - 1 + ((47 / 64 : ℝ) - 3 / 4)) * Real.log n ^ B :=
  fun r hr => U1503.printedA_form_all_U1503_closed r hr (47 / 64) le_rfl (by norm_num)
    (noZerosRight_of_GRH h (by norm_num))

/-- The printed singular series is positive in like parity, so the main term is genuine. -/
theorem singR_pos {r n : ℕ} (hr : 3 ≤ r) (hn : 0 < n) (h : n % 2 = r % 2) :
    0 < singR r n := by
  rw [(U1468.singRProductPos r hr n hn).1 h]
  obtain ⟨c, K, hc, hb⟩ := Br_bounds r hr
  exact mul_pos (mul_pos two_pos (Cr_pos r hr)) (lt_of_lt_of_le hc (hb n).1)

/-- The series defining `singR r n` is summable in like parity, so `tsum` is the true sum. -/
theorem singR_summable {r n : ℕ} (hr : 3 ≤ r) (hn : 0 < n) (h : n % 2 = r % 2) :
    Summable (fun q : ℕ => ((μ q : ℝ) / (q.totient : ℝ)) ^ r *
      LeanLab.HeathBrown1985.ramanujan q n) := by
  by_contra hs
  have hp := singR_pos hr hn h
  rw [singR, tsum_eq_zero_of_not_summable hs] at hp
  exact lt_irrefl _ hp

end LeanLab.HardyLittlewood1923.U1574

