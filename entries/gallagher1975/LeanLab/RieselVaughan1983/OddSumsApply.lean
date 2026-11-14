module

public import Mathlib
public import LeanLab.RieselVaughan1983.Lemma10Sum
public import LeanLab.RieselVaughan1983.OddSums

/-!
P0032 Riesel-Vaughan 1983, Lemma 10 and Lemma 12 windows with the Euler constants A₁₀ and A₁₁.
Unit U-1195, PC run 20261020T0703Z-22071. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

* `lemma10_window_A10`: Σ_{y/2 < d ≤ 101y, d odd} μ(d)²/φ(d) ≤ 6.31 A₁₀, from
  `L10.lemma10_window` and `OddSums.odd_sum_A10`; the paper's factor A₁₀(1 + log 202).
* `lemma12_half_A11`: Σ_{y/2 < d ≤ D, d odd} μ(d)²/φ(d)² ≤ 4A₁₁/y, from `L12.lemma12_half` and
  `OddSums.odd_sum_A11`, the paper's display before (2.24).
KNOWN mathematics.
-/

@[expose] public section

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.RieselVaughan1983.OddSumsApply

theorem lemma10_window_A10 {y : ℝ} (hy : 0 < y) :
    ∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) ⌊101 * y⌋₊).filter Odd, ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ≤
      OddSums.A10 * 6.31 :=
  (L10.lemma10_window hy).trans
    (mul_le_mul_of_nonneg_right (OddSums.odd_sum_A10 _) (by norm_num))

theorem lemma12_half_A11 {y D : ℝ} (hy : 0 < y) :
    ∑ d ∈ (Icc (⌊y / 2⌋₊ + 1) ⌊D⌋₊).filter Odd, ((μ d : ℝ)) ^ 2 / (d.totient : ℝ) ^ 2 ≤
      4 * OddSums.A11 / y := by
  have h := L12.lemma12_half (D := D) hy
  have h2 := mul_le_mul_of_nonneg_left (OddSums.odd_sum_A11 ⌊D⌋₊) (show 0 ≤ 4 / y by positivity)
  calc _ ≤ _ := h
    _ ≤ 4 / y * OddSums.A11 := h2
    _ = 4 * OddSums.A11 / y := by ring

end LeanLab.RieselVaughan1983.OddSumsApply
