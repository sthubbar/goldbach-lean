module

public import LeanLab.SchnirelmannConstant.Defs

/-!
P0032 Riesel, Vaughan, On sums of primes, Ark. Mat. 21 (1983) 45-74, read in full from
papers/P0032.pdf, formulas checked on the page images.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LeanLab.RieselVaughan1983
open LeanLab.SchnirelmannConstant

/-- Page 45: `N(x)` is the number of even numbers `n ≤ x` that are the sum of at most two
primes. Natural numbers start at 1 in the paper, so `n` runs over `1 ≤ n ≤ ⌊x⌋`. -/
noncomputable def NCount (x : ℝ) : ℕ :=
  #{n ∈ Icc 1 ⌊x⌋₊ | Even n ∧ AtMostPrimes 2 n}

/-- (1.1): `N(x) > x/18` for every `x ≥ 2`. -/
def Density11 : Prop := ∀ x : ℝ, 2 ≤ x → x / 18 < (NCount x : ℝ)

/-- The Theorem, page 45: every even natural number is a sum of at most eighteen primes. -/
def Theorem : Prop := ∀ n : ℕ, Even n → AtMostPrimes 18 n

/-- Page 45, the remark after the Theorem: every `n > 1` is a sum of at most nineteen primes. -/
def Corollary19 : Prop := ∀ n : ℕ, 1 < n → AtMostPrimes 19 n

/-- Lemma 7: `N(x) > x/18` for `2 ≤ x ≤ e^27`. -/
def Lemma7 : Prop := ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp 27 → x / 18 < (NCount x : ℝ)

/-- Lemma 8: `N(x) > x/18` for `24 ≤ log x ≤ 424`. -/
def Lemma8 : Prop :=
  ∀ x : ℝ, 0 < x → 24 ≤ Real.log x → Real.log x ≤ 424 → x / 18 < (NCount x : ℝ)

/-- (9.1) with Section 7's `y = x/(K+2)`, `K = 200`: `N(x) - N(y) > (x - y)/18` for
`log x ≥ 375`. -/
def Display91 : Prop :=
  ∀ x : ℝ, 375 ≤ Real.log x →
    (x - x / 202) / 18 < (NCount x : ℝ) - (NCount (x / 202) : ℝ)

end LeanLab.RieselVaughan1983
