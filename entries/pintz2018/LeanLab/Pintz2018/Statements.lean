module

public import Mathlib

/-!
# Pintz 2018, statements used by the Section 8 arguments

Three statement shapes from J. Pintz, A new explicit formula in the additive theory of primes
with applications II. The exceptional set in Goldbach's problem, arXiv 1804.09084v2: the
saturation conclusion (4.41) of Theorem K, the bound (4.36) of Theorem J and the condition
(4.48) of Theorem L.
-/

@[expose] public section


namespace LeanLab.Pintz2018
open Real

/-- Theorem K of arXiv 1804.09084, display (4.41) on page 18, the saturation part of the
optimal choice: every coordinate `d j` with `1 ≤ j < r` equals its cap `e j`. -/
def TheoremK_OptimalChoice (r : ℕ) (d_opt e : ℕ → ℝ) : Prop :=
  ∀ j, 1 ≤ j → j < r → d_opt j = e j

/-- Theorem J, display 4.36, page 17: `D(Λ) ≤ (1 - ξ + O(ε)) / (2Δ)`. Here `x` stands for `ξ`,
`D_var` for `Δ`, and `e` is an explicit stand-in for the `O(ε)` term. -/
def TheoremJ_bound (D : ℝ → ℝ) (x e D_var : ℝ) : Prop :=
  ∀ Λ, D Λ ≤ (1 - x + e) / (2 * D_var)

/-- Theorem L, display (4.48) p. 19: the bounds `c m` have decreasing increments,
`c(m + 1) - c m ≤ c m - c(m - 1)` for `m ≥ 2`. -/
def TheoremL_condition (c : ℕ → ℝ) : Prop :=
  ∀ m, 2 ≤ m → c (m + 1) - c m ≤ c m - c (m - 1)

end LeanLab.Pintz2018
