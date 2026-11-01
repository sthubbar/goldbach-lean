module

public import Mathlib

/-!
# Chebyshev's explicit bounds for ψ, Chebyshev 1852

P. L. Chebyshev, *Mémoire sur les nombres premiers*, Journal de mathématiques pures et
appliquées, 1re série, 17, 1852, 366-390. Chebyshev compares `log n!` with the combination
`log n! - log ⌊n/2⌋! - log ⌊n/3⌋! - log ⌊n/5⌋! + log ⌊n/30⌋!` and obtains explicit two-sided
bounds for his function `ψ` with the constant
`A = log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30 = 0.92129...`.

The target theorems, both unconditional, are, with `ψ` Mathlib's `Chebyshev.psi`:
* `psi_ge_chebyshev30`: for every natural `n ≥ 30`, `ψ(n) ≥ A n - 5 log n + 2 log 30 - 1`;
* `psi_le_chebyshev30`: for every natural `n`, `ψ(n) ≤ (6/5) A n + 2 (log n)² + 160`.

Chebyshev states his bounds for real `x` with smaller error terms; here the argument is a
natural number and the error terms are the explicit ones that the Lean proof reaches.
-/

@[expose] public section

open Real Finset Chebyshev

noncomputable section
namespace GoldbachLean.Chebyshev1852.Explicit

/-- The constant `A = log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30`. -/
def A : ℝ := Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30

/-- **Chebyshev 1852, explicit lower bound.** `ψ(n) ≥ A n - 5 log n + 2 log 30 - 1` for
`n ≥ 30`. -/
theorem psi_ge_chebyshev30 (n : ℕ) (hn : 30 ≤ n) :
    A * n - 5 * Real.log n + 2 * Real.log 30 - 1 ≤ ψ n := by
  sorry

/-- **Chebyshev 1852, explicit upper bound.** `ψ(n) ≤ (6/5) A n + 2 log² n + 160` for every
`n`. -/
theorem psi_le_chebyshev30 (n : ℕ) :
    ψ n ≤ 6 / 5 * A * n + 2 * Real.log n ^ 2 + 160 := by
  sorry

end GoldbachLean.Chebyshev1852.Explicit
