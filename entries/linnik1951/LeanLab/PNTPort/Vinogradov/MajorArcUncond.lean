module

public import LeanLab.PNTPort.Vinogradov.MajorArc
public import LeanLab.PNTPort.PsiChi.SiegelWalfisz

/-!
# The major arc approximation, unconditional

Lab proof, unit U-5252. AI wrote this file. `major_arc` is `major_arc_of_SW` applied to
`LeanLab.PNTPort.PsiChi.siegelWalfisz`, the lab's unconditional, ineffective Siegel-Walfisz
theorem of CLOUD 20261019T0514Z-cloud17. Known mathematics, no cited input.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real
open scoped ArithmeticFunction.Moebius

/-- **Major arcs**: for `A > 0` there are `c > 0`, `K ≥ 0` with, for `N ≥ e⁴`, `1 ≤ q ≤ (log N)^A`,
`(a, q) = 1` and every real `β`,
`‖S(a/q + β) - μ(q)/φ(q) V(β)‖ ≤ (7√N + qKN e^{-c√(log N/2)} + (log q/log 2) log N)(1 + 2π|β|N)`. -/
theorem major_arc (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, Real.exp 4 ≤ N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log N ^ A → ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ β : ℝ,
      ‖S N (a / q + β) - (μ q : ℂ) / q.totient * V N β‖ ≤
        (7 * Real.sqrt N + q * K * N * Real.exp (-c * Real.sqrt (Real.log N / 2)) +
          Real.log q / Real.log 2 * Real.log N) * (1 + 2 * π * |β| * N) :=
  major_arc_of_SW LeanLab.PNTPort.PsiChi.siegelWalfisz A hA

end LeanLab.PNTPort.Vinogradov

