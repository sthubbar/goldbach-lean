module

public import LeanLab.BhowmikGrimmelt2026.Prep1121BGFinish
public import LeanLab.PNTPort.ExplicitPsi1.CharHalfAssembly1122

/-!
Theorem 3.1 of G. Bhowmik and L. Grimmelt, The exceptional set of the Goldbach problem,
arXiv 2607.27282 v2, page 9, with the explicit formula of Davenport, Multiplicative Number
Theory, second edition, chapter 19 pages 115 to 118, proved in `PNTPort/ExplicitPsi1`.

`davenport_integer_half_formula592_ported` proves the half weighted explicit formula for
`ψ(x, χ)` with a primitive nonprincipal character `χ`, in the form that `theorem31_finish150`
takes as its argument; `mult χ ρ` is by definition
`analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ`. It is proved from
`PNTPort.ExplicitPsi1.CharHalfAssembly1122.davenport_half_formula_assembled`, which includes the
contour shift at a good height of pages 116 and 117. `theorem31_ported1122` then proves
`Theorem31` through `theorem31_finish150`, from the three hypotheses `Θ < 3/4`, `ZeroBound Θ`
and `0 < ε` only.

Binary Goldbach is open: Theorem 3.1 bounds the exceptional set under a zero hypothesis that is
unproved for every `Θ` below one. AI wrote the Lean code.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Davenport, Multiplicative Number Theory, second edition, chapter 19 pages 115 to 118, the
half weighted explicit formula for a primitive nonprincipal character, with the zeros in the
strip of height at most `T`. Proved, including the contour shift at a good height of pages 116
and 117. -/
theorem davenport_integer_half_formula592_ported :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1), (mult χ ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n) :=
  PNTPort.ExplicitPsi1.CharHalfAssembly1122.davenport_half_formula_assembled

/-- Theorem 3.1 of Bhowmik and Grimmelt, page 9: if `Θ < 3/4` and every zero of every Dirichlet
L-function in the strip `0 < Re s < 1` has real part at most `Θ`, then for every `ε > 0`,
`E(X) ≪ X^(2Θ - 1/2 + ε)`. Proved from these three hypotheses only. -/
theorem theorem31_ported1122 : Theorem31 :=
  theorem31_finish150 davenport_integer_half_formula592_ported

end LeanLab.BhowmikGrimmelt2026
