module

public import LeanLab.HelfgottMajor.Route669
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
The conjugate in the corrected residue of P0014 page 33, display 4.8.
The existing reflection theorem excludes one. Nontrivial characters have entire L functions,
so continuity extends that identity to one and differentiation gives the required conjugate.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Conjugate669
open Complex
open scoped ComplexConjugate

/-- P0014 page 33, display 4.8. For a nontrivial character the conjugation identity holds
at every complex point, including one. -/
theorem LFunction_inv_eq_conj {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ⁻¹ =
      fun s => conj (DirichletCharacter.LFunction χ (conj s)) := by
  have hi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  apply Continuous.ext_on (dense_compl_singleton (1 : ℂ))
    (DirichletCharacter.differentiable_LFunction hi).continuous
    (continuous_conj.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      continuous_conj))
  intro s hs
  have hsc : conj s ≠ 1 := by
    intro h
    apply hs
    simpa using congrArg conj h
  simpa using ZeroCount1623.LFunction_inv_conj χ hsc

/-- P0014 page 33, display 4.8. The logarithmic derivative at one of the inverse character
is the complex conjugate of the original logarithmic derivative. -/
theorem logDeriv_inv_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    deriv (DirichletCharacter.LFunction χ⁻¹) 1 /
        DirichletCharacter.LFunction χ⁻¹ 1 =
      (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
        DirichletCharacter.LFunction χ 1) := by
  have hd := ((DirichletCharacter.differentiable_LFunction hχ) 1).hasDerivAt.conj_conj
  have heq := LFunction_inv_eq_conj χ hχ
  have hd' : HasDerivAt (DirichletCharacter.LFunction χ⁻¹)
      (conj (deriv (DirichletCharacter.LFunction χ) 1)) 1 := by
    simpa only [heq, Function.comp_def, map_one] using hd
  rw [hd'.deriv, heq]
  simp only [map_one, map_div₀]

end LeanLab.HelfgottMajor.Conjugate669
