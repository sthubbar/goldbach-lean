module

public import LeanLab.HelfgottMajor.Lemma41Leaf123

/-!
The four unchanged integral definitions for the Lemma 4.1 route.
Their statements and bodies are moved verbatim from MainLemma41Split123.
This module lets the analytic supplies precede the sealed leaf declarations.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.MainLemma41Split123
open Real MeasureTheory Set LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- The function -t f'(t) of display 4.14, page 35, for f(t) = exp(-t²/2) e(δt), the
Gaussian η♥ of page 44 twisted by e(δt). -/
noncomputable def tDerivWeight (δ t : ℝ) : ℂ :=
  ((t : ℂ) ^ 2 - 2 * π * Complex.I * δ * t) * (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)

/-- G_δ continued to re s above -1 except s = 0, page 32: s G_δ(s) = M(-t f'(t))(s). -/
noncomputable def contMellin (δ : ℝ) (s : ℂ) : ℂ := mellin (tDerivWeight δ) s / s

/-- The constant c0 of the Laurent expansion 4.6, page 33: c0 = -∫ f'(t) log t dt, with
f'(t) = (-t + 2πiδ) exp(-t²/2) e(δt). -/
noncomputable def laurentC0 (δ : ℝ) : ℂ :=
  -∫ t in Ioi (0 : ℝ),
    ((-(t : ℂ) + 2 * π * Complex.I * δ) * (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) * (log t : ℂ)

/-- The integrand L'(s, χ)/L(s, χ) G_δ(s) x^s of display 4.7, page 33. -/
noncomputable def contourIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ x : ℝ) (s : ℂ) :
    ℂ :=
  deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s *
    contMellin δ s * (x : ℂ) ^ s

end LeanLab.HelfgottMajor.MainLemma41Split123
