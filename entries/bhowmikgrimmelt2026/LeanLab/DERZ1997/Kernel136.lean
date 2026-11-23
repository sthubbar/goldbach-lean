module

public import Mathlib

/-!
The existing Perron kernel definition, moved with its statement and body unchanged.
This keeps the new elementary kernel proofs independent of the later analytic leaves.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.DERZ1997.Decomp1529b
open Complex

/-- Perron's truncated integral `(1/2π) ∫_{-T}^{T} y^{c+it}/(c+it) dt`, which is
`(1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds`. -/
noncomputable def perronI (y c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)

end LeanLab.DERZ1997.Decomp1529b
