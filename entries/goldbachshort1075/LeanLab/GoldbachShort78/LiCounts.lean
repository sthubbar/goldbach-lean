module

public import LeanLab.GoldbachShort78.Statements

/-!
The almost all intervals count at the exponent of R. Li, arXiv 2407.05651 v6, Theorem 1.1.

AI wrote the Lean code, Gemini, Google, with fixes by Claude. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.GoldbachShort78

/-- The almost all intervals count at the exponent `1/21.5 + ε` of R. Li, arXiv 2407.05651 v6,
Theorem 1.1. -/
def LiAlmostAllCountEps (ε y₀ : ℝ) : Prop :=
  AlmostAllCount (1 / 21.5 + ε) y₀

end LeanLab.GoldbachShort78
