module

public import LeanLab.HelfgottMajor.Contour457
public import LeanLab.HelfgottMajor.Numerator457
public import LeanLab.HelfgottMajor.LogWeight457

/-!
The two square energies in the principal contour estimate.
Source P0014 pages 34 and 35, displays 4.12 to 4.15.
Neither energy involves a prime sum, a zero sum or the scale x.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.Decomp457b
open Real MeasureTheory Contour457

/-- LEAF. P0014 page 35 display 4.15 and page 43 display 4.42.
The regular numerator has square energy at most two pi times the square of the repaired
Gaussian derivative norm budget. There is no logarithmic derivative in this statement.
-/
theorem gaussian_numerator_L2 (δ : ℝ) :
    MemLp (gaussianNumerator δ) 2 ∧
      sqrt (∫ t : ℝ, ‖gaussianNumerator δ t‖ ^ 2) ≤
        sqrt (2 * π) * (1 + 6 * |δ|) := by
  exact Numerator457.gaussian_numerator_L2 δ

end LeanLab.HelfgottMajor.Decomp457b
