module

public import LeanLab.Linnik1951.Decomp280b
public import LeanLab.Perelli1996.Ramanujan103

/-!
P0093 pages 165 and 168. Finite singular main term data.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- P0093 page 168 equation 10.6. The finite singular series with Q equal
to N to the one tenth. The existing lab Ramanujan sum uses reduced residues. -/
noncomputable def truncatedSingular357 (N n : ℕ) : ℝ :=
  (∑ q ∈ Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
    (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
      LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n).re

/-- P0093 page 165 equation 8.1. The leading finite singular series sum
before the tail is replaced by the Euler product. -/
noncomputable def truncatedMain357 (k N : ℕ) : ℝ := by
  classical
  exact ∑ ν ∈ (Finset.univ.filter fun ν : Fin k → Fin (N + 1) =>
    (∀ i, 1 ≤ (ν i).val) ∧ 2 ≤ N - ∑ i, 2 ^ (ν i).val ∧
      Even (N - ∑ i, 2 ^ (ν i).val)),
    truncatedSingular357 N (N - ∑ i, 2 ^ (ν i).val) *
      (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2

end LeanLab.Linnik1951
