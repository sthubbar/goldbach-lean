module

public import LeanLab.Linnik1951.Decomp357a
public import LeanLab.Linnik1951.Decomp357l

/-!
P0093 pages 165 and 168. Separate local major arc analysis from the arithmetic tail.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951


/-- LEAF. P0093 page 168 equations 10.5 and 10.6. Summing the singular
series tail over the exponent tuples gives a negligible error. This is
arithmetic and has no GRH or Mellin hypothesis. -/
theorem truncated_to_main357 (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |truncatedMain357 k N - mainTerm111 k N| ≤ ε * scale111 k N := by
  exact truncated_to_main_from_tail357 k hk ε hε

end LeanLab.Linnik1951
