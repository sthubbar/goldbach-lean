module

public import LeanLab.Linnik1951.Data357

/-!
P0093 pages 155 and 161. Sealed local major arc data moved without changes.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- P0093 page 155 equation 3.1. I_q at an integer residual n, with
tau equal to N to the one seventh. -/
noncomputable def localArc1622 (N q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      primeFourier111 N ((a : ℝ) / q + z) ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)

/-- P0093 page 161 after equation 6.3. The sum of 1 over ln m ln m' over m + m' = n
with both at least 2. It is empty for n below 4. -/
noncomputable def logConvolution1622 (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log m * Real.log (n - m : ℕ))

/-- Vacuity instance: at n equal to 4 the convolution is the single term at m equal to 2. -/
theorem logConvolution_four1622 :
    logConvolution1622 4 = 1 / (Real.log 2 * Real.log 2) := by
  simp [logConvolution1622]

/-- The bound of arc_local_expansion1622 as a Prop with its constants. -/
def LocalExpansion1622 (B : ℝ) (N0 : ℕ) : Prop :=
  ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
    ‖localArc1622 N q n -
        (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
          LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat *
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
      B * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))

end LeanLab.Linnik1951
