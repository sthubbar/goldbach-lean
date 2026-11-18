module

public import Mathlib

/-!
# Kumchev and Liu 2007, Theorem 1 from Proposition 1

A. V. Kumchev and J. Y. Liu, Sums of primes and squares of primes in short intervals,
arXiv 0801.0130, Theorem 1 on page 2, display 9. For n in the set ℋ₂ of even n not
congruent to 1 mod 3, the count R₂ of representations n = p₁ + p₂² with p₁ in a window
below X of length Y and p₂ near the square root of Y is close to the main term r₂ times a
truncated singular series, for all but O of H over log X to the A integers n in X, X + H.
Here Y is X to the 7/12 + ε/2, as in the paper.

The statement is proved on the range X to the 7/18 + ε at most H at most X to the 1 - ε,
the range that the proof on page 16 writes, conditional on the paper's Proposition 1,
display 33 on page 8 with the weights of page 15, which is the explicit hypothesis
`Eq33Hyp`. `thm1_full_of_written_small_eps` extends the conclusion to the printed range
H at most X when ε is at most 5/18. `written_range_nonempty` shows the written range is
not empty.

Every definition below repeats the definition of the same name in the solution, with the
same `open` lines and local instances. Goldbach type questions remain open and are not
claimed here.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007
open Real

attribute [local instance] Classical.propDecidable

/-- The paper's `ℋ₂ = {n ∈ ℕ : n ≢ 1 (mod 3), 2 ∣ n}`. -/
def InH2 (n : ℕ) : Prop := n % 3 ≠ 1 ∧ 2 ∣ n

/-- `cntIoc S X H` is the number of natural `n` with `X < n ≤ X + H` and `S n`. -/
noncomputable def cntIoc (S : ℕ → Prop) (X H : ℝ) : ℕ :=
  ((Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ) ∧ S n)).card

end LeanLab.KumchevLiu2007

namespace LeanLab.KumchevLiu2007.U1534

open Real Complex LeanLab.KumchevLiu2007

/-- `e(x) = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- `S(q, a) = ∑_{1 ≤ x ≤ q, (x, q) = 1} e(a x² / q)`, eq. (8); `x = q` is replaced by `x = 0`,
the same residue. -/
noncomputable def gaussS (q a : ℕ) : ℂ :=
  ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q), ee ((a * x ^ 2 : ℕ) / (q : ℝ))

/-- `A₂(n, q) = μ(q) φ(q)^{-2} ∑_{1 ≤ a ≤ q, (a, q) = 1} S(q, a) e(-an/q)`, eq. (45). -/
noncomputable def A2 (n q : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((Nat.totient q : ℂ) ^ 2) *
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      gaussS q a * ee (-((a * n : ℕ) : ℝ) / q)

end LeanLab.KumchevLiu2007.U1534

namespace LeanLab.KumchevLiu2007.Task129

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- The parameter Y of page 2 before eq. 4. -/
noncomputable def windowY (X ε : ℝ) : ℝ := X ^ (7 / 12 + ε / 2)

/-- Integer solutions in the half open windows of page 2 eqs. 4 to 6.
For large X in the nonempty H range of Theorem 1, Y is less than X. -/
noncomputable def windowPairs (X Y : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
    (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
      Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n)

/-- The representation count R2 of page 2 eq. 4. -/
noncomputable def primeCount (X Y : ℝ) (n : ℕ) : ℕ :=
  ((windowPairs X Y n).filter (fun v => v.1.Prime ∧ v.2.Prime)).card

/-- The logarithmically weighted integer count r2 of page 2 eq. 6. -/
noncomputable def integerMain (X Y : ℝ) (n : ℕ) : ℝ :=
  ∑ v ∈ windowPairs X Y n, 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))

/-- The truncated singular series of page 2 eq. 7, using the existing A2. -/
noncomputable def series2 (n : ℕ) (P : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q

/-- The main term r2 times the truncated singular series in page 2 eq. 9. -/
noncomputable def main2 (X Y P : ℝ) (n : ℕ) : ℂ := integerMain X Y n * series2 n P

/-- The sifted count R of page 8 eqs. 12 and 34. -/
noncomputable def roughCount (X Y P : ℝ) (n : ℕ) : ℕ :=
  ((windowPairs X Y n).filter (fun v => v.1.Prime ∧
    ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card

/-- The weight f2 of page 15, Section 4, before display 52:
f2 of u is 1 over log u plus the integral from z0 to the square root of u of
dt over t log t log of u over t. -/
noncomputable def f2Weight (z0 u : ℝ) : ℝ :=
  1 / Real.log u + ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))

/-- The singular integral I of n, varpi, lambda0, page 7 display 27, with
f1 of u equal to 1 over log u, page 15, and f2 as above with z0 from display 34. -/
noncomputable def singInt (X Y P : ℝ) (n : ℕ) : ℝ :=
  ∑ v ∈ windowPairs X Y n,
    (1 / Real.log (v.1 : ℝ)) * f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (v.2 : ℝ)

/-- The error in display 53 of page 16: R of n, varpi, lambda0 minus S2 of n, P times I. -/
noncomputable def err53 (X ε B : ℝ) (n : ℕ) : ℝ :=
  ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
    series2 n (Real.log X ^ B) * (singInt X (windowY X ε) (Real.log X ^ B) n : ℂ)‖

end LeanLab.KumchevLiu2007.Task129

namespace LeanLab.KumchevLiu2007.Task129W

open Real Complex LeanLab.KumchevLiu2007 LeanLab.KumchevLiu2007.Task129
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Theorem 1, page 2 display 9, restated to X to the 7/18 + ε at most H at most
X to the 1 - ε, the range for which page 16 proves display 55. -/
def kumchev_liu_thm1_written : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧
    ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧
      ∀ X H : ℝ, X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
          ‖(primeCount X (windowY X ε) n : ℂ) -
            main2 X (windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
          C * H / Real.log X ^ A

/-- Display 33 of Proposition 1 on page 8 for the primes and the sifted function of
display 34 with the page 15 weights, in the range of page 16 after display 55, as a named
hypothesis. It includes the paper's verification on page 15 of the hypotheses of
Proposition 1 for these functions. -/
def Eq33Hyp : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      (∑ n ∈ (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ)),
        err53 X ε B n ^ 2) ≤ C * H * windowY X ε / Real.log X ^ A

/-- The written range is not empty: ε = 1/18, X = 4 and H = X to the 1 - ε. -/
theorem written_range_nonempty :
    ∃ X H ε : ℝ, 0 < ε ∧ 2 ≤ X ∧ X ^ (7 / 18 + ε) ≤ H ∧ H ≤ X ^ (1 - ε) := by
  sorry

/-- Theorem 1 on the written range X to the 7/18 + ε at most H at most X to the 1 - ε,
from Proposition 1 display 33, taken as the explicit hypothesis `Eq33Hyp`. -/
theorem thm1_written_of_eq33 (h33 : Eq33Hyp) : kumchev_liu_thm1_written := by
  sorry

/-- For ε at most 5/18 the written form gives Theorem 1 on the printed range
H at most X for that ε, since Y is at most X to the 1 - ε. -/
theorem thm1_full_of_written_small_eps (hW : kumchev_liu_thm1_written)
    (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧
    ∀ δ ε : ℝ, 0 < δ → 0 < ε → ε ≤ 5 / 18 → ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧
      ∀ X H : ℝ, X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
          ‖(primeCount X (windowY X ε) n : ℂ) -
            main2 X (windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  sorry

end LeanLab.KumchevLiu2007.Task129W
