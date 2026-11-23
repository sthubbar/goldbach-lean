module

public import LeanLab.Linnik1951.Base491b
public import LeanLab.Linnik1951.PrimeArcPartial491
public import LeanLab.Linnik1951.PrimeArcLimit491
public import LeanLab.DERZ1997.MainHSW

/-!
P0093 pages 154, 155 and 159 through 161. The one analytic input of the principal
convolution estimate, equations 6.1 and 6.3, for the full prime series S of page 154,
restricted to the short arc and stated in mean square. No character occurs.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- P0093 page 154. A unimodular phase does not change the norm of a term. -/
private theorem phase_term_norm491 (c : ℂ) (z : ℝ) (n : ℕ) :
    ‖c * Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ = ‖c‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- P0093 page 154. An absolutely summable coefficient sequence gives a summable
series of negative frequencies. -/
private theorem phase_series_summable491 (c : ℕ → ℂ) (hc : Summable c) (z : ℝ) :
    Summable (fun n : ℕ => c n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)) := by
  apply Summable.of_norm
  simp only [phase_term_norm491]
  exact hc.norm

/-- P0093 pages 154 and 161. The difference of the prime series S and the model
series S one is the series of the differences of the coefficients. -/
private theorem prime_minus_log_series491 (N : ℕ) (hN : 1 ≤ N) (z : ℝ) :
    primeFourier111 N z - logFourier520 N z =
      ∑' n : ℕ, (primeCoefficient552 N n - logCoefficient520 N n) *
        Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I) := by
  rw [prime_series_nat552, logFourier520,
    ← (phase_series_summable491 _ (prime_coefficients_summable552 N hN) z).tsum_sub
      (phase_series_summable491 _ (logCoefficient_summable520 N hN) z)]
  simp only [sub_mul]

/-- P0093 page 160 equation 6.1 with page 161 equation 6.3, on the arc,
for the full prime series. Under the extended Riemann hypothesis the prime
series S of page 154 differs from the model series S one, with weights one over
ln m, by a function whose square integral over the arc of radius one over q tau
is at most a constant times N ln to the 13 of N over q tau. Here q only fixes the
radius. This statement is not printed. It stands in for the print's use of the
page 159 display with Lemma 2 in equation 6.1 and for the step to equation 6.3,
for which the print gives no argument. The proof is the formalizer's and does not
use the Mellin display or Lemma 2: Gallagher's lemma and the short interval mean
square under the Riemann hypothesis from PNTPort, partial summation, an elementary
prime power bound and a limit. The exponent 13 is slack; the argument gives 2.
Inputs: `LeanLab.DERZ1997.rh_of_GRH`, the truncated estimate
`prime_arc_partial491`, which rests on the PNTPort inputs of its own file, and the
passage to the limit `series_arc_limit491`. No PNTPort result is used directly here. -/
theorem prime_arc_mean_square491 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖primeFourier111 N z - logFourier520 N z‖ ^ 2) ≤
          C * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 := by
  obtain ⟨C, hC, N0, h⟩ := prime_arc_partial491 (LeanLab.DERZ1997.rh_of_GRH hG)
  refine ⟨C, hC, N0, fun N hN q hq hqN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  simp only [prime_minus_log_series491 N hN1]
  refine series_arc_limit491 _ ?_ _ _ ?_ (h N hN q hq hqN)
  · exact ((prime_coefficients_summable552 N hN1).sub
      (logCoefficient_summable520 N hN1)).norm
  · positivity

end LeanLab.Linnik1951
