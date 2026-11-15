module

public import LeanLab.Tolev2009.DivisorMoment

/-!
AI wrote this Lean code. Codex task314.
Binary Goldbach is open.
Source: Halupczok 2008 pages 18 to 19, the seven reciprocal divisor moments.
The local singular coefficient and gcd reindexing estimates remain separate obligations.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.CoefficientMoment314
open LeanLab.HeathBrown1985 LeanLab.Tolev2009.DivisorMoment

/-- Halupczok page 18, every reciprocal divisor moment is bounded by a harmonic power. -/
theorem reciprocal_moment (r N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ r / n ≤ Hn N ^ (2 ^ r) := by
  induction r generalizing N with
  | zero => simp [Hn]
  | succ r ih =>
    have he : 2 * 2 ^ r = 2 ^ (r + 1) := by rw [pow_succ]; omega
    simpa only [he] using reciprocal_step N r (2 ^ r) (fun M _ => ih M)

/-- Halupczok page 18, the same moment with an explicit logarithmic constant. -/
theorem reciprocal_moment_log (r N : ℕ) (hL : 1 ≤ Real.log N) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ r / n ≤
      (2 : ℝ) ^ (2 ^ r) * Real.log N ^ (2 ^ r) := by
  have hH : Hn N ≤ 2 * Real.log N := (Hn_le N).trans (by linarith)
  calc
    _ ≤ Hn N ^ (2 ^ r) := reciprocal_moment r N
    _ ≤ (2 * Real.log N) ^ (2 ^ r) := pow_le_pow_left₀ (Hn_nonneg _) hH _
    _ = _ := mul_pow _ _ _

/-- Halupczok page 19, the seven independent reciprocal moments use exponent 4912. -/
theorem seven_reciprocal_moments (N : ℕ) :
    (∑ d ∈ Icc 1 N, (d.divisors.card : ℝ) ^ 12 / d) *
      (∑ a ∈ Icc 1 N, (a.divisors.card : ℝ) ^ 8 / a) ^ 3 *
      (∑ e ∈ Icc 1 N, (e.divisors.card : ℝ) ^ 4 / e) ^ 3 ≤ Hn N ^ 4912 := by
  have h12 := reciprocal_moment 12 N
  have h8 := reciprocal_moment 8 N
  have h4 := reciprocal_moment 4 N
  norm_num only [Nat.reducePow] at h12 h8 h4
  have hn (r : ℕ) : 0 ≤ ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ r / n :=
    sum_nonneg fun _ _ => by positivity
  calc
    _ ≤ (Hn N ^ 4096) * (Hn N ^ 256) ^ 3 * (Hn N ^ 16) ^ 3 :=
      mul_le_mul (mul_le_mul h12 (pow_le_pow_left₀ (hn 8) h8 3) (pow_nonneg (hn 8) 3)
          ((hn 12).trans h12))
        (pow_le_pow_left₀ (hn 4) h4 3) (pow_nonneg (hn 4) 3)
        (mul_nonneg ((hn 12).trans h12) (pow_nonneg ((hn 8).trans h8) 3))
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]

/-- Halupczok pages 18 to 19, the seven moments and twelve log losses fit exponent 5000. -/
theorem seven_moments_log_budget (N : ℕ) (hL : 1 ≤ Real.log N) :
    Real.log N ^ 12 *
      ((∑ d ∈ Icc 1 N, (d.divisors.card : ℝ) ^ 12 / d) *
        (∑ a ∈ Icc 1 N, (a.divisors.card : ℝ) ^ 8 / a) ^ 3 *
        (∑ e ∈ Icc 1 N, (e.divisors.card : ℝ) ^ 4 / e) ^ 3) ≤
      (2 : ℝ) ^ 4912 * Real.log N ^ (5000 : ℕ) := by
  have hH : Hn N ≤ 2 * Real.log N := (Hn_le N).trans (by linarith)
  have hL0 : 0 ≤ Real.log N := by linarith
  calc
    _ ≤ Real.log N ^ 12 * Hn N ^ 4912 :=
      mul_le_mul_of_nonneg_left (seven_reciprocal_moments N) (by positivity)
    _ ≤ Real.log N ^ 12 * (2 * Real.log N) ^ 4912 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Hn_nonneg _) hH _) (by positivity)
    _ = (2 : ℝ) ^ 4912 * Real.log N ^ (4924 : ℕ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num)) (by positivity)

end LeanLab.Tolev2009.CoefficientMoment314
