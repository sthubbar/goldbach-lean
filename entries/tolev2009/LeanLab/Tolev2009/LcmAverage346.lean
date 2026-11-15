module

public import LeanLab.Tolev2009.LcmMultiplicity346
public import LeanLab.Tolev2009.Level346
public import LeanLab.Tolev2009.Discrepancy346

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 pages 6 and 9 to 11, discrepancy product averages.
The fixed 2009 modulus ranges are below the proved theta level.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.LcmAverage346
open LeanLab.HeathBrown1985
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.LcmMultiplicity346 LeanLab.Tolev2009.Discrepancy346
open LeanLab.Tolev2009.Level346

/-- Halupczok page 9, the one discrepancy reciprocal lcm mean at the fixed 2009 cutoff. -/
theorem linear_lcm_average (A : ℝ) (hA : 10 ^ 4 ≤ A) :
    ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N → 1 ≤ Real.log N → ∀ K : ℕ,
      K ≤ Dyadic.cutoff (10 ^ 4 * A) N →
        (∑ q ∈ Icc 1 ⌊Qof A N⌋₊, ∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q) / q) ≤
          C * Hn ⌊Qof A N⌋₊ ^ 2 * N / Real.log N ^ (100 * A) := by
  obtain ⟨C, hC⟩ := thetaError_mean (100 * A) (by linarith)
  refine ⟨C, fun N hN hL K hK => ?_⟩
  have hr := weighted_lcm_sum_le K ⌊Qof A N⌋₊
    ⌊Real.sqrt N / Real.log N ^ (4 * (100 * A) + 15)⌋₊
    (thetaError N) (thetaError_nonneg N) (by
      intro q hq k hk
      exact first_cutoff_lcm A N k q hA hL ((mem_Icc.mp hk).2.trans hK) (mem_Icc.mp hq).2)
  refine hr.trans ?_
  calc
    _ ≤ Hn ⌊Qof A N⌋₊ ^ 2 * (C * N / Real.log N ^ (100 * A)) :=
      mul_le_mul_of_nonneg_left (hC N (by omega)) (sq_nonneg _)
    _ = _ := by ring

/-- Halupczok pages 9 to 11, all positive degree lcm discrepancy products at the 2009 cutoff.
This contains no rational prime phase or arc integral. -/
theorem product_lcm_average (A : ℝ) (hA : 10 ^ 4 ≤ A) :
    ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N → 1 ≤ Real.log N → ∀ r : ℕ, 1 ≤ r →
      ∀ K : Fin r → ℕ, (∀ i, K i ≤ Dyadic.cutoff (10 ^ 4 * A) N) →
        (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
          (∏ i : Fin r, ∑ k ∈ Icc 1 (K i), thetaError N (Nat.lcm k q)) / (q : ℝ) ^ r) ≤
          Hn ⌊Qof A N⌋₊ ^ (2 ^ r) * (C * N / Real.log N ^ (100 * A)) ^ r := by
  obtain ⟨C, hC⟩ := thetaError_mean (100 * A) (by linarith)
  refine ⟨C, fun N hN hL r hr K hK => ?_⟩
  have hs := lcm_product_sum_le r ⌊Qof A N⌋₊
    ⌊Real.sqrt N / Real.log N ^ (4 * (100 * A) + 15)⌋₊ K hr
    (thetaError N) (thetaError_nonneg N) (by
      intro q hq i k hk
      exact first_cutoff_lcm A N k q hA hL ((mem_Icc.mp hk).2.trans (hK i)) (mem_Icc.mp hq).2)
  refine hs.trans ?_
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Hn_nonneg _) _)
  exact pow_le_pow_left₀ (sum_nonneg fun h hh => thetaError_nonneg N h) (hC N (by omega)) r

end LeanLab.Tolev2009.LcmAverage346
