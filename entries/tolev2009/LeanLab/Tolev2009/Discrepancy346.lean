module

public import LeanLab.Tolev2009.QuantitativeBV346
public import LeanLab.Tolev2009.Progression346

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 page 6, maximal progression discrepancy.
The theta convention retains primes rather than prime powers.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.Discrepancy346
open LeanLab.PNTPort.BVMax
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Progression346

/-- Halupczok page 6, the finite maximal theta discrepancy over integer prefixes and residues. -/
noncomputable def thetaError (N q : ℕ) : ℝ :=
  ((range (N + 1)).product (range (q + 1))).sup' (by simp)
    (fun z => if Nat.Coprime z.2 q then |thetaN z.1 q z.2 - (z.1 : ℝ) / q.totient| else 0)

/-- Halupczok page 6, the maximum is nonnegative, including modulus zero. -/
theorem thetaError_nonneg (N q : ℕ) : 0 ≤ thetaError N q := by
  have h := Finset.le_sup'
    (fun z : ℕ × ℕ => if Nat.Coprime z.2 q then |thetaN z.1 q z.2 - (z.1 : ℝ) / q.totient| else 0)
    (show (0, 0) ∈ (range (N + 1)).product (range (q + 1)) by simp)
  simpa only [thetaError, thetaN, Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1),
    filter_empty, sum_empty, Nat.cast_zero, zero_div, sub_zero, abs_zero, ite_self] using h

/-- Halupczok page 6, an integer prefix and a reduced representative lie below the maximum. -/
theorem thetaError_term_le (N q m a : ℕ) (hm : m ≤ N) (haq : a ≤ q)
    (ha : Nat.Coprime a q) :
    |thetaN m q a - (m : ℝ) / q.totient| ≤ thetaError N q := by
  have h := Finset.le_sup'
    (fun z : ℕ × ℕ => if Nat.Coprime z.2 q then |thetaN z.1 q z.2 - (z.1 : ℝ) / q.totient| else 0)
    (show (m, a) ∈ (range (N + 1)).product (range (q + 1)) by
      exact mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩)
  simpa only [thetaError, if_pos ha] using h

/-- Halupczok page 6, choose a reduced residue and prefix attaining the maximum.
A zero maximum is attained at prefix zero and residue one. -/
theorem thetaError_attained (N q : ℕ) :
    ∃ m a : ℕ, m ≤ N ∧ Nat.Coprime a q ∧
      thetaError N q = |thetaN m q a - (m : ℝ) / q.totient| := by
  obtain ⟨⟨m, a⟩, hm, he⟩ := Finset.exists_mem_eq_sup'
    (s := (range (N + 1)).product (range (q + 1))) (by simp)
    (fun z : ℕ × ℕ => if Nat.Coprime z.2 q then |thetaN z.1 q z.2 - (z.1 : ℝ) / q.totient| else 0)
  by_cases ha : Nat.Coprime a q
  · exact ⟨m, a, by have := mem_range.mp (mem_product.mp hm).1; omega,
      ha, by simpa only [thetaError, if_pos ha] using he⟩
  · refine ⟨0, 1, Nat.zero_le _, Nat.coprime_one_left _, ?_⟩
    simpa only [thetaError, if_neg ha, thetaN, Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1),
      filter_empty, sum_empty, Nat.cast_zero, zero_div, sub_zero, abs_zero] using he

/-- Halupczok page 6, the finite maximum discrepancy mean with explicit level four D plus fifteen. -/
theorem thetaError_mean (D : ℝ) (hD : 0 < D) :
    ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∑ q ∈ Icc 1 ⌊Real.sqrt N / Real.log N ^ (4 * D + 15)⌋₊,
        thetaError N q ≤ K * N / Real.log N ^ D := by
  classical
  obtain ⟨K, hK⟩ := QuantitativeBV346.theta_fixed D hD
  refine ⟨K, fun N hN => ?_⟩
  choose m a hm ha he using thetaError_attained N
  simp_rw [he]
  have h := hK N (by exact_mod_cast hN) a ha (fun q => (m q : ℝ))
    (fun q => ⟨Nat.cast_nonneg _, by exact_mod_cast hm q⟩)
  simpa only [thetaAP, Nat.floor_natCast] using h

/-- Halupczok page 7, the exact atom prefix is the rational polynomial minus its linear main term. -/
theorem prefix_identity (k l q a m : ℕ) :
    (∑ n ∈ range (m + 1), atom k l q a n) =
      Sexp k l m ((a : ℝ) / q) - mainCoeff k l q a * (m : ℂ) := by
  have h := residual_eq_sum k l m q a 0
  simpa only [Decomp314a.residual, Decomp314a.approx, mainCoeff,
    add_zero, zero_mul, ee_zero, one_mul, mul_one, Decomp286a.geometric,
    sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_id] using h.symm

end LeanLab.Tolev2009.Discrepancy346
