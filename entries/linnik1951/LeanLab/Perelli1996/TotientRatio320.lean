module

public import LeanLab.Perelli1996.Totient400
public import LeanLab.Perelli1996.FactorBound

/-!
Perelli 1996, page 481 equation 2 and the arithmetic estimates in equation 3.
An elementary logarithmic bound for the totient ratio controls absolute principal coefficients.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.TotientRatio320
open Finset Real
noncomputable section

/-- The reciprocal Euler product for the positive totient ratio. -/
theorem ratio_eq_product (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / n.totient = ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hEuler : (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    exact h
  have hid : (∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
      (∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp <;> ring
  apply (div_eq_iff hφ.ne').mpr
  rw [hEuler]
  nlinarith [congrArg (fun x : ℝ => (n : ℝ) * x) hid]

/-- The totient ratio is at most twice one plus log n, for every positive n. -/
theorem ratio_le_log (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / n.totient ≤ 2 * (1 + Real.log n) := by
  classical
  let s := n.primeFactors
  have hs (p : ℕ) (hp : p ∈ s) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hshift : ∀ p ∈ s.image (fun p => p + 1), 3 ≤ p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have := (hs q hq).two_le
    omega
  have hC' := B.prod_ge_half (s.image (fun p => p + 1)) hshift
  have hC : (1 : ℝ) / 2 ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2) := by
    rw [Finset.prod_image (by intro a ha b hb h; dsimp at h; omega)] at hC'
    simpa using hC'
  have hid : (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) *
      (∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2)) = ∏ p ∈ s, (1 + 1 / (p : ℝ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp <;> ring
  let D : ℕ := ∏ p ∈ s, p
  have hDsq : Squarefree D := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
    · intro p hp
      exact (hs p hp).squarefree
  have hDprime : D.primeFactors = s := Nat.primeFactors_prod_primeFactors n
  let af : ArithmeticFunction ℝ := ⟨fun d => (d : ℝ)⁻¹, by simp⟩
  have haf : af.IsMultiplicative := by
    refine ⟨by simp [af], fun {a b} _ => ?_⟩
    change ((a * b : ℕ) : ℝ)⁻¹ = (a : ℝ)⁻¹ * (b : ℝ)⁻¹
    simp [mul_comm]
  have hsum : (∏ p ∈ s, (1 + 1 / (p : ℝ))) = ∑ d ∈ D.divisors, (d : ℝ)⁻¹ := by
    have h := haf.prodPrimeFactors_one_add_of_squarefree hDsq
    rw [hDprime] at h
    simpa [af, one_div] using h
  have hsub : D.divisors ⊆ Icc 1 n := by
    intro d hd
    have hdn : d ∣ n := dvd_trans (Nat.dvd_of_mem_divisors hd) (Nat.prod_primeFactors_dvd n)
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hn hdn⟩
  have hE : (∏ p ∈ s, (1 + 1 / (p : ℝ))) ≤ 1 + Real.log n := by
    rw [hsum]
    calc
      _ ≤ ∑ d ∈ Icc 1 n, (d : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = (harmonic n : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ _ := harmonic_le_one_add_log n
  have hR : 0 ≤ ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).two_le
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hC hR
  rw [ratio_eq_product n hn]
  change (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) ≤ _
  nlinarith [hid, hE, hmul]

end
end LeanLab.Perelli1996.TotientRatio320
