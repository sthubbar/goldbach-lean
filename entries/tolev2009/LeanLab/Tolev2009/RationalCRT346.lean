module

public import LeanLab.Tolev2009.RationalPrefix346

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 pages 6 to 7, rational prime residue decomposition.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.RationalCRT346
open LeanLab.PNTPort.BVMax
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Progression346 LeanLab.Tolev2009.Discrepancy346
open LeanLab.Tolev2009.RationalPrefix346

/-- Halupczok page 6, reducing an admissible prime residue to the joint modulus. -/
theorem mod_mem_liftRes (k l q p : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    p % Nat.lcm k q ∈ liftRes k l q ↔
      p % k = l % k ∧ Nat.Coprime p (Nat.lcm k q) := by
  have hM : 0 < Nat.lcm k q := Nat.lcm_pos hk hq
  have hc := SeriesIdentification.coprime_modEq (Nat.lcm k q)
    (p % Nat.lcm k q) p (Nat.mod_mod p (Nat.lcm k q))
  simp only [liftRes, mem_filter, mem_range, Nat.mod_lt p hM,
    Nat.mod_mod_of_dvd p (Nat.dvd_lcm_left k q), hc, true_and]

/-- Halupczok page 6, a rational phase is unchanged on a joint residue class. -/
theorem phase_eq_lifted (k q a p r : ℕ) (hq : 1 ≤ q) (he : p % Nat.lcm k q = r) :
    ee ((a : ℝ) / q * p) = ee ((a : ℝ) * r / q) := by
  have hpq : p % q = r % q := by
    rw [← he, Nat.mod_mod_of_dvd p (Nat.dvd_lcm_right k q)]
  calc
    _ = ee ((a : ℝ) * p / q) := by congr 1; ring
    _ = ee ((a : ℝ) * (p % q : ℕ) / q) := SeriesIdentification.ee_rat_mod a p q hq
    _ = ee ((a : ℝ) * (r % q : ℕ) / q) := by rw [hpq]
    _ = _ := (SeriesIdentification.ee_rat_mod a r q hq).symm

/-- Halupczok page 6, the prime polynomial written on its positive integer interval. -/
theorem Sexp_eq_Icc (k l N : ℕ) (α : ℝ) :
    Sexp k l N α = ∑ p ∈ Icc 1 N,
      if p.Prime ∧ p % k = l % k then (Real.log p : ℂ) * ee (α * p) else 0 := by
  rw [← positive_sum]
  simp only [Sexp, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases h : p = 0
  · simp [h]
  · simp [h]

/-- Halupczok page 6, regroup the reduced prime part by the joint progression residue. -/
theorem lifted_theta_identity (k l N q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    (∑ p ∈ (Icc 1 N).filter (fun p => p.Prime ∧ p % k = l % k ∧
        Nat.Coprime p (Nat.lcm k q)), (Real.log p : ℂ) * ee ((a : ℝ) / q * p)) =
      ∑ r ∈ liftRes k l q, ee ((a : ℝ) * r / q) * (thetaN N (Nat.lcm k q) r : ℂ) := by
  let s := (Icc 1 N).filter (fun p => p.Prime ∧ p % k = l % k ∧ Nat.Coprime p (Nat.lcm k q))
  have hmap : ∀ p ∈ s, p % Nat.lcm k q ∈ liftRes k l q := by
    intro p hp
    exact (mod_mem_liftRes k l q p hk hq).mpr (mem_filter.mp hp).2.2
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro r hr
  have hrM : r < Nat.lcm k q := mem_range.mp (mem_filter.mp hr).1
  have hset : s.filter (fun p => p % Nat.lcm k q = r) =
      (Icc 1 N).filter (fun p => p % Nat.lcm k q = r % Nat.lcm k q ∧ p.Prime) := by
    ext p
    simp only [s, mem_filter, Nat.mod_eq_of_lt hrM]
    constructor
    · rintro ⟨⟨hp, hpprime, hpk, hcop⟩, hmod⟩
      exact ⟨hp, hmod, hpprime⟩
    · rintro ⟨hp, hmod, hpprime⟩
      have hplift : p % Nat.lcm k q ∈ liftRes k l q := by rw [hmod]; exact hr
      have hpc := (mod_mem_liftRes k l q p hk hq).mp hplift
      exact ⟨⟨hp, hpprime, hpc⟩, hmod⟩
  rw [hset]
  unfold thetaN
  rw [Complex.ofReal_sum, mul_sum]
  apply sum_congr rfl
  intro p hp
  have hmod := (mem_filter.mp hp).2.1
  rw [Nat.mod_eq_of_lt hrM] at hmod
  rw [phase_eq_lifted k q a p r hq hmod]
  ring

/-- Halupczok pages 6 to 7, the omitted primes not reduced modulo the joint modulus. -/
noncomputable def badPrimeSum (k l N q a : ℕ) : ℂ :=
  ∑ p ∈ Icc 1 N, if p.Prime ∧ p % k = l % k ∧ ¬ Nat.Coprime p (Nat.lcm k q)
    then (Real.log p : ℂ) * ee ((a : ℝ) / q * p) else 0

/-- Halupczok page 6, the exact rational prime polynomial split before any error bound. -/
theorem rational_prime_decomposition (k l N q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    Sexp k l N ((a : ℝ) / q) =
      (∑ r ∈ liftRes k l q, ee ((a : ℝ) * r / q) * (thetaN N (Nat.lcm k q) r : ℂ)) +
        badPrimeSum k l N q a := by
  rw [← lifted_theta_identity k l N q a hk hq, Sexp_eq_Icc]
  simp only [sum_filter, badPrimeSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime <;> by_cases hmod : p % k = l % k <;>
    by_cases hcop : Nat.Coprime p (Nat.lcm k q) <;> simp [hprime, hmod, hcop]

/-- Halupczok page 7, exact rational prefix error as lifted theta errors and bad primes. -/
theorem rational_prefix_identity (k l N q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    (∑ n ∈ range (N + 1), atom k l q a n) =
      (∑ r ∈ liftRes k l q, ee ((a : ℝ) * r / q) *
        ((thetaN N (Nat.lcm k q) r : ℂ) - (N : ℂ) / ((Nat.lcm k q).totient : ℂ))) +
          badPrimeSum k l N q a := by
  rw [prefix_identity, rational_prime_decomposition k l N q a hk hq,
    mainCoeff_eq_lifted k l q a hk hq]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, div_eq_mul_inv]
  ring

/-- Halupczok page 7, nonreduced primes in a reduced k progression are nonreduced modulo q. -/
theorem bad_prime_not_coprime_q (k l q p : ℕ) (hl : Nat.Coprime l k)
    (hpk : p % k = l % k) (hbad : ¬ Nat.Coprime p (Nat.lcm k q)) :
    ¬ Nat.Coprime p q := by
  intro hpq
  have hpc : Nat.Coprime p k := (SeriesIdentification.coprime_modEq k p l hpk).mpr hl
  exact hbad ((hpc.mul_right hpq).coprime_dvd_right (Nat.lcm_dvd_mul k q))

/-- Halupczok page 7, the omitted prime polynomial is bounded by the bad von Mangoldt mass. -/
theorem badPrimeSum_norm_le (k l N q a : ℕ) (hl : Nat.Coprime l k) :
    ‖badPrimeSum k l N q a‖ ≤ LeanLab.PNTPort.BV.psiBad N q := by
  unfold badPrimeSum LeanLab.PNTPort.BV.psiBad
  rw [Nat.floor_natCast, sum_filter]
  refine (norm_sum_le _ _).trans (sum_le_sum fun p hp => ?_)
  by_cases hc : p.Prime ∧ p % k = l % k ∧ ¬ Nat.Coprime p (Nat.lcm k q)
  · have hbad := bad_prime_not_coprime_q k l q p hl hc.2.1 hc.2.2
    simp only [if_pos hc, if_pos hbad, norm_mul, Displays14to16.norm_ee, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg p),
      ArithmeticFunction.vonMangoldt_apply_prime hc.1]
    exact le_rfl
  · rw [if_neg hc, norm_zero]
    split_ifs <;> first | exact le_rfl | exact ArithmeticFunction.vonMangoldt_nonneg

/-- Halupczok page 7, bad prime mass is bounded uniformly over every integer prefix. -/
theorem badPrimeSum_prefix_bound (k l m N q a : ℕ) (hl : Nat.Coprime l k)
    (hm : m ≤ N) (hN : 1 ≤ N) (hq : 1 ≤ q) :
    ‖badPrimeSum k l m q a‖ ≤ Real.log q / Real.log 2 * Real.log N := by
  refine (badPrimeSum_norm_le k l m q a hl).trans (le_trans ?_
    (LeanLab.PNTPort.BV.psiBad_le (by exact_mod_cast hN) hq))
  unfold LeanLab.PNTPort.BV.psiBad
  simp only [Nat.floor_natCast]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hp).1).1,
      (mem_Icc.mp (mem_filter.mp hp).1).2.trans hm⟩, (mem_filter.mp hp).2⟩
  · intro p hp hp'; exact ArithmeticFunction.vonMangoldt_nonneg

/-- Halupczok page 7, the rational atom prefix is bounded by lcm theta discrepancy and bad primes. -/
theorem prefix_norm_le_theta (k l m N q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) (hm : m ≤ N) :
    ‖∑ n ∈ range (m + 1), atom k l q a n‖ ≤
      (q : ℝ) * thetaError N (Nat.lcm k q) + ‖badPrimeSum k l m q a‖ := by
  rw [rational_prefix_identity k l m q a hk hq]
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ ∑ r ∈ liftRes k l q, ‖ee ((a : ℝ) * r / q) *
        ((thetaN m (Nat.lcm k q) r : ℂ) - (m : ℂ) / ((Nat.lcm k q).totient : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r ∈ liftRes k l q, thetaError N (Nat.lcm k q) := by
      apply sum_le_sum
      intro r hr
      have hrM := mem_range.mp (mem_filter.mp hr).1
      have hrc := (mem_filter.mp hr).2.2
      have he : (thetaN m (Nat.lcm k q) r : ℂ) - (m : ℂ) / ((Nat.lcm k q).totient : ℂ) =
          ((thetaN m (Nat.lcm k q) r - (m : ℝ) / (Nat.lcm k q).totient : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [norm_mul, Displays14to16.norm_ee, one_mul, he, Complex.norm_real, Real.norm_eq_abs]
      exact thetaError_term_le N (Nat.lcm k q) m r hm hrM.le hrc
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (thetaError_nonneg N _)
      exact_mod_cast lifted_card_le k l q hq

/-- Halupczok pages 6 to 7, a complete finite rational prime prefix to theta bridge.
The extra factor q is retained rather than claiming the printed cancellation estimate. -/
theorem prefixError_le_theta (k l N q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (hl : Nat.Coprime l k) (hN : 1 ≤ N) :
    prefixError k l q a N ≤ (q : ℝ) * thetaError N (Nat.lcm k q) +
      Real.log q / Real.log 2 * Real.log N := by
  unfold prefixError
  apply Finset.sup'_le
  intro m hm
  have hmN : m ≤ N := by have := mem_range.mp hm; omega
  exact (prefix_norm_le_theta k l m N q a hk hq hmN).trans
    (add_le_add le_rfl (badPrimeSum_prefix_bound k l m N q a hl hmN hN hq))

end LeanLab.Tolev2009.RationalCRT346
