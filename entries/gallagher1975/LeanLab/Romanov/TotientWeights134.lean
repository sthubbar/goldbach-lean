module

public import LeanLab.Romanov.Decomp134b
public import LeanLab.Romanov.HalfOrder

/-!
# Reciprocal totient weights for the SigmaOne connection

Gallagher pages 133 to 136, the divisor expansion and order weight bounds.
The explicit constants are the existing lab constants from HalfOrder.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.Romanov.TotientWeights134

open Finset Real
open LeanLab.Romanov.Decomp134b
open LeanLab.LPZ2007
open LeanLab.LPZ2007.Lemma61Port

/-- The Moebius squared weight vanishes outside squarefree integers. -/
theorem totientWeight_zero_of_not_squarefree {q : ℕ} (hq : ¬ Squarefree q) :
    totientWeight q = 0 := by
  simp [totientWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]

/-- The reciprocal totient weight is dominated by the existing Gallagher order weight. -/
theorem totientWeight_le_fd {q : ℕ} (hq : OddSqf q) : totientWeight q ≤ fd q := by
  have hmu : ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq.2
  have hphi := inverse_totient_prime_product q.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [Nat.prod_primeFactors_of_squarefree hq.2] at hphi
  rw [totientWeight, hmu, hphi, fd_eq hq]
  apply prod_le_prod₀
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : 0 < (p : ℝ) - 1 := by linarith
    positivity
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      intro h
      exact hq.1.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors hp)
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (by have := hprime.two_le; omega : 3 ≤ p)
    exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- The reciprocal totient order series is bounded by the proved square root order series. -/
theorem weight_order_sum_le (T : Finset ℕ) (hT : ∀ q ∈ T, OddSqf q) :
    ∑ q ∈ T, totientWeight q / xi q ≤ 16 * log 2 * exp 27 := by
  have hcomp (q : ℕ) (hq : q ∈ T) : totientWeight q / xi q ≤ halfOrderTerm q := by
    have hs := xi_spec_sqf (hT q hq)
    have hx1 : (1 : ℝ) ≤ xi q := by exact_mod_cast hs.1
    have hx0 : (0 : ℝ) < xi q := by linarith
    rw [halfOrderTerm, ite_eq_left (hT q hq)]
    calc totientWeight q / xi q ≤ fd q / xi q :=
          div_le_div_of_nonneg_right (totientWeight_le_fd (hT q hq)) hx0.le
      _ ≤ fd q / sqrt (xi q) := div_le_div_of_nonneg_left (fd_nonneg (hT q hq))
        (sqrt_pos.mpr hx0) (sqrt_le_self_iff.mpr (Or.inr hx1))
  exact (sum_le_sum hcomp).trans
    ((halfOrder_summable.sum_le_tsum T (fun q _ => halfOrderTerm_nonneg q)).trans halfOrder_tsum_le)

/-- The complete weight on an order block has the same bound as the existing fd weight. -/
theorem weight_block_sum_le (T : Finset ℕ) (j : ℕ)
    (hT : ∀ q ∈ T, OddSqf q ∧ xi q < 2 ^ (j + 1)) :
    ∑ q ∈ T, totientWeight q ≤ exp 27 * (2 * (j + 1) * log 2) := by
  exact (sum_le_sum (fun q hq => totientWeight_le_fd (hT q hq).1)).trans
    (order_block_weight_le T j hT)

/-- Gallagher page 133, the weight over moduli at most X is logarithmic. -/
theorem weight_sum_le_log (T : Finset ℕ) (X : ℕ) (hX : 1 ≤ X)
    (hT : ∀ q ∈ T, OddSqf q ∧ q ≤ X) :
    ∑ q ∈ T, totientWeight q ≤ 2 * exp 27 * log (2 * X) := by
  set j := Nat.log 2 X
  have hb := weight_block_sum_le T j (fun q hq => by
    refine ⟨(hT q hq).1, ?_⟩
    have hxi := (xi_spec_sqf (hT q hq).1).2.1
    exact lt_of_le_of_lt (hxi.trans (hT q hq).2)
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X))
  have hpow : (2 : ℝ) ^ j ≤ X := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : X ≠ 0)
  have hpow' : (2 : ℝ) ^ (j + 1) ≤ 2 * X := by rw [pow_succ]; nlinarith
  have hlog := log_le_log (by positivity : (0 : ℝ) < 2 ^ (j + 1)) hpow'
  rw [log_pow] at hlog
  push_cast at hlog hb
  calc ∑ q ∈ T, totientWeight q ≤ exp 27 * (2 * ((j : ℝ) + 1) * log 2) := hb
    _ ≤ exp 27 * (2 * log (2 * X)) :=
      mul_le_mul_of_nonneg_left (by linarith) (exp_pos 27).le
    _ = _ := by ring

/-- Gallagher pages 135 and 136, a logarithmic power cutoff costs at most a multiple of log n. -/
theorem weight_cutoff_sum_le (T : Finset ℕ) (n d : ℕ) (hn : 3 ≤ n)
    (hT : ∀ q ∈ T, OddSqf q ∧ (q : ℝ) ≤ log n ^ d) :
    ∑ q ∈ T, totientWeight q ≤ 2 * exp 27 * ((d : ℝ) + 1) * log n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 1 < log (n : ℝ) := by
    rw [lt_log_iff_exp_lt (by linarith)]
    have h := exp_one_lt_d9
    linarith
  set X : ℕ := ⌊log (n : ℝ) ^ d⌋₊
  have hX : 1 ≤ X := Nat.le_floor (a := log (n : ℝ) ^ d)
    (by simpa using one_le_pow₀ hlogn.le)
  have hb := weight_sum_le_log T X hX (fun q hq => ⟨(hT q hq).1, Nat.le_floor (hT q hq).2⟩)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hln : log (X : ℝ) ≤ d * log (log n) := by
    calc log (X : ℝ) ≤ log (log (n : ℝ) ^ d) := log_le_log hXpos (Nat.floor_le (by positivity))
      _ = _ := log_pow _ _
  have hlog2 : log (2 : ℝ) ≤ log n := log_le_log (by norm_num) (by linarith)
  have hll : log (log n) ≤ log n := by
    have h := log_le_sub_one_of_pos (show 0 < log (n : ℝ) by linarith)
    linarith
  have hbound : log (2 * X) ≤ ((d : ℝ) + 1) * log n := by
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne']
    have hmul := mul_le_mul_of_nonneg_left hll (Nat.cast_nonneg d)
    nlinarith
  calc ∑ q ∈ T, totientWeight q ≤ 2 * exp 27 * log (2 * X) := hb
    _ ≤ 2 * exp 27 * (((d : ℝ) + 1) * log n) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

end LeanLab.Romanov.TotientWeights134
