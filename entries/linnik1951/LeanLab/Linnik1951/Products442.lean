module

public import LeanLab.Linnik1951.TailBridge376
public import LeanLab.PNTSieve.MertensProduct

/-!
P0093 page 168 equations 10.6 and 10.7. Logarithmic splitting of odd prime factors.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 168 equation 10.6. The number of distinct prime
factors times log two is at most log n for every positive n. -/
theorem prime_factor_card_log442 (n : ℕ) (hn : 1 ≤ n) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
  have hp : 2 ^ n.primeFactors.card ≤ n :=
    (Finset.pow_card_le_prod n.primeFactors (fun p => p) 2
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)).trans
        (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n))
  have hpr : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast hp
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ n.primeFactors.card) hpr
  rwa [Real.log_pow] at hh

/-- P0093 page 168 equation 10.6, small prime part. The proved
PNTSieve Mertens density lower bound gives an upper bound exp of
36 times log Y for any subproduct of odd primes at most Y. -/
theorem small_prime_product442 (Y : ℕ) (hY : 3 ≤ Y) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p ∧ p ≤ Y) :
    (∏ p ∈ S, (((p : ℝ) - 1) / ((p : ℝ) - 2))) ≤ Real.exp 36 * Real.log Y := by
  have hYr : (3 : ℝ) ≤ Y := by exact_mod_cast hY
  have hlog : 0 < Real.log Y := Real.log_pos (by linarith)
  have hm := LeanLab.PNTSieve.Mertens.prod_one_sub_inv_pred_ge Y hY S hS
  have hi := one_div_le_one_div_of_le
    (show (0 : ℝ) < Real.exp (-36) / Real.log Y by positivity) hm
  have he : (∏ p ∈ S, (((p : ℝ) - 1) / ((p : ℝ) - 2))) =
      1 / (∏ p ∈ S, (1 - (1 : ℝ) / ((p : ℝ) - 1))) := by
    calc
      _ = ∏ p ∈ S, (1 / (1 - (1 : ℝ) / ((p : ℝ) - 1))) := by
        apply prod_congr rfl
        intro p hp
        have hpR : (3 : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1
        have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
        have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
        have hd : 1 - (1 : ℝ) / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
          field_simp [hp1]
          <;> ring
        rw [hd, one_div_div]
      _ = _ := by simp only [one_div, Finset.prod_inv_distrib]
  rw [he]
  refine hi.trans (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

/-- P0093 page 168 equation 10.6, large prime part. For a positive
integer n and cutoff Y at least three and at least log n, the odd
prime factor product beyond Y is bounded by exp of two over log two.
Each local factor is bounded by exp of two over Y. -/
theorem large_prime_product442 (n Y : ℕ) (hn : 1 ≤ n) (hY : 3 ≤ Y)
    (hlog : Real.log n ≤ (Y : ℝ)) (S : Finset ℕ) (hS : S ⊆ n.primeFactors)
    (hlarge : ∀ p ∈ S, Y < p) :
    (∏ p ∈ S, (((p : ℝ) - 1) / ((p : ℝ) - 2))) ≤ Real.exp (2 / Real.log 2) := by
  have hYr : (3 : ℝ) ≤ Y := by exact_mod_cast hY
  have hYp : (0 : ℝ) < Y := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (S.card : ℝ) * Real.log 2 ≤ (Y : ℝ) := by
    have hc : (S.card : ℝ) ≤ n.primeFactors.card := by exact_mod_cast Finset.card_le_card hS
    exact ((mul_le_mul_of_nonneg_right hc hl2.le).trans (prime_factor_card_log442 n hn)).trans hlog
  have hfac (p : ℕ) (hp : p ∈ S) : ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ Real.exp (2 / (Y : ℝ)) := by
    have hpNat : Y + 1 ≤ p := by have := hlarge p hp; omega
    have hpR : (Y : ℝ) + 1 ≤ p := by exact_mod_cast hpNat
    have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have hrec : 1 / ((p : ℝ) - 2) ≤ 2 / (Y : ℝ) := by
      rw [div_le_div_iff₀ hp2 hYp]
      linarith
    calc
      _ = 1 + 1 / ((p : ℝ) - 2) := by field_simp [hp2.ne'] <;> ring
      _ ≤ 1 + 2 / (Y : ℝ) := by linarith
      _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (2 / (Y : ℝ))
  have hexp : (S.card : ℝ) * (2 / (Y : ℝ)) ≤ 2 / Real.log 2 := by
    rw [← mul_div_assoc, div_le_div_iff₀ hYp hl2]
    nlinarith
  calc
    _ ≤ ∏ _p ∈ S, Real.exp (2 / (Y : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hpR : (Y : ℝ) < p := by exact_mod_cast hlarge p hp
        exact div_nonneg (by linarith) (by linarith)
      · exact hfac
    _ = Real.exp ((S.card : ℝ) * (2 / (Y : ℝ))) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr hexp

/-- P0093 page 168 equation 10.6. Splitting the odd prime divisors
at any integer Y at least three and at least log n gives an upper
bound C log Y with explicit absolute C. It does not assert the
paper's absolute uniform upper bound. -/
theorem odd_prime_product_log_cutoff442 (n Y : ℕ) (hn : 1 ≤ n) (hY : 3 ≤ Y)
    (hlog : Real.log n ≤ (Y : ℝ)) :
    (∏ p ∈ n.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))) ≤
      (Real.exp 36 * Real.exp (2 / Real.log 2)) * Real.log Y := by
  classical
  let P := n.primeFactors.filter (2 < ·)
  let S := P.filter (fun p => p ≤ Y)
  let T := P.filter (fun p => ¬ p ≤ Y)
  have hs := small_prime_product442 Y hY S (by
    intro p hp
    obtain ⟨hpP, hpY⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpn, hp2⟩ := Finset.mem_filter.mp hpP
    exact ⟨Nat.prime_of_mem_primeFactors hpn, by omega, hpY⟩)
  have ht := large_prime_product442 n Y hn hY hlog T
    (by intro p hp; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
    (by intro p hp; exact lt_of_not_ge (Finset.mem_filter.mp hp).2)
  have he : (∏ p ∈ P, (((p : ℝ) - 1) / ((p : ℝ) - 2))) =
      (∏ p ∈ S, (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
        (∏ p ∈ T, (((p : ℝ) - 1) / ((p : ℝ) - 2))) := by
    exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  change (∏ p ∈ P, (((p : ℝ) - 1) / ((p : ℝ) - 2))) ≤ _
  rw [he]
  have hT0 : 0 ≤ ∏ p ∈ T, (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply prod_nonneg
    intro p hp
    have hp2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hpR : (2 : ℝ) < p := by exact_mod_cast hp2
    exact div_nonneg (by linarith) (by linarith)
  have hYlog : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
  have hh := mul_le_mul hs ht hT0 (mul_nonneg (Real.exp_pos _).le hYlog)
  refine hh.trans (le_of_eq ?_)
  ring

end LeanLab.Linnik1951
