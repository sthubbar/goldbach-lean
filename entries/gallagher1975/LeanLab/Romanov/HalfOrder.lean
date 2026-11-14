module

public import LeanLab.LPZ2007.Lemma61Port
public import LeanLab.HeathBrownPuchta.Lemma8Const

/-!
# The square root order series in Heath-Brown and Puchta

AI wrote the Lean code. Known mathematics. arXiv math/0201299v2, page 21,
the convergent series before display 36. The proof groups orders in powers of four.
Binary Goldbach is OPEN.
-/

@[expose] public section


noncomputable section
namespace LeanLab.Romanov

open Finset Real
open LeanLab.LPZ2007
open LeanLab.LPZ2007.Lemma61Port

attribute [local instance] Classical.propDecidable

/-- A finite order block of the Gallagher weight, in the encoding used by HBP. -/
theorem order_block_weight_le (T : Finset ℕ) (j : ℕ)
    (hT : ∀ d ∈ T, OddSqf d ∧ xi d < 2 ^ (j + 1)) :
    ∑ d ∈ T, fd d ≤ exp 27 * (2 * (j + 1) * log 2) := by
  calc ∑ d ∈ T, fd d = ∑ d ∈ T, ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) :=
        sum_congr rfl fun d hd => fd_eq (hT d hd).1
    _ = ∑ s ∈ T.image Nat.primeFactors, ∏ p ∈ s, 1 / ((p : ℝ) - 2) := by
        rw [sum_image]
        intro a ha b hb hab
        rw [← Nat.prod_primeFactors_of_squarefree (hT a ha).1.2,
          ← Nat.prod_primeFactors_of_squarefree (hT b hb).1.2, hab]
    _ ≤ ∑ s ∈ (M j).primeFactors.powerset, ∏ p ∈ s, 1 / ((p : ℝ) - 2) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro s hs
          obtain ⟨d, hd, rfl⟩ := mem_image.mp hs
          have hsp := xi_spec_sqf (hT d hd).1
          rw [mem_powerset]
          exact Nat.primeFactors_mono (hsp.2.2.trans (dvd_M hsp.1 (hT d hd).2)) (M_ne_zero j)
        · intro s hs _
          apply prod_nonneg
          intro p hp
          have h3 : (3 : ℝ) ≤ p := by exact_mod_cast pf_M_ge_three j p (mem_powerset.mp hs hp)
          have : 0 < (p : ℝ) - 2 := by linarith
          positivity
    _ ≤ exp 27 * (2 * (j + 1) * log 2) := sumH_M_le j

/-- A powers of four block gains a geometric square root denominator. -/
theorem halfOrder_block_le (T : Finset ℕ) (j : ℕ)
    (hT : ∀ d ∈ T, OddSqf d ∧ Nat.log 4 (xi d) = j) :
    ∑ d ∈ T, fd d / sqrt (xi d) ≤
      (4 * log 2 * exp 27) * (((j : ℝ) + 1) / 2 ^ j) := by
  have hfour (j : ℕ) : (4 : ℕ) ^ j = 2 ^ (2 * j) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hweight := order_block_weight_le T (2 * j + 1) (fun d hd => by
    refine ⟨(hT d hd).1, ?_⟩
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) (xi d)
    rw [(hT d hd).2, hfour] at h
    convert h using 1)
  push_cast at hweight
  calc ∑ d ∈ T, fd d / sqrt (xi d) ≤ ∑ d ∈ T, fd d / 2 ^ j := by
        apply sum_le_sum
        intro d hd
        have hs := xi_spec_sqf (hT d hd).1
        have hp : 4 ^ j ≤ xi d := by
          rw [← (hT d hd).2]
          exact Nat.pow_log_le_self 4 (by omega)
        have hr : ((2 : ℝ) ^ j) ^ 2 ≤ xi d := by
          rw [← pow_mul, mul_comm j 2]
          have h := hfour j
          exact_mod_cast (by rw [← h]; exact hp)
        exact div_le_div_of_nonneg_left (fd_nonneg (hT d hd).1) (by positivity)
          (Real.le_sqrt_of_sq_le hr)
    _ = (∑ d ∈ T, fd d) / 2 ^ j := by rw [sum_div]
    _ ≤ (exp 27 * (2 * (2 * j + 1 + 1) * log 2)) / 2 ^ j :=
        div_le_div_of_nonneg_right hweight (by positivity)
    _ = (4 * log 2 * exp 27) * (((j : ℝ) + 1) / 2 ^ j) := by ring

/-- The nonnegative square root order summand. -/
def halfOrderTerm (d : ℕ) : ℝ :=
  if OddSqf d then fd d / sqrt (xi d) else 0

theorem halfOrderTerm_nonneg (d : ℕ) : 0 ≤ halfOrderTerm d := by
  unfold halfOrderTerm
  split_ifs with h
  · exact div_nonneg (fd_nonneg h) (sqrt_nonneg _)
  · exact le_rfl

/-- An explicit uniform bound for all partial sums of the square root order series. -/
theorem halfOrder_partial_le (D : ℕ) :
    ∑ d ∈ range D, halfOrderTerm d ≤ 16 * log 2 * exp 27 := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  set F := (range D).filter OddSqf
  have hmaps : ∀ d ∈ F, Nat.log 4 (xi d) ∈ range (D + 1) := by
    intro d hd
    simp only [F, mem_filter, mem_range] at hd
    have hxi := (xi_spec_sqf hd.2).2.1
    have hl := Nat.log_le_self 4 (xi d)
    rw [mem_range]
    omega
  have heq : ∑ d ∈ range D, halfOrderTerm d = ∑ d ∈ F, fd d / sqrt (xi d) := by
    unfold halfOrderTerm
    rw [← sum_filter]
  rw [heq, ← sum_fiberwise_of_maps_to hmaps]
  calc ∑ j ∈ range (D + 1), ∑ d ∈ F with Nat.log 4 (xi d) = j, fd d / sqrt (xi d)
      ≤ ∑ j ∈ range (D + 1), (4 * log 2 * exp 27) * (((j : ℝ) + 1) / 2 ^ j) := by
        apply sum_le_sum
        intro j _
        apply halfOrder_block_le
        intro d hd
        simp only [mem_filter, F] at hd
        exact ⟨hd.1.2, hd.2⟩
    _ = (4 * log 2 * exp 27) * ∑ j ∈ range (D + 1), (((j : ℝ) + 1) / 2 ^ j) := by
        rw [mul_sum]
    _ ≤ (4 * log 2 * exp 27) * 4 :=
        mul_le_mul_of_nonneg_left (sum_succ_div_pow_le _) (by positivity)
    _ = 16 * log 2 * exp 27 := by ring

/-- The square root order series converges unconditionally. -/
theorem halfOrder_summable : Summable halfOrderTerm :=
  summable_of_sum_range_le halfOrderTerm_nonneg halfOrder_partial_le

/-- The explicit bound applies to the infinite sum. -/
theorem halfOrder_tsum_le : ∑' d, halfOrderTerm d ≤ 16 * log 2 * exp 27 :=
  Real.tsum_le_of_sum_range_le halfOrderTerm_nonneg halfOrder_partial_le

open LeanLab.HeathBrownPuchta.Lemma8Const in
/-- The summand is exactly the one in HBP before display 36. -/
theorem hbp_halfOrder_term (d : ℕ) :
    (k d : ℝ) / sqrt (eps d) = halfOrderTerm d := by
  by_cases hd : OddSqf d
  · have hk : (k d : ℝ) = fd d := by
      rw [k, ite_eq_left (show Odd d ∧ Squarefree d from hd), fd_eq hd]
      push_cast
      rfl
    change (k d : ℝ) / sqrt (xi d) = halfOrderTerm d
    rw [halfOrderTerm, ite_eq_left hd, hk]
  · have hk : k d = 0 := by rw [k, ite_eq_right (show ¬(Odd d ∧ Squarefree d) from hd)]
    simp [halfOrderTerm, hd, hk]

open LeanLab.HeathBrownPuchta.Lemma8Const in
/-- HBP's exact square root order series converges. -/
theorem hbp_36_summable : Summable (fun d : ℕ => (k d : ℝ) / sqrt (eps d)) := by
  simpa only [hbp_halfOrder_term] using halfOrder_summable

open LeanLab.HeathBrownPuchta.Lemma8Const in
/-- HBP's exact series has an explicit absolute bound. -/
theorem hbp_36_tsum_le :
    ∑' d : ℕ, (k d : ℝ) / sqrt (eps d) ≤ 16 * log 2 * exp 27 := by
  simpa only [hbp_halfOrder_term] using halfOrder_tsum_le

end LeanLab.Romanov
