module

public import Mathlib

/-!
P0093 page 161, the sentence after equation 6.3: the relative estimate of the convolution
sum of 1 over ln m ln m prime over m plus m prime equal to n.
Burst 8 p3 port, AI wrote the Lean code. Binary Goldbach is open.

The lab proves this cleanly as log_convolution_estimate487 in Decomp487c, from
SPLIT1622_major, SPLIT_log_convolution_estimate1622 and SPLIT_logConv_excess1622. Those
modules sit downstream of Decomp111, so this file copies the needed declarations with the
same proofs, renamed with the suffix _lc111, on top of Mathlib only.
-/

@[expose] public section

namespace LeanLab.Linnik1951

section PortSPLIT1622_major


/-- PORT of logConvolution1622 from SPLIT1622_major, same proof, renamed so that Major81Split111 can use it.
 P0093 page 161 after equation 6.3. The sum of 1 over ln m ln m' over m + m' = n
with both at least 2. It is empty for n below 4. -/
noncomputable def logConvolution1622_lc111 (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log m * Real.log (n - m : ℕ))

/-- PORT of logConvolution_four1622 from SPLIT1622_major, same proof, renamed so that Major81Split111 can use it.
 Vacuity instance: at n equal to 4 the convolution is the single term at m equal to 2. -/
theorem logConvolution_four1622_lc111 :
    logConvolution1622_lc111 4 = 1 / (Real.log 2 * Real.log 2) := by
  simp [logConvolution1622_lc111]

end PortSPLIT1622_major


section PortSPLIT_log_convolution_estimate1622
open MeasureTheory

/-- PORT of log_two_pos1622 from SPLIT_log_convolution_estimate1622, same proof. -/
private lemma log_two_pos1622_lc111 : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- PORT of log_four_eq1622 from SPLIT_log_convolution_estimate1622, same proof. -/
private lemma log_four_eq1622_lc111 : Real.log 4 = 2 * Real.log 2 := by
  have h : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h, Real.log_pow]
  norm_num

/-- PORT of log_three_le1622 from SPLIT_log_convolution_estimate1622, same proof, renamed so that Major81Split111 can use it.
 `log 3` is at most `2 log 2 - 1/4`, from `log (3/4) ≤ 3/4 - 1`. -/
private lemma log_three_le1622_lc111 : Real.log 3 ≤ 2 * Real.log 2 - 1 / 4 := by
  have h : Real.log 4 + Real.log (3 / 4) = Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h34 : Real.log (3 / 4) ≤ 3 / 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := log_four_eq1622_lc111
  linarith

/-- PORT of log_five_ge1622 from SPLIT_log_convolution_estimate1622, same proof, renamed so that Major81Split111 can use it.
 `log 5` is at least `2 log 2 + 1/5`, from `1 - 1/x ≤ log x` at `x = 5/4`. -/
private lemma log_five_ge1622_lc111 : 2 * Real.log 2 + 1 / 5 ≤ Real.log 5 := by
  have h : Real.log 4 + Real.log (5 / 4) = Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h54 : 1 - (5 / 4 : ℝ)⁻¹ ≤ Real.log (5 / 4) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := log_four_eq1622_lc111
  have hc : (1 : ℝ) - (5 / 4 : ℝ)⁻¹ = 1 / 5 := by norm_num
  linarith

/-- PORT of log_six_ge1622 from SPLIT_log_convolution_estimate1622, same proof, renamed so that Major81Split111 can use it.
 `log 6` is at least `(5/2) log 2`, because `4 * sqrt 2 ≤ 6`. -/
private lemma log_six_ge1622_lc111 : 5 / 2 * Real.log 2 ≤ Real.log 6 := by
  have hsqrt : Real.log (Real.sqrt 2) = Real.log 2 / 2 := Real.log_sqrt (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := log_four_eq1622_lc111
  have hmul : Real.log 4 + Real.log (Real.sqrt 2) = Real.log (4 * Real.sqrt 2) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  have hle : 4 * Real.sqrt 2 ≤ 6 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hlog : Real.log (4 * Real.sqrt 2) ≤ Real.log 6 :=
    Real.log_le_log (by positivity) hle
  linarith

/-- PORT of exp_seven_ge1622 from SPLIT_log_convolution_estimate1622, same proof, renamed so that Major81Split111 can use it.
 `1000 ≤ exp 7`. -/
private lemma exp_seven_ge1622_lc111 : (1000 : ℝ) ≤ Real.exp 7 := by
  have hexp : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (2.7182818283 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by
    exact pow_le_pow_left₀ (by norm_num) h1.le 7
  nlinarith

/-- PORT of logConv_main_le1622 from SPLIT_log_convolution_estimate1622, same proof, renamed so that Major81Split111 can use it.
 LEAF. Scale control, main term is dominated: from n equal to 4 upwards the
convolution sum is at least n / (log n)^2. The sum has about n terms each of size
about 1 / (log n)^2, and this leaf asserts only the one-sided floor, with no error
term. It is the step that removes the absolute value in the large range. -/
theorem logConv_main_le1622_lc111 (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) / Real.log n ^ 2 ≤ logConvolution1622_lc111 n := by
  have h2pos : 0 < Real.log 2 := log_two_pos1622_lc111
  rcases eq_or_lt_of_le hn with h4 | h4
  · -- n = 4: the sum is the single term at m = 2, and log 4 = 2 log 2
    subst h4
    rw [logConvolution_four1622_lc111]
    push_cast
    rw [log_four_eq1622_lc111]
    have h2 : Real.log 2 ≠ 0 := h2pos.ne'
    field_simp
    norm_num
  · rcases eq_or_lt_of_le (show 5 ≤ n by omega) with h5 | h5
    · -- n = 5: two terms, both equal to 1 / (log 2 * log 3)
      subst h5
      have hval : logConvolution1622_lc111 5 = 2 / (Real.log 2 * Real.log 3) := by
        have hset : Finset.Icc 2 (5 - 2) = ({2, 3} : Finset ℕ) := by decide
        rw [logConvolution1622_lc111, hset, Finset.sum_pair (by norm_num)]
        norm_num
        field_simp
        try ring
      rw [hval]
      push_cast
      have ha1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have ha2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have h3 : Real.log 3 ≤ 2 * Real.log 2 - 1 / 4 := log_three_le1622_lc111
      have h5b : 2 * Real.log 2 + 1 / 5 ≤ Real.log 5 := log_five_ge1622_lc111
      have hL3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have hL5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
      have h3' : 5 * Real.log 2 * Real.log 3 ≤ 5 * Real.log 2 * (2 * Real.log 2 - 1 / 4) := by
        apply mul_le_mul_of_nonneg_left h3
        linarith
      have h5sq : (2 * Real.log 2 + 1 / 5) ^ 2 ≤ Real.log 5 ^ 2 := by
        have hpos : (0 : ℝ) ≤ Real.log 5 - (2 * Real.log 2 + 1 / 5) := by linarith
        have hsum : (0 : ℝ) ≤ Real.log 5 + (2 * Real.log 2 + 1 / 5) := by linarith
        nlinarith [hpos, hsum]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h3', h5sq, ha1, ha2]
    · -- n ≥ 6: two end terms of size 1 / (log 2 * log (n-2)), the rest at 1 / L^2
      have hn6 : 6 ≤ n := h5
      set L : ℝ := Real.log (n : ℝ) with hL
      have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      have hLpos : 0 < L := by rw [hL]; exact Real.log_pos hnR
      have hdecomp : Finset.Icc 2 (n - 2) = insert 2 (insert (n - 2) (Finset.Icc 3 (n - 3))) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hmem1 : (2 : ℕ) ∉ insert (n - 2) (Finset.Icc 3 (n - 3)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hmem2 : (n - 2) ∉ Finset.Icc 3 (n - 3) := by
        simp only [Finset.mem_Icc]
        omega
      have hmid : ∀ m ∈ Finset.Icc 3 (n - 3),
          1 / L ^ 2 ≤ 1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) := by
        intro m hm
        simp only [Finset.mem_Icc] at hm
        obtain ⟨hm3, hmn⟩ := hm
        have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
        have hnm1 : (1 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n - m)
        have hmpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
        have hnmpos : 0 < Real.log ((n - m : ℕ) : ℝ) := Real.log_pos hnm1
        have h1 : Real.log (m : ℝ) ≤ L := by
          rw [hL]
          exact Real.log_le_log (by exact_mod_cast (by omega : 0 < m))
            (by exact_mod_cast (by omega : m ≤ n))
        have h2 : Real.log ((n - m : ℕ) : ℝ) ≤ L := by
          rw [hL]
          exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n - m))
            (by exact_mod_cast (by omega : n - m ≤ n))
        have hprod : Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) ≤ L * L :=
          mul_le_mul h1 h2 hnmpos.le hLpos.le
        have hpos : 0 < Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) := mul_pos hmpos hnmpos
        have h := one_div_le_one_div_of_le hpos hprod
        simpa [pow_two] using h
      have hcard : (Finset.Icc 3 (n - 3)).card = n - 5 := by
        rw [Nat.card_Icc]
        omega
      have hsum_ge : ((n - 5 : ℕ) : ℝ) * (1 / L ^ 2) ≤
          ∑ m ∈ Finset.Icc 3 (n - 3), 1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) := by
        have h := Finset.sum_le_sum hmid
        rw [Finset.sum_const, hcard, nsmul_eq_mul] at h
        exact h
      have hlogend : 0 < Real.log ((n - 2 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < n - 2))
      have hleend : Real.log ((n - 2 : ℕ) : ℝ) ≤ L := by
        rw [hL]
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n - 2))
          (by exact_mod_cast (by omega : n - 2 ≤ n))
      have hend1 : 1 / (Real.log 2 * L) ≤ 1 / (Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ)) :=
        one_div_le_one_div_of_le (mul_pos h2pos hlogend)
          (mul_le_mul_of_nonneg_left hleend h2pos.le)
      have hend2 : 1 / (L * Real.log 2) ≤ 1 / (Real.log ((n - 2 : ℕ) : ℝ) * Real.log 2) :=
        one_div_le_one_div_of_le (mul_pos hlogend h2pos)
          (mul_le_mul_of_nonneg_right hleend h2pos.le)
      have h5a : 5 * Real.log 2 ≤ 2 * L := by
        have h6 : 5 / 2 * Real.log 2 ≤ Real.log 6 := log_six_ge1622_lc111
        have h6n : Real.log 6 ≤ L := by
          rw [hL]
          exact Real.log_le_log (by norm_num) (by exact_mod_cast hn6)
        linarith
      have h5div : (5 : ℝ) / L ^ 2 ≤ 2 / (Real.log 2 * L) := by
        rw [div_le_div_iff₀ (by nlinarith [hLpos] : (0 : ℝ) < L ^ 2) (mul_pos h2pos hLpos)]
        have hh := mul_le_mul_of_nonneg_right h5a hLpos.le
        nlinarith [hh]
      have htwo : 2 / (Real.log 2 * L) = 1 / (Real.log 2 * L) + 1 / (L * Real.log 2) := by
        have h2 : Real.log 2 ≠ 0 := h2pos.ne'
        field_simp
        try ring
      have hkey : (n : ℝ) / L ^ 2 ≤ 2 / (Real.log 2 * L) + ((n - 5 : ℕ) : ℝ) * (1 / L ^ 2) := by
        have hc : ((n - 5 : ℕ) : ℝ) = (n : ℝ) - 5 := by
          rw [Nat.cast_sub (show 5 ≤ n by omega)]
          push_cast
          ring
        have hid1 : (n : ℝ) / L ^ 2 = (5 : ℝ) / L ^ 2 + ((n : ℝ) - 5) * (1 / L ^ 2) := by
          field_simp
          try ring
        rw [hid1, hc]
        linarith [h5div]
      have hgoal : (n : ℝ) / L ^ 2 ≤
          1 / (Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ)) +
            (1 / (Real.log ((n - 2 : ℕ) : ℝ) * Real.log 2) +
              ∑ m ∈ Finset.Icc 3 (n - 3),
                1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ))) := by
        linarith [hkey, htwo, hend1, hend2, hsum_ge]
      rw [logConvolution1622_lc111, hdecomp, Finset.sum_insert hmem1, Finset.sum_insert hmem2]
      rw [show n - (n - 2) = 2 from by omega]
      exact hgoal

/-- PORT of logConv_small_range1622 from SPLIT_log_convolution_estimate1622, same proof, renamed so that Major81Split111 can use it.
 LEAF. The finite range: for 2 <= n <= 10^3 the whole claim of the target holds
with one constant, in absolute value and with the relative weight 1/sqrt(log n).
Finitely many cases and no asymptotic content. -/
theorem logConv_small_range1622_lc111 :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n → n ≤ 1000 →
      |logConvolution1622_lc111 n - (n : ℝ) / Real.log n ^ 2| ≤
        B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  refine ⟨1000, by norm_num, ?_⟩
  intro n hn2 hn1000
  have h2pos : 0 < Real.log 2 := log_two_pos1622_lc111
  have hlogmax : Real.log (n : ℝ) ≤ 7 := by
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn1000R : (n : ℝ) ≤ Real.exp 7 := by
      have h : (n : ℝ) ≤ 1000 := by exact_mod_cast hn1000
      linarith [exp_seven_ge1622_lc111]
    calc Real.log (n : ℝ) ≤ Real.log (Real.exp 7) := Real.log_le_log hnR hn1000R
      _ = 7 := Real.log_exp 7
  have hsqrtle : Real.sqrt (Real.log (n : ℝ)) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 3)]
    linarith
  have hrecip : 1 / 3 ≤ 1 / Real.sqrt (Real.log (n : ℝ)) := by
    apply one_div_le_one_div_of_le (by
      have hpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      positivity) hsqrtle
  rcases Nat.lt_or_ge n 4 with hsmall | hbig
  · -- n = 2 or n = 3: the sum is empty
    interval_cases n
    · have hS : logConvolution1622_lc111 2 = 0 := by
        rw [logConvolution1622_lc111, show (2 - 2 : ℕ) = 0 from rfl]
        exact Finset.sum_empty
      rw [hS, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
      have hl2 : 0 < Real.log (2 : ℝ) ^ 2 := by positivity
      have hstep : (2 : ℝ) / Real.log (2 : ℝ) ^ 2 ≤
          1000 * ((2 : ℝ) / Real.log (2 : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (2 : ℝ))) := by
        have h1 : (1 : ℝ) ≤ 1000 * (1 / Real.sqrt (Real.log (2 : ℝ))) := by
          have := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 1000)
          linarith
        calc (2 : ℝ) / Real.log (2 : ℝ) ^ 2
            = 1 * ((2 : ℝ) / Real.log (2 : ℝ) ^ 2) := by ring
          _ ≤ (1000 * (1 / Real.sqrt (Real.log (2 : ℝ)))) *
                ((2 : ℝ) / Real.log (2 : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 / Real.log (2 : ℝ) ^ 2)
          _ = 1000 * ((2 : ℝ) / Real.log (2 : ℝ) ^ 2) *
                (1 / Real.sqrt (Real.log (2 : ℝ))) := by ring
      exact hstep
    · have hS : logConvolution1622_lc111 3 = 0 := by
        rw [logConvolution1622_lc111, show (3 - 2 : ℕ) = 1 from rfl]
        exact Finset.sum_empty
      rw [hS, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
      have hl3 : 0 < Real.log (3 : ℝ) ^ 2 := by
        have : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
        positivity
      have hstep : (3 : ℝ) / Real.log (3 : ℝ) ^ 2 ≤
          1000 * ((3 : ℝ) / Real.log (3 : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (3 : ℝ))) := by
        have h1 : (1 : ℝ) ≤ 1000 * (1 / Real.sqrt (Real.log (3 : ℝ))) := by
          have := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 1000)
          linarith
        calc (3 : ℝ) / Real.log (3 : ℝ) ^ 2
            = 1 * ((3 : ℝ) / Real.log (3 : ℝ) ^ 2) := by ring
          _ ≤ (1000 * (1 / Real.sqrt (Real.log (3 : ℝ)))) *
                ((3 : ℝ) / Real.log (3 : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 3 / Real.log (3 : ℝ) ^ 2)
          _ = 1000 * ((3 : ℝ) / Real.log (3 : ℝ) ^ 2) *
                (1 / Real.sqrt (Real.log (3 : ℝ))) := by ring
      exact hstep
  · -- 4 ≤ n: floor from the main-term leaf, ceiling from the size of one term
    have hn4 : 4 ≤ n := hbig
    have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hLpos : 0 < Real.log (n : ℝ) := Real.log_pos hnR
    have hlow : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ logConvolution1622_lc111 n :=
      logConv_main_le1622_lc111 n hn4
    have hbound : logConvolution1622_lc111 n ≤ (n : ℝ) * (1 / (Real.log 2) ^ 2) := by
      rw [logConvolution1622_lc111]
      have hterm : ∀ m ∈ Finset.Icc 2 (n - 2),
          1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) ≤ 1 / (Real.log 2) ^ 2 := by
        intro m hm
        rw [Finset.mem_Icc] at hm
        obtain ⟨hm2, hmn⟩ := hm
        have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
        have hnm1 : (1 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n - m)
        have hmpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
        have hnmpos : 0 < Real.log ((n - m : ℕ) : ℝ) := Real.log_pos hnm1
        have h2le : Real.log 2 ≤ Real.log (m : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ m))
        have h2le' : Real.log 2 ≤ Real.log ((n - m : ℕ) : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n - m))
        have hprod : Real.log 2 * Real.log 2 ≤ Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) :=
          mul_le_mul h2le h2le' h2pos.le hmpos.le
        have hpos : 0 < Real.log 2 * Real.log 2 := mul_pos h2pos h2pos
        have h := one_div_le_one_div_of_le hpos hprod
        simpa [pow_two] using h
      have hsum := Finset.sum_le_sum hterm
      have hcard : (Finset.Icc 2 (n - 2)).card = n - 3 := by
        rw [Nat.card_Icc]
        omega
      rw [Finset.sum_const, hcard, nsmul_eq_mul] at hsum
      have hcast : ((n - 3 : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : (n - 3 : ℕ) ≤ n := by omega
        exact_mod_cast this
      have hpos : (0 : ℝ) < 1 / (Real.log 2) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_right hcast hpos.le
      linarith [hsum, this]
    have habs : |logConvolution1622_lc111 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
        = logConvolution1622_lc111 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 := abs_of_nonneg (by linarith)
    rw [habs]
    have hLs : 0 < Real.log (n : ℝ) ^ 2 := by positivity
    have hsL : (0 : ℝ) < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hLpos
    have hkey : Real.log (n : ℝ) ^ 2 * Real.sqrt (Real.log (n : ℝ)) ≤
        1000 * (Real.log 2) ^ 2 := by
      have h1 : Real.log (n : ℝ) ^ 2 ≤ 49 := by nlinarith [hlogmax, hLpos]
      have h2 : Real.sqrt (Real.log (n : ℝ)) ≤ 3 := hsqrtle
      nlinarith [h1, h2, hsL, hLs, Real.log_two_gt_d9]
    have hconst : (1 / (Real.log 2) ^ 2) ≤
        1000 * (1 / Real.log (n : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (n : ℝ))) := by
      have hden : (0 : ℝ) < Real.log (n : ℝ) ^ 2 * Real.sqrt (Real.log (n : ℝ)) := by positivity
      rw [div_le_iff₀ (by positivity)]
      have e : 1000 * (1 / Real.log (n : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (n : ℝ))) *
          (Real.log 2) ^ 2 =
          1000 * (Real.log 2) ^ 2 / (Real.log (n : ℝ) ^ 2 * Real.sqrt (Real.log (n : ℝ))) := by
        field_simp
        try ring
      rw [e, le_div_iff₀ hden]
      linarith [hkey]
    have hposn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hratio : (0 : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 := by positivity
    have : logConvolution1622_lc111 n - (n : ℝ) / Real.log (n : ℝ) ^ 2
        ≤ (n : ℝ) * (1 / (Real.log 2) ^ 2) := by linarith
    have htarget : (n : ℝ) * (1 / (Real.log 2) ^ 2) ≤
        1000 * ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (n : ℝ))) := by
      have := mul_le_mul_of_nonneg_left hconst hposn
      calc (n : ℝ) * (1 / (Real.log 2) ^ 2)
          ≤ (n : ℝ) * (1000 * (1 / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ)))) := this
        _ = 1000 * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := by
            field_simp
            try ring
    linarith

/-- PORT of logConv_log_cube_split1622 from SPLIT_log_convolution_estimate1622, same proof, renamed so that Major81Split111 can use it.
 LEAF. The power identity that turns the excess into the relative weight:
n / (log n)^3 is n / (log n)^2 times 1 / log n, for every n at least 2, where the
logarithm does not vanish. -/
theorem logConv_log_cube_split1622_lc111 (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) / Real.log n ^ 3 = ((n : ℝ) / Real.log n ^ 2) * (1 / Real.log n) := by
  have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hL : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos h1)
  field_simp
  try ring

/-- PORT of logConv_recip_log_le_sqrt1622 from SPLIT_log_convolution_estimate1622, same proof, renamed so that Major81Split111 can use it.
 LEAF. The logarithmic weight comparison: for n at least 10^3 the logarithm is at
least one, so 1 / log n is at most 1 / sqrt(log n). This is what converts the
second order excess into the exact weight of the target. -/
theorem logConv_recip_log_le_sqrt1622_lc111 (n : ℕ) (hn : 1000 ≤ n) :
    1 / Real.log n ≤ 1 / Real.sqrt (Real.log n) := by
  have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos h1
  have hexp : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have he : Real.exp 1 < (n : ℝ) := by
      have h2 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith [Real.exp_one_lt_d9]
    have h := Real.log_le_log (Real.exp_pos 1) he.le
    simpa [Real.log_exp] using h
  have hsqrtpos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hL
  have hle : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
    rw [Real.sqrt_le_left hL.le]
    nlinarith
  exact one_div_le_one_div_of_le hsqrtpos hle

end PortSPLIT_log_convolution_estimate1622


section PortSPLIT_logConv_excess1622


/-- PORT of logConv_shift_nonneg1622 from SPLIT_logConv_excess1622, same proof, renamed so that Major81Split111 can use it.
 LEAF. Positivity of the shift: for every index of the convolution the logarithm
of m (n - m) is at most twice the logarithm of n, that is the shift 2 log n minus
log m minus log (n - m) is nonnegative. This is the step that lets the shift be
weight summed over the range without a sign condition. -/
theorem logConv_shift_nonneg1622_lc111 (n m : ℕ) (hm : m ∈ Finset.Icc 2 (n - 2)) :
    0 ≤ 2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)) := by
  have hm1 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
  have hm2 : m ≤ n - 2 := (Finset.mem_Icc.mp hm).2
  have hm_lt_n : m < n := by omega
  have h_pos_m : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h_pos_nm : (0 : ℝ) < (n - m : ℕ) := by exact_mod_cast (show 0 < n - m by omega)
  have h_pos_n : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [sub_nonneg]
  have h_log_add : Real.log m + Real.log (n - m : ℕ) = Real.log (m * (n - m : ℕ)) := by
    exact (Real.log_mul (ne_of_gt h_pos_m) (ne_of_gt h_pos_nm)).symm
  rw [h_log_add]
  have h_log_pow : 2 * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ 2) := by
    have h1 : 2 * Real.log (n : ℝ) = Real.log (n : ℝ) + Real.log (n : ℝ) := by ring
    rw [h1]
    have h2 : (n : ℝ) ^ 2 = (n : ℝ) * (n : ℝ) := by ring
    rw [h2]
    exact (Real.log_mul (ne_of_gt h_pos_n) (ne_of_gt h_pos_n)).symm
  rw [h_log_pow]
  apply Real.log_le_log
  · positivity
  · have : (m : ℝ) * (n - m : ℕ) = (m * (n - m) : ℕ) := by push_cast; rfl
    rw [this]
    push_cast
    have h_ineq : m * (n - m) ≤ n ^ 2 := by
      calc m * (n - m) ≤ n * n := by
            have h1 : m ≤ n := by omega
            have h2 : n - m ≤ n := by omega
            exact Nat.mul_le_mul h1 h2
        _ = n ^ 2 := by ring
    exact_mod_cast h_ineq

/-- PORT of logConv_shift_sum1622 from SPLIT_logConv_excess1622, same proof, renamed so that Major81Split111 can use it.
 LEAF. Total of the shift: summed over the whole range 2 <= m <= n - 2 the shift
2 log n - log m - log (n - m) is at most a constant times n. The shift is the
logarithm of n^2 / (m (n - m)), and the sum of the logarithms is read off a lower
bound for the logarithm of the factorial (n - 2)!, so the constant is absolute. -/
theorem logConv_shift_sum1622_lc111 :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1000 ≤ n →
      (∑ m ∈ Finset.Icc 2 (n - 2),
          (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))))
        ≤ K * (n : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro n hn
  have hsym : (∑ m ∈ Finset.Icc 2 (n - 2), Real.log (n - m : ℕ)) =
      ∑ m ∈ Finset.Icc 2 (n - 2), Real.log m := by
    refine Finset.sum_bij (fun m _ => n - m) ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro b hb
      refine ⟨n - b, ?_, ?_⟩
      · simp only [Finset.mem_Icc] at hb ⊢
        omega
      · simp only [Finset.mem_Icc] at hb
        omega
    · intro m hm
      rfl
  have hset : Finset.Ioc 0 n =
      insert 1 (insert (n - 1) (insert n (Finset.Icc 2 (n - 2)))) := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h1 : (1 : ℕ) ∉ insert (n - 1) (insert n (Finset.Icc 2 (n - 2))) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have h2 : n - 1 ∉ insert n (Finset.Icc 2 (n - 2)) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have h3 : n ∉ Finset.Icc 2 (n - 2) := by
    simp only [Finset.mem_Icc]; omega
  have hfull := Real.le_sum_log_nat n
  rw [hset, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3] at hfull
  simp only [Nat.cast_one, Real.log_one, zero_add] at hfull
  have hlog : Real.log (n - 1 : ℕ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < n - 1 by omega)) (by exact_mod_cast Nat.sub_le n 1)
  have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hcard : ((Finset.Icc 2 (n - 2)).card : ℝ) = (n : ℝ) - 3 := by
    rw [Nat.card_Icc]
    have h : n - 2 + 1 - 2 = n - 3 := by omega
    rw [h, Nat.cast_sub (by omega)]
    norm_num
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, hsym, hcard]
  nlinarith

/-- PORT of logConv_middle_shift1622 from SPLIT_logConv_excess1622, same proof, renamed so that Major81Split111 can use it.
 LEAF. Small shift in the middle of the range: for n at least 10^3 and for an
index m with 2 sqrt n <= m <= n - 2 sqrt n the product m (n - m) is at least
n^(3/2), so the shift 2 log n - log m - log (n - m) is at most half of log n. This
is the step that makes the termwise majorant applicable away from the two ends. -/
theorem logConv_middle_shift1622_lc111 (n m : ℕ) (hn : 1000 ≤ n)
    (hm1 : 2 * Nat.sqrt n ≤ m) (hm2 : m ≤ n - 2 * Nat.sqrt n) :
    2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)) ≤ Real.log (n : ℝ) / 2 := by
  have hs : 31 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hs2 := Nat.sqrt_le n
  have hns := Nat.sqrt_le_add n
  have hmn : m ≤ n := by omega
  have hmpos : 0 < m := by omega
  have hnmp : 0 < n - m := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hsp : (0 : ℝ) < (Nat.sqrt n + 1 : ℕ) := by positivity
  have hproduct : (n : ℝ) * (Nat.sqrt n + 1 : ℕ) ≤
      (m : ℝ) * (n - m : ℕ) := by
    have ha : (2 * Nat.sqrt n : ℕ) ≤ n - m := by omega
    have hb : (0 : ℝ) ≤ ((m : ℝ) - 2 * (Nat.sqrt n : ℝ)) *
        ((n - m : ℕ) - 2 * (Nat.sqrt n : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hm1))
        (sub_nonneg.mpr (by exact_mod_cast ha))
    have hc : (n - m : ℕ) + (m : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hmn
    have hd : (Nat.sqrt n : ℝ) ^ 2 ≤ (n : ℝ) := by simpa only [pow_two] using (show (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) by exact_mod_cast hs2)
    have he : (31 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hs
    have hf := mul_nonneg (show (0 : ℝ) ≤ (Nat.sqrt n : ℝ) - 5 by linarith)
      (show (0 : ℝ) ≤ (Nat.sqrt n : ℝ) ^ 2 by positivity)
    have hg := mul_nonneg (show (0 : ℝ) ≤ (Nat.sqrt n : ℝ) - 1 by linarith)
      (show (0 : ℝ) ≤ (n : ℝ) - (Nat.sqrt n : ℝ) ^ 2 by linarith)
    push_cast
    nlinarith
  have hns' : (n : ℝ) ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast (show n ≤ (Nat.sqrt n + 1) ^ 2 by nlinarith)
  have hlogn := Real.log_le_log hnpos hns'
  rw [Real.log_pow] at hlogn
  norm_num only [Nat.cast_ofNat] at hlogn
  have hlogprod := Real.log_le_log (mul_pos hnpos hsp) hproduct
  rw [Real.log_mul (ne_of_gt hnpos) (ne_of_gt hsp),
    Real.log_mul (by positivity) (by positivity)] at hlogprod
  linarith

/-- PORT of logConv_end_mass1622 from SPLIT_logConv_excess1622, same proof, renamed so that Major81Split111 can use it.
 LEAF. Mass of the two ends: summed over the indices m of the range which fail
2 sqrt n <= m <= n - 2 sqrt n, that is over the two ends of the range, the summand
1 / (log m log (n - m)) is at most a constant times n / (log n)^3. Each such index
has both logarithms at least half of log n, and there are at most 4 sqrt n of them. -/
theorem logConv_end_mass1622_lc111 :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1000 ≤ n →
      (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
          (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)),
          1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
  classical
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨128 / Real.log 2, by positivity, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hpoint : ∀ m ∈ Finset.Icc 2 (n - 2),
      1 / (Real.log m * Real.log (n - m : ℕ)) ≤
        2 / (Real.log 2 * Real.log (n : ℝ)) := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hnm : 2 ≤ n - m := by omega
    have hu : Real.log 2 ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hm1)
    have hv : Real.log 2 ≤ Real.log (n - m : ℕ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hnm)
    have hsum : Real.log (n : ℝ) ≤ 2 * max (Real.log m) (Real.log (n - m : ℕ)) := by
      rcases le_total m (n - m) with h | h
      · have hc : (n : ℝ) ≤ 2 * (n - m : ℕ) := by
          exact_mod_cast (show n ≤ 2 * (n - m) by omega)
        have ht := Real.log_le_log hnpos hc
        rw [Real.log_mul (by norm_num) (by positivity)] at ht
        have hh : Real.log m ≤ Real.log (n - m : ℕ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast h)
        rw [max_eq_right hh]
        linarith
      · have hc : (n : ℝ) ≤ 2 * (m : ℝ) := by
          exact_mod_cast (show n ≤ 2 * m by omega)
        have ht := Real.log_le_log hnpos hc
        rw [Real.log_mul (by norm_num) (by positivity)] at ht
        have hh : Real.log (n - m : ℕ) ≤ Real.log m :=
          Real.log_le_log (by positivity) (by exact_mod_cast h)
        rw [max_eq_left hh]
        linarith
    have hprod : Real.log 2 * Real.log (n : ℝ) ≤
        2 * (Real.log m * Real.log (n - m : ℕ)) := by
      rcases le_total (Real.log m) (Real.log (n - m : ℕ)) with h | h
      · rw [max_eq_right h] at hsum
        nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ Real.log (n - m : ℕ) by linarith)]
      · rw [max_eq_left h] at hsum
        nlinarith [mul_nonneg (sub_nonneg.mpr hv) (show 0 ≤ Real.log (m : ℝ) by linarith)]
    have hp : 0 < Real.log m * Real.log (n - m : ℕ) :=
      mul_pos (lt_of_lt_of_le htwo hu) (lt_of_lt_of_le htwo hv)
    apply (div_le_div_iff₀ hp (mul_pos htwo hL)).mpr
    simpa only [one_mul] using hprod
  have hcard : (((Finset.Icc 2 (n - 2)).filter
      (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n))).card : ℝ)
        ≤ 4 * (Nat.sqrt n : ℝ) := by
    have hsub : (Finset.Icc 2 (n - 2)).filter
        (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)) ⊆
        Finset.range (2 * Nat.sqrt n) ∪
          (Finset.range (2 * Nat.sqrt n)).image (fun k => n - k) := by
      intro m hm
      obtain ⟨hmem, hnot⟩ := Finset.mem_filter.mp hm
      have hm' := Finset.mem_Icc.mp hmem
      by_cases h : m < 2 * Nat.sqrt n
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨n - m, Finset.mem_range.mpr (by omega), by omega⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hi := Finset.card_image_le (s := Finset.range (2 * Nat.sqrt n)) (f := fun k => n - k)
    simp only [Finset.card_range] at hc hi
    exact_mod_cast (show ((Finset.Icc 2 (n - 2)).filter
      (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n))).card ≤
        4 * Nat.sqrt n by omega)
  have hlog2 : Real.log (n : ℝ) ^ 2 ≤ 16 * Real.sqrt (n : ℝ) := by
    have hy : 0 < Real.sqrt (Real.sqrt (n : ℝ)) := by positivity
    have ht := Real.log_le_self hy.le
    rw [Real.log_sqrt (by positivity), Real.log_sqrt (by positivity)] at ht
    have hs := Real.sq_sqrt (Real.sqrt_nonneg (n : ℝ))
    have hh : 0 ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) - Real.log (n : ℝ) := by linarith
    nlinarith [mul_nonneg hh (show 0 ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) + Real.log (n : ℝ) by positivity)]
  have hsle : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    simpa only [pow_two] using (show (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.sqrt_le n)
  have hmass : (Nat.sqrt n : ℝ) * Real.log (n : ℝ) ^ 2 ≤ 16 * (n : ℝ) := by
    calc
      _ ≤ Real.sqrt (n : ℝ) * (16 * Real.sqrt (n : ℝ)) :=
        mul_le_mul hsle hlog2 (by positivity) (by positivity)
      _ = _ := by nlinarith [Real.sq_sqrt hnpos.le]
  calc
    _ ≤ ∑ m ∈ (Finset.Icc 2 (n - 2)).filter
        (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)),
          2 / (Real.log 2 * Real.log (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hpoint m (Finset.mem_filter.mp hm).1
    _ = (((Finset.Icc 2 (n - 2)).filter
        (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n))).card : ℝ) *
          (2 / (Real.log 2 * Real.log (n : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * (Nat.sqrt n : ℝ)) * (2 / (Real.log 2 * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (128 / Real.log 2) * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
      calc
        _ = (8 * (Nat.sqrt n : ℝ)) / (Real.log 2 * Real.log (n : ℝ)) := by ring
        _ ≤ (128 * (n : ℝ)) / (Real.log 2 * Real.log (n : ℝ) ^ 3) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith [mul_nonneg (show 0 ≤ 8 * Real.log 2 * Real.log (n : ℝ) by positivity)
            (show 0 ≤ 16 * (n : ℝ) - (Nat.sqrt n : ℝ) * Real.log (n : ℝ) ^ 2 by linarith)]
        _ = _ := by ring

/-- PORT of logConv_term_majorant_bounded474 from SPLIT_logConv_excess1622, same proof, renamed so that Major81Split111 can use it.
 The valid termwise estimate includes the upper bounds on both logarithms.
These hold for convolution indices on page 161 after equation 6.3. -/
theorem logConv_term_majorant_bounded474_lc111 (u v L : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hL : 0 < L) (huL : u ≤ L) (hvL : v ≤ L)
    (hshift : 2 * L - (u + v) ≤ L / 2) :
    1 / (u * v) ≤ 1 / L ^ 2 + (2 / L ^ 3) * (2 * L - (u + v)) := by
  have hprod : L ^ 2 - L * (2 * L - (u + v)) ≤ u * v := by
    nlinarith [mul_nonneg (sub_nonneg.mpr huL) (sub_nonneg.mpr hvL)]
  have hs : 0 ≤ 2 * L - (u + v) := by linarith
  have ht : 0 ≤ (2 * L - (u + v)) * (L - 2 * (2 * L - (u + v))) :=
    mul_nonneg hs (by linarith)
  have hmult := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ L + 2 * (2 * L - (u + v)) by positivity)
  have hn : L ^ 3 ≤ (L + 2 * (2 * L - (u + v))) * (u * v) := by
    nlinarith [mul_nonneg hL.le ht]
  calc
    _ ≤ (L + 2 * (2 * L - (u + v))) / L ^ 3 := by
      apply (div_le_div_iff₀ (mul_pos hu hv) (pow_pos hL 3)).mpr
      simpa only [one_mul] using hn
    _ = _ := by field_simp [ne_of_gt hL]

/-- PORT of logConv_excess_corrected474 from SPLIT_logConv_excess1622, same proof, renamed so that Major81Split111 can use it.
 The convolution excess estimate from the bounded majorant. This proof
uses the two logarithm upper bounds and avoids the false sealed annotation. -/
theorem logConv_excess_corrected474_lc111 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1000 ≤ n →
      logConvolution1622_lc111 n - (n : ℝ) / Real.log n ^ 2 ≤ C * ((n : ℝ) / Real.log n ^ 3) := by
  classical
  obtain ⟨K, hKpos, hK⟩ := logConv_shift_sum1622_lc111
  obtain ⟨Ke, hKepos, hKe⟩ := logConv_end_mass1622_lc111
  refine ⟨2 * K + Ke, by linarith, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hLne : Real.log (n : ℝ) ≠ 0 := ne_of_gt hL
  have hT : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 (n - 2))
    (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)
    (fun m => 1 / (Real.log m * Real.log (n - m : ℕ)))
  -- the middle range
  have hmid :
      (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
          1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 + 2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
    have hpoint : ∀ m ∈ (Finset.Icc 2 (n - 2)).filter
        (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
        1 / (Real.log m * Real.log (n - m : ℕ))
          ≤ 1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))) := by
      intro m hmf
      obtain ⟨hmem, hm1, hm2⟩ := Finset.mem_filter.mp hmf
      have hu : 0 < Real.log (m : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < m by omega))
      have hv : 0 < Real.log ((n - m : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n - m by omega))
      have hsum : Real.log m + Real.log (n - m : ℕ) ≤ 2 * Real.log (n : ℝ) := by
        linarith [logConv_shift_nonneg1622_lc111 n m hmem]
      have hshift := logConv_middle_shift1622_lc111 n m hn hm1 hm2
      exact logConv_term_majorant_bounded474_lc111 (Real.log m) (Real.log (n - m : ℕ)) (Real.log (n : ℝ))
        hu hv hL
        (Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
          (by exact_mod_cast (show m ≤ n by omega)))
        (Real.log_le_log (by exact_mod_cast (show 0 < n - m by omega))
          (by exact_mod_cast Nat.sub_le n m))
        (by linarith)
    have hcard : (((Finset.Icc 2 (n - 2)).filter
        (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) ≤ (n : ℝ) := by
      have h1 : ((Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card ≤ n := by
        have h2 := Finset.card_le_card (Finset.filter_subset
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n) (Finset.Icc 2 (n - 2)))
        have h3 : (Finset.Icc 2 (n - 2)).card = n - 2 + 1 - 2 := Nat.card_Icc 2 (n - 2)
        omega
      exact_mod_cast h1
    have hsums :
        (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))))
          ≤ K * (n : ℝ) := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans (hK n hn)
      intro x hx _
      exact logConv_shift_nonneg1622_lc111 n x hx
    have hE :
        (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))))
          = (((Finset.Icc 2 (n - 2)).filter
              (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) *
                (1 / Real.log (n : ℝ) ^ 2) +
              (2 / Real.log (n : ℝ) ^ 3) *
                (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
                  (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
                  (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hcast : (0 : ℝ) ≤ 1 / Real.log (n : ℝ) ^ 2 := by positivity
    have hfac : (0 : ℝ) ≤ 2 / Real.log (n : ℝ) ^ 3 := by positivity
    have hle1 : (((Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) *
            (1 / Real.log (n : ℝ) ^ 2) ≤ (n : ℝ) * (1 / Real.log (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard hcast
    have hle2 : (2 / Real.log (n : ℝ) ^ 3) *
          (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))))
        ≤ (2 / Real.log (n : ℝ) ^ 3) * (K * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsums hfac
    calc (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ ∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))) :=
          Finset.sum_le_sum hpoint
      _ = _ := hE
      _ ≤ (n : ℝ) * (1 / Real.log (n : ℝ) ^ 2) +
            (2 / Real.log (n : ℝ) ^ 3) * (K * (n : ℝ)) := add_le_add hle1 hle2
      _ = (n : ℝ) / Real.log (n : ℝ) ^ 2 +
            2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
          field_simp
  -- the two ends
  have hends :
      (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
          (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)),
          1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ Ke * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hKe n hn
  have hcomb : (n : ℝ) / Real.log (n : ℝ) ^ 2 +
        2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) +
          Ke * ((n : ℝ) / Real.log (n : ℝ) ^ 3)
      = (n : ℝ) / Real.log (n : ℝ) ^ 2 +
          (2 * K + Ke) * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by ring
  have hunfold : logConvolution1622_lc111 n =
      ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log m * Real.log (n - m : ℕ)) := rfl
  rw [hunfold]
  linarith [hsplit, hmid, hends, hcomb]

end PortSPLIT_logConv_excess1622


section PortDecomp487c
open MeasureTheory Filter Asymptotics Finset

/-- PORT of log_convolution_estimate487 from Decomp487c, same proof, renamed so that Major81Split111 can use it.
 P0093 page 161 after equation 6.3. Exact relative convolution estimate from the corrected bounded majorant. No use of the refuted unbounded majorant. -/
theorem log_convolution_estimate487_lc111 :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n → |logConvolution1622_lc111 n - (n : ℝ) / Real.log n ^ 2| ≤ B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  obtain ⟨C, hCpos, hC⟩ := logConv_excess_corrected474_lc111
  obtain ⟨B1, hB1pos, hB1⟩ := logConv_small_range1622_lc111
  refine ⟨max B1 C, lt_of_lt_of_le hB1pos (le_max_left B1 C), ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hsqrtpos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlogpos
  have hA : 0 ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 :=
    div_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
  have hS : 0 ≤ 1 / Real.sqrt (Real.log (n : ℝ)) :=
    div_nonneg zero_le_one hsqrtpos.le
  have hX : 0 ≤ ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (n : ℝ))) :=
    mul_nonneg hA hS
  rcases le_total n 1000 with hsmall | hlarge
  · have h := hB1 n hn hsmall
    calc
      |logConvolution1622_lc111 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
          ≤ B1 * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := h
      _ ≤ max B1 C * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ hS
            exact mul_le_mul_of_nonneg_right (le_max_left B1 C) hA
  · have h1000 : 1000 ≤ n := hlarge
    have h4 : 4 ≤ n := by omega
    have hmain : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ logConvolution1622_lc111 n :=
      logConv_main_le1622_lc111 n h4
    have hexc : logConvolution1622_lc111 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤
        C * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hC n h1000
    have habs : |logConvolution1622_lc111 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
        = logConvolution1622_lc111 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 :=
      abs_of_nonneg (by linarith)
    have hid : (n : ℝ) / Real.log (n : ℝ) ^ 3 =
        ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.log (n : ℝ)) :=
      logConv_log_cube_split1622_lc111 n hn
    have hrec : 1 / Real.log (n : ℝ) ≤ 1 / Real.sqrt (Real.log (n : ℝ)) :=
      logConv_recip_log_le_sqrt1622_lc111 n h1000
    calc
      |logConvolution1622_lc111 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
          = logConvolution1622_lc111 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 := habs
      _ ≤ C * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hexc
      _ = C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.log (n : ℝ))) := by
            rw [hid]
      _ ≤ C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hCpos.le
            exact mul_le_mul_of_nonneg_left hrec hA
      _ ≤ max B1 C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ)))) := by
            refine mul_le_mul_of_nonneg_right ?_ hX
            exact le_max_right B1 C
      _ = max B1 C * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := by ring

end PortDecomp487c


end LeanLab.Linnik1951
