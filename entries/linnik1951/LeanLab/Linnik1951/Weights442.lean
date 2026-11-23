module

public import LeanLab.Linnik1951.Uniform442

/-!
P0093 page 168 equation 10.7. Uniform relative weight after logarithmic growth.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Filter

/-- P0093 page 168 equation 10.7, uniform residual weight comparison.
For every positive C and epsilon, the residual weight times C log N
to one quarter is at most epsilon N over log squared N, uniformly
for residuals from two through N once N is large. Split the residual
at square root N. There is no singular coefficient in this statement. -/
theorem relative_weight_small442 (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ n : ℕ, 2 ≤ n → n ≤ N →
      ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) *
        (C * (Real.log N) ^ (1 / 4 : ℝ)) ≤ ε * (N : ℝ) / Real.log N ^ 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A : ℝ := C / (Real.log 2 ^ 2 * Real.sqrt (Real.log 2))
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨Np, hp⟩ := power_saving_negligible357 A (1 / 2) hA
    (by norm_num) 3 ε hε
  have ht : Tendsto (fun N : ℕ => (Real.log N) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨Ng, hg⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (8 * C / ε))
  refine ⟨max 3 (max Np Ng), ?_⟩
  intro N hN n hn hnN
  have hNp : Np < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNg : Ng ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN.le
  have hN3 : (3 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNr : (0 : ℝ) < N := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnNr : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hnlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hnl : 0 < Real.log n := hl2.trans_le hnlog
  have hL1 : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3).le
  have hL : 0 < Real.log N := by linarith
  let Q : ℝ := (Real.log N) ^ (1 / 4 : ℝ)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hQs : Q * Q = Real.sqrt (Real.log N) := by
    dsimp [Q]
    rw [← Real.rpow_add hL, Real.sqrt_eq_rpow]
    norm_num
  have hQle : Q ≤ Real.log N := by
    dsimp [Q]
    calc _ ≤ (Real.log N) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = _ := Real.rpow_one _
  by_cases hnlarge : Real.sqrt (N : ℝ) ≤ (n : ℝ)
  · have hln : Real.log N / 2 ≤ Real.log n := by
      have hh := Real.log_le_log (Real.sqrt_pos.mpr hNr) hnlarge
      rwa [Real.log_sqrt hNr.le] at hh
    have hden : Real.log N ^ 2 ≤ 4 * Real.log n ^ 2 := by
      have hh := pow_le_pow_left₀ hL.le (show Real.log N ≤ 2 * Real.log n by linarith) 2
      nlinarith
    have hw : (n : ℝ) / Real.log n ^ 2 ≤ 4 * (N : ℝ) / Real.log N ^ 2 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hnl) (sq_pos_of_pos hL)]
      have hh := mul_le_mul_of_nonneg_left hden hNr.le
      have hh' := mul_le_mul_of_nonneg_right hnNr (sq_nonneg (Real.log N))
      nlinarith
    have hroots : Real.sqrt (Real.log N) ≤ 2 * Real.sqrt (Real.log n) := by
      have hNroot := Real.sq_sqrt hL.le
      have hnroot := Real.sq_sqrt hnl.le
      nlinarith [Real.sqrt_nonneg (Real.log N), Real.sqrt_nonneg (Real.log n)]
    have hr : 1 / Real.sqrt (Real.log n) ≤ 2 / Real.sqrt (Real.log N) := by
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hnl) (Real.sqrt_pos.mpr hL)]
      simpa using hroots
    have hm : 8 * C / Q ≤ ε := by
      apply (div_le_iff₀ hQ).mpr
      have hh := (div_le_iff₀ hε).mp (hg N hNg)
      change 8 * C ≤ Q * ε at hh
      nlinarith
    calc
      _ ≤ (4 * (N : ℝ) / Real.log N ^ 2) *
          (2 / Real.sqrt (Real.log N)) * (C * Q) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hw hr (by positivity) (by positivity)) (by positivity)
      _ = (8 * C / Q) * ((N : ℝ) / Real.log N ^ 2) := by
        rw [← hQs]
        field_simp [hQ.ne', hL.ne']
        <;> ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hm
          (show 0 ≤ (N : ℝ) / Real.log N ^ 2 by positivity)
        simpa only [mul_div_assoc] using hh
  · have hnsmall : (n : ℝ) ≤ Real.sqrt (N : ℝ) := (lt_of_not_ge hnlarge).le
    have hw : (n : ℝ) / Real.log n ^ 2 ≤ Real.sqrt N / Real.log 2 ^ 2 := by
      calc
        _ ≤ Real.sqrt N / Real.log n ^ 2 := div_le_div_of_nonneg_right hnsmall (sq_nonneg _)
        _ ≤ _ := div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
          (sq_pos_of_pos hl2) (pow_le_pow_left₀ hl2.le hnlog 2)
    have hr : 1 / Real.sqrt (Real.log n) ≤ 1 / Real.sqrt (Real.log 2) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr hl2) (Real.sqrt_le_sqrt hnlog)
    have hpow : A * Real.sqrt N * Real.log N ^ 3 ≤ ε * (N : ℝ) := by
      have hh := hp N hNp
      norm_num only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num] at hh
      simpa only [Real.sqrt_eq_rpow] using hh
    have hend : A * Real.sqrt N * Real.log N ≤ ε * (N : ℝ) / Real.log N ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
      calc
        _ = A * Real.sqrt N * Real.log N ^ 3 := by ring
        _ ≤ _ := hpow
    calc
      _ ≤ (Real.sqrt N / Real.log 2 ^ 2) * (1 / Real.sqrt (Real.log 2)) *
          (C * Real.log N) := by
        exact mul_le_mul (mul_le_mul hw hr (by positivity) (by positivity))
          (mul_le_mul_of_nonneg_left hQle hC.le) (by positivity) (by positivity)
      _ = A * Real.sqrt N * Real.log N := by dsimp [A]; ring
      _ ≤ _ := hend

/-- P0093 page 168 equation 10.7. The actual finite singular
coefficient satisfies the uniform relative weight comparison. The
pointwise coefficient growth and the weight comparison are proved. -/
theorem truncated_relative_weight442 (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
      ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) *
        |truncatedSingular357 N n| ≤ ε * (N : ℝ) / Real.log N ^ 2 := by
  obtain ⟨C, hC, Nc, hc⟩ := truncated_log_quarter442
  obtain ⟨Nw, hw⟩ := relative_weight_small442 C ε hC hε
  refine ⟨max Nc Nw, ?_⟩
  intro N hN n hn hnN hev
  have hNc : Nc < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNw : Nw < N := lt_of_le_of_lt (le_max_right _ _) hN
  calc
    _ ≤ ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) *
        (C * (Real.log N) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hc N hNc n hn hnN hev) (by positivity)
    _ ≤ _ := hw N hNw n hn hnN

end LeanLab.Linnik1951
