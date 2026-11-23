module

public import LeanLab.Linnik1951.Products442
public import LeanLab.Linnik1951.Decomp376a

/-!
P0093 page 168 equation 10.7. A sufficient pointwise logarithmic singular bound.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- P0093 page 168 equation 10.7, elementary cutoff calculation.
For x at least three, log of the natural ceiling of x is at most
five times x to one quarter. -/
theorem log_ceiling_bound442 (x : ℝ) (hx : 3 ≤ x) :
    Real.log (⌈x⌉₊ : ℝ) ≤ 5 * x ^ (1 / 4 : ℝ) := by
  have hx1 : 1 ≤ x := by linarith
  have hxp : 0 < x := by linarith
  have hc : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    have hh := Nat.ceil_lt_add_one hxp.le
    linarith
  have hcp : (0 : ℝ) < (⌈x⌉₊ : ℝ) := lt_of_lt_of_le hxp (Nat.le_ceil x)
  have hh := Real.log_le_log hcp hc
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxp.ne'] at hh
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlx := Real.log_le_rpow_div hxp.le (by norm_num : (0 : ℝ) < 1 / 4)
  have hp : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  norm_num only [div_eq_mul_inv, inv_div, one_mul, inv_one] at hlx
  nlinarith

/-- P0093 page 168 equations 10.6 and 10.7. One absolute positive
C bounds the singular product at every even residual from two
through N by C times log N to one quarter, once log N is at least
three. This follows by a Mertens split at the ceiling of log N. -/
theorem singular_log_quarter442 :
    ∃ C : ℝ, 0 < C ∧ ∀ N n : ℕ, 3 ≤ Real.log N → 2 ≤ n → n ≤ N → Even n →
      singularSeries111 n ≤ C * (Real.log N) ^ (1 / 4 : ℝ) := by
  let A : ℝ := 2 * LeanLab.ChenExplicit.twinC
  let B : ℝ := Real.exp 36 * Real.exp (2 / Real.log 2)
  have hA : 0 < A := by dsimp [A]; exact mul_pos (by norm_num) LeanLab.ChenExplicit.twinC_pos
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨5 * A * B, by positivity, ?_⟩
  intro N n hN hn hnN hev
  let Y : ℕ := ⌈Real.log N⌉₊
  have hY : 3 ≤ Y := by
    have hh := hN.trans (Nat.le_ceil (Real.log N))
    exact_mod_cast hh
  have hlog : Real.log n ≤ (Y : ℝ) :=
    (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast hnN)).trans (Nat.le_ceil _)
  have hp := odd_prime_product_log_cutoff442 n Y (by omega) hY hlog
  have hc := log_ceiling_bound442 (Real.log N) hN
  rw [singular_eq_heath_brown376 n hn hev, LeanLab.HeathBrown1985.singular, if_pos hev]
  change A * (∏ p ∈ n.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))) ≤ _
  have hh := mul_le_mul_of_nonneg_left hp hA.le
  have ht := mul_le_mul_of_nonneg_left hc (mul_nonneg hA.le hB.le)
  dsimp [B] at ht
  nlinarith

/-- P0093 page 168 equation 10.5. Any fixed positive multiple of
N to negative one hundredth is eventually at most one. -/
theorem tail_coefficient_le_one442 (D : ℝ) (hD : 0 < D) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → D * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 := by
  obtain ⟨N0, hp⟩ := power_saving_negligible357 D (1 / 100) hD
    (by norm_num) 0 1 (by norm_num)
  refine ⟨max 1 N0, ?_⟩
  intro N hN
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hh := hp N hN0
  simp only [pow_zero, mul_one, one_mul] at hh
  have he : (N : ℝ) ^ (1 - (1 / 100 : ℝ)) =
      (N : ℝ) ^ (-(1 / 100 : ℝ)) * (N : ℝ) := by
    calc
      _ = (N : ℝ) ^ (-(1 / 100 : ℝ) + 1) := by congr 1; ring
      _ = (N : ℝ) ^ (-(1 / 100 : ℝ)) * (N : ℝ) ^ (1 : ℝ) := Real.rpow_add hNp _ _
      _ = _ := by rw [Real.rpow_one]
  rw [he, ← mul_assoc] at hh
  have hc : D * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ (N : ℝ) / (N : ℝ) :=
    (le_div_iff₀ hNp).mpr hh
  simpa only [div_self hNp.ne'] using hc

/-- P0093 page 168 equation 10.7, a sufficient corrected coefficient
upper bound. For large N and every even residual from two through N,
the truncated singular coefficient has absolute value at most C
log N to one quarter for one positive absolute C. -/
theorem truncated_log_quarter442 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |truncatedSingular357 N n| ≤ C * (Real.log N) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC, hc⟩ := singular_log_quarter442
  obtain ⟨D, hD, Nt, ht⟩ := singular_tail_decomposed376
  obtain ⟨Nd, hd⟩ := tail_coefficient_le_one442 D hD
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 3)
  refine ⟨C + 1, by positivity, max 1 (max L (max Nt Nd)), ?_⟩
  intro N hN n hn hnN hev
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNt : Nt < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNd : Nd < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hl : 3 ≤ Real.log N := by
    have hLR : (L : ℝ) < N := by exact_mod_cast hLN
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 3) (hL.trans hLR).le
  have hsave := (ht N hNt n hn hnN hev).trans (hd N hNd)
  have hs := hc N n hl hn hnN hev
  have hS0 : 0 ≤ singularSeries111 n := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_singularSeries111 hev hn)
  have hp : 1 ≤ (Real.log N) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hh := abs_sub_abs_le_abs_sub (truncatedSingular357 N n) (singularSeries111 n)
  rw [abs_of_nonneg hS0] at hh
  nlinarith

end LeanLab.Linnik1951
