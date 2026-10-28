module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T1803Z-10253, unit U-0963.
P0021 M. Bordignon, V. Starichkova, An explicit version of Chen's theorem assuming the
Generalized Riemann Hypothesis, arXiv 2211.08844 v1, read in full in Claude in Chrome
from arxiv.org/html/2211.08844 in this run.

The parameters of Section 5.4: u = 10^{4.27}, α = 10^{-2.61}, A = 4, ε = 1/8137,
C₁ = 112, C₂ = 114, X₂ = exp(exp 15.85).

PROVED, no cited input:
* `u_ge`, `u_le`: 18620.8 ≤ 10^{4.27} ≤ 18621.
* `alpha_ge`, `alpha_le`: 0.0024547 ≤ 10^{-2.61} ≤ 0.0024548.
* `log_u_ge`: 9.83 ≤ log 10^{4.27}.
* `eps_u_lt`: ε(10^{4.27}) < 1/8137, with ε(u) from (6). The value is 1/8137.24, so
  the paper's ε = 1/8137 is a valid upper bound, with a margin of about 4e-9.
* `table1_*`: Table 1 as printed; both C columns are non-increasing down the table, and
  6100 is the largest printed ε⁻¹ not above 8137, so C₁ = 112 and C₂ = 114 are the row
  ε⁻¹ = 6100. This settles the 2026-10-17 QUESTION: the paper takes the next row on the
  safe side, which is valid if C₁, C₂ are non-increasing in ε⁻¹ between rows, as every
  printed row is.
* `cond18`: for every L ≥ exp 15.85, 10^{4.27} ≤ 10^{-2.61} L − 5 log L, that is
  N^α / log^{A+1} N ≥ exp u for every N ≥ exp(exp 15.85), conditions (18), (21), (27).
Goldbach is open.
-/

@[expose] public section

open Real Finset

set_option exponentiation.threshold 2000

noncomputable section
namespace LeanLab.BS2022GRH

/-- ε(u) of Lemma 8, display (6). -/
def epsBS (u : ℝ) : ℝ :=
  (1 + 1 / (0.996 * u - 1)) * (1 + 1.5e-4 / log u + 2.25e-8 / (log u) ^ 2) *
    (1 + 1 / (u - 1) + 1 / (u - 1) ^ 2) - 1

/-- u = 10^{4.27}. -/
def u0 : ℝ := (10 : ℝ) ^ (4.27 : ℝ)
/-- α = 10^{-2.61}. -/
def α0 : ℝ := (10 : ℝ) ^ (-2.61 : ℝ)

lemma u0_pow : u0 ^ (100 : ℕ) = (10 : ℝ) ^ (427 : ℕ) := by
  unfold u0
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma α0_pow : α0 ^ (100 : ℕ) = ((10 : ℝ) ^ (261 : ℕ))⁻¹ := by
  unfold α0
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num [Real.rpow_neg]

lemma u0_pos : 0 < u0 := by unfold u0; positivity
lemma α0_pos : 0 < α0 := by unfold α0; positivity

theorem u_ge : (18620.8 : ℝ) ≤ u0 := by
  rw [← pow_le_pow_iff_left₀ (by norm_num) u0_pos.le (by norm_num : (100 : ℕ) ≠ 0), u0_pow]
  norm_num

theorem u_le : u0 ≤ 18621 := by
  rw [← pow_le_pow_iff_left₀ u0_pos.le (by norm_num) (by norm_num : (100 : ℕ) ≠ 0), u0_pow]
  norm_num

theorem alpha_ge : (0.0024547 : ℝ) ≤ α0 := by
  rw [← pow_le_pow_iff_left₀ (by norm_num) α0_pos.le (by norm_num : (100 : ℕ) ≠ 0), α0_pow]
  norm_num

theorem alpha_le : α0 ≤ 0.0024548 := by
  rw [← pow_le_pow_iff_left₀ α0_pos.le (by norm_num) (by norm_num : (100 : ℕ) ≠ 0), α0_pow]
  norm_num

lemma exp083_le : exp (0.83 : ℝ) ≤ 2.293319 := by
  have h := Real.exp_bound' (x := (0.83 : ℝ)) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h; linarith

lemma exp_nat_le (n : ℕ) : exp (n : ℝ) ≤ 2.7182818286 ^ n := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_d9.le n

lemma exp_nat_ge (n : ℕ) : (2.7182818283 : ℝ) ^ n ≤ exp (n : ℝ) := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n

lemma exp983_lt : exp (9.83 : ℝ) < 18620.8 := by
  have e : (9.83 : ℝ) = ((9 : ℕ) : ℝ) + 0.83 := by norm_num
  rw [e, exp_add]
  have h1 := exp_nat_le 9
  have h2 := exp083_le
  calc exp ((9 : ℕ) : ℝ) * exp 0.83 ≤ 2.7182818286 ^ 9 * 2.293319 := by
        gcongr
    _ < 18620.8 := by norm_num

theorem log_u_ge : (9.83 : ℝ) ≤ log u0 := by
  rw [Real.le_log_iff_exp_le u0_pos]
  linarith [exp983_lt, u_ge]

/-- **ε(10^{4.27}) < 1/8137.** -/
theorem eps_u_lt : epsBS u0 < 1 / 8137 := by
  have hu := u_ge
  have hL := log_u_ge
  have hLpos : 0 < log u0 := by linarith
  have f1 : 1 + 1 / (0.996 * u0 - 1) ≤ 1 + 1 / (0.996 * 18620.8 - 1) := by
    gcongr
  have f2 : 1 + 1.5e-4 / log u0 + 2.25e-8 / (log u0) ^ 2 ≤
      1 + 1.5e-4 / 9.83 + 2.25e-8 / (9.83 : ℝ) ^ 2 := by
    gcongr
  have f3 : 1 + 1 / (u0 - 1) + 1 / (u0 - 1) ^ 2 ≤
      1 + 1 / (18620.8 - 1) + 1 / ((18620.8 : ℝ) - 1) ^ 2 := by
    have : (18620.8 : ℝ) - 1 ≤ u0 - 1 := by linarith
    have hp : (0 : ℝ) < 18620.8 - 1 := by norm_num
    gcongr
  have p1 : 0 ≤ 1 + 1 / (0.996 * u0 - 1) := by
    have : 0 < 0.996 * u0 - 1 := by linarith
    positivity
  have p2 : 0 ≤ 1 + 1.5e-4 / log u0 + 2.25e-8 / (log u0) ^ 2 := by positivity
  have p3 : 0 ≤ 1 + 1 / (u0 - 1) + 1 / (u0 - 1) ^ 2 := by
    have : 0 < u0 - 1 := by linarith
    positivity
  unfold epsBS
  have := mul_le_mul (mul_le_mul f1 f2 p2 (by norm_num)) f3 p3 (by norm_num)
  have hfin : (1 + 1 / (0.996 * 18620.8 - 1)) * (1 + 1.5e-4 / 9.83 + 2.25e-8 / (9.83 : ℝ) ^ 2) *
      (1 + 1 / (18620.8 - 1) + 1 / ((18620.8 : ℝ) - 1) ^ 2) - 1 < 1 / 8137 := by norm_num
  linarith

/-- Table 1 of the paper, rows (ε⁻¹, C₁(ε), C₂(ε)), as printed. -/
def table1 : List (ℕ × ℕ × ℕ) :=
  [(63, 32881, 32875), (64, 7582, 7580), (65, 3890, 3890), (66, 2542, 2542), (67, 1880, 1881),
   (68, 1480, 1500), (69, 1254, 1255), (70, 1084, 1086), (71, 960, 962), (72, 865, 867),
   (73, 790, 791), (74, 729, 730), (75, 678, 679), (76, 635, 636), (77, 598, 600),
   (78, 566, 568), (79, 538, 540), (80, 514, 515), (81, 492, 493), (84, 438, 439),
   (87, 398, 400), (93, 341, 343), (99, 303, 305), (114, 247, 249), (143, 198, 200),
   (200, 162, 164), (249, 149, 150), (300, 141, 142), (400, 132, 134), (500, 127, 129),
   (600, 124, 126), (700, 122, 124), (800, 121, 122), (900, 120, 121), (1000, 119, 120),
   (1100, 118, 120), (1200, 117, 119), (1400, 117, 118), (1500, 116, 118), (1600, 116, 117),
   (1800, 115, 117), (2100, 115, 116), (2300, 114, 116), (3300, 113, 115), (4500, 113, 114),
   (6100, 112, 114), (12200, 112, 113), (39500, 111, 113)]

theorem table1_length : table1.length = 48 := by decide

/-- ε⁻¹ strictly increases and both C columns are non-increasing down Table 1. -/
theorem table1_monotone :
    table1.Pairwise (fun r s => r.1 < s.1 ∧ s.2.1 ≤ r.2.1 ∧ s.2.2 ≤ r.2.2) := by decide

theorem table1_row6100 : ((6100 : ℕ), (112 : ℕ), (114 : ℕ)) ∈ table1 := by decide

/-- 6100 is the largest printed ε⁻¹ that is at most 8137. -/
theorem table1_row_choice : ∀ r ∈ table1, r.1 ≤ 8137 → r.1 ≤ 6100 := by decide

theorem eps_lt_63 : (1 / 8137 : ℝ) < 1 / 63 := by norm_num

lemma exp1585_ge : (7640000 : ℝ) ≤ exp 15.85 := by
  have h := exp_nat_ge 317
  have e : ((317 : ℕ) : ℝ) = ((20 : ℕ) : ℝ) * 15.85 := by norm_num
  rw [e, Real.exp_nat_mul] at h
  rw [← pow_le_pow_iff_left₀ (by norm_num) (exp_pos _).le (by norm_num : (20 : ℕ) ≠ 0)]
  refine le_trans ?_ h
  norm_num

/-- **Conditions (18), (21), (27)** at the paper's parameters: for every L = log N with
L ≥ exp 15.85, α L − (A + 1) log L ≥ u, so N^α / log^5 N ≥ exp u. -/
theorem cond18 (L : ℝ) (hL : exp 15.85 ≤ L) : u0 ≤ α0 * L - 5 * log L := by
  set L0 := exp (15.85 : ℝ) with hL0
  have h0 : (7640000 : ℝ) ≤ L0 := exp1585_ge
  have hL0pos : 0 < L0 := exp_pos _
  have hLpos : 0 < L := lt_of_lt_of_le hL0pos hL
  have hlog : log L ≤ 15.85 + (L / L0 - 1) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hLpos hL0pos)
    rw [Real.log_div hLpos.ne' hL0pos.ne', hL0, Real.log_exp] at h1
    change log L - 15.85 ≤ L / L0 - 1 at h1
    linarith
  have ha := alpha_ge
  have hu := u_le
  have hq : 5 * (L / L0) ≤ 5 / 7640000 * L := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have : L0⁻¹ ≤ (7640000 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h0
    nlinarith
  have hαL : (0.0024547 - 5 / 7640000) * 7640000 ≤ (α0 - 5 / 7640000) * L := by
    have : (7640000 : ℝ) ≤ L := le_trans h0 hL
    exact mul_le_mul (by linarith) this (by norm_num) (by linarith)
  have : (18621 : ℝ) ≤ (0.0024547 - 5 / 7640000) * 7640000 - 74.25 := by norm_num
  nlinarith

end LeanLab.BS2022GRH
