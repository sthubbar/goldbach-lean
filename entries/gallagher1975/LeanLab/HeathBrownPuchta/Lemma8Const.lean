module

public import Mathlib

/-!
# Heath-Brown and Puchta 2002, Lemma 8's constant `C₂ = Σ_d k(d)/ε(d)`, (35) and (41)

Lab proof, unit U-1277, PC run 20261020T2004Z-7678. AI wrote the Lean code. P0012, arXiv
math/0201299 v2, Section 5, read through WebFetch 2026-10-20.

Paper: `ε(d)` is the order of 2 mod odd `d`; `k` is multiplicative with `k(p) = 1/(p-2)` for odd
`p` and `k = 0` at 2 and on prime squares; `h(n) = Σ_{d ∣ n} k(d) = Π_{p ∣ n, p > 2} (p-1)/(p-2)`;
`κ(e) = Σ_{ε(d) = e} k(d) = Σ_{d ∣ e} μ(e/d) h(2^d - 1)`; (41):
`C₂ ≤ Σ_{m ≤ M} κ(m) (1/m - 1/M) + 2.744 (1 + log M)/M` for `M ≥ 9`, used at `M = 20`, `= 2.2141…`.

PROVED unconditional: `h1`..`h24`, `kappa1`..`kappa24`, the 24 Möbius values; `finitePart_20`,
the paper's `1.6659…`; `bound41_at_20_gt`, the (41) right side at `M = 20` exceeds `2.2141`;
`bound41_at_24_lt`, at `M = 24` it is below `2.184`; `tail_partial`, `tsum_le_P`,
`series_le_of_tail`, the summation-by-parts tail step in discrete form; `k_nonneg`.
CONDITIONAL: `C2_le_conditional`, `C₂ ≤ 2.2141`, ON grouping, the Möbius formula for `e ≤ 24`,
and the Liu, Liu and Wang bound with `C₀⁻¹ e^γ ≤ 2.744`. Binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.HeathBrownPuchta.Lemma8Const
open Finset

set_option linter.unusedSimpArgs false

def h (n : ℕ) : ℚ := ∏ p ∈ n.primeFactors.filter (· ≠ 2), (((p : ℚ) - 1) / ((p : ℚ) - 2))

def kappa (e : ℕ) : ℚ := ∑ d ∈ e.divisors, (ArithmeticFunction.moebius (e / d) : ℚ) * h (2 ^ d - 1)

theorem mu1 : (ArithmeticFunction.moebius 1 : ℤ) = 1 := by simp

theorem mu2 : (ArithmeticFunction.moebius 2 : ℤ) = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu3 : (ArithmeticFunction.moebius 3 : ℤ) = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu4 : (ArithmeticFunction.moebius 4 : ℤ) = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hs => by
    have := hs 2 ⟨1, by norm_num⟩; norm_num at this

theorem mu5 : (ArithmeticFunction.moebius 5 : ℤ) = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu6 : (ArithmeticFunction.moebius 6 : ℤ) = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu7 : (ArithmeticFunction.moebius 7 : ℤ) = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu8 : (ArithmeticFunction.moebius 8 : ℤ) = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hs => by
    have := hs 2 ⟨2, by norm_num⟩; norm_num at this

theorem mu9 : (ArithmeticFunction.moebius 9 : ℤ) = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hs => by
    have := hs 3 ⟨1, by norm_num⟩; norm_num at this

theorem mu10 : (ArithmeticFunction.moebius 10 : ℤ) = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu11 : (ArithmeticFunction.moebius 11 : ℤ) = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu12 : (ArithmeticFunction.moebius 12 : ℤ) = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hs => by
    have := hs 2 ⟨3, by norm_num⟩; norm_num at this

theorem mu13 : (ArithmeticFunction.moebius 13 : ℤ) = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu14 : (ArithmeticFunction.moebius 14 : ℤ) = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu15 : (ArithmeticFunction.moebius 15 : ℤ) = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu16 : (ArithmeticFunction.moebius 16 : ℤ) = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hs => by
    have := hs 2 ⟨4, by norm_num⟩; norm_num at this

theorem mu17 : (ArithmeticFunction.moebius 17 : ℤ) = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu18 : (ArithmeticFunction.moebius 18 : ℤ) = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hs => by
    have := hs 3 ⟨2, by norm_num⟩; norm_num at this

theorem mu19 : (ArithmeticFunction.moebius 19 : ℤ) = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu20 : (ArithmeticFunction.moebius 20 : ℤ) = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hs => by
    have := hs 2 ⟨5, by norm_num⟩; norm_num at this

theorem mu21 : (ArithmeticFunction.moebius 21 : ℤ) = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu22 : (ArithmeticFunction.moebius 22 : ℤ) = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu23 : (ArithmeticFunction.moebius 23 : ℤ) = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num) |>.2 (by simp [Nat.primeFactorsList_ofNat]))]
  simp [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]

theorem mu24 : (ArithmeticFunction.moebius 24 : ℤ) = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hs => by
    have := hs 2 ⟨6, by norm_num⟩; norm_num at this

theorem h1 : h 1 = 1 / 1 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h2 : h 3 = 2 / 1 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h3 : h 7 = 6 / 5 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h4 : h 15 = 8 / 3 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h5 : h 31 = 30 / 29 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h6 : h 63 = 12 / 5 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h7 : h 127 = 126 / 125 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h8 : h 255 = 128 / 45 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h9 : h 511 = 432 / 355 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h10 : h 1023 = 200 / 87 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h11 : h 2047 = 1936 / 1827 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h12 : h 4095 = 192 / 55 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h13 : h 8191 = 8190 / 8189 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h14 : h 16383 = 10584 / 5125 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h15 : h 32767 = 5400 / 4321 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h16 : h 65535 = 32768 / 11475 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h17 : h 131071 = 131070 / 131069 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h18 : h 262143 = 15552 / 6035 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h19 : h 524287 = 524286 / 524285 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h20 : h 1048575 = 32000 / 10179 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h21 : h 2097151 = 254016 / 209375 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h22 : h 4194303 = 2640704 / 1244187 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h23 : h 8388607 = 1642016 / 1606311 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem h24 : h 16777215 = 49152 / 13145 := by
  simp [h, Nat.primeFactors, Nat.primeFactorsList_ofNat, Finset.filter_insert, Finset.filter_singleton] <;> norm_num

theorem kappa1 : kappa 1 = 1 / 1 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa2 : kappa 2 = 1 / 1 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa3 : kappa 3 = 1 / 5 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa4 : kappa 4 = 2 / 3 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa5 : kappa 5 = 1 / 29 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa6 : kappa 6 = 1 / 5 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa7 : kappa 7 = 1 / 125 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa8 : kappa 8 = 8 / 45 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa9 : kappa 9 = 6 / 355 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa10 : kappa 10 = 23 / 87 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa11 : kappa 11 = 109 / 1827 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa12 : kappa 12 = 14 / 33 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa13 : kappa 13 = 1 / 8189 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa14 : kappa 14 = 293 / 5125 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa15 : kappa 15 = 329 / 21605 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa16 : kappa 16 = 128 / 11475 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa17 : kappa 17 = 1 / 131069 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa18 : kappa 18 = 966 / 6035 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa19 : kappa 19 = 1 / 524285 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa20 : kappa 20 = 1814 / 10179 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa21 : kappa 21 = 1091 / 209375 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa22 : kappa 22 = 78101 / 1244187 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa23 : kappa 23 = 35705 / 1606311 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num

theorem kappa24 : kappa 24 = 8344 / 118305 := by
  rw [kappa]; simp only [Nat.divisors_ofNat]
  simp [Finset.sum_insert, mu1, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13, mu14, mu15, mu16, mu17, mu18, mu19, mu20, mu21, mu22, mu23, mu24, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] <;> norm_num


/-- The finite part of (41): `Σ_{m ≤ M} κ(m) (1/m - 1/M)`. -/
def finitePart (M : ℕ) : ℚ := ∑ m ∈ range M, kappa (m + 1) * (1 / ((m : ℚ) + 1) - 1 / M)

/-- (41) at `M = 20`: the paper's `1.6659…`. -/
theorem finitePart_20 : 16659262 / 10000000 < finitePart 20 ∧ finitePart 20 < 16659263 / 10000000 := by
  simp only [finitePart, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.reduceAdd, kappa1, kappa2, kappa3, kappa4, kappa5, kappa6, kappa7, kappa8, kappa9, kappa10, kappa11, kappa12, kappa13, kappa14, kappa15, kappa16, kappa17, kappa18, kappa19, kappa20, kappa21, kappa22, kappa23, kappa24]
  norm_num

/-- The same finite part at `M = 24`. -/
theorem finitePart_24 : finitePart 24 < 17035192 / 10000000 := by
  simp only [finitePart, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.reduceAdd, kappa1, kappa2, kappa3, kappa4, kappa5, kappa6, kappa7, kappa8, kappa9, kappa10, kappa11, kappa12, kappa13, kappa14, kappa15, kappa16, kappa17, kappa18, kappa19, kappa20, kappa21, kappa22, kappa23, kappa24]
  norm_num

/-- `Σ_{e ≤ 24} κ(e) = 4.6348…`, used only in the vacuity test. -/
theorem kappa_sum_24 : ∑ e ∈ range 24, kappa (e + 1) < 4635 / 1000 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, kappa1, kappa2, kappa3, kappa4, kappa5, kappa6, kappa7, kappa8, kappa9, kappa10, kappa11, kappa12, kappa13, kappa14, kappa15, kappa16, kappa17, kappa18, kappa19, kappa20, kappa21, kappa22, kappa23, kappa24]
  norm_num

theorem exp3_lt : Real.exp 3 < 2008553694 / 100000000 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  calc Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 := by gcongr
    _ < _ := by norm_num

theorem exp3_gt : 2008553691 / 100000000 < Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (2008553691 / 100000000 : ℝ) < (2.7182818283 : ℝ) ^ 3 := by norm_num
    _ < _ := by gcongr

/-- `log 20 > 2.99572`, from `log x ≥ 1 - 1/x` at `x = 20 / e³`. -/
theorem log20_gt : 299572 / 100000 < Real.log 20 := by
  have h3 := exp3_lt
  have hp : 0 < Real.exp 3 := Real.exp_pos 3
  have hx : 0 < 20 / Real.exp 3 := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos hx
  rw [Real.log_div (by norm_num) hp.ne', Real.log_exp, inv_div] at hl
  have : Real.exp 3 / 20 < 2008553694 / 2000000000 := by linarith
  linarith

/-- `log 24 < 3.195`, from `log x ≤ x - 1` at `x = 24 / e³`. -/
theorem log24_lt : Real.log 24 < 3195 / 1000 := by
  have h3 := exp3_gt
  have hp : 0 < Real.exp 3 := Real.exp_pos 3
  have hx : 0 < 24 / Real.exp 3 := by positivity
  have hl := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (by norm_num) hp.ne', Real.log_exp] at hl
  have : 24 / Real.exp 3 < 24 / (2008553691 / 100000000) := by gcongr
  have : (24 : ℝ) / (2008553691 / 100000000) < 1195 / 1000 := by norm_num
  linarith

/-- QUESTION evidence: the right side of (41) at `M = 20`, the paper's choice, exceeds `2.2141`;
Python `2.2141407`. -/
theorem bound41_at_20_gt :
    (22141 / 10000 : ℝ) < (finitePart 20 : ℝ) + 2744 / 1000 * (1 + Real.log 20) / 20 := by
  have h1 := finitePart_20.1
  have h1' : ((16659262 / 10000000 : ℚ) : ℝ) < (finitePart 20 : ℝ) := by exact_mod_cast h1
  have h2 := log20_gt
  push_cast at h1'
  nlinarith

/-- The same bound at `M = 24` is below `2.184`. -/
theorem bound41_at_24_lt :
    (finitePart 24 : ℝ) + 2744 / 1000 * (1 + Real.log 24) / 24 < 2184 / 1000 := by
  have h1 : (finitePart 24 : ℝ) < ((17035192 / 10000000 : ℚ) : ℝ) := by exact_mod_cast finitePart_24
  have h2 := log24_lt
  push_cast at h1
  nlinarith

/-- `log(N+1) - log N ≤ 1/N`. -/
theorem log_succ_sub_le {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * (Real.log ((N : ℝ) + 1) - Real.log N) ≤ 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 < ((N : ℝ) + 1) / N := by positivity
  have hl := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (by positivity) hN'.ne'] at hl
  have : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
  rw [this] at hl
  have := mul_le_mul_of_nonneg_left hl hN'.le
  rwa [mul_one_div_cancel hN'.ne'] at this

/-- The quantity that decreases in `N`: `Σ_{e ≤ N} κ(e) (1/e - 1/N) + A (1 + log N)/N`. -/
noncomputable def P (κ : ℕ → ℝ) (A : ℝ) (N : ℕ) : ℝ :=
  ∑ e ∈ range N, κ (e + 1) * (1 / ((e : ℝ) + 1) - 1 / N) + A * (1 + Real.log N) / N

theorem P_succ_le (κ : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A) {N : ℕ} (hN : 1 ≤ N)
    (hS : ∑ e ∈ range N, κ (e + 1) ≤ A * Real.log N) : P κ A (N + 1) ≤ P κ A N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold P
  rw [Finset.sum_range_succ]
  push_cast
  have e1 : ∑ e ∈ range N, κ (e + 1) * (1 / ((e : ℝ) + 1) - 1 / ((N : ℝ) + 1)) =
      ∑ e ∈ range N, κ (e + 1) * (1 / ((e : ℝ) + 1) - 1 / N) +
        (∑ e ∈ range N, κ (e + 1)) * (1 / N - 1 / ((N : ℝ) + 1)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => by ring
  rw [e1]
  have hd : 0 ≤ 1 / (N : ℝ) - 1 / ((N : ℝ) + 1) := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hN' (by linarith)
  have h1 := mul_le_mul_of_nonneg_right hS hd
  have hlog := log_succ_sub_le hN
  have key : A * Real.log N * (1 / N - 1 / ((N : ℝ) + 1)) + A * (1 + Real.log ((N : ℝ) + 1)) / ((N : ℝ) + 1)
      ≤ A * (1 + Real.log N) / N := by
    have e2 : A * (1 + Real.log N) / N - (A * Real.log N * (1 / N - 1 / ((N : ℝ) + 1)) +
        A * (1 + Real.log ((N : ℝ) + 1)) / ((N : ℝ) + 1)) =
        A * (1 - N * (Real.log ((N : ℝ) + 1) - Real.log N)) / (N * ((N : ℝ) + 1)) := by
      field_simp; ring
    have : 0 ≤ A * (1 - N * (Real.log ((N : ℝ) + 1) - Real.log N)) / (N * ((N : ℝ) + 1)) := by
      apply div_nonneg _ (by positivity); exact mul_nonneg hA (by linarith)
    linarith
  have : κ (N + 1) * (1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 1)) = 0 := by ring
  linarith

/-- The tail step of (41), discrete form: if `S(n) = Σ_{e ≤ n} κ(e) ≤ A log n` for all `n ≥ M`,
then every partial sum `Σ_{e ≤ N} κ(e)/e`, `N ≥ M`, is at most
`Σ_{e ≤ M} κ(e) (1/e - 1/M) + A (1 + log M)/M`. -/
theorem tail_partial (κ : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A) {M : ℕ} (hM : 1 ≤ M)
    (hS : ∀ n, M ≤ n → ∑ e ∈ range n, κ (e + 1) ≤ A * Real.log n) :
    ∀ N, M ≤ N → ∑ e ∈ range N, κ (e + 1) / ((e : ℝ) + 1) ≤ P κ A M := by
  have mono : ∀ N, M ≤ N → P κ A N ≤ P κ A M := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (P_succ_le κ hA (le_trans hM hn) (hS n hn)).trans ih
  intro N hN
  have hN1 : 1 ≤ N := le_trans hM hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
  have hP := mono N hN
  have e : ∑ e ∈ range N, κ (e + 1) / ((e : ℝ) + 1) =
      ∑ e ∈ range N, κ (e + 1) * (1 / ((e : ℝ) + 1) - 1 / N) + (∑ e ∈ range N, κ (e + 1)) / N := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => by ring
  rw [e]
  have h2 : (∑ e ∈ range N, κ (e + 1)) / N ≤ A * Real.log N / N :=
    div_le_div_of_nonneg_right (hS N hN) hN'.le
  have h3 : A * Real.log N / N ≤ A * (1 + Real.log N) / N := by
    apply div_le_div_of_nonneg_right _ hN'.le; nlinarith
  unfold P at hP ⊢
  linarith

/-- With `κ ≥ 0`, the full series `Σ_e κ(e)/e` is at most the (41) bound. -/
theorem tsum_le_P (κ : ℕ → ℝ) (hκ : ∀ e, 0 ≤ κ e) {A : ℝ} (hA : 0 ≤ A) {M : ℕ} (hM : 1 ≤ M)
    (hS : ∀ n, M ≤ n → ∑ e ∈ range n, κ (e + 1) ≤ A * Real.log n) :
    ∑' e : ℕ, κ (e + 1) / ((e : ℝ) + 1) ≤ P κ A M := by
  apply Real.tsum_le_of_sum_range_le (fun e => div_nonneg (hκ _) (by positivity))
  intro n
  rcases le_total M n with h | h
  · exact tail_partial κ hA hM hS n h
  · calc ∑ e ∈ range n, κ (e + 1) / ((e : ℝ) + 1)
        ≤ ∑ e ∈ range M, κ (e + 1) / ((e : ℝ) + 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
            (fun e _ _ => div_nonneg (hκ _) (by positivity))
      _ ≤ P κ A M := tail_partial κ hA hM hS M le_rfl

/-- Abstract (41) at `M = 24` with the paper's `A = 2.744`: if `κ ≥ 0`, `κ(e)` is the Möbius value
`kappa e` for `e ≤ 24`, and `S(n) ≤ 2.744 log n` for `n ≥ 24`, then `Σ κ(e)/e ≤ 2.184 < 2.2141`. -/
theorem series_le_of_tail (κ : ℕ → ℝ) (hκ : ∀ e, 0 ≤ κ e)
    (hmob : ∀ e, 1 ≤ e → e ≤ 24 → κ e = (kappa e : ℝ))
    (hS : ∀ n, 24 ≤ n → ∑ e ∈ range n, κ (e + 1) ≤ 2744 / 1000 * Real.log n) :
    ∑' e : ℕ, κ (e + 1) / ((e : ℝ) + 1) ≤ 22141 / 10000 := by
  have h := tsum_le_P κ hκ (by norm_num) (by norm_num) hS
  have hP : P κ (2744 / 1000) 24 = (finitePart 24 : ℝ) + 2744 / 1000 * (1 + Real.log 24) / 24 := by
    unfold P finitePart
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hmob (e + 1) (by omega) (by simp at he; omega)]
  have := bound41_at_24_lt
  linarith

/-! ## The paper's objects -/

/-- `ε(d)`, the order of `2` modulo `d`. -/
noncomputable def eps (d : ℕ) : ℕ := orderOf (2 : ZMod d)

/-- `k(d)`, multiplicative, `k(p) = 1/(p-2)` for odd primes, `0` at `2` and on prime squares. -/
noncomputable def k (d : ℕ) : ℚ :=
  if Odd d ∧ Squarefree d then ∏ p ∈ d.primeFactors, 1 / ((p : ℚ) - 2) else 0

/-- `C₂ = Σ_d k(d)/ε(d)`, (35). -/
noncomputable def C2 : ℝ := ∑' d : ℕ, (k d : ℝ) / eps d

/-- `κ(e) = Σ_{ε(d) = e} k(d)`; `ε(d) = e` forces `d ∣ 2^e - 1`, so the range is finite. -/
noncomputable def kappaTrue (e : ℕ) : ℝ :=
  ∑ d ∈ (2 ^ e - 1).divisors.filter (fun d => eps d = e), (k d : ℝ)

theorem k_nonneg (d : ℕ) : 0 ≤ k d := by
  unfold k
  split_ifs with hd
  · apply Finset.prod_nonneg
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hd.1) (even_iff_two_dvd.2 hpd)
    have : 3 ≤ p := by have := hpp.two_le; omega
    have : (3 : ℚ) ≤ p := by exact_mod_cast this
    apply div_nonneg zero_le_one; linarith
  · exact le_rfl

theorem kappaTrue_nonneg (e : ℕ) : 0 ≤ kappaTrue e :=
  Finset.sum_nonneg fun d _ => by exact_mod_cast k_nonneg d

/-- `C₂ ≤ 2.2141`, CONDITIONAL ON three inputs:
`grouping`, `C₂ = Σ_e κ(e)/e`, a rearrangement of a series of nonnegative terms;
`mobius`, the paper's `κ(e) = Σ_{d ∣ e} μ(e/d) h(2^d - 1)` for `e ≤ 24`;
`llw`, `Σ_{ε(d) ≤ n} k(d) ≤ 2.744 log n` for `n ≥ 24`, from `s(x) ≤ C₀⁻¹ m/φ(m)` and
Liu, Liu and Wang's `m/φ(m) ≤ e^γ log x`, `x ≥ 9`, with `C₀⁻¹ e^γ ≤ 2.744`. -/
theorem C2_le_conditional
    (grouping : C2 = ∑' e : ℕ, kappaTrue (e + 1) / ((e : ℝ) + 1))
    (mobius : ∀ e, 1 ≤ e → e ≤ 24 → kappaTrue e = (kappa e : ℝ))
    (llw : ∀ n, 24 ≤ n → ∑ e ∈ range n, kappaTrue (e + 1) ≤ 2744 / 1000 * Real.log n) :
    C2 ≤ 22141 / 10000 := by
  rw [grouping]; exact series_le_of_tail kappaTrue kappaTrue_nonneg mobius llw

/-- Vacuity test for `series_le_of_tail`: `κ = kappa` on `1..24`, `0` after, meets every hypothesis. -/
theorem series_le_of_tail_nonvacuous :
    ∃ κ : ℕ → ℝ, (∀ e, 0 ≤ κ e) ∧ (∀ e, 1 ≤ e → e ≤ 24 → κ e = (kappa e : ℝ)) ∧
      (∀ n, 24 ≤ n → ∑ e ∈ range n, κ (e + 1) ≤ 2744 / 1000 * Real.log n) := by
  refine ⟨fun e => if 1 ≤ e ∧ e ≤ 24 then (kappa e : ℝ) else 0, ?_, ?_, ?_⟩
  · intro e
    show 0 ≤ (if 1 ≤ e ∧ e ≤ 24 then (kappa e : ℝ) else 0)
    split_ifs with he
    · obtain ⟨h1, h2⟩ := he
      interval_cases e <;> simp only [kappa1, kappa2, kappa3, kappa4, kappa5, kappa6, kappa7, kappa8, kappa9, kappa10, kappa11, kappa12, kappa13, kappa14, kappa15, kappa16, kappa17, kappa18, kappa19, kappa20, kappa21, kappa22, kappa23, kappa24] <;> norm_num
    · exact le_rfl
  · intro e h1 h2; simp [h1, h2]
  · intro n hn
    have hsplit : ∑ e ∈ range n, (fun e => if 1 ≤ e ∧ e ≤ 24 then (kappa e : ℝ) else 0) (e + 1) =
        ∑ e ∈ range 24, (kappa (e + 1) : ℝ) := by
      rw [← Finset.sum_range_add_sum_Ico _ hn]
      have h0 : ∑ e ∈ Finset.Ico 24 n,
          (fun e => if 1 ≤ e ∧ e ≤ 24 then (kappa e : ℝ) else 0) (e + 1) = 0 := by
        refine Finset.sum_eq_zero fun e he => ?_
        simp only [Finset.mem_Ico] at he
        simp only [show ¬(1 ≤ e + 1 ∧ e + 1 ≤ 24) by omega, ite_false]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun e he => ?_
      simp only [Finset.mem_range] at he
      exact if_pos (show 1 ≤ e + 1 ∧ e + 1 ≤ 24 by omega)
    rw [hsplit]
    have hq : (∑ e ∈ range 24, (kappa (e + 1) : ℝ)) < ((4635 / 1000 : ℚ) : ℝ) := by
      rw [← Rat.cast_sum]; exact_mod_cast kappa_sum_24
    have h3 := exp3_lt
    have hl3 : 3 < Real.log 24 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; linarith
    have hmono : Real.log 24 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    push_cast at hq
    linarith

end LeanLab.HeathBrownPuchta.Lemma8Const
