module

public import Mathlib
public import LeanLab.HelfgottMajor.BookT141

/-!
# Helfgott's book, Part IV of 2020-04-01, proof of Theorem 14.3 parts 1 and 2: the arithmetic

Unit U-6719, CLOUD 20261020T1914Z-cloud49, P0014. AI wrote this file.

Source: book pages 448 to 451, copy papers/P0014-book-PartIV.pdf, page images checked; the
statement on book p. 377, Prop. 16.19 and (16.60) on p. 444. Numbers recomputed in
gen/book_t143_U6719.py with output gen/book_t143_U6719.out.

Part 1: `H = 100`, `q ≤ r = 400000`, `T₀ = (1375/32) max(|δ|, 4)`, `T = T₀ + H`,
`qT ≤ 6.875·10⁷ + 100·400000 = 1.0875·10⁸`, `r₀ = 1375/(128π²)`, so `1/√r₀ = π√(128/1375)`.
Part 2: `H = 200`, `q ≤ 2r' = 300000`, `T₀ = (125/2) max(|δ|, 4)`, `qT ≤ 1.35·10⁸`,
`r₀ = 125/(8π²)`, so `1/√r₀ = π√(8/125)`.

PROVED, MATCH with the printed values:
* `qT_p1`, `r0_p1`, `r0_p2`: the parameter arithmetic;
* `exp_p1`, `exp_p2`: `0.75 e^{-(π/4)T₀} ≤ 1.7763·10⁻⁵⁹`, `≤ 3.9953·10⁻⁸⁶`;
* `invsqrt_p1`, `invsqrt_p2`: `1/√r ≤ 606.225`, `≤ 584.033`;
* `eps_p1`: `(1.15275·10⁻⁷ + 1.7763·10⁻⁵⁹) log(1.0875·10⁸/2π) ≤ 1.92126·10⁻⁶ ≤ 1.93·10⁻⁶`;
* `kappa_p1`, `kappa_p2`: `77.9`, `95`, as printed, with `√T₀` in place of `√T`;
* `logq_p1`, `logq_p2`: `22.4`, `473`, `158` for `q ≤ 400000`; `22.2`, `462`, `154` for
  `q ≤ 300000`;
* `final_p1`, `final_p2`: the last steps for `x ≥ 10⁶`, `22.5` and `2|δ|`, `22.3` and `2|δ|`.

CONDITIONAL, on values of the book's `E(r)` of (15.2) checked in Python only:
* `lead_p1`, `lead_p2`: `max(1.05, 2.72/√r₀) e^{-y} ≤ 1.59299·10⁻⁹`, `≤ 1.80186·10⁻¹⁸` for
  `y ≥ 21.21593`, `y ≥ 41.62864`: CONDITIONAL ON `E(r₀)·1375/8 ≥ 21.21593` and
  `250 E(r₀) ≥ 41.62864`, recomputed as 21.2159307 and 41.6286432;
* `small_p1`, `small_p2`: (16.61), (16.62) for `r ≤ 0.001`: CONDITIONAL ON
  `E(0.001)/(0.001π²)·(1375/32)² ≥ 23.38383` and `E(0.001)/(0.001π²)·(125/2)² ≥ 49.47`,
  recomputed as 23.3838309 and 49.4732290, and on the book's Lemma 15.23 that `E(r)/r` is
  non-increasing. The bisection maxima on `[0.001, r₀]` are checked in Python only.

QUESTION, numerically reproduced, no independent falsifier yet:
* `eps_p2_gap`, `eps_p2_true`: p. 450 prints `(1.8019·10⁻¹⁸ + 3.9953·10⁻⁸⁶) log(1.35·10⁸/2π)
  ≤ 1.802·10⁻¹⁸`, dropping the factor `log(1.35·10⁸/2π) ≈ 16.88`; the product is
  `3.0421·10⁻¹⁷`, so `ε'₊ = 1.81·10⁻¹⁸` of Theorem 14.3 part 2 does not follow; `3.05·10⁻¹⁷`
  does. Part 1 and Theorems 14.1, 14.2 keep the factor.
* `sqrtT_gap_p1`, `sqrtT_gap_p2`: (16.60) has `√T` with `T = T₀ + H`, while the proofs bound
  `√T` by `√T₀`, as in `kappa_p1`, `kappa_p2`. At `|δ| ≤ 4` and `q = 400000`, resp. `300000`,
  the printed bound `77.9√4`, resp. `95√4`, fails. `kappa_fix_p1`, `kappa_fix_p2`: with
  `T = T₀ + H` the coefficients `98` and `127.4` do follow, for every `max(|δ|,4) ≥ 4`.

Ternary Goldbach is a theorem; binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-20.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.BookT143
open Real Finset
open LeanLab.HelfgottMajor.BookT141

/-! ## Elementary bounds -/

lemma exp2_lt : exp 2 < 7.39 := by
  have h := exp_one_lt_d9
  have e : exp (2 : ℝ) = exp 1 * exp 1 := by rw [← exp_add]; norm_num
  rw [e]; nlinarith [exp_pos (1 : ℝ)]

/-- `log 10 > 2.302585`, via `exp 2.302585 < 10`. -/
lemma log10_gt : 2.302585 < log 10 := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  have e : exp (2.302585 : ℝ) = exp 1 * exp 1 * exp 0.302585 := by
    rw [← exp_add, ← exp_add]; norm_num
  have h1 := exp_one_lt_d9
  have h2 := exp_bound' (x := (0.302585 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  rw [e]; nlinarith [exp_pos (0.302585 : ℝ), exp_pos 1]

/-- `log π < 1.1447299`, via `π < exp 1.1447299`. -/
lemma log_pi_lt : log π < 1.1447299 := by
  rw [log_lt_iff_lt_exp pi_pos]
  have h := exp_lower 1 (r := 0.1447299) (by norm_num) 12
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := pi_bds.2
  linarith

/-- `log 1.0875 < 0.0838815`; value 0.08388148. -/
lemma log10875_lt : log 1.0875 < 0.0838815 := by
  rw [log_lt_iff_lt_exp (by norm_num)]
  have h := exp_lower 0 (r := 0.0838815) (by norm_num) 9
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢
  linarith

/-- `0.3 < log 1.35 < 0.300105`; value 0.30010459. -/
lemma log135_bds : 0.3 < log 1.35 ∧ log 1.35 < 0.300105 := by
  constructor
  · rw [lt_log_iff_exp_lt (by norm_num)]
    have h := exp_bound' (x := (0.3 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith
  · rw [log_lt_iff_lt_exp (by norm_num)]
    have h := exp_lower 0 (r := 0.300105) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢
    linarith

/-- `log 3 < 1.0986123`; value 1.09861229. -/
lemma log3_lt : log 3 < 1.0986123 := by
  rw [log_lt_iff_lt_exp (by norm_num)]
  have h := exp_lower 1 (r := 0.0986123) (by norm_num) 10
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢
  linarith

/-- `log 300000 = log 3 + 5 log 10 < 12.6115378`; value 12.6115361. -/
lemma log3e5_lt : log 300000 < 12.6115378 := by
  rw [show (300000 : ℝ) = 3 * 10 ^ 5 by norm_num, log_mul (by norm_num) (by norm_num), log_pow]
  have := log10_lt; have := log3_lt; push_cast; linarith

/-- `log 108750000 = log 10⁸ + log 1.0875 < 18.5045623`. -/
lemma logA_lt : log 108750000 < 18.5045623 := by
  rw [show (108750000 : ℝ) = 1e8 * 1.0875 by norm_num, log_mul (by norm_num) (by norm_num)]
  have := log1e8_lt; have := log10875_lt; linarith

lemma logA_gt : 16.63 < log 108750000 := by
  have h : log 1e8 ≤ log 108750000 := log_le_log (by norm_num) (by norm_num)
  rw [show (1e8 : ℝ) = 10 ^ 8 by norm_num, log_pow] at h
  have := log10_gt; push_cast at h; linarith

/-- `log 1.35·10⁸ < 18.7207858`. -/
lemma logB_lt : log 1.35e8 < 18.7207858 := by
  rw [show (1.35e8 : ℝ) = 1e8 * 1.35 by norm_num, log_mul (by norm_num) (by norm_num)]
  have := log1e8_lt; have := log135_bds.2; linarith

lemma logB_gt : 16.63 < log 1.35e8 := by
  have h : log 108750000 ≤ log 1.35e8 := log_le_log (by norm_num) (by norm_num)
  have := logA_gt; linarith

/-- `log(1.0875·10⁸/2π) < 16.6666855`; value 16.6666852. -/
lemma LA_lt : log (108750000 / (2 * π)) < 16.6666855 := by
  rw [show (108750000 : ℝ) / (2 * π) = 1e8 / (2 * π) * 1.0875 by ring,
    log_mul (by positivity) (by norm_num)]
  have := LQ_lt; have := log10875_lt; linarith

/-- `16.8828 < log(1.35·10⁸/2π) < 16.882909`; value 16.8829083. -/
lemma LB_bds : 16.8828 < log (1.35e8 / (2 * π)) ∧ log (1.35e8 / (2 * π)) < 16.882909 := by
  rw [show (1.35e8 : ℝ) / (2 * π) = 1e8 / (2 * π) * 1.35 by ring,
    log_mul (by positivity) (by norm_num)]
  have hq := LQ_lt; have hb := log135_bds
  refine ⟨?_, by linarith⟩
  rw [log_div (by norm_num) (by positivity), log_mul (by norm_num) pi_pos.ne',
    show (1e8 : ℝ) = 10 ^ 8 by norm_num, log_pow]
  have := log10_gt; have := log_pi_lt; have := log_two_lt_d9
  push_cast; linarith

lemma sqrt_1e6 {x : ℝ} (hx : 1e6 ≤ x) : 1000 ≤ √x := by
  rw [show (1000 : ℝ) = √(1e6) by rw [show (1e6 : ℝ) = 1000 ^ 2 by norm_num,
    sqrt_sq (by norm_num)]]
  exact sqrt_le_sqrt hx

/-! ## Parameters -/

/-- **Part 1 parameters**, book p. 448: `6.875·10⁷/4r = 1375/32 = (1375/8)/4` at `r = 400000`,
`6.875·10⁷ + 100q ≤ 10⁸` iff `q ≤ 312500`, `qT ≤ 1.0875·10⁸` at `q = 400000`. -/
theorem qT_p1 :
    (6.875e7 : ℝ) / (4 * 400000) = 1375 / 32 ∧ (1375 / 8 : ℝ) / 4 = 1375 / 32 ∧
    (6.875e7 : ℝ) + 100 * 312500 = 1e8 ∧ (6.875e7 : ℝ) + 100 * 400000 = 108750000 ∧
    (250 : ℝ) * (2 * 150000) + 200 * (2 * 150000) = 1.35e8 := by norm_num

/-- **`r₀` of part 1**: the two lower bounds `E(r₀)·1375/8` and `E(r₀)/(π²r₀)·(1375/32)²`
agree exactly when `r₀ = 1375/(128π²)`. -/
theorem r0_p1 : (1375 / 32 : ℝ) ^ 2 / (π ^ 2 * (1375 / (128 * π ^ 2))) = 1375 / 8 := by
  have : π ≠ 0 := pi_pos.ne'
  field_simp; ring

/-- **`r₀` of part 2**: `250 = (125/2)²/(π² r₀)` at `r₀ = 125/(8π²)`. -/
theorem r0_p2 : (125 / 2 : ℝ) ^ 2 / (π ^ 2 * (125 / (8 * π ^ 2))) = 250 := by
  have : π ≠ 0 := pi_pos.ne'
  field_simp; ring

/-! ## The exponential terms -/

/-- **Part 1, `r ≥ r₀`**: `1.05 ≤ 2.72/√r₀` and `2.72/√r₀ · e^{-y} ≤ 1.59299·10⁻⁹` for
`y ≥ 21.21593`. CONDITIONAL ON `E(r₀)·1375/8 ≥ 21.21593` where applied; value 21.2159307. -/
theorem lead_p1 {y : ℝ} (hy : 21.21593 ≤ y) :
    1.05 ≤ 2.72 * (π * √(128 / 1375)) ∧
    2.72 * (π * √(128 / 1375)) * exp (-y) ≤ 1.59299e-9 := by
  obtain ⟨p1, p2⟩ := pi_bds
  have hs1 : √(128 / 1375) < 0.3051080286 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0.305 < √(128 / 1375) := by rw [lt_sqrt (by norm_num)]; norm_num
  refine ⟨by nlinarith, ?_⟩
  have he : (1.636670e9 : ℝ) ≤ exp 21.21593 := by
    have h := exp_lower 21 (r := 0.21593) (by norm_num) 10
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hmono : exp (-y) ≤ (exp 21.21593)⁻¹ := by
    rw [← exp_neg]; exact exp_le_exp.mpr (by linarith)
  have hinv : (exp 21.21593)⁻¹ ≤ 1 / 1.636670e9 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) he
  have hk : 2.72 * (π * √(128 / 1375)) ≤ 2.6071884 := by nlinarith
  calc 2.72 * (π * √(128 / 1375)) * exp (-y) ≤ 2.6071884 * (1 / 1.636670e9) :=
        mul_le_mul hk (hmono.trans hinv) (exp_pos _).le (by norm_num)
    _ ≤ 1.59299e-9 := by norm_num

/-- **Part 2, `r ≥ r₀`**: `1.05 ≤ 2.72/√r₀` and `2.72/√r₀ · e^{-y} ≤ 1.80186·10⁻¹⁸` for
`y ≥ 41.62864`. CONDITIONAL ON `250 E(r₀) ≥ 41.62864` where applied; value 41.6286432. -/
theorem lead_p2 {y : ℝ} (hy : 41.62864 ≤ y) :
    1.05 ≤ 2.72 * (π * √(8 / 125)) ∧
    2.72 * (π * √(8 / 125)) * exp (-y) ≤ 1.80186e-18 := by
  obtain ⟨p1, p2⟩ := pi_bds
  have hs1 : √(8 / 125) < 0.2529822129 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0.25 < √(8 / 125) := by rw [lt_sqrt (by norm_num)]; norm_num
  refine ⟨by nlinarith, ?_⟩
  have he : (1.1997441e18 : ℝ) ≤ exp 41.62864 := by
    have h := exp_lower 41 (r := 0.62864) (by norm_num) 12
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hmono : exp (-y) ≤ (exp 41.62864)⁻¹ := by
    rw [← exp_neg]; exact exp_le_exp.mpr (by linarith)
  have hinv : (exp 41.62864)⁻¹ ≤ 1 / 1.1997441e18 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) he
  have hk : 2.72 * (π * √(8 / 125)) ≤ 2.1617665 := by nlinarith
  calc 2.72 * (π * √(8 / 125)) * exp (-y) ≤ 2.1617665 * (1 / 1.1997441e18) :=
        mul_le_mul hk (hmono.trans hinv) (exp_pos _).le (by norm_num)
    _ ≤ 1.80186e-18 := by norm_num

/-- **`1/√r` bounds**: `π√(6.875·10⁷)·32/1375 ≤ 606.225`, `π√(1.35·10⁸)·2/125 ≤ 584.033`. -/
theorem invsqrt_p1 : π * √6.875e7 * (32 / 1375) ≤ 606.225 := by
  obtain ⟨p1, p2⟩ := pi_bds
  have hs : √6.875e7 < 8291.562 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have hs0 := sqrt_nonneg (6.875e7 : ℝ)
  nlinarith

theorem invsqrt_p2 : π * √1.35e8 * (2 / 125) ≤ 584.033 := by
  obtain ⟨p1, p2⟩ := pi_bds
  have hs : √1.35e8 < 11618.9501 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have hs0 := sqrt_nonneg (1.35e8 : ℝ)
  nlinarith

/-- **(16.61) for `r ≤ 0.001`**: `2.72 · 606.225 · e^{-y} ≤ 1.15275·10⁻⁷` for `y ≥ 23.38383`.
CONDITIONAL ON `E(0.001)/(0.001π²)·(1375/32)² ≥ 23.38383`, value 23.3838309, and on
Lemma 15.23 of the book, where applied. -/
theorem small_p1 {y : ℝ} (hy : 23.38383 ≤ y) : 2.72 * 606.225 * exp (-y) ≤ 1.15275e-7 := by
  have he : (1.430435e10 : ℝ) ≤ exp 23.38383 := by
    have h := exp_lower 23 (r := 0.38383) (by norm_num) 12
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hmono : exp (-y) ≤ (exp 23.38383)⁻¹ := by
    rw [← exp_neg]; exact exp_le_exp.mpr (by linarith)
  have hinv : (exp 23.38383)⁻¹ ≤ 1 / 1.430435e10 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) he
  calc 2.72 * 606.225 * exp (-y) ≤ 2.72 * 606.225 * (1 / 1.430435e10) :=
        mul_le_mul_of_nonneg_left (hmono.trans hinv) (by norm_num)
    _ ≤ 1.15275e-7 := by norm_num

/-- **(16.62) for `r ≤ 0.001`**: `2.72 · 584.033 · e^{-y} ≤ 5.46217·10⁻¹⁹` for `y ≥ 49.47`.
CONDITIONAL ON `E(0.001)/(0.001π²)·(125/2)² ≥ 49.47`, value 49.4732290, and on Lemma 15.23. -/
theorem small_p2 {y : ℝ} (hy : 49.47 ≤ y) : 2.72 * 584.033 * exp (-y) ≤ 5.46217e-19 := by
  have he : (3.0e21 : ℝ) ≤ exp 49.47 := by
    have h := exp_lower 49 (r := 0.47) (by norm_num) 8
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hmono : exp (-y) ≤ (exp 49.47)⁻¹ := by
    rw [← exp_neg]; exact exp_le_exp.mpr (by linarith)
  have hinv : (exp 49.47)⁻¹ ≤ 1 / 3.0e21 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) he
  calc 2.72 * 584.033 * exp (-y) ≤ 2.72 * 584.033 * (1 / 3.0e21) :=
        mul_le_mul_of_nonneg_left (hmono.trans hinv) (by norm_num)
    _ ≤ 5.46217e-19 := by norm_num

/-- **`0.75 e^{-(π/4)T₀}` of part 1**: `≤ 1.7763·10⁻⁵⁹` for `T₀ ≥ 1375/8`. -/
theorem exp_p1 {T : ℝ} (hT : 1375 / 8 ≤ T) : 0.75 * exp (-(π / 4) * T) ≤ 1.7763e-59 := by
  obtain ⟨p1, p2⟩ := pi_bds
  have hmono : exp (-(π / 4) * T) ≤ (exp 134.990309)⁻¹ := by
    rw [← exp_neg]; exact exp_le_exp.mpr (by nlinarith)
  have he : (4.222260e58 : ℝ) ≤ exp 134.990309 := by
    have h := exp_lower 134 (r := 0.990309) (by norm_num) 18
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hinv : (exp 134.990309)⁻¹ ≤ 1 / 4.222260e58 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) he
  calc 0.75 * exp (-(π / 4) * T) ≤ 0.75 * (1 / 4.222260e58) :=
        mul_le_mul_of_nonneg_left (hmono.trans hinv) (by norm_num)
    _ ≤ 1.7763e-59 := by norm_num

/-- **`0.75 e^{-(π/4)T₀}` of part 2**: `≤ 3.9953·10⁻⁸⁶` for `T₀ ≥ 250`. -/
theorem exp_p2 {T : ℝ} (hT : 250 ≤ T) : 0.75 * exp (-(π / 4) * T) ≤ 3.9953e-86 := by
  obtain ⟨p1, p2⟩ := pi_bds
  have hmono : exp (-(π / 4) * T) ≤ (exp 196.34954)⁻¹ := by
    rw [← exp_neg]; exact exp_le_exp.mpr (by nlinarith)
  have he : (1.87721e85 : ℝ) ≤ exp 196.34954 := by
    have h := exp_lower 196 (r := 0.34954) (by norm_num) 10
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hinv : (exp 196.34954)⁻¹ ≤ 1 / 1.87721e85 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) he
  calc 0.75 * exp (-(π / 4) * T) ≤ 0.75 * (1 / 1.87721e85) :=
        mul_le_mul_of_nonneg_left (hmono.trans hinv) (by norm_num)
    _ ≤ 3.9953e-86 := by norm_num

/-! ## `ε₊` -/

/-- **`ε₊` of Theorem 14.3 part 1**: `(1.15275·10⁻⁷ + 1.7763·10⁻⁵⁹) log(1.0875·10⁸/2π) ≤
1.92126·10⁻⁶ ≤ 1.93·10⁻⁶`, MATCH. -/
theorem eps_p1 :
    (1.15275e-7 + 1.7763e-59) * log (108750000 / (2 * π)) ≤ 1.92126e-6 ∧
    (1.92126e-6 : ℝ) ≤ 1.93e-6 := by
  refine ⟨?_, by norm_num⟩
  calc _ ≤ (1.15275e-7 + 1.7763e-59) * 16.6666855 :=
        mul_le_mul_of_nonneg_left LA_lt.le (by norm_num)
    _ ≤ _ := by norm_num

/-- **QUESTION, p. 450**: the printed `(1.8019·10⁻¹⁸ + 3.9953·10⁻⁸⁶) log(1.35·10⁸/2π) ≤
1.802·10⁻¹⁸` is false: the product exceeds `3.042·10⁻¹⁷`, so above `ε'₊ = 1.81·10⁻¹⁸`. -/
theorem eps_p2_gap :
    3.042e-17 < (1.8019e-18 + 3.9953e-86) * log (1.35e8 / (2 * π)) ∧
    (1.81e-18 : ℝ) < (1.8019e-18 + 3.9953e-86) * log (1.35e8 / (2 * π)) := by
  have h := LB_bds.1
  have : (3.042e-17 : ℝ) < (1.8019e-18 + 3.9953e-86) * 16.8828 := by norm_num
  have h2 : (1.8019e-18 + 3.9953e-86) * 16.8828 < (1.8019e-18 + 3.9953e-86) *
      log (1.35e8 / (2 * π)) := mul_lt_mul_of_pos_left h (by norm_num)
  constructor <;> linarith

/-- **Repair of `ε'₊`**: the product is at most `3.0422·10⁻¹⁷ ≤ 3.05·10⁻¹⁷`. -/
theorem eps_p2_true :
    (1.8019e-18 + 3.9953e-86) * log (1.35e8 / (2 * π)) ≤ 3.0422e-17 := by
  calc _ ≤ (1.8019e-18 + 3.9953e-86) * 16.882909 :=
        mul_le_mul_of_nonneg_left LB_bds.2.le (by norm_num)
    _ ≤ _ := by norm_num

/-! ## `κ` and the lower order terms -/

/-- **`77.9` of part 1 as printed**, with `√T₀ = √((1375/32) max(|δ|,4))`:
`(0.566 log 108750000 + 1.41)√(1375/32) ≤ 77.9 ≤ 78`. -/
theorem kappa_p1 : (0.566 * log 108750000 + 1.41) * √(1375 / 32) ≤ 77.9 := by
  have h := logA_lt; have h0 := logA_gt
  have s : √(1375 / 32) < 6.5550554 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have s0 := sqrt_nonneg (1375 / 32 : ℝ)
  nlinarith

/-- **`95` of part 2 as printed**: `(0.566 log 1.35·10⁸ + 1.41)√(125/2) ≤ 95`. -/
theorem kappa_p2 : (0.566 * log 1.35e8 + 1.41) * √(125 / 2) ≤ 95 := by
  have h := logB_lt; have h0 := logB_gt
  have s : √(125 / 2) < 7.9056942 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have s0 := sqrt_nonneg (125 / 2 : ℝ)
  nlinarith

/-- **QUESTION, p. 449**: with `T = T₀ + H` as in (16.60), at `max(|δ|, 4) = 4` and
`q = 400000`, so `T = 271.875` and `qT = 1.0875·10⁸`, the term `0.566√T log qT + 1.41√T`
exceeds `78√4`, so the printed `≤ 77.9√max(|δ|,4)` fails there. -/
theorem sqrtT_gap_p1 :
    (78 : ℝ) * √4 < 0.566 * √(1375 / 32 * 4 + 100) * log (400000 * (1375 / 32 * 4 + 100)) +
      1.41 * √(1375 / 32 * 4 + 100) := by
  have e4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have eA : (400000 : ℝ) * (1375 / 32 * 4 + 100) = 108750000 := by norm_num
  rw [e4, eA]
  have h0 := logA_gt
  have s : 16.48 < √(1375 / 32 * 4 + 100 : ℝ) := by rw [lt_sqrt (by norm_num)]; norm_num
  nlinarith

/-- **QUESTION, p. 450**: the same at `H = 200`, `max(|δ|,4) = 4`, `q = 300000`: `T = 450`,
`qT = 1.35·10⁸`, and the term exceeds `95√4`. -/
theorem sqrtT_gap_p2 :
    (95 : ℝ) * √4 < 0.566 * √(125 / 2 * 4 + 200) * log (300000 * (125 / 2 * 4 + 200)) +
      1.41 * √(125 / 2 * 4 + 200) := by
  have e4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have eB : (300000 : ℝ) * (125 / 2 * 4 + 200) = 1.35e8 := by norm_num
  rw [e4, eB]
  have h0 := logB_gt
  have s : 21.2 < √(125 / 2 * 4 + 200 : ℝ) := by rw [lt_sqrt (by norm_num)]; norm_num
  nlinarith

/-- **Repair, part 1**: for `D = max(|δ|,4) ≥ 4` and `T = (1375/32)D + 100`,
`(0.566 log 108750000 + 1.41)√T ≤ 98√D`. -/
theorem kappa_fix_p1 {D : ℝ} (hD : 4 ≤ D) :
    (0.566 * log 108750000 + 1.41) * √(1375 / 32 * D + 100) ≤ 98 * √D := by
  have h := logA_lt; have h0 := logA_gt
  have hT : √(1375 / 32 * D + 100) ≤ √(1375 / 32 + 25) * √D := by
    rw [← sqrt_mul (by norm_num)]; exact sqrt_le_sqrt (by nlinarith)
  have s : √(1375 / 32 + 25 : ℝ) < 8.2443163 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have sD := sqrt_nonneg D
  have sT := sqrt_nonneg (1375 / 32 + 25 : ℝ)
  have hc : 0 ≤ 0.566 * log 108750000 + 1.41 := by linarith
  calc (0.566 * log 108750000 + 1.41) * √(1375 / 32 * D + 100)
      ≤ (0.566 * log 108750000 + 1.41) * (√(1375 / 32 + 25) * √D) :=
        mul_le_mul_of_nonneg_left hT hc
    _ ≤ 98 * √D := by nlinarith [mul_nonneg sT sD]

/-- **Repair, part 2**: for `D ≥ 4` and `T = (125/2)D + 200`,
`(0.566 log 1.35·10⁸ + 1.41)√T ≤ 127.4√D`. -/
theorem kappa_fix_p2 {D : ℝ} (hD : 4 ≤ D) :
    (0.566 * log 1.35e8 + 1.41) * √(125 / 2 * D + 200) ≤ 127.4 * √D := by
  have h := logB_lt; have h0 := logB_gt
  have hT : √(125 / 2 * D + 200) ≤ √(125 / 2 + 50) * √D := by
    rw [← sqrt_mul (by norm_num)]; exact sqrt_le_sqrt (by nlinarith)
  have s : √(125 / 2 + 50 : ℝ) < 10.6066018 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have sD := sqrt_nonneg D
  have sT := sqrt_nonneg (125 / 2 + 50 : ℝ)
  have hc : 0 ≤ 0.566 * log 1.35e8 + 1.41 := by linarith
  calc (0.566 * log 1.35e8 + 1.41) * √(125 / 2 * D + 200)
      ≤ (0.566 * log 1.35e8 + 1.41) * (√(125 / 2 + 50) * √D) :=
        mul_le_mul_of_nonneg_left hT hc
    _ ≤ 127.4 * √D := by nlinarith [mul_nonneg sT sD]

/-- **The `log q` terms of part 1, `1 ≤ q ≤ 400000`**: `0.84 log q + 11.52 ≤ 22.4`,
`6.1 log q · 6 ≤ 473`, `6.1 log q · 2 ≤ 158`, MATCH. -/
theorem logq_p1 {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 400000) :
    0.84 * log q + 11.52 ≤ 22.4 ∧ 6.1 * log q * 6 ≤ 473 ∧ 6.1 * log q * 2 ≤ 158 := by
  have h : log q ≤ log 400000 := log_le_log (by linarith) hq
  have := log4e5_lt
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **The `log q` terms of part 2, `1 ≤ q ≤ 300000`**: `22.2`, `462`, `154`, MATCH. -/
theorem logq_p2 {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000) :
    0.84 * log q + 11.52 ≤ 22.2 ∧ 6.1 * log q * 6 ≤ 462 ∧ 6.1 * log q * 2 ≤ 154 := by
  have h : log q ≤ log 300000 := log_le_log (by linarith) hq
  have := log3e5_lt
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **Last step of part 1**: for `x ≥ 10⁶`, `1 ≤ q ≤ 400000`, `d = |δ| ≥ 0` and any `A`,
`(A + 22.4)√x + 1.6d + 1.1 + (6.1 log q)(6 + 2d)/√x ≤ (A + 22.5)√x + 2d`, MATCH. -/
theorem final_p1 {x q d A : ℝ} (hx : 1e6 ≤ x) (hq1 : 1 ≤ q) (hq : q ≤ 400000) (hd : 0 ≤ d) :
    (A + 22.4) * √x + (1.6 * d + 1.1) + 6.1 * log q * (6 + 2 * d) / √x ≤
      (A + 22.5) * √x + 2 * d := by
  have hl : log q ≤ log 400000 := log_le_log (by linarith) hq
  have hl0 : 0 ≤ log q := log_nonneg hq1
  have := log4e5_lt
  have hs := sqrt_1e6 hx
  have hB : 6.1 * log q * (6 + 2 * d) ≤ 473 + 158 * d := by nlinarith
  have hfrac : 6.1 * log q * (6 + 2 * d) / √x ≤ (473 + 158 * d) / 1000 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have h0 : 0 ≤ 6.1 * log q * (6 + 2 * d) := by positivity
    nlinarith
  have : (473 + 158 * d) / 1000 = 0.473 + 0.158 * d := by ring
  nlinarith

/-- **Last step of part 2**: for `x ≥ 10⁶`, `1 ≤ q ≤ 300000`, `d ≥ 0` and any `A`,
`(A + 22.2)√x + 1.6d + 1.1 + (6.1 log q)(6 + 2d)/√x ≤ (A + 22.3)√x + 2d`, MATCH. -/
theorem final_p2 {x q d A : ℝ} (hx : 1e6 ≤ x) (hq1 : 1 ≤ q) (hq : q ≤ 300000) (hd : 0 ≤ d) :
    (A + 22.2) * √x + (1.6 * d + 1.1) + 6.1 * log q * (6 + 2 * d) / √x ≤
      (A + 22.3) * √x + 2 * d := by
  have hl : log q ≤ log 300000 := log_le_log (by linarith) hq
  have hl0 : 0 ≤ log q := log_nonneg hq1
  have := log3e5_lt
  have hs := sqrt_1e6 hx
  have hB : 6.1 * log q * (6 + 2 * d) ≤ 462 + 154 * d := by nlinarith
  have hfrac : 6.1 * log q * (6 + 2 * d) / √x ≤ (462 + 154 * d) / 1000 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have h0 : 0 ≤ 6.1 * log q * (6 + 2 * d) := by positivity
    nlinarith
  have : (462 + 154 * d) / 1000 = 0.462 + 0.154 * d := by ring
  nlinarith

end LeanLab.HelfgottMajor.BookT143
