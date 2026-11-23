module

public import Mathlib

/-!
# Helfgott's book, Part IV of 2020-04-01, proofs of Theorems 14.1 and 14.2: the arithmetic

Unit U-6716, CLOUD 20261020T1914Z-cloud49, P0014. AI wrote this file.

Source: book pages 446 to 448, copy papers/P0014-book-PartIV.pdf, page images checked. Here
`r = c · 10⁵`, `c ∈ {3, 4}`, `q ≤ r`, `T = max(250|δ|/c, 1000/c)`, so `qT ≤ 10⁸`, and
`r₀ = 125/(2π²c)`, so `1/√r₀ = π√(2c/125)`.

* `lead_c3`, `lead_c4`: `1.14 π√(2c/125) e^{-y} ≤ 1.94863·10⁻³⁰`, `≤ 7.5519·10⁻¹⁹` for every
  `y ≥ 68.16791`, `y ≥ 41.62864`: CONDITIONAL ON `E(r₀)·1000/c ≥ 68.16791`, `41.62864`, the
  values of the book's `E` at `r₀`, recomputed as 68.1679125 and 41.6286432 in
  gen/book_t141_142_U6716.py but not proved in Lean;
* `exp_pi_T`: `e^{-(π/4)·250} ≤ 5.33·10⁻⁸⁶`;
* `eps_141`, `eps_142`: `ε₃ = 3.231375·10⁻²⁹`, `ε₄ = 1.25232·10⁻¹⁷` of Thm. 14.1 and
  `9.6942·10⁻²⁹`, `3.75696·10⁻¹⁷` of Thm. 14.2, from `log(10⁸/2π) < 16.582804`;
* `kappa_141`, `kappa_142`: `κ₃ = 279.34`, `κ₄ = 241.91`, `κ₃ = 114.53`, `κ₄ = 99.19`;
* `logq_terms`: `42.5`, `91.2`, `11.4`, `24.8`, `87.4`, `20.9` for `q ≤ 400000`;
* `const_gap`: `1.1 log 400000 + 2 > 14.2`, so the printed `1.1 log q + 5.6|δ| + 2 ≤
  5.6|δ| + 14.2` fails for large `q`, true value 16.19, see QUESTION in PROGRESS.md;
* `final_141`, `final_142`: the last steps of both proofs for `x ≥ 10⁶` and `1 ≤ q ≤ 400000`,
  `ε x + (A + 43)√x + 6|δ|` and `ε x + (A + 25)√x + 3|δ|`, PROVED with the true 16.19, so
  Theorem 14.1's statement SURVIVES.

Ternary Goldbach is a theorem; binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-20.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.BookT141
open Real Finset

lemma pi_bds : 3.14159265358 < π ∧ π < 3.14159265359 := by
  constructor
  · have := pi_gt_d20; linarith
  · have := pi_lt_d20; linarith

/-- `e^k · Σ_{i<n} rⁱ/i! ≤ exp(k + r)` for `r ≥ 0`, with `e ≥ 2.7182818283`. -/
lemma exp_lower (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    2.7182818283 ^ k * ∑ i ∈ range n, r ^ i / i.factorial ≤ exp (k + r) := by
  rw [exp_add]
  have h1 : (2.7182818283 : ℝ) ^ k ≤ exp k := by
    rw [← exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le k
  have h2 := sum_le_exp_of_nonneg hr n
  have h0 : 0 ≤ ∑ i ∈ range n, r ^ i / i.factorial := sum_nonneg (fun i _ => by positivity)
  exact mul_le_mul h1 h2 h0 (exp_pos _).le

/-- `log 10 < 2.3025851`, via `10 ≤ exp 2.3025851`. -/
lemma log10_lt : log 10 < 2.3025851 := by
  rw [log_lt_iff_lt_exp (by norm_num)]
  have h := exp_lower 2 (r := 0.3025851) (by norm_num) 10
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢
  linarith

/-- `log π > 1.1447298`, via `exp 1.1447298 < π`. -/
lemma log_pi_gt : 1.1447298 < log π := by
  rw [lt_log_iff_exp_lt pi_pos]
  have e : exp (1.1447298 : ℝ) = exp 1 * exp 0.1447298 := by rw [← exp_add]; norm_num
  have h1 := exp_one_lt_d9
  have h2 := exp_bound' (x := (0.1447298 : ℝ)) (by norm_num) (by norm_num) (n := 7) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have := pi_bds.1
  rw [e]; nlinarith [exp_pos (0.1447298 : ℝ), exp_pos 1]

/-- **`log(10⁸/2π) < 16.582804`**; value 16.5828037. -/
lemma LQ_lt : log (1e8 / (2 * π)) < 16.582804 := by
  rw [log_div (by norm_num) (by positivity), log_mul (by norm_num) pi_pos.ne',
    show (1e8 : ℝ) = 10 ^ 8 by norm_num, log_pow]
  have := log10_lt; have := log_pi_gt; have := log_two_gt_d9
  push_cast; linarith

lemma LQ_pos : 0 < log (1e8 / (2 * π)) := by
  apply log_pos; rw [one_lt_div (by positivity)]; have := pi_bds.2; linarith

/-- **Thm. 14.1, `c = 3`, `r ≥ r₀`**: `1.14/√r₀ · e^{-y} ≤ 1.94863·10⁻³⁰` for `y ≥ 68.16791`;
`0.44 ≤ 1.14/√r₀`, so the `max` is the second term. CONDITIONAL ON `E(r₀)·1000/3 ≥ 68.16791`,
which is where it is applied. -/
theorem lead_c3 {y : ℝ} (hy : 68.16791 ≤ y) :
    0.44 ≤ 1.14 * (π * √(6 / 125)) ∧ 1.14 * (π * √(6 / 125)) * exp (-y) ≤ 1.94863e-30 := by
  obtain ⟨p1, p2⟩ := pi_bds
  have hs1 : √(6 / 125) < 0.2190890231 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0.219 < √(6 / 125) := by rw [lt_sqrt (by norm_num)]; norm_num
  refine ⟨by nlinarith, ?_⟩
  have he : (4.02668e29 : ℝ) ≤ exp 68.16791 := by
    have h := exp_lower 68 (r := 0.16791) (by norm_num) 8
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hmono : exp (-y) ≤ (exp 68.16791)⁻¹ := by
    rw [← exp_neg]; exact exp_le_exp.mpr (by linarith)
  have hinv : (exp 68.16791)⁻¹ ≤ 1 / 4.02668e29 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) he
  have hk : 1.14 * (π * √(6 / 125)) ≤ 0.78464886 := by nlinarith
  have hk0 : 0 ≤ 1.14 * (π * √(6 / 125)) := by positivity
  calc 1.14 * (π * √(6 / 125)) * exp (-y) ≤ 0.78464886 * (1 / 4.02668e29) :=
        mul_le_mul hk (hmono.trans hinv) (exp_pos _).le (by norm_num)
    _ ≤ 1.94863e-30 := by norm_num

/-- **Thm. 14.1, `c = 4`, `r ≥ r₀`**: `1.14/√r₀ · e^{-y} ≤ 7.5519·10⁻¹⁹` for `y ≥ 41.62864`.
CONDITIONAL ON `E(r₀)·1000/4 ≥ 41.62864` where applied. -/
theorem lead_c4 {y : ℝ} (hy : 41.62864 ≤ y) :
    0.44 ≤ 1.14 * (π * √(8 / 125)) ∧ 1.14 * (π * √(8 / 125)) * exp (-y) ≤ 7.5519e-19 := by
  obtain ⟨p1, p2⟩ := pi_bds
  have hs1 : √(8 / 125) < 0.2529822129 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0.25 < √(8 / 125) := by rw [lt_sqrt (by norm_num)]; norm_num
  refine ⟨by nlinarith, ?_⟩
  have he : (1.1997438e18 : ℝ) ≤ exp 41.62864 := by
    have h := exp_lower 41 (r := 0.62864) (by norm_num) 12
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  have hmono : exp (-y) ≤ (exp 41.62864)⁻¹ := by
    rw [← exp_neg]; exact exp_le_exp.mpr (by linarith)
  have hinv : (exp 41.62864)⁻¹ ≤ 1 / 1.1997438e18 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) he
  have hk : 1.14 * (π * √(8 / 125)) ≤ 0.906034451 := by nlinarith
  have hk0 : 0 ≤ 1.14 * (π * √(8 / 125)) := by positivity
  calc 1.14 * (π * √(8 / 125)) * exp (-y) ≤ 0.906034451 * (1 / 1.1997438e18) :=
        mul_le_mul hk (hmono.trans hinv) (exp_pos _).le (by norm_num)
    _ ≤ 7.5519e-19 := by norm_num

/-- **`e^{-(π/4)T} ≤ e^{-(π/4)·250} ≤ 5.33·10⁻⁸⁶`** for `T ≥ 250`, book p. 447. -/
theorem exp_pi_T {T : ℝ} (hT : 250 ≤ T) : exp (-(π / 4) * T) ≤ 5.33e-86 := by
  obtain ⟨p1, p2⟩ := pi_bds
  have hmono : exp (-(π / 4) * T) ≤ (exp (196 + 0.3495408))⁻¹ := by
    rw [← exp_neg]; exact exp_le_exp.mpr (by nlinarith)
  have he : (1.8765e85 : ℝ) ≤ exp (196 + 0.3495408) := by
    have h1 : (2.71828 : ℝ) ^ 196 ≤ exp 196 := by
      rw [show (196 : ℝ) = ((196 : ℕ) : ℝ) by norm_num, ← exp_one_pow]
      exact pow_le_pow_left₀ (by norm_num) (by have := exp_one_gt_d9; linarith) 196
    have h2 := sum_le_exp_of_nonneg (x := (0.3495408 : ℝ)) (by norm_num) 6
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h2
    norm_num at h2
    rw [exp_add]
    have : (1.8765e85 : ℝ) ≤ 2.71828 ^ 196 * 1.4183 := by norm_num
    have h3 : (1.4183 : ℝ) ≤ exp 0.3495408 := by linarith
    nlinarith [exp_pos (196 : ℝ), exp_pos (0.3495408 : ℝ)]
  have hinv : (exp (196 + 0.3495408))⁻¹ ≤ 1 / 1.8765e85 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) he
  calc exp (-(π / 4) * T) ≤ 1 / 1.8765e85 := hmono.trans hinv
    _ ≤ 5.33e-86 := by norm_num

/-- **`ε_c` of Theorem 14.1**: `(1.94863·10⁻³⁰ + 1.18·10⁻⁸⁶) log(10⁸/2π) ≤ 3.231375·10⁻²⁹`,
`(7.5519·10⁻¹⁹ + 1.18·10⁻⁸⁶) log(10⁸/2π) ≤ 1.25232·10⁻¹⁷`, with `0.22 · 5.33·10⁻⁸⁶ ≤
1.18·10⁻⁸⁶`, and the statement's `3.24·10⁻²⁹`, `1.26·10⁻¹⁷`. -/
theorem eps_141 :
    (0.22 : ℝ) * 5.33e-86 ≤ 1.18e-86 ∧
    (1.94863e-30 + 1.18e-86) * log (1e8 / (2 * π)) ≤ 3.231375e-29 ∧
    (7.5519e-19 + 1.18e-86) * log (1e8 / (2 * π)) ≤ 1.25232e-17 ∧
    (3.231375e-29 : ℝ) ≤ 3.24e-29 ∧ (1.25232e-17 : ℝ) ≤ 1.26e-17 := by
  have h := LQ_lt.le
  refine ⟨by norm_num, ?_, ?_, by norm_num, by norm_num⟩
  · calc _ ≤ (1.94863e-30 + 1.18e-86) * 16.582804 := mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ _ := by norm_num
  · calc _ ≤ (7.5519e-19 + 1.18e-86) * 16.582804 := mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ _ := by norm_num

/-- **`ε_c` of Theorem 14.2**: `3 · 1.94863·10⁻³⁰ ≤ 5.84589·10⁻³⁰`, `3 · 7.5519·10⁻¹⁹ ≤
2.26557·10⁻¹⁸`, `0.88 · 5.33·10⁻⁸⁶ ≤ 4.72·10⁻⁸⁶`, then `≤ 9.6942·10⁻²⁹`, `≤ 3.75696·10⁻¹⁷` and
the statement's `9.7·10⁻²⁹`, `3.76·10⁻¹⁷`. -/
theorem eps_142 :
    (3 : ℝ) * 1.94863e-30 ≤ 5.84589e-30 ∧ (3 : ℝ) * 7.5519e-19 ≤ 2.26557e-18 ∧
    (0.88 : ℝ) * 5.33e-86 ≤ 4.72e-86 ∧
    (5.84589e-30 + 4.72e-86) * log (1e8 / (2 * π)) ≤ 9.6942e-29 ∧
    (2.26557e-18 + 4.72e-86) * log (1e8 / (2 * π)) ≤ 3.75696e-17 ∧
    (9.6942e-29 : ℝ) ≤ 9.7e-29 ∧ (3.75696e-17 : ℝ) ≤ 3.76e-17 := by
  have h := LQ_lt.le
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num, by norm_num⟩
  · calc _ ≤ (5.84589e-30 + 4.72e-86) * 16.582804 := mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ _ := by norm_num
  · calc _ ≤ (2.26557e-18 + 4.72e-86) * 16.582804 := mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ _ := by norm_num

lemma log1e8_lt : log 1e8 < 18.4206808 := by
  rw [show (1e8 : ℝ) = 10 ^ 8 by norm_num, log_pow]; have := log10_lt; push_cast; linarith

lemma log1e8_pos : 0 < log 1e8 := log_pos (by norm_num)

/-- **`κ_c` of Theorem 14.1**: `(1.02 log 10⁸ + 11.81)√(250/c) ≤ 279.34, 241.91`, and the
statement's `280`, `242`. -/
theorem kappa_141 :
    (1.02 * log 1e8 + 11.81) * √(250 / 3) ≤ 279.34 ∧
    (1.02 * log 1e8 + 11.81) * √(250 / 4) ≤ 241.91 ∧ (279.34 : ℝ) ≤ 280 ∧ (241.91 : ℝ) ≤ 242 := by
  have h := log1e8_lt; have h0 := log1e8_pos
  have s3 : √(250 / 3) < 9.1287093 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have s4 : √(250 / 4) < 7.9056942 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have s30 := sqrt_nonneg (250 / 3 : ℝ); have s40 := sqrt_nonneg (250 / 4 : ℝ)
  refine ⟨by nlinarith, by nlinarith, by norm_num, by norm_num⟩

/-- **`κ_c` of Theorem 14.2**: `(0.56 log 10⁸ + 2.23)√(250/c) ≤ 114.53, 99.19`, and the
statement's `115`, `100`. -/
theorem kappa_142 :
    (0.56 * log 1e8 + 2.23) * √(250 / 3) ≤ 114.53 ∧
    (0.56 * log 1e8 + 2.23) * √(250 / 4) ≤ 99.19 ∧ (114.53 : ℝ) ≤ 115 ∧ (99.19 : ℝ) ≤ 100 := by
  have h := log1e8_lt; have h0 := log1e8_pos
  have s3 : √(250 / 3) < 9.1287093 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have s4 : √(250 / 4) < 7.9056942 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have s30 := sqrt_nonneg (250 / 3 : ℝ); have s40 := sqrt_nonneg (250 / 4 : ℝ)
  refine ⟨by nlinarith, by nlinarith, by norm_num, by norm_num⟩

/-- `log 400000 = 2 log 2 + 5 log 10 < 12.8992201`; value 12.8992198. -/
lemma log4e5_lt : log 400000 < 12.8992201 := by
  rw [show (400000 : ℝ) = 2 ^ 2 * 10 ^ 5 by norm_num, log_mul (by norm_num) (by norm_num),
    log_pow, log_pow]
  have := log10_lt; have := log_two_lt_d9; push_cast; linarith

/-- **The `log q` terms, `1 ≤ q ≤ 400000`**: `1.6 log q + 21.8 ≤ 42.5`,
`(log q + 6.1) · 4.8 ≤ 91.2`, `· 0.6 ≤ 11.4`, `0.93 log q + 12.8 ≤ 24.8`, `· 4.6 ≤ 87.4`,
`· 1.1 ≤ 20.9`, MATCH. -/
theorem logq_terms {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 400000) :
    1.6 * log q + 21.8 ≤ 42.5 ∧ (log q + 6.1) * 4.8 ≤ 91.2 ∧ (log q + 6.1) * 0.6 ≤ 11.4 ∧
    0.93 * log q + 12.8 ≤ 24.8 ∧ (log q + 6.1) * 4.6 ≤ 87.4 ∧ (log q + 6.1) * 1.1 ≤ 20.9 := by
  have h : log q ≤ log 400000 := log_le_log (by linarith) hq
  have := log4e5_lt
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **The printed `1.1 log q + 2 ≤ 14.2` fails at `q = 400000`**: `1.1 log 400000 + 2 > 14.2`,
true value 16.189. It holds only for `q ≤ e^{12.2/1.1} ≈ 65700`. -/
theorem const_gap : 14.2 < 1.1 * log 400000 + 2 := by
  have h8 : log 8 ≤ log 10 := log_le_log (by norm_num) (by norm_num)
  have e8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; push_cast; ring
  rw [show (400000 : ℝ) = 2 ^ 2 * 10 ^ 5 by norm_num, log_mul (by norm_num) (by norm_num),
    log_pow, log_pow]
  have := log_two_gt_d9; push_cast; linarith

/-- **Last step of the proof of Theorem 14.1**, with the true constant `1.1 log q + 2 ≤ 16.19`:
for `x ≥ 10⁶`, `1 ≤ q ≤ 400000`, `d = |δ| ≥ 0` and any `A`, `(A + 42.5)√x +
(1.1 log q + 5.6 d + 2) + (log q + 6.1)(0.6 + 4.8 d)/√x ≤ (A + 43)√x + 6 d`, so Theorem 14.1's
bound survives the slip of `const_gap`. -/
theorem final_141 {x q d A : ℝ} (hx : 1e6 ≤ x) (hq1 : 1 ≤ q) (hq : q ≤ 400000) (hd : 0 ≤ d) :
    (A + 42.5) * √x + (1.1 * log q + 5.6 * d + 2) + (log q + 6.1) * (0.6 + 4.8 * d) / √x ≤
      (A + 43) * √x + 6 * d := by
  have hl : log q ≤ log 400000 := log_le_log (by linarith) hq
  have hl0 : 0 ≤ log q := log_nonneg hq1
  have := log4e5_lt
  have hs : 1000 ≤ √x := by
    rw [show (1000 : ℝ) = √(1e6) by rw [show (1e6 : ℝ) = 1000 ^ 2 by norm_num,
      sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hx
  have hB : (log q + 6.1) * (0.6 + 4.8 * d) ≤ 11.4 + 91.2 * d := by nlinarith
  have hfrac : (log q + 6.1) * (0.6 + 4.8 * d) / √x ≤ (11.4 + 91.2 * d) / 1000 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have h0 : 0 ≤ (log q + 6.1) * (0.6 + 4.8 * d) := by positivity
    nlinarith
  have : (11.4 + 91.2 * d) / 1000 = 0.0114 + 0.0912 * d := by ring
  nlinarith

/-- **Last step of the proof of Theorem 14.2**: for `x ≥ 10⁶`, `d ≥ 0` and any `A`,
`(A + 24.8)√x + (2.7 d + 1.2) + (87.4 d + 20.9)/√x ≤ (A + 25)√x + 3 d`, MATCH. -/
theorem final_142 {x d A : ℝ} (hx : 1e6 ≤ x) (hd : 0 ≤ d) :
    (A + 24.8) * √x + (2.7 * d + 1.2) + (87.4 * d + 20.9) / √x ≤ (A + 25) * √x + 3 * d := by
  have hs : 1000 ≤ √x := by
    rw [show (1000 : ℝ) = √(1e6) by rw [show (1e6 : ℝ) = 1000 ^ 2 by norm_num,
      sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hx
  have hfrac : (87.4 * d + 20.9) / √x ≤ (87.4 * d + 20.9) / 1000 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have h0 : 0 ≤ 87.4 * d + 20.9 := by positivity
    nlinarith
  have : (87.4 * d + 20.9) / 1000 = 0.0874 * d + 0.0209 := by ring
  nlinarith

end LeanLab.HelfgottMajor.BookT141
