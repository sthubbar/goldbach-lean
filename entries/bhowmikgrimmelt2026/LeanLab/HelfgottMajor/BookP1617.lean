module

public import Mathlib

/-!
# Helfgott's book, Part IV of 2020-04-01, Lemmas 16.15 and 16.16, Props. 16.17 and 16.18:
# the arithmetic of their constants

Unit U-6716, CLOUD 20261020T1914Z-cloud49, P0014. AI wrote this file.

Source: book pages 439 to 443, copy papers/P0014-book-PartIV.pdf, page images checked. The
constants of Prop. 16.11 are, by (16.29) to (16.31),
`c₂ = |η|₂/√π + 0.3√π |η log|₂`, `c₁ = 6.484√π |η log|₂ - (log 2π√e/√π) |η|₂`,
`c_{1/2} = (0.919 log q + 12.653) |η/√t|₁`, `c₀ = (4/3) η(0) log q + 1.349 η(0) + |η'_δ log|₁`,
`c₋ = (log q + 6.083) |η'_δ|₂`. We write `π^{1/4}` as `√√π`.

Gaussian `η = √(2/π) e^{-t²/2}`, Prop. 16.17, `|η|₂ = π^{-1/4}` exact:
* `gauss_c2`, `gauss_c1`: `c₂ ≤ 1.01586`, `c₁ ≤ 11.80604` from `|η log|₂ ≤ 1.11348`;
* `gauss_chalf`, `gauss_c0`, `gauss_cminus`: `1.58076 log q + 21.76418`, `1.06385`,
  `1.47674`, `0.53113`, `4.71947`, `5.52475`;
* `gauss_eps_plus`, `gauss_eps_minus`, `gauss_eps_round`: the `ε_{T,q,f}` coefficients `0.43`,
  `0.39`, `1.124`, `0.77`, `0.214`, `0.196` for `T ≥ 40`, and `0.435`, `1.134`, `0.22`.

Part III smoothing `η = √(2/π)·2(e^{-t²/2} - e^{-2t²})`, Lemma 16.16 and Prop. 16.18:
* `p3_norm2`, `p3_norm2_deriv`: the closed forms `≤ 0.72839` and `≤ 1.04951`;
* `p3_c2`: `c₂ ≤ 0.55817`;
* `p3_c1_printed`: `6.484√π·0.27686 - (log 2π√e/√π)·0.72839 ≤ 2.22109`, the book's arithmetic;
* `p3_c1_gap`: with the exact `|η|₂` and `|η log|₂ ≤ 0.27686` alone, the expression is
  `> 2.22109`: the upper bound `0.72839` sits in a subtracted term, see QUESTION in PROGRESS.md;
* `p3_c1_true`: `c₁ ≤ 2.22109` CONDITIONAL ON `|η log|₂ ≤ 0.276856`, which the script
  gen/book_c1614_1618_U6716.py gives as `0.2768557588`; so the printed constant holds.

Ternary Goldbach is a theorem; binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-20.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.BookP1617
open Real Finset

/-! ### Numerical bounds -/

lemma pi_bds : 3.14159265358 < π ∧ π < 3.14159265359 := by
  constructor
  · have := pi_gt_d20; linarith
  · have := pi_lt_d20; linarith

lemma s_bds : 1.7724538509 < √π ∧ √π < 1.7724538510 := by
  obtain ⟨h1, h2⟩ := pi_bds
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; linarith
  · rw [Real.sqrt_lt' (by norm_num)]; linarith

lemma w_bds : 1.3313353637 < √√π ∧ √√π < 1.3313353639 := by
  obtain ⟨h1, h2⟩ := s_bds
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; linarith
  · rw [Real.sqrt_lt' (by norm_num)]; linarith

lemma c_bds : 0.7978845608 < √(2 / π) ∧ √(2 / π) < 0.7978845609 := by
  obtain ⟨h1, h2⟩ := pi_bds
  have hp : 0 < π := pi_pos
  constructor
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ hp]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ hp]; nlinarith

lemma sqrt2_bds : 1.4142135623 < √2 ∧ √2 < 1.4142135624 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `log π > 1.1447298`, via `exp 1.1447298 < π`. -/
lemma log_pi_gt : 1.1447298 < log π := by
  rw [Real.lt_log_iff_exp_lt pi_pos]
  have e : exp (1.1447298 : ℝ) = exp 1 * exp 0.1447298 := by rw [← exp_add]; norm_num
  have h1 := exp_one_lt_d9
  have h2 := Real.exp_bound' (x := (0.1447298 : ℝ)) (by norm_num) (by norm_num) (n := 7) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have := pi_bds.1
  rw [e]; nlinarith [exp_pos (0.1447298 : ℝ), exp_pos 1]

/-- `log π < 1.1447299`, via `π < exp 1.1447299`. -/
lemma log_pi_lt : log π < 1.1447299 := by
  rw [Real.log_lt_iff_lt_exp pi_pos]
  have e : exp (1.1447299 : ℝ) = exp 1 * exp 0.1447299 := by rw [← exp_add]; norm_num
  have h1 := exp_one_gt_d9
  have h2 := sum_le_exp_of_nonneg (x := (0.1447299 : ℝ)) (by norm_num) 8
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have := pi_bds.2
  rw [e]; nlinarith [exp_pos (0.1447299 : ℝ), exp_pos 1]

/-- `log (2π√e) = log 2 + log π + 1/2 ∈ (2.3378769, 2.3378771)`; value 2.3378770664. -/
lemma K_bds : 2.3378769 < log (2 * π * √(exp 1)) ∧ log (2 * π * √(exp 1)) < 2.3378771 := by
  rw [log_mul (by positivity) (by positivity), Real.log_sqrt (exp_pos 1).le, log_exp,
    log_mul (by norm_num) (by positivity)]
  have := log_pi_gt; have := log_pi_lt; have := log_two_gt_d9; have := log_two_lt_d9
  constructor <;> linarith

/-! ### Prop. 16.17, the Gaussian -/

/-- **`c₂ = π^{-1/4}/√π + 0.3√π · 1.11348 ≤ 1.01586`**, MATCH, 1.0158548. -/
theorem gauss_c2 : (1 / √√π) / √π + 0.3 * √π * 1.11348 ≤ 1.01586 := by
  obtain ⟨s1, s2⟩ := s_bds; obtain ⟨w1, w2⟩ := w_bds
  have h : (1 / √√π) / √π ≤ 0.4237773 := by
    rw [div_div, div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- **`c₁ = 6.484√π · 1.11348 - (log 2π√e/√π) π^{-1/4} ≤ 11.80604`**, MATCH, 11.8060310. -/
theorem gauss_c1 :
    6.484 * √π * 1.11348 - log (2 * π * √(exp 1)) / √π * (1 / √√π) ≤ 11.80604 := by
  obtain ⟨s1, s2⟩ := s_bds; obtain ⟨w1, w2⟩ := w_bds; obtain ⟨k1, k2⟩ := K_bds
  have h : 0.990738 ≤ log (2 * π * √(exp 1)) / √π * (1 / √√π) := by
    rw [div_mul_div_comm, mul_one, le_div_iff₀ (by positivity)]; nlinarith
  linarith

/-- **`c_{1/2} ≤ 1.58076 log q + 21.76418`**: `0.919 · 1.72008` and `12.653 · 1.72008`, MATCH. -/
theorem gauss_chalf : (0.919 : ℝ) * 1.72008 ≤ 1.58076 ∧ (12.653 : ℝ) * 1.72008 ≤ 21.76418 := by
  norm_num

/-- **`c₀`**: `(4/3)√(2/π) ≤ 1.06385`, `1.349√(2/π) + 0.40039 ≤ 1.47674`, and for `q = 1`
`√(2/π) log 2π ≤ 1.47674`, MATCH. -/
theorem gauss_c0 : 4 / 3 * √(2 / π) ≤ 1.06385 ∧ 1.349 * √(2 / π) + 0.40039 ≤ 1.47674 ∧
    √(2 / π) * log (2 * π) ≤ 1.47674 := by
  obtain ⟨c1, c2⟩ := c_bds
  refine ⟨by linarith, by linarith, ?_⟩
  have : log (2 * π) < 1.838 := by
    rw [log_mul (by norm_num) (by positivity)]
    have := log_pi_lt; have := log_two_lt_d9; linarith
  have h0 : 0 ≤ log (2 * π) := log_nonneg (by have := pi_bds.1; linarith)
  nlinarith

/-- **`c₋`**: `1/(√2 π^{1/4}) ≤ 0.53113`, `2π^{3/4} = 2√π π^{1/4} ≤ 4.71947`,
`2π · 0.87929 ≤ 5.52475`, MATCH. -/
theorem gauss_cminus : 1 / (√2 * √√π) ≤ 0.53113 ∧ 2 * √π * √√π ≤ 4.71947 ∧
    2 * π * 0.87929 ≤ 5.52475 := by
  obtain ⟨s1, s2⟩ := s_bds; obtain ⟨w1, w2⟩ := w_bds; obtain ⟨r1, r2⟩ := sqrt2_bds
  obtain ⟨p1, p2⟩ := pi_bds
  refine ⟨?_, by nlinarith, by nlinarith⟩
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- **`ε_{T,q,f}`, the part from `f(t)`**, book p. 442: with `c₀ = 5.6`, `T ≥ 40` and the
constants `5.927`, `5.6`, `15.527`, `11.2` of (16.35) and (16.36):
`√(2/π)/(4π) · 5.927 (1 + 5.6/T) ≤ 0.43`, `0.075√(2/π) · 5.6 (1 + 5.6/T) ≤ 0.39`,
`√(2/π)/(4π) · 15.527 (1 + 5.6/T) ≤ 1.124`, `0.075√(2/π) · 11.2 (1 + 5.6/T) ≤ 0.77`. -/
theorem gauss_eps_plus {T : ℝ} (hT : 40 ≤ T) :
    √(2 / π) / (4 * π) * 5.927 * (1 + 5.6 / T) ≤ 0.43 ∧
    0.075 * √(2 / π) * 5.6 * (1 + 5.6 / T) ≤ 0.39 ∧
    √(2 / π) / (4 * π) * 15.527 * (1 + 5.6 / T) ≤ 1.124 ∧
    0.075 * √(2 / π) * 11.2 * (1 + 5.6 / T) ≤ 0.77 := by
  obtain ⟨c1, c2⟩ := c_bds; obtain ⟨p1, p2⟩ := pi_bds
  have hf : 1 + 5.6 / T ≤ 1.14 := by
    have : 5.6 / T ≤ 0.14 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hf0 : 0 ≤ 1 + 5.6 / T := by have : 0 ≤ 5.6 / T := by positivity
                                   linarith
  have hk : √(2 / π) / (4 * π) ≤ 0.0634937 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hk0 : 0 ≤ √(2 / π) / (4 * π) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **`ε_{T,q,f}`, the part from `f(-t)`**, book p. 442, from (16.32) and (16.33) with
`f(-t) = √(2/π) · 2.56 e^{-πt/4}`: `√(2/π)/(4π) · 2.56/(π/4 - 1/T) ≤ 0.214` and
`0.075 √(2/π) · 2.56/(π/4) ≤ 0.196` for `T ≥ 40`. -/
theorem gauss_eps_minus {T : ℝ} (hT : 40 ≤ T) :
    √(2 / π) / (4 * π) * 2.56 / (π / 4 - 1 / T) ≤ 0.214 ∧
    0.075 * √(2 / π) * 2.56 / (π / 4) ≤ 0.196 := by
  obtain ⟨c1, c2⟩ := c_bds; obtain ⟨p1, p2⟩ := pi_bds
  have hk : √(2 / π) / (4 * π) ≤ 0.0634937 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hT1 : 1 / T ≤ 1 / 40 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hd : 0.76 ≤ π / 4 - 1 / T := by linarith
  constructor
  · rw [div_le_iff₀ (by linarith)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

/-- **The rounding steps of p. 442**, with `L = log(qT/2π) ≥ 2` and `T ≥ 40`:
`0.43L + 0.39/T ≤ 0.435L`, `1.124L + 0.77/T ≤ 1.134L`, `0.214L + 0.196/T ≤ 0.22L`. -/
theorem gauss_eps_round {L T : ℝ} (hL : 2 ≤ L) (hT : 40 ≤ T) :
    0.43 * L + 0.39 / T ≤ 0.435 * L ∧ 1.124 * L + 0.77 / T ≤ 1.134 * L ∧
    0.214 * L + 0.196 / T ≤ 0.22 * L := by
  have h1 : 0.39 / T ≤ 0.00975 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : 0.77 / T ≤ 0.01925 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h3 : 0.196 / T ≤ 0.0049 := by rw [div_le_iff₀ (by linarith)]; linarith
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **(16.55) rounds the proof's constants up.** -/
theorem gauss_final_round :
    (0.435 : ℝ) ≤ 0.44 ∧ (1.134 : ℝ) ≤ 1.14 ∧ (1.01586 : ℝ) ≤ 1.02 ∧ (11.80604 : ℝ) ≤ 11.81 ∧
    (1.58076 : ℝ) ≤ 1.6 ∧ (21.76418 : ℝ) ≤ 21.8 ∧ (1.06385 : ℝ) ≤ 1.1 ∧ (5.52476 : ℝ) ≤ 5.6 ∧
    (1.47674 : ℝ) ≤ 2 ∧ (6.083 : ℝ) ≤ 6.1 ∧ (0.53113 : ℝ) ≤ 0.6 ∧ (4.71947 : ℝ) ≤ 4.8 := by
  norm_num

/-! ### Lemma 16.16 and Prop. 16.18, the Part III smoothing -/

lemma sqrt25_bds : 0.6324555320 < √(2 / 5) ∧ √(2 / 5) < 0.6324555321 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma sqrt10_bds : 3.1622776601 < √10 ∧ √10 < 3.1622776602 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma in46_bds : 0.9697194144 < √(6 - 8 * √(2 / 5)) ∧ √(6 - 8 * √(2 / 5)) < 0.9697194154 := by
  obtain ⟨a1, a2⟩ := sqrt25_bds
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith

lemma in47_bds : 1.3972417806 < √(6 - 32 / 25 * √10) ∧ √(6 - 32 / 25 * √10) < 1.3972417816 := by
  obtain ⟨a1, a2⟩ := sqrt10_bds
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num)]; nlinarith

/-- `|η|₂ = √(6 - 8√(2/5))/π^{1/4} ∈ (0.72838, 0.7283811)`; (16.46) prints `≤ 0.72839`. -/
theorem p3_norm2 : 0.72838 < √(6 - 8 * √(2 / 5)) / √√π ∧
    √(6 - 8 * √(2 / 5)) / √√π < 0.7283811 := by
  obtain ⟨a1, a2⟩ := in46_bds; obtain ⟨w1, w2⟩ := w_bds
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- **(16.47)**: `|η'|₂ = √(6 - (32/25)√10)/π^{1/4} ≤ 1.04951`, MATCH, 1.0495040. -/
theorem p3_norm2_deriv : √(6 - 32 / 25 * √10) / √√π ≤ 1.04951 := by
  obtain ⟨a1, a2⟩ := in47_bds; obtain ⟨w1, w2⟩ := w_bds
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- **(16.52), (16.53)**: `2π · 0.72839 ≤ 4.57661`, `2π · 0.4155 ≤ 2.61067`, MATCH. -/
theorem p3_delta_coeffs : 2 * π * 0.72839 ≤ 4.57661 ∧ 2 * π * 0.4155 ≤ 2.61067 := by
  obtain ⟨p1, p2⟩ := pi_bds
  constructor <;> nlinarith

/-- **Prop. 16.18, `c₂ = 0.72839/√π + 0.3√π · 0.27686 ≤ 0.55817`**, MATCH, 0.5581665. -/
theorem p3_c2 : 0.72839 / √π + 0.3 * √π * 0.27686 ≤ 0.55817 := by
  obtain ⟨s1, s2⟩ := s_bds
  have h : 0.72839 / √π ≤ 0.4109515 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-- **Prop. 16.18, `c₁` as the book computes it**: `6.484√π · 0.27686 - (log 2π√e/√π) · 0.72839
≤ 2.22109`; value 2.2210880. -/
theorem p3_c1_printed :
    6.484 * √π * 0.27686 - log (2 * π * √(exp 1)) / √π * 0.72839 ≤ 2.22109 := by
  obtain ⟨s1, s2⟩ := s_bds; obtain ⟨k1, k2⟩ := K_bds
  have h : 0.96075 ≤ log (2 * π * √(exp 1)) / √π * 0.72839 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
  linarith

/-- **The gap**: with the exact `|η|₂` of (16.46) and the printed `|η log|₂ ≤ 0.27686`, the
expression for `c₁` exceeds `2.22109`; value 2.2210998. `0.72839` is an upper bound for `|η|₂`
and enters `c₁` with a minus sign, so the printed inputs do not give the printed `c₁`. -/
theorem p3_c1_gap : 2.22109 <
    6.484 * √π * 0.27686 - log (2 * π * √(exp 1)) / √π * (√(6 - 8 * √(2 / 5)) / √√π) := by
  obtain ⟨s1, s2⟩ := s_bds; obtain ⟨k1, k2⟩ := K_bds; obtain ⟨n1, n2⟩ := p3_norm2
  have hn0 : 0 < √(6 - 8 * √(2 / 5)) / √√π := by linarith
  have h : log (2 * π * √(exp 1)) / √π * (√(6 - 8 * √(2 / 5)) / √√π) < 0.960739 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  nlinarith

/-- **`c₁ ≤ 2.22109` holds**, CONDITIONAL ON `|η log|₂ ≤ 0.276856`, the norm of (16.48) to six
digits, recomputed as 0.2768557588 by gen/book_c1614_1618_U6716.py; value 2.2210552. -/
theorem p3_c1_true {N : ℝ} (hN : N ≤ 0.276856) :
    6.484 * √π * N - log (2 * π * √(exp 1)) / √π * (√(6 - 8 * √(2 / 5)) / √√π) ≤ 2.22109 := by
  obtain ⟨s1, s2⟩ := s_bds; obtain ⟨k1, k2⟩ := K_bds; obtain ⟨n1, n2⟩ := p3_norm2
  have h : 0.960737 ≤ log (2 * π * √(exp 1)) / √π * (√(6 - 8 * √(2 / 5)) / √√π) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
  have hs0 : 0 < √π := by linarith
  nlinarith

/-- **Prop. 16.18, the other constants**: `c_{1/2}` from `0.919 · 1.0076`, `12.653 · 1.0076`;
`ε_{T,q,f}` from `3 · 0.435`, `3 · 1.134`, `4 · 0.22`; and (16.57)'s rounding, MATCH. -/
theorem p3_rest :
    (0.919 : ℝ) * 1.0076 ≤ 0.92599 ∧ (12.653 : ℝ) * 1.0076 ≤ 12.74917 ∧
    (3 : ℝ) * 0.435 ≤ 1.305 ∧ (3 : ℝ) * 1.134 ≤ 3.402 ∧ (4 : ℝ) * 0.22 ≤ 0.88 ∧
    (1.305 : ℝ) ≤ 1.31 ∧ (3.402 : ℝ) ≤ 3.41 ∧ (0.55817 : ℝ) ≤ 0.56 ∧ (2.22109 : ℝ) ≤ 2.23 ∧
    (0.92599 : ℝ) ≤ 0.93 ∧ (12.74917 : ℝ) ≤ 12.8 ∧ (2.61067 : ℝ) ≤ 2.7 ∧ (1.10616 : ℝ) ≤ 1.2 ∧
    (1.04951 : ℝ) ≤ 1.1 ∧ (4.57661 : ℝ) ≤ 4.6 := by
  norm_num

end LeanLab.HelfgottMajor.BookP1617
