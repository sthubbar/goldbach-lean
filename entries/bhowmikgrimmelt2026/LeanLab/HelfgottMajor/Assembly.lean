module

public import Mathlib
public import LeanLab.Helfgott2013.SectionSevenB

/-!
P0014 H. A. Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Section 4.6
"A verification of zeros and its consequences", pages 56 to 59: the arithmetic that turns
Prop. 4.6, Prop. 4.8, Cor. 4.9 and (4.65) with Platt's GRH verification into the constants
of Theorems 1.1, 1.2, Corollary 1.3 and Theorem 1.4. Read from the arXiv PDF with
pdftotext, cloud session 20261018T1720Z-cloud5.

Only the arithmetic is checked; the propositions themselves and Platt's verification are
the paper's. This folder is new so that LeanLab/HelfgottArcs/, where Theorems 1.1 to 1.4 are
stated and which another session holds for P0013, stays untouched.

AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor
open Real Finset
open LeanLab.Helfgott2013 (log_ten_lt_ratio log_ten_gt_ratio log_three_lt_ratio log_300000_lt)

/-! ### Bounds on `exp`, `log` and `π` -/

/-- `e^k · Σ_{i<n} rⁱ/i! ≤ exp(k + r)` for `r ≥ 0`. -/
theorem exp_lower (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    2.7182818283 ^ k * ∑ i ∈ range n, r ^ i / i.factorial ≤ Real.exp (k + r) := by
  rw [Real.exp_add]
  have h1 : (2.7182818283 : ℝ) ^ k ≤ Real.exp k := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le k
  have h2 := Real.sum_le_exp_of_nonneg hr n
  have h0 : 0 ≤ ∑ i ∈ range n, r ^ i / i.factorial :=
    sum_nonneg (fun i _ => by positivity)
  exact mul_le_mul h1 h2 h0 (Real.exp_pos _).le

/-- `log x ≥ log y + 1 − y/x` for `0 < x`, `0 < y`. -/
theorem log_ge_lin {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y + (1 - y / x) ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h; linarith

theorem log_ten_lt : Real.log 10 < 2.3025854 := by
  have := log_ten_lt_ratio; have := Real.log_two_lt_d9; linarith

theorem log_ten_gt : 2.30258487 < Real.log 10 := by
  have := log_ten_gt_ratio; have := Real.log_two_gt_d9; linarith

/-- `log (2π) ≥ 1.837862`, from `log 6.25 = 2 log 10 − 4 log 2` and `log x ≥ log y + 1 − y/x`. -/
theorem log_two_pi_gt : 1.837862 < Real.log (2 * π) := by
  have hp := Real.pi_gt_d20
  have h := log_ge_lin (by positivity : 0 < 2 * π) (by norm_num : (0 : ℝ) < 6.25)
  have e : Real.log 6.25 = 2 * Real.log 10 - 4 * Real.log 2 := by
    rw [show (6.25 : ℝ) = 10 ^ 2 / 2 ^ 4 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]; push_cast; ring
  have : 6.25 / (2 * π) < 6.25 / (2 * 3.14159265358979323846) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) (by linarith)
  have := log_ten_gt_ratio; have := Real.log_two_gt_d9; have := Real.log_two_lt_d9
  have : (6.25 : ℝ) / (2 * 3.14159265358979323846) < 0.9947184 := by norm_num
  linarith

/-- `log 10^8 = 8 log 10 ≤ 18.420684`. -/
theorem log_1e8_lt : Real.log 1e8 < 18.420684 := by
  rw [show (1e8 : ℝ) = 10 ^ 8 by norm_num, Real.log_pow]; push_cast
  have := log_ten_lt; linarith

/-- `L = log(10^8/(2π)) ≤ 16.5829`. -/
theorem L_lt : Real.log (1e8 / (2 * π)) < 16.5829 := by
  rw [Real.log_div (by norm_num) (by positivity)]
  have := log_1e8_lt; have := log_two_pi_gt; linarith

theorem log_q_le {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 3e5) : Real.log q ≤ 12.61154 := by
  have := Real.log_le_log (by linarith) hq
  have := log_300000_lt; norm_num at *; linarith

theorem log_q_nonneg {q : ℝ} (hq1 : 1 ≤ q) : 0 ≤ Real.log q := Real.log_nonneg hq1

theorem sqrt_T0 {q : ℝ} (hq : 0 < q) : Real.sqrt (1e8 / q) = 1e4 / Real.sqrt q := by
  rw [Real.sqrt_div' _ hq.le]
  congr 1
  rw [show (1e8 : ℝ) = 1e4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ### Theorem 1.1, `η(t) = e^{−t²/2}`, `r = 3 · 10^5`, `δ₀ = 8`, `T₀ = 10^8/q` -/

/-- `4.329 e^{−0.1598 T₀} ≤ 3.184 · 10^-23` for `T₀ ≥ 1000/3`. MATCHES, 3.183964e-23. -/
theorem A1 {T0 : ℝ} (h : 1000 / 3 ≤ T0) : 4.329 * Real.exp (-0.1598 * T0) ≤ 3.184e-23 := by
  have he : Real.exp (-0.1598 * T0) ≤ Real.exp (-((53 : ℕ) + 4 / 15)) :=
    Real.exp_le_exp.mpr (by push_cast; linarith)
  have hl := exp_lower 53 (by norm_num : (0 : ℝ) ≤ 4 / 15) 7
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at hl
  rw [Real.exp_neg] at he
  have hp : 0 < Real.exp ((53 : ℕ) + 4 / 15) := Real.exp_pos _
  have : 4.329 * (Real.exp ((53 : ℕ) + 4 / 15))⁻¹ ≤ 3.184e-23 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hp]; norm_num at hl ⊢; linarith
  linarith

/-- `0.802 e^{−0.1065 u²} ≤ 4.3166 · 10^-33` for `u = T₀/(π|δ|) ≥ 1000/(12π)`. MATCHES with
room, the value at the edge is 2.29e-33. -/
theorem A2 {u : ℝ} (h : 1000 / (12 * π) ≤ u) : 0.802 * Real.exp (-0.1065 * u ^ 2) ≤ 4.3166e-33 := by
  have hp := Real.pi_lt_d6
  have hu : (26.5 : ℝ) ≤ u := by
    refine le_trans ?_ h
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hu2 : (74.5 : ℝ) ≤ 0.1065 * u ^ 2 := by nlinarith
  have he : Real.exp (-0.1065 * u ^ 2) ≤ Real.exp (-((74 : ℕ) + 1 / 2)) :=
    Real.exp_le_exp.mpr (by push_cast; linarith)
  have hl := exp_lower 74 (by norm_num : (0 : ℝ) ≤ 1 / 2) 5
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at hl
  rw [Real.exp_neg] at he
  have hpos : 0 < Real.exp ((74 : ℕ) + 1 / 2) := Real.exp_pos _
  have : 0.802 * (Real.exp ((74 : ℕ) + 1 / 2))⁻¹ ≤ 4.3166e-33 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]; norm_num at hl ⊢; linarith
  linarith

/-- With `qT₀ = 10^8` and `|δ| ≤ 1.2 · 10^6/q`: `log(qT₀/2π) · 3.184 · 10^-23 ≤ 5.28 · 10^-22`,
`log(qT₀/2π) · 1.2 · 10^6 · 4.3166 · 10^-33 ≤ 8.59 · 10^-26`, and the sum `≤ 5.281 · 10^-22`.
MATCHES. -/
theorem A3 : Real.log (1e8 / (2 * π)) * 3.184e-23 ≤ 5.28e-22 ∧
    Real.log (1e8 / (2 * π)) * (1.2e6 * 4.3166e-33) ≤ 8.59e-26 ∧
    (5.28e-22 : ℝ) + 8.59e-26 ≤ 5.281e-22 := by
  have := L_lt
  refine ⟨by nlinarith, by nlinarith, by norm_num⟩

/-- `2.337 √T₀ log(qT₀) + 21.817 √T₀ + 2.85 log q + 74.38 ≤ 648662/√q + 111` for
`1 ≤ q ≤ 3 · 10^5`, `T₀ = 10^8/q`. MATCHES, `648661.3/√q + 110.32`. -/
theorem A4 {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 3e5) :
    2.337 * Real.sqrt (1e8 / q) * Real.log (q * (1e8 / q)) + 21.817 * Real.sqrt (1e8 / q) +
      2.85 * Real.log q + 74.38 ≤ 648662 / Real.sqrt q + 111 := by
  have hq0 : 0 < q := by linarith
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  rw [sqrt_T0 hq0, show q * (1e8 / q) = 1e8 by field_simp]
  have hl := log_1e8_lt
  have hlq := log_q_le hq1 hq
  have e : 2.337 * (1e4 / Real.sqrt q) * Real.log 1e8 + 21.817 * (1e4 / Real.sqrt q) =
      (2.337e4 * Real.log 1e8 + 21.817e4) / Real.sqrt q := by field_simp; ring
  rw [e]
  have : (2.337e4 * Real.log 1e8 + 21.817e4) / Real.sqrt q ≤ 648662 / Real.sqrt q :=
    div_le_div_of_nonneg_right (by nlinarith) hs.le
  linarith

/-- `3 log q + 14|δ| + 17 ≤ 55 + 1.7 · 10^7/q` and `(log q + 6)(1 + 5|δ|) ≤ 19 + 1.2 · 10^8/q`
for `1 ≤ q ≤ 3 · 10^5`, `0 ≤ |δ| ≤ 1.2 · 10^6/q`. MATCHES. -/
theorem A56 {q d : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 3e5) (_hd0 : 0 ≤ d) (hd : d ≤ 1.2e6 / q) :
    3 * Real.log q + 14 * d + 17 ≤ 55 + 1.7e7 / q ∧
    (Real.log q + 6) * (1 + 5 * d) ≤ 19 + 1.2e8 / q := by
  have hq0 : 0 < q := by linarith
  have hlq := log_q_le hq1 hq
  have hl0 := log_q_nonneg hq1
  have hdq : d * q ≤ 1.2e6 := by rwa [le_div_iff₀ hq0] at hd
  constructor
  · have : 14 * d ≤ 1.7e7 / q := by rw [le_div_iff₀ hq0]; nlinarith
    linarith
  · have h1 : (Real.log q + 6) * (5 * d) ≤ 1.2e8 / q := by
      rw [le_div_iff₀ hq0]; nlinarith [mul_le_mul_of_nonneg_left hdq (by linarith : (0:ℝ) ≤ Real.log q + 6)]
    nlinarith

/-- The last display of Theorem 1.1's proof: for `1 ≤ q`, `x = s² ≥ 10^8`,
`648662/√q + 111 + (55 + 1.7 · 10^7/q)/√x + (19 + 1.2 · 10^8/q)/x ≤ 650400/√q + 112`,
all times `x^{-1/2}`. MATCHES. -/
theorem A7 {q s : ℝ} (hq1 : 1 ≤ q) (hs : 1e4 ≤ s) :
    648662 / Real.sqrt q + 111 + (55 + 1.7e7 / q) / s + (19 + 1.2e8 / q) / s ^ 2 ≤
      650400 / Real.sqrt q + 112 := by
  have hq0 : 0 < q := by linarith
  have hsq1 : 1 ≤ Real.sqrt q := by rw [Real.one_le_sqrt]; exact hq1
  have hsq : 0 < Real.sqrt q := by linarith
  have hqs : Real.sqrt q ≤ q := by
    have := Real.sq_sqrt hq0.le; nlinarith
  have hs0 : 0 < s := by linarith
  have i1 : 1 / q ≤ 1 / Real.sqrt q := one_div_le_one_div_of_le hsq hqs
  have i2 : 0 < 1 / Real.sqrt q := by positivity
  have i3 : 1 / s ≤ 1e-4 := by rw [div_le_iff₀ hs0]; linarith
  have i4 : 1 / s ^ 2 ≤ 1e-8 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have i5 : 0 < 1 / s := by positivity
  have i6 : 0 < 1 / s ^ 2 := by positivity
  have e1 : (55 + 1.7e7 / q) / s = 55 * (1 / s) + 1.7e7 * (1 / q) * (1 / s) := by ring
  have e2 : (19 + 1.2e8 / q) / s ^ 2 = 19 * (1 / s ^ 2) + 1.2e8 * (1 / q) * (1 / s ^ 2) := by ring
  have e3 : 648662 / Real.sqrt q = 648662 * (1 / Real.sqrt q) := by ring
  have e4 : 650400 / Real.sqrt q = 650400 * (1 / Real.sqrt q) := by ring
  rw [e1, e2, e3, e4]
  have : (1 / q) * (1 / s) ≤ (1 / Real.sqrt q) * 1e-4 :=
    mul_le_mul i1 i3 i5.le i2.le
  have : (1 / q) * (1 / s ^ 2) ≤ (1 / Real.sqrt q) * 1e-8 :=
    mul_le_mul i1 i4 i6.le i2.le
  nlinarith

/-! ### Theorem 1.2 and Corollary 1.3, `η = t² e^{−t²/2}` and `η = t² e^{−t²/2} ∗_M η₂` -/

/-- `log(qT₀/2π) (3.5 e^{−0.1598 T₀} + 0.64 e^{−0.1065 u²}) ≤ 4.269 · 10^-22` for `qT₀ = 10^8`,
`T₀ ≥ 1000/3`, `u ≥ 1000/(12π)`; times `T₀ = 10^8/q` this is the paper's `≤ 4.269 · 10^-14/q`.
MATCHES, 4.26883e-22. -/
theorem B1 {T0 u : ℝ} (hT : 1000 / 3 ≤ T0) (hu : 1000 / (12 * π) ≤ u) :
    Real.log (1e8 / (2 * π)) * (3.5 * Real.exp (-0.1598 * T0) + 0.64 * Real.exp (-0.1065 * u ^ 2))
      ≤ 4.269e-22 := by
  have hL := L_lt
  have hL0 : 0 ≤ Real.log (1e8 / (2 * π)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; have := Real.pi_lt_d2; nlinarith
  have he : Real.exp (-0.1598 * T0) ≤ Real.exp (-((53 : ℕ) + 4 / 15)) :=
    Real.exp_le_exp.mpr (by push_cast; linarith)
  have hl := exp_lower 53 (by norm_num : (0 : ℝ) ≤ 4 / 15) 7
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at hl
  rw [Real.exp_neg] at he
  have hp : 0 < Real.exp ((53 : ℕ) + 4 / 15) := Real.exp_pos _
  have h1 : 3.5 * (Real.exp ((53 : ℕ) + 4 / 15))⁻¹ ≤ 2.5743e-23 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hp]; norm_num at hl ⊢; linarith
  have h2 := A2 hu
  have h3 : 0 ≤ Real.exp (-0.1065 * u ^ 2) := (Real.exp_pos _).le
  have h4 : 3.5 * Real.exp (-0.1598 * T0) + 0.64 * Real.exp (-0.1065 * u ^ 2) ≤
      2.5743e-23 + 0.64 * (4.3166e-33 / 0.802) := by
    have : Real.exp (-0.1065 * u ^ 2) ≤ 4.3166e-33 / 0.802 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith
  calc Real.log (1e8 / (2 * π)) * (3.5 * Real.exp (-0.1598 * T0) + 0.64 * Real.exp (-0.1065 * u ^ 2))
      ≤ 16.5829 * (2.5743e-23 + 0.64 * (4.3166e-33 / 0.802)) := by
        apply mul_le_mul hL.le h4 (by positivity) (by norm_num)
    _ ≤ 4.269e-22 := by norm_num

/-- `1.22 √T₀ log qT₀ + 5.053 √T₀ + 1.423 log q + 37.19 ≤ 275263/√q + 55.2` and
`1.675 √T₀ log qT₀ + 6.936 √T₀ + 1.954 log q + 51.047 ≤ 377907/√q + 75.7`. MATCHES,
`275262.3/√q + 55.14` and `377906.4/√q + 75.690`. -/
theorem B23 {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 3e5) :
    1.22 * Real.sqrt (1e8 / q) * Real.log (q * (1e8 / q)) + 5.053 * Real.sqrt (1e8 / q) +
      1.423 * Real.log q + 37.19 ≤ 275263 / Real.sqrt q + 55.2 ∧
    1.675 * Real.sqrt (1e8 / q) * Real.log (q * (1e8 / q)) + 6.936 * Real.sqrt (1e8 / q) +
      1.954 * Real.log q + 51.047 ≤ 377907 / Real.sqrt q + 75.7 := by
  have hq0 : 0 < q := by linarith
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  rw [sqrt_T0 hq0, show q * (1e8 / q) = 1e8 by field_simp]
  have hl := log_1e8_lt
  have hlq := log_q_le hq1 hq
  constructor
  · have e : 1.22 * (1e4 / Real.sqrt q) * Real.log 1e8 + 5.053 * (1e4 / Real.sqrt q) =
        (1.22e4 * Real.log 1e8 + 5.053e4) / Real.sqrt q := by field_simp; ring
    rw [e]
    have : (1.22e4 * Real.log 1e8 + 5.053e4) / Real.sqrt q ≤ 275263 / Real.sqrt q :=
      div_le_div_of_nonneg_right (by nlinarith) hs.le
    linarith
  · have e : 1.675 * (1e4 / Real.sqrt q) * Real.log 1e8 + 6.936 * (1e4 / Real.sqrt q) =
        (1.675e4 * Real.log 1e8 + 6.936e4) / Real.sqrt q := by field_simp; ring
    rw [e]
    have : (1.675e4 * Real.log 1e8 + 6.936e4) / Real.sqrt q ≤ 377907 / Real.sqrt q :=
      div_le_div_of_nonneg_right (by nlinarith) hs.le
    linarith

/-- With `x = s²`, `s ≥ 10^4`, `0 ≤ |δ| ≤ 1.2 · 10^6/q`, `1 ≤ q ≤ 3 · 10^5`:
`(3 + 11|δ|) x^{-1} + (log q + 6)(1 + 6|δ|) x^{-3/2} ≤ (0.0004 + 1322/q) x^{-1/2}` and
`(6 + 22|δ|) x^{-1} + (log q + 6)(3 + 17|δ|) x^{-3/2} ≤ (0.0007 + 2644/q) x^{-1/2}`, here
multiplied through by `√x`. MATCHES, `1321.34/q` and `2643.80/q`. -/
theorem B45 {q d s : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 3e5) (hd0 : 0 ≤ d) (hd : d ≤ 1.2e6 / q)
    (hs : 1e4 ≤ s) :
    (3 + 11 * d) / s + (Real.log q + 6) * (1 + 6 * d) / s ^ 2 ≤ 0.0004 + 1322 / q ∧
    (6 + 22 * d) / s + (Real.log q + 6) * (3 + 17 * d) / s ^ 2 ≤ 0.0007 + 2644 / q := by
  have hq0 : 0 < q := by linarith
  have hlq := log_q_le hq1 hq
  have hl0 := log_q_nonneg hq1
  have hdq : d * q ≤ 1.2e6 := by rwa [le_div_iff₀ hq0] at hd
  have hs0 : 0 < s := by linarith
  have i3 : 1 / s ≤ 1e-4 := by rw [div_le_iff₀ hs0]; linarith
  have i4 : 1 / s ^ 2 ≤ 1e-8 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have i5 : 0 < 1 / s := by positivity
  have i6 : 0 < 1 / s ^ 2 := by positivity
  have hiq : 0 < 1 / q := by positivity
  have hdi : d ≤ 1.2e6 * (1 / q) := by rw [mul_one_div]; exact hd
  have hA : 0 ≤ Real.log q + 6 := by linarith
  have k1 : d * (1 / s) ≤ 1.2e6 * (1 / q) * 1e-4 := mul_le_mul hdi i3 i5.le (by positivity)
  have k2 : (Real.log q + 6) * (1 / s ^ 2) ≤ 18.61154 * 1e-8 := mul_le_mul (by linarith) i4 i6.le (by norm_num)
  have k3 : (Real.log q + 6) * d * (1 / s ^ 2) ≤ 18.61154 * (1.2e6 * (1 / q)) * 1e-8 :=
    mul_le_mul (mul_le_mul (by linarith) hdi hd0 (by norm_num)) i4 i6.le (by positivity)
  have e1 : (3 + 11 * d) / s + (Real.log q + 6) * (1 + 6 * d) / s ^ 2 =
      3 * (1 / s) + 11 * (d * (1 / s)) + (Real.log q + 6) * (1 / s ^ 2) +
        6 * ((Real.log q + 6) * d * (1 / s ^ 2)) := by ring
  have e2 : (6 + 22 * d) / s + (Real.log q + 6) * (3 + 17 * d) / s ^ 2 =
      6 * (1 / s) + 22 * (d * (1 / s)) + 3 * ((Real.log q + 6) * (1 / s ^ 2)) +
        17 * ((Real.log q + 6) * d * (1 / s ^ 2)) := by ring
  have e3 : (1322 : ℝ) / q = 1322 * (1 / q) := by ring
  have e4 : (2644 : ℝ) / q = 2644 * (1 / q) := by ring
  rw [e1, e2, e3, e4]
  constructor <;> nlinarith

/-- Summing: `275263/√q + 55.2 + 0.0004 + 1322/q ≤ 276600/√q + 56` and
`377907/√q + 75.7 + 0.0007 + 2644/q ≤ 380600/√q + 76` for `q ≥ 1`. MATCHES. -/
theorem B6 {q : ℝ} (hq1 : 1 ≤ q) :
    275263 / Real.sqrt q + 55.2 + (0.0004 + 1322 / q) ≤ 276600 / Real.sqrt q + 56 ∧
    377907 / Real.sqrt q + 75.7 + (0.0007 + 2644 / q) ≤ 380600 / Real.sqrt q + 76 := by
  have hq0 : 0 < q := by linarith
  have hsq1 : 1 ≤ Real.sqrt q := by rw [Real.one_le_sqrt]; exact hq1
  have hsq : 0 < Real.sqrt q := by linarith
  have hqs : Real.sqrt q ≤ q := by have := Real.sq_sqrt hq0.le; nlinarith
  have i1 : 1 / q ≤ 1 / Real.sqrt q := one_div_le_one_div_of_le hsq hqs
  have i2 : 0 < 1 / Real.sqrt q := by positivity
  have h1 : (1322 : ℝ) / q ≤ 1322 / Real.sqrt q := div_le_div_of_nonneg_left (by norm_num) hsq hqs
  have h2 : (2644 : ℝ) / q ≤ 2644 / Real.sqrt q := div_le_div_of_nonneg_left (by norm_num) hsq hqs
  have h3 : (1322 : ℝ) / Real.sqrt q ≤ 1337 / Real.sqrt q :=
    div_le_div_of_nonneg_right (by norm_num) hsq.le
  have h4 : (2644 : ℝ) / Real.sqrt q ≤ 2693 / Real.sqrt q :=
    div_le_div_of_nonneg_right (by norm_num) hsq.le
  have e1 : (276600 : ℝ) / Real.sqrt q = 275263 / Real.sqrt q + 1337 / Real.sqrt q := by ring
  have e2 : (380600 : ℝ) / Real.sqrt q = 377907 / Real.sqrt q + 2693 / Real.sqrt q := by ring
  rw [e1, e2]
  constructor <;> linarith

/-! ### Theorem 1.4, `η₊`, `H = 200`, `T₀ = H + 250r/q`, `r ≤ 3 · 10^5` -/

/-- `250/(4π) ≥ 19.89436`. MATCHES, 19.8943678. -/
theorem C1 : (19.89436 : ℝ) ≤ 250 / (4 * π) := by
  have := Real.pi_lt_d20
  rw [le_div_iff₀ (by positivity)]; nlinarith

/-- `T₀ ≤ 200 + 250 · 150000 ≤ 3.751 · 10^7` and `rH + 250 r ≤ 1.35 · 10^8` at `r = 3 · 10^5`.
MATCHES. -/
theorem C2 : (200 : ℝ) + 250 * 150000 ≤ 3.751e7 ∧ (300000 : ℝ) * 200 + 250 * 300000 ≤ 1.35e8 := by
  constructor <;> norm_num

/-- `9.462 e^{−0.1598 · 250} ≤ 4.2259 · 10^-17`. MATCHES, margin `2 · 10^-6` relative. -/
theorem C3a : 9.462 * Real.exp (-0.1598 * 250) ≤ 4.2259e-17 := by
  have hl := exp_lower 39 (by norm_num : (0 : ℝ) ≤ 0.95) 12
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at hl
  have e : -0.1598 * 250 = -((39 : ℕ) + (0.95 : ℝ)) := by push_cast; norm_num
  rw [e, Real.exp_neg]
  have hp : 0 < Real.exp ((39 : ℕ) + (0.95 : ℝ)) := Real.exp_pos _
  rw [← div_eq_mul_inv, div_le_iff₀ hp]; norm_num at hl ⊢; linarith

/-- `11.287 e^{−0.1065 (250/(4π))²} ≤ 5.57888 · 10^-18`. MATCHES, value 5.578878e-18, margin
`3 · 10^-7` relative. -/
theorem C3b : 11.287 * Real.exp (-0.1065 * (250 / (4 * π)) ^ 2) ≤ 5.57888e-18 := by
  have hp := Real.pi_lt_d20
  have hw : 250 / (4 * 3.14159265358979323847) ≤ 250 / (4 * π) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hw0 : (0 : ℝ) ≤ 250 / (4 * 3.14159265358979323847) := by norm_num
  have hexp : (42 : ℝ) + 0.1511955 ≤ 0.1065 * (250 / (4 * π)) ^ 2 := by
    have : (250 / (4 * 3.14159265358979323847) : ℝ) ^ 2 ≤ (250 / (4 * π)) ^ 2 :=
      pow_le_pow_left₀ hw0 hw 2
    have : (42 : ℝ) + 0.1511955 ≤ 0.1065 * (250 / (4 * 3.14159265358979323847)) ^ 2 := by norm_num
    nlinarith
  have he : Real.exp (-0.1065 * (250 / (4 * π)) ^ 2) ≤ Real.exp (-((42 : ℕ) + (0.1511955 : ℝ))) :=
    Real.exp_le_exp.mpr (by push_cast; linarith)
  have hl := exp_lower 42 (by norm_num : (0 : ℝ) ≤ 0.1511955) 7
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at hl
  rw [Real.exp_neg] at he
  have hpos : 0 < Real.exp ((42 : ℕ) + (0.1511955 : ℝ)) := Real.exp_pos _
  have : 11.287 * (Real.exp ((42 : ℕ) + (0.1511955 : ℝ)))⁻¹ ≤ 5.57888e-18 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]; norm_num at hl ⊢; linarith
  linarith

/-- `4.2259 · 10^-17 √(250 r) ≤ 3.6598 · 10^-13` and `4r · 5.57888 · 10^-18 ≤ 6.6947 · 10^-12` at
`r = 3 · 10^5`. MATCHES. -/
theorem C3c : 4.2259e-17 * Real.sqrt (250 * 300000) ≤ (3.6598e-13 : ℝ) ∧
    4 * 300000 * 5.57888e-18 ≤ (6.6947e-12 : ℝ) := by
  have : Real.sqrt (250 * 300000) ≤ (8660.2541 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  constructor
  · nlinarith
  · norm_num

/-- `log(1.35 · 10^8) = 3 log 3 + 7 log 10 − log 2 < 18.720789`. -/
theorem log_135e6_lt : Real.log 1.35e8 < 18.720789 := by
  have e : Real.log 1.35e8 = 3 * Real.log 3 + 7 * Real.log 10 - Real.log 2 := by
    rw [show (1.35e8 : ℝ) = 3 ^ 3 * 10 ^ 7 / 2 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]; push_cast; ring
  have := log_three_lt_ratio; have := log_ten_lt_ratio
  have := Real.log_two_lt_d9; have := Real.log_two_gt_d9
  rw [e]; linarith

/-- (4.65) assembled: `log(1.35 · 10^8/2π) · 3.6598 · 10^-13 ≤ 6.18 · 10^-12`,
`log(1.35 · 10^8/2π) · 6.6947 · 10^-12 ≤ 1.14 · 10^-10`,
`(1.631 log(1.35 · 10^8) + 12.42) √(1.35 · 10^8) ≤ 499076`, `1.321 log 300000 + 34.51 ≤ 51.17`,
`11 log 300000 ≤ 139`, `6 · 1.2 · 10^6 log 300000 ≤ 9.1 · 10^7`. MATCHES. -/
theorem C4 :
    Real.log (1.35e8 / (2 * π)) * 3.6598e-13 ≤ (6.18e-12 : ℝ) ∧
    Real.log (1.35e8 / (2 * π)) * 6.6947e-12 ≤ (1.14e-10 : ℝ) ∧
    (1.631 * Real.log 1.35e8 + 12.42) * Real.sqrt 1.35e8 ≤ (499076 : ℝ) ∧
    1.321 * Real.log 300000 + 34.51 ≤ (51.17 : ℝ) ∧
    Real.log 300000 * 11 ≤ (139 : ℝ) ∧ Real.log 300000 * (6 * 1.2e6) ≤ (9.1e7 : ℝ) := by
  have h1 := log_135e6_lt
  have h2 := log_two_pi_gt
  have h3 := log_300000_lt
  have hL : Real.log (1.35e8 / (2 * π)) < 16.882927 := by
    rw [Real.log_div (by norm_num) (by positivity)]; linarith
  have hs : Real.sqrt 1.35e8 ≤ (11618.9501 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt (1.35e8 : ℝ) := Real.sqrt_nonneg _
  have hl0 : 0 ≤ Real.log (1.35e8 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨by nlinarith, by nlinarith, ?_, by linarith, by linarith, by linarith⟩
  calc (1.631 * Real.log 1.35e8 + 12.42) * Real.sqrt 1.35e8
      ≤ (1.631 * 18.720789 + 12.42) * 11618.9501 := by
        apply mul_le_mul (by linarith) hs hs0 (by norm_num)
    _ ≤ 499076 := by norm_num

/-- The factor in front of `x^{-1}` is `9 + 11 · 1.2 · 10^6/q`, so the term written over
`q√x` inside the `x^{-1/2}` bracket is `11 · 1.2 · 10^6 = 1.32 · 10^7`, not the printed
`1.32 · 10^6`. A factor ten typo, also in the book version; harmless, see `C4_final`. -/
theorem C4_typo : (11 : ℝ) * 1.2e6 = 1.32e7 ∧ (11 : ℝ) * 1.2e6 ≠ 1.32e6 := by
  constructor <;> norm_num

/-- The end of Theorem 1.4's proof with the corrected `1.32 · 10^7`: for `q ≥ 1`,
`√x = s ≥ 10^6`,
`499076/√q + 51.17 + 1.32 · 10^7/(q s) + 9/s + 9.1 · 10^7/(q s²) + 139/s² ≤ 499100/√q + 52`.
MATCHES; the printed `499100` and `52` hold. -/
theorem C4_final {q s : ℝ} (hq1 : 1 ≤ q) (hs : 1e6 ≤ s) :
    499076 / Real.sqrt q + 51.17 + 1.32e7 / (q * s) + 9 / s + 9.1e7 / (q * s ^ 2) + 139 / s ^ 2 ≤
      499100 / Real.sqrt q + 52 := by
  have hq0 : 0 < q := by linarith
  have hsq1 : 1 ≤ Real.sqrt q := by rw [Real.one_le_sqrt]; exact hq1
  have hsq : 0 < Real.sqrt q := by linarith
  have hqs : Real.sqrt q ≤ q := by have := Real.sq_sqrt hq0.le; nlinarith
  have hs0 : 0 < s := by linarith
  have i1 : 1 / q ≤ 1 / Real.sqrt q := one_div_le_one_div_of_le hsq hqs
  have i2 : 0 < 1 / Real.sqrt q := by positivity
  have i3 : 1 / s ≤ 1e-6 := by rw [div_le_iff₀ hs0]; linarith
  have i4 : 1 / s ^ 2 ≤ 1e-12 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have i5 : 0 < 1 / s := by positivity
  have i6 : 0 < 1 / s ^ 2 := by positivity
  have k1 : (1 / q) * (1 / s) ≤ (1 / Real.sqrt q) * 1e-6 := mul_le_mul i1 i3 i5.le i2.le
  have k2 : (1 / q) * (1 / s ^ 2) ≤ (1 / Real.sqrt q) * 1e-12 := mul_le_mul i1 i4 i6.le i2.le
  have e : 499076 / Real.sqrt q + 51.17 + 1.32e7 / (q * s) + 9 / s + 9.1e7 / (q * s ^ 2) +
      139 / s ^ 2 = 499076 * (1 / Real.sqrt q) + 51.17 + 1.32e7 * ((1 / q) * (1 / s)) +
      9 * (1 / s) + 9.1e7 * ((1 / q) * (1 / s ^ 2)) + 139 * (1 / s ^ 2) := by
    field_simp
  have e2 : 499100 / Real.sqrt q + 52 = 499100 * (1 / Real.sqrt q) + 52 := by ring
  rw [e, e2]
  nlinarith

/-! ### Theorem 1.4 at `q = 1`, `T₀ = H + 600000π t`, `t = 20` -/

/-- `11.287 · 600000 ≤ 6773000`. MATCHES. -/
theorem C5a : (11.287 : ℝ) * 600000 ≤ 6773000 := by norm_num

/-- `9.462 √(T₀ − H) e^{−0.1598 (T₀ − H)} ≤ 10^{−1300000}` at `T₀ − H = 1.2 · 10^7 π`, in the form
`… ≤ exp(−1300000 log 10)`. MATCHES with vast room. -/
theorem C5b : 9.462 * Real.sqrt (1.2e7 * π) * Real.exp (-0.1598 * (1.2e7 * π)) ≤
    Real.exp (-1300000 * Real.log 10) := by
  have hp := Real.pi_lt_d6
  have hp' := Real.pi_gt_three
  have hs : Real.sqrt (1.2e7 * π) ≤ 6140 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hl := log_ten_lt
  have hK : 9.462 * Real.sqrt (1.2e7 * π) ≤ Real.exp 11 := by
    have h11 := exp_lower 11 (by norm_num : (0 : ℝ) ≤ 0) 1
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h11
    norm_num at h11
    nlinarith
  have hK0 : 0 ≤ 9.462 * Real.sqrt (1.2e7 * π) := by positivity
  calc 9.462 * Real.sqrt (1.2e7 * π) * Real.exp (-0.1598 * (1.2e7 * π))
      ≤ Real.exp 11 * Real.exp (-0.1598 * (1.2e7 * π)) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
    _ = Real.exp (11 + -0.1598 * (1.2e7 * π)) := by rw [Real.exp_add]
    _ ≤ Real.exp (-1300000 * Real.log 10) := Real.exp_le_exp.mpr (by nlinarith)

/-- `log(T₀/2π) (10^{−1300000} + 6773000 e^{−0.1065 · 20²}) ≤ 3.34 · 10^-11` at
`T₀ = 1.2 · 10^7 π + 200`. MATCHES, value 3.3355e-11. -/
theorem C5c : Real.log ((1.2e7 * π + 200) / (2 * π)) *
    (Real.exp (-1300000 * Real.log 10) + 6773000 * Real.exp (-0.1065 * 20 ^ 2)) ≤ (3.34e-11 : ℝ) := by
  have hp := Real.pi_gt_d2
  have hpos : (0 : ℝ) < 2 * π := by positivity
  have hT : (1.2e7 * π + 200) / (2 * π) ≤ 6000032 := by
    rw [div_le_iff₀ hpos]; nlinarith
  have hT1 : 6e6 ≤ (1.2e7 * π + 200) / (2 * π) := by
    rw [le_div_iff₀ hpos]; nlinarith
  have hlog : Real.log ((1.2e7 * π + 200) / (2 * π)) ≤ 15.607278 := by
    have h1 := LeanLab.Helfgott2013.log_le_lin (by norm_num : (0 : ℝ) < 6e6) hT1
    have e : Real.log 6e6 = Real.log 2 + Real.log 3 + 6 * Real.log 10 := by
      rw [show (6e6 : ℝ) = 2 * 3 * 10 ^ 6 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have := log_three_lt_ratio; have := log_ten_lt_ratio; have := Real.log_two_lt_d9
    have : (1.2e7 * π + 200) / (2 * π) / 6e6 ≤ 6000032 / 6e6 :=
      div_le_div_of_nonneg_right hT (by norm_num)
    rw [e] at h1; norm_num at this ⊢; linarith
  have hlog0 : 0 ≤ Real.log ((1.2e7 * π + 200) / (2 * π)) := Real.log_nonneg (by linarith)
  have hA : Real.exp (-1300000 * Real.log 10) ≤ 1e-20 := by
    have hl := log_ten_gt
    have h47 : Real.exp (-1300000 * Real.log 10) ≤ Real.exp (-((47 : ℕ) + (0 : ℝ))) :=
      Real.exp_le_exp.mpr (by push_cast; linarith)
    have hl47 := exp_lower 47 (by norm_num : (0 : ℝ) ≤ 0) 1
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at hl47
    rw [Real.exp_neg] at h47
    have hpos47 : 0 < Real.exp ((47 : ℕ) + (0 : ℝ)) := Real.exp_pos _
    have : (Real.exp ((47 : ℕ) + (0 : ℝ)))⁻¹ ≤ 1e-20 := by
      rw [inv_le_comm₀ hpos47 (by norm_num)]; norm_num at hl47 ⊢; linarith
    linarith
  have hB : Real.exp (-0.1065 * 20 ^ 2) ≤ 3.156e-19 := by
    have e : (-0.1065 * 20 ^ 2 : ℝ) = -((42 : ℕ) + (0.6 : ℝ)) := by push_cast; norm_num
    rw [e, Real.exp_neg]
    have hl := exp_lower 42 (by norm_num : (0 : ℝ) ≤ 0.6) 8
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at hl
    have hpos : 0 < Real.exp ((42 : ℕ) + (0.6 : ℝ)) := Real.exp_pos _
    rw [inv_le_comm₀ hpos (by norm_num)]; norm_num at hl ⊢; linarith
  have hC : Real.exp (-1300000 * Real.log 10) + 6773000 * Real.exp (-0.1065 * 20 ^ 2) ≤
      1e-20 + 6773000 * 3.156e-19 := by linarith
  have hC0 : 0 ≤ Real.exp (-1300000 * Real.log 10) + 6773000 * Real.exp (-0.1065 * 20 ^ 2) := by
    positivity
  calc _ ≤ 15.607278 * (1e-20 + 6773000 * 3.156e-19) := mul_le_mul hlog hC hC0 (by norm_num)
    _ ≤ 3.34e-11 := by norm_num

/-- `((1.631 log T₀ + 12.42) √T₀ + 34.51) + 6600009 x^{-1/2} ≤ 251100` at `T₀ = 1.2 · 10^7 π + 200`,
`√x = s ≥ 10^6`. MATCHES, about 251002. -/
theorem C5d {s : ℝ} (hs : 1e6 ≤ s) :
    (1.631 * Real.log (1.2e7 * π + 200) + 12.42) * Real.sqrt (1.2e7 * π + 200) + 34.51 +
      6600009 / s ≤ 251100 := by
  have hp := Real.pi_lt_d6
  have hp' := Real.pi_gt_three
  have hT : 1.2e7 * π + 200 ≤ 37699400 := by nlinarith
  have hT0 : 3.75e7 ≤ 1.2e7 * π + 200 := by nlinarith [Real.pi_gt_d6]
  have hsq : Real.sqrt (1.2e7 * π + 200) ≤ 6140 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hlog : Real.log (1.2e7 * π + 200) ≤ 17.44518 := by
    have h1 := LeanLab.Helfgott2013.log_le_lin (by norm_num : (0 : ℝ) < 3.75e7) hT0
    have e : Real.log 3.75e7 = Real.log 3 + 8 * Real.log 10 - 3 * Real.log 2 := by
      rw [show (3.75e7 : ℝ) = 3 * 10 ^ 8 / 2 ^ 3 by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow, Real.log_pow]; push_cast; ring
    have := log_three_lt_ratio; have := log_ten_lt_ratio
    have := Real.log_two_lt_d9; have := Real.log_two_gt_d9
    have : (1.2e7 * π + 200) / 3.75e7 ≤ 37699400 / 3.75e7 :=
      div_le_div_of_nonneg_right hT (by norm_num)
    rw [e] at h1; norm_num at this ⊢; linarith
  have hlog0 : 0 ≤ Real.log (1.2e7 * π + 200) := Real.log_nonneg (by nlinarith)
  have hs0 : 0 < s := by linarith
  have hd : 6600009 / s ≤ 6.600009 := by rw [div_le_iff₀ hs0]; nlinarith
  have hsq0 : 0 ≤ Real.sqrt (1.2e7 * π + 200) := Real.sqrt_nonneg _
  have : (1.631 * Real.log (1.2e7 * π + 200) + 12.42) * Real.sqrt (1.2e7 * π + 200) ≤
      (1.631 * 17.44518 + 12.42) * 6140 := mul_le_mul (by linarith) hsq hsq0 (by norm_num)
  have : (1.631 * 17.44518 + 12.42) * 6140 + 34.51 + 6.600009 ≤ (251100 : ℝ) := by norm_num
  linarith

end LeanLab.HelfgottMajor
