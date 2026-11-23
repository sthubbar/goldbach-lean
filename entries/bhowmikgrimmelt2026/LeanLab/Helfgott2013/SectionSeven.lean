module

public import Mathlib
public import LeanLab.Helfgott2013.Conclusion

/-!
P0001 H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2,
Sections 7.1 to 7.3, pages 56 to 69: the printed arithmetic of the norm bounds (7.3) and
(7.5), the major arc total (7.24), and the minor arc total (7.26) to (7.48).
Read from the arXiv PDF through pdftotext, cloud session 20261018T1720Z-cloud5.

Only the arithmetic between displayed numbers is checked. The analytic inputs, the
integrals computed with VNODE-LP, Theorem 6.3, the norm values cited from [Hela], are NOT
proved here; where a step needs one it is a hypothesis.

AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Helfgott2013
open Real

/-! ### More elementary bounds -/

set_option exponentiation.threshold 2000 in
/-- `log 7 < (1603/571) log 2`, from `7^571 < 2^1603`. -/
theorem log_seven_lt_ratio : Real.log 7 < 1603 / 571 * Real.log 2 := by
  have hn : (7 : ℕ) ^ 571 < 2 ^ 1603 := by norm_num
  have h : (7 : ℝ) ^ 571 < 2 ^ 1603 := by exact_mod_cast hn
  have h' := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h'
  push_cast at h'
  linarith

set_option exponentiation.threshold 10000 in
/-- `(9029/2718) log 2 < log 10`, from `2^9029 < 10^2718`. -/
theorem log_ten_gt_ratio : 9029 / 2718 * Real.log 2 < Real.log 10 := by
  have hn : (2 : ℕ) ^ 9029 < 10 ^ 2718 := by norm_num
  have h : (2 : ℝ) ^ 9029 < 10 ^ 2718 := by exact_mod_cast hn
  have h' := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h'
  push_cast at h'
  linarith

theorem log_49_lt : Real.log 49 < 3.8918212 := by
  have e : Real.log 49 = 2 * Real.log 7 := by
    rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := log_seven_lt_ratio
  have := Real.log_two_lt_d9
  rw [e]; linarith

theorem sqrt_pi_half_gt : (1.25331413 : ℝ) < Real.sqrt (π / 2) := by
  rw [Real.lt_sqrt (by norm_num)]
  have := Real.pi_gt_d20; linarith

theorem sqrt_pi_half_lt : Real.sqrt (π / 2) < 1.25331414 := by
  rw [Real.sqrt_lt' (by norm_num)]
  have := Real.pi_lt_d20; linarith

/-- `log u ≤ log u₀ + u/u₀ − 1` for `0 < u₀ ≤ u`. -/
theorem log_le_lin {u u0 : ℝ} (h0 : 0 < u0) (h : u0 ≤ u) :
    Real.log u ≤ Real.log u0 + (u / u0 - 1) := by
  have hu : 0 < u := lt_of_lt_of_le h0 h
  have h1 := Real.log_le_sub_one_of_pos (div_pos hu h0)
  rw [Real.log_div hu.ne' h0.ne'] at h1; linarith

/-- `log (4.9 · 10^26) = 2 log 7 + 25 log 10 < 61.456455`. -/
theorem log_xplus_lt : Real.log 4.9e26 < 61.456455 := by
  have e : Real.log 4.9e26 = 2 * Real.log 7 + 25 * Real.log 10 := by
    rw [show (4.9e26 : ℝ) = 7 ^ 2 * 10 ^ 25 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; push_cast; ring
  have := log_seven_lt_ratio
  have := log_ten_lt_ratio
  have := Real.log_two_lt_d9
  rw [e]; linarith

/-- For `x ≥ x₊ = 4.9 · 10^26`, with `u = √x ≥ u₀ = 2.2135943 · 10^13`:
`log x ≤ 2 (30.7282275 + u/u₀ − 1)`. -/
theorem log_x_le {x : ℝ} (hx : 4.9e26 ≤ x) :
    Real.log x ≤ 2 * (30.7282275 + (Real.sqrt x / 2.2135943e13 - 1)) := by
  have hx0 : 0 ≤ x := by linarith
  have hu0 : (2.2135943e13 : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx0]; linarith
  have hl := log_le_lin (by norm_num) hu0
  have hlu0 : Real.log 2.2135943e13 ≤ 30.7282275 := by
    have : (2.2135943e13 : ℝ) ^ 2 ≤ 4.9e26 := by norm_num
    have h := Real.log_le_log (by positivity) this
    rw [Real.log_pow] at h; push_cast at h
    have := log_xplus_lt; linarith
  have hlx : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← Real.sq_sqrt hx0]
    rw [Real.log_pow]; push_cast; ring
  rw [hlx]; linarith

/-! ### (7.3) and (7.5): `200^{7/2}` -/

theorem rpow_200_sq : ((200 : ℝ) ^ (7 / 2 : ℝ)) ^ 2 = 200 ^ 7 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

theorem rpow_200_ge : (1.13137e8 : ℝ) ≤ (200 : ℝ) ^ (7 / 2 : ℝ) := by
  have h := rpow_200_sq
  have h0 : 0 ≤ (200 : ℝ) ^ (7 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  nlinarith

/-- (7.3): `|η+|₂ ≤ 0.800129 + 274.8569/200^{7/2} ≤ 0.800132`. MATCHES, value 0.80013143. -/
theorem etaPlus_two : (0.800129 : ℝ) + 274.8569 / (200 : ℝ) ^ (7 / 2 : ℝ) ≤ 0.800132 := by
  have h := rpow_200_ge
  have : 274.8569 / (200 : ℝ) ^ (7 / 2 : ℝ) ≤ 274.8569 / 1.13137e8 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h
  have : (274.8569 : ℝ) / 1.13137e8 ≤ 0.000003 := by norm_num
  linarith

/-- (7.5): `274.856893/H^{7/2} ≤ 2.42942 · 10^-6` at `H = 200`. MATCHES, value 2.4294147e-6. -/
theorem eta_diff_75 : (274.856893 : ℝ) / (200 : ℝ) ^ (7 / 2 : ℝ) ≤ 2.42942e-6 := by
  have h := rpow_200_ge
  have : 274.856893 / (200 : ℝ) ^ (7 / 2 : ℝ) ≤ 274.856893 / 1.13137e8 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h
  have : (274.856893 : ℝ) / 1.13137e8 ≤ 2.42942e-6 := by norm_num
  linarith

/-! ### The major arc total, (7.24) and (7.25) -/

/-- (7.24), second display: with `|ϕ|₁ = √(π/2)` and `|η◦|₂ ≥ 0.8001287` from (7.4),
`1.3203236 · |ϕ|₁ |η◦|₂² ≥ 1.0594001`. MATCHES, margin `3 · 10^-8`. -/
theorem C0C_main {e : ℝ} (he : 0.8001287 ≤ e) :
    (1.0594001 : ℝ) ≤ 1.3203236 * (Real.sqrt (π / 2) * e ^ 2) := by
  have hs := sqrt_pi_half_gt
  have he2 : (0.8001287 : ℝ) ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ (by norm_num) he 2
  have : (1.0594001 : ℝ) ≤ 1.3203236 * (1.25331413 * 0.8001287 ^ 2) := by norm_num
  have : 1.3203236 * (1.25331413 * (0.8001287 : ℝ) ^ 2) ≤
      1.3203236 * (Real.sqrt (π / 2) * e ^ 2) := by gcongr
  linarith

/-- (7.24): `1.3203236 · 0.000834 ≤ 0.001102`. MATCHES. -/
theorem C0C_err : (1.3203236 : ℝ) * 0.000834 ≤ 0.001102 := by norm_num

/-- `(log x)² ≤ 4 · 30.7282275² · (√x/u₀)²`, the form used for small terms. -/
theorem log_sq_le {x : ℝ} (hx : 4.9e26 ≤ x) :
    Real.log x ^ 2 ≤ 4 * 30.7282275 ^ 2 * (x / 2.2135943e13 ^ 2) := by
  have hx0 : 0 ≤ x := by linarith
  have hl := log_x_le hx
  have hu0 : (2.2135943e13 : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx0]; linarith
  set t := Real.sqrt x / 2.2135943e13 with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ (by norm_num)]; linarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hle : Real.log x ≤ 2 * 30.7282275 * t := by nlinarith
  have ht2 : t ^ 2 = x / 2.2135943e13 ^ 2 := by
    rw [ht, div_pow, Real.sq_sqrt hx0]
  rw [← ht2]
  nlinarith

/-- (7.24): `2.9387 · 10^-5 |ϕ|₁ + 1.7815 · 10^-6 + κ · 43 (log x)²/x ≤ 3.8613 · 10^-5` for
`x ≥ 4.9 · 10^26`. MATCHES, value 3.86126e-5. -/
theorem major_err {x : ℝ} (hx : 4.9e26 ≤ x) :
    2.9387e-5 * Real.sqrt (π / 2) + 1.7815e-6 + κ * 43 * Real.log x ^ 2 / x ≤ (3.8613e-5 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hs := sqrt_pi_half_lt
  have hl := log_sq_le hx
  have hsmall : κ * 43 * Real.log x ^ 2 / x ≤ κ * 43 * (4 * 30.7282275 ^ 2 / 2.2135943e13 ^ 2) := by
    rw [div_le_iff₀ hx0]
    have : κ * 43 * (4 * 30.7282275 ^ 2 / 2.2135943e13 ^ 2) * x =
        κ * 43 * (4 * 30.7282275 ^ 2 * (x / 2.2135943e13 ^ 2)) := by ring
    rw [this]; unfold κ; nlinarith
  have : κ * 43 * (4 * 30.7282275 ^ 2 / 2.2135943e13 ^ 2) ≤ (1e-15 : ℝ) := by unfold κ; norm_num
  linarith

/-- (7.24): `3.8613 · 10^-5/κ ≤ 7.881 · 10^-7`. MATCHES. -/
theorem major_err_div : (3.8613e-5 : ℝ) / κ ≤ 7.881e-7 := by unfold κ; norm_num

/-- (7.25): `1.058298/κ − 7.881 · 10^-7 ≥ 1.058259/κ`. MATCHES. -/
theorem major_total : (1.058259 : ℝ) / κ ≤ 1.058298 / κ - 7.881e-7 := by unfold κ; norm_num

/-! ### The minor arc total, (7.26) to (7.48) -/

/-- `C_{η+,2} = 0.51941 |η+|∞² ≤ 0.60579`. MATCHES, value 0.6057893. -/
theorem C_etaPlus_2 : (0.51941 : ℝ) * 1.079955 ^ 2 ≤ 0.60579 := by norm_num

/-- (7.26), coefficients: `2.3375 + 0.60579 ≤ 2.9433` and `2 · 2.3375 + 0.4494 = 5.1244`.
MATCHES. -/
theorem E_coeffs : (2.3375 : ℝ) + 0.60579 ≤ 2.9433 ∧ (2 : ℝ) * 2.3375 + 0.4494 = 5.1244 := by
  constructor <;> norm_num

/-- (7.26): `(2.9433 log x + 5.1244) x^{1/2} ≤ 8.4031 · 10^-12 x` for `x ≥ 4.9 · 10^26`.
MATCHES; at `x = 4.9 · 10^26` the ratio is `8.40304 · 10^-12`. -/
theorem E_bound {x : ℝ} (hx : 4.9e26 ≤ x) :
    (2.9433 * Real.log x + 5.1244) * Real.sqrt x ≤ 8.4031e-12 * x := by
  have hx0 : 0 ≤ x := by linarith
  have hl := log_x_le hx
  have hu0 : (2.2135943e13 : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx0]; linarith
  set u := Real.sqrt x with hu
  have hux : u * u = x := Real.mul_self_sqrt hx0
  have hupos : 0 < u := by linarith
  -- linear in `u`: `2.9433 · 2 (30.7282275 + u/u₀ − 1) + 5.1244 ≤ 8.4031e-12 u`
  have key : 2.9433 * Real.log x + 5.1244 ≤ 8.4031e-12 * u := by
    have hdiv : u / 2.2135943e13 = u * (1 / 2.2135943e13) := by ring
    rw [hdiv] at hl
    have hc : (0 : ℝ) ≤ 8.4031e-12 - 2.9433 * 2 * (1 / 2.2135943e13) := by norm_num
    have hstep : (8.4031e-12 - 2.9433 * 2 * (1 / 2.2135943e13)) * 2.2135943e13 ≤
        (8.4031e-12 - 2.9433 * 2 * (1 / 2.2135943e13)) * u :=
      mul_le_mul_of_nonneg_left hu0 hc
    have hbase : 2.9433 * (2 * (30.7282275 - 1)) + 5.1244 ≤
        (8.4031e-12 - 2.9433 * 2 * (1 / (2.2135943e13 : ℝ))) * 2.2135943e13 := by norm_num
    nlinarith
  calc (2.9433 * Real.log x + 5.1244) * u ≤ 8.4031e-12 * u * u :=
        mul_le_mul_of_nonneg_right key hupos.le
    _ = 8.4031e-12 * x := by rw [← hux]; ring

/-- (7.27): `(|ϕ|₁ + 1.9075 · 10^-8) · 8.4031 · 10^-12 ≤ 1.0532 · 10^-11`. MATCHES. -/
theorem SE_coeff : (Real.sqrt (π / 2) + 1.9075e-8) * 8.4031e-12 ≤ (1.0532e-11 : ℝ) := by
  have := sqrt_pi_half_lt
  nlinarith

/-- (7.29): `(√(8.7052 − 0.0754) − √(8.4031 · 10^-12))² ≥ 8.6297`. MATCHES, value 8.629783. -/
theorem J_bound :
    (8.6297 : ℝ) ≤ (Real.sqrt (8.7052 - 0.0754) - Real.sqrt 8.4031e-12) ^ 2 := by
  have h1 : (2.93765 : ℝ) ≤ Real.sqrt (8.7052 - 0.0754) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h2 : Real.sqrt 8.4031e-12 ≤ (2.9e-6 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h3 : 0 ≤ Real.sqrt (8.4031e-12 : ℝ) := Real.sqrt_nonneg _
  have : (2.93765 : ℝ) - 2.9e-6 ≤ Real.sqrt (8.7052 - 0.0754) - Real.sqrt 8.4031e-12 := by linarith
  have : ((2.93765 : ℝ) - 2.9e-6) ^ 2 ≤
      (Real.sqrt (8.7052 - 0.0754) - Real.sqrt 8.4031e-12) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) this 2
  have : (8.6297 : ℝ) ≤ (2.93765 - 2.9e-6) ^ 2 := by norm_num
  linarith

/-- (7.30), coefficients: `0.2779 · 0.640209 ≤ 0.17792`, with `8 · 0.17792 = 1.42336`, and
`0.2779 (0.021095 + 8.6297) ≥ 2.40405`. MATCHES. -/
theorem T_coeffs : (0.2779 : ℝ) * 0.640209 ≤ 0.17792 ∧ (8 : ℝ) * 0.17792 = 1.42336 ∧
    (2.40405 : ℝ) ≤ 0.2779 * (0.021095 + 8.6297) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- (7.30): splitting `log x = log(x/κ) + log 49`, the `1/(log x/κ)³` coefficient is
`1.42336 log 49 − 8 · 2.40405 ≤ −13.69288`. MATCHES, value −13.692937. -/
theorem T_split : (1.42336 : ℝ) * Real.log 49 - 8 * 2.40405 ≤ -13.69288 := by
  have := log_49_lt
  linarith

/-- (7.30): for `L = log(x/κ) ≥ log 10^25`, `1.42336/L² − 13.69288/L³ ≤ 3.5776 · 10^-4`.
MATCHES, value 3.5775578e-4 at `L = 25 log 10`. -/
theorem T_final {L : ℝ} (hL : 25 * Real.log 10 ≤ L) :
    1.42336 / L ^ 2 - 13.69288 / L ^ 3 ≤ (3.5776e-4 : ℝ) := by
  have h10 := log_ten_gt_ratio
  have h2 := Real.log_two_gt_d9
  have hL0 : (57.5646 : ℝ) ≤ L := by nlinarith
  have hLpos : 0 < L := by linarith
  have e : 1.42336 / L ^ 2 - 13.69288 / L ^ 3 = (1.42336 * L - 13.69288) / L ^ 3 := by
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  -- `g(L) = 3.5776e-4 L³ − 1.42336 L + 13.69288` is nonnegative at 57.5646 and increasing
  have hg0 : 0 ≤ (3.5776e-4 : ℝ) * 57.5646 ^ 3 - 1.42336 * 57.5646 + 13.69288 := by norm_num
  have hd : 0 ≤ L - 57.5646 := by linarith
  have hq : 0 ≤ (3.5776e-4 : ℝ) * (L ^ 2 + L * 57.5646 + 57.5646 ^ 2) - 1.42336 := by nlinarith
  nlinarith [mul_nonneg hd hq]

/-- (7.35): `17.4347 − 8.6297 ≤ 8.805` and `0.041061 · 8.805 ≤ 0.36155`. MATCHES.
The text first prints `g(r₀) ≤ 0.041014` and then uses the larger `0.041061`, harmless. -/
theorem M_main : (17.4347 : ℝ) - 8.6297 ≤ 8.805 ∧ (0.041061 : ℝ) * 8.805 ≤ 0.36155 := by
  constructor <;> norm_num

/-- (7.35): with `x log x/(½ log x + 0.6294) = 2x − 1.2588 x/(½ log x + 0.6294)`,
`13.6164 · 2 · 0.640209 ≤ 17.4347` and `13.6164 (1.2588 · 0.640209 + 0.021095) ≥ 11.2606`.
MATCHES. -/
theorem M_split : (13.6164 : ℝ) * 2 * 0.640209 ≤ 17.4347 ∧
    (11.2606 : ℝ) ≤ 13.6164 * (2 * 0.6294 * 0.640209 + 0.021095) := by
  constructor <;> norm_num

/-- (7.47): `0.36155 + 0.30386 + 0.111292 ≤ 0.77671`. MATCHES. -/
theorem M_total : (0.36155 : ℝ) + 0.30386 + 0.111292 ≤ 0.77671 := by norm_num

/-- (7.48), numbers: `(√(|ϕ|₁ (0.77671 + 3.5776 · 10^-4)) + √(1.0532 · 10^-11))² ≤ 0.97392`.
MATCHES, value 0.9739164. -/
theorem minor_number :
    (Real.sqrt (Real.sqrt (π / 2) * (0.77671 + 3.5776e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤
      (0.97392 : ℝ) := by
  have hs := sqrt_pi_half_lt
  have hs0 : 0 ≤ Real.sqrt (π / 2) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (Real.sqrt (π / 2) * (0.77671 + 3.5776e-4)) ≤ (0.9868688 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have h2 : Real.sqrt 1.0532e-11 ≤ (3.2454e-6 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h0 : 0 ≤ Real.sqrt (Real.sqrt (π / 2) * (0.77671 + 3.5776e-4)) + Real.sqrt 1.0532e-11 :=
    by positivity
  have : (Real.sqrt (Real.sqrt (π / 2) * (0.77671 + 3.5776e-4)) + Real.sqrt 1.0532e-11) ^ 2 ≤
      (0.9868688 + 3.2454e-6) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
  have : ((0.9868688 : ℝ) + 3.2454e-6) ^ 2 ≤ 0.97392 := by norm_num
  linarith

/-- (7.48) as an implication: with `M ≤ 0.77671 x`, `T ≤ 3.5776 · 10^-4 x` and
`S_{η*}(0, x) · E ≤ 1.0532 · 10^-11 x²/κ`, Theorem 6.3's bound
`(√(|ϕ|₁ x (M + T)/κ) + √(S_{η*}(0, x) E))²` is at most `0.97392 x²/κ`. PROVED; the three
bounds and Theorem 6.3 itself are the paper's, taken as hypotheses. -/
theorem minor_total {x M T P : ℝ} (hx : 0 ≤ x) (hMT : 0 ≤ M + T) (hM : M ≤ 0.77671 * x)
    (hT : T ≤ 3.5776e-4 * x) (hP0 : 0 ≤ P) (hP : P ≤ 1.0532e-11 * x ^ 2 / κ) :
    (Real.sqrt (Real.sqrt (π / 2) * x * (M + T) / κ) + Real.sqrt P) ^ 2 ≤ 0.97392 * x ^ 2 / κ := by
  have hs := sqrt_pi_half_lt
  have hs0 : 0 ≤ Real.sqrt (π / 2) := Real.sqrt_nonneg _
  set y := x / 7 with hy
  have hy0 : 0 ≤ y := by positivity
  have hk : x ^ 2 / κ = y ^ 2 := by rw [hy]; unfold κ; ring
  set A := Real.sqrt (Real.sqrt (π / 2) * x * (M + T) / κ) with hA
  set B := Real.sqrt P with hB
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hA2 : A ^ 2 ≤ 0.9868688 ^ 2 * y ^ 2 := by
    rw [hA, Real.sq_sqrt (by unfold κ; positivity)]
    have hMT' : M + T ≤ (0.77671 + 3.5776e-4) * x := by linarith
    have : Real.sqrt (π / 2) * x * (M + T) ≤ Real.sqrt (π / 2) * x * ((0.77671 + 3.5776e-4) * x) :=
      mul_le_mul_of_nonneg_left hMT' (mul_nonneg hs0 hx)
    have : Real.sqrt (π / 2) * x * (M + T) / κ ≤
        Real.sqrt (π / 2) * (0.77671 + 3.5776e-4) * (x ^ 2 / κ) := by
      have hk0 : (0 : ℝ) < κ := by unfold κ; norm_num
      rw [div_le_iff₀ hk0]
      have : Real.sqrt (π / 2) * (0.77671 + 3.5776e-4) * (x ^ 2 / κ) * κ =
          Real.sqrt (π / 2) * x * ((0.77671 + 3.5776e-4) * x) := by field_simp
      linarith
    rw [hk] at this
    have hc : Real.sqrt (π / 2) * (0.77671 + 3.5776e-4) ≤ (0.9868688 : ℝ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg y]
  have hB2 : B ^ 2 ≤ 3.2454e-6 ^ 2 * y ^ 2 := by
    rw [hB, Real.sq_sqrt hP0]
    have : (1.0532e-11 : ℝ) * x ^ 2 / κ = 1.0532e-11 * (x ^ 2 / κ) := by ring
    rw [this, hk] at hP
    nlinarith [sq_nonneg y]
  have hA' : A ≤ 0.9868688 * y := by
    by_contra h; push Not at h; nlinarith
  have hB' : B ≤ 3.2454e-6 * y := by
    by_contra h; push Not at h; nlinarith
  have hsum : A + B ≤ (0.9868688 + 3.2454e-6) * y := by linarith
  have : (A + B) ^ 2 ≤ ((0.9868688 + 3.2454e-6) * y) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsum 2
  have e : (0.97392 : ℝ) * x ^ 2 / κ = 0.97392 * y ^ 2 := by
    rw [← hk]; ring
  rw [e]
  have : ((0.9868688 : ℝ) + 3.2454e-6) ^ 2 ≤ 0.97392 := by norm_num
  nlinarith [sq_nonneg y]

end LeanLab.Helfgott2013
