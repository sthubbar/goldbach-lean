module

public import Mathlib

/-!
P0001 H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2,
Section 7.4 "Conclusion: proof of main theorem", pages 69 to 71, with the constants it uses
from (7.3), (7.14), (7.19) and (7.24). Read from the arXiv PDF through pdftotext,
cloud session 20261018T1720Z-cloud5.

Every printed number in the final chain is checked here, and the chain itself is proved as
an implication between real numbers: if the major plus minor arc total is at least
0.08433 x²/κ and the terms with a non-prime or even nᵢ add at most 7.3306 N^{3/2} log N,
then the odd prime part is at least 0.000422 N² > 0 for every N ≥ 10^27.
The analytic inputs, (7.25), (7.48), [RS62] and the norm bounds, are NOT proved here.

AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Helfgott2013
open Real

/-! ### Elementary bounds on `log 2`, `log 10`, `π`, `√(2π)` -/

set_option exponentiation.threshold 3000 in
/-- `log 10 < (2136/643) log 2`, from `10^643 < 2^2136`. -/
theorem log_ten_lt_ratio : Real.log 10 < 2136 / 643 * Real.log 2 := by
  have hn : (10 : ℕ) ^ 643 < 2 ^ 2136 := by norm_num
  have h : (10 : ℝ) ^ 643 < 2 ^ 2136 := by exact_mod_cast hn
  have h' := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h'
  push_cast at h'
  linarith

theorem log_ten_lt : Real.log 10 < 2.302586 := by
  have := log_ten_lt_ratio
  have := Real.log_two_lt_d9
  linarith

/-- `log 200 = log 2 + 2 log 10 < 5.298318`. -/
theorem log_200_lt : Real.log 200 < 5.298318 := by
  have e : Real.log 200 = Real.log 2 + 2 * Real.log 10 := by
    rw [show (200 : ℝ) = 2 * 10 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have := log_ten_lt_ratio
  have := Real.log_two_lt_d9
  rw [e]; linarith

theorem sqrt_two_pi_gt : (2.50662 : ℝ) < Real.sqrt (2 * π) := by
  rw [Real.lt_sqrt (by norm_num)]
  have := Real.pi_gt_d6; nlinarith

theorem sqrt_two_pi_lt : Real.sqrt (2 * π) < 2.50663 := by
  rw [Real.sqrt_lt' (by norm_num)]
  have := Real.pi_lt_d6; nlinarith

/-! ### (7.14): `x = N / (2 + c₁/κ)` with `c₁ = 9/(4√(2π))`, `κ = 49` -/

/-- `κ = 49`. -/
def κ : ℝ := 49

/-- The ratio `x / N = 1 / (2 + 9/(196 √(2π)))`. -/
noncomputable def ratio : ℝ := 1 / (2 + 9 / (196 * Real.sqrt (2 * π)))

/-- `x = ratio · N`, as in (7.14). -/
noncomputable def xOf (N : ℝ) : ℝ := ratio * N

theorem ratio_bounds : 0.495461 < ratio ∧ ratio < 0.495462 := by
  have h1 := sqrt_two_pi_gt
  have h2 := sqrt_two_pi_lt
  have hs : 0 < Real.sqrt (2 * π) := by linarith
  have hc1 : 9 / (196 * Real.sqrt (2 * π)) < 9 / (196 * 2.50662) := by
    apply div_lt_div_of_pos_left (by norm_num) (by norm_num); nlinarith
  have hc2 : 9 / (196 * 2.50663) < 9 / (196 * Real.sqrt (2 * π)) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity); nlinarith
  have hc0 : 0 < 9 / (196 * Real.sqrt (2 * π)) := by positivity
  unfold ratio
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    calc (0.495461 : ℝ) * (2 + 9 / (196 * Real.sqrt (2 * π)))
        < 0.495461 * (2 + 9 / (196 * 2.50662)) := by gcongr
      _ < 1 := by norm_num
  · rw [div_lt_iff₀ (by positivity)]
    calc (1 : ℝ) < 0.495462 * (2 + 9 / (196 * 2.50663)) := by norm_num
      _ < 0.495462 * (2 + 9 / (196 * Real.sqrt (2 * π))) := by gcongr

/-- (7.15): for `N ≥ 10^27`, `x ≥ 4.9 · 10^26` and `x/κ ≥ 10^25`. MATCHES. -/
theorem x_bounds {N : ℝ} (hN : 1e27 ≤ N) : 4.9e26 ≤ xOf N ∧ 1e25 ≤ xOf N / κ := by
  have := ratio_bounds.1
  have hx : 4.9e26 ≤ xOf N := by unfold xOf; nlinarith
  refine ⟨hx, ?_⟩
  unfold κ; rw [le_div_iff₀ (by norm_num)]; linarith

/-- The coefficient in the last display: `0.08433 · ratio² / κ ≥ 0.00042248`. MATCHES,
the true value is `0.000422480334...`. -/
theorem coeff_ge : (0.00042248 : ℝ) ≤ 0.08433 * ratio ^ 2 / κ := by
  have h1 := sqrt_two_pi_gt
  have hs : 0 < Real.sqrt (2 * π) := by linarith
  have hc : 9 / (196 * Real.sqrt (2 * π)) < 9 / (196 * 2.50662) := by
    apply div_lt_div_of_pos_left (by norm_num) (by norm_num); nlinarith
  have hc0 : 0 < 9 / (196 * Real.sqrt (2 * π)) := by positivity
  have hr : 1 / (2 + 9 / (196 * 2.50662)) ≤ ratio := by
    unfold ratio
    apply one_div_le_one_div_of_le (by positivity); linarith
  have hr0 : (0 : ℝ) ≤ 1 / (2 + 9 / (196 * 2.50662)) := by norm_num
  unfold κ
  rw [le_div_iff₀ (by norm_num)]
  calc (0.00042248 : ℝ) * 49 ≤ 0.08433 * (1 / (2 + 9 / (196 * 2.50662))) ^ 2 := by norm_num
    _ ≤ 0.08433 * ratio ^ 2 := by gcongr

/-! ### The printed constants of Section 7 -/

/-- (7.24): `1.0594001/κ − 0.001102/κ ≥ 1.058298/κ`. MATCHES. -/
theorem major_724 : (1.058298 : ℝ) / κ ≤ 1.0594001 / κ - 0.001102 / κ := by
  unfold κ; norm_num

/-- Major arcs `1.058259 x²/κ` against minor arcs `0.97392 x²/κ`:
`1.058259 − 0.97392 ≥ 0.08433`. MATCHES, the difference is `0.084339`. -/
theorem major_minus_minor : (0.08433 : ℝ) ≤ 1.058259 - 0.97392 := by norm_num

/-- (7.3): `1 + 2.06440727 (1 + (4/π) log H)/H ≤ 1.079955` at `H = 200`. MATCHES,
the true value is `1.0799547742...`, margin `2.3 · 10^-7`. -/
theorem etaPlus_sup : 1 + 2.06440727 * (1 + 4 / π * Real.log 200) / 200 ≤ (1.079955 : ℝ) := by
  have hl := log_200_lt
  have hl0 : 0 < Real.log 200 := Real.log_pos (by norm_num)
  have hp := Real.pi_gt_d6
  have h4 : 4 / π < 4 / 3.141592 := div_lt_div_of_pos_left (by norm_num) (by norm_num) hp
  have : 4 / π * Real.log 200 < 4 / 3.141592 * 5.298318 := by
    calc 4 / π * Real.log 200 < 4 / 3.141592 * Real.log 200 := by gcongr
      _ < 4 / 3.141592 * 5.298318 := by gcongr
  have : (1 : ℝ) + 2.06440727 * (1 + 4 / 3.141592 * 5.298318) / 200 ≤ 1.079955 := by norm_num
  nlinarith

/-- (7.19): `4 (log 2)² · 2/e ≤ 1.414`. MATCHES, the true value is `1.41399029...`. -/
theorem etaStar_sup : 4 * Real.log 2 ^ 2 * (2 / Real.exp 1) ≤ (1.414 : ℝ) := by
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  have he := Real.exp_one_gt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hd : 2 / Real.exp 1 < 2 / 2.7182818283 := div_lt_div_of_pos_left (by norm_num)
    (by norm_num) he
  have hl : Real.log 2 ^ 2 < 0.6931471808 ^ 2 := by
    apply pow_lt_pow_left₀ h2 (by linarith) (by norm_num)
  have : (4 : ℝ) * 0.6931471808 ^ 2 * (2 / 2.7182818283) ≤ 1.414 := by norm_num
  have hl0 : 0 ≤ Real.log 2 ^ 2 := sq_nonneg _
  have hd0 : 0 ≤ 2 / Real.exp 1 := by positivity
  nlinarith

/-- [RS62] step: `1.4262 √N + log 2 < 1.4263 √N` for `N ≥ 10^27`. MATCHES. -/
theorem rs62_step {N : ℝ} (hN : 1e27 ≤ N) :
    1.4262 * Real.sqrt N + Real.log 2 < 1.4263 * Real.sqrt N := by
  have hs : (1e13 : ℝ) ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have := Real.log_two_lt_d9
  linarith

/-- `1.4263 · 1.03883 ≤ 1.48169`. MATCHES, the product is `1.481683229`. -/
theorem rs62_product : (1.4263 : ℝ) * 1.03883 ≤ 1.48169 := by norm_num

/-- `3 |η+|∞² |η*|∞ · 1.48169 ≤ 7.3306` with `|η+|∞ ≤ 1.079955`, `|η*|∞ ≤ 1.414`. MATCHES,
the product is `7.3305968...`. -/
theorem nonprime_coeff : (3 : ℝ) * 1.079955 ^ 2 * 1.414 * 1.48169 ≤ 7.3306 := by norm_num

/-- The same with the norm bounds as hypotheses. -/
theorem nonprime_coeff_of {a b : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1.079955) (hb0 : 0 ≤ b)
    (hb : b ≤ 1.414) : 3 * a ^ 2 * b * 1.48169 ≤ (7.3306 : ℝ) := by
  have : a ^ 2 ≤ 1.079955 ^ 2 := pow_le_pow_left₀ ha0 ha 2
  have := nonprime_coeff
  have : 3 * a ^ 2 * b * 1.48169 ≤ 3 * 1.079955 ^ 2 * 1.414 * 1.48169 := by gcongr
  linarith

/-- `N^{3/2} = (√N)^3` for `N ≥ 0`. -/
theorem rpow_three_halves {N : ℝ} (hN : 0 ≤ N) : N ^ (3 / 2 : ℝ) = Real.sqrt N ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN]; norm_num

/-- `7.3306 N^{3/2} log N ≤ 1.4412 · 10^-11 N²` for `N ≥ 10^27`. MATCHES; at `N = 10^27` the
left side over `N²` is `1.44118... · 10^-11`. -/
theorem error_le {N : ℝ} (hN : 1e27 ≤ N) :
    7.3306 * N ^ (3 / 2 : ℝ) * Real.log N ≤ 1.4412e-11 * N ^ 2 := by
  have hN0 : 0 ≤ N := by linarith
  have h32 := rpow_three_halves hN0
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.sqrt N := ⟨_, rfl⟩
  rw [← hu] at h32
  have hu2 : u ^ 2 = N := by rw [hu]; exact Real.sq_sqrt hN0
  rw [h32]
  subst hu2
  obtain ⟨u0, hu0d⟩ : ∃ u0 : ℝ, u0 = 3.16227766e13 := ⟨_, rfl⟩
  have hu0pos : 0 < u0 := by rw [hu0d]; norm_num
  have hupos0 : 0 ≤ u := by rw [hu]; exact Real.sqrt_nonneg _
  have hu0 : u0 ≤ u := by
    have : u0 ^ 2 ≤ u ^ 2 := by rw [hu0d]; norm_num; linarith
    nlinarith
  have hupos : 0 < u := lt_of_lt_of_le hu0pos hu0
  -- `log u0 ≤ (27/2) log 10`, since `u0² ≤ 10^27`
  have hlu0 : Real.log u0 ≤ 27 / 2 * Real.log 10 := by
    have : u0 ^ 2 ≤ (10 : ℝ) ^ 27 := by rw [hu0d]; norm_num
    have h := Real.log_le_log (by positivity) this
    rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith
  -- `log u ≤ log u0 + u/u0 − 1`
  have hlu : Real.log u ≤ Real.log u0 + (u / u0 - 1) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hupos hu0pos)
    rw [Real.log_div hupos.ne' hu0pos.ne'] at h1; linarith
  have hl10 := log_ten_lt
  have hlogN : Real.log (u ^ 2) = 2 * Real.log u := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlogN]
  -- `14.6612 log u ≤ 1.4412e-11 u`, linear in `u` once `log u` is bounded
  have key : 7.3306 * (2 * Real.log u) ≤ 1.4412e-11 * u := by
    have hdiv : u / u0 = u * (1 / u0) := by ring
    have hc : (1.4412e-11 : ℝ) - 7.3306 * 2 * (1 / u0) > 0 := by rw [hu0d]; norm_num
    have hbase : 7.3306 * (2 * (27 / 2 * 2.302586 - 1)) ≤
        (1.4412e-11 - 7.3306 * 2 * (1 / u0)) * u0 := by
      rw [hu0d]; norm_num
    have hstep : (1.4412e-11 - 7.3306 * 2 * (1 / u0)) * u0 ≤
        (1.4412e-11 - 7.3306 * 2 * (1 / u0)) * u := mul_le_mul_of_nonneg_left hu0 hc.le
    rw [hdiv] at hlu
    nlinarith
  have hu3 : 0 ≤ u ^ 3 := by positivity
  calc 7.3306 * u ^ 3 * (2 * Real.log u) = u ^ 3 * (7.3306 * (2 * Real.log u)) := by ring
    _ ≤ u ^ 3 * (1.4412e-11 * u) := mul_le_mul_of_nonneg_left key hu3
    _ = 1.4412e-11 * (u ^ 2) ^ 2 := by ring

/-- `0.00042248 − 1.4412 · 10^-11 ≥ 0.000422`. MATCHES. -/
theorem final_coeff : (0.000422 : ℝ) ≤ 0.00042248 - 1.4412e-11 := by norm_num

/-! ### The chain of Section 7.4 -/

/-- Section 7.4, the last display, as an implication between real numbers. `T` is the
weighted sum over all `n₁ + n₂ + n₃ = N`, `E` its part with some `nᵢ` even or non-prime, so
`T − E` is the odd prime part. From the major and minor arc bounds `T ≥ 0.08433 x²/κ`,
and `E ≤ 7.3306 N^{3/2} log N`, we get `T − E ≥ 0.000422 N² > 0` for every `N ≥ 10^27`.
PROVED; the two bounds on `T` and `E` are hypotheses, the paper's (7.25), (7.48), (7.50). -/
theorem conclusion_chain {N T E : ℝ} (hN : 1e27 ≤ N)
    (hT : 0.08433 * xOf N ^ 2 / κ ≤ T) (hE : E ≤ 7.3306 * N ^ (3 / 2 : ℝ) * Real.log N) :
    0.000422 * N ^ 2 ≤ T - E ∧ 0 < T - E := by
  have h1 : 0.00042248 * N ^ 2 ≤ 0.08433 * xOf N ^ 2 / κ := by
    have hc := coeff_ge
    have : 0.08433 * xOf N ^ 2 / κ = (0.08433 * ratio ^ 2 / κ) * N ^ 2 := by
      unfold xOf; ring
    rw [this]; exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have h2 := error_le hN
  have hN2 : 0 < N ^ 2 := by positivity
  constructor
  · nlinarith [final_coeff]
  · nlinarith [final_coeff]

/-- The major and minor arc totals combine as printed: if the major arc integral is at
least `1.058259 x²/κ` and the minor arc part is at most `0.97392 x²/κ` in absolute value,
the whole integral is at least `0.08433 x²/κ`. -/
theorem arcs_combine {x M m : ℝ} (hM : 1.058259 * x ^ 2 / κ ≤ M) (hm : |m| ≤ 0.97392 * x ^ 2 / κ) :
    0.08433 * x ^ 2 / κ ≤ M + m := by
  have := (abs_le.mp hm).1
  have hx : 0 ≤ x ^ 2 / κ := by unfold κ; positivity
  have e1 : 1.058259 * x ^ 2 / κ = 1.058259 * (x ^ 2 / κ) := by ring
  have e2 : 0.97392 * x ^ 2 / κ = 0.97392 * (x ^ 2 / κ) := by ring
  have e3 : 0.08433 * x ^ 2 / κ = 0.08433 * (x ^ 2 / κ) := by ring
  rw [e1] at hM; rw [e2] at this; rw [e3]
  nlinarith

end LeanLab.Helfgott2013
