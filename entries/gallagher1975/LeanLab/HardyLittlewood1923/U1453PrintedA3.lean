module

public import LeanLab.HardyLittlewood1923.U1438Circle
public import LeanLab.HardyLittlewood1923.U1444PrintedA

/-!
AI-written Lean code, Claude, 2026-10-22, CLOUD run 20261022T0003Z-15508, unit U-1453, paper P0004.

# Hardy-Littlewood 1923, Theorem A for r = 3 at the printed exponent, upper range of Θ

Printed, eq. (3.113) p. 21: on Hypothesis R at level `Θ < 3/4`,
`ν₃(n) = n²/2 · S₃(n) + O(n^{2 + (Θ - 3/4)} (log n)^B)`.

* `PsiPowerLog θ`: `|ψ(x; k, l) - x/φ(k)| ≤ C x^θ (log x)²` for `x ≥ 2`, `(l, k) = 1`, `k ≤ x`.
* `ExplicitFormulaLog`: the cited step, no zeros of any `L(s, χ)` in `Re s > Θ` gives
  `PsiPowerLog Θ`; the truncated explicit formula, Davenport ch. 19 and 20. NOT proved here.
* `major_of_psiPowerLog`: the major arc approximation from `PsiPowerLog θ`.
* `r3_rate_of_psiPowerLog`: for `0 ≤ θ < 1`, `PsiPowerLog θ` gives
  `|r₃(n) - n²/2 · 𝔖₃(n)| ≤ K n^{2 - (1-θ)/17} (1 + log n)⁵`, a saving `(1-θ)/17`, against
  `(1-θ)/96` of `r3Power_of_psiPower`. The parameters are `P ≈ n^{2δ}`, `Q ≈ n^{1-5δ}`,
  `δ = (1-θ)/17`, which balances the lab's minor arc bound against its major arc error.
* `printedA3Bound_of_psiPowerLog`: for `47/64 ≤ Θ < 3/4`, `PsiPowerLog Θ` gives the printed bound
  `printedA3Bound Θ`, with `B = 5`, since `(1-Θ)/17 ≥ 3/4 - Θ` exactly when `Θ ≥ 47/64`.
* `printedA3_upper`: CONDITIONAL ON `ExplicitFormulaLog`, the printed Theorem A for `r = 3` holds
  for every `Θ ∈ [47/64, 3/4)`.
* `printedA3_upper_of_R`: the same on the open range `47/64 < Θ < 3/4` CONDITIONAL ON U-1438's
  cited `PsiPowerOfR`.

The range `Θ < 47/64`, in particular `Θ = 1/2`, is NOT reached: the lab's minor arc bound saves at
most `n^{1/5}` and its major arc error grows like `P³ n^{3+θ}/Q²`. Binary Goldbach is OPEN.

Packaging note: in this copy the cited Props of this file and the theorems that take them as
hypotheses were removed, as no compared theorem uses them; see PORTING.md.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1453

open Real Finset Filter
open scoped ArithmeticFunction.Moebius
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.U1444
open LeanLab.PNTPort.Vinogradov (S V Aq r3 J singP singP_eq_fS norm_Aq_sub_le norm_Aq_le
  major_of_bound ternary_explicit lp_bound sum_vonMangoldt_sq_le fS)

/-- Primes in progressions with error `C x^θ (log x)²`, uniform in `k ≤ x`. -/
def PsiPowerLog (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ x →
    |LeanLab.HeathBrown1985.psi x k l - x / (Nat.totient k : ℝ)| ≤ C * x ^ θ * Real.log x ^ 2

lemma log_two_sq_pos : 0 < Real.log 2 ^ 2 := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity

/-- `PsiPower θ` implies `PsiPowerLog θ`. -/
theorem psiPowerLog_of_psiPower {θ : ℝ} (h : PsiPower θ) : PsiPowerLog θ := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C / Real.log 2 ^ 2, by have := log_two_sq_pos; positivity,
    fun x hx k l hk hc hkx => (h x hx k l hk hc hkx).trans ?_⟩
  have hl2 := log_two_sq_pos
  have hlx : Real.log 2 ^ 2 ≤ Real.log x ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) (Real.log_le_log (by norm_num) hx) 2
  have hxθ : 0 ≤ C * x ^ θ := mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
  have : C * x ^ θ * Real.log x ^ 2 / Real.log 2 ^ 2 = C / Real.log 2 ^ 2 * x ^ θ * Real.log x ^ 2 :=
    by ring
  rw [← this, le_div_iff₀ hl2]
  exact mul_le_mul_of_nonneg_left hlx hxθ

/-- Vacuity of the form: `PsiPowerLog 1` holds, from Chebyshev. -/
theorem psiPowerLog_one : PsiPowerLog 1 := psiPowerLog_of_psiPower psiPower_one

/-- The major arc approximation from `PsiPowerLog θ`. -/
theorem major_of_psiPowerLog {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (h : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ x →
      |LeanLab.HeathBrown1985.psi x k l - x / (Nat.totient k : ℝ)| ≤ C * x ^ θ * Real.log x ^ 2)
    {N : ℕ} (hN : 1 ≤ N) {q : ℕ} (hq : 1 ≤ q) (a : ℤ) (hcop : IsCoprime a (q : ℤ)) (β : ℝ) :
    ‖S N (a / q + β) - (μ q : ℂ) / q.totient * V N β‖ ≤
      q * (7 + C * (N : ℝ) ^ θ * Real.log N ^ 2 + 2 * Real.log N) * (1 + 2 * π * |β| * N) := by
  apply major_of_bound hq a N β
  intro n hn
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hNθ : 0 ≤ C * (N : ℝ) ^ θ * Real.log N ^ 2 := by positivity
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  have htot : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  by_cases hsmall : n < 2 ∨ (n : ℝ) < q
  · have hnq : (n : ℝ) ≤ q := by
      rcases hsmall with h1 | h1
      · have : (n : ℝ) ≤ 1 := by exact_mod_cast (by omega : n ≤ 1)
        linarith
      · exact h1.le
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 := norm_Aq_le q a n
    have h2 : ‖(μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖ ≤ n := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hμ : ‖(μ q : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc ‖(μ q : ℂ)‖ * ((n : ℝ) / q.totient) ≤ 1 * n :=
            mul_le_mul hμ (div_le_self hn0 htot) (by positivity) zero_le_one
        _ = n := one_mul _
    have h4 : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    calc ‖Aq q a n - (μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖
        ≤ ‖Aq q a n‖ + ‖(μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖ := norm_sub_le _ _
      _ ≤ (Real.log 4 + 4) * n + n := add_le_add h1 h2
      _ ≤ 7 * q := by nlinarith
      _ ≤ q * (7 + C * (N : ℝ) ^ θ * Real.log N ^ 2 + 2 * Real.log N) := by nlinarith
  · push_neg at hsmall
    obtain ⟨hn2, hqn⟩ := hsmall
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hlogn : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hterm : ∀ r ∈ (range q).filter (fun r => Nat.Coprime r q),
        |LeanLab.HeathBrown1985.psi n q r - (n : ℝ) / q.totient| ≤
          C * (N : ℝ) ^ θ * Real.log N ^ 2 := by
      intro r hr
      have hcr : Nat.Coprime r q := (mem_filter.1 hr).2
      refine (h n hn2' q r hq hcr hqn).trans ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hnN hθ) hC)
        (pow_le_pow_left₀ hlogn0 hlogn 2) (sq_nonneg _) (by positivity)
    have hsum := sum_le_sum hterm
    rw [sum_const, nsmul_eq_mul] at hsum
    have hcard : (((range q).filter (fun r => Nat.Coprime r q)).card : ℝ) ≤ q := by
      have := (card_filter_le (range q) (fun r => Nat.Coprime r q)).trans (card_range q).le
      exact_mod_cast this
    have hbad := LeanLab.PNTPort.BV.psiBad_le (x := (n : ℝ)) (by linarith) hq
    have hlp := lp_bound hqr
    have hbad' : LeanLab.PNTPort.BV.psiBad n q ≤ 2 * q * Real.log N := by
      calc LeanLab.PNTPort.BV.psiBad n q ≤ Real.log q / Real.log 2 * Real.log n := hbad
        _ ≤ 2 * q * Real.log N := mul_le_mul hlp hlogn hlogn0 (by positivity)
    calc ‖Aq q a n - (μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖
        ≤ ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q),
            |LeanLab.HeathBrown1985.psi n q r - (n : ℝ) / q.totient|
          + LeanLab.PNTPort.BV.psiBad n q := norm_Aq_sub_le q hq hcop n
      _ ≤ q * (C * (N : ℝ) ^ θ * Real.log N ^ 2) + 2 * q * Real.log N := by
          have := mul_le_mul_of_nonneg_right hcard hNθ
          linarith
      _ ≤ q * (7 + C * (N : ℝ) ^ θ * Real.log N ^ 2 + 2 * Real.log N) := by nlinarith

set_option maxHeartbeats 1000000 in
/-- The full error with the new parameters `P ≈ s⁴`, `Q ≈ x/s¹⁰`, `x^θ = x/s³⁴`. -/
lemma err_total17 {x s u L p q M C Λ2 E : ℝ} (hx : 1 ≤ x) (hs : 1 ≤ s) (hL : 0 ≤ L)
    (hu : u = 1 + L) (hC : 0 ≤ C) (hs34 : s ^ 34 ≤ x) (hx45 : x ^ ((4 : ℝ) / 5) * s ^ 2 ≤ x)
    (hp1 : 1 ≤ p) (hp : p ≤ s ^ 4) (hp2 : s ^ 4 / 2 ≤ p)
    (hq0 : 0 ≤ q) (hq : q ≤ x / s ^ 10) (hq1 : x / s ^ 10 ≤ q + 1) (hM : x ≤ M)
    (hΛ : Λ2 ≤ 6 * x * L) (hΛ0 : 0 ≤ Λ2)
    (hE0 : 0 ≤ E) (hE : E ≤ s ^ 4 * (7 + C * (x / s ^ 34) * L ^ 2 + 2 * L)) :
    300 * (x / Real.sqrt p + x ^ ((4 : ℝ) / 5) + Real.sqrt (x * q)) * (1 + L) ^ 4 * Λ2
      + p ^ 2 * (2 / (q + 1) + 1 / M) * (3 * ((Real.log 4 + 4) * x) ^ 2 *
        (E * (1 + 2 * π * x / (q + 1))))
      + x * p ^ 2 * (q + 1) / 2 ≤
    (1800 * (Real.sqrt 2 + 2) + 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 + C) + 1) *
      (x ^ 2 * u ^ 5 / s ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := by linarith
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hp0 : 0 < p := by linarith
  have hM0 : 0 < M := by linarith
  have hLu : L ≤ u := by rw [hu]; linarith
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have s2le8 : s ^ 2 ≤ s ^ 8 := pow_le_pow_right₀ hs (by norm_num)
  have s2le5 : s ^ 2 ≤ s ^ 5 := pow_le_pow_right₀ hs (by norm_num)
  have s10 : s ^ 10 ≤ x := le_trans (pow_le_pow_right₀ hs (by norm_num)) hs34
  have hs10 : (0 : ℝ) < s ^ 10 := by positivity
  set B := x ^ 2 * u ^ 5 / s ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hx2B : x ^ 2 / s ^ 2 ≤ B := by
    rw [hB]
    calc x ^ 2 / s ^ 2 = x ^ 2 * 1 / s ^ 2 := by ring
      _ ≤ x ^ 2 * u ^ 5 / s ^ 2 := by
          apply div_le_div_of_nonneg_right _ hs2.le
          exact mul_le_mul_of_nonneg_left (one_le_pow₀ hu1) (by positivity)
  -- T1
  have hsp : s ^ 2 / Real.sqrt 2 ≤ Real.sqrt p := by
    apply le_sqrt_of_sq (by positivity)
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    calc (s ^ 2) ^ 2 / 2 = s ^ 4 / 2 := by ring
      _ ≤ p := hp2
  have hsq2 : 0 < Real.sqrt 2 := by positivity
  have a1 : x / Real.sqrt p ≤ Real.sqrt 2 * (x / s ^ 2) := by
    calc x / Real.sqrt p ≤ x / (s ^ 2 / Real.sqrt 2) :=
          div_le_div_of_nonneg_left hx0.le (by positivity) hsp
      _ = Real.sqrt 2 * (x / s ^ 2) := by field_simp
  have a2 : x ^ ((4 : ℝ) / 5) ≤ x / s ^ 2 := by rw [le_div_iff₀ hs2]; exact hx45
  have a3 : Real.sqrt (x * q) ≤ x / s ^ 2 := by
    have h8 : x * q ≤ (x / s ^ 5) ^ 2 := by
      calc x * q ≤ x * (x / s ^ 10) := mul_le_mul_of_nonneg_left hq hx0.le
        _ = (x / s ^ 5) ^ 2 := by field_simp <;> ring
    calc Real.sqrt (x * q) ≤ Real.sqrt ((x / s ^ 5) ^ 2) := Real.sqrt_le_sqrt h8
      _ = x / s ^ 5 := Real.sqrt_sq (by positivity)
      _ ≤ x / s ^ 2 := div_le_div_of_nonneg_left hx0.le hs2 s2le5
  have a4 : (1 + L) ^ 4 * Λ2 ≤ 6 * x * u ^ 5 := by
    rw [← hu]
    calc u ^ 4 * Λ2 ≤ u ^ 4 * (6 * x * L) := mul_le_mul_of_nonneg_left hΛ (by positivity)
      _ ≤ u ^ 4 * (6 * x * u) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hLu (by positivity)
      _ = 6 * x * u ^ 5 := by ring
  have T1 : 300 * (x / Real.sqrt p + x ^ ((4 : ℝ) / 5) + Real.sqrt (x * q)) * (1 + L) ^ 4 * Λ2
      ≤ 1800 * (Real.sqrt 2 + 2) * B := by
    have hsum : x / Real.sqrt p + x ^ ((4 : ℝ) / 5) + Real.sqrt (x * q) ≤
        (Real.sqrt 2 + 2) * (x / s ^ 2) := by linarith
    calc 300 * (x / Real.sqrt p + x ^ ((4 : ℝ) / 5) + Real.sqrt (x * q)) * (1 + L) ^ 4 * Λ2
        = 300 * (x / Real.sqrt p + x ^ ((4 : ℝ) / 5) + Real.sqrt (x * q)) * ((1 + L) ^ 4 * Λ2) := by
          ring
      _ ≤ 300 * ((Real.sqrt 2 + 2) * (x / s ^ 2)) * (6 * x * u ^ 5) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hsum (by norm_num)) a4 (by positivity)
          positivity
      _ = 1800 * (Real.sqrt 2 + 2) * B := by rw [hB]; field_simp <;> ring
  -- T2
  have b1 : p ^ 2 ≤ s ^ 8 := by
    calc p ^ 2 ≤ (s ^ 4) ^ 2 := pow_le_pow_left₀ (by linarith) hp 2
      _ = s ^ 8 := by ring
  have hq1' : 0 < q + 1 := by linarith
  have hxs : 0 < x / s ^ 10 := by positivity
  have b2 : 2 / (q + 1) + 1 / M ≤ 3 * s ^ 10 / x := by
    have c1 : 2 / (q + 1) ≤ 2 * s ^ 10 / x := by
      calc 2 / (q + 1) ≤ 2 / (x / s ^ 10) := div_le_div_of_nonneg_left (by norm_num) hxs hq1
        _ = 2 * s ^ 10 / x := by field_simp
    have c2 : 1 / M ≤ s ^ 10 / x := by
      calc 1 / M ≤ 1 / x := div_le_div_of_nonneg_left (by norm_num) hx0 hM
        _ ≤ s ^ 10 / x := div_le_div_of_nonneg_right (one_le_pow₀ hs) hx0.le
    have : 2 * s ^ 10 / x + s ^ 10 / x = 3 * s ^ 10 / x := by ring
    linarith
  have b3 : 1 + 2 * π * x / (q + 1) ≤ (1 + 2 * π) * s ^ 10 := by
    have c1 : x / (q + 1) ≤ s ^ 10 := by
      rw [div_le_iff₀ hq1']
      have := (div_le_iff₀ hs10).1 hq1
      linarith
    have := one_le_pow₀ (n := 10) hs
    have hπ := Real.pi_pos
    calc 1 + 2 * π * x / (q + 1) = 1 + 2 * π * (x / (q + 1)) := by ring
      _ ≤ s ^ 10 + 2 * π * s ^ 10 := by nlinarith
      _ = (1 + 2 * π) * s ^ 10 := by ring
  have hM0' : 0 ≤ 2 / (q + 1) + 1 / M := by positivity
  have hE' : E * (1 + 2 * π * x / (q + 1)) ≤
      s ^ 4 * (7 + C * (x / s ^ 34) * L ^ 2 + 2 * L) * ((1 + 2 * π) * s ^ 10) := by
    have h1 : 0 ≤ 2 * π * x / (q + 1) := by have := Real.pi_pos; positivity
    apply mul_le_mul hE b3 (by linarith) (by positivity)
  have T2 : p ^ 2 * (2 / (q + 1) + 1 / M) * (3 * ((Real.log 4 + 4) * x) ^ 2 *
        (E * (1 + 2 * π * x / (q + 1)))) ≤
      9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 + C) * B := by
    have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hπ := Real.pi_pos
    have step : p ^ 2 * (2 / (q + 1) + 1 / M) * (3 * ((Real.log 4 + 4) * x) ^ 2 *
        (E * (1 + 2 * π * x / (q + 1)))) ≤
        s ^ 8 * (3 * s ^ 10 / x) * (3 * ((Real.log 4 + 4) * x) ^ 2 *
        (s ^ 4 * (7 + C * (x / s ^ 34) * L ^ 2 + 2 * L) * ((1 + 2 * π) * s ^ 10))) := by
      apply mul_le_mul (mul_le_mul b1 b2 hM0' (by positivity)) _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hE' (by positivity)
    have hval : s ^ 8 * (3 * s ^ 10 / x) * (3 * ((Real.log 4 + 4) * x) ^ 2 *
        (s ^ 4 * (7 + C * (x / s ^ 34) * L ^ 2 + 2 * L) * ((1 + 2 * π) * s ^ 10))) =
        9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) *
          (x * s ^ 32 * (7 + 2 * L) + C * (L ^ 2 * (x ^ 2 / s ^ 2))) := by
      field_simp <;> ring
    have d1 : x * s ^ 32 * (7 + 2 * L) ≤ 9 * B := by
      have e1 : x * s ^ 32 ≤ x ^ 2 / s ^ 2 := by
        rw [le_div_iff₀ hs2]
        calc x * s ^ 32 * s ^ 2 = x * s ^ 34 := by ring
          _ ≤ x * x := mul_le_mul_of_nonneg_left hs34 hx0.le
          _ = x ^ 2 := by ring
      have hu5 : u ≤ u ^ 5 := by
        calc u = u ^ 1 := (pow_one u).symm
          _ ≤ u ^ 5 := pow_le_pow_right₀ hu1 (by norm_num)
      have e9 : 7 + 2 * L ≤ 9 * u := by rw [hu]; linarith
      have e2 : 7 + 2 * L ≤ 9 * u ^ 5 := by linarith
      calc x * s ^ 32 * (7 + 2 * L) ≤ (x ^ 2 / s ^ 2) * (9 * u ^ 5) :=
            mul_le_mul e1 e2 (by linarith) (by positivity)
        _ = 9 * B := by rw [hB]; ring
    have d2 : C * (L ^ 2 * (x ^ 2 / s ^ 2)) ≤ C * B := by
      apply mul_le_mul_of_nonneg_left _ hC
      have hL2 : L ^ 2 ≤ u ^ 5 := by
        calc L ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hL hLu 2
          _ ≤ u ^ 5 := pow_le_pow_right₀ hu1 (by norm_num)
      rw [hB]
      calc L ^ 2 * (x ^ 2 / s ^ 2) ≤ u ^ 5 * (x ^ 2 / s ^ 2) :=
            mul_le_mul_of_nonneg_right hL2 (by positivity)
        _ = x ^ 2 * u ^ 5 / s ^ 2 := by ring
    rw [hval] at step
    have hc0 : 0 ≤ 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) := by positivity
    calc _ ≤ _ := step
      _ ≤ 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 * B + C * B) :=
          mul_le_mul_of_nonneg_left (add_le_add d1 d2) hc0
      _ = _ := by ring
  -- T3
  have T3 : x * p ^ 2 * (q + 1) / 2 ≤ B := by
    have e1 : x * p ^ 2 * (q + 1) ≤ x * s ^ 8 * (x / s ^ 10 + 1) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left b1 hx0.le) (by linarith) hq1'.le (by positivity)
    have e2 : x * s ^ 8 * (x / s ^ 10 + 1) = x ^ 2 / s ^ 2 + x * s ^ 8 := by field_simp <;> ring
    have e4 : x * s ^ 8 ≤ x ^ 2 / s ^ 2 := by
      rw [le_div_iff₀ hs2]
      calc x * s ^ 8 * s ^ 2 = x * s ^ 10 := by ring
        _ ≤ x * x := mul_le_mul_of_nonneg_left s10 hx0.le
        _ = x ^ 2 := by ring
    linarith
  have : (1800 * (Real.sqrt 2 + 2) + 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 + C) + 1) * B =
      1800 * (Real.sqrt 2 + 2) * B + 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 + C) * B + B := by
    ring
  linarith

set_option maxHeartbeats 4000000 in
/-- **The rate**: `PsiPowerLog θ` with `0 ≤ θ < 1` gives
`|r₃(n) - n²/2 · 𝔖₃(n)| ≤ K n^{2 - (1-θ)/17} (1 + log n)⁵` for all large `n`. -/
theorem r3_rate_of_psiPowerLog {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hψ : PsiPowerLog θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |r3 n n - sing3 n * (n : ℝ) ^ 2 / 2| ≤
        K * ((n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 5) := by
  obtain ⟨C, hC, h⟩ := hψ
  set η := 2 * (1 - θ) / 17 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hη1 : η ≤ 2 / 17 := by rw [hηdef]; linarith
  set C0 := 1800 * (Real.sqrt 2 + 2) + 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 + C) + 1
    with hC0
  have hC00 : 0 ≤ C0 := by have := Real.pi_pos; rw [hC0]; positivity
  refine ⟨C0 + 3 * Real.exp 8, by positivity, max 3 ⌈(2 : ℝ) ^ (1 / η)⌉₊, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_left _ _) hn
  set x := (n : ℝ) with hxdef
  have hx3 : (3 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hn3
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set s := x ^ (η / 4) with hsdef
  have hs1 : 1 ≤ s := Real.one_le_rpow hx1 (by positivity)
  have hs0 : 0 < s := by linarith
  have hsk : ∀ k : ℕ, s ^ k = x ^ (η / 4 * k) := fun k => pow_rpow_eq hx0.le _ k
  have hs4 : s ^ 4 = x ^ η := by rw [hsk]; congr 1; push_cast; ring
  have hs4_2 : 2 ≤ s ^ 4 := by
    rw [hs4]
    have hc : (2 : ℝ) ^ (1 / η) ≤ x := by
      have : ⌈(2 : ℝ) ^ (1 / η)⌉₊ ≤ n := le_trans (le_max_right _ _) hn
      exact (Nat.le_ceil _).trans (by rw [hxdef]; exact_mod_cast this)
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / η)) ^ η := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hη.ne', Real.rpow_one]
      _ ≤ x ^ η := Real.rpow_le_rpow (by positivity) hc hη.le
  have hs34 : s ^ 34 ≤ x := by
    rw [hsk]
    calc x ^ (η / 4 * ((34 : ℕ) : ℝ)) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; rw [hηdef]; nlinarith)
      _ = x := Real.rpow_one x
  have hx45 : x ^ ((4 : ℝ) / 5) * s ^ 2 ≤ x := by
    rw [hsk, ← Real.rpow_add hx0]
    calc x ^ ((4 : ℝ) / 5 + η / 4 * ((2 : ℕ) : ℝ)) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; nlinarith)
      _ = x := Real.rpow_one x
  have hθs : x ^ θ = x / s ^ 34 := by
    rw [hsk, show η / 4 * ((34 : ℕ) : ℝ) = 1 - θ by rw [hηdef]; push_cast; ring]
    rw [eq_div_iff (by positivity), ← Real.rpow_add hx0, show θ + (1 - θ) = 1 by ring,
      Real.rpow_one]
  -- the parameters
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = ⌊s ^ 4⌋₊ := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = ⌊x / s ^ 10⌋₊ := ⟨_, rfl⟩
  have hp : (P : ℝ) ≤ s ^ 4 := by rw [hPdef]; exact Nat.floor_le (by positivity)
  have hp2 : s ^ 4 / 2 ≤ (P : ℝ) := by
    have : s ^ 4 < (P : ℝ) + 1 := by rw [hPdef]; exact Nat.lt_floor_add_one _
    linarith
  have hp1 : (1 : ℝ) ≤ P := by linarith
  have hP1 : 1 ≤ P := by exact_mod_cast hp1
  have hs10 : s ^ 10 ≤ x := le_trans (pow_le_pow_right₀ hs1 (by norm_num)) hs34
  have hs10p : (0 : ℝ) < s ^ 10 := by positivity
  have hq : (Q : ℝ) ≤ x / s ^ 10 := by rw [hQdef]; exact Nat.floor_le (by positivity)
  have hq1 : x / s ^ 10 ≤ Q + 1 := by
    have : x / s ^ 10 < (Q : ℝ) + 1 := by rw [hQdef]; exact Nat.lt_floor_add_one _
    linarith
  have hQ1 : 1 ≤ Q := by
    rw [hQdef]
    exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hs10p, one_mul]; exact hs10)
  have hQN : Q ≤ n := by
    have : (Q : ℝ) ≤ n := hq.trans (div_le_self hx0.le (one_le_pow₀ hs1))
    exact_mod_cast this
  have hs_gt : 1 < s := by
    by_contra hle
    push_neg at hle
    have : s ^ 4 ≤ 1 := pow_le_one₀ hs0.le hle
    linarith
  have h18 : 2 * s ^ 18 < x := by
    have a1 : 2 * s ^ 18 ≤ s ^ 4 * s ^ 18 := mul_le_mul_of_nonneg_right hs4_2 (by positivity)
    have a2 : s ^ 4 * s ^ 18 = s ^ 22 := by ring
    have a3 : s ^ 22 < s ^ 34 := pow_lt_pow_right₀ hs_gt (by norm_num)
    linarith
  have hPQ : 2 / ((Q : ℝ) + 1) < 1 / (P : ℝ) ^ 2 := by
    have hxs : 0 < x / s ^ 10 := by positivity
    have c1 : 2 / ((Q : ℝ) + 1) ≤ 2 * s ^ 10 / x := by
      calc 2 / ((Q : ℝ) + 1) ≤ 2 / (x / s ^ 10) := div_le_div_of_nonneg_left (by norm_num) hxs hq1
        _ = 2 * s ^ 10 / x := by field_simp
    have c2 : 2 * s ^ 10 / x < 1 / s ^ 8 := by
      rw [div_lt_div_iff₀ hx0 (by positivity)]
      calc 2 * s ^ 10 * s ^ 8 = 2 * s ^ 18 := by ring
        _ < x := h18
        _ = 1 * x := (one_mul x).symm
    have c3 : 1 / s ^ 8 ≤ 1 / (P : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      calc (P : ℝ) ^ 2 ≤ (s ^ 4) ^ 2 := pow_le_pow_left₀ (by linarith) hp 2
        _ = s ^ 8 := by ring
    linarith
  have : NeZero (3 * n + 1) := ⟨by omega⟩
  set E := (P : ℝ) * (7 + C * x ^ θ * Real.log x ^ 2 + 2 * Real.log x) with hEdef
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hE0 : 0 ≤ E := by positivity
  have hmaj : ∀ q ∈ Icc 1 P, ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S n (a' / q + β) - (μ q : ℂ) / q.totient * V n β‖ ≤ E * (1 + 2 * π * |β| * n) := by
    intro q hq a' hcop β
    rw [mem_Icc] at hq
    refine (major_of_psiPowerLog hθ0 hC h (by omega) hq.1 a' hcop β).trans ?_
    apply mul_le_mul_of_nonneg_right _ (by have := Real.pi_pos; positivity)
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hq.2) (by positivity)
  have hTE := ternary_explicit (N := n) (M := 3 * n + 1) (P := P) (Q := Q) (n := n)
    (by omega) (by omega) hP1 hQ1 hQN hPQ hE0 hmaj
  have hsP : s ^ 2 / Real.sqrt 2 ≤ Real.sqrt P := by
    apply le_sqrt_of_sq (by positivity)
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    calc (s ^ 2) ^ 2 / 2 = s ^ 4 / 2 := by ring
      _ ≤ (P : ℝ) := hp2
  have hE : E ≤ s ^ 4 * (7 + C * (x / s ^ 34) * Real.log x ^ 2 + 2 * Real.log x) := by
    rw [hEdef, ← hθs]
    exact mul_le_mul_of_nonneg_right hp (by positivity)
  have hM : x ≤ ((3 * n + 1 : ℕ) : ℝ) := by rw [hxdef]; exact_mod_cast (by omega : n ≤ 3 * n + 1)
  have herr := err_total17 (x := x) (s := s) (u := 1 + Real.log x) (L := Real.log x) (p := P)
    (q := Q) (M := ((3 * n + 1 : ℕ) : ℝ)) (C := C)
    (Λ2 := ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m ^ 2)
    (E := E) hx1 hs1 hlog0 rfl hC hs34 hx45 hp1 hp hp2 (Nat.cast_nonneg Q) hq hq1 hM
    (sum_vonMangoldt_sq_le n) (sum_nonneg fun _ _ => sq_nonneg _) hE0 hE
  rw [← hC0] at herr
  have hreal : (r3 n n : ℂ) - (J n n : ℂ) * singP P n =
      ((r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q : ℝ) : ℂ) := by
    rw [singP_eq_fS]; push_cast; ring
  rw [hreal, Complex.norm_real, Real.norm_eq_abs] at hTE
  have h1 : |r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q| ≤
      C0 * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) := hTE.trans herr
  have hs2x : s ^ 2 ≤ x := le_trans (pow_le_pow_right₀ hs1 (by norm_num)) hs34
  have h2 := main_term_err hn3 hP1 hs1 hsP hs2x
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hu1 : (1 : ℝ) ≤ (1 + Real.log x) ^ 5 := one_le_pow₀ (by linarith)
  have hB : x ^ 2 / s ^ 2 ≤ x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2 := by
    apply div_le_div_of_nonneg_right _ hs2.le
    have := mul_le_mul_of_nonneg_left hu1 (sq_nonneg x)
    linarith
  have hfin : x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2 =
      x ^ (2 - (1 - θ) / 17) * (1 + Real.log x) ^ 5 := by
    have e2 : s ^ 2 = x ^ ((1 - θ) / 17) := by
      rw [hsk]; congr 1; rw [hηdef]; push_cast; ring
    rw [e2, Real.rpow_sub hx0, show (x : ℝ) ^ (2 : ℝ) = x ^ 2 from Real.rpow_two x]
    ring
  calc |r3 n n - sing3 n * x ^ 2 / 2|
      = |(r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q) +
          (J n n * ∑ q ∈ Icc 1 P, fS n q - sing3 n * x ^ 2 / 2)| := by congr 1; ring
    _ ≤ |r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q| +
          |J n n * ∑ q ∈ Icc 1 P, fS n q - sing3 n * x ^ 2 / 2| := abs_add_le _ _
    _ ≤ C0 * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) +
          3 * Real.exp 8 * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) := by
        apply add_le_add h1
        exact h2.trans (mul_le_mul_of_nonneg_left hB (by positivity))
    _ = (C0 + 3 * Real.exp 8) * (x ^ (2 - (1 - θ) / 17) * (1 + Real.log x) ^ 5) := by
        rw [← hfin]; ring

/-- The rate for prime weights `ν₃`, via `r3_sub_nur3_power`. -/
theorem nur3_rate_of_psiPowerLog {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hψ : PsiPowerLog θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n| ≤
        K * ((n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 5) := by
  obtain ⟨K, hK, n₀, h⟩ := r3_rate_of_psiPowerLog hθ0 hθ1 hψ
  obtain ⟨C₁, hC₁, hpp⟩ := r3_sub_nur3_power
  refine ⟨K + C₁, by positivity, max n₀ 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have e1 := h n (le_trans (le_max_left _ _) hn)
  have e2 := hpp n hn2
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hu1 : (1 : ℝ) ≤ (1 + Real.log n) ^ 5 := one_le_pow₀ (by linarith)
  have k1 : (n : ℝ) ^ ((7 : ℝ) / 4) ≤ (n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 5 := by
    have : (n : ℝ) ^ ((7 : ℝ) / 4) ≤ (n : ℝ) ^ (2 - (1 - θ) / 17) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have h0 : 0 ≤ (n : ℝ) ^ (2 - (1 - θ) / 17) := by positivity
    nlinarith
  calc |nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n|
      = |(r3 n n - sing3 n * (n : ℝ) ^ 2 / 2) - (r3 n n - nur 3 n)| := by congr 1; ring
    _ ≤ |r3 n n - sing3 n * (n : ℝ) ^ 2 / 2| + |r3 n n - nur 3 n| := abs_sub _ _
    _ ≤ K * ((n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 5) +
          C₁ * ((n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 5) := by
        have := mul_le_mul_of_nonneg_left k1 hC₁
        linarith
    _ = (K + C₁) * ((n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 5) := by ring

/-- **The printed bound for `47/64 ≤ Θ < 3/4`** from `PsiPowerLog Θ`, with `B = 5`. -/
theorem printedA3Bound_of_psiPowerLog {Θ : ℝ} (hΘ0 : 47 / 64 ≤ Θ) (hΘ1 : Θ < 3 / 4)
    (hψ : PsiPowerLog Θ) : printedA3Bound Θ := by
  obtain ⟨K, hK, n₀, h⟩ := nur3_rate_of_psiPowerLog (by linarith) (by linarith) hψ
  refine ⟨5, by norm_num, 32 * K, max n₀ 3, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hn3'
  have hm := h n (le_trans (le_max_left _ _) hn)
  have hexp : (n : ℝ) ^ (2 - (1 - Θ) / 17) ≤ (n : ℝ) ^ (2 + (Θ - 3 / 4)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hl5 : (1 + Real.log n) ^ 5 ≤ 32 * Real.log n ^ (5 : ℝ) := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (1 + Real.log n) ^ 5 ≤ (2 * Real.log n) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
      _ = 32 * Real.log n ^ 5 := by ring
  have h0 : 0 ≤ (n : ℝ) ^ (2 - (1 - Θ) / 17) := by positivity
  calc |nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n|
      ≤ K * ((n : ℝ) ^ (2 - (1 - Θ) / 17) * (1 + Real.log n) ^ 5) := hm
    _ ≤ K * ((n : ℝ) ^ (2 + (Θ - 3 / 4)) * (32 * Real.log n ^ (5 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact mul_le_mul hexp hl5 (by positivity) (by positivity)
    _ = 32 * K * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ (5 : ℝ) := by ring

/-- Vacuity of the range: `Θ = 47/64` lies in it, `47/64 < 3/4`. -/
theorem range_nonempty : (47 : ℝ) / 64 < 3 / 4 := by norm_num

end LeanLab.HardyLittlewood1923.U1453

