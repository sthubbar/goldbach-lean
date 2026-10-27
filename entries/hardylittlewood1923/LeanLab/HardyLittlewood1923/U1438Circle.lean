module

public import LeanLab.HardyLittlewood1923.U1438TheoremA
public import LeanLab.PNTPort.Vinogradov.TernaryAsymp

/-!
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T1603Z-28836, unit U-1438, paper P0004.

# Hardy-Littlewood 1923, Theorem A for r = 3, conditional on a power saving for primes in
# progressions

* `PsiPower θ`: `|ψ(x; k, l) - x/φ(k)| ≤ C x^θ` for `x ≥ 2`, `(l, k) = 1`, `k ≤ x`. This is the
  analytic input. On Hypothesis R, no zeros of `L(s, χ)` in `Re s > Θ`, the explicit formula gives
  it for every `θ > Θ`; that implication is the cited `PsiPowerOfR`, not proved here.
* `major_of_psiPower`: the major arc approximation `S(a/q + β) ≈ μ(q)/φ(q) V(β)` with error
  `q (7 + C N^θ + 2 log N)(1 + 2π|β|N)`, for every `q ≤ N`.
* `r3Power_of_psiPower`: for `0 ≤ θ < 1`, `PsiPower θ` gives `R3Power`, hence Theorem A,
  `theoremA3_of_psiPower`. The minor arcs are the lab's unconditional Vinogradov bound,
  `PNTPort.Vinogradov.ternary_explicit`; the major arcs are taken up to `P = n^η`,
  `η = (1 - θ)/24`, and `δ = η/4`.
* `theoremA3_of_R`: Theorem A CONDITIONAL ON `HypothesisR` and the cited `PsiPowerOfR`.

This is the Vinogradov route with Hardy and Littlewood's hypothesis in its usual explicit formula
form, not their Farey dissection with `|x| → 1`; Hypothesis R is used only through `PsiPower`,
so any `Θ < 1` would do here. Binary Goldbach is OPEN.

Packaging note: in this copy the cited Props of this file and the theorems that take them as
hypotheses were removed, as no compared theorem uses them; see PORTING.md.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1438

open Real Finset Filter
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.Vinogradov (S V Aq r3 J singP singP_eq_fS norm_Aq_sub_le norm_Aq_le
  major_of_bound ternary_explicit lp_bound sum_vonMangoldt_sq_le fS)

/-- The analytic input: primes in progressions with a power saving `x^θ`, uniform in `k ≤ x`. -/
def PsiPower (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ x →
    |LeanLab.HeathBrown1985.psi x k l - x / (Nat.totient k : ℝ)| ≤ C * x ^ θ

/-- The predicate `PsiPower` is not vacuous in form: it holds at `θ = 1`, from Chebyshev. -/
theorem psiPower_one : PsiPower 1 := by
  refine ⟨7, by norm_num, fun x hx k l hk _ _ => ?_⟩
  have h0 : 0 ≤ LeanLab.HeathBrown1985.psi x k l :=
    sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have h4 : Real.log 4 < 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have h1 : LeanLab.HeathBrown1985.psi x k l ≤ (Real.log 4 + 4) * x := by
    have hψ := Chebyshev.psi_le_const_mul_self (x := x) (by linarith)
    have : LeanLab.HeathBrown1985.psi x k l ≤ Chebyshev.psi x := by
      unfold LeanLab.HeathBrown1985.psi Chebyshev.psi
      have hI : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by ext m; simp only [mem_Ioc, mem_Icc]; omega
      rw [hI]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    linarith
  have htot : (1 : ℝ) ≤ k.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have h2 : 0 ≤ x / (k.totient : ℝ) := by positivity
  have h3 : x / (k.totient : ℝ) ≤ x := div_le_self (by linarith) htot
  rw [Real.rpow_one, abs_le]
  have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  constructor <;> nlinarith

/-- The major arc approximation from `PsiPower θ`. -/
theorem major_of_psiPower {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (h : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ x →
      |LeanLab.HeathBrown1985.psi x k l - x / (Nat.totient k : ℝ)| ≤ C * x ^ θ)
    {N : ℕ} (hN : 1 ≤ N) {q : ℕ} (hq : 1 ≤ q) (a : ℤ) (hcop : IsCoprime a (q : ℤ)) (β : ℝ) :
    ‖S N (a / q + β) - (μ q : ℂ) / q.totient * V N β‖ ≤
      q * (7 + C * (N : ℝ) ^ θ + 2 * Real.log N) * (1 + 2 * π * |β| * N) := by
  apply major_of_bound hq a N β
  intro n hn
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hNθ : 0 ≤ C * (N : ℝ) ^ θ := by positivity
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
      _ ≤ q * (7 + C * (N : ℝ) ^ θ + 2 * Real.log N) := by nlinarith
  · push_neg at hsmall
    obtain ⟨hn2, hqn⟩ := hsmall
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hterm : ∀ r ∈ (range q).filter (fun r => Nat.Coprime r q),
        |LeanLab.HeathBrown1985.psi n q r - (n : ℝ) / q.totient| ≤ C * (N : ℝ) ^ θ := by
      intro r hr
      have hcr : Nat.Coprime r q := (mem_filter.1 hr).2
      refine (h n hn2' q r hq hcr hqn).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hnN hθ) hC
    have hsum := sum_le_sum hterm
    rw [sum_const, nsmul_eq_mul] at hsum
    have hcard : (((range q).filter (fun r => Nat.Coprime r q)).card : ℝ) ≤ q := by
      have := (card_filter_le (range q) (fun r => Nat.Coprime r q)).trans (card_range q).le
      exact_mod_cast this
    have hbad := LeanLab.PNTPort.BV.psiBad_le (x := (n : ℝ)) (by linarith) hq
    have hlp := lp_bound hqr
    have hlogn : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hbad' : LeanLab.PNTPort.BV.psiBad n q ≤ 2 * q * Real.log N := by
      calc LeanLab.PNTPort.BV.psiBad n q ≤ Real.log q / Real.log 2 * Real.log n := hbad
        _ ≤ 2 * q * Real.log N := mul_le_mul hlp hlogn hlogn0 (by positivity)
    calc ‖Aq q a n - (μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖
        ≤ ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q),
            |LeanLab.HeathBrown1985.psi n q r - (n : ℝ) / q.totient|
          + LeanLab.PNTPort.BV.psiBad n q := norm_Aq_sub_le q hq hcop n
      _ ≤ q * (C * (N : ℝ) ^ θ) + 2 * q * Real.log N := by
          have := mul_le_mul_of_nonneg_right hcard hNθ
          linarith
      _ ≤ q * (7 + C * (N : ℝ) ^ θ + 2 * Real.log N) := by nlinarith

/-! ### Choosing the parameters -/

lemma one_add_log_le {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    1 + Real.log x ≤ (1 + 1 / ε) * x ^ ε := by
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) hε
  have h2 : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have : x ^ ε / ε = 1 / ε * x ^ ε := by ring
  nlinarith

lemma pow_rpow_eq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (k : ℕ) : (x ^ a) ^ k = x ^ (a * k) := by
  rw [Real.rpow_mul hx, Real.rpow_natCast]

/-- The full error against `x² u⁵/s²`, all inputs real. `x = n`, `s = n^{η/4}`, `u = 1 + log n`,
`p = P`, `q = Q`, `Λ2 = Σ Λ²`, `E` the major arc error. -/
lemma err_total {x s u L p q M C Λ2 E : ℝ} (hx : 1 ≤ x) (hs : 1 ≤ s) (hL : 0 ≤ L) (hu : u = 1 + L)
    (hC : 0 ≤ C) (hs46 : s ^ 46 ≤ x) (hx45 : x ^ ((4 : ℝ) / 5) * s ^ 2 ≤ x)
    (hp1 : 1 ≤ p) (hp : p ≤ s ^ 4) (hp2 : s ^ 4 / 2 ≤ p)
    (hq0 : 0 ≤ q) (hq : q ≤ x / s ^ 16) (hq1 : x / s ^ 16 ≤ q + 1) (hM : x ≤ M)
    (hΛ : Λ2 ≤ 6 * x * L) (hΛ0 : 0 ≤ Λ2)
    (hE0 : 0 ≤ E) (hE : E ≤ s ^ 4 * (7 + C * (x / s ^ 96) + 2 * L)) :
    300 * (x / Real.sqrt p + x ^ ((4 : ℝ) / 5) + Real.sqrt (x * q)) * (1 + L) ^ 4 * Λ2
      + p ^ 2 * (2 / (q + 1) + 1 / M) * (3 * ((Real.log 4 + 4) * x) ^ 2 *
        (E * (1 + 2 * π * x / (q + 1))))
      + x * p ^ 2 * (q + 1) / 2 ≤
    (1800 * (Real.sqrt 2 + 2) + 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 + C) + 1) *
      (x ^ 2 * u ^ 5 / s ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := by linarith
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hu0 : 0 < u := by linarith
  have hp0 : 0 < p := by linarith
  have hM0 : 0 < M := by linarith
  have hLu : L ≤ u := by rw [hu]; linarith
  have hu5 : u ≤ u ^ 5 := by
    calc u = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ 5 := pow_le_pow_right₀ hu1 (by norm_num)
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have s2le8 : s ^ 2 ≤ s ^ 8 := pow_le_pow_right₀ hs (by norm_num)
  have s10 : s ^ 10 ≤ x := le_trans (pow_le_pow_right₀ hs (by norm_num)) hs46
  have s16 : s ^ 16 ≤ x := le_trans (pow_le_pow_right₀ hs (by norm_num)) hs46
  have hs16 : (0 : ℝ) < s ^ 16 := by positivity
  set B := x ^ 2 * u ^ 5 / s ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
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
      _ = Real.sqrt 2 * (x / s ^ 2) := by field_simp <;> ring
  have a2 : x ^ ((4 : ℝ) / 5) ≤ x / s ^ 2 := by rw [le_div_iff₀ hs2]; exact hx45
  have a3 : Real.sqrt (x * q) ≤ x / s ^ 2 := by
    have h8 : x * q ≤ (x / s ^ 8) ^ 2 := by
      calc x * q ≤ x * (x / s ^ 16) := mul_le_mul_of_nonneg_left hq hx0.le
        _ = (x / s ^ 8) ^ 2 := by field_simp <;> ring
    calc Real.sqrt (x * q) ≤ Real.sqrt ((x / s ^ 8) ^ 2) := Real.sqrt_le_sqrt h8
      _ = x / s ^ 8 := Real.sqrt_sq (by positivity)
      _ ≤ x / s ^ 2 := div_le_div_of_nonneg_left hx0.le hs2 s2le8
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
  have hxs : 0 < x / s ^ 16 := by positivity
  have b2 : 2 / (q + 1) + 1 / M ≤ 3 * s ^ 16 / x := by
    have c1 : 2 / (q + 1) ≤ 2 * s ^ 16 / x := by
      calc 2 / (q + 1) ≤ 2 / (x / s ^ 16) := div_le_div_of_nonneg_left (by norm_num) hxs hq1
        _ = 2 * s ^ 16 / x := by field_simp <;> ring
    have c2 : 1 / M ≤ s ^ 16 / x := by
      calc 1 / M ≤ 1 / x := div_le_div_of_nonneg_left (by norm_num) hx0 hM
        _ ≤ s ^ 16 / x := div_le_div_of_nonneg_right (one_le_pow₀ hs) hx0.le
    have : 2 * s ^ 16 / x + s ^ 16 / x = 3 * s ^ 16 / x := by ring
    linarith
  have b3 : 1 + 2 * π * x / (q + 1) ≤ (1 + 2 * π) * s ^ 16 := by
    have c1 : x / (q + 1) ≤ s ^ 16 := by
      rw [div_le_iff₀ hq1']
      have := (div_le_iff₀ hs16).1 hq1
      linarith
    have := one_le_pow₀ (n := 16) hs
    have hπ := Real.pi_pos
    calc 1 + 2 * π * x / (q + 1) = 1 + 2 * π * (x / (q + 1)) := by ring
      _ ≤ s ^ 16 + 2 * π * s ^ 16 := by nlinarith
      _ = (1 + 2 * π) * s ^ 16 := by ring
  have hM0' : 0 ≤ 2 / (q + 1) + 1 / M := by positivity
  have hE' : E * (1 + 2 * π * x / (q + 1)) ≤
      s ^ 4 * (7 + C * (x / s ^ 96) + 2 * L) * ((1 + 2 * π) * s ^ 16) := by
    have h1 : 0 ≤ 2 * π * x / (q + 1) := by have := Real.pi_pos; positivity
    apply mul_le_mul hE b3 (by linarith) (by positivity)
  have T2 : p ^ 2 * (2 / (q + 1) + 1 / M) * (3 * ((Real.log 4 + 4) * x) ^ 2 *
        (E * (1 + 2 * π * x / (q + 1)))) ≤
      9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 + C) * B := by
    have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hπ := Real.pi_pos
    have step : p ^ 2 * (2 / (q + 1) + 1 / M) * (3 * ((Real.log 4 + 4) * x) ^ 2 *
        (E * (1 + 2 * π * x / (q + 1)))) ≤
        s ^ 8 * (3 * s ^ 16 / x) * (3 * ((Real.log 4 + 4) * x) ^ 2 *
        (s ^ 4 * (7 + C * (x / s ^ 96) + 2 * L) * ((1 + 2 * π) * s ^ 16))) := by
      apply mul_le_mul (mul_le_mul b1 b2 hM0' (by positivity)) _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hE' (by positivity)
    have hval : s ^ 8 * (3 * s ^ 16 / x) * (3 * ((Real.log 4 + 4) * x) ^ 2 *
        (s ^ 4 * (7 + C * (x / s ^ 96) + 2 * L) * ((1 + 2 * π) * s ^ 16))) =
        9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (x * s ^ 44 * (7 + 2 * L) + C * (x ^ 2 / s ^ 52)) := by
      field_simp <;> ring
    have d1 : x * s ^ 44 * (7 + 2 * L) ≤ 9 * B := by
      have e1 : x * s ^ 44 ≤ x ^ 2 / s ^ 2 := by
        rw [le_div_iff₀ hs2]
        calc x * s ^ 44 * s ^ 2 = x * s ^ 46 := by ring
          _ ≤ x * x := mul_le_mul_of_nonneg_left hs46 hx0.le
          _ = x ^ 2 := by ring
      have e2 : 7 + 2 * L ≤ 9 * u ^ 5 := by linarith
      calc x * s ^ 44 * (7 + 2 * L) ≤ (x ^ 2 / s ^ 2) * (9 * u ^ 5) :=
            mul_le_mul e1 e2 (by linarith) (by positivity)
        _ = 9 * B := by rw [hB]; ring
    have d2 : C * (x ^ 2 / s ^ 52) ≤ C * B := by
      apply mul_le_mul_of_nonneg_left _ hC
      rw [hB]
      have : s ^ 2 ≤ s ^ 52 := pow_le_pow_right₀ hs (by norm_num)
      calc x ^ 2 / s ^ 52 ≤ x ^ 2 / s ^ 2 := div_le_div_of_nonneg_left (by positivity) hs2 this
        _ = x ^ 2 * 1 / s ^ 2 := by ring
        _ ≤ x ^ 2 * u ^ 5 / s ^ 2 := by
            apply div_le_div_of_nonneg_right _ hs2.le
            exact mul_le_mul_of_nonneg_left (one_le_pow₀ hu1) (by positivity)
    rw [hval] at step
    have hc0 : 0 ≤ 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) := by positivity
    calc _ ≤ _ := step
      _ ≤ 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 * B + C * B) :=
          mul_le_mul_of_nonneg_left (add_le_add d1 d2) hc0
      _ = _ := by ring
  -- T3
  have T3 : x * p ^ 2 * (q + 1) / 2 ≤ B := by
    have e1 : x * p ^ 2 * (q + 1) ≤ x * s ^ 8 * (x / s ^ 16 + 1) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left b1 hx0.le) (by linarith) hq1'.le (by positivity)
    have e2 : x * s ^ 8 * (x / s ^ 16 + 1) = x ^ 2 / s ^ 8 + x * s ^ 8 := by field_simp <;> ring
    have e3 : x ^ 2 / s ^ 8 ≤ x ^ 2 / s ^ 2 := div_le_div_of_nonneg_left (by positivity) hs2 s2le8
    have e4 : x * s ^ 8 ≤ x ^ 2 / s ^ 2 := by
      rw [le_div_iff₀ hs2]
      calc x * s ^ 8 * s ^ 2 = x * s ^ 10 := by ring
        _ ≤ x * x := mul_le_mul_of_nonneg_left s10 hx0.le
        _ = x ^ 2 := by ring
    have e5 : x ^ 2 / s ^ 2 ≤ B := by
      rw [hB]
      calc x ^ 2 / s ^ 2 = x ^ 2 * 1 / s ^ 2 := by ring
        _ ≤ x ^ 2 * u ^ 5 / s ^ 2 := by
            apply div_le_div_of_nonneg_right _ hs2.le
            exact mul_le_mul_of_nonneg_left (one_le_pow₀ hu1) (by positivity)
    linarith
  have : (1800 * (Real.sqrt 2 + 2) + 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 + C) + 1) * B =
      1800 * (Real.sqrt 2 + 2) * B + 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 + C) * B + B := by
    ring
  linarith

/-- The main term: `|J(n) 𝔖_P(n) - ½ 𝔖₃(n) n²| ≤ 3 e⁸ n²/s²` when `√P ≥ s²/√2`, `s² ≤ n`. -/
lemma main_term_err {n P : ℕ} (hn : 3 ≤ n) (hP : 1 ≤ P) {s : ℝ} (hs : 1 ≤ s)
    (hsP : s ^ 2 / Real.sqrt 2 ≤ Real.sqrt P) (hs2n : s ^ 2 ≤ n) :
    |J n n * ∑ q ∈ Icc 1 P, fS n q - sing3 n * (n : ℝ) ^ 2 / 2| ≤
      3 * Real.exp 8 * ((n : ℝ) ^ 2 / s ^ 2) := by
  have hx3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hJ := LeanLab.VanDerCorput1939.J_self n hn
  set Sp := ∑ q ∈ Icc 1 P, fS n q with hSp
  have hSpb : |Sp| ≤ Real.exp 8 := by
    calc |Sp| ≤ ∑ q ∈ Icc 1 P, |fS n q| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Icc 1 P, LeanLab.PNTPort.Vinogradov.hS n q := sum_le_sum fun q _ => abs_fS_le_hS n q
      _ ≤ Real.exp 8 := sum_Icc_hS_le n P
  have htail := abs_partial_sub_sing3 n hP
  simp only [singTerm_eq_fS] at htail
  rw [← hSp] at htail
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hsq2 : 0 < Real.sqrt 2 := by positivity
  have hsPpos : 0 < Real.sqrt P := lt_of_lt_of_le (by positivity) hsP
  have htail' : |Sp - sing3 n| ≤ Real.sqrt 2 * Real.exp 8 / s ^ 2 := by
    refine htail.trans ?_
    calc Real.exp 8 / Real.sqrt P ≤ Real.exp 8 / (s ^ 2 / Real.sqrt 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsP
      _ = Real.sqrt 2 * Real.exp 8 / s ^ 2 := by field_simp <;> ring
  have e : J n n * Sp - sing3 n * (n : ℝ) ^ 2 / 2 =
      (J n n - (n : ℝ) ^ 2 / 2) * Sp + (n : ℝ) ^ 2 / 2 * (Sp - sing3 n) := by ring
  have hJd : |J n n - (n : ℝ) ^ 2 / 2| ≤ 3 * (n : ℝ) / 2 := by
    rw [hJ, abs_le]; constructor <;> nlinarith
  have hx_le : (n : ℝ) ≤ (n : ℝ) ^ 2 / s ^ 2 := by
    rw [le_div_iff₀ hs2]; nlinarith
  have hsq2le : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  rw [e]
  calc |(J n n - (n : ℝ) ^ 2 / 2) * Sp + (n : ℝ) ^ 2 / 2 * (Sp - sing3 n)|
      ≤ |(J n n - (n : ℝ) ^ 2 / 2) * Sp| + |(n : ℝ) ^ 2 / 2 * (Sp - sing3 n)| := abs_add_le _ _
    _ = |J n n - (n : ℝ) ^ 2 / 2| * |Sp| + (n : ℝ) ^ 2 / 2 * |Sp - sing3 n| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 2)]
    _ ≤ 3 * (n : ℝ) / 2 * Real.exp 8 + (n : ℝ) ^ 2 / 2 * (Real.sqrt 2 * Real.exp 8 / s ^ 2) := by
        apply add_le_add
        · exact mul_le_mul hJd hSpb (abs_nonneg _) (by positivity)
        · exact mul_le_mul_of_nonneg_left htail' (by positivity)
    _ ≤ 3 * (n : ℝ) ^ 2 / s ^ 2 / 2 * Real.exp 8 + (n : ℝ) ^ 2 / 2 * (2 * Real.exp 8 / s ^ 2) := by
        apply add_le_add
        · have : 3 * (n : ℝ) / 2 ≤ 3 * ((n : ℝ) ^ 2 / s ^ 2) / 2 := by linarith
          have h2 : 3 * ((n : ℝ) ^ 2 / s ^ 2) / 2 = 3 * (n : ℝ) ^ 2 / s ^ 2 / 2 := by ring
          rw [← h2]; exact mul_le_mul_of_nonneg_right this (by positivity)
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_right _ hs2.le
          exact mul_le_mul_of_nonneg_right hsq2le (by positivity)
    _ ≤ 3 * Real.exp 8 * ((n : ℝ) ^ 2 / s ^ 2) := by
        have : 3 * (n : ℝ) ^ 2 / s ^ 2 / 2 * Real.exp 8 + (n : ℝ) ^ 2 / 2 * (2 * Real.exp 8 / s ^ 2) =
            (5 / 2) * Real.exp 8 * ((n : ℝ) ^ 2 / s ^ 2) := by ring
        rw [this]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have := Real.exp_pos 8
        linarith

set_option maxHeartbeats 4000000 in
/-- **`PsiPower θ` with `0 ≤ θ < 1` gives the von Mangoldt form of Theorem A.** -/
theorem r3Power_of_psiPower {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hψ : PsiPower θ) : R3Power := by
  obtain ⟨C, hC, h⟩ := hψ
  set η := (1 - θ) / 24 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hη1 : η ≤ 1 / 24 := by rw [hηdef]; linarith
  set ε := η / 20 with hεdef
  have hε : 0 < ε := by positivity
  set Ka := (1 + 1 / ε) ^ 5 with hKa
  set C0 := 1800 * (Real.sqrt 2 + 2) + 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 + C) + 1
    with hC0
  have hC00 : 0 ≤ C0 := by have := Real.pi_pos; rw [hC0]; positivity
  refine ⟨η / 4, by positivity, (C0 + 3 * Real.exp 8) * Ka, max 3 ⌈(2 : ℝ) ^ (1 / η)⌉₊,
    fun n hn => ?_⟩
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
  have hs46 : s ^ 46 ≤ x := by
    rw [hsk]
    calc x ^ (η / 4 * ((46 : ℕ) : ℝ)) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; nlinarith)
      _ = x := Real.rpow_one x
  have hx45 : x ^ ((4 : ℝ) / 5) * s ^ 2 ≤ x := by
    rw [hsk, ← Real.rpow_add hx0]
    calc x ^ ((4 : ℝ) / 5 + η / 4 * ((2 : ℕ) : ℝ)) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; nlinarith)
      _ = x := Real.rpow_one x
  have hθs : x ^ θ = x / s ^ 96 := by
    rw [hsk, show η / 4 * ((96 : ℕ) : ℝ) = 1 - θ by rw [hηdef]; push_cast; ring]
    rw [eq_div_iff (by positivity), ← Real.rpow_add hx0, show θ + (1 - θ) = 1 by ring,
      Real.rpow_one]
  -- the parameters
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = ⌊s ^ 4⌋₊ := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = ⌊x / s ^ 16⌋₊ := ⟨_, rfl⟩
  have hp : (P : ℝ) ≤ s ^ 4 := by rw [hPdef]; exact Nat.floor_le (by positivity)
  have hp2 : s ^ 4 / 2 ≤ (P : ℝ) := by
    have : s ^ 4 < (P : ℝ) + 1 := by rw [hPdef]; exact Nat.lt_floor_add_one _
    linarith
  have hp1 : (1 : ℝ) ≤ P := by linarith
  have hP1 : 1 ≤ P := by exact_mod_cast hp1
  have hs16 : s ^ 16 ≤ x := le_trans (pow_le_pow_right₀ hs1 (by norm_num)) hs46
  have hs16p : (0 : ℝ) < s ^ 16 := by positivity
  have hq : (Q : ℝ) ≤ x / s ^ 16 := by rw [hQdef]; exact Nat.floor_le (by positivity)
  have hq1 : x / s ^ 16 ≤ Q + 1 := by
    have : x / s ^ 16 < (Q : ℝ) + 1 := by rw [hQdef]; exact Nat.lt_floor_add_one _
    linarith
  have hQ1 : 1 ≤ Q := by
    rw [hQdef]
    exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hs16p, one_mul]; exact hs16)
  have hQN : Q ≤ n := by
    have : (Q : ℝ) ≤ n := hq.trans (div_le_self hx0.le (one_le_pow₀ hs1))
    exact_mod_cast this
  have hs_gt : 1 < s := by
    by_contra hle
    push_neg at hle
    have : s ^ 4 ≤ 1 := pow_le_one₀ hs0.le hle
    linarith
  have h24 : 2 * s ^ 24 < x := by
    have a1 : 2 * s ^ 24 ≤ s ^ 4 * s ^ 24 := mul_le_mul_of_nonneg_right hs4_2 (by positivity)
    have a2 : s ^ 4 * s ^ 24 = s ^ 28 := by ring
    have a3 : s ^ 28 < s ^ 46 := pow_lt_pow_right₀ hs_gt (by norm_num)
    linarith
  have hPQ : 2 / ((Q : ℝ) + 1) < 1 / (P : ℝ) ^ 2 := by
    have hQp : (0 : ℝ) < Q + 1 := by positivity
    have hxs : 0 < x / s ^ 16 := by positivity
    have c1 : 2 / ((Q : ℝ) + 1) ≤ 2 * s ^ 16 / x := by
      calc 2 / ((Q : ℝ) + 1) ≤ 2 / (x / s ^ 16) := div_le_div_of_nonneg_left (by norm_num) hxs hq1
        _ = 2 * s ^ 16 / x := by field_simp <;> ring
    have c2 : 2 * s ^ 16 / x < 1 / s ^ 8 := by
      rw [div_lt_div_iff₀ hx0 (by positivity)]
      calc 2 * s ^ 16 * s ^ 8 = 2 * s ^ 24 := by ring
        _ < x := h24
        _ = 1 * x := (one_mul x).symm
    have c3 : 1 / s ^ 8 ≤ 1 / (P : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      calc (P : ℝ) ^ 2 ≤ (s ^ 4) ^ 2 := pow_le_pow_left₀ (by linarith) hp 2
        _ = s ^ 8 := by ring
    linarith
  have : NeZero (3 * n + 1) := ⟨by omega⟩
  set E := (P : ℝ) * (7 + C * x ^ θ + 2 * Real.log x) with hEdef
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hE0 : 0 ≤ E := by positivity
  have hmaj : ∀ q ∈ Icc 1 P, ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S n (a' / q + β) - (μ q : ℂ) / q.totient * V n β‖ ≤ E * (1 + 2 * π * |β| * n) := by
    intro q hq a' hcop β
    rw [mem_Icc] at hq
    refine (major_of_psiPower hθ0 hC h (by omega) hq.1 a' hcop β).trans ?_
    apply mul_le_mul_of_nonneg_right _ (by have := Real.pi_pos; positivity)
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hq.2) (by positivity)
  have hTE := ternary_explicit (N := n) (M := 3 * n + 1) (P := P) (Q := Q) (n := n)
    (by omega) (by omega) hP1 hQ1 hQN hPQ hE0 hmaj
  have hsP : s ^ 2 / Real.sqrt 2 ≤ Real.sqrt P := by
    apply le_sqrt_of_sq (by positivity)
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    calc (s ^ 2) ^ 2 / 2 = s ^ 4 / 2 := by ring
      _ ≤ (P : ℝ) := hp2
  have hE : E ≤ s ^ 4 * (7 + C * (x / s ^ 96) + 2 * Real.log x) := by
    rw [hEdef, ← hθs]
    exact mul_le_mul_of_nonneg_right hp (by positivity)
  have hM : x ≤ ((3 * n + 1 : ℕ) : ℝ) := by rw [hxdef]; exact_mod_cast (by omega : n ≤ 3 * n + 1)
  have herr := err_total (x := x) (s := s) (u := 1 + Real.log x) (L := Real.log x) (p := P) (q := Q)
    (M := ((3 * n + 1 : ℕ) : ℝ)) (C := C) (Λ2 := ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m ^ 2)
    (E := E) hx1 hs1 hlog0 rfl hC hs46 hx45 hp1 hp hp2 (Nat.cast_nonneg Q) hq hq1 hM
    (sum_vonMangoldt_sq_le n) (sum_nonneg fun _ _ => sq_nonneg _) hE0 hE
  rw [← hC0] at herr
  have hreal : (r3 n n : ℂ) - (J n n : ℂ) * singP P n =
      ((r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q : ℝ) : ℂ) := by
    rw [singP_eq_fS]; push_cast; ring
  rw [hreal, Complex.norm_real, Real.norm_eq_abs] at hTE
  have h1 : |r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q| ≤ C0 * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) :=
    hTE.trans herr
  have hs2x : s ^ 2 ≤ x := le_trans (pow_le_pow_right₀ hs1 (by norm_num)) hs46
  have h2 := main_term_err hn3 hP1 hs1 hsP hs2x
  -- absorb the logarithms
  have hu : (1 + Real.log x) ^ 5 ≤ Ka * s := by
    have hb := one_add_log_le hx1 hε
    calc (1 + Real.log x) ^ 5 ≤ ((1 + 1 / ε) * x ^ ε) ^ 5 :=
          pow_le_pow_left₀ (by linarith) hb 5
      _ = Ka * (x ^ ε) ^ 5 := by rw [hKa, mul_pow]
      _ = Ka * s := by
          rw [pow_rpow_eq hx0.le, hsdef, hεdef]; congr 2; push_cast; ring
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hu1 : (1 : ℝ) ≤ (1 + Real.log x) ^ 5 := one_le_pow₀ (by linarith)
  have hB : x ^ 2 / s ^ 2 ≤ x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2 := by
    apply div_le_div_of_nonneg_right _ hs2.le
    have := mul_le_mul_of_nonneg_left hu1 (sq_nonneg x)
    linarith
  have hfin : x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2 ≤ Ka * x ^ (2 - η / 4) := by
    rw [Real.rpow_sub hx0, hsdef.symm, show (x : ℝ) ^ (2 : ℝ) = x ^ 2 from Real.rpow_two x]
    rw [div_le_iff₀ hs2]
    calc x ^ 2 * (1 + Real.log x) ^ 5 ≤ x ^ 2 * (Ka * s) :=
          mul_le_mul_of_nonneg_left hu (by positivity)
      _ = Ka * (x ^ 2 / s) * s ^ 2 := by field_simp <;> ring
  have h3 : |r3 n n - sing3 n * x ^ 2 / 2| ≤
      (C0 + 3 * Real.exp 8) * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) := by
    calc |r3 n n - sing3 n * x ^ 2 / 2|
        = |(r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q) +
            (J n n * ∑ q ∈ Icc 1 P, fS n q - sing3 n * x ^ 2 / 2)| := by congr 1; ring
      _ ≤ |r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q| +
            |J n n * ∑ q ∈ Icc 1 P, fS n q - sing3 n * x ^ 2 / 2| := abs_add_le _ _
      _ ≤ C0 * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) +
            3 * Real.exp 8 * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) := by
          apply add_le_add h1
          exact h2.trans (mul_le_mul_of_nonneg_left hB (by positivity))
      _ = _ := by ring
  calc |r3 n n - sing3 n * x ^ 2 / 2|
      ≤ (C0 + 3 * Real.exp 8) * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) := h3
    _ ≤ (C0 + 3 * Real.exp 8) * (Ka * x ^ (2 - η / 4)) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = (C0 + 3 * Real.exp 8) * Ka * x ^ (2 - η / 4) := by ring

/-- **Theorem A, r = 3, CONDITIONAL ON `PsiPower θ`** for some `0 ≤ θ < 1`. -/
theorem theoremA3_of_psiPower {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hψ : PsiPower θ) :
    theoremA3_stmt :=
  theoremA3_of_r3Power (r3Power_of_psiPower hθ0 hθ1 hψ)

end LeanLab.HardyLittlewood1923.U1438
