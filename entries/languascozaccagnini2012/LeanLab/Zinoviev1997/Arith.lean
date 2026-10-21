module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T2314Z-cloud29, unit U-5751, paper P0097.

# Zinoviev 1997, J. Number Theory 65, 334-358: the closing arithmetic

Read from `papers/P0097.pdf`, page images of pp. 335, 347, 348, 352, 356, 357.

* Lemma 3.3, p. 356-357: the count `S(N)` of `n₁ + n₂ + n₃ = N` with `2 < nᵢ < N - 5` is
  `(N - 8)(N - 7)/2 = N²/2 + 8θN`. Here `lemma33_count` and `lemma33_theta`.
* Theorem 3.4, p. 357: from `J₁ = (σ/e)(N²/2 + 8θN) + 0.04θN²`, `σ > 1.21`, the minor arc bound
  `|S(α)| < 0.18 N/ln N` and Lemma 1.5 `Σ ln²p e^{-2p/N} < 0.96 N ln N`, the integral is
  positive. Here `theorem34_J1`, `theorem34_J2`, and `theorem34_final`, which also carries the
  factor `e` and the `θN^{1.5} ln³N` term of (0.4) that the printed last line leaves out.
* Lemma 2.1, Case 2, p. 348: the printed step `φ(q) > 14.1 √q > 14.78 ln N` for `q > 2330` is
  false, `phi_2730` and `printed_phi_false`; and with `N = 10^21` the modulus `q = 2730` lies in
  `E₂` while `N/φ(q) > 0.068 N/ln N`, so (2.10) fails as printed, `printed_210_false`. The lemma
  survives otherwise: the lower alternative of (2.9) arises only where `2πN|z| > 10`, so there
  `|x| > 10/N` and the first term is below `0.0087 N/ln N`; where `2πN|z| ≤ 10` the upper term
  gives at most about `0.171 N/ln N`. Falsifier subagent, U-5751. Keeping the `1/√q` of p. 347
  is NOT a rescue: it cancels against the Gauss sum `|τ(χ̄)| ≤ √q` of p. 344.

Binary Goldbach is OPEN; this is the ternary problem under GRH.
-/

@[expose] public section

namespace LeanLab.Zinoviev1997
open Real Finset

/-- The pairs `(n₁, n₂)` with `n₁, n₂ ≥ 3` and `n₁ + n₂ = m` number `m - 5`, for `m ≥ 6`. -/
theorem pair_count (m : ℕ) (hm : 6 ≤ m) :
    ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
      (fun p => 3 ≤ p.1 ∧ 3 ≤ p.2 ∧ p.1 + p.2 = m)).card = m - 5 := by
  have : ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
      (fun p => 3 ≤ p.1 ∧ 3 ≤ p.2 ∧ p.1 + p.2 = m)).card = (Finset.Icc 3 (m - 3)).card := by
    symm
    apply Finset.card_bij (fun a _ => (a, m - a))
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro a _ b _ h
      simp only [Prod.mk.injEq] at h
      exact h.1
    · rintro ⟨a, b⟩ h
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
      exact ⟨a, by simp only [Finset.mem_Icc]; omega, by simp only [Prod.mk.injEq, true_and]; omega⟩
  rw [this, Nat.card_Icc]; omega

/-- Zinoviev's `S(N)`, Lemma 3.3: the triples of integers `≥ 3` with sum `N`. -/
def S (N : ℕ) : ℕ :=
  ((Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
    (fun t => 3 ≤ t.1 ∧ 3 ≤ t.2.1 ∧ 3 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = N)).card

/-- The paper's sum, p. 357: `S(N) = Σ_{n₃=3}^{N-6} (N - n₃ - 5)`. -/
theorem S_eq_sum (N : ℕ) :
    S N = ∑ n ∈ Finset.Icc 3 N,
      ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
        (fun p => 3 ≤ p.1 ∧ 3 ≤ p.2 ∧ p.1 + p.2 + n = N)).card := by
  unfold S
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t => t.2.2) (t := Finset.Icc 3 N)]
  · apply Finset.sum_congr rfl
    intro n hn
    apply Finset.card_bij (fun t _ => (t.1, t.2.1))
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht ⊢
      obtain ⟨⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩, rfl⟩ := ht
      exact ⟨⟨h1, h2⟩, h4, h5, h7⟩
    · rintro ⟨a, b, c⟩ ha ⟨a', b', c'⟩ hb h
      simp only [Finset.mem_filter] at ha hb
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, h.2, ha.2.trans hb.2.symm⟩
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hab hn
      refine ⟨(a, b, n), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨⟨hab.1.1, hab.1.2, by omega⟩, hab.2.1, hab.2.2.1, hn.1, hab.2.2.2⟩, trivial⟩
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_Icc] at ht ⊢
    omega

/-- The inner count: for `3 ≤ n`, the pairs `≥ 3` with sum `N - n` number `N - n - 5`
when `N - n ≥ 6`, and none otherwise. -/
theorem inner_count (N n : ℕ) :
    ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
        (fun p => 3 ≤ p.1 ∧ 3 ≤ p.2 ∧ p.1 + p.2 + n = N)).card = N - n - 5 := by
  rcases Nat.lt_or_ge (N - n) 6 with h | h
  · rw [show N - n - 5 = 0 by omega, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp; omega
  · rw [← pair_count (N - n) h]
    refine congrArg Finset.card ?_
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨h0, h1, h2, h3⟩; exact ⟨⟨by omega, by omega⟩, h1, h2, by omega⟩
    · rintro ⟨h0, h1, h2, h3⟩; exact ⟨⟨by omega, by omega⟩, h1, h2, by omega⟩

/-- Lemma 3.3, p. 357: `S(N) = (N - 8)(N - 7)/2` for `N ≥ 8`. -/
theorem lemma33_count (N : ℕ) (hN : 8 ≤ N) : 2 * S N = (N - 8) * (N - 7) := by
  rw [S_eq_sum]
  simp_rw [inner_count]
  -- Σ_{n=3}^{N} (N - n - 5) = Σ_{k=0}^{N-8} k
  have key : ∀ M : ℕ, 2 * ∑ n ∈ Finset.Icc 3 (M + 8), (M + 8 - n - 5) = M * (M + 1) := by
    intro M
    induction M with
    | zero => decide
    | succ M ih =>
      rw [show M + 1 + 8 = (M + 8) + 1 by ring, Finset.sum_Icc_succ_top (by omega)]
      have : ∑ n ∈ Finset.Icc 3 (M + 8), (M + 8 + 1 - n - 5) =
          ∑ n ∈ Finset.Icc 3 (M + 8), (M + 8 - n - 5) + M + 1 := by
        have h1 : ∑ n ∈ Finset.Icc 3 (M + 8), (M + 8 + 1 - n - 5) =
            ∑ n ∈ Finset.Icc 3 (M + 8), ((M + 8 - n - 5) + if n ≤ M + 3 then 1 else 0) := by
          apply Finset.sum_congr rfl; intro n hn
          simp only [Finset.mem_Icc] at hn
          split_ifs <;> omega
        rw [h1, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, smul_eq_mul, mul_one]
        have : (Finset.filter (fun n => n ≤ M + 3) (Finset.Icc 3 (M + 8))) = Finset.Icc 3 (M + 3) := by
          ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        rw [this, Nat.card_Icc]; omega
      rw [this]
      have : M + 8 + 1 - (M + 8 + 1) - 5 = 0 := by omega
      rw [this]; nlinarith [ih]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 8 := ⟨N - 8, by omega⟩
  rw [key]
  rw [show M + 8 - 8 = M by omega, show M + 8 - 7 = M + 1 by omega]

/-- Lemma 3.3 in the paper's form: `(N - 8)(N - 7)/2 = N²/2 + 8θN` with `|θ| ≤ 1`, `N ≥ 4`. -/
theorem lemma33_theta (N : ℝ) (hN : 4 ≤ N) :
    ∃ θ : ℝ, |θ| ≤ 1 ∧ (N - 8) * (N - 7) / 2 = N ^ 2 / 2 + 8 * θ * N := by
  refine ⟨(-15 * N + 56) / (16 * N), ?_, ?_⟩
  · rw [abs_div, abs_of_pos (by linarith : 0 < 16 * N), div_le_one (by linarith)]
    rw [abs_le]; constructor <;> nlinarith
  · field_simp; ring

/-- Theorem 3.4, p. 357, first display: `σ > 1.21` and `|θ₁|, |θ₂| ≤ 1` give
`J₁ = (σ/e)(N²/2 + 8θ₁N) + 0.04θ₂N² > 0.18 N²` once `N ≥ 2000`; in fact `> 0.182N² - 3.6N`. -/
theorem theorem34_J1 (N σ θ₁ θ₂ : ℝ) (hN : 2000 ≤ N) (hσ : 1.21 < σ) (h1 : |θ₁| ≤ 1)
    (h2 : |θ₂| ≤ 1) :
    0.18 * N ^ 2 < σ / exp 1 * (N ^ 2 / 2 + 8 * θ₁ * N) + 0.04 * θ₂ * N ^ 2 := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hse : 0.444 < σ / exp 1 := by rw [lt_div_iff₀ he0]; nlinarith
  have hθ₁ := (abs_le.mp h1).1
  have hθ₂ := (abs_le.mp h2).1
  have hA : N ^ 2 / 2 - 8 * N ≤ N ^ 2 / 2 + 8 * θ₁ * N := by nlinarith
  have hA0 : 0 < N ^ 2 / 2 - 8 * N := by nlinarith
  have : 0.444 * (N ^ 2 / 2 - 8 * N) ≤ σ / exp 1 * (N ^ 2 / 2 + 8 * θ₁ * N) := by
    apply mul_le_mul hse.le hA hA0.le (by linarith)
  nlinarith

/-- Theorem 3.4, p. 357, (3.16) with Lemmas 1.5 and 2.1: `0.18 N/ln N · 0.96 N ln N < 0.179 N²`. -/
theorem theorem34_J2 (N L M T : ℝ) (hN : 0 < N) (hL : 0 < L)
    (hM : M ≤ 0.18 * N / L) (hT0 : 0 ≤ T) (hT : T ≤ 0.96 * N * L) : M * T < 0.179 * N ^ 2 := by
  calc M * T ≤ (0.18 * N / L) * (0.96 * N * L) := mul_le_mul hM hT hT0 (by positivity)
    _ = 0.1728 * N ^ 2 := by field_simp; ring
    _ < 0.179 * N ^ 2 := by nlinarith

/-- `ln (10^20) ≥ 46`, from `e < 2.7182818286`. -/
theorem log_1e20_ge : (46 : ℝ) ≤ Real.log (10 ^ 20) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : exp 46 = exp 1 ^ 46 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc exp 1 ^ 46 ≤ (2.7182818286 : ℝ) ^ 46 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 46
    _ ≤ 10 ^ 20 := by norm_num

/-- `x³ < 0.0027 e^{x/2}` for `x ≥ 46`, by `e^y ≥ y^12/12!`. -/
theorem cube_lt_exp (x : ℝ) (hx : 46 ≤ x) : x ^ 3 < 0.0027 * exp (x / 2) := by
  have h := Real.pow_div_factorial_le_exp (x / 2) (by linarith) 12
  have h12 : ((12 : ℕ).factorial : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [h12] at h
  have hx9 : (46 : ℝ) ^ 9 ≤ x ^ 9 := pow_le_pow_left₀ (by norm_num) hx 9
  have hx3 : 0 < x ^ 3 := by positivity
  have : x ^ 3 * 8.0e14 < x ^ 3 * x ^ 9 := by
    apply mul_lt_mul_of_pos_left _ hx3; norm_num at hx9 ⊢; linarith
  have : (x / 2) ^ 12 / 479001600 = x ^ 3 * x ^ 9 / (4096 * 479001600) := by ring
  nlinarith

/-- Theorem 3.4 completed with (0.4): `J = e(J₁ + J₂) + θN^{1.5} ln³N` with `J₁ > 0.18N²`,
`|J₂| < 0.179N²` and `|θ| ≤ 1` is positive for every `N ≥ 10^20`. The printed last line
`J > |J₁| - |J₂|` drops the factor `e` and the error term; both are harmless. -/
theorem theorem34_final (N J₁ J₂ θ : ℝ) (hN : 10 ^ 20 ≤ N) (h1 : 0.18 * N ^ 2 < J₁)
    (h2 : |J₂| < 0.179 * N ^ 2) (hθ : |θ| ≤ 1) :
    0 < exp 1 * (J₁ + J₂) + θ * (N * Real.sqrt N) * Real.log N ^ 3 := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hL : 46 ≤ Real.log N := le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  have hc := cube_lt_exp (Real.log N) hL
  have hsq : exp (Real.log N / 2) = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN0]; congr 1; ring
  rw [hsq] at hc
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hL3 : 0 < Real.log N ^ 3 := by positivity
  -- the error term is at most N^{1.5} L³ < 0.0027 N²
  have herr : |θ * (N * Real.sqrt N) * Real.log N ^ 3| < 0.0027 * N ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < N * Real.sqrt N), abs_of_pos hL3]
    calc |θ| * (N * Real.sqrt N) * Real.log N ^ 3 ≤ 1 * (N * Real.sqrt N) * Real.log N ^ 3 := by
          gcongr
      _ = N * Real.sqrt N * Real.log N ^ 3 := by ring
      _ < N * Real.sqrt N * (0.0027 * Real.sqrt N) := by gcongr
      _ = 0.0027 * N ^ 2 := by rw [show N * Real.sqrt N * (0.0027 * Real.sqrt N) =
            0.0027 * N * (Real.sqrt N * Real.sqrt N) by ring, hss]; ring
  have he := Real.exp_one_gt_d9
  have hJ : 0.001 * N ^ 2 < J₁ + J₂ := by linarith [(abs_lt.mp h2).1]
  have hN2 : 0 < N ^ 2 := by positivity
  have : exp 1 * (0.001 * N ^ 2) < exp 1 * (J₁ + J₂) :=
    mul_lt_mul_of_pos_left hJ (Real.exp_pos 1)
  have h27 : 0.0027 * N ^ 2 ≤ exp 1 * (0.001 * N ^ 2) := by nlinarith
  linarith [(abs_lt.mp herr).1]

/-- Lemma 2.1, Case 2, p. 348: `φ(2730) = 576`. -/
theorem phi_2730 : Nat.totient 2730 = 576 := by decide +kernel

/-- The printed step `φ(q) > 14.1 √q` for `q > 2330` is false at `q = 2730`. -/
theorem printed_phi_false : ¬ ∀ q : ℕ, 2330 < q → 14.1 * Real.sqrt q < Nat.totient q := by
  intro h
  have := h 2730 (by norm_num)
  rw [phi_2730] at this
  push_cast at this
  have hs2 : (41 : ℝ) < Real.sqrt 2730 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

/-- `2.25 < ln 10 < 2.35`, from `e^9 < 10^4` and `10^20 < e^47`. -/
theorem log_ten_bounds : 2.25 < Real.log 10 ∧ Real.log 10 < 2.35 := by
  constructor
  · rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h : exp 2.25 ^ 4 < 10 ^ 4 := by
      rw [← Real.exp_nat_mul, show ((4 : ℕ) : ℝ) * 2.25 = ((9 : ℕ) : ℝ) * 1 by norm_num,
        Real.exp_nat_mul]
      calc exp 1 ^ 9 < 2.7182818286 ^ 9 :=
            pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
        _ < 10 ^ 4 := by norm_num
    exact lt_of_pow_lt_pow_left₀ 4 (by norm_num) h
  · rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h : (10 : ℝ) ^ 20 < exp 2.35 ^ 20 := by
      rw [← Real.exp_nat_mul, show ((20 : ℕ) : ℝ) * 2.35 = ((47 : ℕ) : ℝ) * 1 by norm_num,
        Real.exp_nat_mul]
      calc (10 : ℝ) ^ 20 < 2.7182818283 ^ 47 := by norm_num
        _ < exp 1 ^ 47 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
    exact lt_of_pow_lt_pow_left₀ 20 (Real.exp_pos _).le h

/-- (2.10) fails as printed, Lemma 2.1 Case 2, p. 348. At `N = 10^21`, with `L = ln N`:
`q = 2730` is past `Q = [1.1 L²]` and below `τ = 4900 L⁴`, so arcs with this `q` lie in `E₂`;
yet `N/φ(q) > 0.068 N/L`, and the printed lower term chain `N/φ(q) + 0.1 N/L` exceeds
`0.18 N/L`. -/
theorem printed_210_false :
    1.1 * Real.log (10 ^ 21) ^ 2 < 2730 ∧ (2730 : ℝ) ≤ 4900 * Real.log (10 ^ 21) ^ 4 ∧
    0.068 * (10 ^ 21 : ℝ) / Real.log (10 ^ 21) < (10 ^ 21 : ℝ) / (Nat.totient 2730 : ℝ) ∧
    0.18 < Real.log (10 ^ 21) / (Nat.totient 2730 : ℝ) + 0.1 := by
  obtain ⟨h1, h2⟩ := log_ten_bounds
  have hL : Real.log ((10 : ℝ) ^ 21) = 21 * Real.log 10 := by
    rw [Real.log_pow]; norm_num
  rw [hL, phi_2730]
  push_cast
  have hL0 : 0 < 21 * Real.log 10 := by linarith
  have h4 : (47.25 : ℝ) ^ 4 ≤ (21 * Real.log 10) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 4
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · rw [div_lt_div_iff₀ hL0 (by norm_num)]; nlinarith
  · have : (0.08 : ℝ) < 21 * Real.log 10 / 576 := by rw [lt_div_iff₀ (by norm_num)]; nlinarith
    linarith

end LeanLab.Zinoviev1997

