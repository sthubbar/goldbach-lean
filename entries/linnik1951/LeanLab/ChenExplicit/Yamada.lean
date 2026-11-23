module

public import LeanLab.ChenExplicit.Assembly

/-!
AI-written Lean code, Claude, 2026-10-17, run 20261017T2104Z-19452, unit U-0371.
P0010 T. Yamada, Explicit Chen's theorem, arXiv 1511.03409v2, Section 8.

Yamada proves Theorem 1.1 in Section 8 by combining Lemma 4.1, the sieve bounds Theorems
5.1, 6.1, 7.1, the bound (48) `|A| > N / log N`, and the numerical value `c₂ < 0.36309` of
Lemma 7.3, into (132) and then (133). This file
* states those inputs with Yamada's printed constants, as `Prop` hypotheses;
* PROVES the numerical step (132) to (133): with `ε₀(N) ≤ 1/57`, `ε = e^{-50}` and
  `log N > e^{36}`, the right side of (132) exceeds `0.007`; the margin is about `6 · 10⁻⁵`;
* PROVES `γ > 0.5732` and `e^γ > 1.773` from Mathlib's lower sequence at `n = 127`;
* PROVES `yamada_of_section8`: the inputs imply `Yamada`, Theorem 1.1, using the lab's
  proved Lemma 37 `chen_inequality` in place of Yamada's Lemma 4.1, which it implies.
The result is CONDITIONAL ON Theorems 5.1, 6.1, 7.1, (48) and `c₂ < 0.36309`. BJS 2022 report
mistakes in Yamada's proof of the sieve theorems; this file checks only the final arithmetic.
Added later in the same run, unit U-0375: the Section 8 arithmetic is proved for any
Theorem 6.1 constant `C6 ≤ 2500`, `yamada_of_section8_C6`, because Eq93.lean shows the printed
(93), hence 993.2507, is too small; the corrected constant is near 2100.
Chen's theorem is known; binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real

noncomputable section
namespace LeanLab.ChenExplicit.Yamada

open LeanLab.ChenExplicit

/-- `|A|` for `A = {N - p : p ≤ N, p ∤ N}`, Section 4; `p = N` is excluded by `p ∤ N`. -/
def Acard (N : ℕ) : ℕ := #((range N).filter fun p => p.Prime ∧ ¬ p ∣ N)

/-- `ε₀(N) = 1 / max{57, log log N}`, Section 4. -/
def eps0 (N : ℕ) : ℝ := 1 / max 57 (log (log N))

/-- Yamada's `c₂ = ∫_{1/8}^{1/3} log(2 - 3β) / (β(1 - β)) dβ + 10⁻⁸`, Lemma 7.3. -/
def c2 : ℝ := (∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) + 1 / 10 ^ 8

/-- Lemma 7.3, numerical part, CITED: `c₂ < 0.36309`. Our Python quadrature gives
`0.3630837...`. -/
def C2Bound : Prop := c2 < 36309 / 100000

/-- (48), CITED: `|A| > N / log N` for even `N > exp exp 36`. -/
def Thm48 : Prop :=
  ∀ N : ℕ, Even N → exp (exp 36) < N → (N : ℝ) / log N < Acard N

/-- Theorem 5.1, CITED. -/
def Thm51 : Prop :=
  ∀ N : ℕ, Even N → exp (exp 36) < N →
    U N * Acard N / log N *
        (4 * exp eulerMascheroniConstant * log 3 - 5198 / 10000 * eps0 N -
          7677471 / 10000 / √(log N)) < SA N (zN N)

/-- Theorem 6.1, CITED. The sum is over primes `z ≤ q < y`; a prime `q ∣ N` gives
`A_q = ∅`, so the lab's sum over `q ∤ N` is the same sum. -/
def Thm61C (C6 : ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp 36) < N →
    (sumSAq N (zN N) (yN N) : ℝ) < U N * Acard N / log N *
        (4 * exp eulerMascheroniConstant * log 6 * (1 + eps0 N) + C6 / √(log N))

/-- Theorem 6.1 with Yamada's printed constant `993.2507`. -/
def Thm61 : Prop := Thm61C (9932507 / 10000)

/-- Theorem 7.1, CITED, for every `0 < ε < 0.01`; `log^{3/2} N` is written `log N · √log N`. -/
def Thm71 : Prop :=
  ∀ N : ℕ, Even N → exp (exp 36) < N → ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
    (SB N (zN N) (yN N) : ℝ) ≤
      c2 * (1 + ε) * N * U N / log N ^ 2 *
          (4 * exp eulerMascheroniConstant * (1 + eps0 N) +
            86016295 / 100000 / (log N * √(log N))) +
        exp (-138) * N / (ε * log N ^ 3)

/-! ### Numerical facts, PROVED -/

lemma harmonic_127_gt : (54253 / 10000 : ℚ) < harmonic 127 := by
  simp only [harmonic]
  norm_num [Finset.sum_range_succ]

/-- `γ > 0.5732`, from `γ > H₁₂₇ - log 128`. -/
theorem gamma_gt : (5732 / 10000 : ℝ) < eulerMascheroniConstant := by
  have h := eulerMascheroniSeq_lt_eulerMascheroniConstant 127
  have hH : (((54253 / 10000 : ℚ)) : ℝ) < ((harmonic 127 : ℚ) : ℝ) := Rat.cast_lt.mpr harmonic_127_gt
  push_cast at hH
  have hl : log ((127 : ℕ) + 1 : ℝ) = 7 * log 2 := by
    rw [show ((127 : ℕ) + 1 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  have h2 := log_two_lt_d9
  unfold eulerMascheroniSeq at h
  rw [hl] at h
  norm_num at h2
  linarith

/-- `e^γ > 1.773`. -/
theorem exp_gamma_gt : (1773 / 1000 : ℝ) < exp eulerMascheroniConstant := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 5732 / 10000) (by norm_num) 6
  have h2 : exp (5732 / 10000) < exp eulerMascheroniConstant := exp_lt_exp.mpr gamma_gt
  have h3 : (1773 / 1000 : ℝ) < ∑ i ∈ range 6, (5732 / 10000 : ℝ) ^ i / (i.factorial : ℝ) := by
    simp only [Finset.sum_range_succ, Nat.factorial]; norm_num
  linarith

lemma exp_18_gt : (5 * 10 ^ 7 : ℝ) < exp 18 := by
  have := exp_one_gt_d9
  have e : exp 18 = exp 1 ^ 18 := by rw [exp_one_pow]; norm_num
  have h2 : (2.7182818283 : ℝ) ^ 18 ≤ exp 1 ^ 18 := pow_le_pow_left₀ (by norm_num) this.le 18
  have h3 : (5 * 10 ^ 7 : ℝ) < (2.7182818283 : ℝ) ^ 18 := by norm_num
  linarith

lemma exp_50_gt : (10 ^ 20 : ℝ) < exp 50 := by
  have := exp_one_gt_d9
  have e : exp 50 = exp 1 ^ 50 := by rw [exp_one_pow]; norm_num
  have h2 : (2.7182818283 : ℝ) ^ 50 ≤ exp 1 ^ 50 := pow_le_pow_left₀ (by norm_num) this.le 50
  have h3 : (10 ^ 20 : ℝ) < (2.7182818283 : ℝ) ^ 50 := by norm_num
  linarith

lemma exp_88_gt : (10 ^ 38 : ℝ) < exp 88 := by
  have := exp_one_gt_d9
  have e : exp 88 = exp 1 ^ 88 := by rw [exp_one_pow]; norm_num
  have h2 : (2.7182818283 : ℝ) ^ 88 ≤ exp 1 ^ 88 := pow_le_pow_left₀ (by norm_num) this.le 88
  have h3 : (10 ^ 38 : ℝ) < (2.7182818283 : ℝ) ^ 88 := by norm_num
  linarith

/-- **(132) to (133), PROVED.** Yamada's right side of (132), before the `1/log N` term,
written with `g = e^γ`, `c = c₂(1+ε)`, `e₀ = ε₀(N)`, `s = 1/√log N`, `s₃ = 1/log^{3/2} N`,
is at least `0.00704` once `e₀ ≤ 1/57`, `c ≤ 0.3630900001`, `s ≤ 2·10⁻⁸`, `s₃ ≤ s`, for any
constant `C6 ≤ 2500` in Theorem 6.1 in place of Yamada's `993.2507`; see Eq93.lean for why. -/
theorem section8_numeric (C6 : ℝ) (hC6 : C6 ≤ 2500) (g c e0 s s3 : ℝ) (hg : 1773 / 1000 < g)
    (hc0 : 0 ≤ c)
    (hc : c ≤ 3630900001 / 10000000000) (he0 : 0 ≤ e0) (he1 : e0 ≤ 1 / 57)
    (hs0 : 0 ≤ s) (hs : s ≤ 2 / 10 ^ 8) (hs30 : 0 ≤ s3) (hs3 : s3 ≤ s) :
    (704 / 100000 : ℝ) ≤
      (4 * g * log 3 - 5198 / 10000 * e0 - 7677471 / 10000 * s) -
        (4 * g * log 6 * (1 + e0) + C6 * s) / 2 -
        c * (4 * g * (1 + e0) + 86016295 / 100000 * s3) / 2 := by
  have l3a := log_three_gt_d9
  have l3b := log_three_lt_d9
  have l2a := log_two_gt_d9
  have l2b := log_two_lt_d9
  have l6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [l6]
  set a := 4 * log 3 - 2 * (log 2 + log 3) - 2 * c with ha
  set b := 2 * (log 2 + log 3) + 2 * c with hb
  have hab : (9141 / 1000000 : ℝ) ≤ a - b / 57 := by rw [ha, hb]; linarith
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  have heb : e0 * b ≤ b / 57 := by nlinarith
  have hinner : (9141 / 1000000 : ℝ) ≤ a - e0 * b := by linarith
  have hgi : (1773 / 1000 : ℝ) * (9141 / 1000000) ≤ g * (a - e0 * b) := by
    apply mul_le_mul hg.le hinner (by norm_num) (by linarith)
  have hcs : c * s3 ≤ 3630900001 / 10000000000 * (2 / 10 ^ 8) :=
    mul_le_mul hc (hs3.trans hs) hs30 (by norm_num)
  have key : (4 * g * log 3 - 5198 / 10000 * e0 - 7677471 / 10000 * s) -
        (4 * g * (log 2 + log 3) * (1 + e0) + C6 * s) / 2 -
        c * (4 * g * (1 + e0) + 86016295 / 100000 * s3) / 2 =
      g * (a - e0 * b) - 5198 / 10000 * e0 - 7677471 / 10000 * s - (C6 * s) / 2 -
        86016295 / 200000 * (c * s3) := by
    rw [ha, hb]; ring
  rw [key]
  have : 5198 / 10000 * e0 ≤ 5198 / 10000 * (1 / 57 : ℝ) := by linarith
  have hCs : C6 * s ≤ 2500 * (2 / 10 ^ 8) :=
    (mul_le_mul_of_nonneg_right hC6 hs0).trans (by nlinarith)
  nlinarith

/-! ### Lemma 7.3 sign, PROVED -/

theorem c2_pos : 0 < c2 := by
  unfold c2
  have : 0 ≤ ∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro β hβ
    obtain ⟨h1, h2⟩ := hβ
    apply div_nonneg
    · apply Real.log_nonneg; linarith
    · apply mul_nonneg <;> linarith
  positivity

/-! ### Error terms, PROVED -/

lemma err1 (N : ℕ) (hpos : (0 : ℝ) < N) (hL : exp 36 < Real.log N) (hU : 1 / 1000 ≤ U N) :
    2 * (N : ℝ) / zN N + yN N ≤ 1 / 10 ^ 12 * (U N * N / Real.log N ^ 2) := by
  set L := Real.log N with hLdef
  have hL6 := exp_32_7_gt
  have h36 : exp (327 / 10) ≤ exp 36 := exp_le_exp.mpr (by norm_num)
  have hL0 : 0 < L := by linarith [exp_pos 36]
  have hNe : (N : ℝ) = exp L := (exp_log hpos).symm
  have hz : zN N = exp (L / 8) := by
    simp only [zN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hy : yN N = exp (L / 3) := by
    simp only [yN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hbig := big_exp L (by linarith)
  have e1 : 2 * (N : ℝ) / zN N = 2 * exp (7 * L / 8) := by
    rw [hz, hNe, mul_div_assoc, ← exp_sub]; ring_nf
  have e2 : yN N ≤ exp (7 * L / 8) := by rw [hy]; exact exp_le_exp.mpr (by linarith)
  have e3 : exp L = exp (7 * L / 8) * exp (L / 8) := by rw [← exp_add]; ring_nf
  have hL2 : 0 < L ^ 2 := by positivity
  have hKl : 1 / 1000 * exp L / L ^ 2 ≤ U N * N / L ^ 2 := by
    rw [← hNe]
    apply div_le_div_of_nonneg_right _ hL2.le
    exact mul_le_mul_of_nonneg_right hU hpos.le
  have h7 := exp_pos (7 * L / 8)
  have : 3 * exp (7 * L / 8) ≤ 1 / 10 ^ 12 * (1 / 1000 * exp L / L ^ 2) := by
    rw [e3, show 1 / 10 ^ 12 * (1 / 1000 * (exp (7 * L / 8) * exp (L / 8)) / L ^ 2) =
      exp (7 * L / 8) * exp (L / 8) / (10 ^ 15 * L ^ 2) by ring, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hbig h7.le]
  rw [e1]
  linarith

lemma err2 (N : ℕ) (hpos : (0 : ℝ) < N) (hL1 : 1 ≤ Real.log N) (hU : 1 / 1000 ≤ U N) :
    exp (-138) * N / (exp (-50) * Real.log N ^ 3) ≤
      1 / 10 ^ 12 * (U N * N / Real.log N ^ 2) := by
  set L := Real.log N
  have e : exp (-138) / exp (-50) = (exp 88)⁻¹ := by
    rw [← exp_sub, ← exp_neg]; norm_num
  have h88 := exp_88_gt
  have hinv : (exp 88)⁻¹ ≤ 1 / 10 ^ 38 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (exp_pos _) (by norm_num)]; linarith
  have hL0 : 0 < L := by linarith
  rw [show exp (-138) * N / (exp (-50) * L ^ 3) = (exp (-138) / exp (-50)) * (N / L ^ 3) by
    field_simp]
  rw [e]
  have hNL : (N : ℝ) / L ^ 3 ≤ N / L ^ 2 := by
    apply div_le_div_of_nonneg_left hpos.le (by positivity)
    nlinarith
  have hUN : (N : ℝ) / L ^ 2 ≤ 1000 * (U N * N / L ^ 2) := by
    rw [show 1000 * (U N * N / L ^ 2) = (1000 * U N) * (N / L ^ 2) by ring]
    have : (1 : ℝ) ≤ 1000 * U N := by linarith
    have h0 : 0 ≤ (N : ℝ) / L ^ 2 := by positivity
    nlinarith
  have h0 : 0 ≤ (N : ℝ) / L ^ 3 := by positivity
  calc (exp 88)⁻¹ * (N / L ^ 3) ≤ 1 / 10 ^ 38 * (N / L ^ 3) :=
        mul_le_mul_of_nonneg_right hinv h0
    _ ≤ 1 / 10 ^ 38 * (1000 * (U N * N / L ^ 2)) := by
        apply mul_le_mul_of_nonneg_left (hNL.trans hUN) (by norm_num)
    _ ≤ 1 / 10 ^ 12 * (U N * N / L ^ 2) := by
        have : 0 ≤ U N * N / L ^ 2 := by positivity
        nlinarith

/-! ### Section 8, PROVED from the cited inputs -/

/-- **Yamada Theorem 1.1 from Section 8.** CONDITIONAL ON (48), Theorems 5.1, 6.1, 7.1 and
`c₂ < 0.36309`. Lemma 4.1 is replaced by the lab's proved `chen_inequality`, whose error
`2N/z + y` is at most Yamada's `2N^{7/8} + 2N^{1/3}`. We take `ε = e^{-50}` in Theorem 7.1,
inside Yamada's range `e^{-100} < ε < e^{-20}`. -/
theorem yamada_of_section8_C6 (C6 : ℝ) (hC6 : C6 ≤ 2500) (h48 : Thm48) (h51 : Thm51)
    (h61 : Thm61C C6) (h71 : Thm71) (hc2 : C2Bound) : Yamada := by
  intro N hEven hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  set L := Real.log N with hLdef
  have hL : exp 36 < L := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have hL6 := exp_32_7_gt
  have h36 : exp (327 / 10) ≤ exp 36 := exp_le_exp.mpr (by norm_num)
  have hL0 : 0 < L := by linarith
  have hNe : (N : ℝ) = exp L := (exp_log hpos).symm
  have hz : zN N = exp (L / 8) := by
    simp only [zN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hy : yN N = exp (L / 3) := by
    simp only [yN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hz2 : 2 ≤ zN N := by
    rw [hz]; have := add_one_le_exp (L / 8); linarith
  have hy0 : 0 < yN N := by rw [hy]; exact exp_pos _
  have hy3 : (N : ℝ) ≤ yN N ^ 3 := by
    rw [hy, ← exp_nat_mul, hNe]; apply exp_le_exp.mpr; push_cast; linarith
  have hchen := chen_inequality N (zN N) (yN N) hz2 hy0 hy3
  -- the quantities
  set g := exp eulerMascheroniConstant with hg
  set e0 := eps0 N with he0
  set A : ℝ := (Acard N : ℝ) with hA
  have hU := U_ge N
  have hU0 : 0 < U N := by linarith
  set K := U N * N / L ^ 2 with hK
  set M := U N * A / L with hM
  have hA48 := h48 N hEven hN
  have hKM : K < M := by
    rw [hK, hM]
    have : (N : ℝ) / L ^ 2 < A / L := by
      rw [show (N : ℝ) / L ^ 2 = (N / L) / L by ring]
      exact div_lt_div_of_pos_right hA48 hL0
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_lt_mul_of_pos_left this hU0
  have hK0 : 0 < K := by rw [hK]; positivity
  have hM0 : 0 < M := lt_trans hK0 hKM
  -- e₀ ≤ 1/57
  have he00 : 0 ≤ e0 := by rw [he0, eps0]; positivity
  have he01 : e0 ≤ 1 / 57 := by
    rw [he0, eps0]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_max_left _ _)
  -- s = 1/√L
  have hsq : exp 18 < √L := by
    have e : √(exp 36) = exp 18 := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (exp_pos _), ← exp_add]; norm_num
    rw [← e]
    exact Real.sqrt_lt_sqrt (exp_pos _).le hL
  have h18 := exp_18_gt
  have hsq0 : 0 < √L := by linarith
  set s := 1 / √L with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 2 / 10 ^ 8 := by
    rw [hs, div_le_div_iff₀ hsq0 (by norm_num)]; linarith
  set s3 := 86016295 / 100000 / (L * √L) with hs3def
  have hL1 : 1 ≤ L := by
    have := add_one_le_exp 36; linarith
  -- ε = e^{-50}
  set ε := exp (-50) with hε
  have hε0 : 0 < ε := exp_pos _
  have h50 := exp_50_gt
  have hε1 : ε ≤ 1 / 10 ^ 20 := by
    rw [hε, exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos _) (by norm_num)]; linarith
  have hεs : ε < 1 / 100 := by linarith
  have hc20 := c2_pos
  set c := c2 * (1 + ε) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcb : c ≤ 3630900001 / 10000000000 := by
    rw [hc]; unfold C2Bound at hc2
    nlinarith
  -- the sieve bounds
  have h1 := h51 N hEven hN
  have h2 := h61 N hEven hN
  have h3 := h71 N hEven hN ε hε0 hεs
  set P := 4 * g * (1 + e0) + 86016295 / 100000 / (L * √L) with hP
  have hg0 : 0 < g := exp_pos _
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have h3' : (SB N (zN N) (yN N) : ℝ) ≤ c * M * P + exp (-138) * N / (ε * L ^ 3) := by
    have e : c2 * (1 + ε) * N * U N / L ^ 2 * P = c * K * P := by rw [hc, hK]; ring
    rw [← hLdef] at h3
    have : c * K * P ≤ c * M * P := by
      apply mul_le_mul_of_nonneg_right _ hP0
      exact mul_le_mul_of_nonneg_left hKM.le hc0
    linarith
  -- the small error terms
  have hE1 : 2 * (N : ℝ) / zN N + yN N ≤ 1 / 10 ^ 12 * K := by
    rw [hK]; exact err1 N hpos hL hU
  have hE2 : exp (-138) * N / (ε * L ^ 3) ≤ 1 / 10 ^ 12 * K := by
    rw [hK, hε]; exact err2 N hpos hL1 hU
  -- s₃ ≤ s
  have hs3 : 1 / (L * √L) ≤ s := by
    rw [hs]; apply div_le_div_of_nonneg_left (by norm_num) hsq0
    exact le_mul_of_one_le_left hsq0.le hL1
  have hnum := section8_numeric C6 hC6 g c e0 s (1 / (L * √L)) (by rw [hg]; exact exp_gamma_gt) hc0
    hcb he00 he01 hs0 hs1 (by positivity) hs3
  -- assemble
  have hSA : M * (4 * g * log 3 - 5198 / 10000 * e0 - 7677471 / 10000 * s) <
      (SA N (zN N) : ℝ) := by
    have : 7677471 / 10000 / √L = 7677471 / 10000 * s := by rw [hs]; ring
    rw [hM]; rw [← hLdef, this] at h1; linarith
  have hQ : (sumSAq N (zN N) (yN N) : ℝ) <
      M * (4 * g * log 6 * (1 + e0) + C6 * s) := by
    have : C6 / √L = C6 * s := by rw [hs]; ring
    rw [hM]; rw [← hLdef, this] at h2; linarith
  have hPe : P = 4 * g * (1 + e0) + 86016295 / 100000 * (1 / (L * √L)) := by rw [hP]; ring
  have hfin : (704 / 100000 : ℝ) * M ≤
      M * (4 * g * log 3 - 5198 / 10000 * e0 - 7677471 / 10000 * s) -
        M * (4 * g * log 6 * (1 + e0) + C6 * s) / 2 - c * M * P / 2 := by
    rw [hPe]
    have := mul_le_mul_of_nonneg_left hnum hM0.le
    linarith
  have hgoal : (7 / 1000 : ℝ) * U N * N / Real.log N ^ 2 = 7 / 1000 * K := by
    rw [hK]; ring
  rw [hgoal]
  linarith

/-- Theorem 1.1 from Section 8 with Yamada's printed Theorem 6.1. CONDITIONAL ON (48),
Theorems 5.1, 6.1, 7.1 and `c₂ < 0.36309`. -/
theorem yamada_of_section8 (h48 : Thm48) (h51 : Thm51) (h61 : Thm61) (h71 : Thm71)
    (hc2 : C2Bound) : Yamada :=
  yamada_of_section8_C6 (9932507 / 10000) (by norm_num) h48 h51 h61 h71 hc2

end LeanLab.ChenExplicit.Yamada
