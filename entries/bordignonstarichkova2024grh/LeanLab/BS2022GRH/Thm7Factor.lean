module

public import LeanLab.BS2022GRH.Thm6Factor

/-!
P0021, Bordignon-Starichkova 2022, arXiv 2211.08844 v1, Theorem 7, Section 5.3.
The near-1 factors and the error terms of the Theorem 7 upper bound for `S(B, ℙ, y)` at the
Section 5.4 choices `N ≥ X₂ = exp(exp 15.85)`, `α₃ = 10^{-2.61}`, `A = 4`, `ε₁ = 10⁻²⁰`,
`ε = 1/8137`, `C₁ = 112`. Read in Claude in Chrome from arxiv.org/html/2211.08844 on
2026-10-18: Theorem 7, Lemma 9 and Section 5.4.
AI-written Lean code, Claude, run 20261018T2003Z-9206, unit U-0970. Checked only by the
Lean kernel. Binary Goldbach is OPEN; Theorem 7 itself stays cited.

`li` enters only through the hypothesis `li y ≤ ∫₂^y dt / log t + 2`, weaker than the paper's
`+ 1.046` and PROVED for the principal value `li` in LiPV.lean, `liPV_le`; changed from `1.046`
to `2` by run 20261019T0202Z-9877, unit U-0997, every statement only got stronger.
The Lemma 9 quantity `m(N^{2/3}, (1+ε₁)N^{1/8}, √N / log⁵ N)` enters through the hypothesis
`0 ≤ m ≤ 1000`; that bound is plain arithmetic not yet done here, so every result below that
uses it is CONDITIONAL ON it.

Result: the Theorem 7 bracket is at most `(2e^γ/(1/2-α) + 3εC₁) c̄ + 10⁻⁴`, so with weight
`1/2` it costs at most `5·10⁻⁵` against `K3 > 0.0015`.
-/

@[expose] public section

namespace LeanLab.BS2022GRH
open Real MeasureTheory

/-- `∫ₐᵇ dt / log t ≤ (b - a) / log a` for `1 < a ≤ b`. -/
lemma integral_inv_log_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / log t ≤ (b - a) / log a := by
  have hla : 0 < log a := log_pos ha
  have hc : ContinuousOn (fun t : ℝ => 1 / log t) (Set.Icc a b) := by
    apply continuousOn_const.div (Real.continuousOn_log.mono ?_)
    · intro t ht; exact (log_pos (lt_of_lt_of_le ha ht.1)).ne'
    · intro t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  have hi : IntervalIntegrable (fun t : ℝ => 1 / log t) volume a b :=
    (hc.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
  have := intervalIntegral.integral_mono_on hab hi
    (intervalIntegrable_const (c := 1 / log a)) (fun t ht => by
      have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
      exact one_div_le_one_div_of_le hla (log_le_log (by linarith) ht.1))
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  rw [div_eq_mul_one_div (b - a)]; exact this

lemma intervalIntegrable_inv_log {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / log t) volume a b := by
  have hc : ContinuousOn (fun t : ℝ => 1 / log t) (Set.Icc a b) := by
    apply continuousOn_const.div (Real.continuousOn_log.mono ?_)
    · intro t ht; exact (log_pos (lt_of_lt_of_le ha ht.1)).ne'
    · intro t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  exact (hc.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable

/-- `t e^{-η t} ≤ 10⁻¹⁰` for `η = 2·10⁻⁵`, `t ≥ 2.5·10⁶`. -/
lemma t_exp_neg_le {t : ℝ} (ht : 2500000 ≤ t) : t * exp (-(2e-5 * t)) ≤ 1e-10 := by
  have h := Real.pow_div_factorial_le_exp (x := 2e-5 * t) (by positivity) 30
  have ht29 : (2500000 : ℝ) ^ 29 ≤ t ^ 29 := pow_le_pow_left₀ (by norm_num) ht 29
  have e : (2e-5 * t) ^ 30 = (2e-5 : ℝ) ^ 30 * t ^ 29 * t := by ring
  rw [e] at h
  have hE : 1e10 * t ≤ exp (2e-5 * t) := by
    refine le_trans ?_ h
    rw [le_div_iff₀ (by positivity)]
    have : (1e10 : ℝ) * (Nat.factorial 30 : ℝ) ≤ (2e-5 : ℝ) ^ 30 * t ^ 29 := by
      norm_num [Nat.factorial]; nlinarith
    nlinarith
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
  nlinarith

/-- **The li factor**: for `log y ≥ 2.5·10⁶` and `li ≤ ∫₂^y dt/log t + 2`,
`log y · li / y ≤ 1 + 2.2·10⁻⁵`. Split at `w = y^{1 - 2·10⁻⁵}`. -/
lemma li_factor_le {y li : ℝ} (hy0 : 0 < y) (hy : 2500000 ≤ log y)
    (hli : li ≤ (∫ t in (2 : ℝ)..y, 1 / log t) + 2) :
    log y * li / y ≤ 1 + 2.2e-5 := by
  set t := log y with ht
  have hyt : exp t = y := exp_log hy0
  set w := exp ((1 - 2e-5) * t) with hw
  have hw2 : 2 ≤ w := by have := add_one_le_exp ((1 - 2e-5) * t); linarith
  have hwy : w ≤ y := by rw [← hyt]; exact exp_le_exp.2 (by linarith)
  have hw1 : 1 < w := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_log (a := 2) (b := w) (by norm_num) hw2)
    (intervalIntegrable_inv_log hw1 hwy)
  have hI1 := integral_inv_log_le (a := 2) (b := w) (by norm_num) hw2
  have hI2 := integral_inv_log_le hw1 hwy
  have hlw : log w = (1 - 2e-5) * t := log_exp _
  rw [hlw] at hI2
  have hl2 : (0.69 : ℝ) ≤ log 2 := by have := Real.log_two_gt_d9; linarith
  have hwE : w = y * exp (-(2e-5 * t)) := by rw [← hyt, hw, ← exp_add]; ring_nf
  have hT := t_exp_neg_le hy
  have hexp : t ^ 2 / 2 ≤ y := by
    rw [← hyt]
    have := Real.pow_div_factorial_le_exp (x := t) (by linarith) 2
    norm_num [Nat.factorial] at this; linarith
  have hpt : 0 < (1 - 2e-5) * t := by nlinarith
  have hA : (w - 2) / log 2 ≤ w / log 2 := div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hB : (y - w) / ((1 - 2e-5) * t) ≤ y / ((1 - 2e-5) * t) :=
    div_le_div_of_nonneg_right (by linarith) hpt.le
  have hli2 : li ≤ w / log 2 + y / ((1 - 2e-5) * t) + 2 := by linarith
  have hty : 0 ≤ t / y := div_nonneg (by linarith) hy0.le
  have hE0 : 0 ≤ t * exp (-(2e-5 * t)) := mul_nonneg (by linarith) (exp_pos _).le
  have k1 : t * exp (-(2e-5 * t)) / log 2 ≤ 1e-10 / 0.69 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have k2 : t / y ≤ 8e-7 := by
    rw [div_le_iff₀ hy0]; nlinarith
  have k3 : (1 : ℝ) / (1 - 2e-5) ≤ 1.0000200005 := by norm_num
  have ht0 : t ≠ 0 := by intro h; linarith
  calc t * li / y = t / y * li := by ring
    _ ≤ t / y * (w / log 2 + y / ((1 - 2e-5) * t) + 2) := mul_le_mul_of_nonneg_left hli2 hty
    _ = t * exp (-(2e-5 * t)) / log 2 + 1 / (1 - 2e-5) + 2 * (t / y) := by
        rw [hwE]; field_simp
    _ ≤ 1e-10 / 0.69 + 1.0000200005 + 2 * 8e-7 := by nlinarith
    _ ≤ 1 + 2.2e-5 := by norm_num

/-- The main term of Theorem 7, the third piece of `K3` divided by `1/2`. -/
noncomputable def thm7Main (α g ε C₁ cb : ℝ) : ℝ := (2 * g / (1 / 2 - α) + 3 * ε * C₁) * cb

/-- The Theorem 7 bracket, the factor after `U_N N / log² N`, as printed, with `y = N^{1/3}`,
`τ` the twin prime constant, `cb = c̄` of Lemma 15, `m` the Lemma 9 quantity, `li = li(y)`. -/
noncomputable def thm7Bracket (α g ε C₁ τ cb ε₁ m li N : ℝ) : ℝ :=
  (1 + 0.06 * log N / N ^ (1 / 6 : ℝ)) * (2 * g / (1 / 2 - α) + 3 * ε * C₁) * (1 + ε₁)
    * (log (N ^ (1 / 3 : ℝ)) * (li - sqrt (N ^ (1 / 3 : ℝ)) * log (N ^ (1 / 3 : ℝ)) / (8 * π))
        / N ^ (1 / 3 : ℝ))
    * (cb + 64 * log (26 / 21) / log N ^ 2
        + (log (8 / 3) + 64 / log N ^ 2) * (3 * log (1 + ε₁) / log N + 27 / log N ^ 2))
  + (2 * g * τ)⁻¹ * (N ^ (-1 / 48 : ℝ) * (1 + ε₁) * log N ^ 5 / log (1 + ε₁))
    * (0.046 * m * (1 + ε₁) ^ (-1 / 6 : ℝ) + 0.159 * N ^ (-5 / 48 : ℝ))

lemma logN_ge {X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N) :
    (7640000 : ℝ) ≤ log N ∧ 0 < N := by
  have hN0 : 0 < N := lt_of_lt_of_le (exp_pos _) (le_trans hX hN)
  refine ⟨?_, hN0⟩
  have h1 : exp 15.85 ≤ log N := (le_log_iff_exp_le hN0).2 (le_trans hX hN)
  linarith [exp1585_ge]

lemma rpow_eq_exp {N : ℝ} (hN : 0 < N) (x : ℝ) : N ^ x = exp (log N * x) := rpow_def_of_pos hN x

/-- `1 ≤ 1 + 0.06 log N / N^{1/6} ≤ 1 + 10⁻¹²`. -/
lemma a7_le {N : ℝ} (hN : 0 < N) (hL : 7640000 ≤ log N) :
    1 ≤ 1 + 0.06 * log N / N ^ (1 / 6 : ℝ) ∧ 1 + 0.06 * log N / N ^ (1 / 6 : ℝ) ≤ 1 + 1e-12 := by
  rw [rpow_eq_exp hN]
  set L := log N
  have he := exp_pos (L * (1 / 6))
  have h4 := Real.pow_div_factorial_le_exp (x := L * (1 / 6)) (by positivity) 4
  norm_num [Nat.factorial] at h4
  have hL3 : (7640000 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  constructor
  · have : 0 ≤ 0.06 * L / exp (L * (1 / 6)) := div_nonneg (by linarith) he.le
    linarith
  · have : 0.06 * L / exp (L * (1 / 6)) ≤ 1e-12 := by
      rw [div_le_iff₀ he]
      have e : (L * (1 / 6)) ^ 4 / 24 = L * L ^ 3 / 31104 := by ring
      nlinarith [mul_le_mul_of_nonneg_left hL3 (by linarith : (0:ℝ) ≤ L)]
    linarith

/-- The `c̄` bracket of Theorem 7 is within `10⁻¹¹` above `c̄`, and nonnegative. -/
lemma d7_le {cb L ε₁ : ℝ} (hcb : 0 ≤ cb) (hL : 7640000 ≤ L) (he0 : 0 ≤ ε₁) (he : ε₁ ≤ 1e-20) :
    0 ≤ cb + 64 * log (26 / 21) / L ^ 2
        + (log (8 / 3) + 64 / L ^ 2) * (3 * log (1 + ε₁) / L + 27 / L ^ 2) ∧
    cb + 64 * log (26 / 21) / L ^ 2
        + (log (8 / 3) + 64 / L ^ 2) * (3 * log (1 + ε₁) / L + 27 / L ^ 2) ≤ cb + 1e-11 := by
  have hl26 : log (26 / 21 : ℝ) ≤ 5 / 21 := by
    have := Real.log_le_sub_one_of_pos (x := (26 / 21 : ℝ)) (by norm_num); linarith
  have hl260 : 0 ≤ log (26 / 21 : ℝ) := Real.log_nonneg (by norm_num)
  have hl1 : log (1 + ε₁) ≤ ε₁ := by
    have := Real.log_le_sub_one_of_pos (x := 1 + ε₁) (by linarith); linarith
  have hl10 : 0 ≤ log (1 + ε₁) := Real.log_nonneg (by linarith)
  have hl83 := log83_le
  have hl830 : 0 ≤ log (8 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have hL2 : (7640000 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL 2
  have hL0 : 0 < L := by linarith
  have q1 : 64 * log (26 / 21) / L ^ 2 ≤ 64 * (5 / 21) / 7640000 ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have q10 : 0 ≤ 64 * log (26 / 21) / L ^ 2 := by positivity
  have q2 : 64 / L ^ 2 ≤ 64 / 7640000 ^ 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
  have q20 : 0 ≤ 64 / L ^ 2 := by positivity
  have q3 : 3 * log (1 + ε₁) / L ≤ 3 * 1e-20 / 7640000 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]; nlinarith
  have q30 : 0 ≤ 3 * log (1 + ε₁) / L := by positivity
  have q4 : 27 / L ^ 2 ≤ 27 / 7640000 ^ 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2
  have q40 : 0 ≤ 27 / L ^ 2 := by positivity
  have q5 : (log (8 / 3) + 64 / L ^ 2) * (3 * log (1 + ε₁) / L + 27 / L ^ 2) ≤
      (0.98083 + 64 / 7640000 ^ 2) * (3 * 1e-20 / 7640000 + 27 / 7640000 ^ 2) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have q50 : 0 ≤ (log (8 / 3) + 64 / L ^ 2) * (3 * log (1 + ε₁) / L + 27 / L ^ 2) := by positivity
  have n : (64 * (5 / 21) / 7640000 ^ 2 : ℝ)
      + (0.98083 + 64 / 7640000 ^ 2) * (3 * 1e-20 / 7640000 + 27 / 7640000 ^ 2) ≤ 1e-11 := by
    norm_num
  constructor <;> linarith

/-- The second term of Theorem 7 is below `10⁻¹⁰`, given the Lemma 9 bound `0 ≤ m ≤ 1000`. -/
lemma e7_le {g τ ε₁ m N : ℝ} (hg1 : 1.78103 ≤ g) (hτ : 0.65 ≤ τ) (hN : 0 < N)
    (hL : 7640000 ≤ log N) (he1 : ε₁ = 1e-20) (hm0 : 0 ≤ m) (hm : m ≤ 1000) :
    (2 * g * τ)⁻¹ * (N ^ (-1 / 48 : ℝ) * (1 + ε₁) * log N ^ 5 / log (1 + ε₁))
      * (0.046 * m * (1 + ε₁) ^ (-1 / 6 : ℝ) + 0.159 * N ^ (-5 / 48 : ℝ)) ≤ 1e-10 := by
  subst he1
  have hN1 : 1 ≤ N := by
    have := (le_log_iff_exp_le hN).1 (le_trans (by norm_num) hL : (0 : ℝ) ≤ log N)
    simpa using this
  have hden : (2.3 : ℝ) ≤ 2 * g * τ := by nlinarith
  have hinv : (2 * g * τ)⁻¹ ≤ 1 / 2.3 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hden
  have hinv0 : 0 ≤ (2 * g * τ)⁻¹ := inv_nonneg.2 (by linarith)
  have hr1 : (1 + (1e-20 : ℝ)) ^ (-1 / 6 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hr10 : 0 ≤ (1 + (1e-20 : ℝ)) ^ (-1 / 6 : ℝ) := rpow_nonneg (by norm_num) _
  have hr2 : N ^ (-5 / 48 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hr20 : 0 ≤ N ^ (-5 / 48 : ℝ) := rpow_nonneg hN.le _
  have hB : 0.046 * m * (1 + (1e-20 : ℝ)) ^ (-1 / 6 : ℝ) + 0.159 * N ^ (-5 / 48 : ℝ) ≤ 47 := by
    have : m * (1 + (1e-20 : ℝ)) ^ (-1 / 6 : ℝ) ≤ 1000 := by nlinarith
    nlinarith
  have hB0 : 0 ≤ 0.046 * m * (1 + (1e-20 : ℝ)) ^ (-1 / 6 : ℝ) + 0.159 * N ^ (-5 / 48 : ℝ) := by
    positivity
  have hlog : (9.9e-21 : ℝ) ≤ log (1 + 1e-20) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 1 + (1e-20 : ℝ)) (by norm_num)
    refine le_trans ?_ this; norm_num
  rw [rpow_eq_exp hN]
  set L := log N
  have hE : exp (L * (-1 / 48)) * L ^ 5 ≤ 1e-32 := by
    have h20 := Real.pow_div_factorial_le_exp (x := L / 48) (by linarith) 20
    have hL15 : (7640000 : ℝ) ^ 15 ≤ L ^ 15 := pow_le_pow_left₀ (by norm_num) hL 15
    have e : (L / 48) ^ 20 = L ^ 15 * L ^ 5 / 48 ^ 20 := by ring
    rw [e] at h20
    have hL5 : 0 < L ^ 5 := by positivity
    have hbig : 1e32 * L ^ 5 ≤ exp (L / 48) := by
      refine le_trans ?_ h20
      rw [le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
      have : (1e32 : ℝ) * (48 ^ 20 * (Nat.factorial 20 : ℝ)) ≤ L ^ 15 := by
        norm_num [Nat.factorial]; linarith
      nlinarith
    have hx : exp (L * (-1 / 48)) = (exp (L / 48))⁻¹ := by rw [← exp_neg]; ring_nf
    rw [hx, inv_mul_eq_div, div_le_iff₀ (exp_pos _)]
    nlinarith
  have hE0 : 0 ≤ exp (L * (-1 / 48)) * L ^ 5 := by positivity
  have hQ : exp (L * (-1 / 48)) * (1 + 1e-20) * L ^ 5 / log (1 + 1e-20)
      ≤ 1e-32 * (1 + 1e-20) / 9.9e-21 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have : exp (L * (-1 / 48)) * (1 + 1e-20) * L ^ 5 = exp (L * (-1 / 48)) * L ^ 5 * (1 + 1e-20) :=
      by ring
    rw [this]
    have h1 : exp (L * (-1 / 48)) * L ^ 5 * (1 + 1e-20) ≤ 1e-32 * (1 + 1e-20) :=
      mul_le_mul_of_nonneg_right hE (by norm_num)
    have h2 : 0 ≤ 1e-32 * (1 + (1e-20 : ℝ)) := by norm_num
    nlinarith
  have hQ0 : 0 ≤ exp (L * (-1 / 48)) * (1 + 1e-20) * L ^ 5 / log (1 + 1e-20) := by
    apply div_nonneg _ (by linarith); positivity
  have s1 := mul_le_mul hinv hQ hQ0 (by norm_num)
  have s2 := mul_le_mul s1 hB hB0 (by norm_num)
  refine le_trans s2 ?_
  norm_num

/-- **Theorem 7 bracket at the Section 5.4 range**: at most the main term plus `10⁻⁴`,
CONDITIONAL ON `li` and `m` bounds as hypotheses. -/
theorem thm7Bracket_le {α g ε C₁ τ cb ε₁ m li X₂ N : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 0.0024548)
    (hg1 : 1.78103 ≤ g) (hg2 : g ≤ 1.781081) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8137)
    (hC0 : 0 ≤ C₁) (hC : C₁ ≤ 112) (hτ : 0.65 ≤ τ) (hcb0 : 0 ≤ cb) (hcb : cb ≤ 0.363084)
    (he1 : ε₁ = 1e-20) (hm0 : 0 ≤ m) (hm : m ≤ 1000)
    (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N)
    (hli : li ≤ (∫ t in (2 : ℝ)..N ^ (1 / 3 : ℝ), 1 / log t) + 2) :
    thm7Bracket α g ε C₁ τ cb ε₁ m li N ≤ thm7Main α g ε C₁ cb + 1e-4 := by
  obtain ⟨hL, hN0⟩ := logN_ge hX hN
  obtain ⟨ha1, ha2⟩ := a7_le hN0 hL
  obtain ⟨hd0, hd⟩ := d7_le (L := log N) (ε₁ := ε₁) hcb0 hL (by rw [he1]; norm_num) (by rw [he1])
  have hE := e7_le hg1 hτ hN0 hL he1 hm0 hm
  have hy0 : 0 < N ^ (1 / 3 : ℝ) := rpow_pos_of_pos hN0 _
  have hly : log (N ^ (1 / 3 : ℝ)) = 1 / 3 * log N := log_rpow hN0 _
  have hlyb : 2500000 ≤ log (N ^ (1 / 3 : ℝ)) := by rw [hly]; linarith
  have hΛ := li_factor_le hy0 hlyb hli
  have hs : 0 ≤ sqrt (N ^ (1 / 3 : ℝ)) * log (N ^ (1 / 3 : ℝ)) / (8 * π) := by
    apply div_nonneg (mul_nonneg (sqrt_nonneg _) (by linarith)) (by positivity)
  have hΛ' : log (N ^ (1 / 3 : ℝ)) * (li - sqrt (N ^ (1 / 3 : ℝ)) * log (N ^ (1 / 3 : ℝ)) / (8 * π))
      / N ^ (1 / 3 : ℝ) ≤ 1 + 2.2e-5 := by
    refine le_trans ?_ hΛ
    apply div_le_div_of_nonneg_right _ hy0.le
    apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hd2 : 0 < 1 / 2 - α := by linarith
  have hP0 : 0 ≤ 2 * g / (1 / 2 - α) + 3 * ε * C₁ := by
    have : 0 ≤ 2 * g / (1 / 2 - α) := div_nonneg (by linarith) hd2.le
    have : 0 ≤ 3 * ε * C₁ := by positivity
    linarith
  have hP : 2 * g / (1 / 2 - α) + 3 * ε * C₁ ≤ 7.21 := by
    have h1 : 2 * g / (1 / 2 - α) ≤ 7.16 := by rw [div_le_iff₀ hd2]; nlinarith
    have : ε * C₁ ≤ 112 / 8137 := by nlinarith
    linarith
  unfold thm7Bracket thm7Main
  set a := 1 + 0.06 * log N / N ^ (1 / 6 : ℝ)
  set P := 2 * g / (1 / 2 - α) + 3 * ε * C₁
  set Λ := log (N ^ (1 / 3 : ℝ)) * (li - sqrt (N ^ (1 / 3 : ℝ)) * log (N ^ (1 / 3 : ℝ)) / (8 * π))
      / N ^ (1 / 3 : ℝ)
  set d := cb + 64 * log (26 / 21) / log N ^ 2
        + (log (8 / 3) + 64 / log N ^ 2) * (3 * log (1 + ε₁) / log N + 27 / log N ^ 2)
  set Q := (2 * g * τ)⁻¹ * (N ^ (-1 / 48 : ℝ) * (1 + ε₁) * log N ^ 5 / log (1 + ε₁))
    * (0.046 * m * (1 + ε₁) ^ (-1 / 6 : ℝ) + 0.159 * N ^ (-5 / 48 : ℝ))
  have e1 : (1 + ε₁) = 1 + 1e-20 := by rw [he1]
  have hF0 : 0 ≤ a * P * (1 + ε₁) * d := by
    rw [e1]; apply mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hP0) (by norm_num)) hd0
  have r1 : a * P * (1 + ε₁) * Λ * d = (a * P * (1 + ε₁) * d) * Λ := by ring
  have r2 : (a * P * (1 + ε₁) * d) * Λ ≤ (a * P * (1 + ε₁) * d) * (1 + 2.2e-5) :=
    mul_le_mul_of_nonneg_left hΛ' hF0
  have r3 : a * (1 + ε₁) * (1 + 2.2e-5) ≤ 1 + 2.21e-5 := by
    rw [e1]
    have := mul_le_mul_of_nonneg_right ha2 (by norm_num : (0:ℝ) ≤ (1 + 1e-20) * (1 + 2.2e-5))
    have n : (1 + 1e-12 : ℝ) * ((1 + 1e-20) * (1 + 2.2e-5)) ≤ 1 + 2.21e-5 := by norm_num
    calc a * (1 + 1e-20) * (1 + 2.2e-5) = a * ((1 + 1e-20) * (1 + 2.2e-5)) := by ring
      _ ≤ _ := this
      _ ≤ _ := n
  have r30 : 0 ≤ a * (1 + ε₁) * (1 + 2.2e-5) := by rw [e1]; positivity
  have hPd : P * d ≤ P * (cb + 1e-11) := mul_le_mul_of_nonneg_left hd hP0
  have hPd0 : 0 ≤ P * d := mul_nonneg hP0 hd0
  have r4 : (a * P * (1 + ε₁) * d) * (1 + 2.2e-5) = (a * (1 + ε₁) * (1 + 2.2e-5)) * (P * d) := by
    ring
  have r5 : (a * (1 + ε₁) * (1 + 2.2e-5)) * (P * d) ≤ (1 + 2.21e-5) * (P * (cb + 1e-11)) :=
    mul_le_mul r3 hPd hPd0 (by norm_num)
  have r6 : (1 + 2.21e-5) * (P * (cb + 1e-11)) ≤ P * cb + 9e-5 := by
    have h1 : P * cb ≤ 7.21 * 0.363084 := mul_le_mul hP hcb hcb0 (by norm_num)
    have h2 : (1 + 2.21e-5) * (P * (cb + 1e-11))
        = P * cb + 2.21e-5 * (P * cb) + (1 + 2.21e-5) * 1e-11 * P := by ring
    rw [h2]
    linarith only [h1, hP, hP0]
  rw [r1]
  linarith only [r2, r4, r5, r6, hE]

/-- The third piece of `K3` is exactly `1/2 · thm7Main`. -/
theorem K3_third (α g ε C₁ C₂ cb : ℝ) : K3 α g ε C₁ C₂ cb = 8 * thm5Main α g ε C₂
    - 4 * thm6Main α g ε C₁ - 1 / 2 * thm7Main α g ε C₁ cb := by
  unfold K3 thm5Main thm6Main thm7Main; ring

/-- **Section 5.4 with the exact Theorem 5, 6 and 7 brackets** in place of their main terms,
weights `8`, `1/2 · 8`, `1/2` as in `K3`: the margin stays above
`0.0015 - 8·10⁻⁸ - 4·10⁻⁶ - 5·10⁻⁵`. Arithmetic only: Theorems 4 to 7 themselves stay cited,
and this is CONDITIONAL ON the Lemma 9 bound `0 ≤ m ≤ 1000` and on `li ≤ ∫₂ + 2`. -/
theorem theorem3_main_thm567 {m li X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N)
    (hm0 : 0 ≤ m) (hm : m ≤ 1000)
    (hli : li ≤ (∫ t in (2 : ℝ)..N ^ (1 / 3 : ℝ), 1 / log t) + 2) :
    (0.0015 - 8e-8 - 4e-6 - 5e-5 : ℝ) <
      K3 α0 (exp eulerMascheroniConstant) (1 / 8137) 112 114 LeanLab.ChenExplicit.BJS.cbar
      - 8 * thm5Main α0 (exp eulerMascheroniConstant) (1 / 8137) 114
      + 8 * thm5Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 114
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N
      + 4 * thm6Main α0 (exp eulerMascheroniConstant) (1 / 8137) 112
      - 4 * thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC (cG X₂) X₂ N
      + 1 / 2 * thm7Main α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.BJS.cbar
      - 1 / 2 * thm7Bracket α0 (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC LeanLab.ChenExplicit.BJS.cbar 1e-20 m li N := by
  have h1 := theorem3_main_thm56 hX hN
  obtain ⟨hg1, hg2⟩ := g_bounds
  have hτ : (0.65 : ℝ) ≤ LeanLab.ChenExplicit.twinC := by
    have := LeanLab.ChenExplicit.twinC_ge_065; norm_num at this ⊢; linarith
  have hc1 := LeanLab.ChenExplicit.BJS.cbar_lt
  have hc0 := LeanLab.ChenExplicit.BJS.cbar_gt
  have h3 := thm7Bracket_le (le_trans (by norm_num) alpha_ge) alpha_le hg1 hg2 (by norm_num)
    le_rfl (by norm_num) le_rfl hτ (by linarith) (by norm_num at hc1 ⊢; linarith) rfl hm0 hm
    hX hN hli
  linarith


end LeanLab.BS2022GRH
