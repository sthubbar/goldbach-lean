module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0704Z-6940, unit U-0923.
P0009 BJS 2022, arXiv 2207.09452v6, Section 9 with the constants of Theorems 44, 50 and 51
CORRECTED per FINDINGS F-0020, F-0021, F-0022: `e^{γ}` in Theorem 44 (a), the remainder factor
`(2e^{-γ}∏)⁻¹ = g/(2T)` in Theorems 50 and 51, `ε₂` at `x₂(X₃)`.

Parameters, the lab's choice, not the paper's: `log log X₂ = 32.8`, `X₃ = X₂^{1/8}`,
`δ = 1.476`, `α₁ = α₂ = α₃ = 10⁻⁵`, `ε₀ = 3·10⁻⁵`. At these the inputs are, by the lab's
Python check: `ε₁ = 1/57`, `ε₂ = 1/51`, `m(X₃) ≈ 1.23·10⁻¹¹`.

Notation: `L = log N ≥ LX = log X₂ = e^{32.8}`, `g = e^{γ}`, `T` the twin prime constant,
`cb = c̄` of Lemma 52, so `U_N⁻¹ ≤ (2 e^{-γ} T)⁻¹ = g / (2T)`. The tiny X₂-only constants
`l₁, l₁*, l, l*, c₄, c₄*, a(X₂)` and the factor `w` of Theorem 44 (b) are parameters with
numeric hypotheses, to be proved in later units, as is `m(X₃) ≤ 2·10⁻¹¹`.

PROVED here: `margin_a` and `margin_b`, each case's combination `cA - cQ/2 - cB/2` is at least
`2·10⁻⁴ + 10⁻¹²`, the Section9Margin of Assembly.lean, from `0.5772 < γ < 0.57722`
(GammaBounds), `∫_2^3 log(t-1)/t ≤ 0.1476` (FIntegral), `c̄ < 0.363084` (BJSCbar),
`T ≥ 0.65` (TwinCNumeric) and the hypotheses above. Goldbach is open; this is about the
explicit constant in Chen's theorem.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.Section9

/-- `α₁ = α₂ = α₃ = 10⁻⁵`. -/
abbrev α : ℝ := 1 / 100000
/-- `ε = 1.452·10⁻⁷`, Lemma 18. -/
abbrev ε : ℝ := 1452 / 10 ^ 10
/-- `ε₀ = 3·10⁻⁵`, the lab's choice. -/
abbrev e0 : ℝ := 3 / 100000

/-- `h(s)`, (7). -/
def h (s : ℝ) : ℝ := if s ≤ 2 then exp (-2) else if s ≤ 3 then exp (-s) else 3 / s * exp (-s)

/-- `f(s) = 2e^γ log(s-1)/s`, (62), with `g = e^γ`. -/
def fS (g s : ℝ) : ℝ := 2 * g * log (s - 1) / s

/-- `F(s) = (2e^γ/s)(1 + ∫_2^{s-1} log(t-1)/t dt)`, (60). -/
def FS (g s : ℝ) : ℝ := 2 * g / s * (1 + ∫ t in (2 : ℝ)..(s - 1), log (t - 1) / t)

/-- `c_{α₁,X₂} = 4 - 8α₁ - 160 log log X₂ / log X₂`, (136), with `log log X₂ = 32.8`. -/
def cc (LX : ℝ) : ℝ := 4 - 8 * α - 160 * (328 / 10) / LX

/-- `k_{α₂} = 8(1/6 - α₂)`, (155). -/
abbrev kα : ℝ := 8 * (1 / 6 - α)

/-- `l₂(X₂)`, (160). -/
def l2 (g LX : ℝ) : ℝ :=
  exp (LX / 8) / (exp (LX / 8) - 1) *
    (g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) + 512 / (kα * LX ^ 2)) +
      (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * exp 2 * h kα)

/-- Theorem 44 (a), corrected per F-0020, the constant of `U_N N / log² N`. -/
def cAa (g T c4 L : ℝ) : ℝ :=
  8 * (1 - 32.02 / L ^ 2) * (fS g (4 - 8 * α) - 107 * ε * exp 2 * h (4 - 8 * α) -
    1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L))

/-- Theorem 44 (b), with `w` the factor `1.3841 log(log¹⁰ x₁)/log log(log¹⁰ x₁)`. -/
def cAb (g T e1 a c4s w L LX : ℝ) : ℝ :=
  8 * (1 + 32.02 / L ^ 2) * (fS g (cc LX) - e1 * (1 - fS g (cc LX)) -
    (1 + e1) * ε * 107 * exp 2 * h (cc LX) -
    (3 * e1 + a) * (max (1 - fS g (cc LX)) (FS g (cc LX) - 1) + ε * 107 * exp 2 * h (cc LX)) -
    a - 64.04 / L ^ 2 - 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w)

/-- Theorem 50 (a), the `l(X₂)` term with the factor of F-0021. -/
def cQa (g T l1 l L LX : ℝ) : ℝ := 8.0004 * (1 + 32.02 / L ^ 2) * (l1 + l2 g LX) + l * (g / (2 * T))

/-- Theorem 50 (b). -/
def cQb (g T e1 l1s ls L LX : ℝ) : ℝ :=
  8.0004 * (1 + 32.02 / L ^ 2) * (1 + e1) * (l1s + l2 g LX) + ls * (g / (2 * T))

/-- Theorem 51, corrected per F-0021 and F-0022 (`e2` is `ε₂` at `x₂(X₃)`). -/
def cB (g T e2 cb m L : ℝ) : ℝ :=
  1.00005 * (1 + e2) * (1 + 4.51 / L ^ 2) *
      (2 / (1 / 2 - α) * g + 3 * ε * 106 * exp 2 * h (3 / 2 - 3 * α)) * (1 + e0 + 9 / L) *
      (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2)) +
    g / (2 * T) * (320 * m * (1 + e0) / (3 * log (1 + e0)) +
      0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0)))

/-! ### numeric facts -/

lemma h_le (s : ℝ) (hs : 3.9999 ≤ s) : exp 2 * h s ≤ 0.1016 := by
  unfold h
  rw [if_neg (by linarith), if_neg (by linarith)]
  have e : exp 2 * (3 / s * exp (-s)) = 3 / s * (exp (s - 2))⁻¹ := by
    rw [← exp_neg, show -(s - 2) = 2 + -s by ring, exp_add]; ring
  rw [e]
  have e2 : exp (s - 2) = exp 1 * exp 1 * exp (s - 4) := by
    rw [← exp_add, ← exp_add]; ring_nf
  have he := exp_one_gt_d9
  have h4 := add_one_le_exp (s - 4)
  have h1 : (7.388 : ℝ) ≤ exp (s - 2) := by
    rw [e2]
    have : (2.7182818283 : ℝ) * 2.7182818283 ≤ exp 1 * exp 1 := by
      apply mul_le_mul he.le he.le (by norm_num) (exp_pos 1).le
    have h5 : 0.9999 ≤ exp (s - 4) := by linarith
    have : (2.7182818283 : ℝ) * 2.7182818283 * 0.9999 ≤ exp 1 * exp 1 * exp (s - 4) := by
      apply mul_le_mul this h5 (by norm_num) (by positivity)
    norm_num at this ⊢; linarith
  have h2 : 3 / s ≤ 3 / 3.9999 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have h3 : (exp (s - 2))⁻¹ ≤ 1 / 7.388 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h1
  calc 3 / s * (exp (s - 2))⁻¹ ≤ 3 / 3.9999 * (1 / 7.388) := by
        apply mul_le_mul h2 h3 (by positivity) (by norm_num)
    _ ≤ 0.1016 := by norm_num

lemma h_low (s : ℝ) (h1 : 1 ≤ s) (h2 : s ≤ 2) : exp 2 * h s = 1 := by
  unfold h; rw [if_pos h2, ← exp_add]; norm_num

lemma h_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ h s := by
  unfold h; split_ifs <;> positivity

lemma log_cm1_ge (LX : ℝ) (hLX : 10 ^ 14 ≤ LX) : 1.09858558 ≤ log (cc LX - 1) := by
  unfold cc
  have hx : 160 * (328 / 10) / LX ≤ 10 ^ (-10 : ℤ) := by
    rw [div_le_iff₀ (by linarith)]; norm_num; linarith
  have hpos : 0 < 160 * (328 / 10) / LX := by positivity
  set d := 160 * (328 / 10) / LX
  have e : 4 - 8 * α - d - 1 = 3 * (1 - (8 * α + d) / 3) := by ring
  rw [e, log_mul (by norm_num) (by norm_num at hx ⊢; nlinarith)]
  have h1 := Real.one_sub_inv_le_log_of_pos (x := 1 - (8 * α + d) / 3) (by norm_num at hx ⊢; nlinarith)
  have l3 := log_three_gt_d9
  have h2 : 1 - (1 - (8 * α + d) / 3)⁻¹ ≥ -0.0000267 := by
    have hy : 0.99997 ≤ 1 - (8 * α + d) / 3 := by norm_num at hx ⊢; nlinarith
    have : (1 - (8 * α + d) / 3)⁻¹ ≤ 1 + 0.0000267 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      have : (8 * α + d) / 3 ≤ 0.0000266667 + 0.0000000001 := by norm_num at hx ⊢; nlinarith
      rw [inv_eq_one_div, div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  norm_num at l3 ⊢; linarith

lemma cc_bounds (LX : ℝ) (hLX : 10 ^ 14 ≤ LX) : 3.9999 ≤ cc LX ∧ cc LX ≤ 3.99992 := by
  unfold cc
  have hpos : 0 < 160 * (328 / 10) / LX := by positivity
  have hx : 160 * (328 / 10) / LX ≤ 10 ^ (-10 : ℤ) := by
    rw [div_le_iff₀ (by linarith)]; norm_num; linarith
  norm_num at hx ⊢; constructor <;> linarith

lemma fS_c_ge (g LX : ℝ) (hg : 0 ≤ g) (hLX : 10 ^ 14 ≤ LX) :
    g * 0.54930376 ≤ fS g (cc LX) := by
  unfold fS
  obtain ⟨c1, c2⟩ := cc_bounds LX hLX
  have hl := log_cm1_ge LX hLX
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hl hg, mul_le_mul_of_nonneg_left c2 hg]

lemma fS_a_ge (g : ℝ) (hg : 0 ≤ g) : g * 0.54930376 ≤ fS g (4 - 8 * α) := by
  unfold fS
  have e : (4 - 8 * α - 1 : ℝ) = 3 * (1 - 8 * α / 3) := by ring
  rw [e, log_mul (by norm_num) (by norm_num)]
  have h1 := Real.one_sub_inv_le_log_of_pos (x := (1 - 8 * α / 3 : ℝ)) (by norm_num)
  have l3 := log_three_gt_d9
  norm_num at h1 l3 ⊢
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

lemma fS_c_le (g LX : ℝ) (hg : 0 ≤ g) (hLX : 10 ^ 14 ≤ LX) : fS g (cc LX) ≤ g * 0.5494 := by
  unfold fS
  obtain ⟨c1, c2⟩ := cc_bounds LX hLX
  have hl : log (cc LX - 1) ≤ log 3 := log_le_log (by linarith) (by linarith)
  have l3 := log_three_lt_d9
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ log (cc LX - 1) := log_nonneg (by linarith)
  norm_num at l3 ⊢
  nlinarith

lemma log83_le : log (8 / 3 : ℝ) ≤ 0.98083 := by
  have e : log (8 / 3 : ℝ) = 3 * log 2 - log 3 := by
    rw [log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; push_cast; ring
  rw [e]; have := log_two_lt_d9; have := log_three_gt_d9; norm_num at *; linarith

lemma log83_nonneg : 0 ≤ log (8 / 3 : ℝ) := log_nonneg (by norm_num)

lemma r8_le (LX : ℝ) (hLX : 10 ^ 14 ≤ LX) :
    exp (LX / 8) / (exp (LX / 8) - 1) ≤ 1 + 1 / 10 ^ 12 := by
  have h := add_one_le_exp (LX / 8)
  have hE : 10 ^ 13 ≤ exp (LX / 8) := by linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma Lam_le : (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) ≤ 3.583658 := by
  have h6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
  have hr := log_le_sub_one_of_pos (x := (3 - 8 * α) / (3 - 18 * α)) (by norm_num)
  have := log_two_lt_d9; have := log_three_lt_d9
  rw [h6, div_le_iff₀ (by norm_num)]
  norm_num at *; linarith

lemma l2_le (g LX : ℝ) (hg : 0 ≤ g) (hLX : 10 ^ 14 ≤ LX) :
    l2 g LX ≤ (1 + 1 / 10 ^ 12) * (g / 4 * 3.5836581 + 0.98084 * ε * 106) := by
  unfold l2
  have hk : exp 2 * h kα = 1 := h_low kα (by norm_num) (by norm_num)
  have e : (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * exp 2 * h kα =
      (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * (exp 2 * h kα) := by ring
  rw [e, hk, mul_one]
  have hs1 : 512 / (kα * LX ^ 2) ≤ 1 / 10 ^ 7 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hs2 : 64 / LX ^ 2 ≤ 1 / 10 ^ 7 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hL := Lam_le
  have h8 := log83_le
  have hr := r8_le LX hLX
  have hpos : 0 ≤ g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
      512 / (kα * LX ^ 2)) + (log (8 / 3) + 64 / LX ^ 2) * ε * 106 := by
    have : 0 ≤ (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) := by
      apply div_nonneg _ (by norm_num)
      have : 0 ≤ log ((3 - 8 * α) / (3 - 18 * α)) :=
        log_nonneg (by rw [le_div_iff₀ (by norm_num)]; norm_num)
      have : 0 ≤ log (6 : ℝ) := log_nonneg (by norm_num)
      linarith
    have := log83_nonneg
    positivity
  have hin : g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
      512 / (kα * LX ^ 2)) + (log (8 / 3) + 64 / LX ^ 2) * ε * 106 ≤
      g / 4 * 3.5836581 + 0.98084 * ε * 106 := by
    have a1 : g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
        512 / (kα * LX ^ 2)) ≤ g / 4 * 3.5836581 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    have a2 : (log (8 / 3) + 64 / LX ^ 2) * ε * 106 ≤ 0.98084 * ε * 106 := by
      have : log (8 / 3) + 64 / LX ^ 2 ≤ 0.98084 := by norm_num at hs2 h8 ⊢; linarith
      have := mul_le_mul_of_nonneg_right this (by norm_num : (0:ℝ) ≤ ε * 106)
      linarith
    linarith
  calc exp (LX / 8) / (exp (LX / 8) - 1) * _ ≤ (1 + 1 / 10 ^ 12) *
        (g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
        512 / (kα * LX ^ 2)) + (log (8 / 3) + 64 / LX ^ 2) * ε * 106) :=
        mul_le_mul_of_nonneg_right hr hpos
    _ ≤ _ := mul_le_mul_of_nonneg_left hin (by norm_num)

lemma log1e0_ge : 3 / 100000 / (1 + 3 / 100000) ≤ log (1 + e0) := by
  have := Real.one_sub_inv_le_log_of_pos (x := 1 + e0) (by norm_num)
  have e : 1 - (1 + e0)⁻¹ = 3 / 100000 / (1 + 3 / 100000) := by norm_num
  linarith

lemma log1e0_le : log (1 + e0) ≤ 3 / 100000 := by
  have := log_le_sub_one_of_pos (x := 1 + e0) (by norm_num); norm_num at this ⊢; linarith

lemma tail_le (L : ℝ) (hL : 10 ^ 14 ≤ L) :
    0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0)) ≤ 1 / 10 ^ 12 := by
  have hE := pow_div_factorial_le_exp (x := L / 8) (by positivity) 7
  have hf : (Nat.factorial 7 : ℝ) = 5040 := by norm_num [Nat.factorial]
  rw [hf] at hE
  have hlg := log1e0_ge
  have hq : (0:ℝ) < 3 / 100000 / (1 + 3 / 100000) := by norm_num
  have hlg0 : 0 < log (1 + e0) := lt_of_lt_of_le hq hlg
  have hEp : 0 < exp (L / 8) := exp_pos _
  rw [div_le_iff₀ (by positivity)]
  have h1 : (L / 8) ^ 7 / 5040 * (3 / 100000 / (1 + 3 / 100000)) ≤ exp (L / 8) * log (1 + e0) :=
    mul_le_mul hE hlg (by positivity) hEp.le
  have h2 : 0.13 * (1 + e0) * L ^ 5 ≤ 1 / 10 ^ 12 * ((L / 8) ^ 7 / 5040 * (3 / 100000 / (1 + 3 / 100000))) := by
    have hL2 : (10 ^ 28 : ℝ) ≤ L ^ 2 := by nlinarith
    have : (L / 8) ^ 7 / 5040 * (3 / 100000 / (1 + 3 / 100000)) =
        L ^ 5 * L ^ 2 * (1 / (8 ^ 7 * 5040) * (3 / 100000 / (1 + 3 / 100000))) := by ring
    rw [this]
    have hL5 : 0 ≤ L ^ 5 := by positivity
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left hL2 hL5]
  nlinarith

lemma small_div (c L : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 100) (hL : 10 ^ 14 ≤ L) : c / L ≤ 1 / 10 ^ 12 := by
  rw [div_le_iff₀ (by linarith)]; nlinarith

lemma small_div2 (c L : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 100) (hL : 10 ^ 14 ≤ L) :
    c / L ^ 2 ≤ 1 / 10 ^ 26 := by
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- **Theorem 51 corrected, upper bound linear in `g`.** -/
lemma cB_le (g T e2 cb m L : ℝ) (hg : 0 ≤ g) (hT : 0.65 ≤ T) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hm : 0 ≤ m ∧ m ≤ 2 / 10 ^ 11) (hL : 10 ^ 14 ≤ L) :
    cB g T e2 cb m L ≤
      1.00005 * (1 + 1 / 51) * (1 + 1 / 10 ^ 26) * (2 / (1 / 2 - α) * g + 3 * ε * 106) *
        (1 + e0 + 1 / 10 ^ 12) * (0.363084 + 1 / 10 ^ 11) +
      g / 1.3 * (320 * (2 / 10 ^ 11) * (1 + e0) / (3 * (3 / 100000 / (1 + 3 / 100000))) +
        1 / 10 ^ 12) := by
  unfold cB
  have hk : exp 2 * h (3 / 2 - 3 * α) = 1 := h_low _ (by norm_num) (by norm_num)
  have e : 3 * ε * 106 * exp 2 * h (3 / 2 - 3 * α) = 3 * ε * 106 * (exp 2 * h (3 / 2 - 3 * α)) := by
    ring
  rw [e, hk, mul_one]
  have s1 := small_div2 4.51 L (by norm_num) (by norm_num) hL
  have s2 := small_div 9 L (by norm_num) (by norm_num) hL
  have s3 := small_div2 36 L (by norm_num) (by norm_num) hL
  have s4 := small_div2 64 L (by norm_num) (by norm_num) hL
  have s5 := small_div2 27 L (by norm_num) (by norm_num) hL
  have hl1 := log1e0_le
  have hl0 := log1e0_ge
  have hq : (0:ℝ) < 3 / 100000 / (1 + 3 / 100000) := by norm_num
  have hlp : 0 < log (1 + e0) := lt_of_lt_of_le hq hl0
  have s6 : 10 * log (1 + e0) / L ≤ 1 / 10 ^ 12 :=
    small_div _ L (by positivity)
      (le_trans (mul_le_mul_of_nonneg_left hl1 (by norm_num)) (by norm_num)) hL
  have h83 := log83_le
  have h83n := log83_nonneg
  have hA4 : cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2) ≤
      0.363084 + 1 / 10 ^ 11 := by
    have : (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2) ≤ 1 * (2 / 10 ^ 12) := by
      apply mul_le_mul (by norm_num at s4 h83 ⊢; linarith) (by norm_num at s5 s6 ⊢; linarith)
        (by positivity) (by norm_num)
    norm_num at this s3 ⊢; linarith
  have hA4n : 0 ≤ cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2) := by
    have := hcb.1; positivity
  have hT' : g / (2 * T) ≤ g / 1.3 := div_le_div_of_nonneg_left hg (by norm_num) (by linarith)
  have tl := tail_le L hL
  have hX : 320 * m * (1 + e0) / (3 * log (1 + e0)) ≤
      320 * (2 / 10 ^ 11) * (1 + e0) / (3 * (3 / 100000 / (1 + 3 / 100000))) := by
    apply div_le_div₀ (by norm_num) (by nlinarith [hm.2]) (by positivity) (by linarith)
  have hXn : 0 ≤ 320 * m * (1 + e0) / (3 * log (1 + e0)) +
      0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0)) := by
    have := hm.1; have := exp_pos (L / 8); positivity
  have part2 : g / (2 * T) * (320 * m * (1 + e0) / (3 * log (1 + e0)) +
      0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0))) ≤
      g / 1.3 * (320 * (2 / 10 ^ 11) * (1 + e0) / (3 * (3 / 100000 / (1 + 3 / 100000))) +
        1 / 10 ^ 12) :=
    mul_le_mul hT' (by linarith) hXn (by positivity)
  have part1 : 1.00005 * (1 + e2) * (1 + 4.51 / L ^ 2) * (2 / (1 / 2 - α) * g + 3 * ε * 106) *
      (1 + e0 + 9 / L) *
      (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2)) ≤
      1.00005 * (1 + 1 / 51) * (1 + 1 / 10 ^ 26) * (2 / (1 / 2 - α) * g + 3 * ε * 106) *
        (1 + e0 + 1 / 10 ^ 12) * (0.363084 + 1 / 10 ^ 11) := by
    have h45 : 0 ≤ 4.51 / L ^ 2 := by positivity
    have hLp : 0 < L := by linarith
    have h9 : 0 ≤ 9 / L := by positivity
    gcongr
    · linarith [he2.2]
  linarith

lemma cQb_le (g T e1 l1s ls L LX : ℝ) (hg : 0 ≤ g) (hT : 0.65 ≤ T) (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57)
    (hl1 : 0 ≤ l1s ∧ l1s ≤ 1 / 10 ^ 20) (hls : 0 ≤ ls ∧ ls ≤ 1 / 10 ^ 20)
    (hLX : 10 ^ 14 ≤ LX) (hL : LX ≤ L) :
    cQb g T e1 l1s ls L LX ≤ 8.0004 * (1 + 1 / 10 ^ 26) * (1 + 1 / 57) *
      (1 / 10 ^ 20 + (1 + 1 / 10 ^ 12) * (g / 4 * 3.5836581 + 0.98084 * ε * 106)) +
      1 / 10 ^ 20 * (g / 1.3) := by
  unfold cQb
  have s1 := small_div2 32.02 L (by norm_num) (by norm_num) (hLX.trans hL)
  have hl2 := l2_le g LX hg hLX
  have hT' : g / (2 * T) ≤ g / 1.3 := div_le_div_of_nonneg_left hg (by norm_num) (by linarith)
  have hl2n : 0 ≤ l2 g LX := by
    unfold l2
    have hE := add_one_le_exp (LX / 8)
    have h1 : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) := div_nonneg (exp_pos _).le (by linarith)
    have h2 : 0 ≤ (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) := by
      apply div_nonneg _ (by norm_num)
      have : 0 ≤ log ((3 - 8 * α) / (3 - 18 * α)) :=
        log_nonneg (by rw [le_div_iff₀ (by norm_num)]; norm_num)
      have : 0 ≤ log (6 : ℝ) := log_nonneg (by norm_num)
      linarith
    have := log83_nonneg
    have := h_nonneg kα (by norm_num)
    positivity
  have p1 : 8.0004 * (1 + 32.02 / L ^ 2) * (1 + e1) * (l1s + l2 g LX) ≤
      8.0004 * (1 + 1 / 10 ^ 26) * (1 + 1 / 57) *
        (1 / 10 ^ 20 + (1 + 1 / 10 ^ 12) * (g / 4 * 3.5836581 + 0.98084 * ε * 106)) := by
    have := hl1.1
    have : 0 ≤ 32.02 / L ^ 2 := by positivity
    gcongr
    all_goals first | exact he1.2 | exact hl1.2 | linarith
  have p2 : ls * (g / (2 * T)) ≤ 1 / 10 ^ 20 * (g / 1.3) :=
    mul_le_mul hls.2 hT' (div_nonneg hg (by linarith)) (by norm_num)
  linarith

lemma cQa_le (g T l1 l L LX : ℝ) (hg : 0 ≤ g) (hT : 0.65 ≤ T)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 20) (hls : 0 ≤ l ∧ l ≤ 1 / 10 ^ 20)
    (hLX : 10 ^ 14 ≤ LX) (hL : LX ≤ L) :
    cQa g T l1 l L LX ≤ 8.0004 * (1 + 1 / 10 ^ 26) *
      (1 / 10 ^ 20 + (1 + 1 / 10 ^ 12) * (g / 4 * 3.5836581 + 0.98084 * ε * 106)) +
      1 / 10 ^ 20 * (g / 1.3) := by
  unfold cQa
  -- redo without the (1 + 1/57) factor
  have s1 := small_div2 32.02 L (by norm_num) (by norm_num) (hLX.trans hL)
  have hl2 := l2_le g LX hg hLX
  have hT' : g / (2 * T) ≤ g / 1.3 := div_le_div_of_nonneg_left hg (by norm_num) (by linarith)
  have hl2n : 0 ≤ l2 g LX := by
    unfold l2
    have hE := add_one_le_exp (LX / 8)
    have h1 : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) := div_nonneg (exp_pos _).le (by linarith)
    have h2 : 0 ≤ (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) := by
      apply div_nonneg _ (by norm_num)
      have : 0 ≤ log ((3 - 8 * α) / (3 - 18 * α)) :=
        log_nonneg (by rw [le_div_iff₀ (by norm_num)]; norm_num)
      have : 0 ≤ log (6 : ℝ) := log_nonneg (by norm_num)
      linarith
    have := log83_nonneg
    have := h_nonneg kα (by norm_num)
    positivity
  have p1 : 8.0004 * (1 + 32.02 / L ^ 2) * (l1 + l2 g LX) ≤
      8.0004 * (1 + 1 / 10 ^ 26) *
        (1 / 10 ^ 20 + (1 + 1 / 10 ^ 12) * (g / 4 * 3.5836581 + 0.98084 * ε * 106)) := by
    have := hl1.1
    have : 0 ≤ 32.02 / L ^ 2 := by positivity
    gcongr
    all_goals first | exact hl1.2 | linarith
  have p2 : l * (g / (2 * T)) ≤ 1 / 10 ^ 20 * (g / 1.3) :=
    mul_le_mul hls.2 hT' (div_nonneg hg (by linarith)) (by norm_num)
  linarith

lemma mbar_le (g LX : ℝ) (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hLX : 10 ^ 14 ≤ LX)
    (hI : ∫ t in (2 : ℝ)..(cc LX - 1), log (t - 1) / t ≤ 0.1476) :
    max (1 - fS g (cc LX)) (FS g (cc LX) - 1) ≤ 0.02208 := by
  have h1 := fS_c_ge g LX (by linarith) hLX
  obtain ⟨c1, c2⟩ := cc_bounds LX hLX
  apply max_le
  · nlinarith
  · unfold FS
    have hgc : 2 * g / cc LX ≤ 2 * 1.7812 / 3.9999 := by
      apply div_le_div₀ (by norm_num) (by linarith) (by norm_num) c1
    have hgc0 : 0 ≤ 2 * g / cc LX := div_nonneg (by linarith) (by linarith)
    have : 2 * g / cc LX * (1 + ∫ t in (2 : ℝ)..(cc LX - 1), log (t - 1) / t) ≤
        2 * 1.7812 / 3.9999 * (1 + 0.1476) := by
      rcases le_total 0 (1 + ∫ t in (2 : ℝ)..(cc LX - 1), log (t - 1) / t) with hp | hp
      · exact mul_le_mul hgc (by linarith) hp (by norm_num)
      · have : 2 * g / cc LX * (1 + ∫ t in (2 : ℝ)..(cc LX - 1), log (t - 1) / t) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hgc0 hp
        have : (0 : ℝ) ≤ 2 * 1.7812 / 3.9999 * (1 + 0.1476) := by norm_num
        linarith
    norm_num at this ⊢; linarith

lemma cAb_ge (g T e1 a c4s w L LX : ℝ) (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (ha : 0 ≤ a ∧ a ≤ 1 / 10 ^ 18)
    (hc4 : 0 ≤ c4s ∧ c4s ≤ 1 / 10 ^ 20) (hw : 0 ≤ w ∧ w ≤ L)
    (hLX : 10 ^ 14 ≤ LX) (hL : LX ≤ L)
    (hI : ∫ t in (2 : ℝ)..(cc LX - 1), log (t - 1) / t ≤ 0.1476) :
    8 * ((58 / 57) * (0.54930376 * g) - 1 / 57 - (58 / 57) * ε * 107 * 0.1016 -
      (3 / 57 + 1 / 10 ^ 18) * (0.02208 + ε * 107 * 0.1016) - 3 / 10 ^ 18) ≤
      cAb g T e1 a c4s w L LX := by
  unfold cAb
  obtain ⟨c1, c2⟩ := cc_bounds LX hLX
  set X := fS g (cc LX) with hX
  set H := exp 2 * h (cc LX) with hH
  set Mb := max (1 - fS g (cc LX)) (FS g (cc LX) - 1) with hMb
  have hXl : g * 0.54930376 ≤ X := fS_c_ge g LX (by linarith) hLX
  have hXu : X ≤ g * 0.5494 := fS_c_le g LX (by linarith) hLX
  have hH1 : H ≤ 0.1016 := h_le _ c1
  have hH0 : 0 ≤ H := by have := h_nonneg (cc LX) (by linarith); positivity
  have hM : Mb ≤ 0.02208 := mbar_le g LX hg1 hg2 hLX hI
  have hM0 : 0 ≤ Mb := le_trans (by nlinarith) (le_max_left _ _)
  have hL0 : 0 < L := by linarith
  have eq1 : (1 + e1) * ε * 107 * exp 2 * h (cc LX) = (1 + e1) * ε * 107 * H := by rw [hH]; ring
  have eq2 : ε * 107 * exp 2 * h (cc LX) = ε * 107 * H := by rw [hH]; ring
  rw [eq1, eq2]
  have t1 : e1 * (1 - X) ≤ 1 / 57 * (1 - X) :=
    mul_le_mul_of_nonneg_right he1.2 (by nlinarith)
  have t2 : (1 + e1) * ε * 107 * H ≤ (58 / 57) * ε * 107 * 0.1016 := by
    have : (1 + e1) * (ε * 107) ≤ (58 / 57) * (ε * 107) :=
      mul_le_mul_of_nonneg_right (by linarith [he1.2]) (by norm_num)
    have := mul_le_mul this hH1 hH0 (by norm_num)
    linarith
  have t3 : (3 * e1 + a) * (Mb + ε * 107 * H) ≤ (3 / 57 + 1 / 10 ^ 18) * (0.02208 + ε * 107 * 0.1016) := by
    apply mul_le_mul (by linarith [he1.2, ha.2]) (by nlinarith) (by positivity)
      (by norm_num)
  have s1 := small_div2 64.04 L (by norm_num) (by norm_num) (hLX.trans hL)
  have s2 := small_div2 32.02 L (by norm_num) (by norm_num) (hLX.trans hL)
  have hd0 : 0 ≤ 32.02 / L ^ 2 := by positivity
  have t4 : 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w ≤ 1 / 10 ^ 20 := by
    have i1 : (1 + 32.02 / L ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have i0 : 0 ≤ (1 + 32.02 / L ^ 2)⁻¹ := by positivity
    have i2 : g / (2 * T) ≤ 1.4 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have i20 : 0 ≤ g / (2 * T) := div_nonneg (by linarith) (by linarith)
    have i3 : c4s / L * w ≤ 1 / 10 ^ 20 := by
      have : c4s / L * w ≤ c4s / L * L :=
        mul_le_mul_of_nonneg_left hw.2 (div_nonneg hc4.1 hL0.le)
      rw [div_mul_cancel₀ _ hL0.ne'] at this
      linarith [hc4.2]
    have i30 : 0 ≤ c4s / L * w := mul_nonneg (div_nonneg hc4.1 hL0.le) hw.1
    have : (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) ≤ 1 * 1.4 := mul_le_mul i1 i2 i20 (by norm_num)
    have : (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L * w) ≤ 1.4 * (1 / 10 ^ 20) :=
      mul_le_mul (by linarith) i3 i30 (by norm_num)
    have e : 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w =
        1 / 8 * ((1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L * w)) := by ring
    rw [e]; nlinarith
  set B := X - e1 * (1 - X) - (1 + e1) * ε * 107 * H - (3 * e1 + a) * (Mb + ε * 107 * H) - a -
    64.04 / L ^ 2 - 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w with hB
  have hBl : (58 / 57) * (0.54930376 * g) - 1 / 57 - (58 / 57) * ε * 107 * 0.1016 -
      (3 / 57 + 1 / 10 ^ 18) * (0.02208 + ε * 107 * 0.1016) - 3 / 10 ^ 18 ≤ B := by
    rw [hB]; linarith
  have hB0 : 0 ≤ B := by linarith
  calc 8 * ((58 / 57) * (0.54930376 * g) - 1 / 57 - (58 / 57) * ε * 107 * 0.1016 -
      (3 / 57 + 1 / 10 ^ 18) * (0.02208 + ε * 107 * 0.1016) - 3 / 10 ^ 18) ≤ 8 * 1 * B := by
        linarith
    _ ≤ 8 * (1 + 32.02 / L ^ 2) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0; linarith

lemma cAa_ge (g T c4 L : ℝ) (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T)
    (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 20) (hL : 10 ^ 14 ≤ L) :
    8 * (1 - 1 / 10 ^ 26) * (0.54930376 * g - 107 * ε * 0.1016 - 1 / 10 ^ 20) ≤ cAa g T c4 L := by
  unfold cAa
  have hX := fS_a_ge g (by linarith)
  have hH1 : exp 2 * h (4 - 8 * α) ≤ 0.1016 := h_le _ (by norm_num)
  have hH0 : 0 ≤ exp 2 * h (4 - 8 * α) := by have := h_nonneg (4 - 8 * α) (by norm_num); positivity
  have s2 := small_div2 32.02 L (by norm_num) (by norm_num) hL
  have hd0 : 0 ≤ 32.02 / L ^ 2 := by positivity
  have hL0 : 0 < L := by linarith
  have e : 107 * ε * exp 2 * h (4 - 8 * α) = 107 * ε * (exp 2 * h (4 - 8 * α)) := by ring
  rw [e]
  have t4 : 1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) ≤ 1 / 10 ^ 20 := by
    have i1 : (1 - 32.02 / L ^ 2)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by norm_num at s2 ⊢; linarith) (by norm_num)]; norm_num at s2 ⊢; linarith
    have i0 : 0 ≤ (1 - 32.02 / L ^ 2)⁻¹ := inv_nonneg.mpr (by norm_num at s2 ⊢; linarith)
    have i2 : g / (2 * T) ≤ 1.4 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have i20 : 0 ≤ g / (2 * T) := div_nonneg (by linarith) (by linarith)
    have i3 : c4 / L ≤ 1 / 10 ^ 20 := by
      have := small_div c4 L hc4.1 (by linarith [hc4.2]) hL
      have : c4 / L ≤ c4 := div_le_self hc4.1 (by linarith)
      linarith [hc4.2]
    have i30 : 0 ≤ c4 / L := div_nonneg hc4.1 hL0.le
    have : (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) ≤ 2 * 1.4 := mul_le_mul i1 i2 i20 (by norm_num)
    have : (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) ≤ 2.8 * (1 / 10 ^ 20) :=
      mul_le_mul (by linarith) i3 i30 (by norm_num)
    have e : 1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) =
        1 / 8 * ((1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L)) := by ring
    rw [e]; nlinarith
  set B := fS g (4 - 8 * α) - 107 * ε * (exp 2 * h (4 - 8 * α)) -
    1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) with hB
  have hBl : 0.54930376 * g - 107 * ε * 0.1016 - 1 / 10 ^ 20 ≤ B := by
    rw [hB]
    have := mul_le_mul_of_nonneg_left hH1 (by norm_num : (0:ℝ) ≤ 107 * ε)
    linarith
  have hB0 : 0 ≤ 0.54930376 * g - 107 * ε * 0.1016 - 1 / 10 ^ 20 := by norm_num; linarith
  calc 8 * (1 - 1 / 10 ^ 26) * (0.54930376 * g - 107 * ε * 0.1016 - 1 / 10 ^ 20)
      ≤ 8 * (1 - 32.02 / L ^ 2) * (0.54930376 * g - 107 * ε * 0.1016 - 1 / 10 ^ 20) := by
        apply mul_le_mul_of_nonneg_right _ hB0; norm_num at s2 ⊢; linarith
    _ ≤ 8 * (1 - 32.02 / L ^ 2) * B := by
        apply mul_le_mul_of_nonneg_left hBl; norm_num at s2 ⊢; linarith

/-- **Section 9, case (b), corrected constants, PROVED from the stated inputs:**
`cA - cQ/2 - cB/2 ≥ 2·10⁻⁴ + 10⁻¹²` at `log log X₂ = 32.8`. Margin about `4.2·10⁻⁴` with these
input bounds; `8.3·10⁻³` short at the printed parameters, see FINDINGS F-0023. -/
theorem margin_b (g T e1 e2 cb m a c4s w l1s ls L LX : ℝ)
    (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T)
    (he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hm : 0 ≤ m ∧ m ≤ 2 / 10 ^ 11)
    (ha : 0 ≤ a ∧ a ≤ 1 / 10 ^ 18) (hc4 : 0 ≤ c4s ∧ c4s ≤ 1 / 10 ^ 20) (hw : 0 ≤ w ∧ w ≤ L)
    (hl1 : 0 ≤ l1s ∧ l1s ≤ 1 / 10 ^ 20) (hls : 0 ≤ ls ∧ ls ≤ 1 / 10 ^ 20)
    (hLX : 10 ^ 14 ≤ LX) (hL : LX ≤ L)
    (hI : ∫ t in (2 : ℝ)..(cc LX - 1), log (t - 1) / t ≤ 0.1476) :
    2 / 10000 + 1 / 10 ^ 12 ≤
      cAb g T e1 a c4s w L LX - cQb g T e1 l1s ls L LX / 2 - cB g T e2 cb m L / 2 := by
  have hA := cAb_ge g T e1 a c4s w L LX hg1 hg2 hT he1 ha hc4 hw hLX hL hI
  have hQ := cQb_le g T e1 l1s ls L LX (by linarith) hT he1 hl1 hls hLX hL
  have hB := cB_le g T e2 cb m L (by linarith) hT he2 hcb hm (hLX.trans hL)
  norm_num at hA hQ hB ⊢
  linarith

/-- **Section 9, case (a), corrected constants, PROVED from the stated inputs:**
`cA - cQ/2 - cB/2 ≥ 2·10⁻⁴ + 10⁻¹²`; in fact about `0.1247 ≥ 1/10`. -/
theorem margin_a (g T e2 cb m c4 l1 l L LX : ℝ)
    (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.65 ≤ T) (he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hm : 0 ≤ m ∧ m ≤ 2 / 10 ^ 11)
    (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 20)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 20) (hls : 0 ≤ l ∧ l ≤ 1 / 10 ^ 20)
    (hLX : 10 ^ 14 ≤ LX) (hL : LX ≤ L) :
    1 / 10 ≤ cAa g T c4 L - cQa g T l1 l L LX / 2 - cB g T e2 cb m L / 2 := by
  have hA := cAa_ge g T c4 L hg1 hg2 hT hc4 (hLX.trans hL)
  have hQ := cQa_le g T l1 l L LX (by linarith) hT hl1 hls hLX hL
  have hB := cB_le g T e2 cb m L (by linarith) hT he2 hcb hm (hLX.trans hL)
  norm_num at hA hQ hB ⊢
  linarith

end LeanLab.ChenExplicit.Section9
