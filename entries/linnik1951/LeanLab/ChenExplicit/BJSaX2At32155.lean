module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: stage 3 of gen/port3220_U6718.py, the 3216 file below ported to log log X₂ = 32.155, δ₁ = 1.5026, δ₂ = 1.47088, ε₁ = 1/57, ε₂ = 1/51, ν(x₁) log x₁ ≥ 125, ν ℓ ≥ 145.7 so m(X₃) ≤ 3.81·10⁻¹⁰, ε₀ = 1.45·10⁻⁴, floor 9·10¹³ via Section9F9. The header below is the 3216 one, itself a port; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: stage 2 of gen/port3220_U6718.py, the 3220 file below ported to log log X₂ = 32.16, δ₁ = 1.5024, δ₂ = 1.4707, ε₁ = 1/57, ε₂ = 1/51, ν(x₁) log x₁ ≥ 125, the Siegel term of (87) ≤ 10⁻²³ and p(X₂) ≤ 10⁻²², ν ℓ ≥ 146.3 so m(X₃) ≤ 2.17·10⁻¹⁰, ε₀ = 1.1·10⁻⁴, floor 9·10¹³ via Section9F9. The header below is the 3220 one; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: a scripted port by gen/port3220_U6718.py of the 3225 file of U-6713 to log log X₂ = 32.2, α = 10⁻⁵, Lemma 18 at u₀ = 10⁸ with ε = 1.91·10⁻⁷, δ₁ = 1.5005 for Theorems 44 and 50 and δ₂ = 1.4688 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 1.1·10⁻¹¹ with ν ℓ ≥ 152, ν(x₁) log x₁ ≥ 130, the Siegel term of (87) ≤ 3·10⁻²⁵, p(X₂) ≤ 10⁻²⁴ unchanged, and the floor log X₂ ≥ 10¹⁴ lowered to 9·10¹³ through Section9F9.lean. The 3225 header follows unchanged; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6713, track T2: a scripted port by gen/port3225_U6713.py of the 3230 file of cloud46 U-6602 to log log X₂ = 32.25, α = 10⁻⁵, Lemma 18 at u₀ = 10⁸ with ε = 1.91·10⁻⁷ through Section9U8.lean, δ₁ = 1.4985 for Theorems 44 and 50 and δ₂ = 1.4665 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 10⁻¹¹ with ν ℓ ≥ 158; ν(x₁) log x₁ ≥ 135 in place of 145, so the Siegel term of (87) is bounded by 10⁻²⁶ in place of 10⁻³⁰, p(X₂) ≤ 10⁻²⁴ unchanged. Numeric lemmas retightened by the HAND table of the script. The 3230 header follows unchanged; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1618Z-cloud46, unit U-6602, track T2: a scripted port by gen/port3230_U6602.py of the 3270 file of cloud42 U-6403 to log log X₂ = 32.3, α = 10⁻⁵, with δ₁ = 1.496 for Theorems 44 and 50 and δ₂ = 1.464 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 10⁻¹¹; numeric lemmas retightened where the build required. The 3270 header follows, its numbers updated by the same script.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1217Z-cloud42, unit U-6403, track T1: a scripted port by gen/port3230_U6403.py of the 32.716 file of PC U-1045 to the printed log log X₂ = 32.3, α = 10⁻⁵, with δ₁ = 1.496 for Theorems 44 and 50 and δ₂ = 1.445 for Theorem 51, ε₀ = 2·10⁻⁵, m(X₃) ≤ 10⁻¹¹; numeric lemmas retightened where the build required. The 32.716 header follows, its numbers updated by the same script.
AI-written Lean code, Claude, 2026-10-19, CLOUD-built run 20261019T0903Z-22821 of the PC lab, unit U-1045, track T2, a scripted port of BJSaX2At3272.lean of PC run 20261019T0703Z-249, U-1041, to log log X₂ = 32.3, δ = 1.496, ε₀ = 2·10⁻⁵, m(X₃) ≤ 10⁻¹¹; numeric lemmas retightened where the build required. The ported header follows, its numbers updated by the same script.
PORT to log log X₂ = 32.3, δ = 1.496, PC run 20261019T0703Z-249, unit U-1041, a sed port of the cloud 32.33 file of U-5042, CLOUD 20261019T0114Z-cloud13, from BJSaX2.lean by
script /tmp port3230.py: every 32.8 → 32.3, 1.476 → 1.496; numeric lemmas retightened where
the build failed, listed in PROGRESS.md. Original header follows.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0803Z-19871, unit U-0930.
P0009 Bordignon-Johnston-Starichkova 2022, arXiv 2207.09452 v6, read in Claude in Chrome:
the constant a(X₂) of (138), with c₃(X₂) of (129) and a₁(X₂) of (139), at
X₂ = exp(exp 32.3), δ = 1.496.

Why: Section9Link.lean's `margin_b_X2` took `a(X₂) ≤ 10⁻²⁰` as a hypothesis, TESTED in the
2026-10-18 Python model, but that model never computed a(X₂). It is about 1.16e-19,
numerics/aX2_U0930.py, because a(X₂) carries the factor log log log N / log^δ N, about
e^{-48.4}, not a power of X₂. The hypothesis was false; Section9.lean now takes
`a ≤ 10⁻¹⁸`, and the margin still closes. This file PROVES a(X₂) ≤ 10⁻¹⁸, given the c₂ term
of (139) below 10⁻²⁰, which is X₂-only like the other hypotheses.

Everything is written in t = log log N, so N = exp(exp t), log N = L = exp t, and
log x₁ = L - 5t by (75). `log log (log^δ x₁)` is `log (δ · log (log x₁))` and
`log log (log^{10} x₁)` is `log (10 · log (log x₁))`. The product ∏_{p>2} (p-1)²/(p(p-2)) is
1/T with T the twin prime constant ∏_{p>2} (1 - 1/(p-1)²), taken here as a parameter with
T ≥ 0.65, which `TwinCNumeric.twinC_ge_065` proves.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.BJSaX2At32155

def δ : ℝ := 1.5026

/-- (129), the bracket of c₃(X₂) at `N = exp(exp t)`. -/
def c3f (g t : ℝ) : ℝ :=
  (1 / log t) * (3 / (2 * exp t) + (exp t + 10 * log (exp t - 5 * t)) /
      (exp t - 10 * log (exp t - 5 * t))) * (exp t / (exp t - 5 * t)) ^ δ *
    (g * log (δ * log (exp t - 5 * t)) + 5 / (2 * log (δ * log (exp t - 5 * t)))) +
  1.3841 * (exp t) ^ (2 + δ) / (exp (exp t) * t * log t)

/-- (138), the bracket of a(X₂) at `N = exp(exp t)`, with `1/T` for the prime product. -/
def abr (g T t : ℝ) : ℝ :=
  log t / (exp t) ^ δ * (1 / T) *
    (g * log (10 * log (exp t - 5 * t)) + 2.5 / log (10 * log (exp t - 5 * t)))

/-! ## Elementary bounds for `t ≥ 32.155` -/

lemma exp328_ge : (9.21e13 : ℝ) ≤ exp 32.155 := by
  have e : exp (32.155 : ℝ) = exp 1 ^ 32 * exp 0.155 := by rw [exp_one_pow, ← exp_add]; norm_num
  have h1 : (2.7182818283 : ℝ) ^ 32 ≤ exp 1 ^ 32 :=
    pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 32
  have h2 : (1.167 : ℝ) ≤ exp 0.155 := by
    have := quadratic_le_exp_of_nonneg (x := (0.155 : ℝ)) (by norm_num); norm_num at this ⊢; linarith
  have h3 : (2.7182818283 : ℝ) ^ 32 * 1.167 ≤ exp 1 ^ 32 * exp 0.155 :=
    mul_le_mul h1 h2 (by norm_num) (by positivity)
  have h4 : (9.21e13 : ℝ) ≤ (2.7182818283 : ℝ) ^ 32 * 1.167 := by norm_num
  rw [e]; linarith

lemma expt_ge {t : ℝ} (ht : 32.155 ≤ t) : (9.21e13 : ℝ) * (1 + (t - 32.155)) ≤ exp t := by
  have e : exp t = exp 32.155 * exp (t - 32.155) := by rw [← exp_add]; ring_nf
  have h1 := add_one_le_exp (t - 32.155)
  rw [e]
  have h0 : 0 ≤ 1 + (t - 32.155) := by linarith
  calc (9.21e13 : ℝ) * (1 + (t - 32.155)) ≤ exp 32.155 * (1 + (t - 32.155)) :=
        mul_le_mul_of_nonneg_right exp328_ge h0
    _ ≤ exp 32.155 * exp (t - 32.155) :=
        mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le

lemma L_ge {t : ℝ} (ht : 32.155 ≤ t) : (9.21e13 : ℝ) ≤ exp t := by
  have := expt_ge ht; nlinarith

/-- `t ≤ 3.5e-13 · exp t`. -/
lemma t_le {t : ℝ} (ht : 32.155 ≤ t) : t ≤ 3.5e-13 * exp t := by
  have := expt_ge ht
  nlinarith

lemma Lx_ge {t : ℝ} (ht : 32.155 ≤ t) : exp t / 2 ≤ exp t - 5 * t := by
  have := t_le ht; have := L_ge ht; nlinarith

lemma Lx_le {t : ℝ} (ht : 32.155 ≤ t) : exp t - 5 * t ≤ exp t := by linarith

lemma Lx_pos {t : ℝ} (ht : 32.155 ≤ t) : 0 < exp t - 5 * t := by
  have := Lx_ge ht; have := exp_pos t; linarith

lemma logLx_le {t : ℝ} (ht : 32.155 ≤ t) : log (exp t - 5 * t) ≤ t := by
  have := log_le_log (Lx_pos ht) (Lx_le ht); rwa [log_exp] at this

lemma logLx_ge {t : ℝ} (ht : 32.155 ≤ t) : t - 0.7 ≤ log (exp t - 5 * t) := by
  have h := log_le_log (by positivity) (Lx_ge ht)
  rw [log_div (exp_pos t).ne' (by norm_num), log_exp] at h
  have := log_two_lt_d9
  linarith

lemma log2_gt : (0.6931471803 : ℝ) < log 2 := log_two_gt_d9

/-- `log t ≥ 5 log 2 > 3.4657` for `t ≥ 32`. -/
lemma logt_ge {t : ℝ} (ht : 32.155 ≤ t) : 3.4657 ≤ log t := by
  have h : log 32 ≤ log t := log_le_log (by norm_num) (by linarith)
  have e : log (32 : ℝ) = 5 * log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, log_pow]; norm_num
  have := log2_gt
  linarith

/-- `log t ≤ 3.4908 + (t - 32.155)/32.155`. -/
lemma logt_le {t : ℝ} (ht : 32.155 ≤ t) : log t ≤ 3.4908 + (t - 32.155) / 32.155 := by
  have h1 : log t = log 32.155 + log (t / 32.155) := by
    rw [← log_mul (by norm_num) (by positivity)]; congr 1; field_simp
  have h2 := log_le_sub_one_of_pos (show (0 : ℝ) < t / 32.155 by positivity)
  have h3 : log (32.155 : ℝ) = log 32 + log (32.155 / 32) := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have h4 := log_le_sub_one_of_pos (show (0 : ℝ) < 32.155 / 32 by norm_num)
  have e : log (32 : ℝ) = 5 * log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, log_pow]; norm_num
  have := log_two_lt_d9
  have h5 : t / 32.155 - 1 = (t - 32.155) / 32.155 := by field_simp
  rw [h1, h3]; norm_num at h2 h4 h5 ⊢; linarith

lemma logδ_le : log δ ≤ 0.41 := by
  unfold δ
  rw [log_le_iff_le_exp (by norm_num)]
  have h := sum_le_exp_of_nonneg (x := (0.41 : ℝ)) (by norm_num) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢; linarith

/-- `log (δ log x₁) ≥ 3.78`: `δ (t - 0.7) ≥ 47.26` and `log 47.26 ≥ 5 log 2 + (1 - 32/47.26)`. -/
lemma logδLx_ge {t : ℝ} (ht : 32.155 ≤ t) : 3.78 ≤ log (δ * log (exp t - 5 * t)) := by
  have hl := logLx_ge ht
  have hy : (47.26 : ℝ) ≤ δ * log (exp t - 5 * t) := by unfold δ; nlinarith
  have h1 : log 47.26 ≤ log (δ * log (exp t - 5 * t)) := log_le_log (by norm_num) hy
  have h2 : log (47.26 : ℝ) = log 32 + log (47.26 / 32) := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have h3 := one_sub_inv_le_log_of_pos (show (0 : ℝ) < 47.26 / 32 by norm_num)
  have e : log (32 : ℝ) = 5 * log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, log_pow]; norm_num
  have := log2_gt
  norm_num at h3
  linarith

lemma logδLx_le {t : ℝ} (ht : 32.155 ≤ t) : log (δ * log (exp t - 5 * t)) ≤ log δ + log t := by
  have hl := logLx_le ht
  have hl0 : 0 < log (exp t - 5 * t) := by have := logLx_ge ht; linarith
  rw [← log_mul (by unfold δ; norm_num) (by linarith)]
  apply log_le_log (by unfold δ; positivity)
  unfold δ; nlinarith

/-! ## c₃(X₂) ≤ 2.2 -/

lemma ratio_le {t : ℝ} (ht : 32.155 ≤ t) :
    (exp t + 10 * log (exp t - 5 * t)) / (exp t - 10 * log (exp t - 5 * t)) ≤ 1 + 1e-10 := by
  have hl := logLx_le ht
  have hl0 : 0 < log (exp t - 5 * t) := by have := logLx_ge ht; linarith
  have h1 := t_le ht
  have hL := L_ge ht
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

lemma pow_le' {t : ℝ} (ht : 32.155 ≤ t) : (exp t / (exp t - 5 * t)) ^ δ ≤ 1 + 1e-11 := by
  have hx := Lx_pos ht
  have h1 := t_le ht
  have hL := L_ge ht
  have hb1 : 1 ≤ exp t / (exp t - 5 * t) := by
    rw [le_div_iff₀ hx]; linarith
  have hb2 : exp t / (exp t - 5 * t) ≤ 1 + 2e-12 := by
    rw [div_le_iff₀ hx]; nlinarith
  have h2 : (exp t / (exp t - 5 * t)) ^ δ ≤ (exp t / (exp t - 5 * t)) ^ (2 : ℝ) :=
    rpow_le_rpow_of_exponent_le hb1 (by unfold δ; norm_num)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast] at h2
  have h3 : (exp t / (exp t - 5 * t)) ^ 2 ≤ (1 + 2e-12) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hb2 2
  have h4 : ((1 : ℝ) + 2e-12) ^ 2 ≤ 1 + 1e-11 := by norm_num
  linarith

lemma pow_nonneg' {t : ℝ} (ht : 32.155 ≤ t) : 0 ≤ (exp t / (exp t - 5 * t)) ^ δ :=
  rpow_nonneg (div_nonneg (exp_pos t).le (Lx_pos ht).le) _

/-- The `g`-bracket over `log t`: at most `2.1828`. -/
lemma inner_le {g t : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1.7812) (ht : 32.155 ≤ t) :
    (1 / log t) * (g * log (δ * log (exp t - 5 * t)) +
      5 / (2 * log (δ * log (exp t - 5 * t)))) ≤ 2.1828 := by
  have hlt := logt_ge ht
  have hu := logδLx_le ht
  have hd := logδ_le
  have hlo := logδLx_ge ht
  set ℓ := log (δ * log (exp t - 5 * t)) with hℓ
  set m := log t with hm
  have hm0 : 0 < m := by linarith
  have e : (1 / m) * (g * ℓ + 5 / (2 * ℓ)) = g * ℓ / m + 5 / (2 * ℓ * m) := by
    field_simp
  rw [e]
  have a1 : g * ℓ / m ≤ g + g * 0.41 / 3.4657 := by
    rw [div_le_iff₀ hm0]
    have : g * ℓ ≤ g * (log δ + m) := mul_le_mul_of_nonneg_left hu hg0
    have : g * log δ ≤ g * 0.41 := mul_le_mul_of_nonneg_left hd hg0
    have : g * 0.41 / 3.4657 * m ≥ g * 0.41 := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
      nlinarith
    nlinarith
  have a2 : 5 / (2 * ℓ * m) ≤ 5 / (2 * 3.78 * 3.4657) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : 2 * 3.78 * 3.4657 ≤ 2 * ℓ * 3.4657 := by nlinarith
    nlinarith
  have a3 : g + g * 0.41 / 3.4657 ≤ 1.7812 + 1.7812 * 0.41 / 3.4657 := by
    have : g * 0.41 / 3.4657 ≤ 1.7812 * 0.41 / 3.4657 := by
      apply div_le_div_of_nonneg_right _ (by norm_num); nlinarith
    linarith
  have a4 : (1.7812 : ℝ) + 1.7812 * 0.41 / 3.4657 + 5 / (2 * 3.78 * 3.4657) ≤ 2.1828 := by
    norm_num
  linarith

lemma inner_nonneg {g t : ℝ} (hg0 : 0 ≤ g) (ht : 32.155 ≤ t) :
    0 ≤ (1 / log t) * (g * log (δ * log (exp t - 5 * t)) +
      5 / (2 * log (δ * log (exp t - 5 * t)))) := by
  have hlt := logt_ge ht
  have hlo := logδLx_ge ht
  apply mul_nonneg (by positivity)
  apply add_nonneg (mul_nonneg hg0 (by linarith))
  apply div_nonneg (by norm_num) (by linarith)

/-- The last term of (129), `1.3841 log^{2+δ} N / (N log log N log log log N)`, below `10⁻¹⁰`. -/
lemma tail_le {t : ℝ} (ht : 32.155 ≤ t) :
    1.3841 * (exp t) ^ (2 + δ) / (exp (exp t) * t * log t) ≤ 1e-10 := by
  have hL := L_ge ht
  have hlt := logt_ge ht
  set L := exp t with hLdef
  have hL1 : 1 ≤ L := by linarith
  have h1 : L ^ (2 + δ) ≤ L ^ (4 : ℝ) := rpow_le_rpow_of_exponent_le hL1 (by unfold δ; norm_num)
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast] at h1
  have h2 : L ^ 5 / 120 ≤ exp L := by
    have := pow_div_factorial_le_exp L (by linarith) 5
    simpa [Nat.factorial] using this
  have hpos : 0 < exp L * t * log t := by
    have := exp_pos L; have : 0 < t := by linarith
    have : 0 < log t := by linarith
    positivity
  rw [div_le_iff₀ hpos]
  have h3 : L ^ 5 / 120 * t * log t ≤ exp L * t * log t := by
    have : 0 < t := by linarith
    have : 0 < log t := by linarith
    gcongr
  have h4 : 1.3841 * L ^ 4 ≤ 1e-10 * (L ^ 5 / 120 * t * log t) := by
    have : 0 < L ^ 4 := by positivity
    have hk : 1e-10 * (L ^ 5 / 120 * t * log t) = L ^ 4 * (1e-10 * L * t * log t / 120) := by ring
    rw [hk]
    have : 1.3841 ≤ 1e-10 * L * t * log t / 120 := by
      rw [le_div_iff₀ (by norm_num)]
      have : (9.21e13 : ℝ) * 32.155 * 3.4657 ≤ L * t * log t := by
        have : (0 : ℝ) ≤ 32.155 := by norm_num
        have h5 : (9.21e13 : ℝ) * 32.155 ≤ L * t := by
          have := mul_le_mul (show (9.21e13 : ℝ) ≤ L by norm_num at hL ⊢; linarith) ht (by norm_num)
            (by linarith)
          linarith
        nlinarith
      nlinarith
    nlinarith
  have h5 : 1.3841 * L ^ (2 + δ) ≤ 1.3841 * L ^ 4 := by linarith
  nlinarith

lemma tail_nonneg {t : ℝ} (ht : 32.155 ≤ t) :
    0 ≤ 1.3841 * (exp t) ^ (2 + δ) / (exp (exp t) * t * log t) := by
  have hlt := logt_ge ht
  have : 0 < t := by linarith
  apply div_nonneg (mul_nonneg (by norm_num) (rpow_nonneg (exp_pos t).le _))
  have : 0 < log t := by linarith
  have := exp_pos (exp t)
  positivity

/-- **c₃ bracket at most 2.2 for every `N ≥ X₂ = exp(exp 32.155)`.** -/
theorem c3f_le {g t : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1.7812) (ht : 32.155 ≤ t) : c3f g t ≤ 2.2 := by
  unfold c3f
  have hA := ratio_le ht
  have hL := L_ge ht
  have hP := pow_le' ht
  have hP0 := pow_nonneg' ht
  have hI := inner_le hg0 hg ht
  have hI0 := inner_nonneg hg0 ht
  have hT := tail_le ht
  have hr0 : 0 ≤ (exp t + 10 * log (exp t - 5 * t)) / (exp t - 10 * log (exp t - 5 * t)) := by
    have hl := logLx_le ht
    have hl0 : 0 < log (exp t - 5 * t) := by have := logLx_ge ht; linarith
    have h1 := t_le ht
    apply div_nonneg (by linarith) (by nlinarith)
  have h3 : 3 / (2 * exp t) ≤ 2e-14 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h30 : 0 ≤ 3 / (2 * exp t) := by positivity
  set A := 3 / (2 * exp t) + (exp t + 10 * log (exp t - 5 * t)) / (exp t - 10 * log (exp t - 5 * t))
  set B := (exp t / (exp t - 5 * t)) ^ δ
  set I := (1 / log t) * (g * log (δ * log (exp t - 5 * t)) +
      5 / (2 * log (δ * log (exp t - 5 * t))))
  have e : (1 / log t) * A * B * (g * log (δ * log (exp t - 5 * t)) +
      5 / (2 * log (δ * log (exp t - 5 * t)))) = A * B * I := by ring
  rw [e]
  have hA' : A ≤ 1 + 2e-10 := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hAB : A * B ≤ (1 + 2e-10) * (1 + 1e-11) := mul_le_mul hA' hP hP0 (by norm_num)
  have hAB0 : 0 ≤ A * B := mul_nonneg hA0 hP0
  have : A * B * I ≤ (1 + 2e-10) * (1 + 1e-11) * 2.1828 := mul_le_mul hAB hI hI0 (by norm_num)
  have : ((1 : ℝ) + 2e-10) * (1 + 1e-11) * 2.1828 ≤ 2.1829 := by norm_num
  linarith

/-! ## The a(X₂) bracket at most 6.5e-20 -/

lemma exp4831_ge : (9.1e20 : ℝ) ≤ exp 48.31 := by
  have e : exp (48.31 : ℝ) = exp 1 ^ 48 * exp 0.31 := by rw [exp_one_pow, ← exp_add]; norm_num
  have h1 : (2.7182818283 : ℝ) ^ 48 ≤ exp 1 ^ 48 :=
    pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 48
  have h2 : (1.31 : ℝ) ≤ exp 0.31 := by have := add_one_le_exp (0.31 : ℝ); linarith
  have h3 : (2.7182818283 : ℝ) ^ 48 * 1.31 ≤ exp 1 ^ 48 * exp 0.31 :=
    mul_le_mul h1 h2 (by norm_num) (by positivity)
  have h4 : (9.1e20 : ℝ) ≤ (2.7182818283 : ℝ) ^ 48 * 1.31 := by norm_num
  rw [e]; linarith

lemma log10_le : log (10 : ℝ) ≤ 2.3295 := by
  have h1 : log (10 : ℝ) = log 8 + log (10 / 8) := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have h2 := log_le_sub_one_of_pos (show (0 : ℝ) < 10 / 8 by norm_num)
  have e : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; norm_num
  have := log_two_lt_d9
  norm_num at h2; linarith

lemma log10Lx_ge {t : ℝ} (ht : 32.155 ≤ t) : 5.545 ≤ log (10 * log (exp t - 5 * t)) := by
  have hl := logLx_ge ht
  have h1 : log 256 ≤ log (10 * log (exp t - 5 * t)) := log_le_log (by norm_num) (by nlinarith)
  have e : log (256 : ℝ) = 8 * log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, log_pow]; norm_num
  have := log2_gt
  linarith

lemma log10Lx_le {t : ℝ} (ht : 32.155 ≤ t) : log (10 * log (exp t - 5 * t)) ≤ 2.3295 + log t := by
  have hl := logLx_le ht
  have hl0 : 0 < log (exp t - 5 * t) := by have := logLx_ge ht; linarith
  have h : log (10 * log (exp t - 5 * t)) ≤ log (10 * t) :=
    log_le_log (by positivity) (by linarith)
  have h' : log (10 * t) = log 10 + log t := log_mul (by norm_num) (by linarith)
  linarith [log10_le]

/-- **The bracket of (138) at most 6.5e-20 for every `N ≥ X₂`**, given `T ≥ 0.65`. -/
theorem abr_le {g T t : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1.7812) (hT : 0.65 ≤ T) (ht : 32.155 ≤ t) :
    abr g T t ≤ 6.5e-20 := by
  unfold abr
  set v := t - 32.155 with hv
  have hv0 : 0 ≤ v := by linarith
  have hlt := logt_ge ht
  have hlu := logt_le ht
  have hlo := log10Lx_ge ht
  have hlh := log10Lx_le ht
  set ℓ := log (10 * log (exp t - 5 * t))
  set m := log t
  -- the exponential
  have hE : (exp t) ^ δ = exp (t * δ) := by rw [← exp_mul]
  have hE2 : exp (t * δ) = exp (32.155 * δ) * exp (δ * v) := by
    rw [← exp_add]; congr 1; rw [hv]; ring
  have hq := quadratic_le_exp_of_nonneg (show 0 ≤ δ * v from mul_nonneg (by unfold δ; norm_num) hv0)
  have h48 : (9.1e20 : ℝ) ≤ exp (32.155 * δ) := by
    have : exp 48.31 ≤ exp (32.155 * δ) := exp_le_exp.mpr (by unfold δ; norm_num)
    linarith [exp4831_ge]
  set Q := 1 + δ * v + (δ * v) ^ 2 / 2 with hQ
  have hQ0 : 0 < Q := by
    rw [hQ]; have := mul_nonneg (show (0:ℝ) ≤ δ by unfold δ; norm_num) hv0
    nlinarith [sq_nonneg (δ * v)]
  have hden : 9.1e20 * Q ≤ (exp t) ^ δ := by
    rw [hE, hE2]
    exact mul_le_mul h48 hq hQ0.le (exp_pos _).le
  -- the bracket
  have hb : g * ℓ + 2.5 / ℓ ≤ 4.6003 + 1.7812 * m := by
    have a1 : g * ℓ ≤ 1.7812 * (2.3295 + m) := by
      have : g * ℓ ≤ g * (2.3295 + m) := mul_le_mul_of_nonneg_left hlh hg0
      have : g * (2.3295 + m) ≤ 1.7812 * (2.3295 + m) := mul_le_mul_of_nonneg_right hg (by linarith)
      linarith
    have a2 : 2.5 / ℓ ≤ 2.5 / 5.545 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlo
    have : (2.5 : ℝ) / 5.545 ≤ 0.4509 := by norm_num
    nlinarith
  have hb0 : 0 ≤ g * ℓ + 2.5 / ℓ := add_nonneg (mul_nonneg hg0 (by linarith)) (by positivity)
  have hm0 : 0 < m := by linarith
  have hnum : m * (g * ℓ + 2.5 / ℓ) ≤ 37.77 * Q := by
    have : m * (g * ℓ + 2.5 / ℓ) ≤ (3.4908 + v / 32.155) * (4.6003 + 1.7812 * (3.4908 + v / 32.155)) := by
      have hb' : g * ℓ + 2.5 / ℓ ≤ 4.6003 + 1.7812 * (3.4908 + v / 32.155) := by
        have : 1.7812 * m ≤ 1.7812 * (3.4908 + v / 32.155) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num); rw [hv]; linarith
        linarith
      apply mul_le_mul (by rw [hv]; linarith) hb' hb0 (by positivity)
    have : (3.4908 + v / 32.155) * (4.6003 + 1.7812 * (3.4908 + v / 32.155)) ≤ 37.77 * Q := by
      simp only [hQ, δ]; ring_nf; nlinarith [mul_nonneg hv0 hv0, hv0]
    linarith
  have hT0 : 0 < T := by linarith
  have hEpos : 0 < (exp t) ^ δ := rpow_pos_of_pos (exp_pos t) _
  have e : m / (exp t) ^ δ * (1 / T) * (g * ℓ + 2.5 / ℓ) =
      m * (g * ℓ + 2.5 / ℓ) / ((exp t) ^ δ * T) := by field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have : 37.77 * Q ≤ 6.5e-20 * (9.1e20 * Q * 0.65) := by nlinarith
  have : 9.1e20 * Q * 0.65 ≤ (exp t) ^ δ * T := mul_le_mul hden hT (by norm_num) hEpos.le
  nlinarith

lemma abr_nonneg {g T t : ℝ} (hg0 : 0 ≤ g) (hT : 0.65 ≤ T) (ht : 32.155 ≤ t) : 0 ≤ abr g T t := by
  unfold abr
  have hlt := logt_ge ht
  have hlo := log10Lx_ge ht
  have hE : 0 < (exp t) ^ δ := rpow_pos_of_pos (exp_pos t) _
  have hT0 : 0 < T := by linarith
  have h1 : 0 ≤ log t / (exp t) ^ δ := div_nonneg (by linarith) hE.le
  have h2 : 0 ≤ 1 / T := by positivity
  have h3 : 0 ≤ g * log (10 * log (exp t - 5 * t)) + 2.5 / log (10 * log (exp t - 5 * t)) :=
    add_nonneg (mul_nonneg hg0 (by linarith)) (div_nonneg (by norm_num) (by linarith))
  exact mul_nonneg (mul_nonneg h1 h2) h3

/-! ## a(X₂) itself -/

/-- (138) and (139): `a(X₂) = a₁(X₂) · max_{N ≥ X₂} [bracket]`, with
`a₁(X₂) = c2s + max_{N ≥ X₂} c₃ bracket`, where `c2s` is the first max of (139), the `c₂` term. -/
def aX2 (g T c2s : ℝ) : ℝ :=
  (c2s + sSup (c3f g '' Set.Ici 32.155)) * sSup (abr g T '' Set.Ici 32.155)

/-- **a(X₂) ≤ 10⁻¹⁸ at X₂ = exp(exp 32.155), δ = 1.5026**, given the `c₂` term of (139) at most
`10⁻²⁰`; it is about 1e-28 by numerics/aX2_U0930.out. -/
theorem aX2_le {g T c2s : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1.7812) (hT : 0.65 ≤ T)
    (hc2 : c2s ≤ 1e-20) : aX2 g T c2s ≤ 1e-18 := by
  unfold aX2
  have hne : (Set.Ici (32.155 : ℝ)).Nonempty := ⟨32.155, (Set.mem_Ici.mpr le_rfl)⟩
  have hS1 : sSup (c3f g '' Set.Ici 32.155) ≤ 2.2 := by
    apply csSup_le (hne.image _)
    rintro _ ⟨t, ht, rfl⟩; exact c3f_le hg0 hg ht
  have hS2 : sSup (abr g T '' Set.Ici 32.155) ≤ 6.5e-20 := by
    apply csSup_le (hne.image _)
    rintro _ ⟨t, ht, rfl⟩; exact abr_le hg0 hg hT ht
  have hS20 : 0 ≤ sSup (abr g T '' Set.Ici 32.155) := by
    have hb : BddAbove (abr g T '' Set.Ici 32.155) := ⟨6.5e-20, by
      rintro _ ⟨t, ht, rfl⟩; exact abr_le hg0 hg hT ht⟩
    exact le_trans (abr_nonneg hg0 hT (le_refl 32.155))
      (le_csSup hb ⟨32.155, (Set.mem_Ici.mpr le_rfl), rfl⟩)
  have : (c2s + sSup (c3f g '' Set.Ici 32.155)) * sSup (abr g T '' Set.Ici 32.155) ≤
      (1e-20 + 2.2) * sSup (abr g T '' Set.Ici 32.155) :=
    mul_le_mul_of_nonneg_right (by linarith) hS20
  have : (1e-20 + 2.2) * sSup (abr g T '' Set.Ici 32.155) ≤ (1e-20 + 2.2) * 6.5e-20 :=
    mul_le_mul_of_nonneg_left hS2 (by norm_num)
  have : ((1e-20 : ℝ) + 2.2) * 6.5e-20 ≤ 1e-18 := by norm_num
  linarith

lemma c3f_nonneg {g t : ℝ} (hg0 : 0 ≤ g) (ht : 32.155 ≤ t) : 0 ≤ c3f g t := by
  unfold c3f
  have hP0 := pow_nonneg' ht
  have hI0 := inner_nonneg hg0 ht
  have hT0 := tail_nonneg ht
  have hr0 : 0 ≤ (exp t + 10 * log (exp t - 5 * t)) / (exp t - 10 * log (exp t - 5 * t)) := by
    have hl := logLx_le ht
    have hl0 : 0 < log (exp t - 5 * t) := by have := logLx_ge ht; linarith
    have h1 := t_le ht
    have hL := L_ge ht
    apply div_nonneg (by linarith) (by nlinarith)
  have h30 : 0 ≤ 3 / (2 * exp t) := by positivity
  set A := 3 / (2 * exp t) + (exp t + 10 * log (exp t - 5 * t)) / (exp t - 10 * log (exp t - 5 * t))
  set B := (exp t / (exp t - 5 * t)) ^ δ
  set I := (1 / log t) * (g * log (δ * log (exp t - 5 * t)) +
      5 / (2 * log (δ * log (exp t - 5 * t))))
  have e : (1 / log t) * A * B * (g * log (δ * log (exp t - 5 * t)) +
      5 / (2 * log (δ * log (exp t - 5 * t)))) = A * B * I := by ring
  rw [e]
  have : 0 ≤ A * B * I := mul_nonneg (mul_nonneg (by linarith) hP0) hI0
  linarith

theorem aX2_nonneg {g T c2s : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1.7812) (hT : 0.65 ≤ T)
    (hc2 : 0 ≤ c2s) : 0 ≤ aX2 g T c2s := by
  unfold aX2
  have hb1 : BddAbove (c3f g '' Set.Ici 32.155) := ⟨2.2, by
    rintro _ ⟨t, ht, rfl⟩; exact c3f_le hg0 hg ht⟩
  have hb2 : BddAbove (abr g T '' Set.Ici 32.155) := ⟨6.5e-20, by
    rintro _ ⟨t, ht, rfl⟩; exact abr_le hg0 hg hT ht⟩
  have h1 : 0 ≤ sSup (c3f g '' Set.Ici 32.155) :=
    le_trans (c3f_nonneg hg0 (le_refl 32.155)) (le_csSup hb1 ⟨32.155, (Set.mem_Ici.mpr le_rfl), rfl⟩)
  have h2 : 0 ≤ sSup (abr g T '' Set.Ici 32.155) :=
    le_trans (abr_nonneg hg0 hT (le_refl 32.155)) (le_csSup hb2 ⟨32.155, (Set.mem_Ici.mpr le_rfl), rfl⟩)
  exact mul_nonneg (by linarith) h2


end LeanLab.ChenExplicit.BJSaX2At32155
