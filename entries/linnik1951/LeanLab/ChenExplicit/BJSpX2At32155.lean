module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: stage 3 of gen/port3220_U6718.py, the 3216 file below ported to log log X₂ = 32.155, δ₁ = 1.5026, δ₂ = 1.47088, ε₁ = 1/57, ε₂ = 1/51, ν(x₁) log x₁ ≥ 125, ν ℓ ≥ 145.7 so m(X₃) ≤ 3.81·10⁻¹⁰, ε₀ = 1.45·10⁻⁴, floor 9·10¹³ via Section9F9. The header below is the 3216 one, itself a port; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: stage 2 of gen/port3220_U6718.py, the 3220 file below ported to log log X₂ = 32.16, δ₁ = 1.5024, δ₂ = 1.4707, ε₁ = 1/57, ε₂ = 1/51, ν(x₁) log x₁ ≥ 125, the Siegel term of (87) ≤ 10⁻²³ and p(X₂) ≤ 10⁻²², ν ℓ ≥ 146.3 so m(X₃) ≤ 2.17·10⁻¹⁰, ε₀ = 1.1·10⁻⁴, floor 9·10¹³ via Section9F9. The header below is the 3220 one; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: a scripted port by gen/port3220_U6718.py of the 3225 file of U-6713 to log log X₂ = 32.2, α = 10⁻⁵, Lemma 18 at u₀ = 10⁸ with ε = 1.91·10⁻⁷, δ₁ = 1.5005 for Theorems 44 and 50 and δ₂ = 1.4688 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 1.1·10⁻¹¹ with ν ℓ ≥ 152, ν(x₁) log x₁ ≥ 130, the Siegel term of (87) ≤ 3·10⁻²⁵, p(X₂) ≤ 10⁻²⁴ unchanged, and the floor log X₂ ≥ 10¹⁴ lowered to 9·10¹³ through Section9F9.lean. The 3225 header follows unchanged; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6713, track T2: a scripted port by gen/port3225_U6713.py of the 3230 file of cloud46 U-6602 to log log X₂ = 32.25, α = 10⁻⁵, Lemma 18 at u₀ = 10⁸ with ε = 1.91·10⁻⁷ through Section9U8.lean, δ₁ = 1.4985 for Theorems 44 and 50 and δ₂ = 1.4665 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 10⁻¹¹ with ν ℓ ≥ 158; ν(x₁) log x₁ ≥ 135 in place of 145, so the Siegel term of (87) is bounded by 10⁻²⁶ in place of 10⁻³⁰, p(X₂) ≤ 10⁻²⁴ unchanged. Numeric lemmas retightened by the HAND table of the script. The 3230 header follows unchanged; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1618Z-cloud46, unit U-6602, track T2: a scripted port by gen/port3230_U6602.py of the 3270 file of cloud42 U-6403 to log log X₂ = 32.3, α = 10⁻⁵, with δ₁ = 1.496 for Theorems 44 and 50 and δ₂ = 1.464 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 10⁻¹¹; numeric lemmas retightened where the build required. The 3270 header follows, its numbers updated by the same script.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1217Z-cloud42, unit U-6403, track T1: a scripted port by gen/port3230_U6403.py of the 32.716 file of PC U-1045 to the printed log log X₂ = 32.3, α = 10⁻⁵, with δ₁ = 1.496 for Theorems 44 and 50 and δ₂ = 1.445 for Theorem 51, ε₀ = 2·10⁻⁵, m(X₃) ≤ 10⁻¹¹; numeric lemmas retightened where the build required. The 32.716 header follows, its numbers updated by the same script.
AI-written Lean code, Claude, 2026-10-19, CLOUD-built run 20261019T0903Z-22821 of the PC lab, unit U-1045, track T2, a scripted port of BJSpX2At3272.lean of PC run 20261019T0703Z-249, U-1041, to log log X₂ = 32.3, δ = 1.496, ε₀ = 2·10⁻⁵, m(X₃) ≤ 10⁻¹¹; numeric lemmas retightened where the build required. The ported header follows, its numbers updated by the same script.
PORT to log log X₂ = 32.3, δ = 1.496, PC run 20261019T0703Z-249, unit U-1041, a sed port of the cloud 32.33 file of U-5042, CLOUD 20261019T0114Z-cloud13, from BJSpX2.lean by
script /tmp port3230.py: every 32.8 → 32.3, 1.476 → 1.496; numeric lemmas retightened where
the build failed, listed in PROGRESS.md. Original header follows.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0903Z-17311, unit U-0931.
P0009 Bordignon-Johnston-Starichkova 2022, arXiv 2207.09452 v6, read in Claude in Chrome
from arxiv.org/html/2207.09452: Lemma 31 with (87), the constants p₁(X₂), p(X₂); (75), (76),
(80) 𝓔(y), (81) ν(x₁), β₀(x₁); Lemma 34 with (99) β₀*(x₁) for p*(X₂); (134), (135) c₄(X₂),
c₄*(X₂); (156), (157) l(X₂), l*(X₂). All at X₂ = exp(exp 32.3), δ = 1.496, R₁ = 2.0452.

What this file PROVES: p(X₂), p*(X₂) ≤ 10⁻²⁴ and c₄, c₄*, l, l* ≤ 10⁻²⁰, unconditionally,
for the formulas as printed. Reading choices, recorded in STATEMENTS.md:
* y in the max of (87) runs over the reals y ≥ x₁(X₂); we write L = log y, so y = exp L,
  y^β = exp(β L), log Q₁(y) = log(L¹⁰), log x₁(y) = L - 5 log L by (75).
* β₀(x₁) in (87) is read at x₁ = x₁(X₂), the reading the lab's Python used; see the QUESTION
  of run 20261018T0803Z-19871 in STATEMENTS.md. The bound holds for every ν in `Good`, which
  covers both ν(x₁(X₂)) of (81) and ν* of (99).
* Half-integer powers are written with √: log^{9/2} y = L⁴√L, log^{5.5} y = L⁵√L,
  log^{1/2} y = √L, log^{11/2} y = L⁵√L, √x₁ = √(exp log x₁).
* (87) is a max over an unbounded set; it is taken here as the supremum `⨆ L ≥ log x₁(X₂)`,
  which the bound shows is finite.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.BJSp32155

def δ : ℝ := 1.5026
def R1 : ℝ := 2.0452
/-- log X₂ with log log X₂ = 32.155. -/
def LX : ℝ := exp 32.155
/-- log x₁(X₂) = log X₂ - 5 log log X₂, by (75). -/
def Lx : ℝ := exp 32.155 - 5 * 32.155

/-- (80) 𝓔(y) at y = exp L. -/
def EE (L : ℝ) : ℝ :=
  4 * exp L * (L ^ 4 * √L) / (L - 5 * log L) ^ 10 + 4 * exp L / (L ^ 5 * √L) +
    18 * exp (11 / 12 * L) / √L + 5 / 2 * exp (5 / 6 * L) * (L ^ 5 * √L)

/-- (87) the bracket at y = exp L, with β₀ = 1 - ν. -/
def br (ν L : ℝ) : ℝ :=
  L ^ 2 / exp L * (1.1 * log (L ^ 10) * (3.2e-8 * exp L / L ^ 8 + exp ((1 - ν) * L) / (1 - ν))
    + 27 * EE L + √(exp L) / (2 * log 2 * L ^ 8) + 0.4 * L ^ 3)

/-- (87) p₂(X₂), the max over y ≥ x₁(X₂), as a supremum. -/
def p2 (ν : ℝ) : ℝ := ⨆ L : Set.Ici Lx, br ν L

/-- Lemma 31, p₁(X₂). -/
def p1 (ν : ℝ) : ℝ := p2 ν + 1 / Lx ^ 8 * (0.67 + 2 / exp (Lx / 6))

/-- Lemma 31, p(X₂); with ν = ν* it is p*(X₂) of Lemma 34. -/
def p (ν : ℝ) : ℝ :=
  p1 ν * (1 + 1 / (LX ^ 2 * Lx ^ 3) + 1 / ((1 - 4 / Lx) * LX)) + 2.2 / LX ^ 2

/-- (81) ν(x₁(X₂)), with K_δ(x₁) = log^δ x₁ and Q₁(x₁) = log¹⁰ x₁ by (76). -/
def nu : ℝ := min (100 / (√(Lx ^ δ) * log (Lx ^ δ) ^ 2)) (1 / (2 * R1 * log (Lx ^ 10)))

/-- (99) ν*, β₀* = 1 - ν*. -/
def nuS : ℝ := 1 / (2 * R1 * log (Lx ^ 10))

/-- (134), (135): c₄ with ν, c₄* with ν*. -/
def c4 (ν : ℝ) : ℝ := p ν + 0.9 * √(exp Lx) * LX ^ 4 / (exp LX * Lx ^ 10 * 32.155)

/-- (156), (157): l with ν, l* with ν*. -/
def l (ν : ℝ) : ℝ :=
  p ν * (1 / LX + 0.55) +
    1.3841 * (log (8 / 3) + 64 / LX ^ 2) * √(exp Lx) * LX ^ 3 / (exp LX * 32.155 * Lx ^ 10)

/-! ## Numerical facts about X₂ -/

lemma e328_ge : (9.21e13 : ℝ) ≤ exp 32.155 := by
  have e : exp (32.155 : ℝ) = exp 1 ^ 32 * exp 0.155 := by rw [exp_one_pow, ← exp_add]; norm_num
  have h1 : (2.7182818283 : ℝ) ^ 32 ≤ exp 1 ^ 32 :=
    pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 32
  have h2 : (1.167 : ℝ) ≤ exp 0.155 := by
    have := quadratic_le_exp_of_nonneg (x := (0.155 : ℝ)) (by norm_num); norm_num at this ⊢; linarith
  have h3 : (2.7182818283 : ℝ) ^ 32 * 1.167 ≤ exp 1 ^ 32 * exp 0.155 :=
    mul_le_mul h1 h2 (by norm_num) (by positivity)
  have h4 : (9.21e13 : ℝ) ≤ (2.7182818283 : ℝ) ^ 32 * 1.167 := by norm_num
  rw [e]; linarith

lemma e328_le : exp 32.155 ≤ (1.1e14 : ℝ) := by
  have e : exp (32.155 : ℝ) = exp 1 ^ 32 * exp 0.155 := by rw [exp_one_pow, ← exp_add]; norm_num
  have h1 : exp 1 ^ 32 ≤ (2.7182818286 : ℝ) ^ 32 :=
    pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 32
  have h2 : exp (0.155 : ℝ) ≤ 1.35 := by
    have h := Real.exp_bound' (x := (0.155 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have h3 : exp 1 ^ 32 * exp 0.155 ≤ (2.7182818286 : ℝ) ^ 32 * 1.35 :=
    mul_le_mul h1 h2 (exp_pos _).le (by positivity)
  have h4 : (2.7182818286 : ℝ) ^ 32 * 1.35 ≤ 1.1e14 := by norm_num
  rw [e]; linarith

lemma LX_ge : (9.21e13 : ℝ) ≤ LX := e328_ge
lemma LX_le : LX ≤ (2e14 : ℝ) := e328_le.trans (by norm_num)
lemma LX_le' : LX ≤ (1.1e14 : ℝ) := e328_le
lemma Lx_ge : (9e13 : ℝ) ≤ Lx := by unfold Lx; have := e328_ge; linarith
lemma Lx_le_LX : Lx ≤ LX := by unfold Lx LX; linarith
lemma LX_le_two_Lx : LX ≤ 2 * Lx := by unfold Lx LX; have := e328_ge; linarith
lemma Lx_pos : 0 < Lx := by have := Lx_ge; linarith

lemma logLx_le : log Lx ≤ 32.155 := by
  have := log_le_log Lx_pos Lx_le_LX; unfold LX at this; rwa [log_exp] at this

lemma logLx_ge : 32.145 ≤ log Lx := by
  rw [le_log_iff_exp_le Lx_pos]
  have e : exp (32.155 : ℝ) = exp 32.145 * exp 0.01 := by rw [← exp_add]; norm_num
  have h1 : (1.01 : ℝ) ≤ exp 0.01 := by have := add_one_le_exp (0.01 : ℝ); linarith
  have h2 : (32.145 : ℝ) ^ 4 / 24 ≤ exp 32.145 := by
    have := pow_div_factorial_le_exp (x := (32.145 : ℝ)) (by norm_num) 4
    simpa [Nat.factorial] using this
  have h3 : exp 32.145 * 1.01 ≤ exp 32.145 * exp 0.01 :=
    mul_le_mul_of_nonneg_left h1 (exp_pos _).le
  unfold Lx; norm_num at h2 ⊢; nlinarith

/-! ## Admissible ν -/

/-- The three properties of ν used below. -/
def Good (ν : ℝ) : Prop := 1e-12 ≤ ν ∧ ν ≤ 1 / 2 ∧ 125 / Lx ≤ ν

lemma log_Lx10 : log (Lx ^ 10) = 10 * log Lx := by rw [log_pow]; norm_num

lemma nuS_good : Good nuS := by
  have h1 := logLx_le; have h2 := logLx_ge; have h3 := Lx_ge
  have hd : nuS = 1 / (40.904 * log Lx) := by unfold nuS R1; rw [log_Lx10]; ring
  have hp : 0 < 40.904 * log Lx := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hd, le_div_iff₀ hp]; nlinarith
  · rw [hd, div_le_div_iff₀ hp (by norm_num)]; nlinarith
  · rw [hd, div_le_div_iff₀ Lx_pos hp]; nlinarith

lemma sqrt_rpow : √(Lx ^ δ) = exp (δ * log Lx / 2) := by
  rw [rpow_def_of_pos Lx_pos, ← exp_half]; ring_nf

lemma b1_ge : 125 / Lx ≤ 100 / (√(Lx ^ δ) * log (Lx ^ δ) ^ 2) := by
  have h1 := logLx_le; have h2 := logLx_ge
  rw [sqrt_rpow, log_rpow Lx_pos]
  have hE : Lx = exp (δ * log Lx / 2) * exp ((1 - δ / 2) * log Lx) := by
    rw [← exp_add, ← exp_log Lx_pos]; congr 1; rw [log_exp]; ring
  have hk : (7.99 : ℝ) ≤ (1 - δ / 2) * log Lx := by unfold δ; nlinarith
  have hs : (2950 : ℝ) ≤ exp 7.99 := by
    have h := sum_le_exp_of_nonneg (x := (7.99 : ℝ)) (by norm_num) 24
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have hx : (2950 : ℝ) ≤ exp ((1 - δ / 2) * log Lx) := hs.trans (exp_le_exp.mpr hk)
  have hq : (δ * log Lx) ^ 2 ≤ 2334.5 := by
    have : δ * log Lx ≤ 48.3162 := by unfold δ; nlinarith
    have : 0 ≤ δ * log Lx := by unfold δ; nlinarith
    nlinarith
  have hq0 : 0 < (δ * log Lx) ^ 2 := by
    have : 0 < δ * log Lx := by unfold δ; nlinarith
    positivity
  have ha := exp_pos (δ * log Lx / 2)
  rw [div_le_div_iff₀ Lx_pos (by positivity)]
  have hAB0 : exp (δ * log Lx / 2) * 2950 ≤ Lx :=
    calc exp (δ * log Lx / 2) * 2950 ≤ exp (δ * log Lx / 2) * exp ((1 - δ / 2) * log Lx) :=
          mul_le_mul_of_nonneg_left hx ha.le
      _ = Lx := hE.symm
  have hAB : 100 * (exp (δ * log Lx / 2) * 2950) ≤ 100 * Lx := by linarith
  have : 125 * (exp (δ * log Lx / 2) * (δ * log Lx) ^ 2) ≤
      125 * (exp (δ * log Lx / 2) * 2334.5) := by gcongr
  nlinarith

lemma nu_good : Good nu := by
  obtain ⟨s1, s2, s3⟩ := nuS_good
  have hb := b1_ge
  have h200 : (1e-12 : ℝ) ≤ 125 / Lx := by
    rw [le_div_iff₀ Lx_pos]; have := Lx_le_LX; have := LX_le'; nlinarith
  refine ⟨le_min (h200.trans hb) s1, (min_le_right _ _).trans s2, le_min hb s3⟩

/-! ## Bounds for L ≥ 10¹⁴ -/

section Bounds
variable {L : ℝ} (hL : 9e13 ≤ L)
include hL

lemma L_pos : 0 < L := by linarith

lemma sqrtL_ge : (9e6 : ℝ) ≤ √L := by
  rw [show (9e6 : ℝ) = √((9e6 : ℝ) ^ 2) by rw [sqrt_sq (by norm_num)]]
  exact sqrt_le_sqrt (by norm_num; linarith)

lemma sqrtL_le : √L ≤ L := by
  have h := sqrtL_ge hL
  have e : √L * √L = L := mul_self_sqrt (L_pos hL).le
  nlinarith

lemma logL_le : log L ≤ 2 * √L := by
  have h := log_sqrt (L_pos hL).le
  have h2 := log_le_sub_one_of_pos (show 0 < √L by have := sqrtL_ge hL; linarith)
  linarith

lemma logL_nonneg : 0 ≤ log L := log_nonneg (by linarith)

lemma Lpow_ge (k : ℕ) : (9e13 : ℝ) ^ k * L ≤ L ^ (k + 1) := by
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hL k) (L_pos hL).le

/-- `L - 5 log L ≥ L / 2`. -/
lemma Lsub_ge : L / 2 ≤ L - 5 * log L := by
  have h1 := logL_le hL; have h2 := sqrtL_ge hL
  have e : √L * √L = L := mul_self_sqrt (L_pos hL).le
  nlinarith

/-- `1/L^k`-type bound: `c ≤ ε L^{k+1}` from `c ≤ ε 10^{14k} L`. -/
lemma small_of (c ε : ℝ) (k : ℕ) (hε : 0 ≤ ε) (h : c ≤ ε * ((9e13 : ℝ) ^ k * L)) :
    c ≤ ε * L ^ (k + 1) :=
  h.trans (mul_le_mul_of_nonneg_left (Lpow_ge hL k) hε)

end Bounds

/-! ## The five terms of (87) -/

section Terms
variable {ν L : ℝ} (hL : Lx ≤ L)
include hL

lemma hL14 : (9e13 : ℝ) ≤ L := Lx_ge.trans hL

omit hL in
lemma br_split : br ν L =
    L ^ 2 / exp L * (1.1 * log (L ^ 10) * (3.2e-8 * exp L / L ^ 8)) +
    L ^ 2 / exp L * (1.1 * log (L ^ 10) * (exp ((1 - ν) * L) / (1 - ν))) +
    L ^ 2 / exp L * (27 * EE L) +
    L ^ 2 / exp L * (√(exp L) / (2 * log 2 * L ^ 8)) +
    L ^ 2 / exp L * (0.4 * L ^ 3) := by
  unfold br; ring

lemma X1_le : L ^ 2 / exp L * (1.1 * log (L ^ 10) * (3.2e-8 * exp L / L ^ 8)) ≤ 1e-30 := by
  have h14 := hL14 hL
  have hp := L_pos h14
  have e : L ^ 2 / exp L * (1.1 * log (L ^ 10) * (3.2e-8 * exp L / L ^ 8)) =
      3.52e-7 * log L / L ^ 6 := by
    rw [log_pow]; field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  have h1 := logL_le h14; have h2 := sqrtL_le h14
  have := small_of h14 (3.52e-7 * log L) 1e-30 5 (by norm_num) (by nlinarith)
  simpa using this

lemma X2_le (hν : Good ν) : L ^ 2 / exp L * (1.1 * log (L ^ 10) * (exp ((1 - ν) * L) / (1 - ν))) ≤ 1e-23 := by
  obtain ⟨g1, g2, g3⟩ := hν
  have h14 := hL14 hL
  have hp := L_pos h14
  have hxp := Lx_pos
  have hν0 : 0 < ν := by linarith
  have hb : 0 < 1 - ν := by linarith
  have eL : exp L = exp ((1 - ν) * L) * exp (ν * L) := by rw [← exp_add]; ring_nf
  have e : L ^ 2 / exp L * (1.1 * log (L ^ 10) * (exp ((1 - ν) * L) / (1 - ν))) =
      11 * log L * L ^ 2 / ((1 - ν) * exp (ν * L)) := by
    rw [log_pow, eL]; field_simp; ring
  rw [e]
  -- ν Lx ≥ 125
  have hu : 125 ≤ ν * Lx := by
    have := mul_le_mul_of_nonneg_right g3 hxp.le
    rwa [div_mul_cancel₀ _ Lx_pos.ne'] at this
  have hlx := logLx_le; have hlx2 := logLx_ge
  -- log L ≤ (L / Lx) log Lx
  set t := L / Lx with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hxp]; linarith
  have hLt : L = Lx * t := by rw [ht]; field_simp
  have hlog : log L ≤ t * log Lx := by
    have h1 : log L = log Lx + log t := by rw [hLt, log_mul hxp.ne' (by linarith)]
    have h2 := log_le_sub_one_of_pos (show 0 < t by linarith)
    have : (t - 1) * 1 ≤ (t - 1) * log Lx := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  -- t³ ≤ exp(3(t - 1)) ≤ exp(ν(L - Lx))
  have ht3 : t ^ 3 ≤ exp (ν * (L - Lx)) := by
    have h1 : t ≤ exp (t - 1) := by have := add_one_le_exp (t - 1); linarith
    have h2 : t ^ 3 ≤ exp (t - 1) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
    rw [← exp_nat_mul] at h2
    refine h2.trans (exp_le_exp.mpr ?_)
    have : ν * (L - Lx) = ν * Lx * (t - 1) := by rw [hLt]; ring
    rw [this]; push_cast; nlinarith
  have hnum : 11 * log L * L ^ 2 ≤ 11 * log Lx * Lx ^ 2 * exp (ν * (L - Lx)) := by
    have hl0 : 0 ≤ log L := logL_nonneg h14
    have hm : log L * L ^ 2 ≤ (t * log Lx) * L ^ 2 := mul_le_mul_of_nonneg_right hlog (by positivity)
    have e2 : (t * log Lx) * L ^ 2 = log Lx * Lx ^ 2 * t ^ 3 := by rw [hLt]; ring
    have hlx0 : 0 ≤ log Lx * Lx ^ 2 := by have : 0 ≤ log Lx := by linarith
                                          positivity
    have := mul_le_mul_of_nonneg_left ht3 hlx0
    nlinarith
  have eE : exp (ν * L) = exp (ν * (L - Lx)) * exp (ν * Lx) := by rw [← exp_add]; ring_nf
  have hE145 : (1e54 : ℝ) ≤ exp (ν * Lx) := by
    have e : exp (125 : ℝ) = exp 1 ^ 125 := by rw [exp_one_pow]; norm_num
    have h1 : (2.718 : ℝ) ^ 125 ≤ exp 1 ^ 125 :=
      pow_le_pow_left₀ (by norm_num) (by have := exp_one_gt_d9; linarith) 125
    have h2 : (1e54 : ℝ) ≤ (2.718 : ℝ) ^ 125 := by norm_num
    have h3 : exp (125 : ℝ) ≤ exp (ν * Lx) := exp_le_exp.mpr hu
    rw [e] at h3; linarith
  have hLx2 : Lx ^ 2 ≤ (1.1e14 : ℝ) ^ 2 := pow_le_pow_left₀ hxp.le (Lx_le_LX.trans LX_le') 2
  have hD0 : 0 < exp (ν * (L - Lx)) := exp_pos _
  rw [div_le_iff₀ (by positivity), eE]
  have hb2 : (1 / 2 : ℝ) ≤ 1 - ν := by linarith
  have hk : 11 * log Lx * Lx ^ 2 ≤ 1e-23 * ((1 / 2) * 1e54) := by
    have : 11 * log Lx * Lx ^ 2 ≤ 11 * 32.155 * (1.1e14 : ℝ) ^ 2 := by
      have : 0 ≤ Lx ^ 2 := by positivity
      nlinarith
    norm_num at this ⊢; linarith
  have hprod : (1 / 2) * 1e54 ≤ (1 - ν) * exp (ν * Lx) :=
    mul_le_mul hb2 hE145 (by norm_num) (by linarith)
  have : 11 * log Lx * Lx ^ 2 * exp (ν * (L - Lx)) ≤
      1e-23 * ((1 - ν) * exp (ν * Lx)) * exp (ν * (L - Lx)) := by
    apply mul_le_mul_of_nonneg_right _ hD0.le
    nlinarith
  nlinarith

lemma EE_term_le : L ^ 2 / exp L * (27 * EE L) ≤ 1e-30 := by
  have h14 := hL14 hL
  have hp := L_pos h14
  have hs1 := sqrtL_ge h14; have hs2 := sqrtL_le h14
  have hsub := Lsub_ge h14
  have hs0 : 0 < √L := by linarith
  have eA : exp L = exp (11 / 12 * L) * exp (L / 12) := by rw [← exp_add]; ring_nf
  have eB : exp L = exp (5 / 6 * L) * exp (L / 6) := by rw [← exp_add]; ring_nf
  have hsplit : L ^ 2 / exp L * (27 * EE L) =
      108 * (L ^ 6 * √L) / (L - 5 * log L) ^ 10 + 108 / (L ^ 3 * √L) +
      486 * L ^ 2 / (exp (L / 12) * √L) + 67.5 * (L ^ 7 * √L) / exp (L / 6) := by
    unfold EE
    have e3 : 18 * exp (11 / 12 * L) / √L = 18 * exp L / (exp (L / 12) * √L) := by
      rw [eA]; field_simp
    have e4 : 5 / 2 * exp (5 / 6 * L) * (L ^ 5 * √L) = 5 / 2 * exp L / exp (L / 6) * (L ^ 5 * √L) := by
      rw [eB]; field_simp
    rw [e3, e4]
    have hsub0 : 0 < L - 5 * log L := by linarith
    field_simp
    ring
  rw [hsplit]
  -- term a
  have ta : 108 * (L ^ 6 * √L) / (L - 5 * log L) ^ 10 ≤ 1e-31 := by
    have hpow : (L / 2) ^ 10 ≤ (L - 5 * log L) ^ 10 := pow_le_pow_left₀ (by positivity) hsub 10
    have hd : 0 < (L / 2) ^ 10 := by positivity
    rw [div_le_iff₀ (hd.trans_le hpow)]
    have : 108 * (L ^ 6 * √L) ≤ 1e-31 * (L / 2) ^ 10 := by
      have h1 : 108 * (L ^ 6 * √L) ≤ 108 * L ^ 7 := by
        have : L ^ 6 * √L ≤ L ^ 6 * L := mul_le_mul_of_nonneg_left hs2 (by positivity)
        nlinarith
      have h2 : (9e13 : ℝ) ^ 3 * L ^ 7 ≤ L ^ 10 := by
        have := pow_le_pow_left₀ (by norm_num) h14 3
        calc (9e13 : ℝ) ^ 3 * L ^ 7 ≤ L ^ 3 * L ^ 7 := by gcongr
          _ = L ^ 10 := by ring
      have e : (L / 2) ^ 10 = L ^ 10 / 1024 := by ring
      rw [e]; nlinarith [pow_pos hp 7]
    nlinarith [pow_le_pow_left₀ (by positivity) hsub 10]
  have tb : 108 / (L ^ 3 * √L) ≤ 1e-31 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (9e13 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) h14 3
    have : (9e13 : ℝ) ^ 3 * 9e6 ≤ L ^ 3 * √L := mul_le_mul h2 hs1 (by norm_num) (by positivity)
    nlinarith
  have tc : 486 * L ^ 2 / (exp (L / 12) * √L) ≤ 1e-31 := by
    have hE : (L / 12) ^ 6 / 720 ≤ exp (L / 12) := by
      have := pow_div_factorial_le_exp (x := L / 12) (by positivity) 6
      simpa [Nat.factorial] using this
    rw [div_le_iff₀ (by positivity)]
    have h1 : (L / 12) ^ 6 / 720 * 1 ≤ exp (L / 12) * √L :=
      mul_le_mul hE (by linarith) (by norm_num) (exp_pos _).le
    have h2 : (9e13 : ℝ) ^ 4 * L ^ 2 ≤ L ^ 6 := by
      have := pow_le_pow_left₀ (by norm_num) h14 4
      calc (9e13 : ℝ) ^ 4 * L ^ 2 ≤ L ^ 4 * L ^ 2 := by gcongr
        _ = L ^ 6 := by ring
    have e : (L / 12) ^ 6 / 720 = L ^ 6 / (12 ^ 6 * 720) := by ring
    rw [e] at h1
    nlinarith [pow_pos hp 2]
  have td : 67.5 * (L ^ 7 * √L) / exp (L / 6) ≤ 1e-31 := by
    have hE : (L / 6) ^ 12 / 479001600 ≤ exp (L / 6) := by
      have := pow_div_factorial_le_exp (x := L / 6) (by positivity) 12
      simpa [Nat.factorial] using this
    rw [div_le_iff₀ (exp_pos _)]
    have h1 : 67.5 * (L ^ 7 * √L) ≤ 67.5 * L ^ 8 := by
      have : L ^ 7 * √L ≤ L ^ 7 * L := mul_le_mul_of_nonneg_left hs2 (by positivity)
      nlinarith
    have h2 : (9e13 : ℝ) ^ 4 * L ^ 8 ≤ L ^ 12 := by
      have := pow_le_pow_left₀ (by norm_num) h14 4
      calc (9e13 : ℝ) ^ 4 * L ^ 8 ≤ L ^ 4 * L ^ 8 := by gcongr
        _ = L ^ 12 := by ring
    have e : (L / 6) ^ 12 / 479001600 = L ^ 12 / (6 ^ 12 * 479001600) := by ring
    rw [e] at hE
    nlinarith [pow_pos hp 8]
  linarith

lemma X4_le : L ^ 2 / exp L * (√(exp L) / (2 * log 2 * L ^ 8)) ≤ 1e-30 := by
  have h14 := hL14 hL
  have hp := L_pos h14
  have hs : √(exp L) ≤ exp L := by
    rw [sqrt_le_left (exp_pos L).le]
    have : 1 ≤ exp L := one_le_exp hp.le
    nlinarith
  have hl2 : (1 : ℝ) ≤ 2 * log 2 := by have := log_two_gt_d9; linarith
  have e : L ^ 2 / exp L * (√(exp L) / (2 * log 2 * L ^ 8)) =
      (√(exp L) / exp L) * (1 / (2 * log 2 * L ^ 6)) := by
    field_simp
  rw [e]
  have h1 : √(exp L) / exp L ≤ 1 := by rw [div_le_one (exp_pos L)]; exact hs
  have h2 : 1 / (2 * log 2 * L ^ 6) ≤ 1e-30 := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : (9e13 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) h14 6
    have : L ^ 6 ≤ 2 * log 2 * L ^ 6 := by nlinarith [pow_pos hp 6]
    nlinarith
  calc (√(exp L) / exp L) * (1 / (2 * log 2 * L ^ 6)) ≤ 1 * 1e-30 :=
        mul_le_mul h1 h2 (by positivity) (by norm_num)
    _ = 1e-30 := by norm_num

lemma X5_le : L ^ 2 / exp L * (0.4 * L ^ 3) ≤ 1e-30 := by
  have h14 := hL14 hL
  have hp := L_pos h14
  have hE : L ^ 8 / 40320 ≤ exp L := by
    have := pow_div_factorial_le_exp (x := L) hp.le 8
    simpa [Nat.factorial] using this
  have e : L ^ 2 / exp L * (0.4 * L ^ 3) = 0.4 * L ^ 5 / exp L := by field_simp
  rw [e, div_le_iff₀ (exp_pos L)]
  have h2 : (9e13 : ℝ) ^ 3 * L ^ 5 ≤ L ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num) h14 3
    calc (9e13 : ℝ) ^ 3 * L ^ 5 ≤ L ^ 3 * L ^ 5 := by gcongr
      _ = L ^ 8 := by ring
  nlinarith [pow_pos hp 5]

lemma br_le (hν : Good ν) : br ν L ≤ 1.1e-23 := by
  rw [br_split]
  have := X1_le hL; have := X2_le hL hν; have := EE_term_le hL
  have := X4_le hL; have := X5_le hL
  linarith

lemma br_nonneg (hν : Good ν) : 0 ≤ br ν L := by
  obtain ⟨g1, g2, g3⟩ := hν
  have h14 := hL14 hL
  have hp := L_pos h14
  have hl := logL_nonneg h14
  have hsub := Lsub_ge h14
  have hsub0 : 0 < L - 5 * log L := by linarith
  have hb : 0 < 1 - ν := by linarith
  have hl10 : 0 ≤ log (L ^ 10) := by rw [log_pow]; positivity
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  unfold br EE
  positivity

end Terms

/-! ## p, p*, c₄, c₄*, l, l* -/

lemma p2_le {ν : ℝ} (hν : Good ν) : p2 ν ≤ 1.1e-23 := by
  have : Nonempty (Set.Ici Lx) := ⟨⟨Lx, Set.mem_Ici.mpr le_rfl⟩⟩
  exact ciSup_le fun L => br_le L.2 hν

lemma p2_nonneg {ν : ℝ} (hν : Good ν) : 0 ≤ p2 ν := by
  have hb : BddAbove (Set.range fun L : Set.Ici Lx => br ν L) :=
    ⟨1.1e-23, by rintro _ ⟨L, rfl⟩; exact br_le L.2 hν⟩
  exact (br_nonneg (le_refl Lx) hν).trans (le_ciSup hb ⟨Lx, Set.mem_Ici.mpr le_rfl⟩)

lemma tail1_le : 1 / Lx ^ 8 * (0.67 + 2 / exp (Lx / 6)) ≤ 1e-30 := by
  have h := Lx_ge
  have hp := Lx_pos
  have he : 2 / exp (Lx / 6) ≤ 2 := by
    rw [div_le_iff₀ (exp_pos _)]; have := one_le_exp (show 0 ≤ Lx / 6 by positivity); linarith
  have h8 : (9e13 : ℝ) ^ 8 ≤ Lx ^ 8 := pow_le_pow_left₀ (by norm_num) h 8
  have h1 : 1 / Lx ^ 8 ≤ 1 / (9e13 : ℝ) ^ 8 := one_div_le_one_div_of_le (by positivity) h8
  calc 1 / Lx ^ 8 * (0.67 + 2 / exp (Lx / 6)) ≤ 1 / (9e13 : ℝ) ^ 8 * 2.67 :=
        mul_le_mul h1 (by linarith) (by positivity) (by positivity)
    _ ≤ 1e-30 := by norm_num

lemma tail1_nonneg : 0 ≤ 1 / Lx ^ 8 * (0.67 + 2 / exp (Lx / 6)) := by
  have := Lx_pos; positivity

lemma fac_le : 1 + 1 / (LX ^ 2 * Lx ^ 3) + 1 / ((1 - 4 / Lx) * LX) ≤ 3 := by
  have h1 := Lx_ge; have h2 := LX_ge
  have hq : 4 / Lx ≤ 1 / 2 := by rw [div_le_iff₀ Lx_pos]; linarith
  have hq0 : 0 < 4 / Lx := by have := Lx_pos; positivity
  have a1 : 1 / (LX ^ 2 * Lx ^ 3) ≤ 1 := by
    rw [div_le_one (by have := Lx_pos; positivity)]
    have : (1 : ℝ) ≤ LX ^ 2 := by nlinarith
    have : (1 : ℝ) ≤ Lx ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  have a2 : 1 / ((1 - 4 / Lx) * LX) ≤ 1 := by
    rw [div_le_one (by apply mul_pos <;> linarith)]
    nlinarith
  linarith

lemma fac_nonneg : 0 ≤ 1 + 1 / (LX ^ 2 * Lx ^ 3) + 1 / ((1 - 4 / Lx) * LX) := by
  have h1 := Lx_ge; have h2 := LX_ge
  have hq : 4 / Lx ≤ 1 / 2 := by rw [div_le_iff₀ Lx_pos]; linarith
  have : 0 < (1 - 4 / Lx) * LX := by apply mul_pos <;> linarith
  have := Lx_pos
  positivity

lemma tail2_le : 2.2 / LX ^ 2 ≤ 2.6e-28 := by
  have h := LX_ge
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- **p(X₂) ≤ 10⁻²⁴**, for every admissible ν: Lemma 31 with ν(x₁) and Lemma 34 with ν*. -/
theorem p_le {ν : ℝ} (hν : Good ν) : p ν ≤ 1e-22 := by
  unfold p p1
  have a := p2_le hν; have b := p2_nonneg hν
  have c := tail1_le; have d := tail1_nonneg
  have f := fac_le; have f0 := fac_nonneg
  have t := tail2_le
  have : (p2 ν + 1 / Lx ^ 8 * (0.67 + 2 / exp (Lx / 6))) *
      (1 + 1 / (LX ^ 2 * Lx ^ 3) + 1 / ((1 - 4 / Lx) * LX)) ≤ (1.1e-23 + 1e-30) * 3 :=
    mul_le_mul (by linarith) f f0 (by norm_num)
  linarith

theorem p_nonneg {ν : ℝ} (hν : Good ν) : 0 ≤ p ν := by
  unfold p p1
  have b := p2_nonneg hν; have d := tail1_nonneg; have f0 := fac_nonneg
  have := LX_ge
  have : 0 ≤ 2.2 / LX ^ 2 := by positivity
  have : 0 ≤ (p2 ν + 1 / Lx ^ 8 * (0.67 + 2 / exp (Lx / 6))) *
      (1 + 1 / (LX ^ 2 * Lx ^ 3) + 1 / ((1 - 4 / Lx) * LX)) := mul_nonneg (by linarith) f0
  linarith

/-- The common extra term of (134) and (135) is below 10⁻³⁰. -/
lemma c4tail_le : 0.9 * √(exp Lx) * LX ^ 4 / (exp LX * Lx ^ 10 * 32.155) ≤ 1e-30 := by
  have h1 := Lx_ge; have hp := Lx_pos; have h2 := LX_le_two_Lx; have h3 := Lx_le_LX
  have hs : √(exp Lx) ≤ exp LX := by
    rw [sqrt_le_left (exp_pos LX).le]
    have : exp Lx ≤ exp LX := exp_le_exp.mpr h3
    have : 1 ≤ exp LX := one_le_exp (by linarith)
    nlinarith
  have hLX0 : 0 ≤ LX := by linarith
  have h4 : LX ^ 4 ≤ (2 * Lx) ^ 4 := pow_le_pow_left₀ hLX0 h2 4
  rw [div_le_iff₀ (by positivity)]
  have h6 : (9e13 : ℝ) ^ 6 ≤ Lx ^ 6 := pow_le_pow_left₀ (by norm_num) h1 6
  have hA : 0.9 * √(exp Lx) * LX ^ 4 ≤ 0.9 * exp LX * (16 * Lx ^ 4) := by
    have : (2 * Lx) ^ 4 = 16 * Lx ^ 4 := by ring
    rw [← this]; gcongr
  have hB : 0.9 * exp LX * (16 * Lx ^ 4) ≤ 1e-30 * (exp LX * Lx ^ 10 * 32.155) := by
    have e : exp LX * Lx ^ 10 * 32.155 = exp LX * Lx ^ 4 * (Lx ^ 6 * 32.155) := by ring
    rw [e]
    have : 0 < exp LX * Lx ^ 4 := by positivity
    nlinarith
  linarith

lemma ltail_le : 1.3841 * (log (8 / 3) + 64 / LX ^ 2) * √(exp Lx) * LX ^ 3 /
    (exp LX * 32.155 * Lx ^ 10) ≤ 1e-30 := by
  have h1 := Lx_ge; have hp := Lx_pos; have h2 := LX_le_two_Lx; have h3 := Lx_le_LX
  have h5 := LX_ge
  have hs : √(exp Lx) ≤ exp LX := by
    rw [sqrt_le_left (exp_pos LX).le]
    have : exp Lx ≤ exp LX := exp_le_exp.mpr h3
    have : 1 ≤ exp LX := one_le_exp (by linarith)
    nlinarith
  have hl : log (8 / 3) ≤ 1 := by
    rw [log_le_iff_le_exp (by norm_num)]; have := exp_one_gt_d9; norm_num at this ⊢; linarith
  have hl0 : 0 ≤ log (8 / 3) := log_nonneg (by norm_num)
  have hq : 64 / LX ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hLX0 : 0 ≤ LX := by linarith
  have h4 : LX ^ 3 ≤ (2 * Lx) ^ 3 := pow_le_pow_left₀ hLX0 h2 3
  rw [div_le_iff₀ (by positivity)]
  have hA : 1.3841 * (log (8 / 3) + 64 / LX ^ 2) * √(exp Lx) * LX ^ 3 ≤
      1.3841 * 2 * exp LX * (8 * Lx ^ 3) := by
    have : (2 * Lx) ^ 3 = 8 * Lx ^ 3 := by ring
    rw [← this]
    have : 0 ≤ 64 / LX ^ 2 := by positivity
    gcongr; linarith
  have h7 : (9e13 : ℝ) ^ 7 ≤ Lx ^ 7 := pow_le_pow_left₀ (by norm_num) h1 7
  have hB : 1.3841 * 2 * exp LX * (8 * Lx ^ 3) ≤ 1e-30 * (exp LX * 32.155 * Lx ^ 10) := by
    have e : exp LX * 32.155 * Lx ^ 10 = exp LX * Lx ^ 3 * (Lx ^ 7 * 32.155) := by ring
    rw [e]
    have : 0 < exp LX * Lx ^ 3 := by positivity
    nlinarith
  linarith

/-- **(134), (135): c₄(X₂) and c₄*(X₂) ≤ 10⁻²⁰.** -/
theorem c4_le {ν : ℝ} (hν : Good ν) : c4 ν ≤ 1e-20 := by
  unfold c4; have := p_le hν; have := c4tail_le; linarith

theorem c4_nonneg {ν : ℝ} (hν : Good ν) : 0 ≤ c4 ν := by
  unfold c4; have := p_nonneg hν; have := Lx_pos; have := LX_ge
  have : 0 ≤ 0.9 * √(exp Lx) * LX ^ 4 / (exp LX * Lx ^ 10 * 32.155) := by positivity
  linarith

/-- **(156), (157): l(X₂) and l*(X₂) ≤ 10⁻²⁰.** -/
theorem l_le {ν : ℝ} (hν : Good ν) : l ν ≤ 1e-20 := by
  unfold l
  have hp := p_le hν; have hp0 := p_nonneg hν; have := ltail_le; have h := LX_ge
  have hLX0 : 0 < LX := by linarith
  have hf : 1 / LX + 0.55 ≤ 1 := by
    have : 1 / LX ≤ 0.45 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have : p ν * (1 / LX + 0.55) ≤ 1e-22 * 1 :=
    mul_le_mul hp hf (by positivity) (by norm_num)
  linarith

theorem l_nonneg {ν : ℝ} (hν : Good ν) : 0 ≤ l ν := by
  unfold l
  have hp0 := p_nonneg hν; have := Lx_pos; have h := LX_ge
  have hl0 : 0 ≤ log (8 / 3 : ℝ) := log_nonneg (by norm_num)
  have : 0 < LX := by linarith
  positivity

/-- The four constants the Section 9 margins take as hypotheses, all PROVED. -/
theorem X2_constants :
    p nu ≤ 1e-22 ∧ p nuS ≤ 1e-22 ∧ c4 nu ≤ 1e-20 ∧ c4 nuS ≤ 1e-20 ∧
    l nu ≤ 1e-20 ∧ l nuS ≤ 1e-20 :=
  ⟨p_le nu_good, p_le nuS_good, c4_le nu_good, c4_le nuS_good, l_le nu_good, l_le nuS_good⟩


end LeanLab.ChenExplicit.BJSp32155
