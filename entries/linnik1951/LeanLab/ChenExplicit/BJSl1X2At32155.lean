module

public import LeanLab.ChenExplicit.BJSpX2At32155
public import LeanLab.ChenExplicit.Section9U8

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: stage 3 of gen/port3220_U6718.py, the 3216 file below ported to log log X₂ = 32.155, δ₁ = 1.5026, δ₂ = 1.47088, ε₁ = 1/57, ε₂ = 1/51, ν(x₁) log x₁ ≥ 125, ν ℓ ≥ 145.7 so m(X₃) ≤ 3.81·10⁻¹⁰, ε₀ = 1.45·10⁻⁴, floor 9·10¹³ via Section9F9. The header below is the 3216 one, itself a port; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: stage 2 of gen/port3220_U6718.py, the 3220 file below ported to log log X₂ = 32.16, δ₁ = 1.5024, δ₂ = 1.4707, ε₁ = 1/57, ε₂ = 1/51, ν(x₁) log x₁ ≥ 125, the Siegel term of (87) ≤ 10⁻²³ and p(X₂) ≤ 10⁻²², ν ℓ ≥ 146.3 so m(X₃) ≤ 2.17·10⁻¹⁰, ε₀ = 1.1·10⁻⁴, floor 9·10¹³ via Section9F9. The header below is the 3220 one; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: a scripted port by gen/port3220_U6718.py of the 3225 file of U-6713 to log log X₂ = 32.2, α = 10⁻⁵, Lemma 18 at u₀ = 10⁸ with ε = 1.91·10⁻⁷, δ₁ = 1.5005 for Theorems 44 and 50 and δ₂ = 1.4688 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 1.1·10⁻¹¹ with ν ℓ ≥ 152, ν(x₁) log x₁ ≥ 130, the Siegel term of (87) ≤ 3·10⁻²⁵, p(X₂) ≤ 10⁻²⁴ unchanged, and the floor log X₂ ≥ 10¹⁴ lowered to 9·10¹³ through Section9F9.lean. The 3225 header follows unchanged; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6713, track T2: a scripted port by gen/port3225_U6713.py of the 3230 file of cloud46 U-6602 to log log X₂ = 32.25, α = 10⁻⁵, Lemma 18 at u₀ = 10⁸ with ε = 1.91·10⁻⁷ through Section9U8.lean, δ₁ = 1.4985 for Theorems 44 and 50 and δ₂ = 1.4665 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 10⁻¹¹ with ν ℓ ≥ 158; ν(x₁) log x₁ ≥ 135 in place of 145, so the Siegel term of (87) is bounded by 10⁻²⁶ in place of 10⁻³⁰, p(X₂) ≤ 10⁻²⁴ unchanged. Numeric lemmas retightened by the HAND table of the script. The 3230 header follows unchanged; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1618Z-cloud46, unit U-6602, track T2: a scripted port by gen/port3230_U6602.py of the 3270 file of cloud42 U-6403 to log log X₂ = 32.3, α = 10⁻⁵, with δ₁ = 1.496 for Theorems 44 and 50 and δ₂ = 1.464 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 10⁻¹¹; numeric lemmas retightened where the build required. The 3270 header follows, its numbers updated by the same script.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1217Z-cloud42, unit U-6403, track T1: a scripted port by gen/port3230_U6403.py of the 32.716 file of PC U-1045 to the printed log log X₂ = 32.3, α = 10⁻⁵, with δ₁ = 1.496 for Theorems 44 and 50 and δ₂ = 1.445 for Theorem 51, ε₀ = 2·10⁻⁵, m(X₃) ≤ 10⁻¹¹; numeric lemmas retightened where the build required. The 32.716 header follows, its numbers updated by the same script.
AI-written Lean code, Claude, 2026-10-19, CLOUD-built run 20261019T0903Z-22821 of the PC lab, unit U-1045, track T2, a scripted port of BJSl1X2At3272.lean of PC run 20261019T0703Z-249, U-1041, to log log X₂ = 32.3, δ = 1.496, ε₀ = 2·10⁻⁵, m(X₃) ≤ 10⁻¹¹; numeric lemmas retightened where the build required. The ported header follows, its numbers updated by the same script.
PORT to log log X₂ = 32.3, δ = 1.496, PC run 20261019T0703Z-249, unit U-1041, a sed port of the cloud 32.33 file of U-5042, CLOUD 20261019T0114Z-cloud13, from BJSl1X2.lean by
script /tmp port3230.py: every 32.8 → 32.3, 1.476 → 1.496; numeric lemmas retightened where
the build failed, listed in PROGRESS.md. Original header follows.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0903Z-17311, unit U-0931.
P0009 BJS 2022, arXiv 2207.09452 v6, read in Claude in Chrome: (158) l₁(X₂) and (159) l₁*(X₂)
at X₂ = exp(exp 32.3), with α₂ = 10⁻⁵, k_{α₂} = 8(1/6 - α₂) by (155), ε = 1.452·10⁻⁷ and h of (7)
as in Section9.lean. C₁(ε) of Table 1 is a parameter here: the bound holds for every
0 ≤ C₁ ≤ 10⁶; Section9.lean's `l2` uses C₁(ε) = 106. X₂^{1/8} is written exp(LX/8).

PROVED: l₁(X₂), l₁*(X₂) ≤ 10⁻²⁰, so every X₂-only constant of Section 9 is now PROVED small.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.BJSl32155

open BJSp32155

/-- (158) l₁(X₂) with ν = ν(x₁), and (159) l₁*(X₂) with ν = ν*, `g = e^γ`. -/
def l1 (g C1 ν : ℝ) : ℝ :=
  LX ^ 2 / exp LX * (2 * g / Section9.kα + Section9U8.εU * C1 * exp 2 * Section9.h Section9.kα) *
    (exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 32.155) +
      p ν * exp LX / LX ^ 4)

lemma h_kα : Section9.h Section9.kα = exp (-2) := by
  unfold Section9.h; rw [ite_eq_left_iff.mpr (fun h => absurd (by norm_num) h)]

lemma A_le {g C1 : ℝ} (_hg0 : 0 ≤ g) (hg : g ≤ 1.7812) (_hC0 : 0 ≤ C1) (hC : C1 ≤ 1e6) :
    2 * g / Section9.kα + Section9U8.εU * C1 * exp 2 * Section9.h Section9.kα ≤ 3 := by
  rw [h_kα]
  have e : Section9U8.εU * C1 * exp 2 * exp (-2) = Section9U8.εU * C1 := by
    rw [mul_assoc, ← exp_add]; norm_num
  rw [e]
  have h1 : 2 * g / Section9.kα ≤ 2.7 := by
    rw [div_le_iff₀ (by norm_num)]; norm_num; linarith
  have h2 : Section9U8.εU * C1 ≤ 0.2 := by norm_num; nlinarith
  linarith

lemma A_nonneg {g C1 : ℝ} (hg0 : 0 ≤ g) (hC0 : 0 ≤ C1) :
    0 ≤ 2 * g / Section9.kα + Section9U8.εU * C1 * exp 2 * Section9.h Section9.kα := by
  rw [h_kα]; positivity

lemma B1_le : exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 32.155) ≤ 1 := by
  have hX := LX_ge
  have hE : 2 ≤ exp (LX / 8) := by have := add_one_le_exp (LX / 8); linarith
  have hr : exp (LX / 8) / (exp (LX / 8) - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hl : log (8 / 3) ≤ 1 := by
    rw [log_le_iff_le_exp (by norm_num)]; have := exp_one_gt_d9; norm_num at this ⊢; linarith
  have hl0 : 0 ≤ log (8 / 3) := log_nonneg (by norm_num)
  have hq : 64 / LX ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hq0 : 0 ≤ 64 / LX ^ 2 := by positivity
  have hr0 : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) := div_nonneg (exp_pos _).le (by linarith)
  calc exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 32.155)
      ≤ 2 * 2 * (1.3841 / 32.155) := by gcongr; linarith
    _ ≤ 1 := by norm_num

lemma B1_nonneg : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 32.155) := by
  have hX := LX_ge
  have hE : 2 ≤ exp (LX / 8) := by have := add_one_le_exp (LX / 8); linarith
  have hl0 : 0 ≤ log (8 / 3) := log_nonneg (by norm_num)
  have : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) := div_nonneg (exp_pos _).le (by linarith)
  positivity

lemma LXexp_le : LX ^ 2 / exp LX ≤ 1e-30 := by
  have h := LX_ge
  have hp : 0 < LX := by linarith
  have hE : LX ^ 6 / 720 ≤ exp LX := by
    have := pow_div_factorial_le_exp (x := LX) hp.le 6
    simpa [Nat.factorial] using this
  rw [div_le_iff₀ (exp_pos _)]
  have h2 : (9.21e13 : ℝ) ^ 4 ≤ LX ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
  have : LX ^ 6 = LX ^ 2 * LX ^ 4 := by ring
  rw [this] at hE
  have := pow_pos hp 2
  nlinarith

/-- **(158), (159): l₁(X₂), l₁*(X₂) ∈ [0, 10⁻²⁰]** for 0 ≤ g ≤ 1.7812 and 0 ≤ C₁ ≤ 10⁶. -/
theorem l1_bounds {g C1 ν : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1.7812) (hC0 : 0 ≤ C1) (hC : C1 ≤ 1e6)
    (hν : Good ν) : 0 ≤ l1 g C1 ν ∧ l1 g C1 ν ≤ 1e-20 := by
  have hX := LX_ge
  have hp : 0 < LX := by linarith
  have hA := A_le hg0 hg hC0 hC; have hA0 := A_nonneg (C1 := C1) hg0 hC0
  have hB := B1_le; have hB0 := B1_nonneg
  have hP := p_le hν; have hP0 := p_nonneg hν
  have hR := LXexp_le
  have hR0 : 0 ≤ LX ^ 2 / exp LX := by positivity
  have k : LX ^ 2 / exp LX * (p ν * exp LX / LX ^ 4) = p ν / LX ^ 2 := by
    field_simp
  have e : l1 g C1 ν =
      (2 * g / Section9.kα + Section9U8.εU * C1 * exp 2 * Section9.h Section9.kα) *
        (LX ^ 2 / exp LX * (exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) *
          (1.3841 / 32.155))) +
      (2 * g / Section9.kα + Section9U8.εU * C1 * exp 2 * Section9.h Section9.kα) *
        (p ν / LX ^ 2) := by
    unfold l1
    linear_combination (2 * g / Section9.kα + Section9U8.εU * C1 * exp 2 * Section9.h Section9.kα) * k
  set A := 2 * g / Section9.kα + Section9U8.εU * C1 * exp 2 * Section9.h Section9.kα
  set B1 := exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 32.155)
  have hq : p ν / LX ^ 2 ≤ 1e-24 := by
    rw [div_le_iff₀ (by positivity)]
    have : (100 : ℝ) ≤ LX ^ 2 := by nlinarith
    nlinarith
  have hq0 : 0 ≤ p ν / LX ^ 2 := by positivity
  have t1 : LX ^ 2 / exp LX * B1 ≤ 1e-30 := by nlinarith
  rw [e]
  constructor
  · positivity
  · have := mul_le_mul hA t1 (by positivity) (by norm_num : (0:ℝ) ≤ 3)
    have := mul_le_mul hA hq hq0 (by norm_num : (0:ℝ) ≤ 3)
    linarith


end LeanLab.ChenExplicit.BJSl32155
