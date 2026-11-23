module

public import LeanLab.ChenExplicit.BJSpX2
public import LeanLab.ChenExplicit.Section9

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0903Z-17311, unit U-0931.
P0009 BJS 2022, arXiv 2207.09452 v6, read in Claude in Chrome: (158) l₁(X₂) and (159) l₁*(X₂)
at X₂ = exp(exp 32.8), with α₂ = 10⁻⁵, k_{α₂} = 8(1/6 - α₂) by (155), ε = 1.452·10⁻⁷ and h of (7)
as in Section9.lean. C₁(ε) of Table 1 is a parameter here: the bound holds for every
0 ≤ C₁ ≤ 10⁶; Section9.lean's `l2` uses C₁(ε) = 106. X₂^{1/8} is written exp(LX/8).

PROVED: l₁(X₂), l₁*(X₂) ≤ 10⁻²⁰, so every X₂-only constant of Section 9 is now PROVED small.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.BJSl

open BJSp

/-- (158) l₁(X₂) with ν = ν(x₁), and (159) l₁*(X₂) with ν = ν*, `g = e^γ`. -/
def l1 (g C1 ν : ℝ) : ℝ :=
  LX ^ 2 / exp LX * (2 * g / Section9.kα + Section9.ε * C1 * exp 2 * Section9.h Section9.kα) *
    (exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 32.8) +
      p ν * exp LX / LX ^ 4)

lemma h_kα : Section9.h Section9.kα = exp (-2) := by
  unfold Section9.h; rw [ite_eq_left_iff.mpr (fun h => absurd (by norm_num) h)]

lemma A_le {g C1 : ℝ} (_hg0 : 0 ≤ g) (hg : g ≤ 1.7812) (_hC0 : 0 ≤ C1) (hC : C1 ≤ 1e6) :
    2 * g / Section9.kα + Section9.ε * C1 * exp 2 * Section9.h Section9.kα ≤ 3 := by
  rw [h_kα]
  have e : Section9.ε * C1 * exp 2 * exp (-2) = Section9.ε * C1 := by
    rw [mul_assoc, ← exp_add]; norm_num
  rw [e]
  have h1 : 2 * g / Section9.kα ≤ 2.7 := by
    rw [div_le_iff₀ (by norm_num)]; norm_num; linarith
  have h2 : Section9.ε * C1 ≤ 0.2 := by norm_num; nlinarith
  linarith

lemma A_nonneg {g C1 : ℝ} (hg0 : 0 ≤ g) (hC0 : 0 ≤ C1) :
    0 ≤ 2 * g / Section9.kα + Section9.ε * C1 * exp 2 * Section9.h Section9.kα := by
  rw [h_kα]; positivity

lemma B1_le : exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 32.8) ≤ 1 := by
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
  calc exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 32.8)
      ≤ 2 * 2 * (1.3841 / 32.8) := by gcongr; linarith
    _ ≤ 1 := by norm_num

lemma B1_nonneg : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 32.8) := by
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
  have h2 : (1.4e14 : ℝ) ^ 4 ≤ LX ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
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
      (2 * g / Section9.kα + Section9.ε * C1 * exp 2 * Section9.h Section9.kα) *
        (LX ^ 2 / exp LX * (exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) *
          (1.3841 / 32.8))) +
      (2 * g / Section9.kα + Section9.ε * C1 * exp 2 * Section9.h Section9.kα) *
        (p ν / LX ^ 2) := by
    unfold l1
    linear_combination (2 * g / Section9.kα + Section9.ε * C1 * exp 2 * Section9.h Section9.kα) * k
  set A := 2 * g / Section9.kα + Section9.ε * C1 * exp 2 * Section9.h Section9.kα
  set B1 := exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 32.8)
  have hq : p ν / LX ^ 2 ≤ 1e-24 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ LX ^ 2 := by nlinarith
    nlinarith
  have hq0 : 0 ≤ p ν / LX ^ 2 := by positivity
  have t1 : LX ^ 2 / exp LX * B1 ≤ 1e-30 := by nlinarith
  rw [e]
  constructor
  · positivity
  · have := mul_le_mul hA t1 (by positivity) (by norm_num : (0:ℝ) ≤ 3)
    have := mul_le_mul hA hq hq0 (by norm_num : (0:ℝ) ≤ 3)
    linarith


end LeanLab.ChenExplicit.BJSl
