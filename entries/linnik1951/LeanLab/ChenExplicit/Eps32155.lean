module

public import LeanLab.ChenExplicit.F0023
public import LeanLab.ChenExplicit.BJSm32155
public import LeanLab.ChenExplicit.BJSThm51

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: stage 3 of gen/port3220_U6718.py, the 3216 file below ported to log log X₂ = 32.155, δ₁ = 1.5026, δ₂ = 1.47088, ε₁ = 1/57, ε₂ = 1/51, ν(x₁) log x₁ ≥ 125, ν ℓ ≥ 145.7 so m(X₃) ≤ 3.81·10⁻¹⁰, ε₀ = 1.45·10⁻⁴, floor 9·10¹³ via Section9F9. The header below is the 3216 one, itself a port; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: stage 2 of gen/port3220_U6718.py, the 3220 file below ported to log log X₂ = 32.16, δ₁ = 1.5024, δ₂ = 1.4707, ε₁ = 1/57, ε₂ = 1/51, ν(x₁) log x₁ ≥ 125, the Siegel term of (87) ≤ 10⁻²³ and p(X₂) ≤ 10⁻²², ν ℓ ≥ 146.3 so m(X₃) ≤ 2.17·10⁻¹⁰, ε₀ = 1.1·10⁻⁴, floor 9·10¹³ via Section9F9. The header below is the 3220 one; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6718, track T2: a scripted port by gen/port3220_U6718.py of the 3225 file of U-6713 to log log X₂ = 32.2, α = 10⁻⁵, Lemma 18 at u₀ = 10⁸ with ε = 1.91·10⁻⁷, δ₁ = 1.5005 for Theorems 44 and 50 and δ₂ = 1.4688 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 1.1·10⁻¹¹ with ν ℓ ≥ 152, ν(x₁) log x₁ ≥ 130, the Siegel term of (87) ≤ 3·10⁻²⁵, p(X₂) ≤ 10⁻²⁴ unchanged, and the floor log X₂ ≥ 10¹⁴ lowered to 9·10¹³ through Section9F9.lean. The 3225 header follows unchanged; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6713, track T2: a scripted port by gen/port3225_U6713.py of the 3230 file of cloud46 U-6602 to log log X₂ = 32.25, α = 10⁻⁵, Lemma 18 at u₀ = 10⁸ with ε = 1.91·10⁻⁷ through Section9U8.lean, δ₁ = 1.4985 for Theorems 44 and 50 and δ₂ = 1.4665 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 10⁻¹¹ with ν ℓ ≥ 158; ν(x₁) log x₁ ≥ 135 in place of 145, so the Siegel term of (87) is bounded by 10⁻²⁶ in place of 10⁻³⁰, p(X₂) ≤ 10⁻²⁴ unchanged. Numeric lemmas retightened by the HAND table of the script. The 3230 header follows unchanged; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1618Z-cloud46, unit U-6602, track T2.
P0009 BJS 2022, (121) at log log X₂ = 32.3 with the two δ of the U-6404 model, written from
Eps3270.lean and F0023.pbar1_printed of cloud42:
* `eps1_3230`: `ε₁ = 1/57` at δ₁ = 1.496, since `3·5·…·59 ≤ (log x₁(X₂))^{1.496} < 3·5·…·61`,
  `log x₁(X₂) = e^{32.3} - 5 · 32.3`; the lower side is `1.496 · (32.3 - 10⁻⁴) ≥ 48.3206` against
  `log(3·5·…·59) = 48.3149`, the boundary is `δ₁ = 1.49582`;
* `eps2_3230`: `ε₂ = 1/51` at δ₂ = 1.464 for Theorem 51, since `3·5·…·53 ≤ (log x₂(X₃))^{1.464} <
  3·5·…·59`; the lower side is `1.464 · log x₂(X₃) ≥ 44.2428` against `log(3·5·…·53) = 44.2374`,
  the boundary is `δ₂ = 1.46382`. Theorem 51 states its own "Let 0 < δ < 2", papers/P0009.txt
  line 3327, so δ₂ need not be δ₁.
Chen's theorem is not in doubt; Goldbach is open.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.Eps32155

open LeanLab.ChenExplicit LeanLab.ChenExplicit.BJS LeanLab.ChenExplicit.BJS51

/-- log log X₂ = 32.155. -/
abbrev ll : ℝ := 32155 / 1000

/-- `log^{δ₁} x₁(X₂)`, δ₁ = 1.5026. -/
def B1 : ℝ := (exp ll - 5 * ll) ^ (1.5026 : ℝ)

/-- `log^{δ₂} x₂(X₃)`, δ₂ = 1.47088. -/
def B2 : ℝ := F0023.ℓP ll ^ (1.47088 : ℝ)

theorem ℓ_eq : BJSm32155.ℓ = F0023.ℓP ll := rfl

theorem pbar1_32155 : BJSEm.pbar B1 = 59 := by
  have hE := BJSm32155.exp32155_ge
  have hpos : 0 < exp ll - 5 * ll := by norm_num at hE ⊢; linarith
  have hlo : exp ll * (9999 / 10000) ≤ exp ll - 5 * ll := by norm_num at hE ⊢; nlinarith
  have l2 : ll + log (9999 / 10000) ≤ log (exp ll - 5 * ll) := by
    rw [← log_exp ll, ← log_mul (exp_pos _).ne' (by norm_num), log_exp]
    exact log_le_log (by positivity) hlo
  have l3 : -(1 / 9999 : ℝ) ≤ log (9999 / 10000) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (9999 / 10000 : ℝ)) (by norm_num)
    norm_num at this ⊢; linarith
  have hl : log (exp ll - 5 * ll) ≤ ll := by
    have := log_le_log hpos (show exp ll - 5 * ll ≤ exp ll by norm_num)
    rwa [log_exp] at this
  apply BJSEm.pbar_eq B1 59 61 (by norm_num)
  · unfold B1
    rw [rpow_def_of_pos hpos, BJS51.oddPrimorial_59]
    have hm : log (exp ll - 5 * ll) * 1.5026 = 48 + (1.5026 * log (exp ll - 5 * ll) - 48) := by ring
    rw [hm, exp_add]
    have a1 := BJS51.exp_nat_ge 48
    push_cast at a1
    have b : 0.3159 ≤ 1.5026 * log (exp ll - 5 * ll) - 48 := by norm_num at l2 l3 ⊢; nlinarith
    have b2 := sum_le_exp_of_nonneg (x := 1.5026 * log (exp ll - 5 * ll) - 48) (by linarith) 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at b2
    have q2 := pow_le_pow_left₀ (by norm_num) b 2
    have q3 := pow_le_pow_left₀ (by norm_num) b 3
    have b3 : (1.3705 : ℝ) ≤ exp (1.5026 * log (exp ll - 5 * ll) - 48) := by
      norm_num at b2 q2 q3 ⊢; linarith
    have c : (961380175077106319535 : ℝ) ≤ 2.7182818283 ^ 48 * 1.3705 := by norm_num
    have := mul_le_mul a1 b3 (by norm_num) (exp_pos _).le
    push_cast; linarith
  · unfold B1
    rw [rpow_def_of_pos hpos, BJSEm.oddPrimorial_61]
    have h1 : exp (log (exp ll - 5 * ll) * 1.5026) ≤ exp 49 :=
      exp_le_exp.mpr (by norm_num at hl ⊢; nlinarith)
    have h2 : exp (49 : ℝ) = exp 1 ^ 49 := by rw [exp_one_pow]; norm_num
    have h3 : exp 1 ^ 49 ≤ (2.7182818286 : ℝ) ^ 49 :=
      pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 49
    have h4 : (2.7182818286 : ℝ) ^ 49 < 58644190679703485491635 := by norm_num
    push_cast; linarith
  · intro p h1 h2
    interval_cases p; norm_num

theorem eps1_32155 : BJSEm.eps B1 = 1 / 57 := by unfold BJSEm.eps; rw [pbar1_32155]; norm_num

theorem eps2_32155 : BJSEm.eps B2 = 1 / 51 := by
  obtain ⟨u1, u2⟩ := BJSm32155.logℓ_bounds
  have hℓ := BJSm32155.ℓ_pos
  rw [ℓ_eq] at u1 u2 hℓ
  have hb : (oddPrimorial 53 : ℝ) ≤ B2 ∧ B2 < (oddPrimorial 59 : ℝ) := by
    unfold B2
    rw [rpow_def_of_pos hℓ, oddPrimorial_53, oddPrimorial_59]
    set u := log (F0023.ℓP ll)
    have hm : u * 1.47088 = 44 + (1.47088 * u - 44) := by ring
    rw [hm, exp_add]
    have a1 : (2.7182818283 : ℝ) ^ 44 ≤ exp 44 := by
      rw [show (44 : ℝ) = ((44 : ℕ) : ℝ) by norm_num, ← exp_one_pow]
      exact pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 44
    have a2 : exp 44 ≤ (2.7182818286 : ℝ) ^ 44 := by
      rw [show (44 : ℝ) = ((44 : ℕ) : ℝ) by norm_num, ← exp_one_pow]
      exact pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 44
    have y0 : 0.23745 ≤ 1.47088 * u - 44 := by norm_num at u1 ⊢; linarith
    have y1 : 1.47088 * u - 44 ≤ 0.25 := by norm_num at u2 ⊢; linarith
    have q := sum_le_exp_of_nonneg (x := 1.47088 * u - 44) (by linarith) 6
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at q
    have q2 := pow_le_pow_left₀ (by norm_num) y0 2
    have q3 := pow_le_pow_left₀ (by norm_num) y0 3
    have q4 := pow_le_pow_left₀ (by norm_num) y0 4
    have q5 := pow_le_pow_left₀ (by norm_num) y0 5
    have b1 : (1.268 : ℝ) ≤ exp (1.47088 * u - 44) := by
      norm_num at q q2 q3 q4 q5 ⊢; linarith
    have b2 : exp (1.47088 * u - 44) ≤ exp 1 := exp_le_exp.mpr (by linarith)
    have e1 := exp_one_lt_d9
    have c1 : (16294579238595022365 : ℝ) ≤ 2.7182818283 ^ 44 * 1.268 := by norm_num
    have c2 : (2.7182818286 : ℝ) ^ 44 * 2.7182818286 < 961380175077106319535 := by norm_num
    have p1 := mul_le_mul a1 b1 (by norm_num) (exp_pos _).le
    have p2 := mul_le_mul a2 (b2.trans e1.le) (exp_pos _).le (by positivity)
    constructor
    · push_cast; linarith
    · push_cast; linarith
  have : BJSEm.pbar B2 = 53 := by
    apply BJSEm.pbar_eq B2 53 59 (by norm_num) hb.1 hb.2
    intro p h1 h2
    interval_cases p <;> norm_num
  unfold BJSEm.eps; rw [this]; norm_num


end LeanLab.ChenExplicit.Eps32155
