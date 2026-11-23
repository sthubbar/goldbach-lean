module

public import LeanLab.ChenExplicit.Section9Link
public import LeanLab.ChenExplicit.BJSEpsM

/-!
AI-written Lean code, Claude, 2026-10-18, CLOUD session 20261018T2315Z-cloud11, unit U-5023,
taking up the REQUEST U-0977: harden FINDING F-0023 by moving its Python margin model into Lean.
P0009 Bordignon, Johnston, Starichkova 2022, arXiv 2207.09452v6, Section 9.

The Section9.lean definitions are written for the lab's own parameters, `log log X₂ = 32.8` and
`ε₀ = 3·10⁻⁵`. Here the same formulas take `log log X₂` and `ε₀` as arguments, `cAbP` and `cBP`,
and `cAb_eq`, `cB_eq` check by `rfl` that the old definitions are the instances at 32.8 and
3·10⁻⁵; likewise `mX3P`, `φP` against BJSmX3.lean. So nothing is retyped from the paper here.

At the PRINTED Section 9 parameters `X₂ = exp(exp 32.7)`, `δ = 1.478`, `α = 10⁻⁵`,
`ε₀ = 10⁻⁴`, with `X₃ = X₂^{1/8}` and Theorems 44 (b), 50 (b), 51 as corrected per F-0021 and
F-0022, PROVED:
- `pbar1_printed`, `pbar2_printed`: `p̄ = 59` at `x₁(X₂)` and `p̄ = 53` at `x₂(X₃)`, so
  `ε₁ = 1/57` and `ε₂ = 1/51` exactly by (121);
- `m_ge`: `m(X₃) ≥ 10⁻⁸` for every `v ≥ φ(log x₂(X₃))`, in particular the supremum `v'₀(X₃)` of
  (72); Python gives `m(X₃) ≈ 1.21·10⁻⁸`. The heart is `ν ℓ ≤ 144.5`, true value 144.37;
- `f0023_printed`: the case (b) combination `cA - cQ/2 - cB/2` is below `-6·10⁻³` for every
  `log N ≥ log X₂` and every admissible value of the X₂-only constants `a, c₄*, w, l₁*, l*`,
  each only assumed nonnegative. The paper needs at least `2·10⁻⁴`. Python gives `-8.16·10⁻³`.

`X₃` is taken as `X₂^{1/8}`, `log log X₃ = 30.62056`, where Section 9 prints `X₃ = exp(exp 30.62)`.
The printed `X₃` is slightly smaller, so `m(X₃)` is larger, about `1.228·10⁻⁸` against `1.212·10⁻⁸`,
and the combination about `-8.28·10⁻³`; the choice here favours the paper, but the theorem below
is literally about `X₃ = X₂^{1/8}`. VERIFY subagent, same session: AGREE, all formulas MATCH.

This is a Lean proof that the paper's Section 9 inequality, case (b), fails at its printed
parameters once F-0021 and F-0022 are corrected. It concerns only the explicit threshold
exp(exp(32.7)) of Theorem 3; Chen's theorem itself is not in doubt, and Goldbach is open.
What the proof rests on: the lab's transcription of Theorems 44 (b), 50 (b), 51 in Section9.lean,
checked against the alttext in U-0920 and U-0923, and the corrections F-0021, F-0022; the reading
of `ν` at `x₂(X₃)` in `m(X₃)`, the one most favourable to the paper.
-/

@[expose] public section

open Real

noncomputable section
namespace LeanLab.ChenExplicit.F0023

open LeanLab.ChenExplicit LeanLab.ChenExplicit.BJS LeanLab.ChenExplicit.Section9

/-! ### The Section 9 formulas with `log log X₂` and `ε₀` as arguments -/

/-- `c_{α₁,X₂} = 4 - 8α₁ - 160 log log X₂ / log X₂`, (136), `ll = log log X₂`. -/
def ccP (ll LX : ℝ) : ℝ := 4 - 8 * α - 160 * ll / LX

/-- Theorem 44 (b), as `Section9.cAb` with `log log X₂ = ll`. -/
def cAbP (ll g T e1 a c4s w L LX : ℝ) : ℝ :=
  8 * (1 + 32.02 / L ^ 2) * (fS g (ccP ll LX) - e1 * (1 - fS g (ccP ll LX)) -
    (1 + e1) * ε * 107 * exp 2 * h (ccP ll LX) -
    (3 * e1 + a) * (max (1 - fS g (ccP ll LX)) (FS g (ccP ll LX) - 1) +
      ε * 107 * exp 2 * h (ccP ll LX)) -
    a - 64.04 / L ^ 2 - 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w)

/-- Theorem 51 corrected, as `Section9.cB` with `ε₀ = e0`. -/
def cBP (e0 g T e2 cb m L : ℝ) : ℝ :=
  1.00005 * (1 + e2) * (1 + 4.51 / L ^ 2) *
      (2 / (1 / 2 - α) * g + 3 * ε * 106 * exp 2 * h (3 / 2 - 3 * α)) * (1 + e0 + 9 / L) *
      (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2)) +
    g / (2 * T) * (320 * m * (1 + e0) / (3 * log (1 + e0)) +
      0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0)))

theorem cc_eq (LX : ℝ) : cc LX = ccP (328 / 10) LX := rfl

theorem cAb_eq (g T e1 a c4s w L LX : ℝ) :
    cAb g T e1 a c4s w L LX = cAbP (328 / 10) g T e1 a c4s w L LX := rfl

theorem cB_eq (g T e2 cb m L : ℝ) : cB g T e2 cb m L = cBP (3 / 100000) g T e2 cb m L := rfl

/-! ### Lemma 32's `m(X₃)` with `log log X₂ = ll`, `δ` as arguments, `X₃ = X₂^{1/8}` -/

/-- `log X₃ = e^{ll}/8`. -/
def Λ3P (ll : ℝ) : ℝ := exp ll / 8
/-- `log x₂(X₃)`, (75). -/
def ℓP (ll : ℝ) : ℝ := Λ3P ll - 15 * log (Λ3P ll)
/-- `K_δ(x₂) = log^δ x₂`. -/
def KP (ll δ : ℝ) : ℝ := ℓP ll ^ δ
/-- `ν(x₂)`, (91), `R₁ = 2.0452`. -/
def νP (ll δ : ℝ) : ℝ :=
  min (100 / (sqrt (KP ll δ) * log (KP ll δ) ^ 2)) (1 / (2 * 2.0452 * (10 * log (ℓP ll))))
/-- `β₀(x₂) = 1 - ν(x₂)`. -/
def β0P (ll δ : ℝ) : ℝ := 1 - νP ll δ

/-- the bracket of (72) at `Y = log y`. -/
def φP (ll δ Y : ℝ) : ℝ :=
  3.2e-8 / Y ^ 4 + Y ^ 4 * (exp ((β0P ll δ - 1) * Y) / β0P ll δ + 1.02 * Y ^ 10 / exp (Y / 2) +
    3 * Y ^ 10 / exp (2 * Y / 3))

/-- `v₀(X₃)` of Lemma 29, (71), with `v'₀ = v`. -/
def v0P (ll v : ℝ) : ℝ :=
  v * (1 + 1 / (Λ3P ll ^ 10 * ℓP ll ^ 5) + 1 / ((1 - 6 / ℓP ll) * Λ3P ll)) + 3 / Λ3P ll

/-- `m(X₃)`, Lemma 32. -/
def mX3P (ll v : ℝ) : ℝ :=
  39 * v0P ll v + 108 * Λ3P ll ^ 16 / (exp (Λ3P ll) * log (Λ3P ll)) + 26 * Λ3P ll ^ 5 / ℓP ll ^ 10 +
    88 * Λ3P ll ^ 5 * (exp (-(8 / 3 * Λ3P ll)) + exp (-(Λ3P ll / 2))) + 106 / Λ3P ll ^ 6

theorem φ_eq (Y : ℝ) : BJSm.φ Y = φP (328 / 10) 1.476 Y := rfl

theorem mX3_eq (v : ℝ) : BJSm.mX3 v = mX3P (328 / 10) v := rfl

/-! ### Numerics at the printed `log log X₂ = 32.7` -/

/-- the printed `log log X₂`. -/
abbrev ll : ℝ := 327 / 10

lemma exp327_ge : (1.5 * 10 ^ 14 : ℝ) ≤ exp ll := by
  have e : exp ll = exp ((32 : ℕ) : ℝ) * exp (7 / 10) := by
    rw [← exp_add]; norm_num
  have h1 := BJS51.exp_nat_ge 32
  have h2 := quadratic_le_exp_of_nonneg (x := (7 / 10 : ℝ)) (by norm_num)
  rw [e]
  have h3 := mul_le_mul h1 h2 (by norm_num) (exp_pos _).le
  have h4 : (1.5 * 10 ^ 14 : ℝ) ≤ 2.7182818283 ^ 32 * (1 + 7 / 10 + (7 / 10) ^ 2 / 2) := by
    norm_num
  linarith

lemma Λ3_ge : (1.8 * 10 ^ 13 : ℝ) ≤ Λ3P ll := by unfold Λ3P; have := exp327_ge; linarith

lemma log_Λ3 : log (Λ3P ll) = ll - 3 * log 2 := by
  unfold Λ3P
  rw [log_div (exp_pos _).ne' (by norm_num), log_exp, show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
  push_cast; ring

lemma ℓ_bounds : Λ3P ll * (1 - 1 / 10 ^ 10) ≤ ℓP ll ∧ ℓP ll ≤ Λ3P ll := by
  unfold ℓP
  have h := Λ3_ge
  have hl := log_Λ3
  have l2 := log_two_gt_d9
  have l2' := log_two_lt_d9
  constructor <;> rw [hl] <;> norm_num at l2 l2' ⊢ <;> nlinarith

lemma ℓ_pos : 0 < ℓP ll := by have := ℓ_bounds; have := Λ3_ge; nlinarith

/-- `30.6205 ≤ log ℓ ≤ 30.62056`. -/
lemma logℓ_bounds : 30.6205 ≤ log (ℓP ll) ∧ log (ℓP ll) ≤ 30.62056 := by
  obtain ⟨h1, h2⟩ := ℓ_bounds
  have hΛ := Λ3_ge
  have hl := log_Λ3
  have l2 := log_two_gt_d9
  have l2' := log_two_lt_d9
  constructor
  · have : log (Λ3P ll * (1 - 1 / 10 ^ 10)) ≤ log (ℓP ll) := log_le_log (by positivity) h1
    rw [log_mul (by positivity) (by norm_num), hl] at this
    have h3 := Real.one_sub_inv_le_log_of_pos (x := (1 - 1 / 10 ^ 10 : ℝ)) (by norm_num)
    norm_num at l2' h3 this ⊢; linarith
  · have : log (ℓP ll) ≤ log (Λ3P ll) := log_le_log ℓ_pos h2
    rw [hl] at this; norm_num at l2 this ⊢; linarith

/-- the printed `δ`. -/
abbrev δ : ℝ := 1.478

/-- **`ν ℓ ≤ 144.5`** at the printed parameters, true value 144.37. -/
lemma νℓ_le : νP ll δ * ℓP ll ≤ 144.5 := by
  obtain ⟨u1, u2⟩ := logℓ_bounds
  have hℓ := ℓ_pos
  set u := log (ℓP ll) with hu
  have hK : KP ll δ = exp (u * 1.478) := by unfold KP; rw [rpow_def_of_pos hℓ]
  have hlogK : log (KP ll δ) = 1.478 * u := by rw [hK, log_exp]; ring
  have hsK : sqrt (KP ll δ) = exp (0.739 * u) := by
    rw [hK, sqrt_eq_rpow, ← exp_mul]; ring_nf
  have hℓe : ℓP ll = exp u := (exp_log hℓ).symm
  have hmin : νP ll δ ≤ 100 / (exp (0.739 * u) * (1.478 * u) ^ 2) := by
    unfold νP; rw [hsK, hlogK]; exact min_le_left _ _
  have hν0 : 0 ≤ νP ll δ := by
    unfold νP; rw [hsK, hlogK]
    apply le_min <;> positivity
  have hE : exp (0.261 * u) ≤ 2957.3 := by
    have a : exp (0.261 * u) ≤ exp (8 - 0.00803) := exp_le_exp.mpr (by nlinarith)
    have e : exp (8 - 0.00803 : ℝ) = exp ((8 : ℕ) : ℝ) * (exp 0.00803)⁻¹ := by
      rw [sub_eq_add_neg, exp_add, exp_neg]; norm_num
    have b := BJS51.exp_nat_le 8
    have c := add_one_le_exp (0.00803 : ℝ)
    have c' : (exp (0.00803 : ℝ))⁻¹ ≤ (1.00803 : ℝ)⁻¹ := by
      rw [inv_le_inv₀ (exp_pos _) (by norm_num)]; linarith
    have d := mul_le_mul b c' (by positivity) (by positivity)
    have f : (2.7182818286 : ℝ) ^ 8 * (1.00803 : ℝ)⁻¹ ≤ 2957.3 := by norm_num
    rw [e] at a; linarith
  have hu2 : 2048.2 ≤ (1.478 * u) ^ 2 := by nlinarith
  have key : 100 / (exp (0.739 * u) * (1.478 * u) ^ 2) * ℓP ll ≤ 144.5 := by
    rw [hℓe, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have e : exp u = exp (0.739 * u) * exp (0.261 * u) := by rw [← exp_add]; ring_nf
    rw [e]
    have hp := exp_pos (0.739 * u)
    have : 100 * exp (0.261 * u) ≤ 144.5 * (1.478 * u) ^ 2 := by nlinarith
    nlinarith
  calc νP ll δ * ℓP ll ≤ 100 / (exp (0.739 * u) * (1.478 * u) ^ 2) * ℓP ll :=
        mul_le_mul_of_nonneg_right hmin hℓ.le
    _ ≤ 144.5 := key

lemma ν_pos : 0 < νP ll δ := by
  obtain ⟨u1, _⟩ := logℓ_bounds
  have hℓ := ℓ_pos
  unfold νP
  have hK : 0 < KP ll δ := by unfold KP; positivity
  have hK1 : 0 < log (KP ll δ) := by
    unfold KP; rw [log_rpow hℓ]; exact mul_pos (by norm_num) (by linarith)
  apply lt_min
  · have := sqrt_pos.mpr hK; positivity
  · apply div_pos (by norm_num); nlinarith

lemma ν_lt : νP ll δ < 1 := by
  obtain ⟨u1, _⟩ := logℓ_bounds
  unfold νP
  refine (min_le_right _ _).trans_lt ?_
  rw [div_lt_one (by nlinarith)]; nlinarith

/-- **`φ(log x₂(X₃)) ≥ 2.7·10⁻¹⁰`**, the Siegel zero term `ℓ⁴ e^{-νℓ}/β₀` alone. -/
lemma phi_ℓ_ge : 2.7 / 10 ^ 10 ≤ φP ll δ (ℓP ll) := by
  obtain ⟨u1, u2⟩ := logℓ_bounds
  have hℓ := ℓ_pos
  have hν := νℓ_le
  have hν0 := ν_pos
  have hν1 := ν_lt
  have hb0 : 0 < β0P ll δ := by unfold β0P; linarith
  have hb1 : β0P ll δ ≤ 1 := by unfold β0P; linarith
  have hℓ4 : exp (4 * 30.6205) ≤ ℓP ll ^ 4 := by
    have : ℓP ll = exp (log (ℓP ll)) := (exp_log hℓ).symm
    rw [this, ← exp_nat_mul]; push_cast; exact exp_le_exp.mpr (by linarith)
  have e1 : (β0P ll δ - 1) * ℓP ll = -(νP ll δ * ℓP ll) := by unfold β0P; ring
  have hx : exp (-144.5) ≤ exp ((β0P ll δ - 1) * ℓP ll) := by
    rw [e1]; exact exp_le_exp.mpr (by linarith)
  have hprod : exp (4 * 30.6205) * exp (-144.5) ≤ ℓP ll ^ 4 * exp ((β0P ll δ - 1) * ℓP ll) :=
    mul_le_mul hℓ4 hx (exp_pos _).le (by positivity)
  have hnum : 2.7 / 10 ^ 10 ≤ exp (4 * 30.6205) * exp (-144.5) := by
    rw [← exp_add]
    have e : (4 * 30.6205 + -144.5 : ℝ) = -((22 : ℕ) : ℝ) + -0.018 := by norm_num
    rw [e, exp_add, exp_neg]
    have a := BJS51.exp_nat_le 22
    have b := add_one_le_exp (-0.018 : ℝ)
    have c : ((2.7182818286 : ℝ) ^ 22)⁻¹ ≤ (exp ((22 : ℕ) : ℝ))⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (exp_pos _)]; exact a
    have d := mul_le_mul c b (by norm_num) (by positivity)
    have f : (2.7 / 10 ^ 10 : ℝ) ≤ ((2.7182818286 : ℝ) ^ 22)⁻¹ * (-0.018 + 1) := by norm_num
    linarith
  have hdiv : ℓP ll ^ 4 * exp ((β0P ll δ - 1) * ℓP ll) ≤
      ℓP ll ^ 4 * (exp ((β0P ll δ - 1) * ℓP ll) / β0P ll δ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [le_div_iff₀ hb0]
    have := exp_pos ((β0P ll δ - 1) * ℓP ll)
    nlinarith
  unfold φP
  have t1 : 0 ≤ 3.2e-8 / ℓP ll ^ 4 := by positivity
  have t3 : 0 ≤ ℓP ll ^ 4 * (1.02 * ℓP ll ^ 10 / exp (ℓP ll / 2) +
      3 * ℓP ll ^ 10 / exp (2 * ℓP ll / 3)) := by positivity
  have e : ℓP ll ^ 4 * (exp ((β0P ll δ - 1) * ℓP ll) / β0P ll δ +
      1.02 * ℓP ll ^ 10 / exp (ℓP ll / 2) + 3 * ℓP ll ^ 10 / exp (2 * ℓP ll / 3)) =
      ℓP ll ^ 4 * (exp ((β0P ll δ - 1) * ℓP ll) / β0P ll δ) +
      ℓP ll ^ 4 * (1.02 * ℓP ll ^ 10 / exp (ℓP ll / 2) + 3 * ℓP ll ^ 10 / exp (2 * ℓP ll / 3)) := by
    ring
  rw [e]
  linarith

/-- **`m(X₃) ≥ 10⁻⁸`** at the printed parameters, for every `v` at least the value of (72) at
`y = x₂(X₃)`; the supremum `v'₀(X₃)` of Lemma 29 is such a `v`. -/
theorem m_ge (v : ℝ) (hv : φP ll δ (ℓP ll) ≤ v) : 1 / 10 ^ 8 ≤ mX3P ll v := by
  have hφ := phi_ℓ_ge
  have hv1 : 2.7 / 10 ^ 10 ≤ v := hφ.trans hv
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv1
  have hΛ := Λ3_ge
  have hℓ := ℓ_pos
  have hℓ13 : (1.8 * 10 ^ 13 : ℝ) * (1 - 1 / 10 ^ 10) ≤ ℓP ll := by
    have := ℓ_bounds.1; nlinarith
  have h6 : 6 / ℓP ll < 1 := by rw [div_lt_one hℓ]; norm_num at hℓ13; linarith
  have hlog : 0 < log (Λ3P ll) := log_pos (by linarith)
  have hΛ0 : 0 < Λ3P ll := by linarith
  have hq : 0 ≤ 1 / ((1 - 6 / ℓP ll) * Λ3P ll) := by
    apply div_nonneg (by norm_num); apply mul_nonneg (by linarith) (by linarith)
  have hv0' : v ≤ v0P ll v := by
    unfold v0P
    have : 0 ≤ 1 / (Λ3P ll ^ 10 * ℓP ll ^ 5) := by positivity
    have : 0 ≤ 3 / Λ3P ll := by positivity
    nlinarith
  unfold mX3P
  have r : 0 ≤ 108 * Λ3P ll ^ 16 / (exp (Λ3P ll) * log (Λ3P ll)) + 26 * Λ3P ll ^ 5 / ℓP ll ^ 10 +
      88 * Λ3P ll ^ 5 * (exp (-(8 / 3 * Λ3P ll)) + exp (-(Λ3P ll / 2))) + 106 / Λ3P ll ^ 6 := by
    positivity
  have c : (1 : ℝ) / 10 ^ 8 ≤ 39 * (2.7 / 10 ^ 10) := by norm_num
  linarith

/-! ### `ε₁`, `ε₂` at the printed parameters, (121) -/

/-- `log^δ x₁(X₂)`, `log x₁(X₂) = e^{32.7} - 5 · 32.7`. -/
def B1P : ℝ := (exp ll - 5 * ll) ^ δ
/-- `log^δ x₂(X₃)`. -/
def B2P : ℝ := ℓP ll ^ δ

theorem pbar1_printed : BJSEm.pbar B1P = 59 := by
  have hE := exp327_ge
  have hpos : 0 < exp ll - 5 * ll := by norm_num at hE ⊢; linarith
  have hlo : exp ll * (999 / 1000) ≤ exp ll - 5 * ll := by norm_num at hE ⊢; nlinarith
  have l2 : ll + log (999 / 1000) ≤ log (exp ll - 5 * ll) := by
    rw [← log_exp ll, ← log_mul (exp_pos _).ne' (by norm_num), log_exp]
    exact log_le_log (by positivity) hlo
  have l3 : -(1 / 999 : ℝ) ≤ log (999 / 1000) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (999 / 1000 : ℝ)) (by norm_num)
    norm_num at this ⊢; linarith
  have hl : log (exp ll - 5 * ll) ≤ ll := by
    have := log_le_log hpos (show exp ll - 5 * ll ≤ exp ll by norm_num)
    rwa [log_exp] at this
  apply BJSEm.pbar_eq B1P 59 61 (by norm_num)
  · unfold B1P
    rw [rpow_def_of_pos hpos, BJS51.oddPrimorial_59]
    have hm : log (exp ll - 5 * ll) * δ = 48 + (1.478 * log (exp ll - 5 * ll) - 48) := by ring
    rw [hm, exp_add]
    have a1 := BJS51.exp_nat_ge 48
    push_cast at a1
    have b : 0.329 ≤ 1.478 * log (exp ll - 5 * ll) - 48 := by norm_num at l2 l3 ⊢; nlinarith
    have b2 := quadratic_le_exp_of_nonneg (x := 1.478 * log (exp ll - 5 * ll) - 48) (by linarith)
    have b3 : (1.383 : ℝ) ≤ exp (1.478 * log (exp ll - 5 * ll) - 48) := by nlinarith
    have c : (961380175077106319535 : ℝ) ≤ 2.7182818283 ^ 48 * 1.383 := by norm_num
    have := mul_le_mul a1 b3 (by norm_num) (exp_pos _).le
    push_cast; linarith
  · unfold B1P
    rw [rpow_def_of_pos hpos, BJSEm.oddPrimorial_61]
    have h1 : exp (log (exp ll - 5 * ll) * δ) ≤ exp 49 := exp_le_exp.mpr (by norm_num at hl ⊢; nlinarith)
    have h2 : exp (49 : ℝ) = exp 1 ^ 49 := by rw [exp_one_pow]; norm_num
    have h3 : exp 1 ^ 49 ≤ (2.7182818286 : ℝ) ^ 49 :=
      pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 49
    have h4 : (2.7182818286 : ℝ) ^ 49 < 58644190679703485491635 := by norm_num
    push_cast; linarith
  · intro p h1 h2
    interval_cases p; norm_num

lemma ℓ_eq : ℓP ll = exp (327 / 10) / 8 - 15 * (327 / 10 - 3 * log 2) := by
  unfold ℓP; rw [log_Λ3]; rfl

theorem pbar2_printed : BJSEm.pbar B2P = 53 := by
  obtain ⟨a, b⟩ := BJS51.pbar_X2_eighth
  have e : B2P = (exp (327 / 10) / 8 - 15 * (327 / 10 - 3 * log 2)) ^ (1.478 : ℝ) := by
    unfold B2P; rw [ℓ_eq]
  apply BJSEm.pbar_eq B2P 53 59 (by norm_num) (by rw [e]; exact a) (by rw [e]; exact b)
  intro p h1 h2
  interval_cases p <;> norm_num

theorem eps1_printed : BJSEm.eps B1P = 1 / 57 := by unfold BJSEm.eps; rw [pbar1_printed]; norm_num
theorem eps2_printed : BJSEm.eps B2P = 1 / 51 := by unfold BJSEm.eps; rw [pbar2_printed]; norm_num

/-! ### The case (b) combination at the printed parameters -/

/-- the printed `ε₀`. -/
abbrev e0p : ℝ := 1 / 10000

lemma LXp_ge : (10 : ℝ) ^ 14 ≤ exp ll := by have := exp327_ge; linarith

lemma ccP_bounds (LX : ℝ) (hLX : 10 ^ 14 ≤ LX) :
    3.9999199 ≤ ccP ll LX ∧ ccP ll LX ≤ 4 - 8 * α := by
  unfold ccP
  have hpos : 0 < 160 * ll / LX := by positivity
  have hx : 160 * ll / LX ≤ 1 / 10 ^ 10 := by
    rw [div_le_iff₀ (by linarith)]; norm_num; linarith
  norm_num at hx ⊢; constructor <;> linarith

lemma fS_ub (g LX : ℝ) (hg : 0 ≤ g) (hLX : 10 ^ 14 ≤ LX) : fS g (ccP ll LX) ≤ g * 0.5493087 := by
  unfold fS
  obtain ⟨c1, c2⟩ := ccP_bounds LX hLX
  have e : (4 - 8 * α - 1 : ℝ) = 3 * (1 - 8 * α / 3) := by ring
  have hl0 : log (ccP ll LX - 1) ≤ log (4 - 8 * α - 1) :=
    log_le_log (by norm_num at c1 ⊢; linarith) (by linarith)
  rw [e, log_mul (by norm_num) (by norm_num)] at hl0
  have hl1 := log_le_sub_one_of_pos (x := (1 - 8 * α / 3 : ℝ)) (by norm_num)
  have hl : log (ccP ll LX - 1) ≤ log 3 - 8 * α / 3 := by linarith
  have l3 := log_three_lt_d9
  have h0 : 0 ≤ log (ccP ll LX - 1) := log_nonneg (by norm_num at c1 ⊢; linarith)
  rw [div_le_iff₀ (by linarith)]
  norm_num at l3 ⊢
  nlinarith

/-- **Theorem 44 (b) at the printed parameters, upper bound.** -/
lemma cAbP_le (g T e1 a c4s w L LX : ℝ) (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0 < T)
    (he1 : e1 = 1 / 57) (ha : 0 ≤ a) (hc4 : 0 ≤ c4s) (hw : 0 ≤ w)
    (hLX : 10 ^ 14 ≤ LX) (hL : LX ≤ L) :
    cAbP ll g T e1 a c4s w L LX ≤ 8 * (1 + 1 / 10 ^ 26) * ((61 / 57) * (g * 0.5493087) - 4 / 57) := by
  unfold cAbP
  obtain ⟨c1, c2⟩ := ccP_bounds LX hLX
  set X := fS g (ccP ll LX) with hX
  set H := exp 2 * h (ccP ll LX) with hH
  set Mb := max (1 - fS g (ccP ll LX)) (FS g (ccP ll LX) - 1) with hMb
  have hXu : X ≤ g * 0.5493087 := fS_ub g LX (by linarith) hLX
  have hX1 : X ≤ 1 := by nlinarith
  have hH0 : 0 ≤ H := by have := h_nonneg (ccP ll LX) (by linarith); positivity
  have hM : 1 - X ≤ Mb := le_max_left _ _
  have hL0 : 0 < L := by linarith
  have eq1 : (1 + e1) * ε * 107 * exp 2 * h (ccP ll LX) = (1 + e1) * ε * 107 * H := by rw [hH]; ring
  have eq2 : ε * 107 * exp 2 * h (ccP ll LX) = ε * 107 * H := by rw [hH]; ring
  rw [eq1, eq2]
  subst he1
  have t2 : 0 ≤ (1 + 1 / 57) * ε * 107 * H := by positivity
  have t3 : (3 * (1 / 57) + 0) * (1 - X) ≤ (3 * (1 / 57) + a) * (Mb + ε * 107 * H) := by
    have : 0 ≤ ε * 107 * H := by positivity
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have t4 : 0 ≤ 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w := by
    have : 0 ≤ g / (2 * T) := div_nonneg (by linarith) (by linarith)
    positivity
  have t5 : 0 ≤ 64.04 / L ^ 2 := by positivity
  set B := X - 1 / 57 * (1 - X) - (1 + 1 / 57) * ε * 107 * H - (3 * (1 / 57) + a) * (Mb + ε * 107 * H) -
    a - 64.04 / L ^ 2 - 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w with hB
  have hBu : B ≤ (61 / 57) * (g * 0.5493087) - 4 / 57 := by rw [hB]; nlinarith
  have hBu0 : 0 ≤ (61 / 57) * (g * 0.5493087) - 4 / 57 := by nlinarith
  have s2 := small_div2 32.02 L (by norm_num) (by norm_num) (hLX.trans hL)
  have hd0 : 0 ≤ 32.02 / L ^ 2 := by positivity
  calc 8 * (1 + 32.02 / L ^ 2) * B ≤ 8 * (1 + 32.02 / L ^ 2) * ((61 / 57) * (g * 0.5493087) - 4 / 57) :=
        mul_le_mul_of_nonneg_left hBu (by positivity)
    _ ≤ 8 * (1 + 1 / 10 ^ 26) * ((61 / 57) * (g * 0.5493087) - 4 / 57) := by
        apply mul_le_mul_of_nonneg_right _ hBu0; linarith

lemma Lam_ge : 3.58365 ≤ (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) := by
  have h6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
  have hr := Real.one_sub_inv_le_log_of_pos (x := (3 - 8 * α) / (3 - 18 * α)) (by norm_num)
  have := log_two_gt_d9; have := log_three_gt_d9
  rw [h6, le_div_iff₀ (by norm_num)]
  norm_num at *; linarith

/-- **Theorem 50 (b), lower bound.** -/
lemma cQb_ge (g T e1 l1s ls L LX : ℝ) (hg : 0 ≤ g) (hT : 0 < T) (he1 : e1 = 1 / 57)
    (hl1 : 0 ≤ l1s) (hls : 0 ≤ ls) (hLX : 10 ^ 14 ≤ LX) (hL : 0 < L) :
    8.0004 * (58 / 57) * (g / 4 * 3.58365) ≤ cQb g T e1 l1s ls L LX := by
  unfold cQb l2
  subst he1
  have hE := add_one_le_exp (LX / 8)
  have hEp := exp_pos (LX / 8)
  have r1 : 1 ≤ exp (LX / 8) / (exp (LX / 8) - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hΛ := Lam_ge
  have k1 : 0 ≤ 512 / (kα * LX ^ 2) := by positivity
  have k2 : 0 ≤ (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * exp 2 * h kα := by
    have := log83_nonneg; have := h_nonneg kα (by norm_num); positivity
  have hin : g / 4 * 3.58365 ≤ g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
      512 / (kα * LX ^ 2)) + (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * exp 2 * h kα := by
    have := mul_le_mul_of_nonneg_left (show 3.58365 ≤ (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) /
      (1 / 2 - α) + 512 / (kα * LX ^ 2) by linarith) (show 0 ≤ g / 4 by positivity)
    linarith
  have hin0 : 0 ≤ g / 4 * 3.58365 := by positivity
  have hl2 : g / 4 * 3.58365 ≤ exp (LX / 8) / (exp (LX / 8) - 1) *
      (g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) + 512 / (kα * LX ^ 2)) +
        (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * exp 2 * h kα) := by
    calc g / 4 * 3.58365 = 1 * (g / 4 * 3.58365) := by ring
      _ ≤ _ := mul_le_mul r1 hin hin0 (by linarith)
  have hd : 0 ≤ 32.02 / L ^ 2 := by positivity
  have p2 : 0 ≤ ls * (g / (2 * T)) := mul_nonneg hls (div_nonneg hg (by linarith))
  have p1 : 8.0004 * (58 / 57) * (g / 4 * 3.58365) ≤ 8.0004 * (1 + 32.02 / L ^ 2) * (1 + 1 / 57) *
      (l1s + exp (LX / 8) / (exp (LX / 8) - 1) *
      (g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) + 512 / (kα * LX ^ 2)) +
        (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * exp 2 * h kα)) := by
    have q : 8.0004 * (58 / 57) ≤ 8.0004 * (1 + 32.02 / L ^ 2) * (1 + 1 / 57) := by nlinarith
    apply mul_le_mul q (by linarith) hin0 (by positivity)
  linarith

/-- **Theorem 51 corrected, lower bound**, at `ε₀ = 10⁻⁴`. -/
lemma cBP_ge (g T e2 cb m L : ℝ) (hg : 0 ≤ g) (hT0 : 0 < T) (hT : T ≤ 0.6614) (he2 : e2 = 1 / 51)
    (hcb : 0.3630 ≤ cb) (hm : 1 / 10 ^ 8 ≤ m) (hL : 10 ^ 14 ≤ L) :
    1.00005 * (52 / 51) * 1 * (2 / (1 / 2 - α) * g) * (1 + e0p) * 0.3630 +
      g / 1.3228 * (320 * (1 / 10 ^ 8) * (1 + e0p) / (3 * e0p)) ≤ cBP e0p g T e2 cb m L := by
  unfold cBP
  subst he2
  have hL0 : 0 < L := by linarith
  have hlg0 : 0 < log (1 + e0p) := log_pos (by norm_num)
  have hlg1 : log (1 + e0p) ≤ e0p := by
    have := log_le_sub_one_of_pos (x := 1 + e0p) (by norm_num); linarith
  have hh : 0 ≤ 3 * ε * 106 * exp 2 * h (3 / 2 - 3 * α) := by
    have := h_nonneg (3 / 2 - 3 * α) (by norm_num); positivity
  have hbr : 0.3630 ≤ cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0p) / L + 27 / L ^ 2) := by
    have := log83_nonneg
    have : 0 ≤ (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0p) / L + 27 / L ^ 2) := by positivity
    have : 0 ≤ 36 / L ^ 2 := by positivity
    linarith
  have P1 : 1.00005 * (52 / 51) * 1 * (2 / (1 / 2 - α) * g) * (1 + e0p) ≤
      1.00005 * (1 + 1 / 51) * (1 + 4.51 / L ^ 2) *
      (2 / (1 / 2 - α) * g + 3 * ε * 106 * exp 2 * h (3 / 2 - 3 * α)) * (1 + e0p + 9 / L) := by
    have : 0 ≤ 4.51 / L ^ 2 := by positivity
    have : 0 ≤ 9 / L := by positivity
    have hg2 : 0 ≤ 2 / (1 / 2 - α) * g := by positivity
    have q1 : 1.00005 * (52 / 51) * (1 : ℝ) ≤ 1.00005 * (1 + 1 / 51) * (1 + 4.51 / L ^ 2) := by
      nlinarith
    have q2 : 2 / (1 / 2 - α) * g ≤ 2 / (1 / 2 - α) * g + 3 * ε * 106 * exp 2 * h (3 / 2 - 3 * α) := by
      linarith
    have q3 : 1 + e0p ≤ 1 + e0p + 9 / L := by linarith
    have q12 := mul_le_mul q1 q2 hg2 (by positivity)
    exact mul_le_mul q12 q3 (by norm_num) (le_trans (by positivity) q12)
  have P1n : 0 ≤ 1.00005 * (52 / 51) * 1 * (2 / (1 / 2 - α) * g) * (1 + e0p) := by positivity
  have part1 := mul_le_mul P1 hbr (by norm_num) (le_trans P1n P1)
  have hgT : g / 1.3228 ≤ g / (2 * T) := div_le_div_of_nonneg_left hg (by linarith) (by linarith)
  have hmt : 320 * (1 / 10 ^ 8) * (1 + e0p) / (3 * e0p) ≤ 320 * m * (1 + e0p) / (3 * log (1 + e0p)) := by
    apply div_le_div₀ (by positivity) (by nlinarith) (by positivity) (by linarith)
  have htail : 0 ≤ 0.13 * (1 + e0p) * L ^ 5 / (exp (L / 8) * log (1 + e0p)) := by
    have := exp_pos (L / 8); positivity
  have part2 : g / 1.3228 * (320 * (1 / 10 ^ 8) * (1 + e0p) / (3 * e0p)) ≤
      g / (2 * T) * (320 * m * (1 + e0p) / (3 * log (1 + e0p)) +
        0.13 * (1 + e0p) * L ^ 5 / (exp (L / 8) * log (1 + e0p))) :=
    mul_le_mul hgT (by linarith) (by positivity) (div_nonneg hg (by linarith))
  linarith

/-- **FINDING F-0023 in Lean.** At the printed Section 9 parameters of BJS 2022,
`X₂ = exp(exp 32.7)`, `X₃ = X₂^{1/8}`, `δ = 1.478`, `α = 10⁻⁵`, `ε₀ = 10⁻⁴`, with Theorems 44 (b),
50 (b), 51 corrected per F-0021 and F-0022, `ε₁, ε₂` from (121) and `m(X₃)` from Lemma 32 with any
`v ≥` the value of (72) at `x₂(X₃)`, the case (b) combination `cA - cQ/2 - cB/2` is below
`-6·10⁻³` for every `log N ≥ log X₂` and every nonnegative `a(X₂), c₄*, w, l₁*, l*`. Section 9
needs it to be at least `2·10⁻⁴`. -/
theorem f0023_printed (a c4s w l1s ls L v : ℝ) (ha : 0 ≤ a) (hc4 : 0 ≤ c4s) (hw : 0 ≤ w)
    (hl1 : 0 ≤ l1s) (hls : 0 ≤ ls) (hL : exp ll ≤ L) (hv : φP ll δ (ℓP ll) ≤ v) :
    cAbP ll (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) a c4s w L (exp ll) -
      cQb (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) l1s ls L (exp ll) / 2 -
      cBP e0p (exp eulerMascheroniConstant) twinC (BJSEm.eps B2P) BJS.cbar (mX3P ll v) L / 2 <
      -6 / 1000 := by
  have hg1 := g_ge
  have hg2 := g_le
  have hT0 : 0 < twinC := by have := twinC_ge_065; linarith
  have hT := twinC_le_06614
  have hLX := LXp_ge
  have hA := cAbP_le (exp eulerMascheroniConstant) twinC _ a c4s w L (exp ll) hg1 hg2 hT0
    eps1_printed ha hc4 hw hLX hL
  have hQ := cQb_ge (exp eulerMascheroniConstant) twinC _ l1s ls L (exp ll) (by linarith) hT0
    eps1_printed hl1 hls hLX (by linarith)
  have hB := cBP_ge (exp eulerMascheroniConstant) twinC _ BJS.cbar (mX3P ll v) L (by linarith) hT0
    (by norm_num at hT ⊢; linarith) eps2_printed (by have := BJS.cbar_gt; norm_num at this ⊢; linarith)
    (m_ge v hv) (hLX.trans hL)
  norm_num at hA hQ hB ⊢
  linarith

/-- So Section 9's requirement `cA - cQ/2 - cB/2 ≥ 2·10⁻⁴` fails at the printed parameters. -/
theorem f0023_not_margin (a c4s w l1s ls L v : ℝ) (ha : 0 ≤ a) (hc4 : 0 ≤ c4s) (hw : 0 ≤ w)
    (hl1 : 0 ≤ l1s) (hls : 0 ≤ ls) (hL : exp ll ≤ L) (hv : φP ll δ (ℓP ll) ≤ v) :
    ¬ (2 / 10000 ≤
      cAbP ll (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) a c4s w L (exp ll) -
      cQb (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) l1s ls L (exp ll) / 2 -
      cBP e0p (exp eulerMascheroniConstant) twinC (BJSEm.eps B2P) BJS.cbar (mX3P ll v) L / 2) := by
  have := f0023_printed a c4s w l1s ls L v ha hc4 hw hl1 hls hL hv
  intro h; linarith

/-- Vacuity test: the hypotheses hold, with `log N = log X₂`, `v` the value of (72) at
`x₂(X₃)` and the X₂-only constants zero. -/
theorem f0023_instance :
    cAbP ll (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) 0 0 0 (exp ll) (exp ll) -
      cQb (exp eulerMascheroniConstant) twinC (BJSEm.eps B1P) 0 0 (exp ll) (exp ll) / 2 -
      cBP e0p (exp eulerMascheroniConstant) twinC (BJSEm.eps B2P) BJS.cbar
        (mX3P ll (φP ll δ (ℓP ll))) (exp ll) / 2 < -6 / 1000 :=
  f0023_printed 0 0 0 0 0 _ _ le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl


end LeanLab.ChenExplicit.F0023
