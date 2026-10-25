module

public import LeanLab.DensityGoldbach.U1484Split
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Unit U-1484, run 20261022T1302Z-31860. P0047 Alsetri and Shao 2024, Theorem 1.2.

`ArcClassBound` of U1478Arcs, PROVED, from `twS_explicit` of U1484Split, the lab's
unconditional `major_arc` at `A = 11`, and the choice of levels
`P = ⌈(log X)^10⌉`, `Q = ⌊X/(log X)^10⌋`: then every modulus `q ≤ W P` is at most `(log X)^11`,
`|β| X ≤ (log X)^10`, the minor arc bound is `O_W(X/log X + X^{4/5} (log X)^4)` and the major arc
error is `O_W((log X)^10 √X + X/log X + (log X)^21)`, both `o(X)` for fixed `W`. The `X/z` term is
at most `c/4` of the target once `z ≥ 4/c`.

* `arcClassBound`, PROVED: `ArcClassBound`; `green62`, PROVED: `Green62`.
* `alsetriShao_1_2_U1484 : GreenThm21Circle3 → AlsetriShao12`, Theorem 1.2, CONDITIONAL ON
  `GreenThm21Circle3` only.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real Filter
noncomputable section
namespace LeanLab.DensityGoldbach.U1484

open LeanLab.DensityGoldbach.U1478 LeanLab.DensityGoldbach.U1481

local notation "SV" => LeanLab.PNTPort.Vinogradov.S
local notation "VV" => LeanLab.PNTPort.Vinogradov.V

/-- The major arc level `P = ⌈(log X)^10⌉`. -/
def Pc (X : ℕ) : ℕ := ⌈Real.log X ^ 10⌉₊

/-- The minor arc level `Q = ⌊X/(log X)^10⌋`. -/
def Qc (X : ℕ) : ℕ := ⌊(X : ℝ) / Real.log X ^ 10⌋₊

/-- The uniform major arc error for moduli `q ≤ W P` and `|β| ≤ 1/(Q + 1)`. -/
def Emaj (W X : ℕ) (K c' : ℝ) : ℝ :=
  (7 * Real.sqrt X + ((W * Pc X : ℕ) : ℝ) * K * X * Real.exp (-c' * Real.sqrt (Real.log X / 2)) +
    Real.log ((W * Pc X : ℕ) : ℝ) / Real.log 2 * Real.log X) *
    (1 + 2 * π * X / ((Qc X : ℝ) + 1))

/-- `major_arc`'s error is monotone up to `Emaj`. -/
theorem major_err_le {W X q : ℕ} {K c' β : ℝ} (hK : 0 ≤ K) (hq : 1 ≤ q)
    (hqP : (q : ℝ) ≤ ((W * Pc X : ℕ) : ℝ)) (hβ : |β| ≤ 1 / ((Qc X : ℝ) + 1)) :
    (7 * Real.sqrt X + q * K * X * Real.exp (-c' * Real.sqrt (Real.log X / 2)) +
      Real.log q / Real.log 2 * Real.log X) * (1 + 2 * π * |β| * X) ≤ Emaj W X K c' := by
  unfold Emaj
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hlX := Real.log_natCast_nonneg X
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hex := (Real.exp_pos (-c' * Real.sqrt (Real.log X / 2))).le
  have h1 : (q : ℝ) * K * X * Real.exp (-c' * Real.sqrt (Real.log X / 2)) ≤
      ((W * Pc X : ℕ) : ℝ) * K * X * Real.exp (-c' * Real.sqrt (Real.log X / 2)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hqP hK) hX0) hex
  have h2 : Real.log q / Real.log 2 * Real.log X ≤
      Real.log ((W * Pc X : ℕ) : ℝ) / Real.log 2 * Real.log X :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (Real.log_le_log hq0 hqP) hl2.le) hlX
  have h3 : 1 + 2 * π * |β| * X ≤ 1 + 2 * π * X / ((Qc X : ℝ) + 1) := by
    have : 2 * π * X / ((Qc X : ℝ) + 1) = 2 * π * (1 / ((Qc X : ℝ) + 1)) * X := by ring
    rw [this]; gcongr
  have hn : 0 ≤ 7 * Real.sqrt X + ((W * Pc X : ℕ) : ℝ) * K * X *
      Real.exp (-c' * Real.sqrt (Real.log X / 2)) +
      Real.log ((W * Pc X : ℕ) : ℝ) / Real.log 2 * Real.log X := by
    have := Real.log_natCast_nonneg (W * Pc X)
    have : 0 ≤ ((W * Pc X : ℕ) : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
    positivity
  exact mul_le_mul (by linarith) h3 (by positivity) hn

set_option maxHeartbeats 800000 in
/-- **The pointwise asymptotic estimate**: under explicit size conditions on `ℓ = log X`, all
level conditions hold and both error terms are at most `δ X`. -/
theorem pointwise {W X : ℕ} (hW : 1 ≤ W) {δ K c' K' : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hK' : 0 < K')
    (hℓ : max (max (4 : ℝ) (2 * W)) (max (19200 * W / δ) (48 * W ^ 2 * K * K' / δ)) ≤ Real.log X)
    (hA : (W : ℝ) * Real.log X ^ 10 ≤ X)
    (hB : 9600 * W / δ * Real.log X ^ 4 ≤ (X : ℝ) ^ ((1 : ℝ) / 5))
    (hC : 168 * W / δ * Real.log X ^ 10 ≤ Real.sqrt X)
    (hD : 96 * W ^ 2 / δ * Real.log X ^ 21 ≤ X)
    (hex : Real.exp (-c' * Real.sqrt (Real.log X / 2)) ≤ K' / Real.log X ^ 21) :
    1 ≤ Pc X ∧ 1 ≤ Qc X ∧ Qc X ≤ X ∧ (W : ℝ) ≤ Qc X + 1 ∧ Real.exp 4 ≤ X ∧
      ((W * Pc X : ℕ) : ℝ) ≤ Real.log X ^ (11 : ℝ) ∧
      (W : ℝ) * Mb X (Pc X) (Qc X) ≤ δ * X ∧ 0 ≤ Emaj W X K c' ∧
      (W : ℝ) * Emaj W X K c' ≤ δ * X := by
  set ℓ := Real.log X with hℓdef
  set x : ℝ := (X : ℝ) with hxdef
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hℓ4 : 4 ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hℓ
  have hℓW : 2 * (W : ℝ) ≤ ℓ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hℓ
  have hℓa : 19200 * W / δ ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hℓ
  have hℓb : 48 * W ^ 2 * K * K' / δ ≤ ℓ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hℓ
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos X with h | h
    · exfalso
      have h0 : x = 0 := by rw [hxdef, h]; simp
      rw [hℓdef, h0, Real.log_zero] at hℓ4; linarith
    · have : (0 : ℝ) < (X : ℝ) := by exact_mod_cast h
      exact this
  have hxe : Real.exp ℓ = x := Real.exp_log hx0
  have hL10 : 1 ≤ ℓ ^ 10 := one_le_pow₀ hℓ1
  have hL10p : 0 < ℓ ^ 10 := by positivity
  -- levels
  have hP1 : ℓ ^ 10 ≤ (Pc X : ℝ) := Nat.le_ceil _
  have hP2 : (Pc X : ℝ) ≤ 2 * ℓ ^ 10 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ ℓ ^ 10 by positivity); unfold Pc; linarith
  have hPc : 1 ≤ Pc X := Nat.one_le_ceil_iff.2 (by positivity)
  have hxW : (W : ℝ) ≤ x / ℓ ^ 10 := by rw [le_div_iff₀ hL10p]; linarith
  have hQ1 : (Qc X : ℝ) ≤ x / ℓ ^ 10 := Nat.floor_le (by positivity)
  have hQ2 : x / ℓ ^ 10 < (Qc X : ℝ) + 1 := Nat.lt_floor_add_one _
  have hQc : 1 ≤ Qc X := Nat.le_floor (by push_cast; linarith)
  have hQX : Qc X ≤ X := by
    have : (Qc X : ℝ) ≤ (X : ℝ) := hQ1.trans (div_le_self hx0.le hL10)
    exact_mod_cast this
  have hWQ : (W : ℝ) ≤ Qc X + 1 := by linarith
  have he4 : Real.exp 4 ≤ x := by rw [← hxe]; exact Real.exp_le_exp.2 hℓ4
  have hWP : ((W * Pc X : ℕ) : ℝ) ≤ ℓ ^ (11 : ℝ) := by
    rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    calc (W : ℝ) * Pc X ≤ W * (2 * ℓ ^ 10) := by gcongr
      _ = (2 * W) * ℓ ^ 10 := by ring
      _ ≤ ℓ * ℓ ^ 10 := by gcongr
      _ = ℓ ^ 11 := by ring
  -- the minor arc bound
  have hMb : (W : ℝ) * Mb X (Pc X) (Qc X) ≤ δ * x := by
    unfold Mb
    have hl5 : 0 < ℓ ^ 5 := by positivity
    have hsP : ℓ ^ 5 ≤ Real.sqrt (Pc X) :=
      (Real.le_sqrt hl5.le (Nat.cast_nonneg _)).2 (by rw [← pow_mul]; exact hP1)
    have hA1 : x / Real.sqrt (Pc X) ≤ x / ℓ ^ 5 := div_le_div_of_nonneg_left hx0.le hl5 hsP
    have hA2 : Real.sqrt (x * Qc X) ≤ x / ℓ ^ 5 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      calc x * Qc X ≤ x * (x / ℓ ^ 10) := by gcongr
        _ = (x / ℓ ^ 5) ^ 2 := by field_simp
    have hW0 : (0 : ℝ) ≤ W := by positivity
    have hA3 : (1 + ℓ) ^ 4 ≤ 16 * ℓ ^ 4 := by
      calc (1 + ℓ) ^ 4 ≤ (2 * ℓ) ^ 4 := by gcongr; linarith
        _ = 16 * ℓ ^ 4 := by ring
    have hB' : 9600 * W * ℓ ^ 4 ≤ δ * x ^ ((1 : ℝ) / 5) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at hB; linarith
    have hx45 : x ^ ((4 : ℝ) / 5) * x ^ ((1 : ℝ) / 5) = x := by
      rw [← Real.rpow_add hx0]; norm_num
    have hx45p : 0 ≤ x ^ ((4 : ℝ) / 5) := by positivity
    have hstep : (W : ℝ) * (300 * (x / Real.sqrt (Pc X) + x ^ ((4 : ℝ) / 5) +
        Real.sqrt (x * Qc X)) * (1 + ℓ) ^ 4) ≤
        W * (300 * (2 * (x / ℓ ^ 5) + x ^ ((4 : ℝ) / 5)) * (16 * ℓ ^ 4)) := by
      apply mul_le_mul_of_nonneg_left _ hW0
      apply mul_le_mul _ hA3 (by positivity) (by positivity)
      linarith
    have he1 : (W : ℝ) * (300 * (2 * (x / ℓ ^ 5) + x ^ ((4 : ℝ) / 5)) * (16 * ℓ ^ 4)) =
        9600 * W * x / ℓ + 4800 * (x ^ ((4 : ℝ) / 5) * (W * ℓ ^ 4)) := by
      field_simp; ring
    have h1 : 9600 * W * x / ℓ ≤ δ * x / 2 := by
      rw [div_le_iff₀ hℓ0]
      rw [div_le_iff₀ hδ] at hℓa
      have := mul_le_mul_of_nonneg_left hℓa (show 0 ≤ x / 2 by positivity)
      linarith
    have h2 : 4800 * (x ^ ((4 : ℝ) / 5) * (W * ℓ ^ 4)) ≤ δ * x / 2 := by
      have : x ^ ((4 : ℝ) / 5) * (9600 * W * ℓ ^ 4) ≤
          x ^ ((4 : ℝ) / 5) * (δ * x ^ ((1 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left hB' hx45p
      have e : x ^ ((4 : ℝ) / 5) * (δ * x ^ ((1 : ℝ) / 5)) = δ * x := by
        rw [mul_left_comm, hx45]
      have e2 : 4800 * (x ^ ((4 : ℝ) / 5) * (W * ℓ ^ 4)) =
          x ^ ((4 : ℝ) / 5) * (9600 * W * ℓ ^ 4) / 2 := by ring
      rw [e2]; linarith
    have : (W : ℝ) * (300 * (x / Real.sqrt (Pc X) + x ^ ((4 : ℝ) / 5) +
        Real.sqrt (x * Qc X)) * (1 + ℓ) ^ 4) ≤ δ * x := by
      linarith
    exact this
  -- the major arc error
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  have hWPl : ((W * Pc X : ℕ) : ℝ) ≤ 2 * W * ℓ ^ 10 := by
    push_cast
    have := mul_le_mul_of_nonneg_left hP2 (show (0 : ℝ) ≤ W by positivity)
    linarith
  have hlog : Real.log ((W * Pc X : ℕ) : ℝ) / Real.log 2 ≤ 4 * W * ℓ ^ 10 := by
    rw [div_le_iff₀ hl2p]
    have := Real.log_le_self (Nat.cast_nonneg (W * Pc X))
    have hp : 0 ≤ (W : ℝ) * ℓ ^ 10 := by positivity
    nlinarith
  have hfac : 1 + 2 * π * x / ((Qc X : ℝ) + 1) ≤ 8 * ℓ ^ 10 := by
    have hq : x / ((Qc X : ℝ) + 1) ≤ ℓ ^ 10 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hL10p] at hQ2; linarith
    have hpi := Real.pi_lt_d2
    have : 2 * π * x / ((Qc X : ℝ) + 1) = 2 * π * (x / ((Qc X : ℝ) + 1)) := by ring
    rw [this]
    have : 2 * π * (x / ((Qc X : ℝ) + 1)) ≤ 2 * π * ℓ ^ 10 := by gcongr
    nlinarith [Real.pi_pos]
  have hexp0 := (Real.exp_pos (-c' * Real.sqrt (ℓ / 2))).le
  have hT2 : ((W * Pc X : ℕ) : ℝ) * K * x * Real.exp (-c' * Real.sqrt (ℓ / 2)) ≤
      2 * W * K * K' * x / ℓ ^ 11 := by
    have hl21 : 0 < ℓ ^ 21 := by positivity
    calc ((W * Pc X : ℕ) : ℝ) * K * x * Real.exp (-c' * Real.sqrt (ℓ / 2))
        ≤ (2 * W * ℓ ^ 10) * K * x * (K' / ℓ ^ 21) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hWPl hK)
            hx0.le) hex hexp0 (by positivity)
      _ = 2 * W * K * K' * x / ℓ ^ 11 := by field_simp
  have hlogX : 0 ≤ ℓ := hℓ0.le
  have hEn : 0 ≤ Emaj W X K c' := by
    unfold Emaj
    have := Real.log_natCast_nonneg (W * Pc X)
    have : 0 ≤ ((W * Pc X : ℕ) : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
    have : 0 ≤ Real.log X := Real.log_natCast_nonneg X
    positivity
  have hE : (W : ℝ) * Emaj W X K c' ≤ δ * x := by
    unfold Emaj
    rw [← hℓdef, ← hxdef]
    have hin : 7 * Real.sqrt x + ((W * Pc X : ℕ) : ℝ) * K * x *
        Real.exp (-c' * Real.sqrt (ℓ / 2)) + Real.log ((W * Pc X : ℕ) : ℝ) / Real.log 2 * ℓ ≤
        7 * Real.sqrt x + 2 * W * K * K' * x / ℓ ^ 11 + 4 * W * ℓ ^ 11 := by
      have : Real.log ((W * Pc X : ℕ) : ℝ) / Real.log 2 * ℓ ≤ 4 * W * ℓ ^ 10 * ℓ :=
        mul_le_mul_of_nonneg_right hlog hlogX
      have e : 4 * (W : ℝ) * ℓ ^ 10 * ℓ = 4 * W * ℓ ^ 11 := by ring
      linarith
    have hin0 : 0 ≤ 7 * Real.sqrt x + ((W * Pc X : ℕ) : ℝ) * K * x *
        Real.exp (-c' * Real.sqrt (ℓ / 2)) + Real.log ((W * Pc X : ℕ) : ℝ) / Real.log 2 * ℓ := by
      have := Real.log_natCast_nonneg (W * Pc X)
      have : 0 ≤ ((W * Pc X : ℕ) : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
      positivity
    have hfac0 : 0 ≤ 1 + 2 * π * x / ((Qc X : ℝ) + 1) := by positivity
    have hstep : (W : ℝ) * ((7 * Real.sqrt x + ((W * Pc X : ℕ) : ℝ) * K * x *
        Real.exp (-c' * Real.sqrt (ℓ / 2)) + Real.log ((W * Pc X : ℕ) : ℝ) / Real.log 2 * ℓ) *
        (1 + 2 * π * x / ((Qc X : ℝ) + 1))) ≤
        W * ((7 * Real.sqrt x + 2 * W * K * K' * x / ℓ ^ 11 + 4 * W * ℓ ^ 11) * (8 * ℓ ^ 10)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hin hfac hfac0 (by positivity)
    have he : (W : ℝ) * ((7 * Real.sqrt x + 2 * W * K * K' * x / ℓ ^ 11 + 4 * W * ℓ ^ 11) *
        (8 * ℓ ^ 10)) = 56 * W * ℓ ^ 10 * Real.sqrt x + 16 * W ^ 2 * K * K' * x / ℓ +
        32 * W ^ 2 * ℓ ^ 21 := by field_simp; ring
    have h1 : 56 * (W : ℝ) * ℓ ^ 10 * Real.sqrt x ≤ δ * x / 3 := by
      have hC' : 168 * W * ℓ ^ 10 ≤ δ * Real.sqrt x := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at hC; linarith
      have hs := Real.mul_self_sqrt hx0.le
      have hs0 := Real.sqrt_nonneg x
      have hm := mul_le_mul_of_nonneg_right hC' hs0
      calc 56 * (W : ℝ) * ℓ ^ 10 * Real.sqrt x = (168 * W * ℓ ^ 10 * Real.sqrt x) / 3 := by ring
        _ ≤ (δ * Real.sqrt x * Real.sqrt x) / 3 := by linarith
        _ = δ * x / 3 := by rw [mul_assoc, hs]
    have h2 : 16 * (W : ℝ) ^ 2 * K * K' * x / ℓ ≤ δ * x / 3 := by
      rw [div_le_iff₀ hℓ0]
      rw [div_le_iff₀ hδ] at hℓb
      have hm := mul_le_mul_of_nonneg_right hℓb hx0.le
      linarith
    have h3 : 32 * (W : ℝ) ^ 2 * ℓ ^ 21 ≤ δ * x / 3 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at hD; linarith only [hD]
    linarith only [hstep, he, h1, h2, h3]
  exact ⟨hPc, hQc, hQX, hWQ, he4, hWP, hMb, hEn, hE⟩

/-- `C (log x)^r ≤ x^s` eventually, from Mathlib's `isLittleO_log_rpow_rpow_atTop`. -/
theorem ev_logpow (r : ℕ) {s : ℝ} (hs : 0 < s) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ r ≤ x ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop (r : ℝ) hs).bound (show (0 : ℝ) < 1 / C by positivity)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.rpow_natCast] at hx
  calc C * Real.log x ^ r ≤ C * (1 / C * x ^ s) := mul_le_mul_of_nonneg_left hx hC.le
    _ = x ^ s := by field_simp

/-- **The asymptotic estimate**: for fixed `W`, once `X` is large, the levels `Pc X`, `Qc X`
satisfy every condition of `twS_explicit` and both error terms are at most `δ X`. -/
theorem asymp_exists {W : ℕ} (hW : 1 ≤ W) {δ c' K : ℝ} (hδ : 0 < δ) (hc' : 0 < c')
    (hK : 0 ≤ K) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      1 ≤ Pc X ∧ 1 ≤ Qc X ∧ Qc X ≤ X ∧ (W : ℝ) ≤ Qc X + 1 ∧ Real.exp 4 ≤ X ∧
      ((W * Pc X : ℕ) : ℝ) ≤ Real.log X ^ (11 : ℝ) ∧
      (W : ℝ) * Mb X (Pc X) (Qc X) ≤ δ * X ∧ 0 ≤ Emaj W X K c' ∧
      (W : ℝ) * Emaj W X K c' ≤ δ * X := by
  obtain ⟨K', hK', hexp⟩ :=
    LeanLab.PNTPort.BV.exp_neg_sqrt_log_le (c' / Real.sqrt 2) (by positivity) 21
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have e1 := Real.tendsto_log_atTop.eventually_ge_atTop
    (max (max (4 : ℝ) (2 * W)) (max (19200 * W / δ) (48 * W ^ 2 * K * K' / δ)))
  have e2 := ev_logpow 10 (s := 1) one_pos hWr
  have e3 := ev_logpow 4 (s := 1 / 5) (by norm_num) (show 0 < 9600 * (W : ℝ) / δ by positivity)
  have e4 := ev_logpow 10 (s := 1 / 2) (by norm_num) (show 0 < 168 * (W : ℝ) / δ by positivity)
  have e5 := ev_logpow 21 (s := 1) one_pos (show 0 < 96 * (W : ℝ) ^ 2 / δ by positivity)
  have e6 := eventually_ge_atTop (2 : ℝ)
  obtain ⟨x₀, hx₀⟩ := (e1.and (e2.and (e3.and (e4.and (e5.and e6))))).exists_forall_of_atTop
  refine ⟨⌈x₀⌉₊, fun X hX => ?_⟩
  have hxX : x₀ ≤ (X : ℝ) := Nat.ceil_le.1 hX
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx₀ X hxX
  rw [Real.rpow_one] at h2 h5
  rw [← Real.sqrt_eq_rpow] at h4
  have hex : Real.exp (-c' * Real.sqrt (Real.log X / 2)) ≤ K' / Real.log X ^ 21 := by
    have := hexp X h6
    rw [show (21 : ℝ) = ((21 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have e : -c' * Real.sqrt (Real.log X / 2) =
        -(c' / Real.sqrt 2) * Real.sqrt (Real.log X) := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]; ring
    rw [e]; exact this
  exact pointwise hW hδ hK hK' h1 h2 h3 h4 h5 hex

/-- **`ArcClassBound`, PROVED**: Green 2005 Lemma 6.2 in circle method form. -/
theorem arcClassBound : ArcClassBound := by
  intro c hc
  obtain ⟨c', hc', K, hK, hmaj⟩ := LeanLab.PNTPort.Vinogradov.major_arc 11 (by norm_num)
  refine ⟨max 2 (⌈4 / c⌉₊ + 1), fun z hz b hb hcop => ?_⟩
  have hz2 : 2 ≤ z := le_of_max_le_left hz
  have hzr : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hzc : 4 / c ≤ z := by
    have h1 := Nat.le_ceil (4 / c)
    have h2 : ((⌈4 / c⌉₊ + 1 : ℕ) : ℝ) ≤ z := by exact_mod_cast le_of_max_le_right hz
    push_cast at h2; linarith
  have hW2 : 2 ≤ primorial z := two_le_primorial hz2
  have hW1 : 1 ≤ primorial z := by omega
  obtain ⟨X₀, hX₀⟩ := asymp_exists (W := primorial z) hW1 (δ := c / 4) (by positivity) hc' hK
  refine ⟨max X₀ (⌈4 / c⌉₊ + 1), fun N hNp hN r hr hrN => ?_⟩
  have hN1 : 1 ≤ N := hNp.one_lt.le
  have hb1 : 1 ≤ b := one_le_b hW2 hcop
  have hNX : N ≤ Xc (primorial z) b N := by
    have : 1 * (N - 1) ≤ primorial z * (N - 1) := Nat.mul_le_mul_right _ hW1
    unfold Xc; omega
  have hNc : 4 / c ≤ (N : ℝ) := by
    have h1 := Nat.le_ceil (4 / c)
    have h2 : ((⌈4 / c⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
    push_cast at h2; linarith
  obtain ⟨hP1, hQ1, hQX, hWQ, he4, hWP, hMb, hEn, hE⟩ :=
    hX₀ (Xc (primorial z) b N) (le_trans (le_of_max_le_left hN) hNX)
  have hmaj' : ∀ (a : ℤ) (q : ℕ), 1 ≤ q → q ≤ primorial z * Pc (Xc (primorial z) b N) →
      IsCoprime a (q : ℤ) → ∀ β : ℝ, |β| ≤ 1 / ((Qc (Xc (primorial z) b N) : ℝ) + 1) →
        ‖SV (Xc (primorial z) b N) (a / q + β) - gμ q * VV (Xc (primorial z) b N) β‖ ≤
          Emaj (primorial z) (Xc (primorial z) b N) K c' := by
    intro a q hq hqP hcop' β hβ
    have hqr : (q : ℝ) ≤ ((primorial z * Pc (Xc (primorial z) b N) : ℕ) : ℝ) := by
      exact_mod_cast hqP
    exact (hmaj _ he4 q hq (hqr.trans hWP) a hcop' β).trans (major_err_le hK hq hqr hβ)
  have hT := twS_explicit (by omega) hb hcop hr hrN hP1 hQ1 hQX hWQ hEn hmaj'
  -- the arithmetic
  set W := primorial z
  set X := Xc W b N
  have hW : 0 < W := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hφ : (0 : ℝ) < Nat.totient W := by exact_mod_cast Nat.totient_pos.2 hW
  have hφW := totient_le_real W
  have hXle : (X : ℝ) ≤ W * N := Xc_le hb hN1
  have hA1 : (1 : ℝ) ≤ (W : ℝ) / Nat.totient W := by rw [le_div_iff₀ hφ]; linarith
  have hA0 : (0 : ℝ) ≤ (W : ℝ) / Nat.totient W := by linarith
  have hTe : (W : ℝ) ^ 2 * N / Nat.totient W = (W : ℝ) / Nat.totient W * (W * N) := by ring
  have hz' : (1 : ℝ) / z ≤ c / 4 := by
    rw [div_le_iff₀ hzr]; rw [div_le_iff₀ hc] at hzc; linarith
  have hN' : (1 : ℝ) ≤ c / 4 * N := by
    rw [div_le_iff₀ hc] at hNc; linarith
  have ha : c / 4 * (X : ℝ) ≤ c / 4 * ((W : ℝ) / Nat.totient W * (W * N)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (X : ℝ) ≤ W * N := hXle
      _ ≤ (W : ℝ) / Nat.totient W * (W * N) := le_mul_of_one_le_left (by positivity) hA1
  have hbb : (W : ℝ) / Nat.totient W * ((X : ℝ) / z) ≤
      c / 4 * ((W : ℝ) / Nat.totient W * (W * N)) := by
    have e : (W : ℝ) / Nat.totient W * ((X : ℝ) / z) =
        (W : ℝ) / Nat.totient W * X * (1 / z) := by ring
    rw [e]
    have := mul_le_mul (mul_le_mul_of_nonneg_left hXle hA0) hz' (by positivity) (by positivity)
    linarith
  have hcc : (W : ℝ) / Nat.totient W * W ≤ c / 4 * ((W : ℝ) / Nat.totient W * (W * N)) := by
    have := le_mul_of_one_le_right (show 0 ≤ (W : ℝ) / Nat.totient W * W by positivity) hN'
    linarith
  have hsplit : (W : ℝ) / Nat.totient W * ((X : ℝ) / z + W) =
      (W : ℝ) / Nat.totient W * ((X : ℝ) / z) + (W : ℝ) / Nat.totient W * W := by ring
  rw [hTe]
  have hT' : ‖twS W b N r‖ ≤ W * Mb X (Pc X) (Qc X) +
      (W : ℝ) / Nat.totient W * ((X : ℝ) / z + W) + W * Emaj W X K c' := hT
  linarith

/-- **Green 2005 Lemma 6.2 in the Alsetri-Shao regime, PROVED**, via the equivalence of U-1478. -/
theorem green62 : LeanLab.DensityGoldbach.U1446.Green62 := green62_of_arcs arcClassBound

/-- **Alsetri-Shao Theorem 1.2**, CONDITIONAL ON `GreenThm21Circle3` only. -/
theorem alsetriShao_1_2_U1484 (H21 : LeanLab.DensityGoldbach.U1472.GreenThm21Circle3) :
    AlsetriShao12 :=
  alsetriShao_1_2_U1478 H21 arcClassBound

/-- Vacuity of the level conditions: at `W = 1`, `δ = 1` some `X` meets all of them, so
`twS_explicit` is applied on a nonempty range. -/
theorem vacuity_levels : ∃ X : ℕ, 1 ≤ Pc X ∧ 1 ≤ Qc X ∧ Qc X ≤ X ∧ Real.exp 4 ≤ X := by
  obtain ⟨X₀, h⟩ := asymp_exists (W := 1) le_rfl (δ := 1) (c' := 1) (K := 0) one_pos one_pos le_rfl
  obtain ⟨h1, h2, h3, -, h5, -⟩ := h X₀ le_rfl
  exact ⟨X₀, h1, h2, h3, h5⟩

end LeanLab.DensityGoldbach.U1484

