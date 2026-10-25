module

public import LeanLab.DensityGoldbach.U1484Final

/-!
Unit U-1502, run 20261023T1343Z-19109. P0047 Alsetri and Shao 2024, Theorem 1.2.

Circle method levels with a power of log saving, a variant of `U1484.pointwise` and
`U1484.asymp_exists`: `P = ⌈(log X)^20⌉`, `Q = ⌊X/(log X)^20⌋`. For fixed `W`, once `X` is large,
the minor arc bound and the uniform major arc error, both multiplied by `W`, are at most
`X/(log X)^3`, and every modulus `q ≤ W P` is at most `(log X)^21`, the range of the lab's
`major_arc` at `A = 21`.

Known mathematics, no cited input. AI-written Lean code, Claude, 2026-10-23. Checked only by
the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real Filter
noncomputable section
namespace LeanLab.DensityGoldbach.U1502

open LeanLab.DensityGoldbach.U1478 LeanLab.DensityGoldbach.U1481 LeanLab.DensityGoldbach.U1484

/-- The major arc level `P = ⌈(log X)^20⌉`. -/
def P2 (X : ℕ) : ℕ := ⌈Real.log X ^ 20⌉₊

/-- The minor arc level `Q = ⌊X/(log X)^20⌋`. -/
def Q2 (X : ℕ) : ℕ := ⌊(X : ℝ) / Real.log X ^ 20⌋₊

/-- The uniform major arc error for moduli `q ≤ W P` and `|β| ≤ 1/(Q + 1)`. -/
def Emaj2 (W X : ℕ) (K c' : ℝ) : ℝ :=
  (7 * Real.sqrt X + ((W * P2 X : ℕ) : ℝ) * K * X * Real.exp (-c' * Real.sqrt (Real.log X / 2)) +
    Real.log ((W * P2 X : ℕ) : ℝ) / Real.log 2 * Real.log X) *
    (1 + 2 * π * X / ((Q2 X : ℝ) + 1))

theorem major_err_le2 {W X q : ℕ} {K c' β : ℝ} (hK : 0 ≤ K) (hq : 1 ≤ q)
    (hqP : (q : ℝ) ≤ ((W * P2 X : ℕ) : ℝ)) (hβ : |β| ≤ 1 / ((Q2 X : ℝ) + 1)) :
    (7 * Real.sqrt X + q * K * X * Real.exp (-c' * Real.sqrt (Real.log X / 2)) +
      Real.log q / Real.log 2 * Real.log X) * (1 + 2 * π * |β| * X) ≤ Emaj2 W X K c' := by
  unfold Emaj2
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hlX := Real.log_natCast_nonneg X
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hex := (Real.exp_pos (-c' * Real.sqrt (Real.log X / 2))).le
  have h1 : (q : ℝ) * K * X * Real.exp (-c' * Real.sqrt (Real.log X / 2)) ≤
      ((W * P2 X : ℕ) : ℝ) * K * X * Real.exp (-c' * Real.sqrt (Real.log X / 2)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hqP hK) hX0) hex
  have h2 : Real.log q / Real.log 2 * Real.log X ≤
      Real.log ((W * P2 X : ℕ) : ℝ) / Real.log 2 * Real.log X :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (Real.log_le_log hq0 hqP) hl2.le) hlX
  have h3 : 1 + 2 * π * |β| * X ≤ 1 + 2 * π * X / ((Q2 X : ℝ) + 1) := by
    have : 2 * π * X / ((Q2 X : ℝ) + 1) = 2 * π * (1 / ((Q2 X : ℝ) + 1)) * X := by ring
    rw [this]; gcongr
  have hn : 0 ≤ 7 * Real.sqrt X + ((W * P2 X : ℕ) : ℝ) * K * X *
      Real.exp (-c' * Real.sqrt (Real.log X / 2)) +
      Real.log ((W * P2 X : ℕ) : ℝ) / Real.log 2 * Real.log X := by
    have := Real.log_natCast_nonneg (W * P2 X)
    have : 0 ≤ ((W * P2 X : ℕ) : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
    positivity
  exact mul_le_mul (by linarith) h3 (by positivity) hn

set_option maxHeartbeats 1600000 in
/-- **The pointwise estimate with a power of log saving.** -/
theorem pointwise2 {W X : ℕ} (hW : 1 ≤ W) {K c' K' : ℝ} (hK : 0 ≤ K) (hK' : 0 < K')
    (hℓ : max (max (4 : ℝ) (2 * W)) (max (14400 * W) (54 * W ^ 2 * K * K' + 1)) ≤ Real.log X)
    (hA : 2 * Real.log X ^ 20 ≤ X)
    (hB : Real.log X ^ 10 ≤ (X : ℝ) ^ ((1 : ℝ) / 5))
    (hC : 189 * W * Real.log X ^ 23 ≤ Real.sqrt X)
    (hD : 108 * W ^ 2 * Real.log X ^ 44 ≤ X)
    (hex : Real.exp (-c' * Real.sqrt (Real.log X / 2)) ≤ K' / Real.log X ^ 45) :
    1 ≤ P2 X ∧ 2 ≤ Q2 X ∧ Q2 X ≤ X ∧ Real.exp 4 ≤ X ∧
      ((W * P2 X : ℕ) : ℝ) ≤ Real.log X ^ (21 : ℝ) ∧
      (W : ℝ) * Mb X (P2 X) (Q2 X) ≤ X / Real.log X ^ 3 ∧ 0 ≤ Emaj2 W X K c' ∧
      (W : ℝ) * Emaj2 W X K c' ≤ X / Real.log X ^ 3 := by
  set ℓ := Real.log X with hℓdef
  set x : ℝ := (X : ℝ) with hxdef
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hℓ4 : 4 ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hℓ
  have hℓW : 2 * (W : ℝ) ≤ ℓ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hℓ
  have hℓa : 14400 * (W : ℝ) ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hℓ
  have hℓb : 54 * (W : ℝ) ^ 2 * K * K' + 1 ≤ ℓ :=
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
  have hL20 : 1 ≤ ℓ ^ 20 := one_le_pow₀ hℓ1
  have hL20p : 0 < ℓ ^ 20 := by positivity
  -- levels
  have hP1 : ℓ ^ 20 ≤ (P2 X : ℝ) := Nat.le_ceil _
  have hP2 : (P2 X : ℝ) ≤ 2 * ℓ ^ 20 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ ℓ ^ 20 by positivity); unfold P2; linarith
  have hPc : 1 ≤ P2 X := Nat.one_le_ceil_iff.2 (by positivity)
  have hQ1 : (Q2 X : ℝ) ≤ x / ℓ ^ 20 := Nat.floor_le (by positivity)
  have hQ2 : x / ℓ ^ 20 < (Q2 X : ℝ) + 1 := Nat.lt_floor_add_one _
  have hQc : 2 ≤ Q2 X := by
    apply Nat.le_floor
    rw [le_div_iff₀ hL20p]; push_cast; linarith
  have hQX : Q2 X ≤ X := by
    have : (Q2 X : ℝ) ≤ (X : ℝ) := hQ1.trans (div_le_self hx0.le hL20)
    exact_mod_cast this
  have he4 : Real.exp 4 ≤ x := by rw [← hxe]; exact Real.exp_le_exp.2 hℓ4
  have hWP : ((W * P2 X : ℕ) : ℝ) ≤ ℓ ^ (21 : ℝ) := by
    rw [show (21 : ℝ) = ((21 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    calc (W : ℝ) * P2 X ≤ W * (2 * ℓ ^ 20) := mul_le_mul_of_nonneg_left hP2 (by positivity)
      _ = 2 * W * ℓ ^ 20 := by ring
      _ ≤ ℓ * ℓ ^ 20 := mul_le_mul_of_nonneg_right hℓW (by positivity)
      _ = ℓ ^ 21 := by ring
  -- the minor arc bound
  have hsP : ℓ ^ 10 ≤ Real.sqrt (P2 X) := by
    rw [Real.le_sqrt (by positivity) (Nat.cast_nonneg _)]
    calc (ℓ ^ 10) ^ 2 = ℓ ^ 20 := by ring
      _ ≤ _ := hP1
  have hm1 : x / Real.sqrt (P2 X) ≤ x / ℓ ^ 10 :=
    div_le_div_of_nonneg_left hx0.le (by positivity) hsP
  have hm2 : x ^ ((4 : ℝ) / 5) ≤ x / ℓ ^ 10 := by
    have e : x = x ^ ((4 : ℝ) / 5) * x ^ ((1 : ℝ) / 5) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [le_div_iff₀ (by positivity)]
    calc x ^ ((4 : ℝ) / 5) * ℓ ^ 10 ≤ x ^ ((4 : ℝ) / 5) * x ^ ((1 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = x := e.symm
  have hm3 : Real.sqrt (x * Q2 X) ≤ x / ℓ ^ 10 := by
    have : x * Q2 X ≤ (x / ℓ ^ 10) ^ 2 := by
      calc x * Q2 X ≤ x * (x / ℓ ^ 20) := mul_le_mul_of_nonneg_left hQ1 hx0.le
        _ = (x / ℓ ^ 10) ^ 2 := by field_simp
    calc Real.sqrt (x * Q2 X) ≤ Real.sqrt ((x / ℓ ^ 10) ^ 2) := Real.sqrt_le_sqrt this
      _ = x / ℓ ^ 10 := Real.sqrt_sq (by positivity)
  have hl4 : (1 + ℓ) ^ 4 ≤ 16 * ℓ ^ 4 := by
    have : 1 + ℓ ≤ 2 * ℓ := by linarith
    calc (1 + ℓ) ^ 4 ≤ (2 * ℓ) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
      _ = 16 * ℓ ^ 4 := by ring
  have hMb : (W : ℝ) * Mb X (P2 X) (Q2 X) ≤ x / ℓ ^ 3 := by
    unfold Mb
    have hsum : x / Real.sqrt (P2 X) + x ^ ((4 : ℝ) / 5) + Real.sqrt (x * Q2 X) ≤ 3 * (x / ℓ ^ 10) := by
      linarith
    have h0 : 0 ≤ x / Real.sqrt (P2 X) + x ^ ((4 : ℝ) / 5) + Real.sqrt (x * Q2 X) := by positivity
    have h1 : (W : ℝ) * (300 * (x / Real.sqrt (P2 X) + x ^ ((4 : ℝ) / 5) + Real.sqrt (x * Q2 X)) *
        (1 + ℓ) ^ 4) ≤ W * (300 * (3 * (x / ℓ ^ 10)) * (16 * ℓ ^ 4)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsum (by norm_num)) hl4 (by positivity)
        (by positivity)
    have h2 : (W : ℝ) * (300 * (3 * (x / ℓ ^ 10)) * (16 * ℓ ^ 4)) = 14400 * W * (x / ℓ ^ 6) := by
      field_simp <;> ring
    have h3 : 14400 * (W : ℝ) * (x / ℓ ^ 6) ≤ x / ℓ ^ 3 := by
      have hℓ3 : 14400 * (W : ℝ) ≤ ℓ ^ 3 := by
        have : ℓ ≤ ℓ ^ 3 := by
          calc ℓ = ℓ * 1 := by ring
            _ ≤ ℓ * ℓ ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hℓ1) hℓ0.le
            _ = ℓ ^ 3 := by ring
        linarith
      rw [show x / ℓ ^ 3 = ℓ ^ 3 * (x / ℓ ^ 6) by field_simp <;> ring]
      exact mul_le_mul_of_nonneg_right hℓ3 (by positivity)
    rw [hxdef] at h1 h2 h3 ⊢
    linarith
  -- the major arc error
  have hF : 1 + 2 * π * x / ((Q2 X : ℝ) + 1) ≤ 9 * ℓ ^ 20 := by
    have hQp : (0 : ℝ) < (Q2 X : ℝ) + 1 := by positivity
    have h1 : x / ((Q2 X : ℝ) + 1) ≤ ℓ ^ 20 := by
      rw [div_le_iff₀ hQp]
      rw [div_lt_iff₀ hL20p] at hQ2; nlinarith
    have h2 : 2 * π * x / ((Q2 X : ℝ) + 1) = 2 * π * (x / ((Q2 X : ℝ) + 1)) := by ring
    rw [h2]
    have := Real.pi_le_four
    have hy0 : 0 ≤ x / ((Q2 X : ℝ) + 1) := by positivity
    nlinarith
  have hWPr : ((W * P2 X : ℕ) : ℝ) ≤ 2 * W * ℓ ^ 20 := by
    push_cast; nlinarith
  have hWP1 : (1 : ℝ) ≤ ((W * P2 X : ℕ) : ℝ) := by
    push_cast; nlinarith [(show (1 : ℝ) ≤ P2 X by exact_mod_cast hPc)]
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogWP : Real.log ((W * P2 X : ℕ) : ℝ) / Real.log 2 * ℓ ≤ 4 * W * ℓ ^ 21 := by
    have h1 : Real.log ((W * P2 X : ℕ) : ℝ) ≤ ((W * P2 X : ℕ) : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((W * P2 X : ℕ) : ℝ) by linarith)
      linarith
    have hlw0 : 0 ≤ Real.log ((W * P2 X : ℕ) : ℝ) := Real.log_nonneg hWP1
    have h2 : Real.log ((W * P2 X : ℕ) : ℝ) / Real.log 2 ≤ 2 * Real.log ((W * P2 X : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc Real.log ((W * P2 X : ℕ) : ℝ) / Real.log 2 * ℓ ≤ 2 * Real.log ((W * P2 X : ℕ) : ℝ) * ℓ :=
          mul_le_mul_of_nonneg_right h2 hℓ0.le
      _ ≤ 2 * (2 * W * ℓ ^ 20) * ℓ := by
          apply mul_le_mul_of_nonneg_right _ hℓ0.le; linarith
      _ = 4 * W * ℓ ^ 21 := by ring
  have hexp0 := (Real.exp_pos (-c' * Real.sqrt (ℓ / 2))).le
  have hterm2 : ((W * P2 X : ℕ) : ℝ) * K * x * Real.exp (-c' * Real.sqrt (ℓ / 2)) ≤
      2 * W * K * K' * x / ℓ ^ 25 := by
    have hL45 : 0 < ℓ ^ 45 := by positivity
    calc ((W * P2 X : ℕ) : ℝ) * K * x * Real.exp (-c' * Real.sqrt (ℓ / 2))
        ≤ (2 * W * ℓ ^ 20) * K * x * (K' / ℓ ^ 45) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hWPr hK)
            hx0.le) hex hexp0 (by positivity)
      _ = 2 * W * K * K' * x / ℓ ^ 25 := by field_simp <;> ring
  have hinner : 0 ≤ 7 * Real.sqrt x + ((W * P2 X : ℕ) : ℝ) * K * x *
      Real.exp (-c' * Real.sqrt (ℓ / 2)) + Real.log ((W * P2 X : ℕ) : ℝ) / Real.log 2 * ℓ := by
    have := Real.log_nonneg hWP1
    have : 0 ≤ ((W * P2 X : ℕ) : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
    have : 0 < Real.log 2 := by linarith
    positivity
  have hEn : 0 ≤ Emaj2 W X K c' := by
    unfold Emaj2
    rw [← hℓdef, ← hxdef]
    exact mul_nonneg hinner (by positivity)
  have hE : (W : ℝ) * Emaj2 W X K c' ≤ x / ℓ ^ 3 := by
    unfold Emaj2
    rw [← hℓdef, ← hxdef]
    have hb1 : 7 * Real.sqrt x + ((W * P2 X : ℕ) : ℝ) * K * x * Real.exp (-c' * Real.sqrt (ℓ / 2)) +
        Real.log ((W * P2 X : ℕ) : ℝ) / Real.log 2 * ℓ ≤
        7 * Real.sqrt x + 2 * W * K * K' * x / ℓ ^ 25 + 4 * W * ℓ ^ 21 := by linarith
    have hstep : (W : ℝ) * ((7 * Real.sqrt x + ((W * P2 X : ℕ) : ℝ) * K * x *
        Real.exp (-c' * Real.sqrt (ℓ / 2)) + Real.log ((W * P2 X : ℕ) : ℝ) / Real.log 2 * ℓ) *
        (1 + 2 * π * x / ((Q2 X : ℝ) + 1))) ≤
        W * ((7 * Real.sqrt x + 2 * W * K * K' * x / ℓ ^ 25 + 4 * W * ℓ ^ 21) * (9 * ℓ ^ 20)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hb1 hF (by positivity) (by positivity)
    have e : (W : ℝ) * ((7 * Real.sqrt x + 2 * W * K * K' * x / ℓ ^ 25 + 4 * W * ℓ ^ 21) *
        (9 * ℓ ^ 20)) = 63 * W * ℓ ^ 20 * Real.sqrt x + 18 * W ^ 2 * K * K' * x / ℓ ^ 5 +
          36 * W ^ 2 * ℓ ^ 41 := by
      field_simp <;> ring
    -- three pieces, each at most a third
    have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hsx0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have p1 : 63 * W * ℓ ^ 20 * Real.sqrt x ≤ x / (3 * ℓ ^ 3) := by
      rw [le_div_iff₀ (by positivity)]
      have : 189 * W * ℓ ^ 23 * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hC hsx0
      nlinarith
    have p2 : 18 * (W : ℝ) ^ 2 * K * K' * x / ℓ ^ 5 ≤ x / (3 * ℓ ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hb : 54 * (W : ℝ) ^ 2 * K * K' ≤ ℓ ^ 2 := by nlinarith
      have : 18 * (W : ℝ) ^ 2 * K * K' * x * (3 * ℓ ^ 3) = (54 * W ^ 2 * K * K') * (x * ℓ ^ 3) := by
        ring
      rw [this]
      have : x * ℓ ^ 5 = ℓ ^ 2 * (x * ℓ ^ 3) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hb (by positivity)
    have p3 : 36 * (W : ℝ) ^ 2 * ℓ ^ 41 ≤ x / (3 * ℓ ^ 3) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have : x / (3 * ℓ ^ 3) + x / (3 * ℓ ^ 3) + x / (3 * ℓ ^ 3) = x / ℓ ^ 3 := by field_simp <;> ring
    linarith
  exact ⟨hPc, hQc, hQX, he4, hWP, hMb, hEn, hE⟩

/-- **The asymptotic estimate with a power of log saving.** -/
theorem asymp2 {W : ℕ} (hW : 1 ≤ W) {c' K : ℝ} (hc' : 0 < c') (hK : 0 ≤ K) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      1 ≤ P2 X ∧ 2 ≤ Q2 X ∧ Q2 X ≤ X ∧ Real.exp 4 ≤ X ∧
      ((W * P2 X : ℕ) : ℝ) ≤ Real.log X ^ (21 : ℝ) ∧
      (W : ℝ) * Mb X (P2 X) (Q2 X) ≤ X / Real.log X ^ 3 ∧ 0 ≤ Emaj2 W X K c' ∧
      (W : ℝ) * Emaj2 W X K c' ≤ X / Real.log X ^ 3 := by
  obtain ⟨K', hK', hexp⟩ :=
    LeanLab.PNTPort.BV.exp_neg_sqrt_log_le (c' / Real.sqrt 2) (by positivity) 45
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have e1 := Real.tendsto_log_atTop.eventually_ge_atTop
    (max (max (4 : ℝ) (2 * W)) (max (14400 * W) (54 * W ^ 2 * K * K' + 1)))
  have e2 := ev_logpow 20 (s := 1) one_pos (show (0 : ℝ) < 2 by norm_num)
  have e3 := ev_logpow 10 (s := 1 / 5) (by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have e4 := ev_logpow 23 (s := 1 / 2) (by norm_num) (show 0 < 189 * (W : ℝ) by positivity)
  have e5 := ev_logpow 44 (s := 1) one_pos (show 0 < 108 * (W : ℝ) ^ 2 by positivity)
  have e6 := eventually_ge_atTop (2 : ℝ)
  obtain ⟨x₀, hx₀⟩ := (e1.and (e2.and (e3.and (e4.and (e5.and e6))))).exists_forall_of_atTop
  refine ⟨⌈x₀⌉₊, fun X hX => ?_⟩
  have hxX : x₀ ≤ (X : ℝ) := Nat.ceil_le.1 hX
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx₀ X hxX
  rw [Real.rpow_one] at h2 h5
  rw [one_mul] at h3
  rw [← Real.sqrt_eq_rpow] at h4
  have hex : Real.exp (-c' * Real.sqrt (Real.log X / 2)) ≤ K' / Real.log X ^ 45 := by
    have := hexp X h6
    rw [show (45 : ℝ) = ((45 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have e : -c' * Real.sqrt (Real.log X / 2) =
        -(c' / Real.sqrt 2) * Real.sqrt (Real.log X) := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]; ring
    rw [e]; exact this
  exact pointwise2 hW hK hK' h1 h2 h3 h4 h5 hex

end LeanLab.DensityGoldbach.U1502
