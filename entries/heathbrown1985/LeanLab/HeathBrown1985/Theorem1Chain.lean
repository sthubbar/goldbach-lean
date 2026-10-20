module

public import Mathlib
public import LeanLab.HeathBrown1985.PrimePowers
public import LeanLab.HeathBrown1985.Sigma1

/-!
P0096 Heath-Brown 1985, pages 56 to 58, the end of section 3 and section 4: Theorem 1 from
the bound for Σ₃ on page 56 and the main term on page 57.
STATED: `BoundSigma3`, page 56, `Σ₃² ≪ x⁴ L¹³ Q⁻¹`; `MainTerm4`, page 57, the asymptotic 4.1
combined with the case `t = 2` of 2.2, `Σ_m |Σ_{n ≤ x} Λ_Q(n) Λ(m - n) - x 𝔖(m)| ≪ x² L⁴ Q⁻¹`.
PROVED here: 3.9, `Σ ≪ x² Q^{-1/2} L⁸`, from 3.2, the Σ₂ bound and `BoundSigma3`;
`theorem1_of`, Theorem 1 from `BoundSigma3`, `MainTerm4` and Siegel-Walfisz 1.1, with
`B = 2C + 16` and the prime power error from PrimePowers.lean.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- Page 56: `Σ₃² ≪ x⁴ L¹³ Q⁻¹` for `Q = L^B`. Stated, cited. -/
def BoundSigma3 : Prop :=
  ∀ B : ℝ, 0 < B → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    Sigma3 x (Real.log x ^ B) ^ 2 ≤ K * x ^ 4 * Real.log x ^ 13 / Real.log x ^ B

/-- Page 57: the asymptotic 4.1 for `Σ_{n ≤ x} Λ_Q(n) Λ(m - n)` combined with the case `t = 2`
of 2.2, summed over `2x < m ≤ 3x`: `≪ x² L⁴ Q⁻¹` for `Q = L^B`. Stated, cited. -/
def MainTerm4 : Prop :=
  ∀ B : ℝ, 0 < B → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∑ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ (Real.log x ^ B) n * Λ (m - n) - x * singular m|
      ≤ K * x ^ 2 * Real.log x ^ 4 / Real.log x ^ B

/-- 3.9: `Σ ≪ x² Q^{-1/2} L⁸` for `Q = L^B`. -/
def Bound3_9 : Prop :=
  ∀ B : ℝ, 0 < B → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    Sigma x (Real.log x ^ B) ≤ K * x ^ 2 * (Real.log x ^ B) ^ (-(1 : ℝ) / 2) * Real.log x ^ 8

/-- The trivial bound `Σ ≤ 3x · x (Q³ + L) log 3x`. -/
theorem sigma_crude (x Q : ℝ) (hx : 1 ≤ x) (hQ : 0 ≤ Q) :
    Sigma x Q ≤ 3 * x * (x * (Q ^ 3 + Real.log x) * Real.log (3 * x)) := by
  have hx0 : 0 < x := by linarith
  have hl3 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hper : ∀ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, DeltaQ Q n * Λ (m - n)| ≤
      x * (Q ^ 3 + Real.log x) * Real.log (3 * x) := by
    intro m hm
    simp only [mRange, mem_filter, mem_Icc] at hm
    have hmR : (m : ℝ) ≤ 3 * x :=
      le_trans (by exact_mod_cast hm.1.2) (Nat.floor_le (by linarith))
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hpt : ∀ n ∈ Icc 1 ⌊x⌋₊, |DeltaQ Q n * Λ (m - n)| ≤
        (Q ^ 3 + Real.log x) * Real.log (3 * x) := by
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      have hnR : (n : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Icc.mp hn).2) (Nat.floor_le hx0.le)
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have h1 : |DeltaQ Q n| ≤ Q ^ 3 + Real.log x :=
        (abs_DeltaQ_le_cube_log Q hQ n).trans
          (by gcongr)
      have h2 : Λ (m - n) ≤ Real.log (3 * x) := vonMangoldt_le_log_of_le _ _ (by linarith)
        (le_trans (by exact_mod_cast Nat.sub_le m n) hmR)
      exact mul_le_mul h1 h2 ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    refine (sum_le_sum hpt).trans ?_
    rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le hx0.le)
      (by positivity)) hl3
  unfold Sigma
  refine (sum_le_sum hper).trans ?_
  rw [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (card_mRange_le x hx0.le) (by positivity)

/-- **3.9 from 3.2, the Σ₂ bound and the Σ₃ bound**, via `Σ ≤ Σ₁ + Σ₂ + Σ₃`. -/
theorem bound3_9_of (h1 : Bound3_2) (h2 : BoundSigma2) (h3 : BoundSigma3) : Bound3_9 := by
  intro B hB
  obtain ⟨K1, hK1⟩ := h1 B hB
  obtain ⟨K2, hK2⟩ := h2 B hB
  obtain ⟨K3, hK3⟩ := h3 B hB
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  set S0 := (l2 ^ B) ^ (-(1 : ℝ) / 2)
  have hS0 : 0 < S0 := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hl2 _) _
  set c := Real.sqrt (|K3| / l2 ^ 3)
  set Km := |K1| * S0 / l2 ^ 2 + |K2| + c
  refine ⟨max Km (18 / l2 ^ 8), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set L := Real.log x
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := by linarith
  set Q := L ^ B
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hL0 _
  set s := Q ^ (-(1 : ℝ) / 2)
  have hs0 : 0 < s := Real.rpow_pos_of_pos hQ0 _
  set P := x ^ 2 * s * L ^ 8
  have hP0 : 0 < P := by positivity
  have eR : max Km (18 / l2 ^ 8) * x ^ 2 * s * L ^ 8 = max Km (18 / l2 ^ 8) * P := by ring
  rw [eR]
  have hSig0 : 0 ≤ Sigma x Q := sum_nonneg (fun _ _ => abs_nonneg _)
  rcases lt_or_ge Q 1 with hQ1 | hQ1
  · -- small `x`: `Q < 1`, so `L < 1` and `s ≥ 1`
    have hL1 : L < 1 := by
      by_contra h
      exact absurd (Real.one_le_rpow (not_lt.mp h) hB.le) (not_le.mpr hQ1)
    have hs1 : 1 ≤ s := by
      have := Real.rpow_le_rpow_of_nonpos hQ0 hQ1.le (by norm_num : -(1 : ℝ) / 2 ≤ 0)
      rwa [Real.one_rpow] at this
    have hcr := sigma_crude x Q (by linarith) hQ0.le
    have hl3 : Real.log (3 * x) ≤ 3 := by
      rw [Real.log_mul (by norm_num) hx0.ne']
      have : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    have hQ3 : Q ^ 3 ≤ 1 := pow_le_one₀ hQ0.le hQ1.le
    have hl30 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
    have hsm : Sigma x Q ≤ 18 * x ^ 2 := by
      refine hcr.trans ?_
      have : (Q ^ 3 + L) * Real.log (3 * x) ≤ 2 * 3 :=
        mul_le_mul (by linarith) hl3 hl30 (by norm_num)
      nlinarith
    have hL8 : l2 ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ hl2.le hL2 8
    have hP : 18 * x ^ 2 ≤ 18 / l2 ^ 8 * P := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : x ^ 2 * l2 ^ 8 ≤ x ^ 2 * s * L ^ 8 := by
        calc x ^ 2 * l2 ^ 8 = x ^ 2 * 1 * l2 ^ 8 := by ring
          _ ≤ x ^ 2 * s * L ^ 8 := by gcongr
      simp only [P]; linarith
    exact hsm.trans (hP.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hP0.le))
  · have hsplit := Sigma_le_sum x Q (by linarith) hQ1
    have hQinv : Q⁻¹ = s * s := by
      rw [← Real.rpow_add hQ0, show -(1 : ℝ) / 2 + -(1 : ℝ) / 2 = -1 by norm_num,
        Real.rpow_neg_one]
    have hsS : s ≤ S0 :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hl2 _)
        (Real.rpow_le_rpow hl2.le hL2 hB.le) (by norm_num)
    -- Σ₁
    have hS1 : Sigma1 x Q ≤ |K1| * S0 / l2 ^ 2 * P := by
      have a := hK1 x hx
      have a0 : 0 ≤ x ^ 2 * L ^ 6 / Q := by positivity
      have b : x ^ 2 * L ^ 6 / Q ≤ S0 / l2 ^ 2 * P := by
        rw [div_eq_mul_inv, hQinv, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have hL6 : L ^ 6 * l2 ^ 2 ≤ L ^ 8 := by
          have : l2 ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hl2.le hL2 2
          calc L ^ 6 * l2 ^ 2 ≤ L ^ 6 * L ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
            _ = L ^ 8 := by ring
        have := mul_le_mul hL6 hsS hs0.le (by positivity)
        have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ x ^ 2 * s)
        calc x ^ 2 * L ^ 6 * (s * s) * l2 ^ 2 = x ^ 2 * s * (L ^ 6 * l2 ^ 2 * s) := by ring
          _ ≤ x ^ 2 * s * (L ^ 8 * S0) := this
          _ = S0 * P := by simp only [P]; ring
      calc Sigma1 x Q ≤ K1 * x ^ 2 * L ^ 6 / Q := a
        _ = K1 * (x ^ 2 * L ^ 6 / Q) := by ring
        _ ≤ |K1| * (x ^ 2 * L ^ 6 / Q) := mul_le_mul_of_nonneg_right (le_abs_self _) a0
        _ ≤ |K1| * (S0 / l2 ^ 2 * P) := mul_le_mul_of_nonneg_left b (abs_nonneg _)
        _ = _ := by ring
    -- Σ₂
    have hS2 : Sigma2 x Q ≤ |K2| * P := by
      have a := hK2 x hx
      calc Sigma2 x Q ≤ K2 * x ^ 2 * s * L ^ 8 := a
        _ = K2 * P := by simp only [P]; ring
        _ ≤ |K2| * P := mul_le_mul_of_nonneg_right (le_abs_self _) hP0.le
    -- Σ₃
    have hS3 : Sigma3 x Q ≤ c * P := by
      have a := hK3 x hx
      have h30 : 0 ≤ Sigma3 x Q := sum_nonneg (fun _ _ => abs_nonneg _)
      have hc2 : c ^ 2 = |K3| / l2 ^ 3 := Real.sq_sqrt (by positivity)
      have hsq : Sigma3 x Q ^ 2 ≤ (c * P) ^ 2 := by
        refine a.trans ?_
        have hL13 : L ^ 13 * l2 ^ 3 ≤ L ^ 16 := by
          have : l2 ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hl2.le hL2 3
          calc L ^ 13 * l2 ^ 3 ≤ L ^ 13 * L ^ 3 := mul_le_mul_of_nonneg_left this (by positivity)
            _ = L ^ 16 := by ring
        rw [mul_pow, hc2, div_eq_mul_inv _ Q, hQinv]
        have e : (|K3| / l2 ^ 3) * P ^ 2 = |K3| * (x ^ 4 * L ^ 16 * (s * s)) / l2 ^ 3 := by
          simp only [P]; ring
        rw [e, le_div_iff₀ (by positivity)]
        have hss : 0 ≤ x ^ 4 * (s * s) := by positivity
        have := mul_le_mul_of_nonneg_left hL13 hss
        calc K3 * x ^ 4 * L ^ 13 * (s * s) * l2 ^ 3 = K3 * (x ^ 4 * (s * s) * (L ^ 13 * l2 ^ 3)) := by
              ring
          _ ≤ |K3| * (x ^ 4 * (s * s) * (L ^ 13 * l2 ^ 3)) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          _ ≤ |K3| * (x ^ 4 * (s * s) * L ^ 16) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
          _ = _ := by ring
      have hcP : 0 ≤ c * P := mul_nonneg (Real.sqrt_nonneg _) hP0.le
      nlinarith
    calc Sigma x Q ≤ Sigma1 x Q + Sigma2 x Q + Sigma3 x Q := hsplit
      _ ≤ |K1| * S0 / l2 ^ 2 * P + |K2| * P + c * P := by linarith
      _ = Km * P := by simp only [Km]; ring
      _ ≤ max Km (18 / l2 ^ 8) * P := mul_le_mul_of_nonneg_right (le_max_left _ _) hP0.le

/-- `L^a ≪_a √x` for `x ≥ 2`. -/
theorem log_rpow_le_sqrt (a : ℝ) (ha : 0 ≤ a) : ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    Real.log x ^ a ≤ K * Real.sqrt x := by
  have ev := (isLittleO_log_rpow_rpow_atTop a (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp ev
  set X := max X0 2
  have hX2 : (2 : ℝ) ≤ X := le_max_right _ _
  refine ⟨1 + Real.log X ^ a, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsx : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hLX0 : 0 ≤ Real.log X ^ a := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  rcases le_or_gt x X with h | h
  · have : Real.log x ^ a ≤ Real.log X ^ a :=
      Real.rpow_le_rpow hL0 (Real.log_le_log hx0 h) ha
    nlinarith
  · have hb := hX0 x (le_trans (le_max_left _ _) h.le)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL0 _),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul, ← Real.sqrt_eq_rpow] at hb
    nlinarith

/-- For `L ≥ l > 0` and `a ≤ b`, `L^a ≤ l^{a-b} L^b`. -/
theorem rpow_le_of_ge {l L : ℝ} (hl : 0 < l) (hlL : l ≤ L) {a b : ℝ} (hab : a ≤ b) :
    L ^ a ≤ l ^ (a - b) * L ^ b := by
  have hL : 0 < L := lt_of_lt_of_le hl hlL
  have e : L ^ a = L ^ (a - b) * L ^ b := by rw [← Real.rpow_add hL]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hl hlL (by linarith)) (Real.rpow_nonneg hL.le _)

/-- The `m`-range of Theorem 1 is `mRange x`. -/
theorem theorem1_range_eq (x : ℝ) (hx : 0 ≤ x) :
    (range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ)) = mRange x := by
  ext m
  simp only [mRange, mem_filter, mem_range, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have : 0 < m := by
      have : (0 : ℝ) < m := by linarith
      exact_mod_cast this
    exact ⟨⟨by omega, by omega⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩
    exact ⟨by omega, h2⟩

/-- The pointwise decomposition `N₂ - x𝔖 = (Σ Λ_Q Λ - x𝔖) - Σ Δ_Q Λ - (Σ Λ Λ - N₂)`. -/
theorem abs_N2_sub_le (x Q : ℝ) (m : ℕ) :
    |N2 x m - x * singular m| ≤
      |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n) - x * singular m| +
      |∑ n ∈ Icc 1 ⌊x⌋₊, DeltaQ Q n * Λ (m - n)| +
      |∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * Λ (m - n) - N2 x m| := by
  have e : ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * Λ (m - n) =
      ∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n) - ∑ n ∈ Icc 1 ⌊x⌋₊, DeltaQ Q n * Λ (m - n) := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro n _; unfold DeltaQ; ring
  set A := ∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n)
  set D := ∑ n ∈ Icc 1 ⌊x⌋₊, DeltaQ Q n * Λ (m - n)
  set E := ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * Λ (m - n)
  have : N2 x m - x * singular m = (A - x * singular m) - D - (E - N2 x m) := by rw [e]; ring
  rw [this]
  calc |A - x * singular m - D - (E - N2 x m)| ≤ |A - x * singular m - D| + |E - N2 x m| :=
        abs_sub _ _
    _ ≤ |A - x * singular m| + |D| + |E - N2 x m| := by
        have := abs_sub (A - x * singular m) D
        linarith

/-- **Theorem 1 from 3.9 and the main term**, with `B = 2C + 16`. -/
theorem theorem1_of_bound3_9 (h9 : Bound3_9) (h4 : MainTerm4) : Theorem1 := by
  intro C hC
  set B := 2 * C + 16 with hBdef
  have hB : 0 < B := by positivity
  obtain ⟨K4, hK4⟩ := h4 B hB
  obtain ⟨K9, hK9⟩ := h9 B hB
  obtain ⟨KP, hKP⟩ := log_rpow_le_sqrt (3 + C) (by linarith)
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  refine ⟨|K4| * l2 ^ ((4 - B) - -C) + |K9| + 1296 * KP, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set L := Real.log x
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx
  have hL0 : 0 < L := by linarith
  set T := x ^ 2 * L ^ (-C)
  have hT0 : 0 < T := by positivity
  rw [theorem1_range_eq x hx0.le]
  have hsum := sum_le_sum (fun m (_ : m ∈ mRange x) => abs_N2_sub_le x (L ^ B) m)
  rw [sum_add_distrib, sum_add_distrib] at hsum
  -- the main term
  have hM : ∑ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ (L ^ B) n * Λ (m - n) - x * singular m|
      ≤ |K4| * l2 ^ ((4 - B) - -C) * T := by
    refine (hK4 x hx).trans ?_
    have e : L ^ 4 / L ^ B = L ^ (4 - B) := by
      rw [Real.rpow_sub hL0, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h := rpow_le_of_ge hl2 hL2 (show 4 - B ≤ -C by rw [hBdef]; linarith)
    have hp : 0 ≤ x ^ 2 * L ^ (4 - B) := by positivity
    calc K4 * x ^ 2 * L ^ 4 / L ^ B = K4 * (x ^ 2 * L ^ (4 - B)) := by rw [← e]; ring
      _ ≤ |K4| * (x ^ 2 * L ^ (4 - B)) := mul_le_mul_of_nonneg_right (le_abs_self _) hp
      _ ≤ |K4| * (x ^ 2 * (l2 ^ ((4 - B) - -C) * L ^ (-C))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by positivity)) (abs_nonneg _)
      _ = _ := by simp only [T]; ring
  -- Σ, by 3.9
  have hS : Sigma x (L ^ B) ≤ |K9| * T := by
    refine (hK9 x hx).trans ?_
    have e : (L ^ B) ^ (-(1 : ℝ) / 2) * L ^ 8 = L ^ (-C) := by
      rw [← Real.rpow_mul hL0.le, ← Real.rpow_natCast L 8, ← Real.rpow_add hL0]
      congr 1; rw [hBdef]; push_cast; ring
    have hp : 0 ≤ x ^ 2 * L ^ (-C) := by positivity
    calc K9 * x ^ 2 * (L ^ B) ^ (-(1 : ℝ) / 2) * L ^ 8
        = K9 * (x ^ 2 * ((L ^ B) ^ (-(1 : ℝ) / 2) * L ^ 8)) := by ring
      _ = K9 * T := by rw [e]
      _ ≤ |K9| * T := mul_le_mul_of_nonneg_right (le_abs_self _) hT0.le
  -- prime powers
  have hP : ∑ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * Λ (m - n) - N2 x m| ≤ 1296 * KP * T := by
    refine (sum_ppErr_le x hx).trans ?_
    have e : L ^ 3 = L ^ (3 + C) * L ^ (-C) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_natCast L 3]
      congr 1; push_cast; ring
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have h := hKP x hx
    have hp : 0 ≤ x * Real.sqrt x * L ^ (-C) := by positivity
    calc 1296 * x * Real.sqrt x * L ^ 3 = 1296 * (x * Real.sqrt x * L ^ (-C)) * L ^ (3 + C) := by
          rw [e]; ring
      _ ≤ 1296 * (x * Real.sqrt x * L ^ (-C)) * (KP * Real.sqrt x) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 1296 * KP * (x ^ 2 * L ^ (-C)) := by
          rw [show x ^ 2 = Real.sqrt x * Real.sqrt x * x by rw [hsq]; ring]; ring
  have hSig : ∑ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, DeltaQ (L ^ B) n * Λ (m - n)| =
      Sigma x (L ^ B) := rfl
  rw [hSig] at hsum
  calc _ ≤ _ := hsum
    _ ≤ |K4| * l2 ^ ((4 - B) - -C) * T + |K9| * T + 1296 * KP * T := by linarith
    _ = _ := by simp only [T]; ring

/-- **Theorem 1 from the Σ₃ bound, the main term and Siegel-Walfisz.** -/
theorem theorem1_of (h3 : BoundSigma3) (h4 : MainTerm4) (hSW : SiegelWalfisz) : Theorem1 :=
  theorem1_of_bound3_9
    (bound3_9_of (bound3_2_of_siegelWalfisz hSW) (boundSigma2_of_siegelWalfisz hSW) h3) h4

/-- The same, under the name used for the cited form. -/
theorem theorem1_of_cited (h3 : BoundSigma3) (h4 : MainTerm4) (hSW : SiegelWalfisz) :
    Theorem1 :=
  theorem1_of h3 h4 hSW

end LeanLab.HeathBrown1985
