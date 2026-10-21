module

public import LeanLab.PNTPort.Selberg.CramerDiscrete

/-!
# Cramér's mean square under RH, partial sums

Lab proof, unit U-6116, CLOUD 20261020T0618Z-cloud36, T2 toward P0058 Lemma 1 for small `ξ`.
AI wrote this file. CONDITIONAL ON RiemannHypothesis only, through `cramer_discrete`.
Known mathematics, Cramér 1921.

* `cramer_sum`: **under RH**, there is `K` with `Σ_{m < X} (ψ(m) − m)² ≤ K X²` for every natural `X`.

Proof: strong induction, the block `X/7 ≤ m < X` from `cramer_discrete` with `U = log(X/7) + 1`,
and Chebyshev's `ψ(m) ≪ m` for `X < 120`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Finset

lemma psi_sub_sq_le : ∃ c : ℝ, 0 ≤ c ∧ ∀ m : ℕ, (Chebyshev.psi m - m) ^ 2 ≤ c * (m : ℝ) ^ 2 := by
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ c0 * x :=
    ⟨_, fun x hx => Chebyshev.psi_le_const_mul_self hx⟩
  refine ⟨(|c0| + 1) ^ 2, by positivity, fun m => ?_⟩
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 := hc0 m hm
  have h0 : 0 ≤ Chebyshev.psi (m : ℝ) := Chebyshev.psi_nonneg _
  have hc : c0 ≤ |c0| := le_abs_self c0
  have hb : |Chebyshev.psi (m : ℝ) - m| ≤ (|c0| + 1) * m := by
    rw [abs_le]; constructor <;> nlinarith
  calc (Chebyshev.psi m - m) ^ 2 = |Chebyshev.psi (m : ℝ) - m| ^ 2 := (sq_abs _).symm
    _ ≤ ((|c0| + 1) * m) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = (|c0| + 1) ^ 2 * (m : ℝ) ^ 2 := by ring

set_option maxHeartbeats 1000000 in
/-- **Cramér's mean square under RH, partial sums.** -/
theorem cramer_sum (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ X : ℕ, ∑ m ∈ range X, (Chebyshev.psi m - m) ^ 2 ≤ K * (X : ℝ) ^ 2 := by
  obtain ⟨C, hC, hd⟩ := cramer_discrete hRH
  obtain ⟨c, hc, hpt⟩ := psi_sub_sq_le
  have he2 : Real.exp 2 ≤ 8 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [e]; nlinarith [Real.exp_pos 1]
  set K := 120 * c + 8 * C
  refine ⟨K, by positivity, fun X => ?_⟩
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    rcases lt_or_ge X 120 with hX | hX
    · -- small `X`
      have : ∑ m ∈ range X, (Chebyshev.psi m - m) ^ 2 ≤ ∑ m ∈ range X, c * (X : ℝ) ^ 2 := by
        refine sum_le_sum fun m hm => (hpt m).trans ?_
        apply mul_le_mul_of_nonneg_left _ hc
        have : (m : ℝ) ≤ X := by exact_mod_cast (mem_range.mp hm).le
        exact pow_le_pow_left₀ (Nat.cast_nonneg m) this 2
      rw [sum_const, card_range, nsmul_eq_mul] at this
      have hX' : (X : ℝ) ≤ 120 := by exact_mod_cast hX.le
      have : (X : ℝ) * (c * (X : ℝ) ^ 2) ≤ 120 * c * (X : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hX' (show 0 ≤ c * (X : ℝ) ^ 2 by positivity)
        linarith
      have : 120 * c * (X : ℝ) ^ 2 ≤ K * (X : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); simp only [K]; linarith
      linarith
    · -- the block `X/7 ≤ m < X`
      set a := X / 7 with ha
      have ha1 : 1 ≤ a := by omega
      have haX : a < X := by omega
      have har : (1 : ℝ) ≤ a := by exact_mod_cast ha1
      have h7 : 7 * a ≤ X := Nat.mul_div_le X 7
      have h7' : X < 7 * a + 7 := by omega
      set U := Real.log a + 1 with hU
      have hU0 : 0 ≤ U := by have := Real.log_nonneg har; linarith
      have hlo : Real.exp (U - 1) ≤ a := by
        rw [hU, show Real.log a + 1 - 1 = Real.log a by ring, Real.exp_log (by linarith)]
      have hhi : (X : ℝ) ≤ Real.exp (U + 1) := by
        rw [hU, show Real.log a + 1 + 1 = Real.log a + 2 by ring, Real.exp_add,
          Real.exp_log (by linarith)]
        have h2 : (7.38 : ℝ) ≤ Real.exp 2 := by
          have h := Real.exp_one_gt_d9
          have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          rw [e]; nlinarith
        have hX7 : (X : ℝ) ≤ 7 * a + 6 := by exact_mod_cast (by omega : X ≤ 7 * a + 6)
        have hX120 : (120 : ℝ) ≤ X := by exact_mod_cast hX
        nlinarith
      have hblock := hd U hU0 a X hlo hhi
      have hsplit : ∑ m ∈ range X, (Chebyshev.psi m - m) ^ 2
          = ∑ m ∈ range a, (Chebyshev.psi m - m) ^ 2 + ∑ m ∈ Ico a X, (Chebyshev.psi m - m) ^ 2 := by
        rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le a) haX.le, ← range_eq_Ico]
      have hprev := ih a haX
      have hEU : Real.exp (2 * U) = Real.exp 2 * (a : ℝ) ^ 2 := by
        rw [hU, show 2 * (Real.log a + 1) = 2 + 2 * Real.log a by ring, Real.exp_add,
          show 2 * Real.log (a : ℝ) = Real.log ((a : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
          Real.exp_log (by positivity)]
      rw [hsplit]
      have h49 : 49 * (a : ℝ) ^ 2 ≤ (X : ℝ) ^ 2 := by
        have : 7 * (a : ℝ) ≤ X := by exact_mod_cast h7
        nlinarith
      have hK0 : 0 ≤ K := by positivity
      calc ∑ m ∈ range a, (Chebyshev.psi m - m) ^ 2 + ∑ m ∈ Ico a X, (Chebyshev.psi m - m) ^ 2
          ≤ K * (a : ℝ) ^ 2 + C * (Real.exp 2 * (a : ℝ) ^ 2) := by
            have hb2 := hblock; rw [hEU] at hb2; linarith
        _ ≤ K * (a : ℝ) ^ 2 + 8 * C * (a : ℝ) ^ 2 := by
            have := mul_le_mul_of_nonneg_right he2 (show 0 ≤ C * (a : ℝ) ^ 2 by positivity)
            nlinarith
        _ ≤ K * (X : ℝ) ^ 2 := by
            have : 8 * C ≤ K := by simp only [K]; linarith
            nlinarith [sq_nonneg (a : ℝ)]

end LeanLab.PNTPort.Selberg

