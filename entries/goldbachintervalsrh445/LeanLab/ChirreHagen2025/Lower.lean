module

public import Mathlib
public import LeanLab.ChirreHagen2025.Statements
public import LeanLab.ChirreHagen2025.Upper
public import LeanLab.ChirreHagen2025.Reduction

/-!
P0075 Chirre-Hagen 2025, Section 5's lower bound, after Cully-Hugill and Dudek 2024 Section 4,
proved unconditionally. The argument used here pairs `t` with `x - t`: if both
`(t, (1+δ) t]` and `(x - t, (1+δ)(x - t)]` held a prime, their sum would be a Goldbach
number in `(x, x + δ x] ⊆ (x, x + h]`. So for each `t` one of the two θ-increments is zero,
and there the integrand is `δ² t²` or `δ² (x - t)² ≥ δ² t²`.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025
open Real Chebyshev

/-- θ does not move on an interval with no prime. -/
theorem theta_eq_of_noPrime {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ p : ℕ, p.Prime → a < p → (p : ℝ) ≤ b → False) : θ b = θ a := by
  rw [theta_eq_sum_Icc, theta_eq_sum_Icc]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, hp⟩, hpr⟩
    refine ⟨⟨Nat.zero_le _, ?_⟩, hpr⟩
    have hpb : (p : ℝ) ≤ b := le_trans (by exact_mod_cast hp) (Nat.floor_le (le_trans ha hab))
    have hpa : (p : ℝ) ≤ a := by
      by_contra hc
      exact h p hpr (lt_of_not_ge hc) hpb
    exact Nat.le_floor hpa
  · rintro ⟨⟨_, hp⟩, hpr⟩
    exact ⟨⟨Nat.zero_le _, le_trans hp (Nat.floor_le_floor hab)⟩, hpr⟩

theorem prime_of_theta_ne {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hne : θ b ≠ θ a) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ (p : ℝ) ≤ b := by
  by_contra hc
  push_neg at hc
  exact hne (theta_eq_of_noPrime ha hab (fun p hp h1 h2 => absurd h2 (not_le.mpr (hc p hp h1))))

/-- The integrand as a function. -/
noncomputable def F (δ : ℝ) (y : ℝ) : ℝ := (θ ((1 + δ) * y) - θ y - δ * y) ^ 2

/-- Pointwise: for `t` with `2 ≤ t ≤ x/2` and no Goldbach number in `(x, x + h]`,
`δ² t² ≤ F t + F (x - t)`. -/
theorem pointwise {x h δ t : ℝ} (hδ : 0 < δ) (hδh : δ * x ≤ h) (ht2 : 2 ≤ t) (htx : t ≤ x / 2)
    (hno : ¬ ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + h) :
    δ ^ 2 * t ^ 2 ≤ F δ t + F δ (x - t) := by
  have hF0 : ∀ y, 0 ≤ F δ y := fun y => sq_nonneg _
  have hle : ∀ y : ℝ, 0 ≤ y → y ≤ (1 + δ) * y := fun y hy => by nlinarith
  by_cases hS : θ ((1 + δ) * t) = θ t
  · have : F δ t = δ ^ 2 * t ^ 2 := by unfold F; rw [hS]; ring
    linarith [hF0 (x - t)]
  · by_cases hS' : θ ((1 + δ) * (x - t)) = θ (x - t)
    · have : F δ (x - t) = δ ^ 2 * (x - t) ^ 2 := by unfold F; rw [hS']; ring
      have : δ ^ 2 * t ^ 2 ≤ δ ^ 2 * (x - t) ^ 2 := by
        have : t ^ 2 ≤ (x - t) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left this (by positivity)
      linarith [hF0 t]
    · exfalso
      obtain ⟨p, hp, hp1, hp2⟩ := prime_of_theta_ne (by linarith) (hle t (by linarith)) hS
      obtain ⟨q, hq, hq1, hq2⟩ :=
        prime_of_theta_ne (by linarith) (hle (x - t) (by linarith)) hS'
      have hp2' : p ≠ 2 := by rintro rfl; norm_num at hp1; linarith
      have hq2' : q ≠ 2 := by rintro rfl; norm_num at hq1; linarith
      apply hno
      refine ⟨p + q, ⟨p, q, hp, hq, hp.odd_of_ne_two hp2', hq.odd_of_ne_two hq2', rfl⟩, ?_, ?_⟩
      · push_cast; linarith
      · push_cast; nlinarith

/-- Section 5's lower bound, proved. -/
theorem noGoldbachLower_proved : NoGoldbachLower := by
  intro a x h δ ha ha1 hax hx h1 hhx hδ hδ13 hδh hno
  have hx0 : 0 < x := by linarith
  have hF0 : ∀ y, 0 ≤ F δ y := fun y => sq_nonneg _
  have hJ : JthetaFrom a x δ = ∫ y in a * x..x, F δ y := rfl
  have hax_le : a * x ≤ x := by nlinarith
  have hδx : δ * x ≤ h := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * x)).mp hδh
    nlinarith
  rcases le_or_gt (1 / 2) a with hbig | hsmall
  · have h8 : 1 / 8 - a ^ 3 ≤ 0 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hbig 3
      norm_num at this ⊢; linarith
    have : 0 ≤ JthetaFrom a x δ := intervalIntegral.integral_nonneg hax_le (fun y _ => sq_nonneg _)
    have : δ ^ 2 * x ^ 3 / 3 * (1 / 8 - a ^ 3) ≤ 0 := by
      have : 0 ≤ δ ^ 2 * x ^ 3 / 3 := by positivity
      nlinarith
    linarith
  · have hax2 : a * x ≤ x / 2 := by nlinarith
    have hmid : x / 2 ≤ x - a * x := by linarith
    have iF : ∀ c d : ℝ, 0 ≤ c → c ≤ d → IntervalIntegrable (F δ) MeasureTheory.volume c d :=
      fun c d hc hcd => integrand_intervalIntegrable hδ hc hcd
    have i1 := iF (a * x) (x / 2) (by linarith) hax2
    have i2 := iF (x / 2) (x - a * x) (by linarith) hmid
    have i3 := iF (x - a * x) x (by linarith) (by linarith)
    have i2r : IntervalIntegrable (fun t => F δ (x - t)) MeasureTheory.volume (a * x) (x / 2) := by
      have := (i2.symm).comp_sub_left x
      simpa [sub_sub_cancel, show x - x / 2 = x / 2 by ring] using this
    have hsum : ∫ t in a * x..x / 2, δ ^ 2 * t ^ 2 ≤
        ∫ t in a * x..x / 2, (F δ t + F δ (x - t)) := by
      apply intervalIntegral.integral_mono_on hax2
      · exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
      · exact i1.add i2r
      · intro t ht
        exact pointwise hδ hδx (le_trans hax ht.1) ht.2 hno
    rw [intervalIntegral.integral_add i1 i2r, intervalIntegral.integral_comp_sub_left
      (fun y => F δ y) x] at hsum
    have e1 : x - x / 2 = x / 2 := by ring
    rw [e1, intervalIntegral.integral_add_adjacent_intervals i1 i2] at hsum
    have hrest : 0 ≤ ∫ y in x - a * x..x, F δ y :=
      intervalIntegral.integral_nonneg (by linarith) (fun y _ => hF0 y)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3
    have hpow : ∫ t in a * x..x / 2, δ ^ 2 * t ^ 2 = δ ^ 2 * x ^ 3 / 3 * (1 / 8 - a ^ 3) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring
    rw [hpow] at hsum
    rw [hJ, ← hsplit]
    linarith

/-- Chirre-Hagen Theorem 1 now rests only on Theorem 3 and the `4 · 10^18` even verification. -/
theorem theorem1_of_theorem3
    (h3 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jtheta x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 123 * Real.log x ^ 2 :=
  theorem1_of_inputs (section5Upper_of_RH h3) noGoldbachLower_proved hE

end LeanLab.ChirreHagen2025
