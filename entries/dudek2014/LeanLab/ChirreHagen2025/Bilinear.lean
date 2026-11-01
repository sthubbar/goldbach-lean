module

public import Mathlib
public import LeanLab.ChirreHagen2025.Weighted

/-!
T2, unit U-5027, from P0075 Chirre-Hagen 2025, after Goldston 1990's bilinear form of the pairing.
With `A(t) = θ((1+δ)t) - θ(t) = δ t + E(t)`, no Goldbach number in `(x, x + δ x]` forces
`A(t) A(x - t) = 0` for `2 ≤ t ≤ x - 2`. Multiplying out with the tent weight `ψ(t) = 2t/x`:
`ψ δ² t (x - t) + δ ψ (x - t) E(t) + δ ψ t E(x - t) = - ψ E(t) E(x - t) ≤ (E(t)² + ψ² E(x - t)²)/2`.
Integrated over `[x/16, x/2]`, the main term is `δ² x³ · 0.0519`, the two cross terms cancel
to `O(δ² x² · sup |θ(u) - u|)` after the substitution `u = (1+δ) t`, and the right side is
bounded by Theorem 3 at the 17 scales through `abelSum_mono` with weights `2 (1 - s_j)²`.
Result: under RH, via Theorem 3, the `4 · 10^18` even check and `|θ(u) - u| ≤ u/10^5` for
`u ≥ 10^16` (from Schoenfeld 1976 under RH, or unconditionally from Broadbent, Kadiri, Lumley, Ng, Wilk, Math. Comp. 90 2021, Table 14, row log X₀ = 35), a Goldbach number
lies in `(x, x + 12 log² x)` for every `x ≥ 2`. Constant: 16 steps give `11.72`, the
continuous weight `4.4 · 2.5571 ≈ 11.25`. Binary Goldbach is open; this is conditional.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025
open Real Chebyshev

/-- The error in `θ` over `(t, (1+δ) t]`. -/
noncomputable def Eθ (δ t : ℝ) : ℝ := θ ((1 + δ) * t) - θ t - δ * t

/-- `θ(u) - u`. -/
noncomputable def Rθ (u : ℝ) : ℝ := θ u - u

theorem Eθ_eq (δ t : ℝ) : Eθ δ t = Rθ ((1 + δ) * t) - Rθ t := by unfold Eθ Rθ; ring

theorem F_eq_Eθ (δ t : ℝ) : F δ t = Eθ δ t ^ 2 := rfl

theorem Rθ_ii (a b : ℝ) : IntervalIntegrable Rθ MeasureTheory.volume a b :=
  (theta_mono.intervalIntegrable).sub (continuous_id.intervalIntegrable a b)

theorem Rθk_ii {k : ℝ} (hk : 0 < k) (a b : ℝ) :
    IntervalIntegrable (fun t => Rθ (k * t)) MeasureTheory.volume a b := by
  have hm : Monotone fun t => θ (k * t) := fun u v huv => theta_mono (by nlinarith)
  exact (hm.intervalIntegrable).sub ((continuous_const.mul continuous_id).intervalIntegrable a b)

theorem Eθ_ii {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    IntervalIntegrable (Eθ δ) MeasureTheory.volume a b := by
  have e : Eθ δ = fun t => Rθ ((1 + δ) * t) - Rθ t := funext (Eθ_eq δ)
  rw [e]
  exact (Rθk_ii (by linarith) a b).sub (Rθ_ii a b)

/-- A sup bound on an interval integral with ordered ends. -/
theorem abs_integral_le {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (h : ∀ u, a ≤ u → u ≤ b → |f u| ≤ C) : |∫ u in a..b, f u| ≤ C * (b - a) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := C) (f := f)
    (fun u hu => by
      rw [Set.uIoc_of_le hab] at hu
      rw [Real.norm_eq_abs]; exact h u hu.1.le hu.2)
  rw [Real.norm_eq_abs] at this
  rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at this

/-- The cross term cancels: `∫_α^β g E` is small, by `u = (1+δ) t`. -/
theorem cross_bound {g : ℝ → ℝ} (hg : Continuous g) {α β δ ρ D Gm : ℝ} (hδ : 0 < δ)
    (hα : 0 < α) (hαβ : (1 + δ) * α ≤ β)
    (hρ : ∀ u, α ≤ u → u ≤ (1 + δ) * β → |Rθ u| ≤ ρ)
    (hD : ∀ u, (1 + δ) * α ≤ u → u ≤ β → |g (u / (1 + δ)) / (1 + δ) - g u| ≤ D)
    (hG1 : ∀ u, α ≤ u → u ≤ (1 + δ) * α → |g u| ≤ Gm)
    (hG2 : ∀ u, β ≤ u → u ≤ (1 + δ) * β → |g (u / (1 + δ)) / (1 + δ)| ≤ Gm) :
    |∫ t in α..β, g t * Eθ δ t| ≤ D * ρ * (β - α) + Gm * ρ * (δ * β) + Gm * ρ * (δ * α) := by
  have hk : 0 < 1 + δ := by linarith
  have hkα : α ≤ (1 + δ) * α := by nlinarith
  have hβ : 0 < β := by nlinarith
  have hkβ : β ≤ (1 + δ) * β := by nlinarith
  have hc1 : Continuous fun u => g (u / (1 + δ)) / (1 + δ) :=
    (hg.comp (continuous_id.div_const _)).div_const _
  have i1 : ∀ a b, IntervalIntegrable (fun u => g (u / (1 + δ)) / (1 + δ) * Rθ u)
      MeasureTheory.volume a b := fun a b => (Rθ_ii a b).continuousOn_mul hc1.continuousOn
  have i2 : ∀ a b, IntervalIntegrable (fun u => g u * Rθ u) MeasureTheory.volume a b :=
    fun a b => (Rθ_ii a b).continuousOn_mul hg.continuousOn
  have i3 : IntervalIntegrable (fun t => g t * Rθ ((1 + δ) * t)) MeasureTheory.volume α β :=
    (Rθk_ii hk α β).continuousOn_mul hg.continuousOn
  have hsub0 := intervalIntegral.integral_comp_mul_left (fun u => g (u / (1 + δ)) * Rθ u)
    (ne_of_gt hk) (a := α) (b := β)
  have hsub : (∫ t in α..β, g t * Rθ ((1 + δ) * t))
      = ∫ u in (1 + δ) * α..(1 + δ) * β, g (u / (1 + δ)) / (1 + δ) * Rθ u := by
    have e1 : (∫ t in α..β, g t * Rθ ((1 + δ) * t))
        = ∫ t in α..β, g ((1 + δ) * t / (1 + δ)) * Rθ ((1 + δ) * t) :=
      intervalIntegral.integral_congr (fun t _ => by
        rw [mul_div_cancel_left₀ _ (ne_of_gt hk)])
    rw [e1]
    refine hsub0.trans ?_
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun u _ => by ring)
  have hE : (∫ t in α..β, g t * Eθ δ t)
      = (∫ t in α..β, g t * Rθ ((1 + δ) * t)) - ∫ t in α..β, g t * Rθ t :=
    (intervalIntegral.integral_congr (fun t _ => by simp only [Eθ_eq]; ring)).trans
      (intervalIntegral.integral_sub i3 (i2 α β))
  have s1 : (∫ u in (1 + δ) * α..β, g (u / (1 + δ)) / (1 + δ) * Rθ u)
      + (∫ u in β..(1 + δ) * β, g (u / (1 + δ)) / (1 + δ) * Rθ u)
      = ∫ u in (1 + δ) * α..(1 + δ) * β, g (u / (1 + δ)) / (1 + δ) * Rθ u :=
    intervalIntegral.integral_add_adjacent_intervals (i1 _ _) (i1 _ _)
  have s2 : (∫ u in α..(1 + δ) * α, g u * Rθ u) + (∫ u in (1 + δ) * α..β, g u * Rθ u)
      = ∫ u in α..β, g u * Rθ u :=
    intervalIntegral.integral_add_adjacent_intervals (i2 _ _) (i2 _ _)
  have hdiff : (∫ u in (1 + δ) * α..β, (g (u / (1 + δ)) / (1 + δ) - g u) * Rθ u)
      = (∫ u in (1 + δ) * α..β, g (u / (1 + δ)) / (1 + δ) * Rθ u)
        - ∫ u in (1 + δ) * α..β, g u * Rθ u :=
    (intervalIntegral.integral_congr (fun u _ => by ring)).trans
      (intervalIntegral.integral_sub (i1 _ _) (i2 _ _))
  have eq : (∫ t in α..β, g t * Eθ δ t)
      = (∫ u in (1 + δ) * α..β, (g (u / (1 + δ)) / (1 + δ) - g u) * Rθ u)
        + (∫ u in β..(1 + δ) * β, g (u / (1 + δ)) / (1 + δ) * Rθ u)
        - ∫ u in α..(1 + δ) * α, g u * Rθ u := by
    rw [hE, hsub, hdiff]; linarith [s1, s2]
  rw [eq]
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg _) (hρ α le_rfl (by linarith))
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD β hαβ le_rfl)
  have b1 : |∫ u in (1 + δ) * α..β, (g (u / (1 + δ)) / (1 + δ) - g u) * Rθ u|
      ≤ D * ρ * (β - (1 + δ) * α) := by
    apply abs_integral_le hαβ
    intro u hu1 hu2
    rw [abs_mul]
    have := hD u hu1 hu2
    exact mul_le_mul this (hρ u (by linarith) (by linarith)) (abs_nonneg _) hD0
  have b2 : |∫ u in β..(1 + δ) * β, g (u / (1 + δ)) / (1 + δ) * Rθ u|
      ≤ Gm * ρ * ((1 + δ) * β - β) := by
    apply abs_integral_le hkβ
    intro u hu1 hu2
    rw [abs_mul]
    have := hG2 u hu1 hu2
    exact mul_le_mul this (hρ u (by linarith) hu2) (abs_nonneg _) (le_trans (abs_nonneg _) this)
  have b3 : |∫ u in α..(1 + δ) * α, g u * Rθ u| ≤ Gm * ρ * ((1 + δ) * α - α) := by
    apply abs_integral_le hkα
    intro u hu1 hu2
    rw [abs_mul]
    have := hG1 u hu1 hu2
    exact mul_le_mul this (hρ u hu1 (by linarith)) (abs_nonneg _) (le_trans (abs_nonneg _) this)
  have e1 : (1 + δ) * β - β = δ * β := by ring
  have e2 : (1 + δ) * α - α = δ * α := by ring
  rw [e1] at b2; rw [e2] at b3
  have b1' : D * ρ * (β - (1 + δ) * α) ≤ D * ρ * (β - α) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hD0 hρ0)
  have t1 := abs_sub ((∫ u in (1 + δ) * α..β, (g (u / (1 + δ)) / (1 + δ) - g u) * Rθ u)
      + (∫ u in β..(1 + δ) * β, g (u / (1 + δ)) / (1 + δ) * Rθ u))
    (∫ u in α..(1 + δ) * α, g u * Rθ u)
  have t2 := abs_add_le (∫ u in (1 + δ) * α..β, (g (u / (1 + δ)) / (1 + δ) - g u) * Rθ u)
    (∫ u in β..(1 + δ) * β, g (u / (1 + δ)) / (1 + δ) * Rθ u)
  linarith

/-- The bilinear pointwise inequality. -/
theorem pointwise_bil {x h δ t : ℝ} (hδ : 0 < δ) (hδh : δ * x ≤ h) (ht2 : 2 ≤ t)
    (htx : 2 ≤ x - t)
    (hno : ¬ ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + h) (tw : ℝ) (htw : 0 ≤ tw) :
    tw * δ ^ 2 * t * (x - t) + δ * (tw * (x - t)) * Eθ δ t + δ * (tw * t) * Eθ δ (x - t)
      ≤ (Eθ δ t ^ 2 + tw ^ 2 * Eθ δ (x - t) ^ 2) / 2 := by
  have hle : ∀ y : ℝ, 0 ≤ y → y ≤ (1 + δ) * y := fun y hy => by nlinarith
  have hprod : (θ ((1 + δ) * t) - θ t) * (θ ((1 + δ) * (x - t)) - θ (x - t)) = 0 := by
    by_cases hS : θ ((1 + δ) * t) = θ t
    · rw [hS]; ring
    · by_cases hS' : θ ((1 + δ) * (x - t)) = θ (x - t)
      · rw [hS']; ring
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
  have e1 : θ ((1 + δ) * t) - θ t = δ * t + Eθ δ t := by unfold Eθ; ring
  have e2 : θ ((1 + δ) * (x - t)) - θ (x - t) = δ * (x - t) + Eθ δ (x - t) := by unfold Eθ; ring
  rw [e1, e2] at hprod
  have key : tw * δ ^ 2 * t * (x - t) + δ * (tw * (x - t)) * Eθ δ t + δ * (tw * t) * Eθ δ (x - t)
      = - (tw * (Eθ δ t * Eθ δ (x - t))) := by
    have : tw * ((δ * t + Eθ δ t) * (δ * (x - t) + Eθ δ (x - t))) = 0 := by rw [hprod]; ring
    linarith [this]
  rw [key]
  nlinarith [sq_nonneg (Eθ δ t + tw * Eθ δ (x - t))]

/-- `|θ(u) - u| ≤ u / 10^5` for `u ≥ 10^16`. Cited: under RH it follows from Schoenfeld 1976,
Corollary 1, `|θ(u) - u| < √u log² u / (8π)` for `u ≥ 599`; unconditionally from Broadbent et al. 2021,
Table 14, row log X₀ = 35, not from Dusart 2018, whose θ bounds that paper flags as affected. -/
def ThetaRel : Prop := ∀ u : ℝ, 10 ^ 16 ≤ u → |θ u - u| ≤ u / 10 ^ 5

/-- The step weights `2 (1 - s_j)²`. -/
noncomputable def wb (j : ℕ) : ℝ := 2 * (1 - s16 j) ^ 2

theorem wb_antitone : Antitone wb := by
  intro i j hij
  unfold wb
  have hi := s16_bounds i
  have hj := s16_bounds j
  have hm := s16_mono hij
  have : (1 - s16 j) ^ 2 ≤ (1 - s16 i) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  linarith

theorem Ub_lt : abelSum wb (fun j => s16 j ^ 2) 16 < 0.2380 := by
  simp only [abelSum, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, s16, wb]
  norm_num

/-- The two cross weights: `g₁(t) = ψ(t)(x - t)` and `g₂(u) = ψ(x - u)(x - u)`, `ψ(t) = 2t/x`. -/
noncomputable def g1f (x t : ℝ) : ℝ := 2 * t / x * (x - t)
noncomputable def g2f (x u : ℝ) : ℝ := 2 * (x - u) / x * (x - u)

theorem p_facts {δ : ℝ} (hδ : 0 < δ) :
    0 < 1 / (1 + δ) ∧ 1 / (1 + δ) ≤ 1 ∧ 1 - 1 / (1 + δ) ≤ δ ∧
    0 ≤ 1 - (1 / (1 + δ)) ^ 2 ∧ 1 - (1 / (1 + δ)) ^ 2 ≤ 2 * δ ∧
    0 ≤ 1 - (1 / (1 + δ)) ^ 3 ∧ 1 - (1 / (1 + δ)) ^ 3 ≤ 3 * δ := by
  set p := 1 / (1 + δ) with hp
  have hp0 : 0 < p := by positivity
  have hpk : p * (1 + δ) = 1 := by rw [hp]; field_simp
  have hp1 : p ≤ 1 := by nlinarith
  have hpd : 1 - p ≤ δ := by nlinarith
  have h2 : p ^ 2 ≤ 1 := pow_le_one₀ hp0.le hp1
  have h3 : p ^ 3 ≤ 1 := pow_le_one₀ hp0.le hp1
  refine ⟨hp0, hp1, hpd, by linarith, ?_, by linarith, ?_⟩
  · nlinarith
  · nlinarith

theorem g1_D {x δ u : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hu0 : 0 ≤ u) (hux : u ≤ x) :
    |g1f x (u / (1 + δ)) / (1 + δ) - g1f x u| ≤ 10 * δ * x := by
  obtain ⟨hp0, hp1, hpd, q1, q2, q3, q4⟩ := p_facts hδ
  set p := 1 / (1 + δ) with hp
  have e : g1f x (u / (1 + δ)) / (1 + δ) - g1f x u
      = -(2 * u * (1 - p ^ 2)) + 2 * (u ^ 2 / x) * (1 - p ^ 3) := by
    unfold g1f; rw [hp]; field_simp; ring
  rw [e]
  have hux2 : u ^ 2 / x ≤ x := by rw [div_le_iff₀ hx]; nlinarith
  have hu2x : 0 ≤ u ^ 2 / x := by positivity
  have a1 := mul_le_mul hux2 q4 q3 hx.le
  have a2 := mul_le_mul hux q2 q1 hx.le
  have a3 := mul_nonneg hu0 q1
  have a4 := mul_nonneg hu2x q3
  rw [abs_le]; constructor <;> nlinarith

theorem g2_D {x δ u : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hu0 : 0 ≤ u) (hux : u ≤ x) :
    |g2f x (u / (1 + δ)) / (1 + δ) - g2f x u| ≤ 16 * δ * x := by
  obtain ⟨hp0, hp1, hpd, q1, q2, q3, q4⟩ := p_facts hδ
  set p := 1 / (1 + δ) with hp
  have e : g2f x (u / (1 + δ)) / (1 + δ) - g2f x u
      = -(2 * x * (1 - p)) + 4 * u * (1 - p ^ 2) - 2 * (u ^ 2 / x) * (1 - p ^ 3) := by
    unfold g2f; rw [hp]; field_simp; ring
  rw [e]
  have q0 : 0 ≤ 1 - p := by linarith
  have hux2 : u ^ 2 / x ≤ x := by rw [div_le_iff₀ hx]; nlinarith
  have hu2x : 0 ≤ u ^ 2 / x := by positivity
  have a1 := mul_le_mul hux2 q4 q3 hx.le
  have a2 := mul_le_mul hux q2 q1 hx.le
  have a3 := mul_nonneg hu0 q1
  have a4 := mul_nonneg hu2x q3
  have a5 := mul_le_mul_of_nonneg_left hpd hx.le
  have a6 := mul_nonneg hx.le q0
  rw [abs_le]; constructor <;> nlinarith

theorem g1_abs {x t : ℝ} (hx : 0 < x) (h0 : 0 ≤ t) (h1 : t ≤ x) : |g1f x t| ≤ 2 * x := by
  unfold g1f
  have hnn : 0 ≤ 2 * t / x * (x - t) := mul_nonneg (by positivity) (by linarith)
  rw [abs_of_nonneg hnn, div_mul_eq_mul_div, div_le_iff₀ hx]; nlinarith

theorem g2_abs {x t : ℝ} (hx : 0 < x) (h0 : 0 ≤ t) (h1 : t ≤ x) : |g2f x t| ≤ 2 * x := by
  unfold g2f
  have hnn : 0 ≤ 2 * (x - t) / x * (x - t) :=
    mul_nonneg (div_nonneg (by linarith) hx.le) (by linarith)
  rw [abs_of_nonneg hnn, div_mul_eq_mul_div, div_le_iff₀ hx]; nlinarith

theorem gk_abs {x δ u c : ℝ} (hx : 0 < x) (hδ : 0 < δ) (h0 : 0 ≤ u) (hc : c ≤ x)
    (h1 : u ≤ (1 + δ) * c) (g : ℝ → ℝ) (hg : ∀ t, 0 ≤ t → t ≤ x → |g t| ≤ 2 * x) :
    |g (u / (1 + δ)) / (1 + δ)| ≤ 2 * x := by
  have hk : 0 < 1 + δ := by linarith
  have hut : u / (1 + δ) ≤ x := by rw [div_le_iff₀ hk]; nlinarith
  have := hg (u / (1 + δ)) (by positivity) hut
  rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
  nlinarith [abs_nonneg (g (u / (1 + δ)))]

/-- The bilinear inequality integrated over `[x/16, x/2]`, the second cross term reflected. -/
theorem bil_integrated {x h δ : ℝ} (hx : 32 ≤ x) (hδ : 0 < δ) (hδh : δ * x ≤ h)
    (hno : ¬ ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + h) :
    δ ^ 2 * (2 * ((x / 2) ^ 3 - (x / 16) ^ 3) / 3 - 2 / x * (((x / 2) ^ 4 - (x / 16) ^ 4) / 4))
      + δ * (∫ t in x / 16..x / 2, g1f x t * Eθ δ t)
      + δ * (∫ u in x / 2..15 * x / 16, g2f x u * Eθ δ u)
    ≤ (∫ t in x / 16..x / 2, F δ t) / 2
      + ∫ u in x / 2..15 * x / 16, 2 * ((x - u) / x) ^ 2 * F δ u := by
  have hxpos : 0 < x := by linarith
  have hab : x / 16 ≤ x / 2 := by linarith
  have iE : ∀ a b, IntervalIntegrable (Eθ δ) MeasureTheory.volume a b := Eθ_ii hδ
  have iF : ∀ c d : ℝ, 0 ≤ c → c ≤ d → IntervalIntegrable (F δ) MeasureTheory.volume c d :=
    fun c d hc hcd => integrand_intervalIntegrable hδ hc hcd
  have hψc : Continuous fun t : ℝ => 2 * t / x := (continuous_const.mul continuous_id).div_const x
  have iEr : IntervalIntegrable (fun t => Eθ δ (x - t)) MeasureTheory.volume (x / 16) (x / 2) := by
    have := (iE (x - x / 16) (x - x / 2)).comp_sub_left x
    simpa [sub_sub_cancel] using this
  have iFr : IntervalIntegrable (fun t => F δ (x - t)) MeasureTheory.volume (x / 16) (x / 2) := by
    have := (iF (x - x / 2) (x - x / 16) (by linarith) (by linarith)).symm.comp_sub_left x
    simpa [sub_sub_cancel] using this
  have hpoly : Continuous fun t : ℝ => δ ^ 2 * (2 * t ^ 2 - 2 / x * t ^ 3) := by fun_prop
  have hg1c : Continuous fun t : ℝ => δ * g1f x t := by unfold g1f; fun_prop
  have hg2c : Continuous fun t : ℝ => δ * (2 * t / x * t) := by fun_prop
  have iL1 : IntervalIntegrable (fun t => δ * g1f x t * Eθ δ t) MeasureTheory.volume
      (x / 16) (x / 2) := (iE _ _).continuousOn_mul hg1c.continuousOn
  have iL2 : IntervalIntegrable (fun t => δ * (2 * t / x * t) * Eθ δ (x - t)) MeasureTheory.volume
      (x / 16) (x / 2) := iEr.continuousOn_mul hg2c.continuousOn
  have iR1 : IntervalIntegrable (fun t => F δ t / 2) MeasureTheory.volume (x / 16) (x / 2) :=
    (iF _ _ (by positivity) hab).div_const 2
  have iR2 : IntervalIntegrable (fun t => (2 * t / x) ^ 2 * F δ (x - t) / 2) MeasureTheory.volume
      (x / 16) (x / 2) := (iFr.continuousOn_mul (hψc.pow 2).continuousOn).div_const 2
  have hint : (∫ t in x / 16..x / 2, (δ ^ 2 * (2 * t ^ 2 - 2 / x * t ^ 3)
        + δ * g1f x t * Eθ δ t + δ * (2 * t / x * t) * Eθ δ (x - t)))
      ≤ ∫ t in x / 16..x / 2, (F δ t / 2 + (2 * t / x) ^ 2 * F δ (x - t) / 2) := by
    apply intervalIntegral.integral_mono_on hab
    · exact ((hpoly.intervalIntegrable _ _).add iL1).add iL2
    · exact iR1.add iR2
    · intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hψ0 : 0 ≤ 2 * t / x := by positivity
      have := pointwise_bil (t := t) hδ hδh (by linarith [ht.1]) (by linarith [ht.2]) hno (2 * t / x) hψ0
      have e : 2 * t / x * δ ^ 2 * t * (x - t) = δ ^ 2 * (2 * t ^ 2 - 2 / x * t ^ 3) := by
        field_simp
      rw [F_eq_Eθ, F_eq_Eθ]; unfold g1f
      have e2 : δ * (2 * t / x * (x - t)) * Eθ δ t = δ * (2 * t / x * (x - t)) * Eθ δ t := rfl
      nlinarith [e]
  have sL := intervalIntegral.integral_add ((hpoly.intervalIntegrable (x / 16) (x / 2)).add iL1) iL2
  have sL' := intervalIntegral.integral_add (hpoly.intervalIntegrable (x / 16) (x / 2)) iL1
  have sR := intervalIntegral.integral_add iR1 iR2
  have hmain : (∫ t in x / 16..x / 2, δ ^ 2 * (2 * t ^ 2 - 2 / x * t ^ 3))
      = δ ^ 2 * (2 * ((x / 2) ^ 3 - (x / 16) ^ 3) / 3 - 2 / x * (((x / 2) ^ 4 - (x / 16) ^ 4) / 4)) := by
    rw [intervalIntegral.integral_const_mul]
    have : (∫ t in x / 16..x / 2, (2 * t ^ 2 - 2 / x * t ^ 3))
        = (∫ t in x / 16..x / 2, 2 * t ^ 2) - ∫ t in x / 16..x / 2, 2 / x * t ^ 3 :=
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)
    rw [this, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow]
    ring
  have hc1 : (∫ t in x / 16..x / 2, δ * g1f x t * Eθ δ t)
      = δ * ∫ t in x / 16..x / 2, g1f x t * Eθ δ t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have hc2 : (∫ t in x / 16..x / 2, δ * (2 * t / x * t) * Eθ δ (x - t))
      = δ * ∫ u in x / 2..15 * x / 16, g2f x u * Eθ δ u := by
    rw [← intervalIntegral.integral_const_mul]
    have := intervalIntegral.integral_comp_sub_left (fun u => δ * (g2f x u * Eθ δ u)) x
      (a := x / 16) (b := x / 2)
    have e1 : x - x / 2 = x / 2 := by ring
    have e2 : x - x / 16 = 15 * x / 16 := by ring
    rw [e1, e2] at this
    rw [← this]
    exact intervalIntegral.integral_congr (fun t _ => by unfold g2f; simp only [sub_sub_cancel]; ring)
  have hr1 : (∫ t in x / 16..x / 2, F δ t / 2) = (∫ t in x / 16..x / 2, F δ t) / 2 :=
    intervalIntegral.integral_div _ _
  have hr2 : (∫ t in x / 16..x / 2, (2 * t / x) ^ 2 * F δ (x - t) / 2)
      = ∫ u in x / 2..15 * x / 16, 2 * ((x - u) / x) ^ 2 * F δ u := by
    have := intervalIntegral.integral_comp_sub_left
      (fun u => 2 * ((x - u) / x) ^ 2 * F δ u) x (a := x / 16) (b := x / 2)
    have e1 : x - x / 2 = x / 2 := by ring
    have e2 : x - x / 16 = 15 * x / 16 := by ring
    rw [e1, e2] at this
    rw [← this]
    exact intervalIntegral.integral_congr (fun t _ => by simp only [sub_sub_cancel]; ring)
  rw [sL, sL', sR, hmain, hc1, hc2, hr1, hr2] at hint
  exact hint

/-- The right side is the integral of a step weight, at most the Abel sum over the scales. -/
theorem rhs_le_abel {x δ : ℝ} (hx : 32 ≤ x) (hδ : 0 < δ) :
    (∫ t in x / 16..x / 2, F δ t) / 2 + ∫ u in x / 2..15 * x / 16, 2 * ((x - u) / x) ^ 2 * F δ u
      ≤ abelSum wb (Gs δ x s16) 16 := by
  have hxpos : 0 < x := by linarith
  have iF : ∀ c d : ℝ, 0 ≤ c → c ≤ d → IntervalIntegrable (F δ) MeasureTheory.volume c d :=
    fun c d hc hcd => integrand_intervalIntegrable hδ hc hcd
  have hsb : ∀ j, 0 ≤ s16 j * x := fun j => by nlinarith [(s16_bounds j).1]
  have hsj : ∀ j, s16 j * x ≤ s16 (j + 1) * x := fun j => by
    nlinarith [s16_mono (Nat.le_succ j)]
  have hcw : Continuous fun u : ℝ => 2 * ((x - u) / x) ^ 2 := by fun_prop
  have iW : ∀ j, IntervalIntegrable (fun u => 2 * ((x - u) / x) ^ 2 * F δ u)
      MeasureTheory.volume (s16 j * x) (s16 (j + 1) * x) := fun j =>
    (iF _ _ (hsb j) (hsj j)).continuousOn_mul hcw.continuousOn
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun j => s16 j * x)
    (f := fun u => 2 * ((x - u) / x) ^ 2 * F δ u) (n := 16) (fun j _ => iW j)
  have e0 : s16 0 * x = x / 2 := by simp [s16]; ring
  have e16 : s16 16 * x = 15 * x / 16 := by simp [s16]; norm_num; ring
  simp only [e0, e16] at hsum
  have hpieces : (∫ u in x / 2..15 * x / 16, 2 * ((x - u) / x) ^ 2 * F δ u)
      ≤ ∑ j ∈ Finset.range 16, wb j * (Gs δ x s16 (j + 1) - Gs δ x s16 j) := by
    rw [← hsum]
    apply Finset.sum_le_sum
    intro j _
    have hb := s16_bounds j
    have hb1 := s16_bounds (j + 1)
    have hG : Gs δ x s16 (j + 1) - Gs δ x s16 j = ∫ u in s16 j * x..s16 (j + 1) * x, F δ u := by
      unfold Gs
      exact intervalIntegral.integral_interval_sub_left (iF 1 _ zero_le_one (by nlinarith))
        (iF 1 _ zero_le_one (by nlinarith))
    rw [hG, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (hsj j) (iW j) ((iF _ _ (hsb j) (hsj j)).const_mul _)
    intro u hu
    have hF0 : 0 ≤ F δ u := sq_nonneg _
    have h1 : (x - u) / x ≤ 1 - s16 j := by
      rw [div_le_iff₀ hxpos]; nlinarith [hu.1]
    have h0 : 0 ≤ (x - u) / x := div_nonneg (by nlinarith [hu.2]) hxpos.le
    have : ((x - u) / x) ^ 2 ≤ (1 - s16 j) ^ 2 := pow_le_pow_left₀ h0 h1 2
    unfold wb
    nlinarith
  have hR1 : (∫ t in x / 16..x / 2, F δ t) / 2 ≤ wb 0 * Gs δ x s16 0 := by
    have e : wb 0 = 1 / 2 := by simp [wb, s16]; norm_num
    rw [e]; unfold Gs; rw [e0]
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (iF 1 (x / 16) zero_le_one (by linarith)) (iF (x / 16) (x / 2) (by positivity) (by linarith))
    have h0 : 0 ≤ ∫ y in (1 : ℝ)..x / 16, F δ y :=
      intervalIntegral.integral_nonneg (by linarith) (fun y _ => sq_nonneg _)
    linarith
  unfold abelSum
  linarith

set_option maxHeartbeats 1000000 in
/-- The bilinear argument for `x ≥ 1.1 · 10^18` with `h = 11.9 log² x`. -/
theorem large12_of
    (h3 : ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jtheta x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hT : ThetaRel) :
    ∀ x : ℝ, 1.1 * 10 ^ 18 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 11.9 * Real.log x ^ 2 := by
  intro x hx
  by_contra hno
  have hL : 41 ≤ Real.log x := log_ge_41 hx
  have hxpos : 0 < x := by linarith
  set h := 11.9 * Real.log x ^ 2 with hh
  have hδpos : 0 < h / x := by positivity
  have hδle : h / x ≤ 1 / 10 ^ 13 := by
    have := threshold2 hx
    have : h / x ≤ 61.5 * Real.log x ^ 2 / x := by
      rw [hh]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
    linarith
  have hδx : h / x * x = h := by field_simp
  set δ := h / x with hδ
  have hint := bil_integrated (by linarith) hδpos hδx.le hno
  have hrhs := rhs_le_abel (x := x) (by linarith) hδpos
  -- Theorem 3 at the scales, Abel summation
  set K := 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Real.log (2.0001 / δ) ^ 2 := sq_nonneg _
    positivity
  have hGB : ∀ j, Gs δ x s16 j ≤ x ^ 2 * K * s16 j ^ 2 := by
    intro j
    have hb := s16_bounds j
    have hX : 10 ^ 13 ≤ s16 j * x := by nlinarith
    have := h3 (s16 j * x) δ hX hδpos hδle
    have e : Jtheta (s16 j * x) δ = Gs δ x s16 j := rfl
    rw [e] at this
    calc Gs δ x s16 j ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * (s16 j * x) ^ 2 := this
      _ = x ^ 2 * K * s16 j ^ 2 := by rw [hK]; ring
  have hup := abelSum_mono wb (Gs δ x s16) (fun j => x ^ 2 * K * s16 j ^ 2)
    wb_antitone (fun j => by unfold wb; positivity) hGB 16
  have hfac : abelSum wb (fun j => x ^ 2 * K * s16 j ^ 2) 16
      = x ^ 2 * K * abelSum wb (fun j => s16 j ^ 2) 16 := by
    simp only [abelSum]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hfac] at hup
  have hxK : 0 ≤ x ^ 2 * K := by positivity
  have hup2 : abelSum wb (Gs δ x s16) 16 ≤ x ^ 2 * K * 0.2380 := by
    have := mul_le_mul_of_nonneg_left Ub_lt.le hxK
    linarith
  -- the cross terms
  have hδ1 : δ ≤ 1 / 16 := by linarith
  have hδxle : δ * x ≤ x / 16 := by nlinarith
  have hA1 : (1 + δ) * (x / 16) ≤ x / 2 := by nlinarith
  have hA2 : (1 + δ) * (x / 2) ≤ 15 * x / 16 := by nlinarith
  have hA3 : (1 + δ) * (15 * x / 16) ≤ 2 * x := by nlinarith
  have hρ : ∀ u, x / 16 ≤ u → u ≤ (1 + δ) * (15 * x / 16) → |Rθ u| ≤ 2 * x / 10 ^ 5 := by
    intro u h1 h2
    have := hT u (by linarith)
    have hu2 : u ≤ 2 * x := by linarith
    unfold Rθ
    linarith [div_le_div_of_nonneg_right hu2 (by norm_num : (0 : ℝ) ≤ 10 ^ 5)]
  have hδs : δ ≤ 1 / 10 ^ 13 := hδle
  have hc1 := cross_bound (g := g1f x) (by unfold g1f; fun_prop) hδpos
    (by positivity : (0 : ℝ) < x / 16) hA1
    (fun u h1 h2 => hρ u h1 (by linarith)) (D := 10 * δ * x) (Gm := 2 * x)
    (fun u h1 h2 => g1_D hxpos hδpos (by nlinarith) (by linarith))
    (fun u h1 h2 => g1_abs hxpos (by linarith) (by linarith))
    (fun u h1 h2 => gk_abs hxpos hδpos (by linarith) (by linarith) h2 (g1f x)
      (fun t ht0 ht1 => g1_abs hxpos ht0 ht1))
  have hc2 := cross_bound (g := g2f x) (by unfold g2f; fun_prop) hδpos
    (by positivity : (0 : ℝ) < x / 2) hA2
    (fun u h1 h2 => hρ u (by linarith) h2) (D := 16 * δ * x) (Gm := 2 * x)
    (fun u h1 h2 => g2_D hxpos hδpos (by nlinarith) (by linarith))
    (fun u h1 h2 => g2_abs hxpos (by linarith) (by linarith))
    (fun u h1 h2 => gk_abs hxpos hδpos (by linarith) (by linarith) h2 (g2f x)
      (fun t ht0 ht1 => g2_abs hxpos ht0 ht1))
  have a1' := neg_abs_le (∫ t in x / 16..x / 2, g1f x t * Eθ δ t)
  have a2' := neg_abs_le (∫ u in x / 2..15 * x / 16, g2f x u * Eθ δ u)
  have b1 := mul_le_mul_of_nonneg_left hc1 hδpos.le
  have b2 := mul_le_mul_of_nonneg_left hc2 hδpos.le
  have c1 := mul_le_mul_of_nonneg_left a1' hδpos.le
  have c2 := mul_le_mul_of_nonneg_left a2' hδpos.le
  -- numerics, everything divided by δ x²
  set L := Real.log x with hLdef
  set u := Real.log (2.0001 / δ) with hu
  have hu0 : 0 ≤ u := Real.log_nonneg (by rw [le_div_iff₀ hδpos]; nlinarith)
  have huL : u ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [hδ, hh, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (2.0001 : ℝ) ≤ 11.9 * L ^ 2 := by nlinarith
    nlinarith
  have hu2 : u ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hu0 huL 2
  have hdx : δ * x = 11.9 * L ^ 2 := by rw [hδ, hh]; field_simp
  have hD : 0 < δ * x ^ 2 := by positivity
  have em : δ ^ 2 * (2 * ((x / 2) ^ 3 - (x / 16) ^ 3) / 3 - 2 / x * (((x / 2) ^ 4 - (x / 16) ^ 4) / 4))
      = (δ * x ^ 2) * (δ * x * (2 * ((1 / 2) ^ 3 - (1 / 16) ^ 3) / 3
        - 2 * (((1 / 2) ^ 4 - (1 / 16) ^ 4) / 4))) := by
    field_simp
  have ec : δ * (10 * δ * x * (2 * x / 10 ^ 5) * (x / 2 - x / 16)
        + 2 * x * (2 * x / 10 ^ 5) * (δ * (x / 2)) + 2 * x * (2 * x / 10 ^ 5) * (δ * (x / 16)))
      + δ * (16 * δ * x * (2 * x / 10 ^ 5) * (15 * x / 16 - x / 2)
        + 2 * x * (2 * x / 10 ^ 5) * (δ * (15 * x / 16)) + 2 * x * (2 * x / 10 ^ 5) * (δ * (x / 2)))
      = (δ * x ^ 2) * (δ * x * ((10 * 2 * (7 / 16) + 2 * 2 * (1 / 2) + 2 * 2 * (1 / 16)
        + 16 * 2 * (7 / 16) + 2 * 2 * (15 / 16) + 2 * 2 * (1 / 2)) / 10 ^ 5)) := by ring
  have hKx : x ^ 2 * K * 0.2380 = (δ * x ^ 2) * (2.5571 * 0.2380 * u ^ 2) := by rw [hK]; ring
  have key : (δ * x ^ 2) * (δ * x * (2 * ((1 / 2) ^ 3 - (1 / 16) ^ 3) / 3
        - 2 * (((1 / 2) ^ 4 - (1 / 16) ^ 4) / 4)))
      ≤ (δ * x ^ 2) * (2.5571 * 0.2380 * u ^ 2 + δ * x * ((10 * 2 * (7 / 16) + 2 * 2 * (1 / 2)
        + 2 * 2 * (1 / 16) + 16 * 2 * (7 / 16) + 2 * 2 * (15 / 16) + 2 * 2 * (1 / 2)) / 10 ^ 5)) := by
    rw [mul_add, ← em, ← hKx, ← ec]
    linarith only [hint, hrhs, hup2, b1, b2, c1, c2]
  have k2 := le_of_mul_le_mul_left key hD
  rw [hdx] at k2
  have hm : (2 * ((1 / 2 : ℝ) ^ 3 - (1 / 16) ^ 3) / 3 - 2 * (((1 / 2) ^ 4 - (1 / 16) ^ 4) / 4))
      = 20419 / 393216 := by norm_num
  have hc : ((10 * 2 * (7 / 16) + 2 * 2 * (1 / 2) + 2 * 2 * (1 / 16) + 16 * 2 * (7 / 16)
      + 2 * 2 * (15 / 16) + 2 * 2 * (1 / 2)) / 10 ^ 5 : ℝ) = 123 / 400000 := by norm_num
  rw [hm, hc] at k2
  have hL2 : 0 < L ^ 2 := by positivity
  have hfin : 2.5571 * 0.2380 * u ^ 2 ≤ 2.5571 * 0.2380 * L ^ 2 :=
    mul_le_mul_of_nonneg_left hu2 (by norm_num)
  linarith only [k2, hfin, hL2]

/-- U-5027: under RH, via Chirre-Hagen's Theorem 3, the `4 · 10^18` even check and the cited
`ThetaRel`, a Goldbach number lies in `(x, x + 12 log² x)` for every `x ≥ 2`. The paper has 123,
the lab's I-0010 62 and I-5001 25. -/
theorem goldbach_12
    (h3 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jtheta x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hT : ThetaRel) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 12 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 0.69 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2⟩ := small_of hE x hx hs
    exact ⟨n, hn, h1, by nlinarith⟩
  · obtain ⟨n, hn, h1, h2⟩ := large12_of (h3 hRH) hT x (by linarith)
    exact ⟨n, hn, h1, by nlinarith⟩

/-- Vacuity test for `ThetaRel`'s shape: the bound is consistent with `θ(u) = u`. -/
example : ∀ u : ℝ, 10 ^ 16 ≤ u → |u - u| ≤ u / 10 ^ 5 := fun u hu => by
  rw [sub_self, abs_zero]; positivity

end LeanLab.ChirreHagen2025

