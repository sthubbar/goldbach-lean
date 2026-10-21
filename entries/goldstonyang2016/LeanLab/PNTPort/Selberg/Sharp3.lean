module

public import LeanLab.PNTPort.Selberg.Sharp2

/-!
# Sharp windows, part 3: Selberg's mean square under RH for `ψ(xe^δ) - ψ(x)`

Lab proof, unit U-5924, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, Selberg 1943 and Saffari-Vaughan 1977 in the multiplicative form;
`selberg_sharp` is CONDITIONAL ON RiemannHypothesis only, Mathlib's own definition.

`selberg_sharp`: assuming RH there is `C` such that for `0 < η ≤ δ ≤ 1` and every real `U`,
with `N(u) = e^{-u/2}(ψ(e^{u+δ}) - ψ(e^u) - (e^{u+δ} - e^u))`, `u ↦ N(u)² e^{-(u-U)²/2}` is
integrable and

  `∫ N(u)² e^{-(u-U)²/2} du ≤ C (δ (log(1/δ) + 3)² + η² e^U + η^{-5/4} e^{-2U})`.

`η` is free: with `X = e^U`, `η = √(δ/X)` makes the last two terms `δ + (X/δ)^{5/8} X^{-2}`, at most
`2δ` once `δ ≥ X^{-11/13}`. So for `X^{-11/13} ≤ δ ≤ 1` the mean of `(ψ(x e^δ) - ψ(x) - x(e^δ - 1))²/x`
near `X` is `≪ δ log²(2/δ)`, as `log(1/δ) + 3 ≍ log(2/δ)`; with `dx/x = du` and the weight at least
`e^{-1/2}` on `[X/e, eX]` this is
`∫_{X/e}^{eX} (ψ(xe^δ) - ψ(x) - x(e^δ - 1))² dx ≪ δ X² log²(2/δ)`, the Saffari-Vaughan form of
Selberg's theorem with window `x(e^δ - 1) ∈ [δx, 2δx]`, for `h = δX ≥ X^{2/13}`: a local,
restricted-range form, Saffari-Vaughan having every `δ ≥ 1/X` over all of `[1, X]`.

Route: `lo ≤ ψ(e^{u+δ}) - ψ(e^u) ≤ hi` with `hi = Qr(u+δ) - Qr(u-η)`, `lo = Qr(u+δ-η) - Qr(u)`,
the difference quotients of `ψ₁` of step `η` (`Qr_ge`, `Qr_le`); each split by `Qr_dec` into a
main part within `4ηe^u` of `e^{u+δ} - e^u`, a zero part `e^{u/2} fS d u` whose coefficients are
`m(ρ) c(ρ)` with `‖c(ρ)‖ ≤ 72 min(δ, ‖ρ‖⁻¹)`, and a remainder `≪ η^{-5/8} e^{-u/2}`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex Finset MeasureTheory Filter Topology
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.Gallagher

local notation "ζ" => riemannZeta

/-- `bq` without its multiplicity. -/
noncomputable def bq0 (η : ℝ) (ρ : ℂ) : ℂ :=
  (cexp (η * (ρ + 1)) - 1) / (((Real.exp η - 1 : ℝ) : ℂ) * (ρ * (ρ + 1)))

lemma bq_eq (η : ℝ) (ρ : ℂ) : bq η ρ = (mz ρ : ℂ) * bq0 η ρ := by
  unfold bq bq0 mz; push_cast; ring

lemma mz_ge_one {ρ : ℂ} (hρ : NZ ρ) : 1 ≤ mz ρ := by
  have hk1 : ρ ≠ 1 := by
    intro e; have := hρ.2.2; rw [e, one_re] at this; exact lt_irrefl _ this
  unfold mz; exact_mod_cast ZetaZeros.ord_pos hρ.1 hk1

lemma norm_bq0_le (hRH : RiemannHypothesis) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {ρ : ℂ}
    (hρ : NZ ρ) : ‖bq0 η ρ‖ ≤ 6 / ‖ρ‖ := by
  have h := norm_bq_le hRH hη hη1 hρ
  rw [bq_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mz_nonneg ρ)] at h
  have hm := mz_ge_one hρ
  have hp : 0 < ‖ρ‖ := norm_pos_iff.mpr (NZ_ne_zero hρ)
  rw [le_div_iff₀ hp]
  rw [le_div_iff₀ hp] at h
  nlinarith [norm_nonneg (bq0 η ρ)]

/-- Under RH the phase of `e^{(u+w)/2} e^{iγ(u+w)}`. -/
lemma phase (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : NZ ρ) (u w : ℝ) :
    (Real.exp ((u + w) / 2) : ℂ) * cexp (ρ.im * (u + w : ℝ) * I) =
      (Real.exp (u / 2) : ℂ) * (cexp (w * ρ) * cexp (ρ.im * u * I)) := by
  have hr := re_half hRH hρ
  have key : (w : ℂ) * ρ = ((w / 2 : ℝ) : ℂ) + ρ.im * w * I := by
    apply Complex.ext <;> simp [hr] <;> ring
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add, key]
  congr 1
  push_cast
  ring

lemma norm_cexp_mul_le (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : NZ ρ) {w : ℝ} (hw : |w| ≤ 1) :
    ‖cexp (w * ρ)‖ ≤ 2 := by
  have hr := re_half hRH hρ
  rw [Complex.norm_exp]
  have : ((w : ℂ) * ρ).re = w / 2 := by simp [hr]; ring
  rw [this]
  have : Real.exp (w / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith [le_abs_self w])
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  linarith

/-- The zero coefficient for the window from `u + w₂` to `u + w₁`. -/
noncomputable def dW (η w₁ w₂ : ℝ) (ρ : ℂ) : ℂ := bq η ρ * (cexp (w₁ * ρ) - cexp (w₂ * ρ))

lemma summable_bq (hRH : RiemannHypothesis) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    Summable (fun ρ : NZs => ‖bq η ρ.1‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => norm_bq_le_hw hRH hη hη1 ρ.2)
    (summable_hw_NZs.mul_left _)

lemma summable_dW (hRH : RiemannHypothesis) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {w₁ w₂ : ℝ}
    (h1 : |w₁| ≤ 1) (h2 : |w₂| ≤ 1) : Summable (fun ρ : NZs => ‖dW η w₁ w₂ ρ.1‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => ?_)
    ((summable_bq hRH hη hη1).mul_left 4)
  unfold dW
  rw [norm_mul]
  have : ‖cexp (w₁ * ρ.1) - cexp (w₂ * ρ.1)‖ ≤ 4 :=
    (norm_sub_le _ _).trans (by
      linarith [norm_cexp_mul_le hRH ρ.2 h1, norm_cexp_mul_le hRH ρ.2 h2])
  nlinarith [norm_nonneg (bq η ρ.1)]

/-- **The zero part of a window**, under RH. -/
lemma Zq_window (hRH : RiemannHypothesis) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (u : ℝ) {w₁ w₂ : ℝ}
    (h1 : |w₁| ≤ 1) (h2 : |w₂| ≤ 1) :
    Zq (u + w₁) η - Zq (u + w₂) η = (Real.exp (u / 2) : ℂ) * fS (dW η w₁ w₂) u := by
  rw [Zq_RH hRH hη, Zq_RH hRH hη]
  have hs : ∀ w : ℝ, |w| ≤ 1 →
      Summable (fun ρ : NZs => bq η ρ.1 * (cexp (w * ρ.1) * cexp (ρ.1.im * u * I))) := by
    intro w hw
    refine Summable.of_norm_bounded ((summable_bq hRH hη hη1).mul_left 2) (fun ρ => ?_)
    rw [norm_mul, norm_mul, norm_cexp_im, mul_one]
    nlinarith [norm_cexp_mul_le hRH ρ.2 hw, norm_nonneg (bq η ρ.1)]
  have he : ∀ w : ℝ, |w| ≤ 1 → (Real.exp ((u + w) / 2) : ℂ) *
      ∑' ρ : NZs, bq η ρ.1 * cexp (ρ.1.im * (u + w : ℝ) * I) =
      (Real.exp (u / 2) : ℂ) * ∑' ρ : NZs, bq η ρ.1 * (cexp (w * ρ.1) * cexp (ρ.1.im * u * I)) := by
    intro w hw
    rw [← tsum_mul_left, ← tsum_mul_left]
    congr 1; ext ρ
    rw [mul_left_comm, phase hRH ρ.2 u w]; ring
  rw [he w₁ h1, he w₂ h2, ← mul_sub, ← (hs w₁ h1).tsum_sub (hs w₂ h2)]
  unfold fS dW
  congr 1; congr 1; ext ρ; ring

/-- `‖dW‖ = m(ρ) ‖c(ρ)‖` with `‖c(ρ)‖ ≤ 72 min(δ, ‖ρ‖⁻¹)`. -/
lemma dW_eq (η w₁ w₂ : ℝ) (ρ : ℂ) :
    dW η w₁ w₂ ρ = (mz ρ : ℂ) * (bq0 η ρ * (cexp (w₁ * ρ) - cexp (w₂ * ρ))) := by
  unfold dW; rw [bq_eq]; ring

lemma norm_c_le (hRH : RiemannHypothesis) {η δ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hδ : δ ≤ 1)
    {w₁ w₂ : ℝ} (h1 : |w₁| ≤ δ) (h2 : |w₂| ≤ δ) {ρ : ℂ} (hρ : NZ ρ) :
    ‖bq0 η ρ * (cexp (w₁ * ρ) - cexp (w₂ * ρ))‖ ≤ 72 * min δ ‖ρ‖⁻¹ := by
  have hr := re_half hRH hρ
  have hp : 0 < ‖ρ‖ := norm_pos_iff.mpr (NZ_ne_zero hρ)
  have hb := norm_bq0_le hRH hη hη1 hρ
  have hone : ∀ w : ℝ, |w| ≤ δ → ‖cexp (w * ρ) - 1‖ ≤ 6 * min (δ * ‖ρ‖) 1 := by
    intro w hw
    have hz : |((w : ℂ) * ρ).re| ≤ 3 / 2 := by
      have : ((w : ℂ) * ρ).re = w / 2 := by simp [hr]; ring
      rw [this, abs_div, abs_two]; linarith
    refine (norm_exp_sub_one_le_six hz).trans ?_
    gcongr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hw (norm_nonneg ρ)
  have hdiff : ‖cexp (w₁ * ρ) - cexp (w₂ * ρ)‖ ≤ 12 * min (δ * ‖ρ‖) 1 := by
    have e : cexp (w₁ * ρ) - cexp (w₂ * ρ) = (cexp (w₁ * ρ) - 1) - (cexp (w₂ * ρ) - 1) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith [hone w₁ h1, hone w₂ h2]
  rw [norm_mul]
  have hmin : 6 / ‖ρ‖ * (12 * min (δ * ‖ρ‖) 1) = 72 * min δ ‖ρ‖⁻¹ := by
    rcases le_total (δ * ‖ρ‖) 1 with hc | hc
    · have : δ ≤ ‖ρ‖⁻¹ := by rw [← one_div, le_div_iff₀ hp]; linarith
      rw [min_eq_left hc, min_eq_left this]; field_simp; ring
    · have : ‖ρ‖⁻¹ ≤ δ := by
        rw [inv_le_iff_one_le_mul₀ hp]; linarith
      rw [min_eq_right hc, min_eq_right this]; field_simp; norm_num
  rw [← hmin]
  exact mul_le_mul hb hdiff (norm_nonneg _) (by positivity)

/-- **The mean square of a window's zero part**, under RH. -/
theorem window_mean (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ η : ℝ, 0 < η → η ≤ 1 →
    0 < δ → δ ≤ 1 → ∀ w₁ w₂ : ℝ, |w₁| ≤ δ → |w₂| ≤ δ → ∀ U : ℝ,
    Integrable (fun u => ‖fS (dW η w₁ w₂) u‖ ^ 2 * gw U u) ∧
      ∫ u, ‖fS (dW η w₁ w₂) u‖ ^ 2 * gw U u ≤ C * δ * (Real.log (1 / δ) + 3) ^ 2 := by
  obtain ⟨Cmv, hCmv, hmv⟩ := zero_mean_value_mult
  obtain ⟨Ck, hCk, hkey⟩ := key_sum_two
  refine ⟨2 * (Cmv * (5184 * Ck)), by positivity, fun δ η hη hη1 hδ0 hδ1 w₁ w₂ h1 h2 U => ?_⟩
  have h1' : |w₁| ≤ 1 := h1.trans hδ1
  have h2' : |w₂| ≤ 1 := h2.trans hδ1
  have := zs_mean (dW η w₁ w₂) (summable_dW hRH hη hη1 h1' h2') U
    (Cmv * (5184 * Ck) * δ * (Real.log (1 / δ) + 3) ^ 2) (fun s => ?_)
  · refine ⟨this.1, this.2.trans_eq (by ring)⟩
  set S := s.map (Function.Embedding.subtype _)
  have hS : ∀ ρ ∈ S, NZ ρ := by
    intro ρ hρ
    obtain ⟨σ, _, rfl⟩ := Finset.mem_map.mp hρ
    exact σ.2
  set c : ℂ → ℂ := fun ρ => bq0 η ρ * (cexp (w₁ * ρ) - cexp (w₂ * ρ)) with hc
  have e : ∀ u : ℝ, ∑ ρ ∈ s, dW η w₁ w₂ ρ.1 * cexp (ρ.1.im * u * I)
      = ∑ ρ ∈ S, (mz ρ : ℂ) * c ρ * cexp (ρ.im * u * I) := fun u => by
    rw [Finset.sum_map]
    refine sum_congr rfl fun ρ _ => ?_
    simp only [Function.Embedding.coe_subtype, hc]
    rw [dW_eq]
  simp_rw [e]
  refine (hmv S hS c U).trans ?_
  have hb : ∀ ρ ∈ S, mz ρ * ‖c ρ‖ ^ 2 * Real.log (‖ρ‖ + 4)
      ≤ 5184 * (mz ρ * min (δ ^ 2) (‖ρ‖⁻¹ ^ 2) * Real.log (‖ρ‖ + 4)) := by
    intro ρ hρ
    have h := norm_c_le hRH hη hη1 hδ1 h1 h2 (hS ρ hρ)
    have hmin : 0 ≤ min δ ‖ρ‖⁻¹ := le_min hδ0.le (by positivity)
    have hsq : ‖c ρ‖ ^ 2 ≤ (72 * min δ ‖ρ‖⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    have hmin2 : min δ ‖ρ‖⁻¹ ^ 2 ≤ min (δ ^ 2) (‖ρ‖⁻¹ ^ 2) := by
      apply le_min
      · exact pow_le_pow_left₀ hmin (min_le_left _ _) 2
      · exact pow_le_pow_left₀ hmin (min_le_right _ _) 2
    have hL := one_le_log_add_four (norm_nonneg ρ)
    have hm := mz_nonneg ρ
    calc mz ρ * ‖c ρ‖ ^ 2 * Real.log (‖ρ‖ + 4)
        ≤ mz ρ * (72 * min δ ‖ρ‖⁻¹) ^ 2 * Real.log (‖ρ‖ + 4) := by gcongr
      _ = 5184 * mz ρ * (min δ ‖ρ‖⁻¹ ^ 2) * Real.log (‖ρ‖ + 4) := by ring
      _ ≤ 5184 * mz ρ * min (δ ^ 2) (‖ρ‖⁻¹ ^ 2) * Real.log (‖ρ‖ + 4) := by gcongr
      _ = _ := by ring
  calc Cmv * ∑ ρ ∈ S, mz ρ * ‖c ρ‖ ^ 2 * Real.log (‖ρ‖ + 4)
      ≤ Cmv * ∑ ρ ∈ S, 5184 * (mz ρ * min (δ ^ 2) (‖ρ‖⁻¹ ^ 2) * Real.log (‖ρ‖ + 4)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hb) hCmv.le
    _ = Cmv * (5184 * ∑ ρ ∈ S, mz ρ * min (δ ^ 2) (‖ρ‖⁻¹ ^ 2) * Real.log (‖ρ‖ + 4)) := by
        rw [← mul_sum]
    _ ≤ Cmv * (5184 * (Ck * δ * (Real.log (1 / δ) + 3) ^ 2)) := by
        gcongr; exact hkey δ hδ0 hδ1 S hS
    _ = Cmv * (5184 * Ck) * δ * (Real.log (1 / δ) + 3) ^ 2 := by ring

end LeanLab.PNTPort.Selberg

