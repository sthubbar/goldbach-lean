module

public import LeanLab.PNTPort.Selberg.Cramer
public import LeanLab.PNTPort.Selberg.AdditiveDiscrete

/-!
# Cramér's mean square under RH, in `x` and over integers

Lab proof, unit U-6115, CLOUD 20261020T0618Z-cloud36, T2 toward P0058 Lemma 1 for small `ξ`.
AI wrote this file. CONDITIONAL ON RiemannHypothesis only, through `cramer_gauss`.
Known mathematics, Cramér 1921.

* `cramer_x`: `∫_{x > 0} (ψ(x) − x)² ω_U(x) dx ≤ M` for `U ≥ 0`, `ω_U(x) = e^{−(log x − U)²/2}/x²`;
* `cramer_discrete`: for `U ≥ 0` and naturals `e^{U−1} ≤ a`, `b ≤ e^{U+1}`,
  `Σ_{a ≤ m < b} (ψ(m) − m)² ≤ C e^{2U}`, the local discrete form with no log loss.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open MeasureTheory Filter Set
open LeanLab.PNTPort.Gallagher

lemma Fc_log_smul {x : ℝ} (hx : 0 < x) (U : ℝ) :
    x⁻¹ • (Fc (Real.log x) ^ 2 * gw U (Real.log x)) = (Chebyshev.psi x - x) ^ 2 * omg U x := by
  unfold Fc omg
  rw [Real.exp_log hx, smul_eq_mul]
  have e : Real.exp (-(Real.log x / 2)) ^ 2 = x⁻¹ := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * -(Real.log x / 2) = -Real.log x by push_cast; ring,
      Real.exp_neg, Real.exp_log hx]
  rw [mul_pow, e]; field_simp

lemma omg_log_smul {x : ℝ} (hx : 0 < x) (U : ℝ) :
    x⁻¹ • (Real.exp (-Real.log x) * gw U (Real.log x)) = omg U x := by
  unfold omg
  rw [Real.exp_neg, Real.exp_log hx, smul_eq_mul]; field_simp

lemma exp_neg_mul_gw (U u : ℝ) : Real.exp (-u) * gw U u = Real.exp (-U + 1 / 2) * gw (U - 1) u := by
  unfold gw; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- **Cramér in `x`, under RH.** -/
theorem cramer_x (hRH : RiemannHypothesis) : ∃ M : ℝ, 0 ≤ M ∧ ∀ U : ℝ, 0 ≤ U →
    IntegrableOn (fun x => (Chebyshev.psi x - x) ^ 2 * omg U x) (Ioi 0) ∧
      ∫ x in Ioi 0, (Chebyshev.psi x - x) ^ 2 * omg U x ≤ M := by
  obtain ⟨M, hM, h⟩ := cramer_gauss hRH
  refine ⟨M, hM, fun U hU => ?_⟩
  have hcongr : EqOn (fun x : ℝ => x⁻¹ • (Fc (Real.log x) ^ 2 * gw U (Real.log x)))
      (fun x => (Chebyshev.psi x - x) ^ 2 * omg U x) (Ioi 0) := fun x hx => Fc_log_smul hx U
  have hI : IntegrableOn (fun x : ℝ => x⁻¹ • (Fc (Real.log x) ^ 2 * gw U (Real.log x))) (Ioi 0) :=
    (integrableOn_comp_log_Ioi_zero (fun u => Fc u ^ 2 * gw U u)).mpr (integrable_F2 U)
  refine ⟨hI.congr_fun hcongr measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_comp_log_Ioi_zero (fun u => Fc u ^ 2 * gw U u)]
  exact h U hU

/-- The weight alone: `∫_{x > 0} ω_U ≤ e^{1/2} ∫ gw 0` for `U ≥ 0`. -/
lemma omg_x (U : ℝ) (hU : 0 ≤ U) : IntegrableOn (omg U) (Ioi 0) ∧
    ∫ x in Ioi 0, omg U x ≤ Real.exp (1 / 2) * ∫ u, gw 0 u := by
  have hcongr : EqOn (fun x : ℝ => x⁻¹ • (Real.exp (-Real.log x) * gw U (Real.log x)))
      (omg U) (Ioi 0) := fun x hx => omg_log_smul hx U
  have hint : Integrable (fun u => Real.exp (-u) * gw U u) := by
    have : (fun u => Real.exp (-u) * gw U u) = fun u => Real.exp (-U + 1 / 2) * gw (U - 1) u := by
      ext u; exact exp_neg_mul_gw U u
    rw [this]; exact (gw_integrable (U - 1)).const_mul _
  have hI : IntegrableOn (fun x : ℝ => x⁻¹ • (Real.exp (-Real.log x) * gw U (Real.log x))) (Ioi 0) :=
    (integrableOn_comp_log_Ioi_zero (fun u => Real.exp (-u) * gw U u)).mpr hint
  refine ⟨hI.congr_fun hcongr measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_comp_log_Ioi_zero (fun u => Real.exp (-u) * gw U u)]
  have : (fun u => Real.exp (-u) * gw U u) = fun u => Real.exp (-U + 1 / 2) * gw (U - 1) u := by
    ext u; exact exp_neg_mul_gw U u
  rw [this, integral_const_mul, cr_integral_gw]
  have hc0 : 0 ≤ ∫ u, gw 0 u := integral_nonneg (gw_nonneg 0)
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hc0

lemma psi_floor_eq {m : ℕ} {x : ℝ} (hx : x ∈ Ico (m : ℝ) (m + 1)) :
    Chebyshev.psi x = Chebyshev.psi m := by
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  congr 2
  rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg m) hx.1)]
  exact ⟨hx.1, hx.2⟩

set_option maxHeartbeats 1000000 in
/-- **Cramér over integers, local form, under RH.** -/
theorem cramer_discrete (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ U : ℝ, 0 ≤ U → ∀ a b : ℕ, Real.exp (U - 1) ≤ a → (b : ℝ) ≤ Real.exp (U + 1) →
      ∑ m ∈ Finset.Ico a b, (Chebyshev.psi m - m) ^ 2 ≤ C * Real.exp (2 * U) := by
  obtain ⟨M, hM, hcx⟩ := cramer_x hRH
  set c0 := ∫ u, gw 0 u
  have hc0 : 0 ≤ c0 := integral_nonneg (gw_nonneg 0)
  refine ⟨(2 * M + 2 * (Real.exp (1 / 2) * c0)) * Real.exp (5 / 2), by positivity,
    fun U hU a b ha hb => ?_⟩
  obtain ⟨hIf, hVf⟩ := hcx U hU
  obtain ⟨hIg, hVg⟩ := omg_x U hU
  set f := fun x : ℝ => 2 * ((Chebyshev.psi x - x) ^ 2 * omg U x) + 2 * omg U x with hf
  have hIF : IntegrableOn f (Ioi 0) := (hIf.const_mul 2).add (hIg.const_mul 2)
  have hf0 : ∀ x, 0 ≤ f x := fun x => by
    simp only [hf]; have := omg_nonneg U x; positivity
  have hVF : ∫ x in Ioi 0, f x ≤ 2 * M + 2 * (Real.exp (1 / 2) * c0) := by
    rw [integral_add (hIf.const_mul 2) (hIg.const_mul 2), integral_const_mul, integral_const_mul]
    linarith
  set x₀ := Real.exp (U - 1) with hx₀
  have hx₀0 : 0 < x₀ := Real.exp_pos _
  set c := Real.exp (-(1 / 2)) * Real.exp (-(2 * (U + 1))) with hc
  have hc0' : 0 < c := by positivity
  have hkey : Real.exp (5 / 2) * Real.exp (2 * U) * c = 1 := by
    rw [hc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    ring_nf; exact Real.exp_zero
  set B := 2 * M + 2 * (Real.exp (1 / 2) * c0)
  have hRHS : B * Real.exp (5 / 2) * Real.exp (2 * U) = B / c := by
    rw [eq_div_iff hc0'.ne']
    calc B * Real.exp (5 / 2) * Real.exp (2 * U) * c = B * (Real.exp (5 / 2) * Real.exp (2 * U) * c) := by
          ring
      _ = B := by rw [hkey, mul_one]
  rw [hRHS, le_div_iff₀ hc0']
  rcases lt_or_ge b a with hba | hab
  · rw [Finset.Ico_eq_empty_of_le hba.le, Finset.sum_empty, zero_mul]; positivity
  have hsub : ∀ m, a ≤ m → Icc (m : ℝ) (m + 1) ⊆ Ioi 0 := by
    intro m hm y hy
    exact lt_of_lt_of_le hx₀0 (le_trans (ha.trans (by exact_mod_cast hm)) hy.1)
  have hii : ∀ m, a ≤ m → m < b → IntervalIntegrable f volume (m : ℝ) (m + 1) := by
    intro m hm _
    refine IntegrableOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith)]
    exact hIF.mono_set (hsub m hm)
  have hpiece : ∀ m ∈ Finset.Ico a b, (Chebyshev.psi m - m) ^ 2 * c ≤ ∫ x in (m : ℝ)..(m + 1), f x := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm1 : (m : ℝ) + 1 ≤ b := by exact_mod_cast hm.2
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    have hlow : ∀ x ∈ Ioo (m : ℝ) (m + 1), (Chebyshev.psi m - m) ^ 2 * c ≤ f x := by
      intro x hx
      have hps := psi_floor_eq (m := m) ⟨hx.1.le, hx.2⟩
      have hom := omg_lower (U := U) (x := x)
        (le_trans (ha.trans (by exact_mod_cast hm.1)) hx.1.le) (le_trans (by linarith [hx.2]) hb)
      have h2 : (Chebyshev.psi m - m) ^ 2 ≤ 2 * (Chebyshev.psi x - x) ^ 2 + 2 := by
        rw [hps]
        have h01 : (x - m) ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
        nlinarith [sq_nonneg (Chebyshev.psi (m : ℝ) - x - (x - m))]
      have hom0 := omg_nonneg U x
      simp only [hf]
      calc (Chebyshev.psi m - m) ^ 2 * c ≤ (Chebyshev.psi m - m) ^ 2 * omg U x :=
            mul_le_mul_of_nonneg_left hom (sq_nonneg _)
        _ ≤ (2 * (Chebyshev.psi x - x) ^ 2 + 2) * omg U x := mul_le_mul_of_nonneg_right h2 hom0
        _ = _ := by ring
    have hIoo : IntegrableOn f (Ioo (m : ℝ) (m + 1)) :=
      hIF.mono_set (Ioo_subset_Icc_self.trans (hsub m hm.1))
    calc (Chebyshev.psi m - m) ^ 2 * c
        = ∫ x in Ioo (m : ℝ) (m + 1), (Chebyshev.psi m - m) ^ 2 * c := by
          rw [setIntegral_const, Measure.real, Real.volume_Ioo,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]; ring
      _ ≤ ∫ x in Ioo (m : ℝ) (m + 1), f x :=
          setIntegral_mono_on (integrableOn_const (by simp)) hIoo measurableSet_Ioo hlow
  calc (∑ m ∈ Finset.Ico a b, (Chebyshev.psi m - m) ^ 2) * c
      = ∑ m ∈ Finset.Ico a b, (Chebyshev.psi m - m) ^ 2 * c := Finset.sum_mul _ _ _
    _ ≤ ∑ m ∈ Finset.Ico a b, ∫ x in (m : ℝ)..(m + 1), f x := Finset.sum_le_sum hpiece
    _ = ∫ x in (a : ℝ)..b, f x := sum_unit_intervals f hab hii
    _ = ∫ x in Ioc (a : ℝ) b, f x := intervalIntegral.integral_of_le (by exact_mod_cast hab)
    _ ≤ ∫ x in Ioi 0, f x := by
        refine setIntegral_mono_set hIF (ae_of_all _ hf0) (Filter.Eventually.of_forall ?_)
        intro y hy; exact lt_of_lt_of_le hx₀0 (ha.trans hy.1.le)
    _ ≤ B := hVF

end LeanLab.PNTPort.Selberg

