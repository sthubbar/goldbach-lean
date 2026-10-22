module

public import LeanLab.PNTPort.ZetaZeros.VLine
public import LeanLab.PNTPort.ZetaZeros.MellinBdd
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Von Koch: assuming RH, `ψ(X) = X + O(√X log³ X)`

Lab proof, unit U-5267, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics,
von Koch 1901 with one extra log, CONDITIONAL ON Mathlib's `RiemannHypothesis` as a hypothesis,
no other input.

The smoothed Chebyshev function of the ported MediumPNT, Apache-2.0, PrimeNumberTheoremAnd, is
shifted by its `SmoothedChebyshevPull1` to the line `σ₁ = 1/2 + 1/log X` with `T = X` and
`ε = X^{-1/2}`. Under RH there is no zero right of that line, `logDeriv_vline_RH` and
`logDeriv_bound_RH` bound `ζ'/ζ` on the new contour, `mellin_smooth1_le` and the ported
`MellinOfSmooth1b` bound the Mellin weight, the ported `I1Bound`, `I9Bound` bound the tails,
`SmoothedChebyshevClose` unsmooths at cost `ε X log X`, and `MellinOfSmooth1cExplicit` gives the
main term `X + O(εX)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric Topology MeasureTheory ComplexConjugate
open scoped Real

local notation "ζ" => riemannZeta
local notation (name := mellintransform4) "𝓜" => mellin

lemma one_div_norm_le {σ t : ℝ} (hσ : 1 / 2 ≤ σ) :
    1 / ‖(σ : ℂ) + t * I‖ ≤ 2 * (√(1 + t ^ 2))⁻¹ := by
  have hn : √(1 + t ^ 2) / 2 ≤ ‖(σ : ℂ) + t * I‖ := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_zero,
      add_im, mul_im, zero_add, add_zero, zero_mul]
    rw [div_le_iff₀ (by norm_num)]
    have h4 : √(1 + t ^ 2) = √((1 + t ^ 2) / 4) * 2 := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; ring
    rw [h4]
    gcongr
    nlinarith
  have hpos : 0 < √(1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [one_div, inv_le_comm₀ (lt_of_lt_of_le (by positivity) hn) (by positivity)]
  rw [mul_inv, inv_inv]
  linarith

lemma integral_inv_sqrt (T : ℝ) (hT : 1 ≤ T) :
    ∫ t in (-T)..T, (√(1 + t ^ 2))⁻¹ ≤ 2 * Real.log (3 * T) := by
  have hderiv : ∀ x ∈ uIcc (-T) T, HasDerivAt Real.arsinh (√(1 + x ^ 2))⁻¹ x :=
    fun x _ => Real.hasDerivAt_arsinh x
  have hint : IntervalIntegrable (fun t : ℝ => (√(1 + t ^ 2))⁻¹) volume (-T) T := by
    apply Continuous.intervalIntegrable
    exact (Real.continuous_sqrt.comp (by fun_prop)).inv₀ (fun t => (Real.sqrt_pos.mpr (by positivity)).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Real.arsinh_neg]
  have h : Real.arsinh T ≤ Real.log (3 * T) := by
    unfold Real.arsinh
    apply Real.log_le_log (by positivity)
    have : √(1 + T ^ 2) ≤ 2 * T := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    linarith
  linarith

/-- A vertical integral of a function bounded by `K / √(1 + t²)` on `[-T, T]`. -/
lemma vert_bound (f : ℝ → ℂ) {K T : ℝ} (hT : 1 ≤ T) (hK : 0 ≤ K)
    (hf : ∀ t : ℝ, |t| ≤ T → ‖f t‖ ≤ K * (√(1 + t ^ 2))⁻¹) :
    ‖∫ t in (-T)..T, f t‖ ≤ K * (2 * Real.log (3 * T)) := by
  have hc : Continuous (fun t : ℝ => (√(1 + t ^ 2))⁻¹) :=
    (Real.continuous_sqrt.comp (by fun_prop)).inv₀
      (fun t => (Real.sqrt_pos.mpr (by positivity)).ne')
  have hint : IntervalIntegrable (fun t : ℝ => K * (√(1 + t ^ 2))⁻¹) volume (-T) T :=
    (hc.const_mul K).intervalIntegrable _ _
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f)
    (g := fun t : ℝ => K * (√(1 + t ^ 2))⁻¹) (a := -T) (b := T)
    (by linarith) (Eventually.of_forall fun t ht => hf t (abs_le.mpr ⟨ht.1.le, ht.2⟩)) hint
  rw [intervalIntegral.integral_const_mul] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left (integral_inv_sqrt T hT) hK)

lemma rpow_one_add_inv_log {X : ℝ} (hX : 1 < X) : X ^ (1 + (Real.log X)⁻¹) = Real.exp 1 * X := by
  have hX0 : 0 < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos hX
  rw [Real.rpow_add hX0, Real.rpow_one, Real.rpow_def_of_pos hX0, mul_inv_cancel₀ hl.ne']
  ring

lemma rpow_half_add_inv_log {X : ℝ} (hX : 1 < X) :
    X ^ (1 / 2 + 1 / Real.log X) = Real.exp 1 * √X := by
  have hX0 : 0 < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos hX
  rw [Real.rpow_add hX0, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0 (1 / Real.log X),
    mul_one_div_cancel hl.ne']
  ring

set_option maxHeartbeats 8000000 in
/-- **Von Koch under RH**: `|ψ(X) - X| ≤ C √X log³ X` for `X ≥ X₀`. -/
theorem vonKoch_RH (hRH : RiemannHypothesis) : ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X →
    |Chebyshev.psi X - X| ≤ C * √X * Real.log X ^ 3 := by
  obtain ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have ContDiff1ν : ContDiff ℝ 1 ν := ContDiffν.of_le (by simp)
  have ν_nonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have ν_massOne : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨c_close, c_close_pos, h_close⟩ :=
    SmoothedChebyshevClose ContDiff1ν ν_supp ν_nonneg ν_massOne
  obtain ⟨ε_main, C_main, ε_main_pos, C_main_pos, h_main⟩ :=
    MellinOfSmooth1cExplicit ContDiff1ν ν_supp ν_massOne
  obtain ⟨c₁, c₁pos, hc₁⟩ := I1Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨c₉, c₉pos, hc₉⟩ := I9Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨Cb, Cbpos, hMb⟩ := MellinOfSmooth1b ContDiff1ν ν_supp
  obtain ⟨A, Apos, hMa⟩ := mellin_smooth1_le ContDiff1ν ν_supp
  obtain ⟨CV, CVpos, hV⟩ := logDeriv_vline_RH hRH
  obtain ⟨CR, CRpos, hR⟩ := logDeriv_bound_RH hRH
  set K37 : ℝ := CV * 2 * 2 * A * 2 * Real.exp 1 * 4 with hK37
  set K28 : ℝ := 2 * CR * Cb * Real.exp 1 with hK28
  refine ⟨c_close + C_main + c₁ + c₉ + K37 + 4 * K28,
    max (Real.exp 4) (4 / ε_main ^ 2), by positivity, fun X hX => ?_⟩
  -- the parameters
  have hXe : Real.exp 4 ≤ X := le_trans (le_max_left _ _) hX
  have hXε : 4 / ε_main ^ 2 ≤ X := le_trans (le_max_right _ _) hX
  have he4 : (54 : ℝ) < Real.exp 4 := by
    have := Real.add_one_lt_exp (by norm_num : (4 : ℝ) ≠ 0)
    have h2 := Real.exp_one_gt_d9
    calc (54 : ℝ) < 2.7182818283 ^ 4 := by norm_num
      _ < Real.exp 1 ^ 4 := by gcongr
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  have hX54 : 54 < X := by linarith
  have hX0 : 0 < X := by linarith
  have hlX : 4 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; exact hXe
  have hlX0 : 0 < Real.log X := by linarith
  set L := Real.log X with hL
  have hsX : 0 < √X := Real.sqrt_pos.mpr hX0
  have hsX7 : 7 < √X := by
    rw [show (7 : ℝ) = √49 by rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  set ε : ℝ := 1 / √X with hεdef
  have εpos : 0 < ε := by positivity
  have ε_lt_one : ε < 1 := by rw [hεdef, div_lt_one hsX]; linarith
  have hεmain : ε < ε_main := by
    rw [hεdef, div_lt_iff₀ hsX]
    have h1 : 2 / ε_main ≤ √X := by
      rw [show 2 / ε_main = √((2 / ε_main) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_le_sqrt
      rw [div_pow]; linarith [show (4 : ℝ) / ε_main ^ 2 = 2 ^ 2 / ε_main ^ 2 by norm_num]
    have : 1 < ε_main * √X := by
      have := mul_le_mul_of_nonneg_left h1 ε_main_pos.le
      rw [mul_div_cancel₀ _ ε_main_pos.ne'] at this; linarith
    linarith
  have hXεval : X * ε = √X := by
    rw [hεdef, mul_one_div, div_eq_iff hsX.ne']; exact (Real.mul_self_sqrt hX0.le).symm
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = X := ⟨X, rfl⟩
  set σ₁ : ℝ := 1 / 2 + 1 / L with hσ₁
  have hσ₁a : 1 / 2 < σ₁ := by
    rw [hσ₁]; have : 0 < 1 / L := by positivity
    linarith
  have hσ₁b : σ₁ ≤ 3 / 4 := by
    rw [hσ₁]
    have : 1 / L ≤ 1 / 4 := by rw [div_le_div_iff₀ hlX0 (by norm_num)]; linarith
    linarith
  have hinvσ : 1 / (σ₁ - 1 / 2) = L := by rw [hσ₁]; field_simp; ring
  -- the contour shift
  have holo : HolomorphicOn (deriv ζ / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}) := by
    intro s hs
    have hs1 : s ≠ 1 := hs.2
    have hre : σ₁ ≤ s.re := by
      have := hs.1; simp only [mem_reProdIm, mem_Icc] at this; exact this.1.1
    have hz : ζ s ≠ 0 := by
      intro hz
      have := rh_re hRH hz (by linarith)
      linarith
    exact ((differentiableAt_deriv_riemannZeta hs1).div
      (differentiableAt_riemannZeta hs1) hz).differentiableWithinAt
  have hpull := SmoothedChebyshevPull1 εpos ε_lt_one X (by linarith) (T := T) (by linarith)
    (σ₁ := σ₁) (by linarith) (by linarith) holo ν_supp ν_nonneg ν_massOne ContDiff1ν
  -- bounds on the pieces
  have hb1 := hc₁ ε εpos ε_lt_one X (by linarith) (T := T) (by linarith)
  have hb9 := hc₉ εpos ε_lt_one X (by linarith) (T := T) (by linarith)
  have hclose := h_close X (by linarith) ε εpos ε_lt_one (by rw [hXεval]; linarith)
  have hmain := h_main ε ⟨εpos, hεmain⟩
  have hXT : X * L / (ε * T) = √X * L := by
    rw [hT, hεdef]; field_simp
  -- logs
  have hL1 : 1 ≤ L := by linarith
  have hL23 : L ^ 2 ≤ L ^ 3 := by
    calc L ^ 2 = L ^ 2 * 1 := by ring
      _ ≤ L ^ 2 * L := by gcongr
      _ = L ^ 3 := by ring
  have hLL3 : L ≤ L ^ 3 := by
    calc L = L * 1 := by ring
      _ ≤ L * L ^ 2 := by gcongr; nlinarith
      _ = L ^ 3 := by ring
  have hs1 : (1 : ℝ) ≤ √X := by linarith
  have hL2X : L ^ 2 ≤ √X * L ^ 3 := by
    calc L ^ 2 ≤ L ^ 3 := hL23
      _ = 1 * L ^ 3 := by ring
      _ ≤ √X * L ^ 3 := by gcongr
  have hlogT : ∀ u : ℝ, 0 ≤ u → u ≤ X ^ 2 → Real.log u ≤ 2 * L := by
    intro u hu0 hu
    rcases eq_or_lt_of_le hu0 with h | h
    · rw [← h, Real.log_zero]; linarith
    calc Real.log u ≤ Real.log (X ^ 2) := Real.log_le_log h hu
      _ = 2 * L := by rw [Real.log_pow, hL]; norm_num
  have hXσ₁ : X ^ σ₁ = Real.exp 1 * √X := by
    have h := rpow_half_add_inv_log (X := X) (by linarith)
    rw [← hL] at h; rw [hσ₁]; exact h
  have hXσ₀ : X ^ (1 + (Real.log X)⁻¹) = Real.exp 1 * X := rpow_one_add_inv_log (by linarith)
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hnormI : ‖(1 / (2 * π * I) : ℂ)‖ ≤ 1 := by
    have h2π : ‖(2 * π * I : ℂ)‖ = 2 * π := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]; norm_num
    rw [norm_div, norm_one, h2π, div_le_one (by positivity)]
    have := Real.pi_gt_three; linarith
  -- the vertical integral
  have h37 : ‖I₃₇ ν ε T X σ₁‖ ≤ K37 * √X * L ^ 3 := by
    unfold I₃₇
    set K' : ℝ := CV * 2 * 2 * A * 2 * Real.exp 1 with hK'
    have hpt : ∀ t : ℝ, |t| ≤ T → ‖SmoothedChebyshevIntegrand ν ε X (σ₁ + t * I)‖ ≤
        K' * √X * L ^ 2 * (√(1 + t ^ 2))⁻¹ := by
      intro t ht
      obtain ⟨_, hb⟩ := hV σ₁ hσ₁a hσ₁b t
      have hre : ((σ₁ : ℂ) + t * I).re = σ₁ := by simp
      have hM := hMa ε εpos ε_lt_one ((σ₁ : ℂ) + t * I) (by rw [hre]; linarith)
        (by rw [hre]; linarith)
      have hs := one_div_norm_le (σ := σ₁) (t := t) (by linarith)
      have hl := hlogT (|t| + 5) (by positivity) (by rw [hT] at ht; nlinarith)
      rw [hinvσ] at hb
      unfold SmoothedChebyshevIntegrand
      rw [norm_mul, norm_mul, neg_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hX0, hre,
        hXσ₁]
      have hsq : 0 ≤ (√(1 + t ^ 2))⁻¹ := by positivity
      have hb' : ‖deriv ζ (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ ≤ CV * (2 * L) * (2 * L) := by
        calc _ ≤ CV * Real.log (|t| + 5) * (1 + L) := hb
          _ ≤ CV * (2 * L) * (2 * L) := by gcongr; linarith
      have hM' : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (↑σ₁ + ↑t * I)‖ ≤ A * (2 * (√(1 + t ^ 2))⁻¹) := by
        calc _ ≤ A / ‖(σ₁ : ℂ) + t * I‖ := hM
          _ = A * (1 / ‖(σ₁ : ℂ) + t * I‖) := by ring
          _ ≤ A * (2 * (√(1 + t ^ 2))⁻¹) := by gcongr
      calc ‖deriv ζ (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (↑σ₁ + ↑t * I)‖ * (Real.exp 1 * √X)
          ≤ (CV * (2 * L) * (2 * L)) * (A * (2 * (√(1 + t ^ 2))⁻¹)) * (Real.exp 1 * √X) :=
            mul_le_mul (mul_le_mul hb' hM' (norm_nonneg _) (by positivity)) le_rfl
              (by positivity) (by positivity)
        _ = K' * √X * L ^ 2 * (√(1 + t ^ 2))⁻¹ := by rw [hK']; ring
    have hK'0 : 0 ≤ K' := by rw [hK']; positivity
    have hbound : ‖∫ t in (-T)..T, SmoothedChebyshevIntegrand ν ε X (↑σ₁ + ↑t * I)‖ ≤
        (K' * √X * L ^ 2) * (2 * Real.log (3 * T)) :=
      vert_bound _ (by linarith) (by positivity) hpt
    have hl3 : Real.log (3 * T) ≤ 2 * L :=
      hlogT (3 * T) (by rw [hT]; positivity) (by rw [hT]; nlinarith)
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
    calc ‖(1 / (2 * π * I) : ℂ)‖ * ‖∫ t in (-T)..T, SmoothedChebyshevIntegrand ν ε X (↑σ₁ + ↑t * I)‖
        ≤ 1 * (K' * √X * L ^ 2 * (2 * Real.log (3 * T))) :=
          mul_le_mul hnormI hbound (norm_nonneg _) (by norm_num)
      _ ≤ 1 * (K' * √X * L ^ 2 * (2 * (2 * L))) := by
          gcongr
      _ = K37 * √X * L ^ 3 := by rw [hK37, hK']; ring
  -- the horizontal integrals
  have hhor : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ 1 + (Real.log X)⁻¹ →
      ‖SmoothedChebyshevIntegrand ν ε X (σ - T * I)‖ ≤ K28 * L ^ 2 ∧
      ‖SmoothedChebyshevIntegrand ν ε X (σ + T * I)‖ ≤ K28 * L ^ 2 := by
    intro σ h1 h2
    have hσ2 : σ ≤ 2 := by
      have : (Real.log X)⁻¹ ≤ 1 := by rw [inv_le_one₀ hlX0]; linarith
      linarith
    obtain ⟨_, hb⟩ := hR T (by rw [hT]; linarith) σ (by linarith) (by linarith)
    have hinv2 : 1 / (σ - 1 / 2) ≤ L := by
      rw [← hinvσ]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have hb' : ‖deriv ζ ((σ : ℂ) + I * T) / ζ ((σ : ℂ) + I * T)‖ ≤ CR * L * (2 * L) := by
      calc _ ≤ CR * Real.log T * (1 + 1 / (σ - 1 / 2)) := hb
        _ ≤ CR * L * (2 * L) := by rw [hT]; gcongr; linarith
    have hXσ : X ^ σ ≤ Real.exp 1 * X := by
      rw [← hXσ₀]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) h2
    have key : ∀ s : ℂ, s.re = σ → |s.im| = T →
        ‖deriv ζ s / ζ s‖ ≤ CR * L * (2 * L) →
        ‖SmoothedChebyshevIntegrand ν ε X s‖ ≤ K28 * L ^ 2 := by
      intro s hre him hz
      have hM := hMb (1 / 2) (by norm_num) s (by rw [hre]; linarith) (by rw [hre]; linarith)
        ε εpos ε_lt_one
      have hsT : X ≤ ‖s‖ := by
        have := Complex.abs_im_le_norm s; rw [him, hT] at this; exact this
      have hM' : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ Cb * √X / X ^ 2 := by
        have h1 : X ^ 2 ≤ ‖s‖ ^ 2 := by nlinarith [norm_nonneg s]
        have hs0 : 0 < ‖s‖ := by linarith
        have e : (ε * ‖s‖ ^ 2)⁻¹ = √X / ‖s‖ ^ 2 := by rw [hεdef]; field_simp
        calc _ ≤ Cb * (ε * ‖s‖ ^ 2)⁻¹ := hM
          _ = Cb * (√X / ‖s‖ ^ 2) := by rw [e]
          _ ≤ Cb * (√X / X ^ 2) := by
              gcongr
          _ = Cb * √X / X ^ 2 := by ring
      unfold SmoothedChebyshevIntegrand
      rw [norm_mul, norm_mul, neg_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hX0, hre]
      have hsXX : √X / X ≤ 1 := by
        rw [div_le_one hX0]
        nlinarith [Real.mul_self_sqrt hX0.le]
      calc ‖deriv ζ s / ζ s‖ * ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ * X ^ σ
          ≤ (CR * L * (2 * L)) * (Cb * √X / X ^ 2) * (Real.exp 1 * X) := by gcongr
        _ = K28 * L ^ 2 * (√X / X) := by rw [hK28]; field_simp
        _ ≤ K28 * L ^ 2 * 1 := by gcongr
        _ = K28 * L ^ 2 := by ring
    refine ⟨key _ (by simp) (by simp [abs_of_pos (show (0 : ℝ) < T by linarith)]) ?_,
      key _ (by simp) (by simp [abs_of_pos (show (0 : ℝ) < T by linarith)]) ?_⟩
    · have e : (σ : ℂ) - T * I = conj ((σ : ℂ) + I * T) := by
        apply Complex.ext
        · simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, conj_re, add_re]; ring
        · simp only [sub_im, ofReal_re, mul_im, ofReal_im, I_re, I_im, conj_im, add_im]; ring
      rw [e]
      have := logDerivZeta_conj ((σ : ℂ) + I * T)
      simp only [Pi.div_apply] at this
      rw [this, Complex.norm_conj]; exact hb'
    · have e : (σ : ℂ) + T * I = (σ : ℂ) + I * T := by ring
      rw [e]; exact hb'
  have hlen : |1 + (Real.log X)⁻¹ - σ₁| ≤ 2 := by
    have : (Real.log X)⁻¹ ≤ 1 := by rw [inv_le_one₀ hlX0]; linarith
    have : 0 ≤ (Real.log X)⁻¹ := by positivity
    rw [abs_le]; constructor <;> linarith
  have h2 : ‖I₂ ν ε T X σ₁‖ ≤ 2 * K28 * √X * L ^ 3 := by
    unfold I₂
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ₁)
      (b := 1 + (Real.log X)⁻¹) (C := K28 * L ^ 2)
      (f := fun σ : ℝ => SmoothedChebyshevIntegrand ν ε X (σ - T * I)) (fun σ hσ => by
        rw [uIoc_of_le (by have : 0 < (Real.log X)⁻¹ := by positivity
                           linarith)] at hσ
        exact (hhor σ hσ.1.le hσ.2).1)
    rw [norm_mul]
    have hK0 : 0 ≤ K28 := by rw [hK28]; positivity
    calc ‖(1 / (2 * π * I) : ℂ)‖ * ‖∫ σ in σ₁..(1 + (Real.log X)⁻¹),
          SmoothedChebyshevIntegrand ν ε X (σ - T * I)‖
        ≤ 1 * (K28 * L ^ 2 * 2) := by
          gcongr
          exact hb.trans (by gcongr)
      _ ≤ 2 * K28 * √X * L ^ 3 := by nlinarith [hL2X]
  have h8 : ‖I₈ ν ε T X σ₁‖ ≤ 2 * K28 * √X * L ^ 3 := by
    unfold I₈
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ₁)
      (b := 1 + (Real.log X)⁻¹) (C := K28 * L ^ 2)
      (f := fun σ : ℝ => SmoothedChebyshevIntegrand ν ε X (σ + T * I)) (fun σ hσ => by
        rw [uIoc_of_le (by have : 0 < (Real.log X)⁻¹ := by positivity
                           linarith)] at hσ
        exact (hhor σ hσ.1.le hσ.2).2)
    rw [norm_mul]
    have hK0 : 0 ≤ K28 := by rw [hK28]; positivity
    calc ‖(1 / (2 * π * I) : ℂ)‖ * ‖∫ σ in σ₁..(1 + (Real.log X)⁻¹),
          SmoothedChebyshevIntegrand ν ε X (σ + T * I)‖
        ≤ 1 * (K28 * L ^ 2 * 2) := by
          gcongr
          exact hb.trans (by gcongr)
      _ ≤ 2 * K28 * √X * L ^ 3 := by nlinarith [hL2X]
  -- assembly
  have e : ((Chebyshev.psi X - X : ℝ) : ℂ) =
      -(SmoothedChebyshev ν ε X - (Chebyshev.psi X : ℂ)) +
      (I₁ ν ε X T - I₂ ν ε T X σ₁ + I₃₇ ν ε T X σ₁ + I₈ ν ε T X σ₁ + I₉ ν ε X T) +
      (𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) * X := by
    rw [Complex.ofReal_sub]; linear_combination hpull
  have habs : |Chebyshev.psi X - X| = ‖((Chebyshev.psi X - X : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [habs, e]
  have hεX : ε * X = √X := by rw [mul_comm]; exact hXεval
  have hc : ‖SmoothedChebyshev ν ε X - (Chebyshev.psi X : ℂ)‖ ≤ c_close * √X * L ^ 3 := by
    calc _ ≤ c_close * ε * X * L := hclose
      _ = c_close * √X * L := by rw [mul_assoc c_close, hεX]
      _ ≤ c_close * √X * L ^ 3 := by gcongr
  have hm : ‖(𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) * X‖ ≤ C_main * √X * L ^ 3 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
    calc _ ≤ C_main * ε * X := by gcongr
      _ = C_main * √X := by rw [mul_assoc, hεX]
      _ = C_main * √X * 1 := by ring
      _ ≤ C_main * √X * L ^ 3 := by
          have : 1 ≤ L ^ 3 := le_trans hL1 hLL3
          gcongr
  have hb1' : ‖I₁ ν ε X T‖ ≤ c₁ * √X * L ^ 3 := by
    calc _ ≤ c₁ * X * Real.log X / (ε * T) := hb1
      _ = c₁ * (X * L / (ε * T)) := by rw [hL]; ring
      _ = c₁ * (√X * L) := by rw [hXT]
      _ ≤ c₁ * √X * L ^ 3 := by rw [← mul_assoc]; gcongr
  have hb9' : ‖I₉ ν ε X T‖ ≤ c₉ * √X * L ^ 3 := by
    calc _ ≤ c₉ * X * Real.log X / (ε * T) := hb9
      _ = c₉ * (X * L / (ε * T)) := by rw [hL]; ring
      _ = c₉ * (√X * L) := by rw [hXT]
      _ ≤ c₉ * √X * L ^ 3 := by rw [← mul_assoc]; gcongr
  calc ‖-(SmoothedChebyshev ν ε X - (Chebyshev.psi X : ℂ)) +
        (I₁ ν ε X T - I₂ ν ε T X σ₁ + I₃₇ ν ε T X σ₁ + I₈ ν ε T X σ₁ + I₉ ν ε X T) +
        (𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) * X‖
      ≤ ‖SmoothedChebyshev ν ε X - (Chebyshev.psi X : ℂ)‖ +
        (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖) +
        ‖(𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) * X‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (by rw [norm_neg]) ?_)) le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_sub_le _ _
    _ ≤ c_close * √X * L ^ 3 + (c₁ * √X * L ^ 3 + 2 * K28 * √X * L ^ 3 + K37 * √X * L ^ 3 +
          2 * K28 * √X * L ^ 3 + c₉ * √X * L ^ 3) + C_main * √X * L ^ 3 := by
        gcongr
    _ = (c_close + C_main + c₁ + c₉ + K37 + 4 * K28) * √X * L ^ 3 := by ring
    _ ≤ (c_close + C_main + c₁ + c₉ + K37 + 4 * K28) * √X * Real.log X ^ 3 := le_rfl

end LeanLab.PNTPort.ZetaZeros

