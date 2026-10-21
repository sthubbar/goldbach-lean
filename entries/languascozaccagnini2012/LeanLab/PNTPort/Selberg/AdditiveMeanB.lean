module

public import LeanLab.PNTPort.Selberg.AdditiveMean
public import LeanLab.PNTPort.Selberg.Sharp4b

/-!
# Additive windows with the sharper remainder

Lab proof, unit U-6014, CLOUD 20261020T0415Z-cloud34, T2 toward IDEAS I-5100. AI wrote this
file: `sharp_x` and `additive_mean` of `AdditiveMean.lean` with `selberg_sharp_b` in place of
`selberg_sharp`, so the remainder term is `η^{-1}(abs(log η) + 2)² e^{-2U}`. CONDITIONAL ON
RiemannHypothesis only.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open MeasureTheory Set
open LeanLab.PNTPort.Gallagher

/-- **`selberg_sharp` in the variable `x`.** -/
theorem sharp_x_b (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ δ η : ℝ, 0 < η → η ≤ δ → δ ≤ 1 → ∀ U : ℝ,
    IntegrableOn (fun x => Wm x δ ^ 2 * omg U x) (Ioi 0) ∧
      ∫ x in Ioi 0, Wm x δ ^ 2 * omg U x ≤ C * (δ * (Real.log (1 / δ) + 3) ^ 2 +
        η ^ 2 * Real.exp U + (η ^ (-1 : ℝ) * (|Real.log η| + 2) ^ 2) * Real.exp (-(2 * U))) := by
  obtain ⟨C, hC, h⟩ := selberg_sharp_b hRH
  refine ⟨C, hC, fun δ η hη hηδ hδ1 U => ?_⟩
  obtain ⟨hi, hb⟩ := h δ η hη hηδ hδ1 U
  have hcongr : EqOn (fun x : ℝ => x⁻¹ • (Nw δ (Real.log x) ^ 2 * gw U (Real.log x)))
      (fun x => Wm x δ ^ 2 * omg U x) (Ioi 0) := fun x hx => smul_eq hx δ U
  have hI : IntegrableOn (fun x : ℝ => x⁻¹ • (Nw δ (Real.log x) ^ 2 * gw U (Real.log x)))
      (Ioi 0) :=
    (integrableOn_comp_log_Ioi_zero (fun u => Nw δ u ^ 2 * gw U u)).mpr hi
  refine ⟨hI.congr_fun hcongr measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_comp_log_Ioi_zero (fun u => Nw δ u ^ 2 * gw U u)]
  exact hb

/-- **Selberg's mean square for additive windows, under RH.** -/
theorem additive_mean_b (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (η : ℝ) (K : ℕ), 0 < η → 3 ≤ K → 2 * K * η ≤ 1 →
    ∀ U x₀ h : ℝ, 0 < x₀ → 0 ≤ h → h ≤ x₀ → h ≤ Real.exp U → h ≤ x₀ * ((K : ℝ) - 2) * η →
    IntegrableOn (fun x => (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x)
        (Ici x₀) ∧
      ∫ x in Ici x₀, (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x ≤
        C * (2 * K * η * (Real.log (1 / (2 * K * η)) + 3) ^ 2 + η ^ 2 * Real.exp U +
          (η ^ (-1 : ℝ) * (|Real.log η| + 2) ^ 2) * Real.exp (-(2 * U))) := by
  obtain ⟨C1, hC1, hsx⟩ := sharp_x_b hRH
  set c0 := ∫ u, gw 0 u with hc0def
  have hc0 : 0 ≤ c0 := integral_nonneg (gw_nonneg 0)
  refine ⟨16 * (1 + 4 * Real.exp 1) * C1 + 576 * Real.exp (1 / 2) * c0, by positivity,
    fun η K hη hK3 hK U x₀ h hx₀ hh hhx₀ hhU hs => ?_⟩
  have hK0 : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
  set Δ := 2 * K * η with hΔ
  set B := Δ * (Real.log (1 / Δ) + 3) ^ 2 + η ^ 2 * Real.exp U +
    (η ^ (-1 : ℝ) * (|Real.log η| + 2) ^ 2) * Real.exp (-(2 * U)) with hB
  have hΔ0 : 0 < Δ := by positivity
  have hB1 : 0 ≤ Δ * (Real.log (1 / Δ) + 3) ^ 2 := by positivity
  have hB3 : 0 ≤ (η ^ (-1 : ℝ) * (|Real.log η| + 2) ^ 2) * Real.exp (-(2 * U)) := by positivity
  have hBη : η ^ 2 * Real.exp U ≤ B := by rw [hB]; linarith
  have hsub : Ici x₀ ⊆ Ioi 0 := Ici_subset_Ioi.mpr hx₀
  -- the windows of the grid
  have hgrid : ∀ m ∈ Finset.Icc 1 (2 * K),
      IntegrableOn (fun x => Wm x (m * η) ^ 2 * omg U x) (Ioi 0) ∧
        ∫ x in Ioi 0, Wm x (m * η) ^ 2 * omg U x ≤ C1 * B := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hm2 : (m : ℝ) ≤ 2 * K := by exact_mod_cast hm.2
    have hδ1 : η ≤ m * η := by nlinarith
    have hδ2 : m * η ≤ Δ := by rw [hΔ]; nlinarith
    obtain ⟨hi, hb⟩ := hsx (m * η) η hη hδ1 (hδ2.trans hK) U
    refine ⟨hi, hb.trans (mul_le_mul_of_nonneg_left ?_ hC1)⟩
    have := bmain_mono (by positivity) hδ2 hK
    rw [hB]; linarith
  -- the three kinds of terms on `Ici x₀`
  have hF : ∀ m ∈ Finset.Icc 1 (2 * K),
      IntegrableOn (fun x => Wm x (m * η) ^ 2 * omg U x) (Ici x₀) ∧
        ∫ x in Ici x₀, Wm x (m * η) ^ 2 * omg U x ≤ C1 * B := by
    intro m hm
    obtain ⟨hi, hb⟩ := hgrid m hm
    refine ⟨hi.mono_set hsub, le_trans ?_ hb⟩
    exact setIntegral_mono_set hi (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (omg_nonneg _ _))
      (Filter.Eventually.of_forall hsub)
  have hG : ∀ m ∈ Finset.Icc 1 (2 * K),
      IntegrableOn (fun x => Wm (x + h) (m * η) ^ 2 * omg U x) (Ici x₀) ∧
        ∫ x in Ici x₀, Wm (x + h) (m * η) ^ 2 * omg U x ≤ 4 * Real.exp 1 * (C1 * B) := by
    intro m hm
    obtain ⟨hi, hb⟩ := hgrid m hm
    set f := (Ioi (0 : ℝ)).indicator (fun y => Wm y (m * η) ^ 2 * omg U y) with hf
    have hfi : Integrable f := (integrable_indicator_iff measurableSet_Ioi).mpr hi
    have hf0 : ∀ y, 0 ≤ f y := fun y => by
      rw [hf]; exact indicator_nonneg (fun y _ => mul_nonneg (sq_nonneg _) (omg_nonneg _ _)) y
    have hsh : Integrable (fun x => 4 * Real.exp 1 * f (x + h)) :=
      (hfi.comp_add_right h).const_mul _
    have hpt : ∀ x ∈ Ici x₀, Wm (x + h) (m * η) ^ 2 * omg U x ≤ 4 * Real.exp 1 * f (x + h) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
      have hxh : x + h ∈ Ioi (0 : ℝ) := by show 0 < x + h; linarith
      rw [hf, indicator_of_mem hxh]
      have := omg_shift (U := U) hx0 hh (hhx₀.trans hx) hhU
      calc Wm (x + h) (m * η) ^ 2 * omg U x ≤
            Wm (x + h) (m * η) ^ 2 * (4 * Real.exp 1 * omg U (x + h)) :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = _ := by ring
    have hmeas : Measurable (fun x => Wm (x + h) (m * η) ^ 2 * omg U x) :=
      (((measurable_Wm _).comp (measurable_add_const h)).pow_const 2).mul (measurable_omg U)
    have hGi : IntegrableOn (fun x => Wm (x + h) (m * η) ^ 2 * omg U x) (Ici x₀) := by
      refine hsh.integrableOn.mono' hmeas.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ici).mpr (ae_of_all _ fun x hx => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (omg_nonneg _ _))]
      exact hpt x hx
    refine ⟨hGi, ?_⟩
    calc ∫ x in Ici x₀, Wm (x + h) (m * η) ^ 2 * omg U x
        ≤ ∫ x in Ici x₀, 4 * Real.exp 1 * f (x + h) :=
          setIntegral_mono_on hGi hsh.integrableOn measurableSet_Ici hpt
      _ ≤ ∫ x, 4 * Real.exp 1 * f (x + h) :=
          setIntegral_le_integral hsh (ae_of_all _ fun x => by have := hf0 (x + h); positivity)
      _ = 4 * Real.exp 1 * ∫ x in Ioi 0, Wm x (m * η) ^ 2 * omg U x := by
          rw [integral_const_mul, integral_add_right_eq_self (fun x => f x) h, hf,
            integral_indicator measurableSet_Ioi]
      _ ≤ 4 * Real.exp 1 * (C1 * B) := mul_le_mul_of_nonneg_left hb (by positivity)
  obtain ⟨hgi, hgv⟩ := gw_log U
  have hE : IntegrableOn (fun x => (x + h) ^ 2 * η ^ 2 * omg U x) (Ici x₀) ∧
      ∫ x in Ici x₀, (x + h) ^ 2 * η ^ 2 * omg U x ≤
        4 * η ^ 2 * (Real.exp (U + 1 / 2) * c0) := by
    have hpt : ∀ x ∈ Ici x₀, (x + h) ^ 2 * η ^ 2 * omg U x ≤ 4 * η ^ 2 * gw U (Real.log x) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
      have hhx : h ≤ x := hhx₀.trans hx
      unfold omg
      rw [div_eq_mul_inv]
      have hg := gw_nonneg U (Real.log x)
      have h1 : (x + h) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
      have h2 : x ^ 2 * (x ^ 2)⁻¹ = 1 := by field_simp
      calc (x + h) ^ 2 * η ^ 2 * (gw U (Real.log x) * (x ^ 2)⁻¹)
          ≤ 4 * x ^ 2 * η ^ 2 * (gw U (Real.log x) * (x ^ 2)⁻¹) := by gcongr
        _ = 4 * η ^ 2 * gw U (Real.log x) * (x ^ 2 * (x ^ 2)⁻¹) := by ring
        _ = _ := by rw [h2, mul_one]
    have hmeas : Measurable (fun x => (x + h) ^ 2 * η ^ 2 * omg U x) :=
      (by fun_prop : Measurable (fun x : ℝ => (x + h) ^ 2 * η ^ 2)).mul (measurable_omg U)
    have hgi4 : IntegrableOn (fun x => 4 * η ^ 2 * gw U (Real.log x)) (Ioi 0) := hgi.const_mul _
    have hdom : IntegrableOn (fun x => 4 * η ^ 2 * gw U (Real.log x)) (Ici x₀) :=
      hgi4.mono_set hsub
    have hEi : IntegrableOn (fun x => (x + h) ^ 2 * η ^ 2 * omg U x) (Ici x₀) := by
      refine hdom.mono' hmeas.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ici).mpr (ae_of_all _ fun x hx => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := omg_nonneg U x; positivity)]
      exact hpt x hx
    refine ⟨hEi, ?_⟩
    calc ∫ x in Ici x₀, (x + h) ^ 2 * η ^ 2 * omg U x
        ≤ ∫ x in Ici x₀, 4 * η ^ 2 * gw U (Real.log x) :=
          setIntegral_mono_on hEi hdom measurableSet_Ici hpt
      _ ≤ ∫ x in Ioi 0, 4 * η ^ 2 * gw U (Real.log x) :=
          setIntegral_mono_set hgi4
            (ae_of_all _ fun x => by have := gw_nonneg U (Real.log x); positivity)
            (Filter.Eventually.of_forall hsub)
      _ = _ := by rw [integral_const_mul, hgv]
  -- the right side
  have hSi : IntegrableOn (fun x => ∑ m ∈ Finset.Icc 1 (2 * K),
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x)) (Ici x₀) :=
    integrable_finsetSum _ fun m hm => ((hF m hm).1.add (hG m hm).1)
  have hS8 : IntegrableOn (fun x => 8 * ∑ m ∈ Finset.Icc 1 (2 * K),
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x)) (Ici x₀) :=
    hSi.const_mul 8
  have hEK : IntegrableOn (fun x => 144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x)) (Ici x₀) :=
    hE.1.const_mul _
  have hRi : IntegrableOn (fun x => 8 * ∑ m ∈ Finset.Icc 1 (2 * K),
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) +
      144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x)) (Ici x₀) := hS8.add hEK
  have hsumeq : ∫ x in Ici x₀, ∑ m ∈ Finset.Icc 1 (2 * K),
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) =
      ∑ m ∈ Finset.Icc 1 (2 * K), ∫ x in Ici x₀,
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) :=
    integral_finsetSum _ fun m hm => ((hF m hm).1.add (hG m hm).1)
  have hRv : ∫ x in Ici x₀, (8 * ∑ m ∈ Finset.Icc 1 (2 * K),
      (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) +
      144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x)) ≤
      8 * (2 * K * ((1 + 4 * Real.exp 1) * (C1 * B))) +
      144 * K * (4 * η ^ 2 * (Real.exp (U + 1 / 2) * c0)) := by
    rw [integral_add hS8 hEK, integral_const_mul, integral_const_mul, hsumeq]
    have h1 : ∑ m ∈ Finset.Icc 1 (2 * K), ∫ x in Ici x₀,
        (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) ≤
        ∑ m ∈ Finset.Icc 1 (2 * K), (1 + 4 * Real.exp 1) * (C1 * B) := by
      refine Finset.sum_le_sum fun m hm => ?_
      rw [integral_add (hF m hm).1 (hG m hm).1]
      linarith [(hF m hm).2, (hG m hm).2]
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h1
    have hc : ((2 * K + 1 - 1 : ℕ) : ℝ) = 2 * K := by
      rw [show 2 * K + 1 - 1 = 2 * K by omega]; push_cast; ring
    rw [hc] at h1
    have h2 := hE.2
    have hK0' : (0 : ℝ) ≤ 144 * K := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hK0']
  -- the pointwise bound times the weight
  have hpt : ∀ x ∈ Ici x₀,
      K * ((Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x) ≤
        8 * ∑ m ∈ Finset.Icc 1 (2 * K),
          (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) +
        144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
    have hK2 : (0 : ℝ) ≤ ((K : ℝ) - 2) * η := by
      have : (3 : ℝ) ≤ K := by exact_mod_cast hK3
      nlinarith
    have hsx' : h ≤ x * ((K : ℝ) - 2) * η := by
      rw [mul_assoc] at hs ⊢; exact hs.trans (mul_le_mul_of_nonneg_right hx hK2)
    have := pointwise_avg hx0 hh hη hK3 hK hsx'
    have hω := omg_nonneg U x
    have h2 := mul_le_mul_of_nonneg_right this hω
    have expand : (8 * ∑ m ∈ Finset.Icc 1 (2 * K), (Wm x (m * η) ^ 2 + Wm (x + h) (m * η) ^ 2) +
        144 * K * ((x + h) ^ 2 * η ^ 2)) * omg U x =
        8 * ∑ m ∈ Finset.Icc 1 (2 * K),
          (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) +
        144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x) := by
      rw [add_mul, mul_assoc (8 : ℝ), Finset.sum_mul]
      congr 1
      · congr 1; exact Finset.sum_congr rfl (fun m _ => by ring)
      · ring
    rw [expand] at h2
    calc K * ((Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x)
        = K * (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x := by ring
      _ ≤ _ := h2
  have hmeasA : Measurable (fun x => (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x) :=
    ((((measurable_psi.comp (measurable_add_const h)).sub measurable_psi).sub
      measurable_const).pow_const 2).mul (measurable_omg U)
  have hAi : IntegrableOn (fun x => (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x)
      (Ici x₀) := by
    refine (hRi.const_mul (1 / (K : ℝ))).mono' hmeasA.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ici).mpr (ae_of_all _ fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (omg_nonneg _ _))]
    have := hpt x hx
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hK0]
    linarith
  refine ⟨hAi, ?_⟩
  have hint : K * ∫ x in Ici x₀, (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x ≤
      ∫ x in Ici x₀, (8 * ∑ m ∈ Finset.Icc 1 (2 * K),
        (Wm x (m * η) ^ 2 * omg U x + Wm (x + h) (m * η) ^ 2 * omg U x) +
        144 * K * ((x + h) ^ 2 * η ^ 2 * omg U x)) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hAi.const_mul _) hRi measurableSet_Ici hpt
  have hfin : K * ∫ x in Ici x₀, (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 * omg U x ≤
      K * ((16 * (1 + 4 * Real.exp 1) * C1 + 576 * Real.exp (1 / 2) * c0) * B) := by
    refine hint.trans (hRv.trans ?_)
    have he : Real.exp (U + 1 / 2) = Real.exp (1 / 2) * Real.exp U := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    have h1 : 0 ≤ Real.exp (1 / 2) * c0 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hBη h1
    have h4 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 576 * K by positivity)
    calc 8 * (2 * K * ((1 + 4 * Real.exp 1) * (C1 * B))) +
          144 * K * (4 * η ^ 2 * (Real.exp (1 / 2) * Real.exp U * c0))
        = K * (16 * (1 + 4 * Real.exp 1) * C1 * B) +
          576 * K * (Real.exp (1 / 2) * c0 * (η ^ 2 * Real.exp U)) := by ring
      _ ≤ K * (16 * (1 + 4 * Real.exp 1) * C1 * B) +
          576 * K * (Real.exp (1 / 2) * c0 * B) := by linarith
      _ = _ := by ring
  exact le_of_mul_le_mul_left hfin hK0

end LeanLab.PNTPort.Selberg

