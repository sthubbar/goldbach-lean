module

public import LeanLab.Perelli1996.Kernel17

/-!
P0083, page 484, equations 16 and 17. Integrals on subsets of punctured arcs.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.LocalBounds88
open MeasureTheory Real

noncomputable section

/-- Equation 17 on any measurable subset of the containing symmetric kernel domain. -/
theorem kernel_subset (M q : ℕ) {s : Set ℝ} {P N c : ℝ}
    (hq : 0 < q) (hP : 0 < P) (hN : 0 < N) (hc : 1 ≤ c)
    (hM : (M : ℝ) ≤ c * N) (hradius : P / N ≤ 1 / 2)
    (hhalf : s ⊆ Set.Icc (-1 / 2 : ℝ) (1 / 2))
    (hgap : (q : ℝ) ≤ P → ∀ η ∈ s, P / N ≤ |η|) :
    (∫ η in s, ‖Kernel.T 0 M η‖ ^ 2) / (q.totient : ℝ) ^ 2 ≤ 4 * c * N / P := by
  have hcont : Continuous (fun η : ℝ => ‖Kernel.T 0 M η‖ ^ 2) := by
    unfold Kernel.T Kernel.e
    fun_prop
  have hbound : (∫ η in s, ‖Kernel.T 0 M η‖ ^ 2) / (q.totient : ℝ) ^ 2 ≤
      Kernel17.kernelMass 0 M q P N := by
    unfold Kernel17.kernelMass
    split_ifs with hqP
    · have hsub : s ⊆ Set.Icc (-1 / 2 : ℝ) (-(P / N)) ∪ Set.Icc (P / N) (1 / 2) := by
        intro η hη
        have hh := hhalf hη
        rcases le_abs.mp (hgap hqP η hη) with hg | hg
        · exact Or.inr ⟨hg, hh.2⟩
        · exact Or.inl ⟨hh.1, by linarith⟩
      have hl : IntegrableOn (fun η : ℝ => ‖Kernel.T 0 M η‖ ^ 2)
          (Set.Icc (-1 / 2 : ℝ) (-(P / N))) volume := hcont.integrableOn_Icc
      have hr : IntegrableOn (fun η : ℝ => ‖Kernel.T 0 M η‖ ^ 2)
          (Set.Icc (P / N) (1 / 2 : ℝ)) volume := hcont.integrableOn_Icc
      have hb := setIntegral_mono_set (hl.union hr)
        (Filter.Eventually.of_forall (fun η => sq_nonneg ‖Kernel.T 0 M η‖))
        (Filter.Eventually.of_forall hsub)
      have hdis : Disjoint (Set.Icc (-1 / 2 : ℝ) (-(P / N))) (Set.Icc (P / N) (1 / 2)) := by
        apply Set.disjoint_left.mpr
        intro η hl hr
        have := div_pos hP hN
        linarith [hl.2, hr.1]
      rw [setIntegral_union hdis measurableSet_Icc hl hr] at hb
      rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : (-1 / 2 : ℝ) ≤ -(P / N)),
        ← intervalIntegral.integral_of_le hradius] at hb
      exact div_le_div_of_nonneg_right hb (sq_nonneg _)
    · have hi : IntegrableOn (fun η : ℝ => ‖Kernel.T 0 M η‖ ^ 2)
          (Set.Icc (-1 / 2 : ℝ) (1 / 2)) volume := hcont.integrableOn_Icc
      have hb := setIntegral_mono_set hi
        (Filter.Eventually.of_forall (fun η => sq_nonneg ‖Kernel.T 0 M η‖))
        (Filter.Eventually.of_forall hhalf)
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hb
      exact div_le_div_of_nonneg_right hb (sq_nonneg _)
  exact hbound.trans (Kernel17.kernel17 0 M q hq hP hN hc hM hradius)

/-- Translation of a local arc integral to its center, equation 16. -/
theorem translate_setIntegral (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ℝ) (t : ℝ) :
    (∫ x in s, f x) = ∫ η in {η | t + η ∈ s}, f (t + η) := by
  have hpre : MeasurableSet {η : ℝ | t + η ∈ s} :=
    hs.preimage (measurable_const.add measurable_id)
  rw [← integral_indicator hs, ← integral_add_left_eq_self (s.indicator f) t,
    ← integral_indicator hpre]
  rfl

/-- The exact principal kernel and remainder give equation 16 on any punctured subset. -/
theorem second_moment_subset (M q : ℕ) (f r : ℝ → ℂ) (z : ℂ)
    {s : Set ℝ} {P N c δ E : ℝ} (hs : MeasurableSet s)
    (hf : Continuous f) (hr : Continuous r) (hq : 0 < q) (hP : 0 < P)
    (hN : 0 < N) (hc : 1 ≤ c) (hM : (M : ℝ) ≤ c * N)
    (hradius : P / N ≤ 1 / 2) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hsub : s ⊆ Set.Icc (-δ) δ)
    (hgap : (q : ℝ) ≤ P → ∀ η ∈ s, P / N ≤ |η|)
    (hz : ‖z‖ ≤ 1 / (q.totient : ℝ))
    (hdecomp : ∀ η, f η = z * Kernel.T 0 M η + r η)
    (hR : (∫ η in (-δ)..δ, ‖r η‖ ^ 2) ≤ E) :
    (∫ η in s, ‖f η‖ ^ 2) ≤ 8 * c * N / P + 2 * E := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hhalf : s ⊆ Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro η hη
    obtain ⟨hlo, hhi⟩ := hsub hη
    constructor <;> linarith
  have hk := kernel_subset M q hq hP hN hc hM hradius hhalf hgap
  have hTc : Continuous (fun η : ℝ => ‖Kernel.T 0 M η‖ ^ 2) := by
    unfold Kernel.T Kernel.e
    fun_prop
  have hti : IntegrableOn (fun η => ‖Kernel.T 0 M η‖ ^ 2) s volume :=
    hTc.integrableOn_Icc.mono_set hhalf
  have hrc : Continuous (fun η : ℝ => ‖r η‖ ^ 2) := by fun_prop
  have hri : IntegrableOn (fun η => ‖r η‖ ^ 2) (Set.Icc (-δ) δ) volume := hrc.integrableOn_Icc
  have hrem : (∫ η in s, ‖r η‖ ^ 2) ≤ E := by
    have hb := setIntegral_mono_set hri
      (Filter.Eventually.of_forall (fun η => sq_nonneg ‖r η‖))
      (Filter.Eventually.of_forall hsub)
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -δ ≤ δ)] at hb
    exact hb.trans hR
  have hfi : IntegrableOn (fun η => ‖f η‖ ^ 2) s volume :=
    (hf.norm.pow 2).integrableOn_Icc.mono_set hsub
  have hri' := hri.mono_set hsub
  have hki := (hti.const_mul 2).div_const ((q.totient : ℝ) ^ 2)
  have hbi : IntegrableOn (fun η => 2 * ‖Kernel.T 0 M η‖ ^ 2 / (q.totient : ℝ) ^ 2 +
      2 * ‖r η‖ ^ 2) s volume := by
    exact (hki.add (hri'.const_mul 2)).congr (Filter.Eventually.of_forall (fun η => rfl))
  have hpoint (η : ℝ) : ‖f η‖ ^ 2 ≤
      2 * ‖Kernel.T 0 M η‖ ^ 2 / (q.totient : ℝ) ^ 2 + 2 * ‖r η‖ ^ 2 := by
    have hb : ‖f η‖ ≤ ‖Kernel.T 0 M η‖ / (q.totient : ℝ) + ‖r η‖ := by
      rw [hdecomp η]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have hm := mul_le_mul_of_nonneg_right hz (norm_nonneg (Kernel.T 0 M η))
      simpa [div_eq_mul_inv, mul_comm] using add_le_add_right hm ‖r η‖
    have hsq := pow_le_pow_left₀ (norm_nonneg (f η)) hb 2
    have hnon := sq_nonneg (‖Kernel.T 0 M η‖ / (q.totient : ℝ) - ‖r η‖)
    have hid : (‖Kernel.T 0 M η‖ / (q.totient : ℝ)) ^ 2 =
        ‖Kernel.T 0 M η‖ ^ 2 / (q.totient : ℝ) ^ 2 := div_pow _ _ _
    calc ‖f η‖ ^ 2 ≤ (‖Kernel.T 0 M η‖ / (q.totient : ℝ) + ‖r η‖) ^ 2 := hsq
      _ ≤ 2 * (‖Kernel.T 0 M η‖ / (q.totient : ℝ)) ^ 2 + 2 * ‖r η‖ ^ 2 := by nlinarith only [hnon]
      _ = _ := by rw [hid]; ring
  calc (∫ η in s, ‖f η‖ ^ 2) ≤
      ∫ η in s, 2 * ‖Kernel.T 0 M η‖ ^ 2 / (q.totient : ℝ) ^ 2 + 2 * ‖r η‖ ^ 2 :=
      setIntegral_mono_on hfi hbi hs (fun η _ => hpoint η)
    _ = 2 * (∫ η in s, ‖Kernel.T 0 M η‖ ^ 2) / (q.totient : ℝ) ^ 2 +
        2 * (∫ η in s, ‖r η‖ ^ 2) := by
      rw [integral_add hki (hri'.const_mul 2)]
      simp only [div_eq_mul_inv, integral_mul_const, integral_const_mul]
    _ = 2 * ((∫ η in s, ‖Kernel.T 0 M η‖ ^ 2) / (q.totient : ℝ) ^ 2) +
        2 * (∫ η in s, ‖r η‖ ^ 2) := by ring
    _ ≤ 2 * (4 * c * N / P) + 2 * E := by gcongr
    _ = 8 * c * N / P + 2 * E := by ring

end
end LeanLab.Perelli1996.LocalBounds88
