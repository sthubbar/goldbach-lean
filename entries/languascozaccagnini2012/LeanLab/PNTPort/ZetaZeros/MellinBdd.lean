module

public import LeanLab.PNTPort.StrongPNT.MediumPNT

/-!
# The Mellin transform of the smoothed cutoff is `O(1/|s|)` uniformly in `ε`

Lab proof, unit U-5267, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known, no cited input.
With the ported `MellinOfSmooth1a`, Apache-2.0, PrimeNumberTheoremAnd: `𝓜(Smooth1 ν ε)(s) =
s⁻¹ 𝓜(ν)(εs)`, and `𝓜(ν)` is bounded on `0 ≤ Re w ≤ 2` since `ν` is bounded with support in
`[1/2, 2]`. The ported `MellinOfSmooth1b` gives the other bound `C/(ε|s|²)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter MeasureTheory

local notation (name := mellintransform3) "𝓜" => mellin

lemma rpow_le_two {t a : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 2) (ha1 : -1 ≤ a) (ha2 : a ≤ 1) :
    t ^ a ≤ 2 := by
  obtain ⟨h1, h2⟩ := ht
  have ht0 : 0 < t := by linarith
  rcases le_or_gt 1 t with h | h
  · calc t ^ a ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h ha2
      _ = t := Real.rpow_one t
      _ ≤ 2 := h2
  · calc t ^ a ≤ t ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ht0 h.le ha1
      _ = t⁻¹ := Real.rpow_neg_one t
      _ ≤ 2 := by rw [inv_le_comm₀ ht0 (by norm_num)]; linarith

/-- `𝓜(ν)` is bounded on the strip `0 ≤ Re w ≤ 2`. -/
lemma mellin_nu_bdd {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν) (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 2 → ‖𝓜 (fun x ↦ (ν x : ℂ)) w‖ ≤ A := by
  obtain ⟨Mν, hMν⟩ := (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    diffν.continuous.continuousOn
  refine ⟨3 * (|Mν| + 1), by positivity, fun w hw0 hw2 => ?_⟩
  unfold mellin
  have hsub : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun x hx => by simp only [mem_Ioi]; linarith [hx.1]
  have heq : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) • (ν t : ℂ) =
      ∫ t in Icc (1 / 2 : ℝ) 2, (t : ℂ) ^ (w - 1) • (ν t : ℂ) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub ?_
    intro t ht
    have hν : ν t = 0 := by
      by_contra h
      exact ht.2 (suppν (Function.mem_support.mpr h))
    simp [hν]
  show ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) • (ν t : ℂ)‖ ≤ _
  rw [heq]
  have hvol : (volume : Measure ℝ) (Icc (1 / 2 : ℝ) 2) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (C := 2 * (|Mν| + 1))
    (f := fun t : ℝ => (t : ℂ) ^ (w - 1) • (ν t : ℂ)) hvol (fun t ht => by
      have ht0 : 0 < t := by linarith [ht.1]
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
        Real.norm_eq_abs]
      have h1 : t ^ (w - 1).re ≤ 2 := rpow_le_two ht (by simp; linarith) (by simp; linarith)
      have h2 : |ν t| ≤ |Mν| + 1 := by
        have := hMν t ht; rw [Real.norm_eq_abs] at this; linarith [le_abs_self Mν]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num))
  refine hb.trans ?_
  rw [Real.volume_real_Icc_of_le (by norm_num)]
  nlinarith [abs_nonneg Mν]

/-- **`‖𝓜(Smooth1 ν ε)(s)‖ ≤ A / ‖s‖`** for `0 < Re s ≤ 2`, `0 < ε < 1`. -/
lemma mellin_smooth1_le {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν) (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ s : ℂ, 0 < s.re → s.re ≤ 2 →
      ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ A / ‖s‖ := by
  obtain ⟨A, hA, hb⟩ := mellin_nu_bdd diffν suppν
  refine ⟨A, hA, fun ε hε hε1 s hs0 hs2 => ?_⟩
  rw [MellinOfSmooth1a diffν suppν hε hs0, norm_mul, norm_inv]
  have hw0 : 0 ≤ ((ε : ℂ) * s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]; positivity
  have hw2 : ((ε : ℂ) * s).re ≤ 2 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]; nlinarith
  have := hb _ hw0 hw2
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left this (inv_nonneg.mpr (norm_nonneg _))

end LeanLab.PNTPort.ZetaZeros

