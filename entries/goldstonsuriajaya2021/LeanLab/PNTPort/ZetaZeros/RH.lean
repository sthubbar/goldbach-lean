module

public import LeanLab.PNTPort.ZetaZeros.GoodHeight

/-!
# Under RH, `ζ'/ζ(σ + it) ≪ log t · (1 + 1/(σ - 1/2))` for `1/2 < σ ≤ 5/2`

Lab proof, unit U-5265, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics,
Titchmarsh ch. 14 in a weak form, CONDITIONAL ON Mathlib's `RiemannHypothesis` as a hypothesis,
no other input. From `logDeriv_local` and `zero_count_two`: under RH every zero in the local sum
has real part `1/2`, so each term is at most `1/(σ - 1/2)` and there are `O(log t)` of them.
At `σ = 1/2 + 1/log x` this is the `log t · log x` bound that a contour at that abscissa needs.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric Topology

local notation "ζ" => riemannZeta

lemma not_trivial_of_im {s : ℂ} (h : s.im ≠ 0) : ¬∃ n : ℕ, s = -2 * (n + 1) := by
  rintro ⟨n, rfl⟩; apply h; simp

lemma ne_one_of_im {s : ℂ} (h : s.im ≠ 0) : s ≠ 1 := by
  rintro rfl; apply h; simp

/-- **Under RH**, `‖ζ'/ζ(σ + it)‖ ≤ C log t · (1 + 1/(σ - 1/2))` for `t ≥ 5`, `1/2 < σ ≤ 5/2`;
in particular `ζ(σ + it) ≠ 0` there. -/
theorem logDeriv_bound_RH (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 5 ≤ t →
    ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 5 / 2 →
      ζ (σ + I * t) ≠ 0 ∧
      ‖deriv ζ (σ + I * t) / ζ (σ + I * t)‖ ≤ C * Real.log t * (1 + 1 / (σ - 1 / 2)) := by
  obtain ⟨C1, hC1, h2⟩ := zero_count_two
  obtain ⟨C2, hC2, hL⟩ := logDeriv_local
  refine ⟨C1 + C2, by positivity, fun t ht σ hσ1 hσ2 => ?_⟩
  set s : ℂ := σ + I * t with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have ht3 : 3 ≤ |t| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hsc : ‖s - cen t‖ ≤ 1 := by
    have e : s - cen t = ((σ - 3 / 2 : ℝ) : ℂ) := by simp only [hs, cen]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
  -- RH: a zero with nonzero imaginary part has real part `1/2`
  have hre : ∀ ρ : ℂ, ζ ρ = 0 → ρ.im ≠ 0 → ρ.re = 1 / 2 :=
    fun ρ hz him => hRH ρ hz (not_trivial_of_im him) (ne_one_of_im him)
  have hzs : ζ s ≠ 0 := by
    intro hz
    have := hre s hz (by rw [hsim]; linarith)
    rw [hsre] at this; linarith
  refine ⟨hzs, ?_⟩
  obtain ⟨hfin, hb⟩ := hL t ht3
  have hloc := hb s hsc hzs
  obtain ⟨hfW, hsW⟩ := h2 t ht
  have hsub : hfin.toFinset ⊆ hfW.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    refine ⟨hρ.1, ?_⟩
    have him : |(ρ - cen t).im| ≤ ‖ρ - cen t‖ := Complex.abs_im_le_norm _
    have e : (ρ - cen t).im = ρ.im - t := by simp [cen]
    rw [e] at him; linarith [hρ.2]
  have hd : 0 < σ - 1 / 2 := by linarith
  have hterm : ∀ ρ ∈ hfin.toFinset,
      ‖(analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ ≤ (analyticOrderNatAt ζ ρ : ℝ) / (σ - 1 / 2) := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have him : |(ρ - cen t).im| ≤ ‖ρ - cen t‖ := Complex.abs_im_le_norm _
    have e : (ρ - cen t).im = ρ.im - t := by simp [cen]
    rw [e] at him
    have hρim : ρ.im ≠ 0 := by
      intro h0; rw [h0] at him
      have := hρ.2
      rw [abs_le] at him; linarith [him.1]
    have hρre := hre ρ hρ.1 hρim
    have hn : σ - 1 / 2 ≤ ‖s - ρ‖ := by
      have : |(s - ρ).re| ≤ ‖s - ρ‖ := Complex.abs_re_le_norm _
      have e2 : (s - ρ).re = σ - 1 / 2 := by simp [hsre, hρre]
      rw [e2, abs_of_pos hd] at this; exact this
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd hn
  have hsumle : ‖∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ ≤
      C1 * Real.log t / (σ - 1 / 2) := by
    calc _ ≤ ∑ ρ ∈ hfin.toFinset, ‖(analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ) / (σ - 1 / 2) :=
          Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) / (σ - 1 / 2) := by
          rw [Finset.sum_div]
      _ ≤ C1 * Real.log t / (σ - 1 / 2) := by
          apply div_le_div_of_nonneg_right _ hd.le
          exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => Nat.cast_nonneg _)).trans hsW
  have htri : ‖deriv ζ s / ζ s‖ ≤ C2 * Real.log |t| + C1 * Real.log t / (σ - 1 / 2) := by
    have := norm_sub_le_norm_sub_add_norm_sub (deriv ζ s / ζ s)
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)) 0
    rw [sub_zero, sub_zero] at this
    linarith
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)] at htri
  have hl : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hinv : 0 ≤ 1 / (σ - 1 / 2) := by positivity
  calc ‖deriv ζ s / ζ s‖ ≤ C2 * Real.log t + C1 * Real.log t / (σ - 1 / 2) := htri
    _ = C2 * Real.log t + C1 * Real.log t * (1 / (σ - 1 / 2)) := by ring
    _ ≤ (C1 + C2) * Real.log t * (1 + 1 / (σ - 1 / 2)) := by nlinarith [mul_nonneg hl hinv]

end LeanLab.PNTPort.ZetaZeros

