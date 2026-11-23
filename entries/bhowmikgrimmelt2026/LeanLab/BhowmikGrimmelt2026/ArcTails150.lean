module

public import LeanLab.BhowmikGrimmelt2026.ModelL2_150
public import LeanLab.BhowmikGrimmelt2026.Coefficients150

/-!
ROUTE BURST 7, 20261112. The arc tails of P0029, Bhowmik and Grimmelt 2026, page 12, the
`O(N^{1/2+ε})` in the contribution of the arc around `a/q`, in mean square.

`V² - W` is minus the sum over `q ≤ Q`, `(a, q) = 1`, of `μ(q)²/φ(q)² T(α - a/q)²` off the arc of
`a/q`.  PROVED here: its integral `∫_0^1 |V² - W| ≪ X^{1+ε}`, from `∫|V|² ≪ X^{1+ε}` of
ModelL2_150.lean and `∫|W| ≤ X Σ_{q ≤ Q} q/φ(q)²`; and the interpolation
`∫|V² - W|² ≤ sup |V² - W| · ∫|V² - W|`.  The pointwise bound `sup |V² - W| ≪ X^{1+ε}` stays a
leaf in Decomp150a.lean.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

/-- `X Σ_{q ≤ ⌊X^{1/2}⌋} (q + 1)/φ(q)² ≪ X^{1+ε}`. PROVED, the last step of
`integral_norm_sq_VX_le150`. -/
theorem X_mul_weight_le150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      (X : ℝ) * ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2 ≤
        C * (X : ℝ) ^ (1 + ε) := by
  intro ε hε
  set k : ℕ := ⌈2 / ε⌉₊ + 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hkR : (2 / ε : ℝ) < k := by
    have := Nat.le_ceil (2 / ε)
    rw [hk]; push_cast; linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hs : 2 * (k : ℝ)⁻¹ ≤ ε := by
    rw [mul_comm, ← div_eq_inv_mul, div_le_iff₀ hkpos]
    have := (div_lt_iff₀ hε).mp hkR
    linarith
  obtain ⟨C, hC0, hC⟩ := sum_totient_weight_le150 k hk1
  refine ⟨C, hC0, fun X hX => ?_⟩
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hQ1 : 1 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by simpa using hX)
  have hQR : (1 : ℝ) ≤ (Nat.sqrt X : ℝ) := by exact_mod_cast hQ1
  have hQ2 : ((Nat.sqrt X : ℝ)) ^ 2 ≤ X := by exact_mod_cast Nat.sqrt_le' X
  have hQpow : (Nat.sqrt X : ℝ) ^ (4 * (k : ℝ)⁻¹) ≤ (X : ℝ) ^ ε := by
    have e : (Nat.sqrt X : ℝ) ^ (4 * (k : ℝ)⁻¹) = ((Nat.sqrt X : ℝ) ^ 2) ^ (2 * (k : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
    rw [e]
    calc ((Nat.sqrt X : ℝ) ^ 2) ^ (2 * (k : ℝ)⁻¹) ≤ (X : ℝ) ^ (2 * (k : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hQ2 (by positivity)
      _ ≤ (X : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le hXR hs
  have hw := hC (Nat.sqrt X) hQ1
  calc (X : ℝ) * ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2
      ≤ (X : ℝ) * (C * (X : ℝ) ^ ε) := by
        apply mul_le_mul_of_nonneg_left _ hX0
        exact hw.trans (mul_le_mul_of_nonneg_left hQpow hC0)
    _ = C * (X : ℝ) ^ (1 + ε) := by
        rw [Real.rpow_add (by linarith : (0 : ℝ) < X) 1 ε, Real.rpow_one]; ring

theorem norm_wq_le150 {q : ℕ} : ‖wq150 q‖ ≤ 1 / (Nat.totient q : ℝ) ^ 2 := by
  unfold wq150
  rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_intCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hm : |((moebius q : ℤ) : ℝ)| ≤ 1 := by
    have := abs_moebius_le_one (n := q)
    exact_mod_cast this
  have := pow_le_pow_left₀ (abs_nonneg _) hm 2
  simpa using this

/-- `∫_0^1 |W| ≤ X Σ_{q ≤ Q} (q + 1)/φ(q)²`. PROVED. -/
theorem integral_norm_WX_le150 (X : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖WX150 X α‖ ≤
      (X : ℝ) * ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2 := by
  have hTc : ∀ q a : ℕ, Continuous fun α : ℝ => ‖TX150 X (α - (a : ℝ) / q)‖ ^ 2 :=
    fun q a => ((continuous_TX150 X).comp (continuous_id.sub continuous_const)).norm.pow 2
  set R : ℝ → ℝ := fun α => ∑ q ∈ Finset.Icc 1 (Nat.sqrt X),
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (α - (a : ℝ) / q)‖ ^ 2 with hR
  have hRc : Continuous R := continuous_finsetSum _ fun q _ => continuous_finsetSum _ fun a _ =>
    continuous_const.mul (hTc q a)
  have hpt : ∀ α, ‖WX150 X α‖ ≤ R α := by
    intro α
    unfold WX150
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right norm_wq_le150 (by positivity)
  have hmono := intervalIntegral.integral_mono_on zero_le_one
    ((continuous_WX150 X).norm.intervalIntegrable (μ := volume) 0 1) (hRc.intervalIntegrable (μ := volume) 0 1)
    (fun α _ => hpt α)
  refine hmono.trans ?_
  have hIq : ∀ q ∈ Finset.Icc 1 (Nat.sqrt X), IntervalIntegrable (fun α =>
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (α - (a : ℝ) / q)‖ ^ 2) volume 0 1 :=
    fun q _ => (continuous_finsetSum _ fun a _ =>
      continuous_const.mul (hTc q a)).intervalIntegrable _ _
  rw [hR, intervalIntegral.integral_finsetSum hIq, Finset.mul_sum]
  refine Finset.sum_le_sum (fun q _ => ?_)
  have hIa : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), IntervalIntegrable
      (fun α => 1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (α - (a : ℝ) / q)‖ ^ 2) volume 0 1 :=
    fun a _ => (continuous_const.mul (hTc q a)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hIa]
  simp_rw [intervalIntegral.integral_const_mul, integral_norm_sq_TX_shift150]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤ (q : ℝ) + 1 := by
    have : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card ≤ q := by
      calc _ ≤ (Finset.range q).card := Finset.card_filter_le _ _
        _ = q := Finset.card_range q
    have h' : (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤ q := by
      exact_mod_cast this
    linarith
  have h0 : (0 : ℝ) ≤ 1 / (Nat.totient q : ℝ) ^ 2 * X := by positivity
  calc (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) *
        (1 / (Nat.totient q : ℝ) ^ 2 * X)
      ≤ ((q : ℝ) + 1) * (1 / (Nat.totient q : ℝ) ^ 2 * X) := mul_le_mul_of_nonneg_right hcard h0
    _ = (X : ℝ) * (((q : ℝ) + 1) / (Nat.totient q : ℝ) ^ 2) := by ring

/-- PROVED. `∫_0^1 |V² - W| ≪ X^{1+ε}`. -/
theorem integral_norm_VW_le150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∫ α in (0 : ℝ)..1, ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε) := by
  intro ε hε
  obtain ⟨C1, hC1⟩ := integral_norm_sq_VX_le150 ε hε
  obtain ⟨C2, _, hC2⟩ := X_mul_weight_le150 ε hε
  refine ⟨C1 + C2, fun X hX => ?_⟩
  set M := ∑ q ∈ Finset.Icc 1 (Nat.sqrt X),
      ‖((moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)‖ * X
  have hVM : ∀ α, ‖VX150 X α‖ ≤ M := norm_VX_le150 X
  have hV2int : IntervalIntegrable (fun α => ‖VX150 X α‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.of_bound (C := M ^ 2) ?_ (ae_of_all _ fun α => ?_)
    · exact ((measurable_VX150 X).norm.pow_const 2).aestronglyMeasurable.restrict
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hVM α) 2
  have hWint : IntervalIntegrable (fun α => ‖WX150 X α‖) volume 0 1 :=
    (continuous_WX150 X).norm.intervalIntegrable (μ := volume) 0 1
  have hgint : IntervalIntegrable (fun α => ‖VX150 X α ^ 2 - WX150 X α‖) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.mono' ((hV2int.add hWint).1) ?_ (ae_of_all _ fun α => ?_)
    · exact ((((measurable_VX150 X).pow_const 2).sub
        (continuous_WX150 X).measurable).norm).aestronglyMeasurable.restrict
    · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow]
  have hmono := intervalIntegral.integral_mono_on zero_le_one hgint (hV2int.add hWint)
    (fun α _ => by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow])
  rw [intervalIntegral.integral_add hV2int hWint] at hmono
  have h1 := hC1 X hX
  have h2 := (integral_norm_WX_le150 X).trans (hC2 X hX)
  calc _ ≤ _ := hmono
    _ ≤ C1 * (X : ℝ) ^ (1 + ε) + C2 * (X : ℝ) ^ (1 + ε) := by linarith
    _ = (C1 + C2) * (X : ℝ) ^ (1 + ε) := by ring

/-- PROVED. The interpolation `∫|g|² ≤ B ∫|g|` when `|g| ≤ B` on `[0, 1]`, for `g = V² - W`. -/
theorem integral_sq_VW_le_sup150 (X : ℕ) (B : ℝ)
    (hB : ∀ α ∈ Set.Icc (0 : ℝ) 1, ‖VX150 X α ^ 2 - WX150 X α‖ ≤ B) :
    ∫ α in (0 : ℝ)..1, ‖VX150 X α ^ 2 - WX150 X α‖ ^ 2 ≤
      B * ∫ α in (0 : ℝ)..1, ‖VX150 X α ^ 2 - WX150 X α‖ := by
  set M := ∑ q ∈ Finset.Icc 1 (Nat.sqrt X),
      ‖((moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)‖ * X
  have hVM : ∀ α, ‖VX150 X α‖ ≤ M := norm_VX_le150 X
  set MW := ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ∑ a ∈ (Finset.range q).filter
      (fun a => Nat.Coprime a q), ‖wq150 q‖ * (X : ℝ) ^ 2
  have hWM : ∀ α, ‖WX150 X α‖ ≤ MW := by
    intro α
    unfold WX150
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_TX_le150 _ _) 2)
      (norm_nonneg _)
  set g : ℝ → ℂ := fun α => VX150 X α ^ 2 - WX150 X α with hgdef
  have hgm : Measurable g := ((measurable_VX150 X).pow_const 2).sub (continuous_WX150 X).measurable
  have hgM : ∀ α, ‖g α‖ ≤ M ^ 2 + MW := by
    intro α
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow]
    have := pow_le_pow_left₀ (norm_nonneg _) (hVM α) 2
    linarith [hWM α]
  have hg1 : IntervalIntegrable (fun α => ‖g α‖) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.of_bound (C := M ^ 2 + MW) hgm.norm.aestronglyMeasurable.restrict
      (ae_of_all _ fun α => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hgM α
  have hg2 : IntervalIntegrable (fun α => ‖g α‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.of_bound (C := (M ^ 2 + MW) ^ 2)
      (hgm.norm.pow_const 2).aestronglyMeasurable.restrict (ae_of_all _ fun α => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgM α) 2
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one hg2 (hg1.const_mul B) (fun α hα => ?_)
  have h := hB α hα
  rw [sq]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

end LeanLab.BhowmikGrimmelt2026
