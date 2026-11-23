module

public import Mathlib

/-!
ArcCross520: replacing a continuous function by a model inside a squared arc integral.

Pure Mathlib real analysis, no lab imports.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory

/-- Standard analysis, the Cauchy Schwarz step of P0093 page 160 equation 5.3 in its weighted
arithmetic geometric mean form, split at an inner radius. The square of `P` is replaced by the
square of the model `L` on the arc of radius `δ`; the cross term is bounded with the sup bound
`S` outside the inner radius `ξ` and with the weight `lam` inside it. -/
theorem arc_square_replace520 (P L : ℝ → ℂ) (hP : Continuous P) (hL : Continuous L)
    (φ : ℝ → ℂ) (hφc : Continuous φ) (hφ : ∀ z, ‖φ z‖ = 1)
    (δ ξ lam A B Mass S : ℝ) (hξ : 0 < ξ) (hξδ : ξ ≤ δ) (hlam : 0 < lam)
    (hA : (∫ z in -δ..δ, ‖P z - L z‖ ^ 2) ≤ A)
    (hB : (∫ z in -ξ..ξ, ‖P z - L z‖ ^ 2) ≤ B)
    (hMass : (∫ z in -ξ..ξ, ‖L z‖ ^ 2) ≤ Mass)
    (hS : ∀ z : ℝ, ξ ≤ |z| → |z| ≤ δ → ‖L z‖ ^ 2 ≤ S) :
    ‖(∫ z in -δ..δ, P z ^ 2 * φ z) - (∫ z in -δ..δ, L z ^ 2 * φ z)‖ ≤
      3 * A + 2 * S * δ + lam * B + Mass / lam := by
  have hδ : 0 < δ := lt_of_lt_of_le hξ hξδ
  have hfc : Continuous fun z => ‖P z - L z‖ ^ 2 := by fun_prop
  have hgc : Continuous fun z => 2 * ‖P z - L z‖ * ‖L z‖ := by fun_prop
  have hLc : Continuous fun z => ‖L z‖ ^ 2 := by fun_prop
  have hfi : ∀ a b : ℝ, IntervalIntegrable (fun z => ‖P z - L z‖ ^ 2) volume a b :=
    fun a b => hfc.intervalIntegrable a b
  have hgi : ∀ a b : ℝ, IntervalIntegrable (fun z => 2 * ‖P z - L z‖ * ‖L z‖) volume a b :=
    fun a b => hgc.intervalIntegrable a b
  have hLi : ∀ a b : ℝ, IntervalIntegrable (fun z => ‖L z‖ ^ 2) volume a b :=
    fun a b => hLc.intervalIntegrable a b
  -- step 1: pointwise bound of the difference
  have h1 : ‖(∫ z in -δ..δ, P z ^ 2 * φ z) - (∫ z in -δ..δ, L z ^ 2 * φ z)‖ ≤
      ∫ z in -δ..δ, (‖P z - L z‖ ^ 2 + 2 * ‖P z - L z‖ * ‖L z‖) := by
    rw [← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun z => P z ^ 2 * φ z).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun z => L z ^ 2 * φ z).intervalIntegrable _ _)]
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans ?_
    refine intervalIntegral.integral_mono_on (by linarith)
      ((by fun_prop : Continuous fun z => ‖P z ^ 2 * φ z - L z ^ 2 * φ z‖).intervalIntegrable _ _)
      ((hfc.add hgc).intervalIntegrable _ _) ?_
    intro z _
    have e : P z ^ 2 * φ z - L z ^ 2 * φ z = (P z - L z) * ((P z - L z) + 2 * L z) * φ z := by
      ring
    rw [e, norm_mul, norm_mul, hφ, mul_one]
    have h2 : ‖(P z - L z) + 2 * L z‖ ≤ ‖P z - L z‖ + 2 * ‖L z‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      simp
    nlinarith [norm_nonneg (P z - L z), norm_nonneg (L z)]
  rw [intervalIntegral.integral_add (hfi _ _) (hgi _ _)] at h1
  -- split
  have sf : (∫ z in -δ..δ, ‖P z - L z‖ ^ 2) =
      (∫ z in -δ..-ξ, ‖P z - L z‖ ^ 2) + (∫ z in -ξ..ξ, ‖P z - L z‖ ^ 2) +
        (∫ z in ξ..δ, ‖P z - L z‖ ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _),
      intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _)]
  have sg : (∫ z in -δ..δ, 2 * ‖P z - L z‖ * ‖L z‖) =
      (∫ z in -δ..-ξ, 2 * ‖P z - L z‖ * ‖L z‖) + (∫ z in -ξ..ξ, 2 * ‖P z - L z‖ * ‖L z‖) +
        (∫ z in ξ..δ, 2 * ‖P z - L z‖ * ‖L z‖) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _),
      intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _)]
  have fnn : ∀ a b : ℝ, a ≤ b → 0 ≤ ∫ z in a..b, ‖P z - L z‖ ^ 2 := fun a b hab =>
    intervalIntegral.integral_nonneg hab (fun z _ => by positivity)
  have hSnn : 0 ≤ S :=
    (sq_nonneg _).trans (hS δ (by rw [abs_of_pos hδ]; exact hξδ) (by rw [abs_of_pos hδ]))
  -- outer pieces
  have outer : ∀ a b : ℝ, a ≤ b → (∀ z ∈ Set.Icc a b, ξ ≤ |z| ∧ |z| ≤ δ) →
      (∫ z in a..b, 2 * ‖P z - L z‖ * ‖L z‖) ≤ (∫ z in a..b, ‖P z - L z‖ ^ 2) + S * (b - a) := by
    intro a b hab h
    have : (∫ z in a..b, ‖P z - L z‖ ^ 2) + S * (b - a) =
        ∫ z in a..b, (‖P z - L z‖ ^ 2 + S) := by
      rw [intervalIntegral.integral_add (hfi _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [this]
    refine intervalIntegral.integral_mono_on hab (hgi _ _)
      ((hfc.add continuous_const).intervalIntegrable _ _) ?_
    intro z hz
    have := hS z (h z hz).1 (h z hz).2
    nlinarith [sq_nonneg (‖P z - L z‖ - ‖L z‖)]
  have o1 := outer (-δ) (-ξ) (by linarith) (by
    intro z hz
    rw [abs_of_nonpos (by linarith [hz.2])]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩)
  have o2 := outer ξ δ hξδ (by
    intro z hz
    rw [abs_of_nonneg (by linarith [hz.1])]
    exact ⟨hz.1, hz.2⟩)
  -- inner piece
  have inner : (∫ z in -ξ..ξ, 2 * ‖P z - L z‖ * ‖L z‖) ≤
      lam * (∫ z in -ξ..ξ, ‖P z - L z‖ ^ 2) + (∫ z in -ξ..ξ, ‖L z‖ ^ 2) / lam := by
    have : lam * (∫ z in -ξ..ξ, ‖P z - L z‖ ^ 2) + (∫ z in -ξ..ξ, ‖L z‖ ^ 2) / lam =
        ∫ z in -ξ..ξ, (lam * ‖P z - L z‖ ^ 2 + ‖L z‖ ^ 2 / lam) := by
      rw [intervalIntegral.integral_add ((hfi _ _).const_mul lam) ((hLi _ _).div_const lam),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
    rw [this]
    refine intervalIntegral.integral_mono_on (by linarith) (hgi _ _)
      (((hfi _ _).const_mul lam).add ((hLi _ _).div_const lam)) ?_
    intro z _
    have key : 2 * ‖P z - L z‖ * ‖L z‖ * lam ≤
        (lam * ‖P z - L z‖ ^ 2 + ‖L z‖ ^ 2 / lam) * lam := by
      have : (lam * ‖P z - L z‖ ^ 2 + ‖L z‖ ^ 2 / lam) * lam =
          lam ^ 2 * ‖P z - L z‖ ^ 2 + ‖L z‖ ^ 2 := by
        field_simp
      rw [this]
      nlinarith [sq_nonneg (lam * ‖P z - L z‖ - ‖L z‖)]
    exact le_of_mul_le_mul_right key hlam
  have hBl : lam * (∫ z in -ξ..ξ, ‖P z - L z‖ ^ 2) ≤ lam * B :=
    mul_le_mul_of_nonneg_left hB hlam.le
  have hMl : (∫ z in -ξ..ξ, ‖L z‖ ^ 2) / lam ≤ Mass / lam :=
    div_le_div_of_nonneg_right hMass hlam.le
  have n0 := fnn (-ξ) ξ (by linarith)
  have hSξ : 0 ≤ S * ξ := mul_nonneg hSnn hξ.le
  have hAnn : 0 ≤ A := (fnn (-δ) δ (by linarith)).trans hA
  nlinarith

end LeanLab.Linnik1951
