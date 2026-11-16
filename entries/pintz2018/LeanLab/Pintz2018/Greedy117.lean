module

public import LeanLab.Pintz2018.Curvature117

/-!
The elementary saturation conclusion of Theorem K in its weighted integral model.
Source: Pintz 2018, pages 34 and 35, displays 8.10 to 8.16.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.Pintz2018.Greedy117
open MeasureTheory

/-- The saturation part of Theorem K with both curvature hypotheses proved.
The objective is the paper's power difference and the cost is the integral in 8.11. -/
theorem power_integral_saturation (J r : ℕ) (y Y : ℕ → ℝ) (w : ℝ → ℝ)
    (b c budget : ℝ) (hb : 1 < b) (hc : 0 ≤ c) (hcb : c < b)
    (hw : ContinuousOn w (Set.Icc 0 1)) (hw0 : ∀ v ∈ Set.Icc 0 1, 0 ≤ w v)
    (hr : r ∈ Finset.Icc 1 J) (hmono : AntitoneOn y (Set.Icc 1 J))
    (hY : AntitoneOn Y (Set.Icc 1 J))
    (hbox : ∀ j ∈ Finset.Icc 1 J, 1 ≤ y j ∧ y j ≤ Y j)
    (hactive : 1 < y r) (htail : ∀ j ∈ Set.Icc 1 J, r < j → y j = 1)
    (hbudget : (∑ j ∈ Finset.Icc 1 J,
      ∫ v in Set.Icc (0 : ℝ) 1, w v * (y j) ^ v) ≤ budget)
    (hmax : ∀ z : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 J, 1 ≤ z j ∧ z j ≤ Y j) →
      AntitoneOn z (Set.Icc 1 J) →
      (∑ j ∈ Finset.Icc 1 J, ∫ v in Set.Icc (0 : ℝ) 1, w v * (z j) ^ v) ≤ budget →
      (∑ j ∈ Finset.Icc 1 J, ((z j) ^ b - (z j) ^ c)) ≤
        ∑ j ∈ Finset.Icc 1 J, ((y j) ^ b - (y j) ^ c)) :
    TheoremK_OptimalChoice r y Y := by
  exact Ordered117.saturation_ordered J r y Y
    (fun y => ∫ v in Set.Icc (0 : ℝ) 1, w v * y ^ v)
    (fun y => y ^ b - y ^ c) budget hr
    (Curvature117.integral_cost_concave w hw hw0)
    (Curvature117.objective_strictConvex b c hb hc hcb)
    hmono hY hbox hactive htail hbudget hmax

/-- The exponential substitution 8.10 turns each exponential objective term into a power. -/
theorem exp_coordinate_power (d T B : ℝ) (hT : 0 < T) :
    (Real.exp (d * T)) ^ (B / T) = Real.exp (B * d) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp

/-- The exact cited saturation Prop in the original exponential coordinates.
Source: page 18, display 4.41, proved through pages 34 and 35, displays 8.10 to 8.16.
The cost is the continuous nonnegative weighted integral representation in 8.11. -/
theorem theoremK_ordered_integral (J r : ℕ) (d e : ℕ → ℝ) (w : ℝ → ℝ)
    (T B C budget : ℝ) (hT : 0 < T) (hB : T < B) (hC : 0 ≤ C) (hCB : C < B)
    (hw : ContinuousOn w (Set.Icc 0 1)) (hw0 : ∀ v ∈ Set.Icc 0 1, 0 ≤ w v)
    (hr : r ∈ Finset.Icc 1 J) (hd : AntitoneOn d (Set.Icc 1 J))
    (he : AntitoneOn e (Set.Icc 1 J))
    (hbox : ∀ j ∈ Finset.Icc 1 J, 0 ≤ d j ∧ d j ≤ e j)
    (hactive : 0 < d r) (htail : ∀ j ∈ Set.Icc 1 J, r < j → d j = 0)
    (hbudget : (∑ j ∈ Finset.Icc 1 J,
      ∫ v in Set.Icc (0 : ℝ) 1, w v * (Real.exp (d j * T)) ^ v) ≤ budget)
    (hmax : ∀ x : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 J, 0 ≤ x j ∧ x j ≤ e j) →
      AntitoneOn x (Set.Icc 1 J) →
      (∑ j ∈ Finset.Icc 1 J, ∫ v in Set.Icc (0 : ℝ) 1,
        w v * (Real.exp (x j * T)) ^ v) ≤ budget →
      (∑ j ∈ Finset.Icc 1 J, (Real.exp (B * x j) - Real.exp (C * x j))) ≤
        ∑ j ∈ Finset.Icc 1 J, (Real.exp (B * d j) - Real.exp (C * d j))) :
    TheoremK_OptimalChoice r d e := by
  have hy : AntitoneOn (fun j => Real.exp (d j * T)) (Set.Icc 1 J) := by
    intro i hi j hj hij
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hd hi hj hij) hT.le)
  have hY : AntitoneOn (fun j => Real.exp (e j * T)) (Set.Icc 1 J) := by
    intro i hi j hj hij
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (he hi hj hij) hT.le)
  have hybox : ∀ j ∈ Finset.Icc 1 J,
      1 ≤ Real.exp (d j * T) ∧ Real.exp (d j * T) ≤ Real.exp (e j * T) := by
    intro j hj
    exact ⟨Real.one_le_exp_iff.mpr (mul_nonneg (hbox j hj).1 hT.le),
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hbox j hj).2 hT.le)⟩
  have hyactive : 1 < Real.exp (d r * T) := Real.one_lt_exp_iff.mpr (mul_pos hactive hT)
  have hytail : ∀ j ∈ Set.Icc 1 J, r < j → Real.exp (d j * T) = 1 := by
    intro j hj hrj
    rw [htail j hj hrj, zero_mul, Real.exp_zero]
  have htransmax : ∀ z : ℕ → ℝ,
      (∀ j ∈ Finset.Icc 1 J, 1 ≤ z j ∧ z j ≤ Real.exp (e j * T)) →
      AntitoneOn z (Set.Icc 1 J) →
      (∑ j ∈ Finset.Icc 1 J, ∫ v in Set.Icc (0 : ℝ) 1, w v * (z j) ^ v) ≤ budget →
      (∑ j ∈ Finset.Icc 1 J, ((z j) ^ (B / T) - (z j) ^ (C / T))) ≤
        ∑ j ∈ Finset.Icc 1 J,
          ((Real.exp (d j * T)) ^ (B / T) - (Real.exp (d j * T)) ^ (C / T)) := by
    intro z hz hzm hzbudget
    let x := fun j => Real.log (z j) / T
    have hzpos : ∀ j ∈ Finset.Icc 1 J, 0 < z j := by
      intro j hj
      exact lt_of_lt_of_le zero_lt_one (hz j hj).1
    have hxbox : ∀ j ∈ Finset.Icc 1 J, 0 ≤ x j ∧ x j ≤ e j := by
      intro j hj
      exact ⟨div_nonneg (Real.log_nonneg (hz j hj).1) hT.le,
        (div_le_iff₀ hT).mpr ((Real.log_le_iff_le_exp (hzpos j hj)).mpr (hz j hj).2)⟩
    have hxm : AntitoneOn x (Set.Icc 1 J) := by
      intro i hi j hj hij
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (hzpos j (Finset.mem_Icc.mpr hj)) (hzm hi hj hij)) hT.le
    have hxp : ∀ j ∈ Finset.Icc 1 J, Real.exp (x j * T) = z j := by
      intro j hj
      dsimp [x]
      rw [div_mul_cancel₀ _ hT.ne', Real.exp_log (hzpos j hj)]
    have hxbudget : (∑ j ∈ Finset.Icc 1 J,
        ∫ v in Set.Icc (0 : ℝ) 1, w v * (Real.exp (x j * T)) ^ v) ≤ budget := by
      convert hzbudget using 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [hxp j hj]
    calc
      (∑ j ∈ Finset.Icc 1 J, ((z j) ^ (B / T) - (z j) ^ (C / T))) =
          ∑ j ∈ Finset.Icc 1 J, (Real.exp (B * x j) - Real.exp (C * x j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← hxp j hj, exp_coordinate_power (x j) T B hT, exp_coordinate_power (x j) T C hT]
      _ ≤ ∑ j ∈ Finset.Icc 1 J, (Real.exp (B * d j) - Real.exp (C * d j)) :=
        hmax x hxbox hxm hxbudget
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [exp_coordinate_power (d j) T B hT, exp_coordinate_power (d j) T C hT]
  have hsat := power_integral_saturation J r
    (fun j => Real.exp (d j * T)) (fun j => Real.exp (e j * T)) w (B / T) (C / T) budget
    ((one_lt_div hT).mpr hB) (div_nonneg hC hT.le) ((div_lt_div_iff_of_pos_right hT).mpr hCB)
    hw hw0 hr hy hY hybox hyactive hytail hbudget htransmax
  intro j hj hjr
  exact Decomp117b.leaf_exp_coordinates T (d j) (e j) hT (hsat j hj hjr)

end LeanLab.Pintz2018.Greedy117
