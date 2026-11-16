module

public import LeanLab.Pintz2018.Statements

/-!
The cumulative cap condition in Pintz 2018, page 19, displays 4.46 to 4.48.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.Pintz2018.Discrete117

/-- Cumulative costs of decreasing caps have decreasing increments.
Source: pages 18 and 19, displays 4.46 and 4.48. -/
theorem partial_sums_condition (e : ℕ → ℝ) (H : ℝ → ℝ)
    (he : Antitone e) (hH : Monotone H) :
    TheoremL_condition (fun m => ∑ j ∈ Finset.range m, H (e (j + 1))) := by
  intro m hm
  have hm1 : m - 1 + 1 = m := by omega
  have hprev : (∑ j ∈ Finset.range m, H (e (j + 1))) =
      (∑ j ∈ Finset.range (m - 1), H (e (j + 1))) + H (e m) := by
    conv_lhs => rw [← hm1, Finset.sum_range_succ]
    rw [hm1]
  dsimp only
  rw [Finset.sum_range_succ]
  have hinc := hH (he (Nat.le_succ m))
  linarith

/-- The sealed condition 4.48 makes the increment sequence decreasing after index two.
Source: page 19, display 4.48. -/
theorem increments_antitone (c : ℕ → ℝ) (hc : TheoremL_condition c) :
    AntitoneOn (fun m => c m - c (m - 1)) (Set.Ici 2) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro m hm
  simpa only [Nat.add_sub_cancel] using hc m hm

/-- Sharpness inside an equal contribution block forces sharpness at the preceding prefix.
Source: page 36, display 8.19, in the proof of Theorem L. -/
theorem sharp_equal_block (c a : ℕ → ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hc : TheoremL_condition c)
    (hprev : (∑ j ∈ Finset.range (m - 1), a j) ≤ c (m - 1))
    (hsharp : (∑ j ∈ Finset.range m, a j) = c m)
    (hnext : (∑ j ∈ Finset.range (m + 1), a j) ≤ c (m + 1))
    (hequal : a m = a (m - 1)) :
    (∑ j ∈ Finset.range (m - 1), a j) = c (m - 1) := by
  have hm1 : m - 1 + 1 = m := by omega
  have hs : (∑ j ∈ Finset.range (m - 1), a j) + a (m - 1) = ∑ j ∈ Finset.range m, a j := by
    simpa only [hm1] using (Finset.sum_range_succ a (m - 1)).symm
  have hn := Finset.sum_range_succ a m
  have hconc := hc m hm
  linarith

end LeanLab.Pintz2018.Discrete117
