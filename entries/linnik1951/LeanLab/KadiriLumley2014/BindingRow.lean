module

public import LeanLab.KadiriLumley2014.TableArithmetic

/-!
Kadiri and Lumley 2014, Table 2 and Corollary 1.2, arXiv 1407.7902v1 pages 2 and 13.
The certified ceiling is a limit of this sufficient condition, not a negative
statement about the actual locations of primes or Goldbach representations.
AI wrote this Lean code, Codex by OpenAI, 2026-10-25.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task64
open Real

/-- The first exponential threshold lies above the binary base. -/
theorem evenBase_lt_exp43 : (evenBase : ℝ) < Real.exp 43 := by
  calc
    (evenBase : ℝ) < (2.7182818283 : ℝ) ^ 43 := by norm_num [evenBase]
    _ ≤ Real.exp 1 ^ 43 := by gcongr; exact Real.exp_one_gt_d9.le
    _ = Real.exp 43 := by rw [← Real.exp_nat_mul]; norm_num

/-- Every printed threshold is admissible for the binary base. -/
theorem tableTwo_threshold_ge_base {r : PrintedRow} (hr : r ∈ tableTwo) :
    (evenBase : ℝ) ≤ r.threshold := by
  have hk : r.logIndex = 0 ∨ 43 ≤ r.logIndex := by
    have hall : ∀ s ∈ tableTwo, s.logIndex = 0 ∨ 43 ≤ s.logIndex := by decide +kernel
    exact hall r hr
  rcases hk with h0 | hk
  · simp [PrintedRow.threshold, h0]
  · have h0 : r.logIndex ≠ 0 := by omega
    simp only [PrintedRow.threshold, ite_eq_right h0]
    exact evenBase_lt_exp43.le.trans (Real.exp_le_exp.mpr (by exact_mod_cast hk))

/-- Every threshold through row 60 lies below 1.15 times 10^26. -/
theorem threshold_le_115e24 {r : PrintedRow} (hk : r.logIndex ≤ 60) :
    r.threshold ≤ 1.15 * 10 ^ 26 := by
  unfold PrintedRow.threshold
  split_ifs
  · norm_num [evenBase]
  · exact (Real.exp_le_exp.mpr (by exact_mod_cast hk)).trans exp60_le

/-- A stronger uniform overlap bound implies every successive ladder overlap
through row 60, including the jump directly from the first row to row 60. -/
theorem tableTwo_overlap {r s : PrintedRow} (hr : r ∈ tableTwo)
    (hs : s.logIndex ≤ 60) : s.threshold < (r.gapDenom : ℝ) * evenBase := by
  have hd : (36082898 : ℝ) ≤ r.gapDenom := by
    exact_mod_cast (tableTwo_denominators r hr).1
  have hnum : (1.15 : ℝ) * 10 ^ 26 < 36082898 * evenBase := by norm_num [evenBase]
  calc
    s.threshold ≤ 1.15 * 10 ^ 26 := threshold_le_115e24 hs
    _ < 36082898 * evenBase := hnum
    _ ≤ (r.gapDenom : ℝ) * evenBase := mul_le_mul_of_nonneg_right hd (by positivity)

/-- Even the last printed denominator times the odd base is below exp 150.
Thus row 150 cannot start a fresh ladder interval for either verification base. -/
theorem final_row_above_odd_reach :
    (2442159714 : ℝ) * oddBase < Real.exp 150 := by
  calc
    (2442159714 : ℝ) * oddBase < (2 : ℝ) ^ 150 := by norm_num [oddBase]
    _ ≤ Real.exp 1 ^ 150 := by gcongr; exact Real.exp_one_gt_two.le
    _ = Real.exp 150 := by rw [← Real.exp_nat_mul]; norm_num

/-- An active row has a nonempty real interval before its sufficient ceiling. -/
def ActiveRow (r : PrintedRow) : Prop :=
  r.threshold < (r.gapDenom : ℝ) * evenBase

/-- Precisely the first nineteen rows have nonempty certified ranges. -/
theorem active_iff_index_le60 {r : PrintedRow} (hr : r ∈ tableTwo) :
    ActiveRow r ↔ r.logIndex ≤ 60 := by
  constructor
  · intro ha
    rcases (tableTwo_denominators r hr).2.2 with hsmall | hlast
    · exact hsmall.1
    · obtain ⟨hk, hd⟩ := hlast
      have ht : r.threshold = Real.exp 150 := by simp [PrintedRow.threshold, hk]
      have hbase : (evenBase : ℝ) ≤ oddBase := by norm_num [evenBase, oddBase]
      have hu : (r.gapDenom : ℝ) * evenBase < r.threshold := by
        rw [ht, hd]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hbase (by norm_num))
          final_row_above_odd_reach
      exact False.elim ((not_lt_of_ge hu.le) ha)
  · intro hk
    exact tableTwo_overlap hr hk

/-- Row 60 attains the largest denominator among active rows. -/
theorem binding_row60 {r : PrintedRow} (hr : r ∈ tableTwo) (ha : ActiveRow r) :
    r.gapDenom ≤ 1966196911 := by
  have hk := (active_iff_index_le60 hr).mp ha
  rcases (tableTwo_denominators r hr).2.2 with hsmall | hlast
  · exact hsmall.2
  · omega

/-- Row 60 is itself active, so the bound is attained. -/
theorem binding_row60_attained :
    ∃ r ∈ tableTwo, ActiveRow r ∧ r.gapDenom = 1966196911 := by
  refine ⟨⟨60, 61, 4588, 20504393735, 93, 4527, 1966196911⟩, row60_mem, ?_, rfl⟩
  exact (active_iff_index_le60 row60_mem).mpr (by decide)

/-- Each row step is obtained from its own cited interval inequality.
No row is inferred from a larger denominator without an interval hypothesis. -/
theorem tableTwo_step (hrows : TableTwoIntervals) (hE : EvenGoldbachUpTo evenBase)
    {r : PrintedRow} (hr : r ∈ tableTwo) {n : ℕ} (hn : Odd n)
    (hlo : r.threshold + 3 < n) (hhi : (n : ℝ) < r.gapDenom * evenBase) :
    IsTernarySum n := by
  have hd : (2 : ℝ) ≤ r.gapDenom := by exact_mod_cast (tableTwo_parameters r hr).2.2.2.2.2.2.2.2
  exact ternary_of_row (hrows r hr) (tableTwo_threshold_ge_base hr) hd hE hn hlo hhi

/-- All table based sufficient ranges are contained in the named odd verification.
This conclusion concerns the sufficient condition, not all uses of Theorem 1.1. -/
theorem no_table_step_above_hp {r : PrintedRow} (hr : r ∈ tableTwo) {n : ℕ}
    (hn : oddBase < n) : ¬ ((n : ℝ) < r.gapDenom * evenBase) := by
  have hcap : (r.gapDenom : ℝ) * evenBase < oddBase := by
    exact_mod_cast tableTwo_reach_lt_oddBase r hr
  have hn' : (oddBase : ℝ) < n := by exact_mod_cast hn
  linarith

/-- The cited odd base contains every output of the printed three prime ladder. -/
theorem ternary_row_is_already_in_hp (hHP : HelfgottPlattBase)
    {r : PrintedRow} (hr : r ∈ tableTwo) {n : ℕ} (hn : Odd n) (h7 : 7 ≤ n)
    (hhi : (n : ℝ) < r.gapDenom * evenBase) : IsTernarySum n := by
  apply hHP n hn h7
  by_contra hh
  exact no_table_step_above_hp hr (by omega) hhi

/-- Exact ceiling of the active table ladder and its strict comparison to HP. -/
theorem binding_ceiling :
    1966196911 * evenBase = 7864787644000000000000000000 ∧
    1966196911 * evenBase < oddBase := by
  norm_num [evenBase, oddBase]

end LeanLab.KadiriLumley2014.Task64
