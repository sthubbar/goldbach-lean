module

public import LeanLab.KadiriLumley2014.Decomp92
public import LeanLab.KadiriLumley2014.Kernel259
public import LeanLab.KadiriLumley2014.BindingRow

/-!
Kadiri and Lumley 2014, the absolute sum over the nontrivial zeros of ζ in equation 2.19 of the
paper. The weighted zero series inside `zeroError` is summable for every positive degree `m`,
positive `δ`, `u` and `X`, so `zeroError` is its true sum. In particular this holds at every
Table 2 row at the normalized `X` where display 2.64 is asked, so the display 2.64 hypotheses of
the compared theorems carry the full zero contribution. The proof uses the zero counting bound
behind the convergent explicit formula for ψ. AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.PalomarSummable
open Real
open LeanLab.KadiriLumley2014.Task64 LeanLab.KadiriLumley2014.Task92

/-- For positive degree `m` and positive `δ`, `u`, `X`, the weighted zero series of equation
2.19 is summable and `zeroError m δ u X` is its sum. -/
theorem zeroError_hasSum {m : ℕ} (hm : 0 < m) {δ u X : ℝ}
    (hδ : 0 < δ) (hu : 0 < u) (hX : 0 < X) :
    HasSum (zeroSummand m δ u X) (zeroError m δ u X) :=
  (Task259.absolute_zero_summable hm hδ hu hX).hasSum

/-- At every row of Table 2, the weighted zero series of equation 2.19 at the row's normalized
`X`, the point where display 2.64 is asked, is summable and `zeroError` there is its sum. -/
theorem row_zeroError_hasSum {r : PrintedRow} (hr : r ∈ tableTwo) :
    HasSum (zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r))
      (zeroError r.m r.deltaQ r.uQ (rowEndpointX r)) := by
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hu : (0 : ℝ) < r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    have h0 : (0 : ℝ) < ((1 / 10 ^ 12 : ℚ) : ℝ) := by norm_num
    exact h0.trans_le h
  have hm : 0 < r.m := by
    have hall : ∀ s ∈ tableTwo, 0 < s.m := by decide +kernel
    exact hall r hr
  have hbase := tableTwo_threshold_ge_base hr
  have hth : 0 < r.threshold := lt_of_lt_of_le (by norm_num [evenBase]) hbase
  have hX : 0 < rowEndpointX r := by
    unfold rowEndpointX
    positivity
  exact zeroError_hasSum hm hδ hu hX

end LeanLab.KadiriLumley2014.PalomarSummable
