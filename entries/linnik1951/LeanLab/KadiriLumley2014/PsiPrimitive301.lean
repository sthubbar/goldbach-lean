module

public import LeanLab.KadiriLumley2014.PsiFinite301
public import LeanLab.KadiriLumley2014.WeightDerivative
public import LeanLab.Dudek2014.Lemma5

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4, the weighted explicit formula transfer.
The standard psi-one primitive is the finite sum used in Dudek2014.Lemma5.
These elementary primitive identities do not assume an explicit zero formula.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task301

open Real Set MeasureTheory Filter Topology
open Task64
open LeanLab.Dudek2014.Section22 (psi1 psi1_ext)

/-- The positive part of y minus a has right derivative one at and above a, zero below a. -/
theorem positivePart_hasDerivWithinAt_right (a x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => max (y - a) 0) (if a ≤ x then 1 else 0) (Ioi x) x := by
  by_cases ha : a ≤ x
  · rw [if_pos ha]
    have hd : HasDerivWithinAt (fun y : ℝ => y - a) 1 (Ioi x) x := by
      simpa using ((hasDerivAt_id x).sub_const a).hasDerivWithinAt (s := Ioi x)
    apply hd.congr (fun y hy => max_eq_left (by
      change x < y at hy
      linarith : 0 ≤ y - a))
    exact max_eq_left (sub_nonneg.mpr ha)
  · rw [if_neg ha]
    have hxa : x < a := lt_of_not_ge ha
    have hd : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Ioi x) x :=
      (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
    apply hd.congr_of_eventuallyEq ?_ (max_eq_right (by linarith : x - a ≤ 0))
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hxa)] with y hy
    change y < a at hy
    exact max_eq_right (by linarith : y - a ≤ 0)

/-- The standard psi-one finite sum has right derivative psi at every positive point. -/
theorem psi1_hasDerivWithinAt_right {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt psi1 (Chebyshev.psi x) (Ioi x) x := by
  classical
  let N : ℕ := ⌊x⌋₊ + 2
  have hxN : x < N := by
    have h := Nat.lt_floor_add_one x
    dsimp [N]
    push_cast
    linarith
  have hfin : HasDerivWithinAt
      (fun y : ℝ => ∑ n ∈ Finset.Iic N, max (y - n) 0 * ArithmeticFunction.vonMangoldt n)
      (∑ n ∈ Finset.Iic N, (if (n : ℝ) ≤ x then 1 else 0) * ArithmeticFunction.vonMangoldt n)
      (Ioi x) x := by
    apply HasDerivWithinAt.fun_sum
    intro n _
    exact (positivePart_hasDerivWithinAt_right (n : ℝ) x).mul_const _
  have hderiv : (∑ n ∈ Finset.Iic N,
      (if (n : ℝ) ≤ x then 1 else 0) * ArithmeticFunction.vonMangoldt n) = Chebyshev.psi x := by
    simp_rw [ite_mul, one_mul, zero_mul]
    have heq : Finset.Iic N = Finset.Icc 0 N := by ext n; simp
    rw [heq, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le N)]
    simpa using (psi_eq_fixed_sum hx.le hxN.le).symm
  rw [hderiv] at hfin
  apply hfin.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hx),
      nhdsWithin_le_nhds (Iio_mem_nhds hxN)] with y hy0 hyN
    change 0 < y at hy0
    change y < (N : ℝ) at hyN
    apply (psi1_ext hy0.le ?_).symm
    simpa using Nat.floor_mono hyN.le
  · apply (psi1_ext hx.le ?_).symm
    simpa using Nat.floor_mono hxN.le

/-- On any positive bounded interval, psi one agrees with a continuous finite positive-part sum. -/
theorem psi1_continuousOn_Icc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ContinuousOn psi1 (Icc a b) := by
  classical
  let N : ℕ := ⌈b⌉₊
  have hbN : b ≤ N := Nat.le_ceil b
  have hc : Continuous (fun y : ℝ => ∑ n ∈ Finset.Iic N,
      max (y - n) 0 * ArithmeticFunction.vonMangoldt n) := by
    fun_prop
  apply hc.continuousOn.congr
  intro y hy
  apply (psi1_ext (ha.trans hy.1) ?_).symm
  have hyN : y ≤ N := hy.2.trans hbN
  simpa using Nat.floor_mono hyN

end LeanLab.KadiriLumley2014.Task301
