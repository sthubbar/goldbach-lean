module

public import Mathlib
public import LeanLab.ChenExplicit.Assembly

/-!
Run 20261017T1103Z-22220, unit U-0292. AI-written Lean code, Claude. Checked only by the Lean
kernel.

The twin prime constant `twinC = ∏_{p > 2} (1 - 1/(p-1)²) ≈ 0.66016` is at least `0.65`,
replacing the lab's earlier `twinC ≥ e⁻⁶`. Proof: the exact product over the 24 odd primes
below 100 is about 0.66138; the tail factor is at least `exp(-1.01/98)`, from
`log(1 - x) ≥ -x/(1 - x) ≥ -1.01 x` for `x ≤ 1/101` and `Σ_{n ≥ 100} 1/(n-1)² ≤ 1/98`.
-/

@[expose] public section

namespace LeanLab.ChenExplicit
open Real Finset

attribute [local instance] Classical.propDecidable

/-- The Euler factor at `n`. -/
noncomputable def gT (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) - 1) ^ 2

/-- Its log on odd primes, `0` elsewhere. -/
noncomputable def aT (n : ℕ) : ℝ := if n.Prime ∧ 2 < n then Real.log (gT n) else 0

lemma gT_pos {n : ℕ} (hn : 2 < n) : 0 < gT n := by
  unfold gT
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (2 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have : 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

lemma sum_head_tail_sq (N : ℕ) :
    ∑ n ∈ range N, 1 / ((n : ℝ) + 99) ^ 2 ≤ 1 / 98 - 1 / ((N : ℝ) + 98) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have key : 1 / ((N : ℝ) + 99) ^ 2 ≤ 1 / ((N : ℝ) + 98) - 1 / ((N : ℝ) + 1 + 98) := by
      rw [show (N : ℝ) + 1 + 98 = N + 99 by ring]
      rw [div_sub_div _ _ (by positivity) (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma tsum_tail_sq_le : ∑' n : ℕ, 1 / ((n : ℝ) + 99) ^ 2 ≤ 1 / 98 := by
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  have := sum_head_tail_sq N
  have : 0 ≤ 1 / ((N : ℝ) + 98) := by positivity
  linarith

lemma aT_tail_ge (n : ℕ) : -(101 / 100) * (1 / ((n : ℝ) + 99) ^ 2) ≤ aT (n + 100) := by
  unfold aT
  have hb : 0 ≤ 1 / ((n : ℝ) + 99) ^ 2 := by positivity
  split_ifs with hp
  · have hpos := gT_pos hp.2
    have h1 := Real.one_sub_inv_le_log_of_pos hpos
    set x := 1 / ((n : ℝ) + 99) ^ 2 with hx
    have hg : gT (n + 100) = 1 - x := by
      unfold gT; push_cast; rw [hx]; ring_nf
    rw [hg] at h1 hpos ⊢
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hx0 : 0 ≤ x := hb
    have hxs : x ≤ 1 / 101 := by
      rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h3 : (1 - x)⁻¹ ≤ 1 + 101 / 100 * x := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]; nlinarith
    linarith
  · nlinarith

lemma summable_aT : Summable aT := by
  have hs : Summable (fun n : ℕ => 2 * (1 / ((n : ℝ) - 1) ^ 2)) :=
    summable_inv_sub_one_sq.mul_left 2
  refine Summable.of_norm_bounded hs fun n => ?_
  unfold aT
  split_ifs with hp
  · have hpos := gT_pos hp.2
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hp.2
    set x := 1 / ((n : ℝ) - 1) ^ 2 with hx
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    have hx4 : x ≤ 1 / 4 := by
      rw [hx, div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
    have hg : gT n = 1 - x := rfl
    rw [hg] at hpos ⊢
    have hle : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    have h1 := Real.one_sub_inv_le_log_of_pos hpos
    have h3' : (1 - x)⁻¹ ≤ 1 + 2 * x := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]; nlinarith
    rw [Real.norm_eq_abs, abs_of_nonpos hle]
    linarith
  · simp only [norm_zero]; positivity

/-- The odd primes below `100`. -/
lemma head_filter : (range 100).filter (fun n => n.Prime ∧ 2 < n) =
    {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
      97} := by
  decide

lemma head_prod_ge : (6613 / 10000 : ℝ) ≤
    ∏ n ∈ (range 100).filter (fun n => n.Prime ∧ 2 < n), gT n := by
  rw [head_filter]
  simp only [gT]
  norm_num

/-- `exp` of the head sum is the head product. -/
lemma exp_head : Real.exp (∑ n ∈ range 100, aT n) =
    ∏ n ∈ (range 100).filter (fun n => n.Prime ∧ 2 < n), gT n := by
  unfold aT
  rw [← Finset.sum_filter, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro n hn
  exact Real.exp_log (gT_pos (mem_filter.mp hn).2.2)

/-- `twinC` as `exp` of the `ℕ`-indexed log sum. -/
lemma twinC_eq_exp : twinC = Real.exp (∑' n, aT n) := by
  set f : {p : ℕ // p.Prime ∧ 2 < p} → ℝ := fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2 with hf
  have hpos : ∀ p, 0 < f p := fun p => gT_pos p.2.2
  have hlog : Summable (fun p => Real.log (f p)) := by
    have := summable_aT.subtype {p : ℕ | p.Prime ∧ 2 < p}
    refine this.congr fun p => ?_
    show aT p.1 = _
    unfold aT; rw [if_pos (show Nat.Prime p.1 ∧ 2 < p.1 from p.2)]; rfl
  have hT : twinC = exp (∑' p, Real.log (f p)) := by
    rw [Real.rexp_tsum_eq_tprod hpos hlog]; rfl
  rw [hT]
  congr 1
  rw [show (∑' p, Real.log (f p)) = ∑' p : {p : ℕ | p.Prime ∧ 2 < p}, aT p from by
    apply tsum_congr; intro p; show _ = aT p.1; unfold aT; rw [if_pos (show Nat.Prime p.1 ∧ 2 < p.1 from p.2)]; rfl]
  rw [_root_.tsum_subtype]
  apply tsum_congr
  intro n
  simp only [Set.indicator_apply, Set.mem_setOf_eq, aT]
  split_ifs <;> rfl

/-- **The twin prime constant is at least `0.65`.** Fully proved. True value 0.66016. -/
theorem twinC_ge_065 : (65 / 100 : ℝ) ≤ twinC := by
  rw [twinC_eq_exp, ← summable_aT.sum_add_tsum_nat_add 100, Real.exp_add, exp_head]
  have htail : -(101 / 100) * (1 / 98 : ℝ) ≤ ∑' n, aT (n + 100) := by
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 99) ^ 2) := by
      have := (summable_nat_add_iff 100).mpr summable_inv_sub_one_sq
      refine this.congr fun n => ?_
      push_cast; ring_nf
    have h1 : ∑' n : ℕ, -(101 / 100) * (1 / ((n : ℝ) + 99) ^ 2) ≤ ∑' n, aT (n + 100) :=
      Summable.tsum_le_tsum aT_tail_ge (hs.mul_left _)
        ((summable_nat_add_iff 100).mpr summable_aT)
    rw [tsum_mul_left] at h1
    have h2 := tsum_tail_sq_le
    nlinarith
  have he : 1 + (-(101 / 100) * (1 / 98 : ℝ)) ≤ Real.exp (∑' n, aT (n + 100)) := by
    have := Real.add_one_le_exp (∑' n, aT (n + 100))
    linarith
  have hP := head_prod_ge
  have hP0 : (0 : ℝ) ≤ 6613 / 10000 := by norm_num
  calc (65 / 100 : ℝ) ≤ 6613 / 10000 * (1 + (-(101 / 100) * (1 / 98 : ℝ))) := by norm_num
    _ ≤ _ := mul_le_mul hP he (by norm_num) (hP0.trans hP)

lemma aT_nonpos (n : ℕ) : aT n ≤ 0 := by
  unfold aT
  split_ifs with hp
  · have hpos := gT_pos hp.2
    apply Real.log_nonpos hpos.le
    unfold gT
    have : 0 ≤ 1 / ((n : ℝ) - 1) ^ 2 := by
      have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hp.2
      have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      positivity
    linarith
  · exact le_rfl

lemma head_prod_le : ∏ n ∈ (range 100).filter (fun n => n.Prime ∧ 2 < n), gT n ≤
    (6614 / 10000 : ℝ) := by
  rw [head_filter]
  simp only [gT]
  norm_num

/-- **The twin prime constant is at most `0.6614`.** Fully proved. -/
theorem twinC_le_06614 : twinC ≤ (6614 / 10000 : ℝ) := by
  rw [twinC_eq_exp, ← summable_aT.sum_add_tsum_nat_add 100, Real.exp_add, exp_head]
  have ht : ∑' n, aT (n + 100) ≤ 0 := tsum_nonpos fun n => aT_nonpos _
  have he : Real.exp (∑' n, aT (n + 100)) ≤ 1 := Real.exp_le_one_iff.mpr ht
  have hP := head_prod_le
  have hP0 : 0 ≤ ∏ n ∈ (range 100).filter (fun n => n.Prime ∧ 2 < n), gT n :=
    prod_nonneg fun n hn => (gT_pos (mem_filter.mp hn).2.2).le
  calc _ ≤ (∏ n ∈ (range 100).filter (fun n => n.Prime ∧ 2 < n), gT n) * 1 :=
        mul_le_mul_of_nonneg_left he hP0
    _ ≤ _ := by linarith

/-- `0.65 ≤ twinC ≤ 0.6614`. -/
theorem twinC_bounds : (65 / 100 : ℝ) ≤ twinC ∧ twinC ≤ (6614 / 10000 : ℝ) :=
  ⟨twinC_ge_065, twinC_le_06614⟩

end LeanLab.ChenExplicit
