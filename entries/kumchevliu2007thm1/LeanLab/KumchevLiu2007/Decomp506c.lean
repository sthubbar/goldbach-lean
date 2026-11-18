module

public import LeanLab.KumchevLiu2007.Decomp506bBase
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Elementary distribution algebra and parameter margins for page 17 display 58.
These theorems do not supply the cited prime distribution or sieve weights.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Task506c

open Real Task506b
open scoped BigOperators Topology

/-- Page 17 Cauchy step with the reciprocal modulus weight retained. -/
theorem cauchy_progression_errors {ι : Type*} (s : Finset ι) (w E d : ι → ℝ)
    (M T V : ℝ) (hd : ∀ i ∈ s, 0 < d i) (hE : ∀ i ∈ s, 0 ≤ E i)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hpoint : ∀ i ∈ s, d i * E i ≤ M)
    (hmoment : ∑ i ∈ s, w i ^ 2 / d i ≤ T) (hBV : ∑ i ∈ s, E i ≤ V) :
    (∑ i ∈ s, w i * E i) ^ 2 ≤ T * M * V := by
  have hc : (∑ i ∈ s, w i * E i) ^ 2 ≤
      (∑ i ∈ s, w i ^ 2 / d i) * ∑ i ∈ s, d i * E i ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i hi => div_nonneg (sq_nonneg _) (hd i hi).le)
      (fun i hi => mul_nonneg (hd i hi).le (sq_nonneg _))
    intro i hi
    apply le_of_eq
    field_simp [(hd i hi).ne']
    <;> ring
  have hsecond : (∑ i ∈ s, d i * E i ^ 2) ≤ M * V := by
    calc _ ≤ ∑ i ∈ s, M * E i := by
           apply Finset.sum_le_sum
           intro i hi
           nlinarith [mul_le_mul_of_nonneg_right (hpoint i hi) (hE i hi)]
         _ = M * ∑ i ∈ s, E i := by rw [Finset.mul_sum]
         _ ≤ M * V := mul_le_mul_of_nonneg_left hBV hM
  have hnonneg : 0 ≤ ∑ i ∈ s, d i * E i ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hd i hi).le (sq_nonneg _)
  exact hc.trans (by simpa only [mul_assoc] using mul_le_mul hmoment hsecond hnonneg hT)

/-- Page 17, D equal to Y to one ninth fits below Y to one eighth with every fixed log loss. -/
theorem sieve_level_margin (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      Y X ε ^ (1 / 9 : ℝ) ≤ Y X ε ^ (1 / 8 : ℝ) * Real.log X ^ (-C) := by
  have ha : 0 < (7 / 12 + ε / 2) / 72 := by linarith
  have hb := (isLittleO_log_rpow_rpow_atTop C ha).bound zero_lt_one
  filter_upwards [hb, Filter.eventually_gt_atTop (1 : ℝ)] with X hb hX
  have hXp : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX
  have hY : 0 < Y X ε := Real.rpow_pos_of_pos hXp _
  have hbound : Real.log X ^ C ≤ X ^ ((7 / 12 + ε / 2) / 72) := by
    simpa only [one_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL C),
      abs_of_pos (Real.rpow_pos_of_pos hXp _)] using hb
  have hpower : Y X ε ^ (1 / 72 : ℝ) = X ^ ((7 / 12 + ε / 2) / 72) := by
    unfold Y
    rw [← Real.rpow_mul hXp.le]
    congr 1
    ring
  have hsplit : Y X ε ^ (1 / 8 : ℝ) = Y X ε ^ (1 / 9 : ℝ) * Y X ε ^ (1 / 72 : ℝ) := by
    rw [← Real.rpow_add hY]
    norm_num
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hL C), hsplit]
  exact mul_le_mul_of_nonneg_left (hbound.trans_eq hpower.symm) (Real.rpow_nonneg hY.le _)

/-- Page 13 Lemma 3.7 and page 17 display 58, the chosen sieve level eventually exceeds z. -/
theorem sieve_cutoff_below_level (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      2 ≤ Real.exp (Real.log X ^ (1 - δ / 2)) ∧
      Real.exp (Real.log X ^ (1 - δ / 2)) ≤ Y X ε ^ (1 / 9 : ℝ) := by
  let a : ℝ := (7 / 12 + ε / 2) / 9
  have ha : 0 < a := by dsimp [a]; linarith
  have ht := (tendsto_rpow_atTop (show 0 < δ / 2 by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (Filter.eventually_ge_atTop (1 / a)),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_gt_atTop (1 : ℝ)] with X hb hL1 hX
  have hXp : 0 < X := by linarith
  have hL : 0 < Real.log X := by linarith
  have hY : 0 < Y X ε := Real.rpow_pos_of_pos hXp _
  have hsplit : Real.log X ^ (δ / 2) * Real.log X ^ (1 - δ / 2) = Real.log X := by
    rw [← Real.rpow_add hL]
    norm_num
  change 1 / a ≤ Real.log X ^ (δ / 2) at hb
  have hab : 1 ≤ a * Real.log X ^ (δ / 2) := by
    have hh := (div_le_iff₀ ha).mp hb
    nlinarith
  have hexp : Real.log X ^ (1 - δ / 2) ≤ a * Real.log X := by
    nlinarith [mul_le_mul_of_nonneg_right hab
      (Real.rpow_nonneg hL.le (1 - δ / 2))]
  have hone : 1 ≤ Real.log X ^ (1 - δ / 2) :=
    Real.one_le_rpow hL1 (by linarith)
  refine ⟨(by linarith [Real.add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ Real.exp 1).trans
    (Real.exp_le_exp.mpr hone), ?_⟩
  rw [← Real.exp_log (Real.rpow_pos_of_pos hY (1 / 9 : ℝ))]
  apply Real.exp_le_exp.mpr
  rw [Real.log_rpow hY, Y, Real.log_rpow hXp]
  dsimp [a] at hexp
  nlinarith

/-- Page 16 display 56, an elementary injective projection bound for representation pairs. -/
theorem representation_pairs_le_window (s : Finset (ℕ × ℕ)) (t : Finset ℕ) (n : ℕ)
    (hwindow : ∀ v ∈ s, v.2 ∈ t) (hrep : ∀ v ∈ s, v.1 + v.2 ^ 2 = n) :
    s.card ≤ t.card := by
  apply Finset.card_le_card_of_injOn (s := s) (t := t) (fun v : ℕ × ℕ => v.2) hwindow
  intro v hv w hw heq
  have hvn := hrep v hv
  have hwn := hrep w hw
  have heq' : v.2 = w.2 := heq
  rw [heq'] at hvn
  apply Prod.ext
  · omega
  · exact heq

/-- Page 16 display 56, counting all possible second coordinates gives only a square root bound. -/
theorem siftedCount_trivial (X B δ ε : ℝ) (n : ℕ) :
    siftedCount X B δ ε n ≤ (⌊Real.sqrt (Y X ε)⌋₊ + 1 : ℕ) := by
  classical
  unfold siftedCount
  conv_rhs => rw [← Finset.card_range (⌊Real.sqrt (Y X ε)⌋₊ + 1)]
  apply Nat.cast_le.mpr
  apply representation_pairs_le_window _ _ n
  · intro v hv
    exact (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1).2
  · intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.2.2.2.2

/-- Page 17 display 58, a limitation of the trivial counting route, not a refutation
of the sieve statement. No fixed constant can convert a unit bound to the stated
normalized logarithmic scale, even when the sieve product is replaced by one. -/
theorem no_uniform_trivial_reduction :
    ¬ ∃ K L0 : ℝ, 0 < K ∧ ∀ L : ℝ, L0 ≤ L → 1 ≤ L →
      1 ≤ K * (L ^ (-2 : ℝ) * Real.log L + L ^ (-1 : ℝ)) := by
  rintro ⟨K, L0, hK, h⟩
  let L := max L0 (4 * K + 1)
  have hL4 : 4 * K + 1 ≤ L := le_max_right _ _
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hlog : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos hL]
  have hb : L ^ (-2 : ℝ) * Real.log L + L ^ (-1 : ℝ) ≤
      L ^ (-2 : ℝ) * L + L ^ (-1 : ℝ) :=
    add_le_add (mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hL.le (-2))) le_rfl
  have he : L ^ (-2 : ℝ) * L + L ^ (-1 : ℝ) = 2 / L := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hL.le,
      Real.rpow_two, Real.rpow_neg_one]
    field_simp
    <;> ring
  rw [he] at hb
  have hc := (h L (le_max_left _ _) hL1).trans (mul_le_mul_of_nonneg_left hb hK.le)
  have hlt : K * (2 / L) < 1 := by
    rw [← mul_div_assoc, div_lt_one hL]
    linarith
  linarith

end LeanLab.KumchevLiu2007.Task506c
