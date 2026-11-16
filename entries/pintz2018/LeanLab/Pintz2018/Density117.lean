module

public import LeanLab.Pintz2018.Decomp117

/-!
Finite algebra before display 8.2 in Pintz 2018, page 33.
The analytic character estimate 7.20 stays explicit.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.Pintz2018.Density117

/-- Weights at least one give a total weight at least the number of zeros.
Source: page 30, display 7.7. -/
theorem weighted_count_ge_card {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hA : ∀ j ∈ s, 1 ≤ A j) : (s.card : ℝ) ≤ ∑ j ∈ s, A j := by
  simpa using Finset.sum_le_sum hA

/-- Displays 7.20 and 8.2, page 33. The cross term upper bound and centering identity
reduce the analytic estimate to the squared inequality used in Theorem J. -/
theorem square_of_centered_estimate {ι : Type*} (s : Finset ι) (A p : ι → ℝ)
    (psi xi eps cross : ℝ) (hA : ∀ j ∈ s, 1 ≤ A j)
    (hp : ∀ j ∈ s, psi ≤ p j) (hDelta : xi ≤ psi) (hxi : 0 ≤ xi)
    (hcross : cross ≤ (∑ j ∈ s, A j) ^ 2 - ∑ j ∈ s, A j)
    (h720 : (∑ j ∈ s, (A j * p j - xi)) ^ 2 ≤
      (∑ j ∈ s, A j) + xi * cross + eps * (∑ j ∈ s, A j) ^ 2) :
    ((∑ j ∈ s, A j) * (psi - xi) + (∑ j ∈ s, A j * (p j - psi))) ^ 2 ≤
      (∑ j ∈ s, A j) + xi * ((∑ j ∈ s, A j) ^ 2 - ∑ j ∈ s, A j) +
        eps * (∑ j ∈ s, A j) ^ 2 := by
  have hn0 : 0 ≤ ∑ j ∈ s, A j := Finset.sum_nonneg (fun j hj => (zero_le_one.trans (hA j hj)))
  have hd0 : 0 ≤ ∑ j ∈ s, A j * (p j - psi) :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (zero_le_one.trans (hA j hj)) (sub_nonneg.mpr (hp j hj)))
  have hbase0 : 0 ≤ (∑ j ∈ s, A j) * (psi - xi) + ∑ j ∈ s, A j * (p j - psi) :=
    add_nonneg (mul_nonneg hn0 (sub_nonneg.mpr hDelta)) hd0
  have hcard := weighted_count_ge_card s A hA
  have hid := Decomp117.leaf_centered_identity s A p psi xi
  have hcenter : (∑ j ∈ s, A j) * (psi - xi) + (∑ j ∈ s, A j * (p j - psi)) ≤
      ∑ j ∈ s, (A j * p j - xi) := by
    have := mul_nonpos_of_nonneg_of_nonpos hxi (sub_nonpos.mpr hcard)
    linarith
  have hsq := (sq_le_sq₀ hbase0 (hbase0.trans hcenter)).mpr hcenter
  have hcross' := mul_le_mul_of_nonneg_left hcross hxi
  linarith

/-- Distinct character groups contribute at most N squared minus N ordered zero pairs.
Source: page 33, the cross term in 7.20 and its bound in 8.2. -/
theorem off_diagonal_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (n : ι → ℕ) :
    (∑ i ∈ s, ∑ j ∈ s.erase i, (n i : ℝ) * (n j : ℝ)) ≤
      (∑ i ∈ s, (n i : ℝ)) ^ 2 - ∑ i ∈ s, (n i : ℝ) := by
  have hdiag : (∑ i ∈ s, (n i : ℝ)) ≤ ∑ i ∈ s, (n i : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact_mod_cast Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) (n i)
  calc
    (∑ i ∈ s, ∑ j ∈ s.erase i, (n i : ℝ) * (n j : ℝ)) =
        ∑ i ∈ s, (n i : ℝ) * ((∑ j ∈ s, (n j : ℝ)) - (n i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hi]
    _ = (∑ i ∈ s, (n i : ℝ)) ^ 2 - ∑ i ∈ s, (n i : ℝ) ^ 2 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← sq]
    _ ≤ _ := by linarith

/-- The weighted count bound used in 8.2 remains valid with N prime in place of N.
The group sizes sum to the number of zeros. Source: page 30, 7.5 and 7.7, and page 33, 8.2. -/
theorem weighted_off_diagonal_bound {ι κ : Type*} [DecidableEq κ]
    (zeros : Finset ι) (groups : Finset κ) (A : ι → ℝ) (n : κ → ℕ)
    (hA : ∀ j ∈ zeros, 1 ≤ A j) (htotal : (∑ k ∈ groups, n k) = zeros.card) :
    (∑ i ∈ groups, ∑ j ∈ groups.erase i, (n i : ℝ) * (n j : ℝ)) ≤
      (∑ j ∈ zeros, A j) ^ 2 - ∑ j ∈ zeros, A j := by
  have hcount := weighted_count_ge_card zeros A hA
  have hoff := off_diagonal_bound groups n
  have hcast : (∑ k ∈ groups, (n k : ℝ)) = (zeros.card : ℝ) := by exact_mod_cast htotal
  rw [hcast] at hoff
  by_cases hz : zeros = ∅
  · subst zeros
    simpa using hoff
  · have hcardnat : 1 ≤ zeros.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
    have hcard : (1 : ℝ) ≤ zeros.card := by exact_mod_cast hcardnat
    have hprod := mul_nonneg (sub_nonneg.mpr hcount)
      (show 0 ≤ (∑ j ∈ zeros, A j) + zeros.card - 1 by linarith)
    nlinarith

/-- Weighted excess bound with only the analytic estimate 7.20 remaining as input.
Source: page 33, displays 7.20 and 8.1 to 8.4. CONDITIONAL ON 7.20. -/
theorem excess_bound_of_720 {ι κ : Type*} [DecidableEq κ]
    (zeros : Finset ι) (groups : Finset κ) (A p : ι → ℝ) (n : κ → ℕ)
    (psi xi eps : ℝ) (hA : ∀ j ∈ zeros, 1 ≤ A j)
    (hp : ∀ j ∈ zeros, psi ≤ p j) (hDelta : xi < psi) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hgap : xi + eps ≤ (psi - xi) ^ 2) (htotal : (∑ k ∈ groups, n k) = zeros.card)
    (h720 : (∑ j ∈ zeros, (A j * p j - xi)) ^ 2 ≤
      (∑ j ∈ zeros, A j) +
        xi * (∑ i ∈ groups, ∑ j ∈ groups.erase i, (n i : ℝ) * (n j : ℝ)) +
        eps * (∑ j ∈ zeros, A j) ^ 2) :
    (∑ j ∈ zeros, (p j - psi)) ≤ (1 - xi) / (2 * (psi - xi)) := by
  have hcross := weighted_off_diagonal_bound zeros groups A n hA htotal
  have hsquare := square_of_centered_estimate zeros A p psi xi eps _ hA hp hDelta.le hxi0 hcross h720
  have hbound := Decomp117.theoremJ_bound_of_leaves
    (fun _ => ∑ j ∈ zeros, (p j - psi))
    (fun _ => ∑ j ∈ zeros, A j)
    (fun _ => ∑ j ∈ zeros, A j * (p j - psi)) xi 0 (psi - xi) eps
    (sub_pos.mpr hDelta) hxi1 (by norm_num) hgap
    (fun _ => Finset.sum_nonneg (fun j hj => zero_le_one.trans (hA j hj)))
    (fun _ => Decomp117.leaf_weighted_excess zeros A p psi hA hp)
    (fun _ => hsquare)
  simpa only [TheoremJ_bound, add_zero] using hbound (0 : ℝ)

end LeanLab.Pintz2018.Density117
