module

public import LeanLab.PNTSieve.BrunBlocks

/-!
# The support of Brun's block weights

Unit U-5506, CLOUD 20261019T1218Z-cloud24. AI wrote the Lean code. Known mathematics.

`support_prod`: if `cL Bs S ≠ 0` or `cU Bs S ≠ 0` for `S ⊆ Ω`, then `∏S ≤ lev Bs`, where
`lev Bs = ∏_B max(max B, 1)^{max(re, ro)}`; so the remainders of `blocks_main` only involve moduli up
to `lev Bs`, the level the remainder estimate must reach.
`blocks_main_level`: `blocks_main` with the remainder sum cut to the support and the coefficient
bound `3^{#blocks}` pulled out.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Bonferroni

open Finset

/-- The level of a list of blocks. -/
def lev : List Block → ℕ
  | [] => 1
  | b :: Bs => (max (b.1.sup id) 1) ^ (max b.2.1 b.2.2) * lev Bs

lemma tc_ne_zero {r : ℕ} {T : Finset ℕ} (h : tc r T ≠ 0) : T.card ≤ r := by
  unfold tc at h
  by_contra hc
  exact h (if_neg hc)

lemma prod_block_le (B T : Finset ℕ) (hT : T ⊆ B) (k : ℕ) (hk : T.card ≤ k) :
    ∏ p ∈ T, p ≤ (max (B.sup id) 1) ^ k := by
  have h1 : ∏ p ∈ T, p ≤ (max (B.sup id) 1) ^ T.card :=
    Finset.prod_le_pow_card T _ _ (fun p hp =>
      le_max_of_le_left (Finset.le_sup (f := id) (hT hp)))
  exact h1.trans (Nat.pow_le_pow_right (lt_of_lt_of_le one_pos (le_max_right _ _)) hk)

/-- **Support of the block weights.** -/
theorem support_prod : ∀ Bs : List Block, Good Bs → ∀ S : Finset ℕ, S ⊆ univB Bs →
    (cL Bs S ≠ 0 ∨ cU Bs S ≠ 0) → ∏ p ∈ S, p ≤ lev Bs
  | [], _, S, hS, _ => by
    simp only [univB, subset_empty] at hS
    subst hS; simp [lev]
  | b :: Bs, hG, S, hS, hne => by
    obtain ⟨_, hD, _, _, hG'⟩ := hG
    simp only [univB] at hS
    -- some truncation on the first block and some weight on the rest are nonzero
    have key : (S ∩ b.1).card ≤ max b.2.1 b.2.2 ∧
        (cL Bs (S ∩ univB Bs) ≠ 0 ∨ cU Bs (S ∩ univB Bs) ≠ 0) := by
      simp only [cL, cU, tens] at hne
      rcases hne with h | h
      · by_cases h1 : tc b.2.1 (S ∩ b.1) * cL Bs (S ∩ univB Bs) ≠ 0
        · rcases mul_ne_zero_iff.mp h1 with ⟨ha, hb⟩
          exact ⟨(tc_ne_zero ha).trans (le_max_left _ _), Or.inl hb⟩
        · push Not at h1
          by_cases h2 : tc b.2.2 (S ∩ b.1) * cU Bs (S ∩ univB Bs) ≠ 0
          · rcases mul_ne_zero_iff.mp h2 with ⟨ha, hb⟩
            exact ⟨(tc_ne_zero ha).trans (le_max_right _ _), Or.inr hb⟩
          · push Not at h2
            rw [h1, h2, zero_add, zero_sub, neg_ne_zero] at h
            rcases mul_ne_zero_iff.mp h with ⟨ha, hb⟩
            exact ⟨(tc_ne_zero ha).trans (le_max_left _ _), Or.inr hb⟩
      · rcases mul_ne_zero_iff.mp h with ⟨ha, hb⟩
        exact ⟨(tc_ne_zero ha).trans (le_max_left _ _), Or.inr hb⟩
    have ih := support_prod Bs hG' (S ∩ univB Bs) inter_subset_right key.2
    have hsplit : ∏ p ∈ S, p = (∏ p ∈ S ∩ b.1, p) * ∏ p ∈ S ∩ univB Bs, p := by
      conv_lhs => rw [split_union hS]
      rw [prod_union (hD.mono inter_subset_right inter_subset_right)]
    rw [hsplit, lev]
    exact Nat.mul_le_mul (prod_block_le b.1 _ inter_subset_right _ key.1) ih

/-- **`blocks_main` cut to the support**: the remainder is at most `3^{#blocks}` times the sum of
`|R_S|` over the `S ⊆ Ω` with `cL S ≠ 0`, all of which have `∏S ≤ lev Bs`. -/
theorem blocks_main_level (A : Finset ℕ) (Bs : List Block) (hG : Good Bs) (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) (X : ℝ) (hX : 0 ≤ X) :
    X * (∏ p ∈ univB Bs, (1 - x p) - eL x Bs) -
      3 ^ Bs.length * ∑ S ∈ (univB Bs).powerset.filter (fun S => cL Bs S ≠ 0), |rem A x X S| ≤
      (sifted A (univB Bs) : ℝ) := by
  have h := blocks_main A Bs hG x hx0 hx1 X hX
  have hle : ∑ S ∈ (univB Bs).powerset, |cL Bs S| * |rem A x X S| ≤
      3 ^ Bs.length * ∑ S ∈ (univB Bs).powerset.filter (fun S => cL Bs S ≠ 0), |rem A x X S| := by
    rw [mul_sum, sum_filter]
    refine sum_le_sum (fun S _ => ?_)
    split_ifs with hS
    · exact mul_le_mul_of_nonneg_right (coeff_bounds Bs S).2 (abs_nonneg _)
    · push Not at hS; rw [hS]; simp
  linarith

end LeanLab.PNTSieve.Bonferroni

