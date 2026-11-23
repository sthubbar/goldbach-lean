module

public import LeanLab.LanguascoPintzZaccagnini2007.TrueConstantK

/-!
P0045 task131. The finite residue dependence of C(k,N), preprint page 3.
This decomposition uses the already proved convergence of the series 26.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real Filter

noncomputable section

/-- Display 23 on page 8, truncated at d < D. -/
def partialC131 (D k N : ℕ) : ℝ := ∑ d ∈ range D, Ckterm k N d

/-- CITED statement of the page 3 remark about finite residue dependence.
For fixed k, knowing N modulo all odd squarefree d < D determines C(k,N)
up to any prescribed positive error. -/
def ConstantResidueDependence131 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, ∀ N M : ℕ,
    (∀ d : ℕ, d < D → OddSqf d → (d : ℤ) ∣ (N : ℤ) - M) →
      |Ck k N - Ck k M| < ε

/-- LEAF. Page 8 displays 19, 23 and 26. The tail of C(k,N) is nonnegative
and bounded uniformly in k >= 1 and N by the tail of the convergent series 26. -/
theorem coefficient_tail131 {k : ℕ} (hk : 1 ≤ k) (D N : ℕ) :
    0 ≤ Ck k N - partialC131 D k N ∧
      Ck k N - partialC131 D k N ≤ ∑' d, seriesTerm (d + D) := by
  have hsum : Summable (fun d => Ckterm k N (d + D)) :=
    (summable_nat_add_iff D).2 (Ck_summable hk N)
  have hdom : Summable (fun d => seriesTerm (d + D)) :=
    (summable_nat_add_iff D).2 lemma61_proved
  have he := (Ck_summable hk N).sum_add_tsum_nat_add D
  change partialC131 D k N + ∑' d, Ckterm k N (d + D) = Ck k N at he
  have he' : Ck k N - partialC131 D k N = ∑' d, Ckterm k N (d + D) := by linarith
  rw [he']
  exact ⟨tsum_nonneg (fun d => Ckterm_nonneg k N (d + D)),
    Summable.tsum_le_tsum (fun d => Ckterm_le hk N (d + D)) hsum hdom⟩

/-- LEAF. Page 3 and convergence of display 26. A single finite cutoff
approximates every C(k,N) with k >= 1 to within epsilon. -/
theorem coefficient_tail_small131 (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ N : ℕ,
      0 ≤ Ck k N - partialC131 D k N ∧ Ck k N - partialC131 D k N < ε := by
  obtain ⟨D, hD⟩ := ((tendsto_order.1 (tendsto_sum_nat_add seriesTerm)).2 ε hε).exists_forall_of_atTop
  refine ⟨D, fun k hk N => ?_⟩
  have h := coefficient_tail131 hk D N
  exact ⟨h.1, h.2.trans_lt (hD D le_rfl)⟩

/-- LEAF. Page 3 and display 18 on page 8. Equal residues for all odd squarefree
d below D give identical finite sums in display 23. -/
theorem partialC_congr131 (D k N M : ℕ)
    (h : ∀ d : ℕ, d < D → OddSqf d → (d : ℤ) ∣ (N : ℤ) - M) :
    partialC131 D k N = partialC131 D k M := by
  classical
  apply sum_congr rfl
  intro d hd
  unfold Ckterm
  split_ifs with hs
  · rw [jcount_congr (h d (mem_range.mp hd) hs)]
  · rfl

/-- LEAF. Page 3. Two nonnegative tails smaller than epsilon differ
in absolute value by less than epsilon when their finite parts agree. -/
theorem equal_partial_error131 {a b p ε : ℝ}
    (ha0 : 0 ≤ a - p) (ha : a - p < ε)
    (hb0 : 0 ≤ b - p) (hb : b - p < ε) : |a - b| < ε := by
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The page 3 finite residue dependence statement, assembled from the four leaves.
No cited analytic input is used beyond the already proved Lemma 6.1. -/
theorem constant_residue_dependence131 : ConstantResidueDependence131 := by
  intro k hk ε hε
  obtain ⟨D, hD⟩ := coefficient_tail_small131 ε hε
  refine ⟨D, fun N M h => ?_⟩
  obtain ⟨hN0, hN⟩ := hD k hk N
  obtain ⟨hM0, hM⟩ := hD k hk M
  rw [← partialC_congr131 D k N M h] at hM0 hM
  exact equal_partial_error131 hN0 hN hM0 hM

end

end LeanLab.LPZ2007
