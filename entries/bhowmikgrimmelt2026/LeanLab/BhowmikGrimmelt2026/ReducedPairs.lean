module

public import LeanLab.BhowmikGrimmelt2026.Farey

/-!
Finite reduced pairs and the minimum weighted distance in Lemma 7.2, page 26.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Positive denominators at most M, paired with their reduced residues. -/
noncomputable def reducedPairs (M : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 M).sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))

/-- Membership records the denominator bounds and reduced residue conditions. -/
theorem mem_reducedPairs (M : ℕ) (p : Σ _ : ℕ, ℕ) :
    p ∈ reducedPairs M ↔ 1 ≤ p.1 ∧ p.1 ≤ M ∧ p.2 < p.1 ∧ Nat.Coprime p.2 p.1 := by
  simp [reducedPairs, and_assoc]

/-- At least the pair with denominator one and residue zero is present. -/
theorem reducedPairs_nonempty {M : ℕ} (hM : 1 ≤ M) : (reducedPairs M).Nonempty := by
  refine ⟨⟨1, 0⟩, ?_⟩
  simp [mem_reducedPairs, hM]

/-- The reduced pair set has cardinality at most M squared. -/
theorem reducedPairs_card_le (M : ℕ) : (reducedPairs M).card ≤ M ^ 2 := by
  rw [reducedPairs, Finset.card_sigma]
  exact reduced_card_sum_le M

/-- The pair sum is exactly the double sum over denominators and reduced residues. -/
theorem sum_reducedPairs (M : ℕ) (f : ℕ → ℕ → ℂ) :
    ∑ p ∈ reducedPairs M, f p.1 p.2 =
      ∑ q ∈ Finset.Icc 1 M, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), f q a := by
  rw [reducedPairs, Finset.sum_sigma]

/-- Some reduced pair minimizes denominator times distance to the frequency. -/
theorem reducedPairs_min {M : ℕ} (hM : 1 ≤ M) (α : ℝ) :
    ∃ p₀ ∈ reducedPairs M, ∀ p ∈ reducedPairs M,
      (p₀.1 : ℝ) * intDist (α - p₀.2 / p₀.1) ≤
        (p.1 : ℝ) * intDist (α - p.2 / p.1) := by
  exact (reducedPairs M).exists_min_image
    (fun p => (p.1 : ℝ) * intDist (α - p.2 / p.1)) (reducedPairs_nonempty hM)

end LeanLab.BhowmikGrimmelt2026
