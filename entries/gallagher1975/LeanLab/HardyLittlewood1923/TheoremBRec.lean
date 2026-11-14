module

public import LeanLab.HardyLittlewood1923.TheoremC

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5901, paper P0004.

# Hardy-Littlewood 1923, a recursion for ν_r(n)

`nur_succ`: peeling off the first prime of an ordered tuple gives
`ν_{r+1}(n) = Σ_{p ≤ n prime} log p · ν_r(n - p)`.
`nur_le_pow`: the crude bound `ν_{r+1}(n) ≤ (n+1)^r (log n)^{r+1}`, from `nur_le` and the count
of tuples with a fixed sum, `card_fixsum_le`.

Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter

theorem nur_succ (r n : ℕ) :
    nur (r + 1) n = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p * nur r (n - p) := by
  simp_rw [nur_eq, Finset.mul_sum]
  rw [Finset.sum_sigma' _ (fun p => Sr r (n - p))
    (fun p (u : Fin r → ℕ) => Real.log p * ∏ i, Real.log (u i : ℝ))]
  refine Finset.sum_nbij' (fun t => (⟨t 0, Fin.tail t⟩ : Σ _ : ℕ, Fin r → ℕ))
    (fun x => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_Sr, mem_sigma, mem_filter, mem_range] at ht ⊢
    obtain ⟨h1, h2, h3⟩ := ht
    rw [Fin.sum_univ_succ] at h3
    refine ⟨⟨h1 0, h2 0⟩, fun i => ?_, fun i => h2 _, ?_⟩
    · have : t i.succ ≤ ∑ j : Fin r, t j.succ :=
        Finset.single_le_sum (f := fun j : Fin r => t j.succ) (fun _ _ => Nat.zero_le _)
          (mem_univ i)
      simp only [Fin.tail]; omega
    · simp only [Fin.tail]; omega
  · intro x hx
    simp only [mem_Sr, mem_sigma, mem_filter, mem_range] at hx ⊢
    obtain ⟨⟨hp1, hp2⟩, h1, h2, h3⟩ := hx
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hp1
      · simp only [Fin.cons_succ]; have := h1 j; omega
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hp2
      · simpa using h2 j
    · rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; omega
  · intro t _; simp
  · intro x _; simp
  · intro t _
    simp [Fin.prod_univ_succ, Fin.tail]

theorem nur_le_pow (r n : ℕ) : nur (r + 1) n ≤ ((n : ℝ) + 1) ^ r * Real.log n ^ (r + 1) := by
  have hN : Nr (r + 1) n ≤ (n + 1) ^ r := by
    refine le_trans (Finset.card_le_card ?_) (card_fixsum_le r n n)
    intro t ht
    rw [← Sr, mem_Sr] at ht
    simp only [mem_filter, Fintype.mem_piFinset, mem_range]
    exact ⟨ht.1, ht.2.2⟩
  have hl : 0 ≤ Real.log n ^ (r + 1) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · exact pow_nonneg (Real.log_nonneg (by exact_mod_cast h)) _
  calc nur (r + 1) n ≤ (Nr (r + 1) n : ℝ) * Real.log n ^ (r + 1) := nur_le _ _
    _ ≤ ((n : ℝ) + 1) ^ r * Real.log n ^ (r + 1) := by
        apply mul_le_mul_of_nonneg_right _ hl
        exact_mod_cast hN

end LeanLab.HardyLittlewood1923

