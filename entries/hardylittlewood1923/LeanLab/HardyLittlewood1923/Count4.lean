module

public import LeanLab.HardyLittlewood1923.TheoremEStatements

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5707, paper P0004.

# `N̄₄(n) = Σ_{p odd prime} N̄₃(n - p)`

The first coordinate of an ordered 4-tuple of odd primes with sum `n` is an odd prime `p < n`,
and the other three are a 3-tuple of odd primes with sum `n - p`. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Finset

attribute [local instance] Classical.propDecidable

/-- The odd primes up to `n`. -/
noncomputable def oddPrimesLE (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p => p.Prime ∧ Odd p)

theorem N4bar_eq_sum (n : ℕ) :
    N4bar n = ∑ p ∈ oddPrimesLE n, N3bar (n - p) := by
  unfold N4bar
  rw [card_eq_sum_card_fiberwise (f := fun t : ℕ × ℕ × ℕ => t.1) (t := oddPrimesLE n)]
  · refine sum_congr rfl fun p hp => ?_
    unfold N3bar
    simp only [oddPrimesLE, mem_filter, mem_range] at hp
    refine card_nbij' (fun t => t.2) (fun u => (p, u)) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [coe_filter, mem_filter, mem_product, mem_range, Set.mem_ofPred_eq] at ht ⊢
      obtain ⟨⟨⟨_, h2, h3⟩, hp1, hp2, hp3, hlt, hp4, ho1, ho2, ho3, ho4⟩, rfl⟩ := ht
      refine ⟨⟨by omega, by omega⟩, ⟨hp2, hp3, by omega, ?_, by omega⟩, ho2, ho3, ?_⟩
      · rwa [show n - t.1 - t.2.1 - t.2.2 = n - t.1 - t.2.1 - t.2.2 from rfl,
          show n - t.1 - t.2.1 - t.2.2 = n - t.1 - t.2.1 - t.2.2 from rfl] at hp4
      · exact ho4
    · intro u hu
      simp only [coe_filter, mem_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hu ⊢
      obtain ⟨⟨h1, h2⟩, ⟨hp1, hp2, hne, hp3, hle⟩, ho1, ho2, ho3⟩ := hu
      refine ⟨⟨⟨by omega, by omega, by omega⟩, hp.2.1, hp1, hp2, by omega, ?_, hp.2.2, ho1, ho2, ?_⟩,
        trivial⟩
      · exact hp3
      · exact ho3
    · intro t ht
      simp only [coe_filter, mem_filter, Set.mem_ofPred_eq] at ht
      ext <;> simp [ht.2]
    · intro u _; rfl
  · intro t ht
    rw [Finset.mem_coe, mem_filter, mem_product, mem_range] at ht
    show t.1 ∈ (oddPrimesLE n : Set ℕ)
    rw [Finset.mem_coe, oddPrimesLE, mem_filter, mem_range]
    exact ⟨ht.1.1, ht.2.1, ht.2.2.2.2.2.2.1⟩

end LeanLab.HardyLittlewood1923

