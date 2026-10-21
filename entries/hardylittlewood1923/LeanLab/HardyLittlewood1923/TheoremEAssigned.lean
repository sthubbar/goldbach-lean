module

public import LeanLab.HardyLittlewood1923.TheoremD

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1614Z-cloud28, unit U-5709, paper P0004.

# Hardy-Littlewood 1923, Theorem E, p. 31: "of which one may be assigned"

Every large even `n` is a sum of four odd primes one of which is any prescribed odd prime `q`:
`n - q` is a large odd number, a sum of three odd primes by Theorem D. PROVED with no hypothesis
from `theoremD_ternary`. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Finset

attribute [local instance] Classical.propDecidable

/-- Theorem E's assigned prime: for each odd prime `q`, every large even `n` is
`q + p₁ + p₂ + p₃` with `p₁, p₂, p₃` odd primes. -/
theorem theoremE_assigned (q : ℕ) (hq : q.Prime) (hqo : Odd q) :
    ∃ n₀ : ℕ, ∀ n, Even n → n₀ ≤ n → ∃ a b c : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧
      Odd a ∧ Odd b ∧ Odd c ∧ q + a + b + c = n := by
  obtain ⟨m₀, hm⟩ := theoremD_ternary
  refine ⟨m₀ + q, fun n hn hn0 => ?_⟩
  have hodd : Odd (n - q) := by
    obtain ⟨k, hk⟩ := hn; obtain ⟨j, hj⟩ := hqo
    exact ⟨k - j - 1, by omega⟩
  have hpos := hm (n - q) hodd (by omega)
  unfold N3bar at hpos
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht
  obtain ⟨_, ⟨h1, h2, hne, h3, hle⟩, o1, o2, o3⟩ := ht
  exact ⟨t.1, t.2, n - q - t.1 - t.2, h1, h2, h3, o1, o2, o3, by omega⟩

end LeanLab.HardyLittlewood1923

