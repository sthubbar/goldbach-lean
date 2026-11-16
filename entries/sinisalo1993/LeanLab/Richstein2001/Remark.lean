module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
P0017 Richstein 2001, Section 7 Remark, page 1748: the reduction behind the remark that an
exception to the ternary Goldbach conjecture would need a long prime gap.
If even Goldbach holds up to M and some odd prime p has N - M ≤ p ≤ N - 4, then the odd
number N is a sum of three primes. Run 20261018T1103Z-12430, unit U-0937.
AI-written Lean code, Claude, 2026-10-18. Ternary Goldbach is a theorem of Helfgott; binary
Goldbach is open.

This file is an extract of the lab file `LeanLab/Richstein2001/Remark.lean`: only
`ternary_of_prime_near` is kept.
-/

@[expose] public section

namespace LeanLab.Richstein2001

open LeanLab

/-- The reduction in Richstein's remark. -/
theorem ternary_of_prime_near {M N p : ℕ} (hE : EvenGoldbachUpTo M) (hN : Odd N)
    (hp : p.Prime) (hp2 : p ≠ 2) (h4 : p + 4 ≤ N) (hM : N ≤ p + M) : IsTernarySum N := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hev : Even (N - p) := by
    obtain ⟨a, ha⟩ := hN
    obtain ⟨b, hb⟩ := hpo
    exact ⟨a - b, by omega⟩
  obtain ⟨q, r, hq, hr, hqr⟩ := hE (N - p) hev (by omega) (by omega)
  exact ⟨p, q, r, hp, hq, hr, by omega⟩

end LeanLab.Richstein2001
