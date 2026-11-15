module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
The ladder reduction of Helfgott and Platt, P0006, unit U-0341, run 20261017T1803Z-21479.
If binary Goldbach holds up to B and odd primes 3 = p₀ < p₁ < ... < p_k have every gap at most
B - 4, then ternary Goldbach holds up to p_k + B: for odd n, take the largest pᵢ ≤ n - 4, then
4 ≤ n - pᵢ ≤ B. This is the reduction P0006 uses with B = 4e18; the sharp form this entry uses is in
HelfgottPlattU6816Sharp.lean.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.

This file is an extract of the lab file `LeanLab/HelfgottPlatt/Ladder.lean`: it keeps
`ternary_step` and `getLastD_cons'`, which the sharp ladder lemma uses, and drops the ladder
lemma with gaps at most `B - 4` and the Boolean checks, which no compared theorem uses; with
them went the lab import `LeanLab.Verifications.Top50.FastCheck`.
-/

@[expose] public section

namespace LeanLab.HelfgottPlatt

/-- One step: an odd `n` with `a + 4 ≤ n ≤ a + B`, `a` an odd prime, is a sum of three primes. -/
theorem ternary_step {B : ℕ} (hB : EvenGoldbachUpTo B) {a n : ℕ} (ha : a.Prime) (ha3 : 3 ≤ a)
    (hn : Odd n) (h1 : a + 4 ≤ n) (h2 : n ≤ a + B) : IsTernarySum n := by
  have hao : Odd a := ha.odd_of_ne_two (by omega)
  have he : Even (n - a) := Nat.Odd.sub_odd hn hao
  obtain ⟨p, q, hp, hq, hpq⟩ := hB (n - a) he (by omega) (by omega)
  exact ⟨a, p, q, ha, hp, hq, by omega⟩

theorem getLastD_cons' (a b : ℕ) (t : List ℕ) : (b :: t).getLastD a = t.getLastD b := by
  cases t with
  | nil => rfl
  | cons c t => simp [List.getLastD]

end LeanLab.HelfgottPlatt
