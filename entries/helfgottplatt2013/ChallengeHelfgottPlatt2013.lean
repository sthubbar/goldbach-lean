module

public import Mathlib

/-!
# Proth's criterion and the reduction of ternary Goldbach up to 8.875 · 10^30

H. A. Helfgott and D. J. Platt, Numerical verification of the ternary Goldbach conjecture up
to 8.875 · 10^30, Experimental Mathematics 22, 2013, arXiv:1305.3062.

Section 2 of the paper calls `N = k · 2^n + 1` with `0 < k < 2^n` a Proth number and states
Theorem 2.3: if some `a` has Jacobi symbol `(a / N) = -1` and `a^((N-1)/2) ≡ -1 mod N`, then
`N` is prime; the paper remarks that conversely, for a prime `N`, every such `a` satisfies the
congruence. Section 3 builds ladders of Proth primes in which no gap exceeds `4 · 10^18`, and Section 4 runs this over `492700` ranges of width `2^54 · 10^9`, whose union
ends at `T = 8875694145621773516800000000000`. Theorem 4.1: every odd number from 7 to `T` is a
sum of three primes. Together with the verification of binary Goldbach up to `4 · 10^18` by
Oliveira e Silva, Herzog and Pardi, this is the computation the paper reports.

This file states:

* `LeanLab.HelfgottPlatt.U1455.proth_iff`: Proth's criterion. A Proth number
  `N = k · 2^(m+1) + 1`, `0 < k < 2^(m+1)`, is prime if and only if some integer `a` has
  Jacobi symbol `-1` over `N` and `a^((N-1)/2) = -1` in `ZMod N`. The paper's `n` is `m + 1`.
* `LeanLab.HelfgottPlatt.U6816.theorem4_1_of_ranges`: Theorem 4.1 from two hypotheses, binary
  Goldbach for every even number from 4 to `4 · 10^18`, and for each of the `492700` ranges a
  list of odd primes with gaps at most `4 · 10^18 - 2` that starts at most `2 · 10^18` above the
  left end of the range and ends less than `2 · 10^18` below its right end. These are the two
  computations, binary Goldbach and the paper's ladders, and both stay hypotheses here; neither
  is proved.
-/

@[expose] public section

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- `n` is a sum of three primes. -/
def IsTernarySum (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

/-- Binary Goldbach holds for every even `n` with `4 ≤ n ≤ N`. -/
def EvenGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n, Even n → 4 ≤ n → n ≤ N → IsGoldbachSum n

/-- Ternary Goldbach holds for every odd `n` with `7 ≤ n ≤ N`. -/
def TernaryGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n, Odd n → 7 ≤ n → n ≤ N → IsTernarySum n

end LeanLab

namespace LeanLab.HelfgottPlatt.Proth

/-- The paper's bound, Theorem 4.1. -/
def T : ℕ := 8875694145621773516800000000000

end LeanLab.HelfgottPlatt.Proth

namespace LeanLab.HelfgottPlatt.U1455

open LeanLab.HelfgottPlatt.Proth

/-- The full Proth criterion, Section 2: a Proth number is prime if and only if some `a`
has Jacobi symbol `-1` over `N` and `a^((N-1)/2) = -1 mod N`. -/
theorem proth_iff {k m N : ℕ} (hk0 : 0 < k) (hk : k < 2 ^ (m + 1))
    (hN : N = k * 2 ^ (m + 1) + 1) :
    N.Prime ↔ ∃ a : ℤ, jacobiSym a N = -1 ∧ (a : ZMod N) ^ ((N - 1) / 2) = -1 := by
  sorry

end LeanLab.HelfgottPlatt.U1455

namespace LeanLab.HelfgottPlatt.U6816

open LeanLab.HelfgottPlatt LeanLab.HelfgottPlatt.Proth

/-- One rung, sharp form: the next prime is larger and at most `B - 2` above. -/
def Step2 (B a b : ℕ) : Prop := a < b ∧ b ≤ a + (B - 2)

/-- The range width of Section 4, `2^54 · 10^9`, as a numeral. -/
def W : ℕ := 18014398509481984000000000

/-- The ladder of range `i`: odd prime rungs with gaps at most `4e18 - 2`, starting at most
`2e18` above the left end point `i W` and ending strictly within `2e18` of the right end point
`(i + 1) W`. Nothing else is assumed, not even that the rungs lie in the range. -/
def RangeOK (i : ℕ) (l : List ℕ) : Prop :=
  ∃ h t, l = h :: t ∧ h.Prime ∧ 3 ≤ h ∧ (∀ p ∈ t, p.Prime) ∧
    (h :: t).IsChain (Step2 (4 * 10 ^ 18)) ∧ h ≤ i * W + 2 * 10 ^ 18 ∧
    (i + 1) * W < t.getLastD h + 2 * 10 ^ 18

/-- Theorem 4.1 of the paper from its two computational inputs, which are hypotheses here:
binary Goldbach up to `4 · 10^18`, `hB`, and the prime ladders of the 492,700 ranges of
Section 4, `hL`. Conclusion: every odd number from 7 to `T` is a sum of three primes. -/
theorem theorem4_1_of_ranges (hB : EvenGoldbachUpTo (4 * 10 ^ 18)) (L : ℕ → List ℕ)
    (hL : ∀ i < 492700, RangeOK i (L i)) : TernaryGoldbachUpTo T := by
  sorry

end LeanLab.HelfgottPlatt.U6816
