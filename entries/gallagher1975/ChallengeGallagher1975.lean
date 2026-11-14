module

public import Mathlib

/-!
# Primes and powers of 2, after Gallagher 1975

P. X. Gallagher, *Primes and powers of 2*, Invent. Math. 29 (1975) 125–142,
DOI 10.1007/BF01390190. For `k ≥ 1` let `r'_k(n)` count the representations
`n = p + 2^{ν₁} + ⋯ + 2^{ν_k}` with `p` prime and `1 ≤ νᵢ ≤ L = [log₂ N]`, and let `r''_k(N)` count
the representations `N = p₁ + p₂ + 2^{ν₁} + ⋯ + 2^{ν_k}`. Gallagher proves, for the base `g = 2`:

* Theorem 1, display (3) p. 125: the mean square
  `Σ_{n ≤ N, n odd} (r'_k(n) − 2 L^k / log N)² ≪ (log² 2k / k) N L^{2k−2}` for `N ≥ N_k`, with an
  implied constant independent of `k`;
* Theorem 2, display (4) p. 125: for even `N ≥ N_k`,
  `r''_k(N) = (2 N L^k / log² N) (1 + O(log² k / k))`, with an absolute implied constant.

Both are proved in the solution with no hypothesis. Binary Goldbach is open; nothing here
claims it. `≪` and `O(·)` are explicit existential constants, `N ≥ N_k` is an explicit
threshold depending on `k`. Lean names keep the namespaces of the lab where the proofs were
written: `LPZ2007` for the exponent tuples, shared with the lab's work on Languasco, Pintz and
Zaccagnini 2007, and `Decomp1532c` for the final assembly.
-/

@[expose] public section

noncomputable section

open Finset Real MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

namespace LeanLab.LPZ2007

/-- Exponent tuples `(ν_1, ..., ν_k) ∈ [1, M]^k`. -/
def tuples (k M : ℕ) : Finset (Fin k → ℕ) := Fintype.piFinset fun _ => Icc 1 M

/-- `2^{ν_1} + ... + 2^{ν_k}`. -/
def pow2sum {k : ℕ} (ν : Fin k → ℕ) : ℕ := ∑ i, 2 ^ ν i

end LeanLab.LPZ2007
end

noncomputable section

open Finset Real Filter
open scoped Topology

namespace LeanLab.Linnik.Gallagher1975

open LeanLab.LPZ2007 (tuples pow2sum)

/-- Gallagher's `r'_k(n)`, p.125, with `L = [log₂ N]`: pairs `(p, ν)`, `p` prime,
`ν ∈ [1, L]^k`, `n = p + 2^{ν1} + ... + 2^{νk}`. Any prime in such a representation is at most `n`. The paper defines `r'_k` only for odd `n`;
this definition extends it to all `n`, and Theorem 1 uses only odd `n`. -/
def rk (k N n : ℕ) : ℕ :=
  #{x ∈ range (n + 1) ×ˢ tuples k (Nat.log 2 N) | x.1.Prime ∧ n = x.1 + pow2sum x.2}

/-- **Gallagher 1975, Theorem 1**, display (3), p.125, `g = 2`: for `k ≥ 1` and
`N ≥ N_k`, `Σ_{n ≤ N, n odd} (r'_k(n) - 2L^k/log N)² ≪ (log² 2k / k) N L^{2k-2}`, with an
implied constant independent of `k`, depending only on `g = 2` per the p.126 Notation; the
sum is over odd `n`, as the definition of `r'_k` for odd `n`, the remark on p.126 and the
dashed sums of p.139 fix. -/
def Theorem1 : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
    ∑ n ∈ range (N + 1) with Odd n,
        ((rk k N n : ℝ) - 2 * (Nat.log 2 N : ℝ) ^ k / Real.log N) ^ 2 ≤
      C * (Real.log (2 * k) ^ 2 / k) * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2)

end LeanLab.Linnik.Gallagher1975
end

noncomputable section

open Finset Real

namespace LeanLab.Linnik.Gallagher1975Thm2

open LeanLab.Linnik.Gallagher1975
open LeanLab.LPZ2007 (tuples pow2sum)

/-- Gallagher's `r''_k(N)`, p.125, `g = 2`, `L = [log₂ N]`. -/
def rpp (k N : ℕ) : ℕ :=
  #{x ∈ (range (N + 1) ×ˢ range (N + 1)) ×ˢ tuples k (Nat.log 2 N) |
    x.1.1.Prime ∧ x.1.2.Prime ∧ N = x.1.1 + x.1.2 + pow2sum x.2}

end LeanLab.Linnik.Gallagher1975Thm2
end

section

open Finset MeasureTheory Filter
open scoped Topology

namespace LeanLab.Linnik.Decomp1532c

/-- **Gallagher 1975, Theorem 1**, display (3) p. 125, for `g = 2`, with no hypothesis. -/
theorem theorem1_of_leaves : LeanLab.Linnik.Gallagher1975.Theorem1 := by
  sorry

/-- **Gallagher 1975, Theorem 2**, display (4) p. 125, for `g = 2`, with no hypothesis: an
absolute `K` such that for `k ≥ 2` and even `N ≥ N_k`,
`|r''_k(N) − 2N L^k / log² N| ≤ K (log² k / k) · 2N L^k / log² N`. -/
theorem theorem2_of_leaves :
    ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N → Even N →
      |(LeanLab.Linnik.Gallagher1975Thm2.rpp k N : ℝ) -
        2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2| ≤
        K * (Real.log k ^ 2 / k) * (2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2) := by
  sorry

end LeanLab.Linnik.Decomp1532c
end
