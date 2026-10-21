module

public import Mathlib

/-!
# Romanov 1934: the integers of the form p + 2^k have positive lower density

N. P. Romanov, *Über einige Sätze der additiven Zahlentheorie*, Math. Ann. 109, 1934, 668-678,
proves that the integers `n = p + 2^k`, `p` prime, `k ≥ 1`, have positive lower density.
P. Erdős, *On integers of the form 2^k + p and some related problems*, Summa Brasil. Math. 2,
1950, 113-123, showed by a covering system that an arithmetic progression of odd numbers
contains no such `n`, so the odd numbers that are not of that form also have positive lower
density. Erdős printed the progression `7629217 mod 11184810`; the progression
`119477317 mod 346729110` used here was chosen by the lab from Erdős' covering, with the extra
condition `31 ∣ n`, and is checked by the Lean kernel.

The target theorems, each proved in the solution with no hypothesis, are:
* `romanov`: an absolute `c > 0` such that for every `x ≥ 16` at least `c x` numbers below `x`
  are of the form `p + 2^k`, `p` prime, `k ≥ 0`;
* `romanov_pos`: Romanov's theorem with `k ≥ 1`, for all `x` from some `X₀` on;
* `erdos_odd_not_sum`: every `n = 119477317 + 346729110 t` is odd and is not `p + 2^k`
  for any prime `p` and any `k ≥ 0`;
* `erdos_density`: for `x ≥ 4 · 346729110` at least `x / (2 · 346729110)` odd numbers below `x`
  are not `p + 2^k`;
* `romanov_erdos`: the two positive lower densities together.

Being `p + 2^k` for some `k ≥ 0` is weaker than being `p + 2^k` for some `k ≥ 1`, so the
non-sums of `erdos_odd_not_sum` and `erdos_density`, which exclude every `k ≥ 0`, are in
particular not `p + 2^k` with `k ≥ 1`. Binary Goldbach itself is open; nothing here
claims it. Lean names keep the namespace of the lab where the proofs were written.
-/

@[expose] public section

namespace LeanLab.Romanov

section
open Finset Real

/-- **Romanov's theorem**, `k ≥ 0`: the numbers `p + 2^k` have positive lower density. -/
theorem romanov : ∃ c : ℝ, 0 < c ∧ ∀ x : ℕ, 16 ≤ x → ∃ I : Finset ℕ,
    (∀ n ∈ I, n < x ∧ ∃ p k : ℕ, p.Prime ∧ n = p + 2 ^ k) ∧ c * x ≤ #I := by
  sorry

end

section
open Finset Real Filter

attribute [local instance] Classical.propDecidable

/-- **Romanov's theorem**, `k ≥ 1`, Romanov 1934: the numbers `p + 2^k`, `p` prime, `k ≥ 1`,
have positive lower density. -/
theorem romanov_pos : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∃ I : Finset ℕ,
    (∀ n ∈ I, n < x ∧ ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p + 2 ^ k) ∧ c * x ≤ #I := by
  sorry

end

/-- **Erdős 1950**, by Erdős' covering but with the lab's progression, not the printed
`7629217 mod 11184810`: every `119477317 + 346729110 t` is odd and is not `p + 2^k`. -/
theorem erdos_odd_not_sum (t : ℕ) :
    Odd (119477317 + 346729110 * t) ∧
      ∀ p k : ℕ, p.Prime → 119477317 + 346729110 * t ≠ p + 2 ^ k := by
  sorry

section
open Finset

/-- **Erdős in density form**: the odd numbers that are not `p + 2^k` have positive lower
density. -/
theorem erdos_density : ∀ x : ℕ, 4 * 346729110 ≤ x → ∃ I : Finset ℕ,
    (∀ n ∈ I, n < x ∧ Odd n ∧ ∀ p k : ℕ, p.Prime → n ≠ p + 2 ^ k) ∧
    (1 / (2 * 346729110) : ℝ) * x ≤ #I := by
  sorry

/-- **Romanov and Erdős**: the numbers `p + 2^k`, `k ≥ 1`, and the odd numbers that are no
`p + 2^k`, `k ≥ 0`, both have positive lower density. -/
theorem romanov_erdos : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
    (∃ I : Finset ℕ, (∀ n ∈ I, n < x ∧ ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p + 2 ^ k) ∧ c * x ≤ #I) ∧
    (∃ J : Finset ℕ, (∀ n ∈ J, n < x ∧ Odd n ∧ ∀ p k : ℕ, p.Prime → n ≠ p + 2 ^ k) ∧
      c * x ≤ #J) := by
  sorry

end

end LeanLab.Romanov
