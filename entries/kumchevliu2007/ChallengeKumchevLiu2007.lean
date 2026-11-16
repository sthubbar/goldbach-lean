module

public import Mathlib

/-!
# A remark on the conjecture of Kumchev and Liu on sums of a prime and the square of a prime

A. V. Kumchev and J. Y. Liu, Sums of primes and squares of primes in short intervals,
arXiv 0801.0130 v1, 2007. Page 1 sets `ℋ₂ = {n ∈ ℕ : n ≢ 1 (mod 3), 2 ∣ n}` and says

  It is conjectured that every sufficiently large `n ∈ ℋ₂` can be represented as the sum of a
  prime and the square of another prime.

As printed, this is false, because squares are not excluded. If `m² = p + q²` with `p, q`
prime then `p = (m - q)(m + q)`, so `q = m - 1`. For `m = 30 t + 6` with `t ≥ 1`, the number
`m²` lies in `ℋ₂` while `m - 1 = 5 (6 t + 1)` is composite. This file states:

* `LeanLab.KumchevLiu2007.Novelty1612.inH2_family`: `(30 t + 6)²` lies in `ℋ₂`;
* `LeanLab.KumchevLiu2007.Novelty1612.not_form_family`: for `t ≥ 1`, `(30 t + 6)²` is not
  `p + q²` with `p, q` prime;
* `LeanLab.KumchevLiu2007.Novelty1612.conjecture_printed_false`: the printed conjecture is
  false, even when `p = q` is allowed, and so also with "another prime" read as `p ≠ q`.

The paper's theorems, which concern almost all `n ∈ ℋ₂` in short intervals, are not affected.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007

/-- `n = p₁ + p₂²` with `p₁, p₂` prime. The paper's conjecture says "another prime", but its
counting function `R₂` and the sets `E₂` do not require `p₁ ≠ p₂`; we follow `E₂`. -/
def IsPrimePlusPrimeSq (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q ^ 2

/-- The paper's `ℋ₂ = {n ∈ ℕ : n ≢ 1 (mod 3), 2 ∣ n}`. -/
def InH2 (n : ℕ) : Prop := n % 3 ≠ 1 ∧ 2 ∣ n

end LeanLab.KumchevLiu2007

namespace LeanLab.KumchevLiu2007.Novelty1612

/-- The conjecture as printed on p. 1 of the paper, with `p₁ = p₂` allowed: there is `N₀`
such that every `n ≥ N₀` in `ℋ₂` is `p + q²` with `p, q` prime. -/
def conjecture_printed : Prop := ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → InH2 n → IsPrimePlusPrimeSq n

/-- The family: `m = 30 t + 6` gives `m²` in H₂. -/
theorem inH2_family (t : ℕ) : InH2 ((30 * t + 6) ^ 2) := by
  sorry

/-- For `t ≥ 1`, `(30 t + 6)²` is not a prime plus the square of a prime. -/
theorem not_form_family {t : ℕ} (ht : 1 ≤ t) : ¬ IsPrimePlusPrimeSq ((30 * t + 6) ^ 2) := by
  sorry

/-- **The printed conjecture is false.** No hypothesis. -/
theorem conjecture_printed_false : ¬ conjecture_printed := by
  sorry

end LeanLab.KumchevLiu2007.Novelty1612
