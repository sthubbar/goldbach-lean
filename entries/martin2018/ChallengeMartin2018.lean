module

public import Mathlib

/-!
# Martin's Conjecture 1.2 iv on sums of two primes congruent to 1 mod 4, corrected

Kimball Martin, Refined Goldbach conjectures with primes in progressions, arXiv 1806.00946 v1,
2018, published in Experimental Mathematics 31, 2022, pages 226-232. Conjecture 1.2 iv, as
printed on page 1 of the arXiv version:

  any `n ≡ 2` mod 4 except `n = 2, 6, 14, 18, 62` is of the form `p + q` with primes
  `p ≡ q ≡ 1` mod 4.

As printed the conjecture is false, at `n = 38`: it is `≡ 2` mod 4 and not in the printed list,
but no two primes `≡ 1` mod 4 sum to 38. Also 18 = 5 + 13 is such a sum. Section 3 of the paper
lists the exceptional set `E_{1,1,4} = {2, 6, 14, 38, 62}`, so 38 was printed as 18. The
corrected conjecture, with exceptions 2, 6, 14, 38, 62, is open and is not stated as proved
here. This file states:

* `LeanLab.Martin2018.conj1_2_iv_printed_false`: Conjecture 1.2 iv as printed is false;
* `LeanLab.Martin2018.conj1_2_iv_exceptions`: each of 2, 6, 14, 38, 62 is not a sum of two
  primes `≡ 1` mod 4, so the corrected list has no spurious entry;
* `LeanLab.Martin2018.eighteen_is_sum`: 18 is a sum of two primes `≡ 1` mod 4.
-/

@[expose] public section

namespace LeanLab.Martin2018

/-- `GoldbachAP m a b n`: `n = p + q` with primes `p ≡ a` and `q ≡ b` mod `m`. -/
def GoldbachAP (m a b n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % m = a % m ∧ q % m = b % m ∧ p + q = n

/-- Conjecture 1.2 iv as printed: every `n ≡ 2` mod 4 except 2, 6, 14, 18, 62 is `p + q` with
primes `p ≡ q ≡ 1` mod 4. -/
def Conj1_2_iv_printed : Prop :=
  ∀ n, n % 4 = 2 → n ∉ ({2, 6, 14, 18, 62} : Finset ℕ) → GoldbachAP 4 1 1 n

/-- None of 2, 6, 14, 38, 62 is a sum of two primes `≡ 1` mod 4. -/
theorem conj1_2_iv_exceptions :
    ∀ n ∈ ({2, 6, 14, 38, 62} : Finset ℕ), ¬ GoldbachAP 4 1 1 n := by
  sorry

/-- 18 is a sum of two primes `≡ 1` mod 4, namely 5 + 13, so it is not an exception. -/
theorem eighteen_is_sum : GoldbachAP 4 1 1 18 := by
  sorry

/-- Conjecture 1.2 iv as printed is false; the number 38 fails it. -/
theorem conj1_2_iv_printed_false : ¬ Conj1_2_iv_printed := by
  sorry

end LeanLab.Martin2018
