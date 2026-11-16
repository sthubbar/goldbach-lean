module

public import Mathlib

/-!
# Goldbach with primes in progressions, the printed Conjecture 1.2 iv

Kimball Martin, Refined Goldbach conjectures with primes in progressions, arXiv 1806.00946 v1,
2018, published in Experimental Mathematics 31, 2022, pages 226-232. Conjecture 1.2 iv, as
printed on page 1: any `n ≡ 2` mod 4 except `n = 2, 6, 14, 18, 62` is of the form `p + q` with
primes `p ≡ q ≡ 1` mod 4.

As printed this is false. The number 38 is `≡ 2` mod 4, is not in the printed list, and is not
a sum of two primes `≡ 1` mod 4; and 18 = 5 + 13 is such a sum. The paper's own list of
exceptional sets in Section 3 gives `E_{1,1,4} = {2, 6, 14, 38, 62}`, so 38 was printed as 18.

This file is an extract of the lab file `LeanLab/Martin2018/Statements.lean`; see `PORTING.md`.
AI agents wrote the Lean code; it was checked by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.Martin2018

/-- `n = p + q` with primes `p ≡ a`, `q ≡ b` mod `m`. -/
def GoldbachAP (m a b n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % m = a % m ∧ q % m = b % m ∧ p + q = n

/-- Conj 1.2 iv as printed: every `n ≡ 2` mod 4 except 2, 6, 14, 18, 62, with `p ≡ q ≡ 1`.
False as printed, see `conj1_2_iv_printed_false`: 38 is an exception and 18 = 5 + 13 is not. -/
def Conj1_2_iv_printed : Prop :=
  ∀ n, n % 4 = 2 → n ∉ ({2, 6, 14, 18, 62} : Finset ℕ) → GoldbachAP 4 1 1 n

/-- The corrected exceptions 2, 6, 14, 38, 62 are not sums of two primes `≡ 1` mod 4. -/
theorem conj1_2_iv_exceptions :
    ∀ n ∈ ({2, 6, 14, 38, 62} : Finset ℕ), ¬ GoldbachAP 4 1 1 n := by
  rintro n hn ⟨p, q, hp, hq, hpm, hqm, hpq⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  obtain rfl : q = n - p := by omega
  have hpn : p ≤ n := by omega
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> interval_cases p <;>
    revert hp hq hpm hqm <;> norm_num

/-- 18 = 5 + 13 with both primes `≡ 1` mod 4, so 18 is not an exception. -/
theorem eighteen_is_sum : GoldbachAP 4 1 1 18 :=
  ⟨5, 13, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Conj 1.2 iv as printed is false: `n = 38` is `≡ 2` mod 4, not in the printed list, and is
not a sum of two primes `≡ 1` mod 4. A misprint of 38 as 18; the paper's table has 38. -/
theorem conj1_2_iv_printed_false : ¬ Conj1_2_iv_printed := by
  intro h
  exact conj1_2_iv_exceptions 38 (by simp) (h 38 (by norm_num) (by simp))

end LeanLab.Martin2018
