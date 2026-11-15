module

public import Mathlib
public import LeanLab.SchnirelmannConstant.Defs

/-!
Tao 2012, Every odd number greater than 1 is the sum of at most five primes,
arXiv 1201.6656v4, Math. Comp. 83, 2014.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
In the lab a placeholder proof marks a statement taken from the paper and not proved in the lab.
-/

@[expose] public section

namespace LeanLab.Tao2012
open LeanLab.SchnirelmannConstant

/-- `N₀ = 4 · 10^14`, Richstein's even Goldbach bound used by the paper. -/
def N0 : ℕ := 4 * 10 ^ 14

/-- `8.7 · 10^36`, the lower end of the range handled by the circle method. -/
def X0 : ℕ := 87 * 10 ^ 35

/-- Conjecture 1.1, even Goldbach in the paper's form: every even natural number is a sum
of at most two primes. OPEN. Stated, never to be proved here. -/
def Conjecture1_1 : Prop := ∀ n : ℕ, Even n → AtMostPrimes 2 n

/-- Conjecture 1.2, odd Goldbach: every odd number greater than 1 is a sum of at most
three primes. Proved by Helfgott 2013, not in the lab. -/
def Conjecture1_2 : Prop := ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 3 n



/-- Theorem 8.2 as paraphrased in the introduction: every integer larger than `8.7 · 10^36`
is a sum of three primes and a natural number between 2 and `N₀`. The upper range uses
Liu and Wang. Not proved in the lab. QUESTION for VERIFY: does the paper restrict to odd
`x`, or require the extra number to be even? The deduction below needs neither. -/
def Theorem8_2 : Prop := ∀ x : ℕ, X0 < x → ∃ p q r m : ℕ,
    p.Prime ∧ q.Prime ∧ r.Prime ∧ 2 ≤ m ∧ m ≤ N0 ∧ x = p + q + r + m


/-- The range `x ≤ 8.7 · 10^36`, which the paper handles with Theorems 1.5, 1.6 and the
Ramaré-Saouter short interval theorem. The lab has not read the exact argument; this is
the statement the deduction needs. Not proved in the lab. -/
def SmallRange : Prop := ∀ x : ℕ, Odd x → 1 < x → x ≤ X0 → AtMostPrimes 5 x


/-! ### The deduction of Theorem 1.4, proved in the lab with no gap -/

/-- Parity step: with a 2 among the three primes, `2 + q + r + m` with `m` odd is
`5 + q + r + (m - 3)`. -/
theorem five_of_two {N q r m : ℕ} (hG : EvenGoldbachUpTo N) (hq : q.Prime) (hr : r.Prime)
    (hm : Odd m) (hmN : m ≤ N) : AtMostPrimes 5 (2 + q + r + m) := by
  have h3 : 3 ≤ m ∨ m = 1 := by obtain ⟨k, rfl⟩ := hm; omega
  rcases h3 with h3 | h1
  · have hev : Even (m - 3) := by obtain ⟨k, rfl⟩ := hm; exact ⟨k - 1, by omega⟩
    have h := (((AtMostPrimes.prime (by norm_num : (5 : ℕ).Prime)).add
      (AtMostPrimes.prime hq)).add (AtMostPrimes.prime hr)).add
      (atMost2_of_even hG hev (by omega))
    rw [show 5 + q + r + (m - 3) = 2 + q + r + m by omega] at h
    exact h.mono (by norm_num)
  · subst h1
    have h := ((AtMostPrimes.prime Nat.prime_three).add (AtMostPrimes.prime hq)).add
      (AtMostPrimes.prime hr)
    rw [show 3 + q + r = 2 + q + r + 1 by omega] at h
    exact h.mono (by norm_num)

/-- From three primes plus a number `m` in `[2, N]` to at most five primes, for odd `x`,
given even Goldbach up to `N`. Covers the case `m = 2` and the case of a prime equal to 2. -/
theorem five_of_three_plus_small {N x p q r m : ℕ} (hG : EvenGoldbachUpTo N) (hx : Odd x)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hm2 : 2 ≤ m) (hmN : m ≤ N)
    (hsum : x = p + q + r + m) : AtMostPrimes 5 x := by
  rcases Nat.even_or_odd m with hme | hmo
  · subst hsum
    have h := (((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add
      (AtMostPrimes.prime hr)).add (atMost2_of_even hG hme hmN)
    exact h.mono (by norm_num)
  · have hxo := Nat.odd_iff.mp hx
    have hmo' := Nat.odd_iff.mp hmo
    rcases hp.eq_two_or_odd with rfl | hp1
    · subst hsum; exact five_of_two hG hq hr hmo hmN
    rcases hq.eq_two_or_odd with rfl | hq1
    · subst hsum
      rw [show p + 2 + r + m = 2 + p + r + m by omega]
      exact five_of_two hG hp hr hmo hmN
    rcases hr.eq_two_or_odd with rfl | hr1
    · subst hsum
      rw [show p + q + 2 + m = 2 + p + q + m by omega]
      exact five_of_two hG hp hq hmo hmN
    · exfalso; subst hsum; omega

/-- Theorem 1.4, conditional form: Theorem 8.2, Theorem 1.6 and the small range give
that every odd `x > 1` is a sum of at most five primes. No gap of its own. -/
theorem theorem1_4_of (h82 : Theorem8_2) (h16 : EvenGoldbachUpTo N0) (hS : SmallRange) :
    ∀ x : ℕ, Odd x → 1 < x → AtMostPrimes 5 x := by
  intro x hx h1
  rcases Nat.lt_or_ge X0 x with h | h
  · obtain ⟨p, q, r, m, hp, hq, hr, hm2, hmN, hs⟩ := h82 x h
    exact five_of_three_plus_small h16 hx hp hq hr hm2 hmN hs
  · exact hS x hx h1 h

/-- Abstract: this improves Ramaré's six primes for even numbers and gives Schnirelmann's
constant at most six. Proved in the lab from Theorem 1.4 alone. -/
theorem every_even_at_most_six_of (h14 : ∀ x : ℕ, Odd x → 1 < x → AtMostPrimes 5 x) :
    ∀ n : ℕ, Even n → AtMostPrimes 6 n := by
  intro n hn
  obtain ⟨k, rfl⟩ := hn
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k
    · exact AtMostPrimes.zero.mono (by norm_num)
    · exact (AtMostPrimes.prime Nat.prime_two).mono (by norm_num)
    · have h := (AtMostPrimes.prime Nat.prime_two).add (AtMostPrimes.prime Nat.prime_two)
      exact h.mono (by norm_num)
  · have h := (AtMostPrimes.prime Nat.prime_three).add
      (h14 (k + k - 3) ⟨k - 2, by omega⟩ (by omega))
    rw [show 3 + (k + k - 3) = k + k by omega] at h
    exact h

theorem every_at_most_six_of (h14 : ∀ x : ℕ, Odd x → 1 < x → AtMostPrimes 5 x) :
    ∀ n : ℕ, 1 < n → AtMostPrimes 6 n := by
  intro n hn
  rcases Nat.even_or_odd n with he | ho
  · exact every_even_at_most_six_of h14 n he
  · exact (h14 n ho hn).mono (by norm_num)

end LeanLab.Tao2012
