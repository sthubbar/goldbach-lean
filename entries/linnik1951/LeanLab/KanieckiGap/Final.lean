module

public import Mathlib
public import LeanLab.Common.GoldbachSmall
public import LeanLab.SchnirelmannConstant.Defs
public import LeanLab.KanieckiGap.Lemma6

/-!
P0022 L. Kaniecki 1995, Acta Arith. 72, page 373, the end of the proof of the Theorem, read
from the page image of papers/P0022.pdf, cloud session 20261019T1116Z-cloud23, unit U-5464.

Printed: "every interval of the form [x, x + 1.4045 · 10^12], x ≤ n₀, contains at least one sum
of two odd primes. Applying this observation with x = n - 2 we infer that for every
9 < n ≤ n₀ there exist two odd prime numbers p₁ and p₂ such that
3 < m := n - (p₁ + p₂) < 1.405 · 10^12. If n is odd then m is odd as well, and according to
[14] and [16] it is a sum of at most three primes. Hence n itself is a sum of at most five
primes."

Here:
* `printed_choice_useless`: with x = n - 2 every sum in [x, x + h] is ≥ n - 2, so m ≤ 2 and
  3 < m never follows; `step_m` takes x = n - 4 - h instead, cosmetic.
* `odd_m_three`: every odd m with 7 ≤ m ≤ 1.405 · 10^12 is a sum of three primes, from
  `YoungPotler` [16] and even Goldbach to 1000, kernel checked; [14], Sinisalo's 4 · 10^11,
  is not needed.
* `kaniecki_odd_of`: every odd n > 1 is a sum of at most five primes, CONDITIONAL ON the
  interval statement for x ≤ N₀, odd n > N₀ a sum of three primes, the Chen-Wang input,
  and `YoungPotler`. Natural x only in the interval statement, a weaker hypothesis than the
  paper's real x.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Goldbach is OPEN; ternary Goldbach, Helfgott 2013, already implies the odd statement.
-/

@[expose] public section

namespace LeanLab.KanieckiGap
open LeanLab.SchnirelmannConstant

/-- The interval statement Kaniecki derives from Lemmas 4 to 7, at integers `x ≤ N₀`:
`[x, x + H]` holds a sum of two odd primes. CITED as a hypothesis. -/
def IntervalProp (H N₀ : ℕ) : Prop :=
  ∀ x : ℕ, x ≤ N₀ → ∃ p₁ p₂ : ℕ, p₁.Prime ∧ Odd p₁ ∧ p₂.Prime ∧ Odd p₂ ∧
    x ≤ p₁ + p₂ ∧ p₁ + p₂ ≤ x + H

/-- The printed choice `x = n - 2` cannot give `3 < n - (p₁ + p₂)`. -/
theorem printed_choice_useless {n s : ℕ} (h : n - 2 ≤ s) : ¬ 3 < n - s := by omega

/-- The step with `x = n - 4 - H`: for `9 < n ≤ N₀` there are odd primes with
`4 ≤ n - (p₁ + p₂) ≤ H + 4`. -/
theorem step_m {H N₀ : ℕ} (hI : IntervalProp H N₀) {n : ℕ} (hn : 9 < n) (hnN : n ≤ N₀) :
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ Odd p₁ ∧ p₂.Prime ∧ Odd p₂ ∧
      p₁ + p₂ + 4 ≤ n ∧ n - (p₁ + p₂) ≤ H + 4 := by
  rcases Nat.lt_or_ge n (H + 4) with hs | hb
  · exact ⟨3, 3, Nat.prime_three, by decide, Nat.prime_three, by decide, by omega, by omega⟩
  · obtain ⟨p₁, p₂, h1, o1, h2, o2, hx1, hx2⟩ := hI (n - 4 - H) (by omega)
    exact ⟨p₁, p₂, h1, o1, h2, o2, by omega, by omega⟩

/-- Every odd `m` with `7 ≤ m ≤ 1.405 · 10^12` is a sum of three primes, given Young-Potler. -/
theorem odd_m_three (hY : YoungPotler) {m : ℕ} (ho : Odd m) (h7 : 7 ≤ m)
    (hm : m ≤ 1405 * 10 ^ 9) : IsTernarySum m := by
  classical
  have h3 : (3 : ℕ).Prime := Nat.prime_three
  set p := Nat.findGreatest Nat.Prime (m - 4) with hp
  have hpP : p.Prime := Nat.findGreatest_spec (m := 3) (by omega) h3
  have hp3 : 3 ≤ p := Nat.le_findGreatest (by omega) h3
  have hpm : p ≤ m - 4 := Nat.findGreatest_le _
  obtain ⟨hn1, hn2⟩ := nextPrime_spec p
  have hnm : m - 4 < nextPrime p := by
    by_contra h
    exact Nat.findGreatest_is_greatest (P := Nat.Prime) hn1 (by omega) hn2
  have h2p := nextPrime_le_two_mul (p := p) (by omega)
  have hg := hY p hpP (by omega)
  unfold gapAt at hg
  have hpo : Odd p := hpP.odd_of_ne_two (by omega)
  have hev : Even (m - p) := Nat.Odd.sub_odd ho hpo
  obtain ⟨q, r, hq, hr, hqr⟩ :=
    evenGoldbachUpTo_1000 (m - p) hev (by omega) (by omega)
  exact ⟨p, q, r, hpP, hq, hr, by omega⟩

/-- **Kaniecki, the odd half of the Theorem**, CONDITIONAL ON the interval statement with
`H = 1.4045 · 10^12` up to `N₀`, on every odd `n > N₀` being a sum of three primes, and on
`YoungPotler`: every odd `n > 1` is a sum of at most five primes. -/
theorem kaniecki_odd_of {N₀ : ℕ} (hI : IntervalProp (14045 * 10 ^ 8) N₀)
    (hCW : ∀ n : ℕ, Odd n → N₀ < n → IsTernarySum n) (hY : YoungPotler) :
    ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := by
  intro n ho h1
  rcases Nat.lt_or_ge N₀ n with hbig | hsmall
  · obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := hCW n ho hbig
    exact (((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add
      (AtMostPrimes.prime hr)).mono (by norm_num)
  rcases Nat.lt_or_ge n 10 with hlow | hn
  · -- 3, 5, 7 are prime and 9 = 2 + 7
    obtain ⟨k, rfl⟩ := ho
    have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact (AtMostPrimes.prime Nat.prime_three).mono (by norm_num)
    · exact (AtMostPrimes.prime (by norm_num : Nat.Prime 5)).mono (by norm_num)
    · exact (AtMostPrimes.prime (by norm_num : Nat.Prime 7)).mono (by norm_num)
    · exact ((AtMostPrimes.prime Nat.prime_two).add
        (AtMostPrimes.prime (by norm_num : Nat.Prime 7))).mono (by norm_num)
  obtain ⟨p₁, p₂, h1', o1, h2', o2, hle, hm⟩ := step_m hI (by omega) hsmall
  have hpp : AtMostPrimes 2 (p₁ + p₂) :=
    (AtMostPrimes.prime h1').add (AtMostPrimes.prime h2')
  have hmo : Odd (n - (p₁ + p₂)) := Nat.Odd.sub_even (by omega) ho (o1.add_odd o2)
  have hn' : n = (p₁ + p₂) + (n - (p₁ + p₂)) := by omega
  rcases Nat.lt_or_ge (n - (p₁ + p₂)) 7 with h5 | h7
  · -- m = 5 = 2 + 3
    have h5' : n - (p₁ + p₂) = 5 := by
      obtain ⟨k, hk⟩ := hmo; omega
    rw [hn', h5']
    exact (hpp.add (show AtMostPrimes 2 5 from
      (AtMostPrimes.prime Nat.prime_two).add (AtMostPrimes.prime Nat.prime_three))).mono
      (by norm_num)
  · obtain ⟨p, q, r, hp, hq, hr, hs⟩ := odd_m_three hY hmo h7 (by omega)
    rw [hn', ← hs]
    exact hpp.add (((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add
      (AtMostPrimes.prime hr))

end LeanLab.KanieckiGap

