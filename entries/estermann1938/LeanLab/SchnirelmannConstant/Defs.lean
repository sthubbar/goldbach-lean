module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
Shared definitions for papers on Schnirelmann's constant.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.SchnirelmannConstant

/-- `n` is a sum of at most `k` primes. -/
def AtMostPrimes (k n : ℕ) : Prop :=
  ∃ l : List ℕ, l.length ≤ k ∧ (∀ p ∈ l, p.Prime) ∧ l.sum = n

theorem AtMostPrimes.mono {k k' n : ℕ} (h : AtMostPrimes k n) (hk : k ≤ k') :
    AtMostPrimes k' n := by
  obtain ⟨l, hl, hp, hs⟩ := h
  exact ⟨l, hl.trans hk, hp, hs⟩

theorem AtMostPrimes.add {a b m n : ℕ} (ha : AtMostPrimes a m) (hb : AtMostPrimes b n) :
    AtMostPrimes (a + b) (m + n) := by
  obtain ⟨l, hl, hp, hs⟩ := ha
  obtain ⟨l', hl', hp', hs'⟩ := hb
  refine ⟨l ++ l', ?_, ?_, ?_⟩
  · simp; omega
  · intro p hpl; rcases List.mem_append.mp hpl with h | h
    · exact hp p h
    · exact hp' p h
  · simp [hs, hs']

theorem AtMostPrimes.prime {p : ℕ} (hp : p.Prime) : AtMostPrimes 1 p :=
  ⟨[p], by simp, by simpa using hp, by simp⟩

theorem AtMostPrimes.zero : AtMostPrimes 0 0 := ⟨[], by simp, by simp, by simp⟩

theorem AtMostPrimes.of_goldbach {n : ℕ} (h : IsGoldbachSum n) : AtMostPrimes 2 n := by
  obtain ⟨p, q, hp, hq, rfl⟩ := h
  exact (AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)

/-- An even `m` with `m ≤ N` is a sum of at most two primes, given even Goldbach up to `N`. -/
theorem atMost2_of_even {N m : ℕ} (hG : EvenGoldbachUpTo N) (hev : Even m) (hm : m ≤ N) :
    AtMostPrimes 2 m := by
  rcases Nat.lt_or_ge m 4 with h | h
  · obtain ⟨k, rfl⟩ := hev
    have hk : k < 2 := by omega
    interval_cases k
    · exact AtMostPrimes.zero.mono (by norm_num)
    · exact (AtMostPrimes.prime Nat.prime_two).mono (by norm_num)
  · exact AtMostPrimes.of_goldbach (hG m hev h hm)

end LeanLab.SchnirelmannConstant
