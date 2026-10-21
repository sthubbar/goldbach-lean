module

public import Mathlib
public import LeanLab.Tao2012.Statements

/-!
Tao 2012, the range of odd x up to 8.7e36, from two cited inputs.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
The argument, subtract two primes found by the Ramaré-Saouter short interval theorem and
finish with odd Goldbach up to 1.13e22, was reconstructed by a VERIFY subagent; the lab has
not read Tao's Section 8, so this is a proof of `SmallRange` from these two hypotheses,
not a transcription of Tao's own argument.
-/

@[expose] public section

namespace LeanLab.Tao2012
open LeanLab.SchnirelmannConstant

/-- `Δ = 28 314 000`, the Ramaré-Saouter 2003 interval ratio. -/
def Δ : ℕ := 28314000

/-- Ramaré-Saouter 2003, P0099, as quoted on a citing page: for every `y > 10 726 905 041`
the interval `(y (1 - 1/Δ), y]` contains a prime. Natural number form: `Δ (y - p) < y`. -/
def RSShortIntervals : Prop :=
  ∀ y : ℕ, 10726905041 < y → ∃ p : ℕ, p.Prime ∧ p ≤ y ∧ Δ * (y - p) < y

/-- Odd Goldbach up to `1.13e22`, credited by Tao to Ramaré and Saouter. -/
def OddGoldbachTo113e20 : Prop :=
  ∀ n : ℕ, Odd n → 7 ≤ n → n ≤ 113 * 10 ^ 20 → AtMostPrimes 3 n

theorem odd_prime_of_big {p : ℕ} (hp : p.Prime) (h : 2 < p) : p % 2 = 1 := by
  rcases hp.eq_two_or_odd with h2 | h2
  · omega
  · exact h2

/-- `SmallRange` from the two inputs, fully proved. -/
theorem small_range_of (hRS : RSShortIntervals) (hOG : OddGoldbachTo113e20) : SmallRange := by
  intro x hx h1 hX
  have hxo := Nat.odd_iff.mp hx
  rcases Nat.lt_or_ge (113 * 10 ^ 20) x with hbig | hsmall
  · -- first prime, just below `x - 2e10`
    obtain ⟨p1, hp1, hp1y, hp1Δ⟩ := hRS (x - 2 * 10 ^ 10) (by omega)
    simp only [Δ] at hp1Δ
    have hp1o : p1 % 2 = 1 := odd_prime_of_big hp1 (by omega)
    -- second prime, just below `x - p1 - 7`
    obtain ⟨p2, hp2, hp2z, hp2Δ⟩ := hRS (x - p1 - 7) (by omega)
    simp only [Δ] at hp2Δ
    have hp2o : p2 % 2 = 1 := odd_prime_of_big hp2 (by omega)
    have hX' : x ≤ 87 * 10 ^ 35 := hX
    have key : 28314000 * (28314000 * (x - p1 - 7 - p2)) < 28314000 * (x - p1 - 7) :=
      Nat.mul_lt_mul_of_pos_left hp2Δ (by norm_num)
    have hr : AtMostPrimes 3 (x - p1 - p2) :=
      hOG _ (Nat.odd_iff.mpr (by omega)) (by omega) (by omega)
    have h := ((AtMostPrimes.prime hp1).add (AtMostPrimes.prime hp2)).add hr
    rw [show p1 + p2 + (x - p1 - p2) = x by omega] at h
    exact h
  · rcases Nat.lt_or_ge x 7 with h7 | h7
    · have : x = 3 ∨ x = 5 := by omega
      rcases this with rfl | rfl
      · exact (AtMostPrimes.prime Nat.prime_three).mono (by norm_num)
      · exact (AtMostPrimes.prime Nat.prime_five).mono (by norm_num)
    · exact (hOG x hx h7 hsmall).mono (by norm_num)

/-- Tao's Theorem 1.4 from Theorem 8.2, Theorem 1.6, Ramaré-Saouter short intervals and odd
Goldbach to 1.13e22. No gap of its own. -/
theorem theorem1_4_of' (h82 : Theorem8_2) (h16 : EvenGoldbachUpTo N0)
    (hRS : RSShortIntervals) (hOG : OddGoldbachTo113e20) :
    ∀ x : ℕ, Odd x → 1 < x → AtMostPrimes 5 x :=
  theorem1_4_of h82 h16 (small_range_of hRS hOG)

end LeanLab.Tao2012
