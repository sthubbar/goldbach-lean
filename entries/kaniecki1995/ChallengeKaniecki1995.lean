module

public import Mathlib

/-!
# Kaniecki's Lemma 7 on sums of two odd primes in short intervals, corrected

L. Kaniecki, On Šnirelman's constant under the Riemann hypothesis, Acta Arith. 72, 1995,
361-374. Page 371 defines, for consecutive primes `p < p'`, the gap function
`λ(x) = 2` for `0 < x ≤ 7` and `λ(x) = max_{p ≤ x} (p' - p)` for `x > 7`, and states

  Lemma 7. Every interval of the form `(x, x + λ(λ(x)))`, `x > 4`, contains a sum of two
  odd primes.

As printed, with the open interval, the lemma is false: at `x = 6`, `λ(6) = λ(2) = 2` and the
open interval `(6, 8)` contains no even number. The printed proof goes through when the right
end is included, which is the form the paper uses later, since Section 3 applies the lemma only
through closed intervals `[x, x + h]`. This file states:

* `LeanLab.Kaniecki1995.not_lemma7_printed`: Lemma 7 as printed, for real `x > 4`, is false;
* `LeanLab.KanieckiGap.lemma7_printed_false_at_6`: the same failure, at the integer `x = 6`;
* `LeanLab.KanieckiGap.RealIntervals127.lemma7_closed_real`: for every real `x > 4` there are
  odd primes `p, q` with `x < p + q ≤ x + λ(λ(x))`;
* `LeanLab.KanieckiGap.lemma7_closed`: the same corrected statement for every integer `x > 4`,
  with `λ` computed on the integers.

None of these uses the Riemann hypothesis or any cited input.
-/

@[expose] public section

namespace LeanLab.Kaniecki1995
open Finset

/-- The least prime larger than `p`. -/
noncomputable def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- Kaniecki's gap function on the reals, page 371: `λ(x) = 2` for `x ≤ 7`, and for `x > 7`
the largest gap `p' - p` between a prime `p ≤ x` and the next prime `p'`. The paper defines
`λ` for `x > 0`; the value `2` for `x ≤ 0` is never used, since `λ(x) ≥ 2 > 0`. -/
noncomputable def lam (x : ℝ) : ℕ :=
  if x ≤ 7 then 2 else ((range (⌊x⌋₊ + 1)).filter Nat.Prime).sup (fun p => nextPrime p - p)

/-- Lemma 7 as printed, page 371: for every real `x > 4` the open interval
`(x, x + λ(λ(x)))` contains a sum `p + q` of two odd primes. -/
def Lemma7Printed : Prop :=
  ∀ x : ℝ, 4 < x → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧
    x < ((p + q : ℕ) : ℝ) ∧ ((p + q : ℕ) : ℝ) < x + (lam (lam x) : ℝ)

/-- Lemma 7 as printed is false. -/
theorem not_lemma7_printed : ¬ Lemma7Printed := by
  sorry

end LeanLab.Kaniecki1995

namespace LeanLab.KanieckiGap

/-- The least prime greater than `p`. -/
noncomputable def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- The gap `p' - p` from `p` to the next prime. -/
noncomputable def gapAt (p : ℕ) : ℕ := nextPrime p - p

/-- Kaniecki's `λ` at a natural number `x`: `2` for `x ≤ 7`, else the largest gap `p' - p`
over primes `p ≤ x`. It agrees with the real `λ` at every natural number. -/
noncomputable def lam (x : ℕ) : ℕ :=
  if x ≤ 7 then 2 else ((Finset.range (x + 1)).filter Nat.Prime).sup gapAt

/-- Lemma 7 as printed fails at `x = 6`: no sum of two odd primes lies in the open
interval `(6, 6 + λ(λ(6))) = (6, 8)`. -/
theorem lemma7_printed_false_at_6 :
    ¬ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ Odd p₁ ∧ p₂.Prime ∧ Odd p₂ ∧
      6 < p₁ + p₂ ∧ p₁ + p₂ < 6 + lam (lam 6) := by
  sorry

/-- Lemma 7 with the right end included, for integers: for every integer `x > 4` there are
odd primes `p₁, p₂` with `x < p₁ + p₂ ≤ x + λ(λ(x))`. -/
theorem lemma7_closed (x : ℕ) (hx : 4 < x) :
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ Odd p₁ ∧ p₂.Prime ∧ Odd p₂ ∧
      x < p₁ + p₂ ∧ p₁ + p₂ ≤ x + lam (lam x) := by
  sorry

end LeanLab.KanieckiGap

namespace LeanLab.KanieckiGap.RealIntervals127

open Real

/-- Lemma 7 with the right end included, page 371: for every real `x > 4` there are odd
primes `p, q` with `x < p + q ≤ x + λ(λ(x))`. -/
theorem lemma7_closed_real (x : ℝ) (hx : 4 < x) :
    ∃ p q : ℕ, p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧
      x < ((p + q : ℕ) : ℝ) ∧
      ((p + q : ℕ) : ℝ) ≤ x +
        (LeanLab.Kaniecki1995.lam (LeanLab.Kaniecki1995.lam x) : ℝ) := by
  sorry

end LeanLab.KanieckiGap.RealIntervals127
