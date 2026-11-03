module

public import Mathlib

/-!
# Goldbach numbers in short intervals of length `x^(26/1075+ε)`

The main theorem, `LeanLab.GoldbachShort78.goldbach_short_1075`: for every `ε > 0` and all large
natural `x` there is an even sum of two primes in `[x, x + 3 x^{26/1075+ε}]`.

It takes two cited results as explicit hypotheses, never as axioms, and neither is proved here.
* `LiRow052`, R. Li, The number of primes in short intervals and numerical calculations for
  Harman's sieve, arXiv 2308.04458, Theorem 2, page 2, the row `θ = 0.52`, with some positive
  constant `c`, since the printed value of `LB(0.520)` differs between versions of the paper.
* `LiPrintedExceptionalCount`, R. Li, Primes in almost all short intervals, arXiv 2407.05651 v6,
  Theorem 1.1, page 2.

The argument adapts Theorem 7.1, page 27, of arXiv 2407.05651 v6, exponent `21/860` from the `0.525`
of Baker, Harman and Pintz. The exponent `26/1075` is `0.52 · 1/21.5`, lower than `21/860` by
`1/4300`, and the gain is only the replacement of `0.525` by Li's `0.52`. Li prints the same exponent
as Theorem 7 of arXiv 2308.04458, with no `ε` and no factor `3`, so the statement here is the slightly
weaker form that follows from the two theorems as printed.

Also compared: `windowCount_of_backward` and `goldbach_of_counts`, the two steps of the argument,
both proved with no cited input, and `exponent_1075`, the exponent arithmetic.

Binary Goldbach is open and is not claimed. AI agents wrote the Lean code, Claude, Anthropic, Codex,
OpenAI, and Gemini, Google. Lean names keep the namespaces of the lab where the proofs were written;
every definition below is restated under its exact name and in the same `open` context as in the
solution files.
-/

@[expose] public section

/-! ### Sums of two primes, `LeanLab/Common/Goldbach.lean` -/

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

end LeanLab

/-! ### Goldbach numbers and counts, `LeanLab/GoldbachShort78/Statements.lean` -/

namespace LeanLab.GoldbachShort78
open Real

/-- A Goldbach number: an even sum of two primes. -/
def IsGoldbachNumber (n : ℕ) : Prop := Even n ∧ IsGoldbachSum n

/-- The primes in `[x − 2Y, x − Y]`, with subtraction in `ℕ`. -/
noncomputable def primeWindow (x Y : ℕ) : Finset ℕ :=
  (Finset.Icc (x - 2 * Y) (x - Y)).filter Nat.Prime

/-- The `z ∈ [Y, 2Y]` with no prime in `[z, z + H]`. -/
noncomputable def badSet (Y H : ℕ) : Finset ℕ :=
  (Finset.Icc Y (2 * Y)).filter (fun z => ∀ q ∈ Finset.Icc z (z + H), ¬ q.Prime)

/-- Count in all windows: for `x ≥ x₀` and `Y ≥ x^a` with `2Y + 3 ≤ x`, the window
`[x − 2Y, x − Y]` holds at least `c Y / log x` primes. -/
def WindowCount (a c x₀ : ℝ) : Prop :=
  ∀ x : ℕ, x₀ ≤ x → ∀ Y : ℕ, (x : ℝ) ^ a ≤ Y → 2 * Y + 3 ≤ x →
    c * Y / Real.log x ≤ (primeWindow x Y).card

/-- The combinatorial step, proved with no cited input: if fewer `z ∈ [Y, 2Y]` have a prime free
`[z, z + H]` than there are primes in `[x − 2Y, x − Y]`, some `n ∈ [x, x + H]` is a Goldbach number. -/
theorem goldbach_of_counts {x Y H : ℕ} (hY : 3 ≤ Y) (hx : 2 * Y + 3 ≤ x)
    (hcount : (badSet Y H).card < (primeWindow x Y).card) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧ n ≤ x + H := by
  sorry

end LeanLab.GoldbachShort78

/-! ### Primes in real intervals, `LeanLab/GoldbachShort78/Tiling.lean` -/

namespace LeanLab.GoldbachShort78

/-- The primes `p` with `a < p ≤ b`, for real `a`, `b`. -/
noncomputable def primeInterval (a b : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌈b⌉₊).filter fun p => a < (p : ℝ) ∧ (p : ℝ) ≤ b ∧ p.Prime

end LeanLab.GoldbachShort78

/-! ### The almost all input, `LeanLab/GoldbachShort78/LiNormalization.lean` -/

namespace LeanLab.GoldbachShort78

/-- The integers `z ∈ [Y, 2Y]` whose closed interval `[z, z + z^a]` has no prime. -/
noncomputable def powerBadSet (a : ℝ) (Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc Y (2 * Y)).filter fun z =>
    ∀ p : ℕ, z ≤ p → (p : ℝ) ≤ z + (z : ℝ) ^ a → ¬p.Prime

/-- Cited input, R. Li, arXiv 2407.05651 v6, Theorem 1.1, page 2, in exceptional count form: for
every `η > 0` and all large `Y`, at most `C Y / log³ Y` of the integers `z ∈ [Y, 2Y]` have no prime
in `[z, z + z^{1/21.5 + η}]`. The theorem allows every large power of the
logarithm, and the power three follows, since `log^{-B} ≤ log^{-3}` for `B ≥ 3`. It is printed for sufficiently small positive `ε`, and a longer interval
can only have fewer exceptions, so it extends to every `η > 0`. -/
def LiPrintedExceptionalCount : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C y₀ : ℝ, 0 < C ∧ ∀ Y : ℕ, y₀ ≤ Y →
    ((powerBadSet (1 / 21.5 + η) Y).card : ℝ) ≤ C * Y / Real.log Y ^ 3

end LeanLab.GoldbachShort78

/-! ### The main results, `LeanLab/GoldbachShort78/Short1075.lean` -/

namespace LeanLab.GoldbachShort78

open Real

/-- The exponent arithmetic: `0.52 · 1/21.5 = 26/1075`, below the `21/860` of R. Li, arXiv
2407.05651 v6, Theorem 7.1, by `1/4300`. -/
theorem exponent_1075 :
    (0.52 : ℝ) * (1 / 21.5) = 26 / 1075 ∧ (26 : ℝ) / 1075 < 21 / 860 ∧
      (21 : ℝ) / 860 - 26 / 1075 = 1 / 4300 := by
  sorry

/-- Cited input, R. Li, arXiv 2308.04458, Theorem 2, page 2, the row `θ = 0.52`, with some positive
constant `c` in place of the printed `LB(0.520)`: for `0 < ε ≤ 0.005` and all large integers `n`, the
interval `(n − n^{0.52+ε}, n]` holds more than `c n^{0.52+ε} / log n` primes. The printed value of
`LB(0.520)` differs between versions of the paper, so only its positivity is assumed. -/
def LiRow052 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 0.005 → ∃ X : ℝ, ∀ n : ℕ, X ≤ n →
    c * (n : ℝ) ^ (0.52 + ε : ℝ) / Real.log n <
      ((primeInterval ((n : ℝ) - (n : ℝ) ^ (0.52 + ε : ℝ)) n).card : ℝ)

/-- Proved with no cited input: a count of primes in `(n − n^a, n]` for all large integers `n` gives
`WindowCount a (c/32)`. Tiles have the integer length `⌈x^a⌉`, so every right endpoint is an integer,
as the hypothesis needs. -/
theorem windowCount_of_backward {a c X : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hc : 0 < c)
    (hin : ∀ n : ℕ, X ≤ n →
      c * (n : ℝ) ^ a / Real.log n < ((primeInterval ((n : ℝ) - (n : ℝ) ^ a) n).card : ℝ)) :
    ∃ x₀ : ℝ, WindowCount a (c / 32) x₀ := by
  sorry

/-- Goldbach numbers in `[x, x + 3 x^{26/1075+ε}]`: for every `ε > 0` and all large natural `x` there
is an even sum of two primes in this interval. The two cited results `LiRow052` and
`LiPrintedExceptionalCount` are explicit hypotheses. -/
theorem goldbach_short_1075 (hRow : LiRow052) (hLi : LiPrintedExceptionalCount) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℕ, X ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x ≤ n ∧ (n : ℝ) ≤ x + 3 * (x : ℝ) ^ (26 / 1075 + ε : ℝ) := by
  sorry

end LeanLab.GoldbachShort78
