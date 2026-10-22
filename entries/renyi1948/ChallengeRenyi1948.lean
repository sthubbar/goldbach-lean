module

public import Mathlib

/-!
# Rényi's theorem, Rényi 1948

A. Rényi, *On the representation of an even number as the sum of a single prime and a single
almost-prime number*, Izv. Akad. Nauk SSSR Ser. Mat. 12, no. 1, 1948, 57-78, MR 23863,
Zbl 0038.18601, Math-Net.Ru im3018. There is a constant `K`
such that every sufficiently large even number `N` is `p + m` with `p` prime and `m` having at
most `K` prime factors.

`Ω(m)`, Mathlib's `ArithmeticFunction.cardFactors m`, counts the prime factors of `m` with
multiplicity. Every statement is unconditional and ineffective: the threshold `N₀` comes through
the Siegel-Walfisz theorem inside the Bombieri-Vinogradov theorem, as in the classical proofs.

The target theorems, each proved in the solution with no hypothesis, are:
* `renyi8_fixedK`: Rényi's theorem with `K = 8`: every even `N ≥ N₀` is `p + m` with `p` prime,
  `m ≥ 1` and `Ω(m) ≤ 8`;
* `renyi8_fixedK_count`: the counting form with `K = 8`,
  `#{p < N prime : Ω(N - p) ≤ 8} ≥ e^{-36} N / (2 log² N)` for every even `N ≥ N₀`;
* `renyi_fixedK` and `renyi_fixedK_count`: the same two statements with the weaker `K = 13000`,
  the first version proved in the lab, the count `≥ 1000 e^{-36} N / log² N`;
* `twin_renyi_count`: a derived analogue proved in this entry by the same sieve method, a
  twin-prime analogue of Rényi's theorem with `K = 13000`, not a result of Rényi 1948:
  `#{p ≤ N prime : Ω(p + 2) ≤ 13000} ≥ 1000 e^{-36} N / log² N` for every `N ≥ N₀`, so there are
  infinitely many primes `p` with `Ω(p + 2) ≤ 13000`;
* `renyi8_isAtMostAlmostPrime`: `renyi8_fixedK` phrased with Mathlib's
  `Nat.IsAtMostAlmostPrime 8 m`, which is `m ≠ 0 ∧ Ω(m) ≤ 8`.

Nothing here is new mathematics: Pan has `K = 4` and Chen 1973 has `K = 2`. Binary Goldbach is
`Ω(m) = 1` and is open; nothing here claims it. The twin prime conjecture is open too. Lean names
keep the namespace of the lab where the proofs were written, `LeanLab.PNTPort.BVMax`. An AI agent,
Claude by Anthropic, wrote the Lean code; the zero-free region for ζ and the prime number theorem
files under `LeanLab/PNTPort/StrongPNT` are ported from PrimeNumberTheoremAnd, Apache-2.0.
-/

@[expose] public section

namespace LeanLab.PNTPort.BVMax

open Finset

open Filter in
/-- Rényi's theorem with the count and `K = 8`. -/
theorem renyi8_fixedK_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    Real.exp (-36) * N / (2 * Real.log N ^ 2) ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 8)).card : ℝ) := by
  sorry

/-- Rényi's theorem with `K = 8`. -/
theorem renyi8_fixedK : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ ArithmeticFunction.cardFactors m ≤ 8 := by
  sorry

open Filter in
/-- Rényi's theorem with `K = 13000`. -/
theorem renyi_fixedK : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ ArithmeticFunction.cardFactors m ≤ 13000 := by
  sorry

open Filter in
/-- Rényi's theorem with the count and `K = 13000`. -/
theorem renyi_fixedK_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    1000 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 13000)).card : ℝ) := by
  sorry

open Filter in
/-- A derived analogue proved in this entry by the same sieve method, a twin-prime analogue of
Rényi's theorem with the count and `K = 13000`; not a result of Rényi 1948. -/
theorem twin_renyi_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    1000 * Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((Icc 1 N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 13000)).card : ℝ) := by
  sorry

/-- Rényi's theorem with `K = 8`, stated with Mathlib's `Nat.IsAtMostAlmostPrime`. -/
theorem renyi8_isAtMostAlmostPrime : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ Nat.IsAtMostAlmostPrime 8 m ∧ N = p + m := by
  sorry

end LeanLab.PNTPort.BVMax
