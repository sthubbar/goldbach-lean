module

public import Mathlib
public import LeanLab.HelfgottPlatt.Proth

/-!
Helfgott and Platt 2013, P0006, unit U-1455, run 20261022T0003Z-15508.
Section 2 of the paper in full: Theorem 2.3 with the paper's Jacobi hypothesis, and the
converse the paper prints right after it, that for a prime N the congruence
a^((N-1)/2) = -1 mod N holds for EVERY a whose Jacobi symbol over N is -1. Together with the
existence of a quadratic nonresidue mod an odd prime this gives the full Proth criterion:
a Proth number is prime if and only if some a has Jacobi symbol -1 and a^((N-1)/2) = -1.

The converse is Euler's criterion; the existence of a nonresidue is a finite field fact;
both come from Mathlib. Nothing here is new mathematics.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.

This file is the lab file `LeanLab/HelfgottPlatt/HelfgottPlattU1455ProthIff.lean` in module
syntax; no declaration was removed.
-/

@[expose] public section

namespace LeanLab.HelfgottPlatt.U1455

open LeanLab.HelfgottPlatt.Proth

/-- Any integer residue mod `N` is the cast of a natural number. -/
theorem exists_nat_cast {N : ℕ} [NeZero N] (a : ℤ) : ∃ b : ℕ, (b : ZMod N) = (a : ZMod N) :=
  ⟨(a : ZMod N).val, ZMod.natCast_zmod_val _⟩

/-- Theorem 2.3 exactly as printed: a Proth number `N = k 2^n + 1`, `0 < k < 2^n`, `n = m + 1`,
with some `a` such that the Jacobi symbol `(a / N)` is `-1` and `a^((N-1)/2) = -1 mod N`, is
prime. The Jacobi hypothesis is carried but not used, see `Proth.proth`. -/
theorem theorem2_3 {k m N : ℕ} {a : ℤ} (hk0 : 0 < k) (hk : k < 2 ^ (m + 1))
    (hN : N = k * 2 ^ (m + 1) + 1) (_hJ : jacobiSym a N = -1)
    (ha : (a : ZMod N) ^ ((N - 1) / 2) = -1) : N.Prime := by
  have hNe : (N - 1) / 2 = k * 2 ^ m := by
    rw [hN, Nat.add_sub_cancel, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num)]
  have : NeZero N := ⟨by omega⟩
  obtain ⟨b, hb⟩ := exists_nat_cast (N := N) a
  refine proth (a := b) hk0 hk hN ?_
  rw [hb, ← hNe]; exact ha

/-- The converse printed after Theorem 2.3: if `N` is an odd prime then every `a` with Jacobi
symbol `-1` over `N` satisfies `a^((N-1)/2) = -1 mod N`. Euler's criterion. -/
theorem converse {N : ℕ} (hp : N.Prime) (h2 : N ≠ 2) {a : ℤ} (hJ : jacobiSym a N = -1) :
    (a : ZMod N) ^ ((N - 1) / 2) = -1 := by
  have : Fact N.Prime := ⟨hp⟩
  have hL : legendreSym N a = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hJ
  have h := legendreSym.eq_pow N a
  rw [hL] at h
  have hdiv : (N - 1) / 2 = N / 2 := by
    obtain ⟨x, hx⟩ := hp.odd_of_ne_two h2
    omega
  rw [hdiv, ← h]
  simp

/-- The converse for a Proth prime, in the exponent `k 2^m` the computation uses. -/
theorem converse_proth {k m N : ℕ} (hk0 : 0 < k) (hN : N = k * 2 ^ (m + 1) + 1) (hp : N.Prime)
    {a : ℤ} (hJ : jacobiSym a N = -1) : (a : ZMod N) ^ (k * 2 ^ m) = -1 := by
  have hNe : (N - 1) / 2 = k * 2 ^ m := by
    rw [hN, Nat.add_sub_cancel, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num)]
  have h2 : N ≠ 2 := by
    intro h; rw [h] at hN
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [pow_succ] at hN; nlinarith
  rw [← hNe]
  exact converse hp h2 hJ

/-- An odd prime has a quadratic nonresidue, that is an integer with Jacobi symbol `-1`. -/
theorem exists_jacobi_neg_one {N : ℕ} (hp : N.Prime) (h2 : N ≠ 2) :
    ∃ a : ℤ, jacobiSym a N = -1 := by
  have : Fact N.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod N) (by rw [ZMod.ringChar_zmod_n]; exact h2)
  refine ⟨(x.val : ℤ), ?_⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
  simpa using hx

/-- The full Proth criterion, Section 2: a Proth number is prime if and only if some `a`
has Jacobi symbol `-1` over `N` and `a^((N-1)/2) = -1 mod N`. -/
theorem proth_iff {k m N : ℕ} (hk0 : 0 < k) (hk : k < 2 ^ (m + 1))
    (hN : N = k * 2 ^ (m + 1) + 1) :
    N.Prime ↔ ∃ a : ℤ, jacobiSym a N = -1 ∧ (a : ZMod N) ^ ((N - 1) / 2) = -1 := by
  constructor
  · intro hp
    have h2 : N ≠ 2 := by
      intro h; rw [h] at hN
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      rw [pow_succ] at hN; nlinarith
    obtain ⟨a, ha⟩ := exists_jacobi_neg_one hp h2
    exact ⟨a, ha, converse hp h2 ha⟩
  · rintro ⟨a, hJ, ha⟩
    exact theorem2_3 hk0 hk hN hJ ha

/-! ### Vacuity instances -/

/-- 13 = 3 · 2^2 + 1 is a Proth number; a = 2 has Jacobi symbol -1 and 2^6 = -1 mod 13. -/
theorem vac_jacobi : jacobiSym 2 13 = -1 := by norm_num

theorem vac_pow : ((2 : ℤ) : ZMod 13) ^ ((13 - 1) / 2) = -1 := by decide

theorem vac_theorem2_3 : (13 : ℕ).Prime :=
  theorem2_3 (k := 3) (m := 1) (by norm_num) (by norm_num) (by norm_num) vac_jacobi vac_pow

/-- The converse fires on a Proth prime: 5 has Jacobi symbol -1 over 13 = 3 · 2^2 + 1, so
5^6 = -1 mod 13 follows from primality alone. -/
theorem vac_converse : ((5 : ℤ) : ZMod 13) ^ (3 * 2 ^ 1) = -1 :=
  converse_proth (k := 3) (m := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end LeanLab.HelfgottPlatt.U1455
