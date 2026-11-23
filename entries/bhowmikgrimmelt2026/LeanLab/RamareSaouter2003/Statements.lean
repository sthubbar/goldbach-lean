module

public import Mathlib
public import LeanLab.Tao2012.SmallRange

/-!
P0099, O. Ramaré and Y. Saouter, Short effective intervals containing primes,
J. Number Theory 98 (2003) 10-33. Read 2026-10-16 from Ramaré's copy,
https://ramare-olivier.github.io/Maths/gap.pdf, by a subagent of run 20261016T2102Z-17972.
Cited results are stated without proof in the lab and removed from this copy; links to the lab's earlier forms proved.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.RamareSaouter2003
open Real LeanLab.SchnirelmannConstant

/-- Theorem 1: under RH, `]x - (8/5) √x log x, x]` contains a prime for `x ≥ 2`. -/
def theorem1_stmt : Prop := RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x - 8 / 5 * √x * Real.log x < p ∧ (p : ℝ) ≤ x

/-- Theorem 3: for real `x > 10 726 905 041` the interval `]x (1 - 1/28 314 000), x]`
contains a prime. The abstract says `x ≥`; the theorem says larger than; the lab states `>`. -/
def theorem3_stmt : Prop := ∀ x : ℝ, 10726905041 < x →
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x

/-- Theorem 2 for the Table 1 row `log x0 = 59`, `Δ = 209 257 759`. -/
def theorem2_row59_stmt : Prop := ∀ x : ℝ, Real.exp 59 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 209257759) < p ∧ (p : ℝ) ≤ x

/-- Corollary 1: every odd integer `> 1` not more than `1.13256 · 10^22` is a sum of at most
three primes. -/
def corollary1_stmt : Prop := ∀ n : ℕ, Odd n → 1 < n → n ≤ 113256 * 10 ^ 17 → AtMostPrimes 3 n

/-- The lab's natural number form, used by Tao2012 and DERZ1997, follows from Theorem 3. -/
theorem rsShortIntervals_of
    (h : ∀ x : ℝ, 10726905041 < x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x) :
    LeanLab.Tao2012.RSShortIntervals := by
  intro y hy
  obtain ⟨p, hp, hl, hu⟩ := h y (by exact_mod_cast hy)
  have hpy : p ≤ y := by exact_mod_cast hu
  refine ⟨p, hp, hpy, ?_⟩
  have hc : ((y - p : ℕ) : ℝ) = (y : ℝ) - p := Nat.cast_sub hpy
  have : (28314000 : ℝ) * ((y : ℝ) - p) < y := by
    have e : (y : ℝ) * (1 - 1 / 28314000) = y - y / 28314000 := by ring
    rw [e] at hl
    have : (y : ℝ) - p < y / 28314000 := by linarith
    rw [lt_div_iff₀ (by norm_num)] at this
    linarith
  rw [← hc] at this
  simp only [LeanLab.Tao2012.Δ]
  exact_mod_cast this

/-- Tao's odd Goldbach input to `1.13 · 10^22` follows from Corollary 1. -/
theorem oddGoldbach_of
    (h : ∀ n : ℕ, Odd n → 1 < n → n ≤ 113256 * 10 ^ 17 → AtMostPrimes 3 n) :
    LeanLab.Tao2012.OddGoldbachTo113e20 := by
  intro n hn h7 hle
  exact h n hn (by omega) (by omega)

end LeanLab.RamareSaouter2003
