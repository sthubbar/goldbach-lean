module

public import Mathlib

/-!
P0022, L. Kaniecki, On Šnirelman's constant under the Riemann hypothesis,
Acta Arith. 72, 1995, 361-374. The gap function `λ` of page 371 and Lemma 7 as printed.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is open. Nothing here proves it.

This file is an extract of the lab files `LeanLab/Kaniecki1995/Statements.lean` and
`LeanLab/Kaniecki1995/Reduction.lean`: only the declarations on `λ` and Lemma 7 are kept.
-/

@[expose] public section

namespace LeanLab.Kaniecki1995
open Finset

/-! ### Prime gaps: `λ(x)`, p. 371 -/

/-- The least prime larger than `p`. -/
noncomputable def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- `λ(x) = 2` for `0 < x ≤ 7`, `max_{p ≤ x} (p' - p)` for `x > 7`, p. 371. -/
noncomputable def lam (x : ℝ) : ℕ :=
  if x ≤ 7 then 2 else ((range (⌊x⌋₊ + 1)).filter Nat.Prime).sup (fun p => nextPrime p - p)

/-- Lemma 7 as printed, p. 371: every interval `(x, x + λ(λ(x)))`, `x > 4`, contains a sum of
two odd primes. It is false at `x = 6`, see `not_lemma7_printed`. -/
def Lemma7Printed : Prop :=
  ∀ x : ℝ, 4 < x → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧
    x < ((p + q : ℕ) : ℝ) ∧ ((p + q : ℕ) : ℝ) < x + (lam (lam x) : ℝ)

theorem gap_le_lam {x : ℝ} (hx : 7 < x) {p : ℕ} (hp : p.Prime) (hpx : (p : ℝ) ≤ x) :
    nextPrime p - p ≤ lam x := by
  unfold lam
  rw [if_neg (by linarith)]
  apply Finset.le_sup (f := fun p => nextPrime p - p)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpx), hp⟩

/-! ### Lemma 7 as printed fails at `x = 6` -/

theorem lam_of_le_seven {x : ℝ} (hx : x ≤ 7) : lam x = 2 := by simp [lam, hx]

/-- Lemma 7 as printed, p. 371, is false at `x = 6`.
`λ(6) = 2` and `λ(2) = 2`, and the open interval `(6, 8)` contains no even number. The proof's
step `p₂ - (x - p₁) < λ(x - p₁)` fails for small `x - p₁`. Section 3 only uses the lemma for
large `x` and with closed intervals, so the Theorem is not affected. -/
theorem not_lemma7_printed : ¬ Lemma7Printed := by
  intro h
  obtain ⟨p, q, hp, hq, hop, hoq, h1, h2⟩ := h 6 (by norm_num)
  have e1 : lam 6 = 2 := lam_of_le_seven (by norm_num)
  have e2 : lam 2 = 2 := lam_of_le_seven (by norm_num)
  rw [e1, show ((2 : ℕ) : ℝ) = 2 by norm_num, e2] at h2
  push_cast at h1 h2
  have h1' : 6 < p + q := by exact_mod_cast h1
  have h2' : p + q < 8 := by exact_mod_cast (by linarith : ((p : ℝ) + q) < 8)
  have hpq : p + q = 7 := by omega
  have : Even (p + q) := Odd.add_odd hop hoq
  rw [hpq] at this
  exact absurd this (by decide)

end LeanLab.Kaniecki1995
