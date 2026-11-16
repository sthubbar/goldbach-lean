module

public import Mathlib

/-!
P0022, L. Kaniecki, On Šnirelman's constant under the Riemann hypothesis,
Acta Arith. 72, 1995, 361-374. The gap function `λ` of page 371 and the Young and Potler gap
input that the paper cites as reference 16.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.

This file is an extract of the lab file `LeanLab/Kaniecki1995/Statements.lean`: only
`nextPrime`, `lam` and `YoungPotler` are kept. `YoungPotler` is a cited computation, stated as
a `Prop` and never proved here; theorems that use it take it as a hypothesis.
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

/-- [16] Young-Potler 1989, as used on p. 371: the maximal gap between primes up to
`7.263 · 10^13` is at most 778. -/
def YoungPotler : Prop := (lam 72630000000000 : ℝ) ≤ 778

end LeanLab.Kaniecki1995
