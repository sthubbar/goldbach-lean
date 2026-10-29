module

public import LeanLab.Verifications.U1437Fast.Sieve
public import LeanLab.Verifications.U1497Split.Core

/-!
U-1497, run 20261022T2003Z-18, I-5067, Dudek 2017. Bridge from the core only checker copies of
`U1497Split/Core.lean` to the Mathlib definitions of `U1437Fast/Sieve.lean`, so a window proved by
`decide +kernel` in a module without Mathlib extends `SqfUpTo` exactly as a U1437Fast window does.
AI-written Lean code, Claude. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Verifications.U1497Split

open LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits LeanLab.Verifications.U1437Fast

theorem rep_eq (d : ℕ) : ∀ j, Core.rep d j = Bits.rep d j
  | 0 => rfl
  | j + 1 => by simp only [Core.rep, Bits.rep, Core.dup, Bits.dup, rep_eq d j]

theorem gm_eq (P : ℕ) : ∀ Q, Core.gm P Q = Bits.gm P Q
  | [] => rfl
  | q :: t => by simp only [Core.gm, Bits.gm, gm_eq P t]

theorem nsq_eq (lo W : ℕ) : ∀ L, Core.nsq lo W L = U1437Fast.nsq lo W L
  | [] => rfl
  | r :: t => by
    simp only [Core.nsq, U1437Fast.nsq, nsq_eq lo W t, rep_eq, Core.jOf, Bits.jOf,
      Core.firstMul, Bits.firstMul] <;> rfl

theorem P32c_eq : Core.P32c = P32 := by decide +kernel

theorem SR_eq (L : ℕ) : Core.SR L = U1437Fast.SR L := by
  simp only [Core.SR, U1437Fast.SR, P32c_eq]

theorem sfm_eq (lo W : ℕ) : Core.sfm lo W = U1437Fast.sfm lo W := by
  simp only [Core.sfm, U1437Fast.sfm, SR_eq, nsq_eq]

theorem tm_eq (lo A B : ℕ) : Core.tm lo A B = U1437Fast.tm lo A B := rfl

theorem Q16_eq : Core.Q16 = P10k.take 16 := by decide +kernel

/-- One core only window check is a U1437Fast window check. -/
theorem wcheck_of_core {lo W A B : ℕ}
    (h : Core.tm lo A B &&& Core.gm (Core.sfm lo W) Core.Q16 = Core.tm lo A B) :
    tm lo A B &&& gm (sfm lo W) (P10k.take 16) = tm lo A B := by
  rw [tm_eq, sfm_eq, gm_eq, Q16_eq] at h
  exact h

/-- `sqf_extend` with the window check in core only form. -/
theorem sqf_extend_core {lo W a A B : ℕ} (ha : SqfUpTo a) (hA : a + 1 = A)
    (h1 : 1 ≤ lo) (hW : lo + W ≤ BB) (hlo : lo ≤ A)
    (h : Core.tm lo A B &&& Core.gm (Core.sfm lo W) Core.Q16 = Core.tm lo A B) : SqfUpTo B :=
  sqf_extend ha hA h1 hW hlo q16_prime (wcheck_of_core h)

end LeanLab.Verifications.U1497Split
