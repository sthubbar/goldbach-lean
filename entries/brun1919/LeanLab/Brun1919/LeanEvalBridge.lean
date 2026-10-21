module

public import LeanLab.Brun1919.Final

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Bridge: the lean-eval leaderboard statement of Brun's theorem, definitions copied verbatim from
github.com/leanprover/lean-eval LeanEval/NumberTheory/BrunConstant.lean, follows from
LeanLab.Brun1919.brun. Nothing has been submitted anywhere.
-/

@[expose] public section

namespace LeanLab.Brun1919.LeanEvalBridge
def IsTwinPrimeStart (p : ℕ) : Prop :=
  p.Prime ∧ (p + 2).Prime
noncomputable def twinPrimeReciprocalTerm (p : ℕ) : ℝ :=
  by
    classical
    exact if IsTwinPrimeStart p then (1 / (p : ℝ)) + (1 / ((p + 2 : ℕ) : ℝ)) else 0
theorem brun_constant_converges :
    Summable twinPrimeReciprocalTerm := by
  have h := LeanLab.Brun1919.brun
  unfold LeanLab.Brun1919.BrunTheorem at h
  convert h using 2 with p
  unfold twinPrimeReciprocalTerm LeanLab.Brun1919.IsTwin IsTwinPrimeStart
  push_cast; split_ifs <;> rfl
end LeanLab.Brun1919.LeanEvalBridge
