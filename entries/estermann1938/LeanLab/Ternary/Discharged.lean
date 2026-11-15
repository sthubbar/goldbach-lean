module

public import LeanLab.PNTPort.PsiChi.CitedDischarged

/-!
Audit U-1058, PC run 20261019T1204Z-858. The cited `vinogradov` and `hardyLittlewood` of
Statements.lean are now `_stmt` Props there and PROVED here from the lab's unconditional
Siegel-Walfisz chain, `PNTPort/PsiChi/CitedDischarged.lean`. `hardyLittlewood` holds with GRH
unused; this is NOT a formalization of Hardy and Littlewood's argument. The constant `C` is
ineffective. Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.Ternary

/-- P0003 Vinogradov 1937: every sufficiently large odd number is a sum of three primes. -/
theorem vinogradov : vinogradov_stmt := LeanLab.PNTPort.PsiChi.ternary_vinogradov

/-- P0004 Hardy-Littlewood 1923, the lab's GRH form; GRH is not used. -/
theorem hardyLittlewood : hardyLittlewood_stmt := LeanLab.PNTPort.PsiChi.ternary_hardyLittlewood

example : vinogradov_stmt = ∃ C : ℝ, TernaryAbove C := rfl

end LeanLab.Ternary

