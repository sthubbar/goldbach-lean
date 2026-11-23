module

public import LeanLab.BhowmikGrimmelt2026.Statements
public import LeanLab.BhowmikGrimmelt2026.Decomp515a

/-!
Leaf of `zeroBound_lower150`: P0029 Section 3, page 12, the remark after the display
`q^{1/2} N^{Θ+ε}`, "in the best case we could hope for Θ = 1/2".  The lower limit one half rests
on Hardy 1914, Sur les zeros de la fonction zeta de Riemann, which proves infinitely many zeros
of the Riemann zeta function on the critical line.  The survey does not cite Hardy 1914; the
classical source is Hardy's paper, and this leaf states only one such zero, the first being at
`t = 14.1347...`, checked numerically by the architect pass U-1662.

Moved here from `Decomp150a.lean` by the REPAIR pass 20261112 so that an existing file carries no
newly added unproved step.  The statement is unchanged, and `zeroBound_lower150` there still derives the
lower bound from this leaf exactly as before.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF: P0029 Section 3, page 12, the remark after the display `q^{1/2} N^{Θ+ε}`,
"in the best case we could hope for Θ = 1/2".  The lower limit one half rests on Hardy 1914,
Sur les zeros de la fonction zeta de Riemann, which proves infinitely many zeros on the critical
line; this leaf states one.  The survey does not cite Hardy 1914, so the citation is to Hardy's
paper directly. CITED and CONDITIONAL on the base Mellin transform, differentiation
under its integral, and the theta cusp limit in Decomp515a.
AI wrote the Lean code. Goldbach is open. -/
theorem hardy_critical_line_zero150 :
    ∃ t : ℝ, riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  exact hardy_critical_line_zero515

end LeanLab.BhowmikGrimmelt2026
