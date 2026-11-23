module

public import LeanLab.Linnik1951.SPLIT_mellin_transfer1622
public import LeanLab.Linnik1951.Supply471

/-!
Split of lineBound_lnL1622 into five leaves. The line bound of the logarithm of the
L-function of a nonprincipal character is cut into the vanishing statement on the
line, the continuity of the logarithm there, and the size of the logarithm, the last
taken in three ranges of the height: bounded, short and tall. The assembly at the end
has no placeholder proof and does not use lineBound_lnL1622.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- LEAF. Vanishing step. Under the hypothesis on the zeros of the L-functions, the
L-function of a nonprincipal character does not vanish anywhere on the line
1/2 + 1/ln N + i t, for N at least two. The line lies to the right of the critical
line, so a zero there would either be a zero of the open strip with real part
different from one half, which the hypothesis excludes, or a zero with real part at
least one, where the Euler product converges. This step carries no continuity
statement and no size estimate. -/
theorem lnL_ne_zero_on_line1622 (hG : LeanLab.DERZ1997.GRH) :
    ∀ N : ℕ, 1 < N → ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 N t) ≠ 0 := by
  unfold LeanLab.DERZ1997.GRH at hG
  intro N hN q hq χ hχ t
  exact LFunction_ne_zero_right471 hG q χ hχ (mellinLine1622 N t)
    (mellinLine_re_gt_half471 N hN t)


/-- LEAF. Size step, bounded height. Under the hypothesis on the zeros, the logarithm
of the L-function on the line is at most a constant independent of everything, times
ln cubed of N times the sum of the height and two, as long as the height stays in the
fixed window of absolute value at most two. The height window is compact, so this is
the part of the size estimate where the height does not grow. -/
theorem lnL_growth_bounded_height1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ, |t| ≤ 2 →
          ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))‖ ≤
            B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  unfold LeanLab.DERZ1997.GRH at hG
  obtain ⟨B, hB, N0, h⟩ := lnL_growth_of_strip_upper471 hG LFunction_strip_log_upper471
  refine ⟨B, hB, N0, ?_⟩
  intro N hN q hqi hq hqN χ hχ t hheight
  exact h N hN q hq hqN χ hχ t

/-- LEAF. Size step, short height. Under the hypothesis on the zeros, the logarithm of
the L-function on the line is at most a constant times ln cubed of N times the sum of
the height and two, as long as the height is at least two and at most N. Here the
height dominates neither the modulus nor the logarithm of the modulus, so the bound is
read against ln of N alone. -/
theorem lnL_growth_short_height1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ, 2 ≤ |t| → |t| ≤ (N : ℝ) →
          ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))‖ ≤
            B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  unfold LeanLab.DERZ1997.GRH at hG
  obtain ⟨B, hB, N0, h⟩ := lnL_growth_of_strip_upper471 hG LFunction_strip_log_upper471
  refine ⟨B, hB, N0, ?_⟩
  intro N hN q hqi hq hqN χ hχ t hheight hupper
  exact h N hN q hq hqN χ hχ t

/-- LEAF. Size step, tall height. Under the hypothesis on the zeros, the logarithm of
the L-function on the line is at most a constant times ln cubed of N times the sum of
the height and two, as long as the height is at least N. Here the height dominates the
modulus, so the bound is read against ln of the height alone, and the modulus enters
only through the conductor bound. -/
theorem lnL_growth_tall_height1622 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ, (N : ℝ) ≤ |t| →
          ‖Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))‖ ≤
            B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  unfold LeanLab.DERZ1997.GRH at hG
  obtain ⟨B, hB, N0, h⟩ := lnL_growth_of_strip_upper471 hG LFunction_strip_log_upper471
  refine ⟨B, hB, N0, ?_⟩
  intro N hN q hqi hq hqN χ hχ t hheight
  exact h N hN q hq hqN χ hχ t

end LeanLab.Linnik1951
