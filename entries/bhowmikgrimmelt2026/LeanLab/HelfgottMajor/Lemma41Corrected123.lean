module

public import LeanLab.HelfgottMajor.Lemma41Leaf123
public import LeanLab.HelfgottMajor.SplitGaussian123
public import LeanLab.HelfgottMajor.MiddleSlack123

/-!
Route burst 2026-11-15, step gaussian_explicit_estimate p6, built on p5.
P0014 Helfgott, Major arcs for Goldbach's problem, Proposition 4.6, pages 43 and 44, display
4.43, proved from the CORRECTED Lemma 4.1 of Lemma41Leaf123 in place of the printed one, which
is SUSPECTED FALSE for even primitive characters with q above 1.

The corrected residue carries log x. It is paid by two units of proved slack in the bound for
the zeros up to T, MiddleSlack123.middle_mass_bound_slack, since log x is at most 2 sqrt x for
x at least 1. The conclusion is display 4.43 exactly as Decomp123.gaussian_explicit_estimate
states it, with the recorded factor 6 repair. No definition is made in this file.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.Lemma41Corrected123
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- PROVED. P0014 pages 43 and 44, the triangle inequality and arithmetic that combine
Lemmas 4.1, 4.4 and 4.5 into display 4.43, with the CORRECTED inputs: the residue budget has
the log x of the corrected Lemma 4.1, and the low zero bound has two units of slack on sqrt x.
The two cancel because log x is at most 2 sqrt x for x at least 1. The conclusion is display
4.43 as in SplitGaussian123.assembly_of_components. -/
theorem assembly_of_components_corrected (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hformula : ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 + log x ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x)
    (hL : ‖lowZeros χ δ x T‖ ≤
      (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T +
        2.85 * log q + 74.38 - 2) * sqrt x)
    (hH : ‖highZeros χ δ x T‖ ≤
      log (q * T / (2 * π)) *
        (4.329 * exp (-0.1598 * T) +
          0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x := by
  obtain ⟨R, hR, hE⟩ := hformula
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < sqrt x := sqrt_pos.mpr hx0
  have hbudget := contour_residue_budget (q : ℝ) |δ| x hx (abs_nonneg δ)
  have hlogx : log x ≤ 2 * sqrt x := by
    have h := log_le_sub_one_of_pos hs0
    rw [log_sqrt hx0.le] at h
    linarith
  have htri : ‖Schi etaHeart χ δ x -
      (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ +
        ‖lowZeros χ δ x T‖ + ‖highZeros χ δ x T‖ + ‖R‖ := by
    calc
      _ = ‖(Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
          lowZeros χ δ x T + highZeros χ δ x T + R) -
          lowZeros χ δ x T - highZeros χ δ x T - R‖ := by congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans (by
        gcongr
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _))
  have heq :
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x =
      log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) *
          sqrt x + (3 * log q + 14 * |δ| + 17) +
        (log q + 6) * (1 + 6 * |δ|) / sqrt x := by
    generalize hroot : sqrt x = s
    have hxx : x = s ^ 2 := by rw [← hroot, sq_sqrt hx0.le]
    have hsne : s ≠ 0 := by rw [← hroot]; exact hs0.ne'
    rw [hxx]
    field_simp [hsne]
  rw [heq]
  linarith

end LeanLab.HelfgottMajor.Lemma41Corrected123
