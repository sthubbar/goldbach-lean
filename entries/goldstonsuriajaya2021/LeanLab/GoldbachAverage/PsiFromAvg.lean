module

public import Mathlib
public import LeanLab.GoldbachAverage.Sums

/-!
Chebyshev's ψ squeezed by the average Goldbach asymptotic AvgRH, P0098 Granville 2007 as
quoted by P0060 and arXiv 2405.04315. From ψ(N)² ≤ Σ_{n ≤ 2N} G(n) and Σ_{n ≤ N} G(n) ≤ ψ(N)²,
AvgRH gives N²/2 − K N^{3/2+ε} ≤ ψ(N)² ≤ 2N² + K (2N)^{3/2+ε}. Under RH, by granville_equiv,
now proved in Converse.lean. Elementary; a sanity check of the statement, ψ(N) ~ N lies inside.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN; AvgRH is an average over n.
-/

@[expose] public section

open Finset

noncomputable section
namespace LeanLab.GoldbachAverage

theorem psi_sq_bounds_of_avgRH (H : AvgRH) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) ^ 2 / 2 - K * (N : ℝ) ^ (3 / 2 + ε) ≤ psiN N ^ 2 ∧
      psiN N ^ 2 ≤ 2 * (N : ℝ) ^ 2 + K * ((2 * N : ℕ) : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨K, hK⟩ := H ε hε
  refine ⟨K, fun N hN => ⟨?_, ?_⟩⟩
  · have h1 := hK N hN
    have h2 := sum_G_le N
    rw [abs_le] at h1
    linarith [h1.1]
  · have h1 := hK (2 * N) (by omega)
    have h2 := sum_G_ge N
    rw [abs_le] at h1
    have e : ((2 * N : ℕ) : ℝ) ^ 2 / 2 = 2 * (N : ℝ) ^ 2 := by push_cast; ring
    linarith [h1.2]

/-- So RH, through the Granville equivalence, gives the same squeeze. The equivalence is a named
hypothesis here because this file sits below Converse.lean, which proves it as
`Converse.granville_equiv_proved`; FromVonKoch.psi_sq_bounds_of_RH' needs RH only. -/
theorem psi_sq_bounds_of_RH (hG : GranvilleEquiv) (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) ^ 2 / 2 - K * (N : ℝ) ^ (3 / 2 + ε) ≤ psiN N ^ 2 ∧
      psiN N ^ 2 ≤ 2 * (N : ℝ) ^ 2 + K * ((2 * N : ℕ) : ℝ) ^ (3 / 2 + ε) :=
  psi_sq_bounds_of_avgRH (hG.mp hRH) hε

end LeanLab.GoldbachAverage

