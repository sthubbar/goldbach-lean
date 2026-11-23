module

public import Mathlib
public import LeanLab.DERZ1997.Statements

/-!
Finite GRH verification.
P0065 Platt 2013, arXiv 1305.3087, abstract: GRH verified for all L-functions of primitive
  characters of modulus q ≤ 400 000, for even q to height t0 = max(10^8/q, 7.5·10^7/q + 200),
  for odd q to height t0 = max(10^8/q, 3.75·10^7/q + 200).
  Height is read as |Im s| ≤ t0; QUESTION for VERIFY whether the paper checks both signs.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.GRHComputations
open LeanLab.DERZ1997

/-- Platt's checking height for modulus `q`. -/
noncomputable def t0 (q : ℕ) : ℝ :=
  if Even q then max (10 ^ 8 / q) (7.5e7 / q + 200) else max (10 ^ 8 / q) (3.75e7 / q + 200)

/-- GRH for primitive characters of modulus at most `Q`, for zeros of height at most `T q`. -/
def GRHCheck (Q : ℕ) (T : ℕ → ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], q ≤ Q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T q → s.re = 1 / 2

/-- GRH implies every finite check. -/
theorem grhCheck_of_GRH (hG : GRH) (Q : ℕ) (T : ℕ → ℝ) : GRHCheck Q T :=
  fun q _ _ χ _ s hs h0 h1 _ => hG q χ s hs h0 h1

/-- Smaller ranges follow from larger ones. -/
theorem grhCheck_mono {Q Q' : ℕ} {T T' : ℕ → ℝ} (hQ : Q ≤ Q') (hT : ∀ q, T q ≤ T' q)
    (h : GRHCheck Q' T') : GRHCheck Q T :=
  fun q _ hq χ hχ s hs h0 h1 hh => h q (hq.trans hQ) χ hχ s hs h0 h1 (hh.trans (hT q))

/-- Platt's height is at least 200 for every modulus. -/
theorem t0_ge (q : ℕ) : (200 : ℝ) ≤ t0 q := by
  unfold t0
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  split_ifs
  · exact (le_add_of_nonneg_left (by positivity)).trans (le_max_right _ _)
  · exact (le_add_of_nonneg_left (by positivity)).trans (le_max_right _ _)

/-- So Platt's check contains GRH to height 200 for every primitive modulus up to 400 000. -/
theorem platt_height200 (h : GRHCheck 400000 t0) : GRHCheck 400000 (fun _ => 200) :=
  grhCheck_mono le_rfl t0_ge h

end LeanLab.GRHComputations
