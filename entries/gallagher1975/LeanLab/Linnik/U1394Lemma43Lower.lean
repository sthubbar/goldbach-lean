module

public import LeanLab.Linnik.LiLiuDisplay37PNT
public import LeanLab.Linnik.U1394Fejer

/-!
Li-Liu, arXiv 2610.15784 v1, Section 4, Lemma 4.3, the lower half of display (36) at the
paper's constant 1: the proof's last line "liminf R_1(0)/(N log P) ≥ 1 - 2/(π²T) for T ≥ 1;
letting T → ∞ proves (36)".

Combines `LiLiuDisplay37PNT.lemma43_lower`, unit U-1389, R₁(0) ≥ (I(T) - ε) N log(Q + 1),
with `U1394Fejer.one_sub_I_le`, 1 - I(T) ≤ 2/(π²T), unit U-1394:
* `lemma43_lower_one`: for every ε > 0 there is T ≥ 1 with, eventually in N,
  R₁(0) ≥ (1 - ε) N log(Q + 1) for every Q, P meeting the arc conditions.

Unit U-1394, PC run 20261021T1003Z-20044. AI-written Lean code, Claude. KNOWN mathematics,
the paper's own step. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1394Lemma43Lower

open Real Filter
open LeanLab.Linnik.LiLiuDisplay37 LeanLab.Linnik.U1394Fejer

/-- **Lemma 4.3, lower half of (36), at the paper's constant 1.** For every `ε > 0` there is
`T ≥ 1` such that eventually in `N`, for every `Q ≤ N₁ = ⌊N^{1-κ}⌋` with `Q ≤ P`, `QT ≤ P`,
`2P² < TN`, `R₁(0) ≥ (1 - ε) N log(Q + 1)`. -/
theorem lemma43_lower_one {κ : ℝ} (hκ : 0 < κ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ᶠ N : ℕ in atTop, ∀ (Q : ℕ) (P : ℝ), 1 ≤ Q →
      Q ≤ ⌊(N : ℝ) ^ (1 - κ)⌋₊ → (Q : ℝ) ≤ P → (Q : ℝ) * T ≤ P → 2 * P ^ 2 < T * N →
      (1 - ε) * N * Real.log ((Q : ℝ) + 1) ≤
        LeanLab.Linnik.LiLiuLemma43Int.R10 (primesIn ⌊(N : ℝ) ^ (1 - κ)⌋₊ N) logw P N := by
  set T : ℝ := max 1 (4 / (π ^ 2 * ε)) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 < T := by linarith
  have hIT : 1 - ε / 2 ≤ I T := by
    have h := (one_sub_I_le hT0).2
    have h2 : 2 / (π ^ 2 * T) ≤ ε / 2 := by
      have hT4 : 4 / (π ^ 2 * ε) ≤ T := le_max_right _ _
      have hp : 0 < π ^ 2 := by positivity
      rw [div_le_iff₀ (by positivity)] at hT4
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  refine ⟨T, hT1, ?_⟩
  filter_upwards [LeanLab.Linnik.LiLiuDisplay37PNT.lemma43_lower hκ hT1 (half_pos hε)]
    with N hN Q P hQ hQM hQP hQT hP
  refine le_trans ?_ (hN Q P hQ hQM hQP hQT hP)
  have hNL : 0 ≤ (N : ℝ) * Real.log ((Q : ℝ) + 1) := by
    have : (0 : ℝ) ≤ Real.log ((Q : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) Q])
    positivity
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right (by linarith) hNL

/-- Vacuity: κ = 1/2, ε = 1/10 meet the hypotheses. -/
theorem vacuity : ∃ T : ℝ, 1 ≤ T ∧ ∀ᶠ N : ℕ in atTop, ∀ (Q : ℕ) (P : ℝ), 1 ≤ Q →
      Q ≤ ⌊(N : ℝ) ^ (1 - 1 / 2 : ℝ)⌋₊ → (Q : ℝ) ≤ P → (Q : ℝ) * T ≤ P → 2 * P ^ 2 < T * N →
      (1 - 1 / 10) * N * Real.log ((Q : ℝ) + 1) ≤
        LeanLab.Linnik.LiLiuLemma43Int.R10 (primesIn ⌊(N : ℝ) ^ (1 - 1 / 2 : ℝ)⌋₊ N) logw P N :=
  lemma43_lower_one (by norm_num) (by norm_num)

end LeanLab.Linnik.U1394Lemma43Lower
