module

public import Mathlib
public import LeanLab.ChirreHagen2025.U1263Core

/-!
P0075 line, T2, unit U-6743, CLOUD 20261020T2217Z-cloud52, 2026-10-20.
One new pointwise majorant for the U-1263 diagonal: near an odd multiple of `π`,
`1 - cos t = 1 + cos (t - (2k+1)π) ≤ 2 - q²/2 + q⁴/24` with `q = t - (2k+1)π`, from the
degree-4 Taylor bound `cos_le_four` of U1263Core.lean. It replaces the flat bound
`1 - cos t ≤ 2` of `hu_two` on the pieces where the phase is away from `2πk`.
No hypotheses beyond the real-number facts stated. AI-written Lean code, Claude.
Checked only by the Lean kernel. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025.U6743
open Real

/-- The shifted majorant near `(2k+1)π`. -/
lemma hu_pi (A B : ℝ) (k : ℕ) (qlo qhi : ℝ) (hqlo : 0 ≤ qlo)
    (hcase : (0 ≤ A * (1 - 1 / 10 ^ 13) - (2 * k + 1) * 3.141593 ∧
        qlo ≤ A * (1 - 1 / 10 ^ 13) - (2 * k + 1) * 3.141593 ∧
        B - (2 * k + 1) * 3.141592 ≤ qhi) ∨
      (B - (2 * k + 1) * 3.141592 ≤ 0 ∧ qlo ≤ -(B - (2 * k + 1) * 3.141592) ∧
        -(A * (1 - 1 / 10 ^ 13) - (2 * k + 1) * 3.141593) ≤ qhi) ∨
      (qlo = 0 ∧ -qhi ≤ A * (1 - 1 / 10 ^ 13) - (2 * k + 1) * 3.141593 ∧
        B - (2 * k + 1) * 3.141592 ≤ qhi)) :
    ∀ t, A * (1 - 1 / 10 ^ 13) < t → t ≤ B →
      1 - Real.cos t ≤ 2 - qlo ^ 2 / 2 + qhi ^ 4 / 24 := by
  intro t ht1 ht2
  set φ := t - k * (2 * π) - π with hφ
  have hcos : Real.cos t = - Real.cos φ := by
    have e : t = (φ + π) + k * (2 * π) := by rw [hφ]; ring
    rw [e, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hp1 : A * (1 - 1 / 10 ^ 13) - (2 * k + 1) * 3.141593 < φ := by
    have := Real.pi_lt_d6
    have : k * (2 * π) + π ≤ (2 * k + 1) * 3.141593 := by nlinarith
    linarith
  have hp2 : φ ≤ B - (2 * k + 1) * 3.141592 := by
    have := Real.pi_gt_d6
    have : (2 * k + 1) * 3.141592 ≤ k * (2 * π) + π := by nlinarith
    linarith
  have hab : qlo ≤ |φ| ∧ |φ| ≤ qhi := by
    rcases hcase with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · rw [abs_of_nonneg (by linarith)]; constructor <;> linarith
    · rw [abs_of_nonpos (by linarith)]; constructor <;> linarith
    · constructor
      · rw [h0]; exact abs_nonneg _
      · rw [abs_le]; constructor <;> linarith
  obtain ⟨hl, hh⟩ := hab
  have e2 : φ ^ 2 = |φ| ^ 2 := (sq_abs φ).symm
  have e4 : φ ^ 4 = |φ| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
  have a2 : qlo ^ 2 ≤ |φ| ^ 2 := pow_le_pow_left₀ hqlo hl 2
  have a4 : |φ| ^ 4 ≤ qhi ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hh 4
  have := U1263.cos_le_four φ
  rw [hcos]
  linarith

end LeanLab.ChirreHagen2025.U6743
