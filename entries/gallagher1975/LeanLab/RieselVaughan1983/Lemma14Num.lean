module

public import Mathlib

/-!
P0032 Riesel-Vaughan 1983, the numerical step in the proof of Lemma 14, page 67:
`(y/log y)(1 + 1/y)(1 - 2.9024/log y)⁻¹ ≤ y/log y + 2.92667 y/(log y)²` for `log y ≥ 350`.
The slack is about 4·10⁻⁷ in the constant at `log y = 350`.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.RieselVaughan1983

theorem lemma14_step (y : ℝ) (hy : 0 < y) (hL : 350 ≤ Real.log y) :
    (1 + 1 / y) / (1 - 29024 / 10000 / Real.log y) ≤ 1 + 292667 / 100000 / Real.log y := by
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  -- `y = e^L ≥ L⁵/120`
  have hy5 : L ^ 5 / 120 ≤ y := by
    have := Real.pow_div_factorial_le_exp L hL0.le 5
    have hf : ((5 : ℕ).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
    rw [hf, Real.exp_log hy] at this
    exact this
  have hε : 1 / y ≤ 120 / L ^ 5 := by
    rw [div_le_div_iff₀ hy (by positivity)]; linarith
  have hden : 0 < 1 - 29024 / 10000 / L := by
    have : 29024 / 10000 / L < 1 := by rw [div_lt_one hL0]; linarith
    linarith
  rw [div_le_iff₀ hden]
  have e : (1 + 292667 / 100000 / L) * (1 - 29024 / 10000 / L) =
      1 + ((292667 / 100000 - 29024 / 10000) * L - 292667 / 100000 * (29024 / 10000)) / L ^ 2 := by
    field_simp; ring
  rw [e]
  set c := (292667 / 100000 - 29024 / 10000) * L - 292667 / 100000 * (29024 / 10000) with hc
  have hc0 : 1 / 10000 ≤ c := by rw [hc]; nlinarith
  have hL3 : (350 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  have hb : 120 / L ^ 5 ≤ c / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 120 * L ^ 2 ≤ c * L ^ 3 * L ^ 2 := by
      have h1 : (120 : ℝ) ≤ c * L ^ 3 := by nlinarith
      nlinarith [sq_nonneg L]
    nlinarith
  linarith

end LeanLab.RieselVaughan1983
