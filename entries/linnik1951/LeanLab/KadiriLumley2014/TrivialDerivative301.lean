module

public import LeanLab.PNTPort.ExplicitPsi1.DudekLemma4
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 4, the trivial-zero remainder in equation 2.15.
Derivative of one existing psi-one trivial-zero term.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task301

open Real
open LeanLab.PNTPort.ExplicitPsi1.Trivial

/-- Differentiating y times the integrated trivial-zero term gives the logarithm-series summand. -/
theorem hasDerivAt_y_tb (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => y * tb y n)
      (-y ^ (-2 * ((n : ℝ) + 1)) / (2 * n + 2)) y := by
  let e : ℝ := -2 * ((n : ℝ) + 1)
  have hp := Real.hasDerivAt_rpow_const (x := y) (p := e) (Or.inl hy.ne')
  have h := ((hasDerivAt_id y).mul hp).div_const ((2 * (n : ℝ) + 2) * (2 * n + 1))
  have hpow : y * y ^ (e - 1) = y ^ e := by
    calc
      y * y ^ (e - 1) = y ^ (1 : ℝ) * y ^ (e - 1) := by rw [Real.rpow_one]
      _ = y ^ (1 + (e - 1)) := (Real.rpow_add hy _ _).symm
      _ = y ^ e := by congr 1; ring
  convert h using 1
  · funext x
    dsimp [tb, e]
    ring
  · dsimp only [id_eq]
    rw [show y * (e * y ^ (e - 1)) = e * (y * y ^ (e - 1)) by ring, hpow]
    dsimp [e]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    field_simp
    ring

end LeanLab.KadiriLumley2014.Task301
