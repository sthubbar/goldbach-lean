module

public import Mathlib

/-!
# From multiplicative to additive windows: the pointwise identity

Lab proof, unit U-5928, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. Elementary, no cited input; the first step of Saffari-Vaughan's passage from windows
`(x, xe^δ]` to windows `(x, x + h]`.

`Wm y δ = ψ(ye^δ) - ψ(y) - y(e^δ - 1)`, the error of the multiplicative window.

* `additive_eq`: for `x > 0`, `h ≥ 0` and any `δ`, with `δ' = δ - log(1 + h/x)`,
  `ψ(x + h) - ψ(x) - h = Wm x δ - Wm (x + h) δ'`, exactly, since `(x + h)e^{δ'} = xe^δ`;
* `additive_sq_le`: hence `(ψ(x + h) - ψ(x) - h)² ≤ 2 Wm(x, δ)² + 2 Wm(x + h, δ')²`.

Averaging the second over `δ ∈ [Δ, 2Δ]` with `log(1 + h/x) ≤ Δ/2` puts `δ'` in `[Δ/2, 2Δ]`; with
`selberg_sharp` at each `δ` and Fubini this gives the additive form. That integration is not
done here.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

/-- The error of the multiplicative window `(y, ye^δ]`. -/
noncomputable def Wm (y δ : ℝ) : ℝ :=
  Chebyshev.psi (y * Real.exp δ) - Chebyshev.psi y - y * (Real.exp δ - 1)

/-- **The pointwise identity.** -/
theorem additive_eq {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (δ : ℝ) :
    Chebyshev.psi (x + h) - Chebyshev.psi x - h =
      Wm x δ - Wm (x + h) (δ - Real.log (1 + h / x)) := by
  have h1 : 0 < 1 + h / x := by positivity
  have key : (x + h) * Real.exp (δ - Real.log (1 + h / x)) = x * Real.exp δ := by
    rw [Real.exp_sub, Real.exp_log h1]
    field_simp
  unfold Wm
  rw [key]
  have : (x + h) * (Real.exp (δ - Real.log (1 + h / x)) - 1) = x * Real.exp δ - (x + h) := by
    rw [mul_sub, key, mul_one]
  rw [this]
  ring

/-- **The squared inequality.** -/
theorem additive_sq_le {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (δ : ℝ) :
    (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2 ≤
      2 * Wm x δ ^ 2 + 2 * Wm (x + h) (δ - Real.log (1 + h / x)) ^ 2 := by
  rw [additive_eq hx hh δ]
  nlinarith [sq_nonneg (Wm x δ + Wm (x + h) (δ - Real.log (1 + h / x)))]

/-- The shift is small: `0 ≤ log(1 + h/x) ≤ h/x`. -/
lemma log_shift_le {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    0 ≤ Real.log (1 + h / x) ∧ Real.log (1 + h / x) ≤ h / x := by
  have h0 : 0 ≤ h / x := div_nonneg hh hx.le
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + h / x by linarith)
  linarith

/-- `Wm` at the exponential point is the numerator of the lab's `Nw`:
`Wm (e^u) δ = ψ(e^{u+δ}) - ψ(e^u) - (e^{u+δ} - e^u)`. -/
lemma Wm_exp (u δ : ℝ) : Wm (Real.exp u) δ = Chebyshev.psi (Real.exp (u + δ)) -
    Chebyshev.psi (Real.exp u) - (Real.exp (u + δ) - Real.exp u) := by
  unfold Wm; rw [Real.exp_add]; ring

end LeanLab.PNTPort.Selberg

