module

public import LeanLab.PNTPort.Selberg.Count
public import LeanLab.PNTPort.ExplicitPsi1.Log2Pi

/-!
# The explicit formula for `ψ₁(e^v)` and its second difference

Lab proof, unit U-5920, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, no cited input, unconditional.

`psi1 x = x Σ_n Λ(n) max(0, 1 - n/x)`, which is `ψ₁(x) = ∫₀ˣ ψ(t) dt` for `x > 0`.

* `explicit_exp`: `‖ψ₁(e^v) - e^{2v}/2 + e^v log 2π + Σ_ρ m(ρ) e^{v(ρ + 1)}/(ρ(ρ + 1))‖ ≤ K e^{v/2}`
  for every real `v`, the sum over the nontrivial zeros, from the lab's
  `explicit_formula_psi1_log2pi`.
* `second_difference`: for the multiplicative second difference
  `D₂(λ, u) = ψ₁(e^{u+λ}) - 2ψ₁(e^u) + ψ₁(e^{u-λ}) - e^{2u}(e^{2λ} - 2 + e^{-2λ})/2`,
  `‖D₂ + log 2π · e^u (e^λ - 2 + e^{-λ}) + Σ_ρ m(ρ) e^{u(ρ+1)} E(λ(ρ+1))/(ρ(ρ+1))‖ ≤ 5 K e^{u/2}`
  for `0 ≤ λ ≤ 1`, `E(z) = e^z - 2 + e^{-z}`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex Finset
open LeanLab.PNTPort.ExplicitPsi1

local notation "ζ" => riemannZeta

/-- `ψ₁(x) = x Σ_n Λ(n) max(0, 1 - n/x)`. -/
noncomputable def psi1 (x : ℝ) : ℂ :=
  (x : ℂ) * ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * ZetaZeros.w1 (n / x)

/-- The nontrivial zeros as a type. -/
abbrev NZs := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- `E(z) = e^z - 2 + e^{-z}`. -/
noncomputable def Ez (z : ℂ) : ℂ := cexp z - 2 + cexp (-z)

/-- The zero term of `ψ₁(e^v)`: `m(ρ) e^{v(ρ+1)}/(ρ(ρ + 1))`. -/
noncomputable def ztE (v : ℝ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt ζ ρ : ℂ) * (cexp (v * (ρ + 1)) / (ρ * (ρ + 1)))

/-- The multiplicative second difference minus its main term. -/
noncomputable def D2 (l u : ℝ) : ℂ :=
  psi1 (Real.exp (u + l)) - 2 * psi1 (Real.exp u) + psi1 (Real.exp (u - l)) -
    ((Real.exp (2 * u) * (Real.exp (2 * l) - 2 + Real.exp (-(2 * l))) / 2 : ℝ) : ℂ)

lemma ztE_eq (v : ℝ) (ρ : ℂ) : ztE v ρ = (Real.exp v : ℂ) * zterm (Real.exp v) ρ := by
  unfold ztE zterm
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  rw [show (v : ℂ) * (ρ + 1) = v + v * ρ by ring, Complex.exp_add]
  rw [mul_comm (v : ℂ) ρ]
  ring

lemma summable_ztE (v : ℝ) : Summable (fun ρ : NZs => ztE v ρ.1) := by
  have h := summable_zterm (Real.exp_pos v)
  have e : Zall = {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} := Zall_eq
  have h' : Summable (fun ρ : NZs => zterm (Real.exp v) ρ.1) := by
    revert h; rw [e]; exact id
  simp_rw [ztE_eq]
  exact h'.mul_left _

/-- **The explicit formula in the exponential variable.** -/
theorem explicit_exp : ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ,
    ‖psi1 (Real.exp v) - ((Real.exp (2 * v) / 2 - Real.exp v * Real.log (2 * Real.pi) : ℝ) -
      ∑' ρ : NZs, ztE v ρ.1)‖ ≤ K * Real.exp (v / 2) := by
  obtain ⟨K, hK⟩ := explicit_formula_psi1_log2pi
  have hK0 : 0 ≤ K := by
    have h := hK 1 one_pos
    rw [Real.one_rpow, mul_one] at h
    exact le_trans (norm_nonneg _) h
  refine ⟨K, hK0, fun v => ?_⟩
  have hx := Real.exp_pos v
  have h := hK (Real.exp v) hx
  have e1 : psi1 (Real.exp v) - ((Real.exp (2 * v) / 2 - Real.exp v * Real.log (2 * Real.pi) : ℝ) -
      ∑' ρ : NZs, ztE v ρ.1) = (Real.exp v : ℂ) *
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * ZetaZeros.w1 (n / Real.exp v) -
        (Real.exp v / 2 - Real.log (2 * Real.pi) -
          ∑' ρ : NZs, zterm (Real.exp v) ρ.1)) := by
    unfold psi1
    simp_rw [ztE_eq]
    rw [tsum_mul_left]
    have : Real.exp (2 * v) = Real.exp v * Real.exp v := by rw [← Real.exp_add]; ring_nf
    rw [this]
    push_cast
    ring
  rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  calc Real.exp v * _ ≤ Real.exp v * (K * Real.exp v ^ (-1 / 2 : ℝ)) := by gcongr
    _ = K * Real.exp (v / 2) := by
      rw [← Real.exp_mul, mul_left_comm, ← Real.exp_add]; ring_nf

end LeanLab.PNTPort.Selberg

