module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Signs of Taylor coefficients from a logarithmic derivative

Lab proof, unit U-5111. AI wrote this file. Known mathematics, no cited input. An input to the
Estermann-Goldfeld proof of Siegel's theorem, Davenport chapter 21: there `F = ζ L(χ₁) L(χ₂)
L(χ₁χ₂)` and `Q = -F'/F` is a Dirichlet series with nonnegative coefficients, so
`(-1)^j Q^{(j)}(2) ≥ 0`, and this lemma gives `(-1)^m F^{(m)}(2) ≥ 0`, the nonnegativity of the
Taylor coefficients of `F` at `2` in powers of `2 - s`.

`sign_of_logDeriv`: if `F` and `Q` are analytic at `x`, `F' = -F Q` near `x`, `F(x) ≥ 0` and
`(-1)^j Q^{(j)}(x) ≥ 0` for every `j`, then `(-1)^m F^{(m)}(x) ≥ 0` for every `m`, the order
being the partial order of `ℂ`, nonnegative real.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Filter Topology
open scoped ComplexOrder

theorem sign_of_logDeriv {F Q : ℂ → ℂ} {x : ℂ} (hF : AnalyticAt ℂ F x) (hQ : AnalyticAt ℂ Q x)
    (hd : deriv F =ᶠ[𝓝 x] fun z ↦ -(F z * Q z)) (h0 : 0 ≤ F x)
    (hQs : ∀ j : ℕ, 0 ≤ (-1) ^ j * iteratedDeriv j Q x) :
    ∀ m : ℕ, 0 ≤ (-1) ^ m * iteratedDeriv m F x := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · simpa using h0
    have hstep : iteratedDeriv (m + 1) F x = -iteratedDeriv m (fun z ↦ F z * Q z) x := by
      rw [iteratedDeriv_succ', (hd.iteratedDeriv m).eq_of_nhds]
      rw [show (fun z ↦ -(F z * Q z)) = -(fun z ↦ F z * Q z) by rfl, iteratedDeriv_neg]
    have hmul : iteratedDeriv m (fun z ↦ F z * Q z) x = ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) * iteratedDeriv i F x * iteratedDeriv (m - i) Q x := by
      have := iteratedDeriv_mul (n := m) (hF.contDiffAt) (hQ.contDiffAt)
      simpa [Pi.mul_def] using this
    rw [hstep, hmul]
    have : (-1 : ℂ) ^ (m + 1) * -∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) * iteratedDeriv i F x * iteratedDeriv (m - i) Q x =
        ∑ i ∈ Finset.range (m + 1), (m.choose i : ℂ) * ((-1) ^ i * iteratedDeriv i F x) *
          ((-1) ^ (m - i) * iteratedDeriv (m - i) Q x) := by
      rw [show ∀ a : ℂ, (-1 : ℂ) ^ (m + 1) * -a = (-1) ^ m * a from fun a ↦ by ring, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have : (-1 : ℂ) ^ m = (-1) ^ i * (-1) ^ (m - i) := by
        rw [← pow_add, Nat.add_sub_cancel' him]
      rw [this]; ring
    rw [this]
    refine Finset.sum_nonneg fun i hi ↦ ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    refine mul_nonneg (mul_nonneg (by exact_mod_cast Nat.zero_le _) (ih i (by omega))) (hQs _)

end LeanLab.PNTPort.DirichletZF

