module

public import Mathlib

/-!
# The weighted zero density argument and the case inequalities of Pintz's Goldbach exceptional set paper

J. Pintz, A new explicit formula in the additive theory of primes with applications II.
The exceptional set in Goldbach's problem, arXiv 1804.09084v2, 2018. Theorem 1 of the paper
is `E(X) < X^0.72` for the number of even `n ≤ X` that are not sums of two primes.

The analytic input of the proof is a set of zero density theorems for Dirichlet `L`-functions,
Theorems C to I. Two elementary steps turn them into the bounds Section 9 needs:

* Theorem J, display 4.36, bounds the weighted excess `D = ∑ (ψ_j - ψ)` over zeros by
  `(1 - ξ) / (2Δ)`. Its proof, displays 8.1 to 8.4, starts from the analytic estimate 7.20.
* Theorem K, display 4.41, solves the extremal problem of displays 4.37 to 4.39: to maximise
  `∑ (e^{B d_j} - e^{C d_j})` under the density budget and caps `d_j ≤ e_j`, every coordinate
  before the last active one is saturated, `d_j = e_j`. Its proof, displays 8.10 to 8.16,
  is an exchange argument with a concave cost and a strictly convex objective.

Section 9 then feeds these into the basic inequality 9.4 and closes eight cases.

This file states five theorems.

* `Greedy117.theoremK_ordered_integral`: Theorem K, the saturation part, display 4.41, with the paper's
  objective `∑ (e^{B d_j} - e^{C d_j})`, its cost in the integral form of display 8.11, the ordered
  domain `d_1 ≥ d_2 ≥ ⋯`, caps `0 ≤ d_j ≤ e_j` with `e` decreasing, and `T < B`, `0 ≤ C < B`.
  For any maximiser `d` whose last positive coordinate is `d_r`, `d_j = e_j` for `1 ≤ j < r`.
* `Residual117.saturation_and_residual`: the same exchange argument for an abstract concave,
  continuous cost `H` with `H 1 = 0` and a strictly convex, strictly increasing objective `G`,
  in the coordinates `y_j = e^{d_j T}`; it adds that the budget is used up exactly and that the
  last active coordinate satisfies the residual equation 4.42.
* `Density117.excess_bound_of_720`: Theorem J, the bound 4.36 with error term zero, from
  the estimate 7.20 taken as a hypothesis, under `ξ + ε ≤ Δ²`, `Δ = ψ - ξ`.
* `basic_ineq` and `case8`, the basic inequality 9.4 and Case 8 of Section 9, are proved in the
  solution files but are not part of this comparison.

The analytic estimate 7.20, the existence of a maximiser and the zero density inputs of
Theorems C to I are not proved here; Theorem 1 of the paper is not claimed.
-/

@[expose] public section

namespace LeanLab.Pintz2018

open Real

/-- Theorem K of arXiv 1804.09084, display 4.41 on page 18, the saturation part of the
optimal choice: every coordinate `d j` with `1 ≤ j < r` equals its cap `e j`. -/
def TheoremK_OptimalChoice (r : ℕ) (d_opt e : ℕ → ℝ) : Prop :=
  ∀ j, 1 ≤ j → j < r → d_opt j = e j

end LeanLab.Pintz2018

namespace LeanLab.Pintz2018.Greedy117
open MeasureTheory

/-- Theorem K, display 4.41, proved on pages 34 and 35 through displays 8.10 to 8.16.
`d` is decreasing on `1, …, J`, satisfies `0 ≤ d_j ≤ e_j` and the budget, and maximises `∑_{j=1}^{J} (e^{B d_j} - e^{C d_j})` over all decreasing `x` with
`0 ≤ x_j ≤ e_j` whose cost `∑_j ∫_0^1 w(v) (e^{x_j T})^v dv` is at most `budget`; the weight
`w` is continuous and nonnegative, as `T f(vT) e^{-d_0 v T}` in display 8.11 is. If `d_r > 0` and
`d_j = 0` for `j > r`, then `d_j = e_j` for every `1 ≤ j < r`. -/
theorem theoremK_ordered_integral (J r : ℕ) (d e : ℕ → ℝ) (w : ℝ → ℝ)
    (T B C budget : ℝ) (hT : 0 < T) (hB : T < B) (hC : 0 ≤ C) (hCB : C < B)
    (hw : ContinuousOn w (Set.Icc 0 1)) (hw0 : ∀ v ∈ Set.Icc 0 1, 0 ≤ w v)
    (hr : r ∈ Finset.Icc 1 J) (hd : AntitoneOn d (Set.Icc 1 J))
    (he : AntitoneOn e (Set.Icc 1 J))
    (hbox : ∀ j ∈ Finset.Icc 1 J, 0 ≤ d j ∧ d j ≤ e j)
    (hactive : 0 < d r) (htail : ∀ j ∈ Set.Icc 1 J, r < j → d j = 0)
    (hbudget : (∑ j ∈ Finset.Icc 1 J,
      ∫ v in Set.Icc (0 : ℝ) 1, w v * (Real.exp (d j * T)) ^ v) ≤ budget)
    (hmax : ∀ x : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 J, 0 ≤ x j ∧ x j ≤ e j) →
      AntitoneOn x (Set.Icc 1 J) →
      (∑ j ∈ Finset.Icc 1 J, ∫ v in Set.Icc (0 : ℝ) 1,
        w v * (Real.exp (x j * T)) ^ v) ≤ budget →
      (∑ j ∈ Finset.Icc 1 J, (Real.exp (B * x j) - Real.exp (C * x j))) ≤
        ∑ j ∈ Finset.Icc 1 J, (Real.exp (B * d j) - Real.exp (C * d j))) :
    TheoremK_OptimalChoice r d e := by
  sorry

end LeanLab.Pintz2018.Greedy117

namespace LeanLab.Pintz2018.Residual117
open scoped Topology

/-- Theorem K, displays 4.41 and 4.42, for an abstract cost `H` and objective `G` in the
coordinates `y_j = e^{d_j T} ≥ 1` of display 8.10. Let `y` maximise `∑ G(z_j)` over decreasing `z`
with `1 ≤ z_j ≤ Y_j` and `∑ H(z_j) ≤ budget`, where `Y` is decreasing, `H` is concave and
continuous on `[1, ∞)` with `H 1 = 0`, and `G` is strictly convex and strictly increasing on
`[1, ∞)`. If `y_r > 1`, `y_j = 1` for `j > r` and some cap is not reached, then `y_j = Y_j` for
`1 ≤ j < r`, the budget is used up exactly, and `H(y_r)` is the budget minus
`∑_{j<r} H(Y_j)`. -/
theorem saturation_and_residual (J r : ℕ) (y Y : ℕ → ℝ) (H G : ℝ → ℝ) (budget : ℝ)
    (hr : r ∈ Finset.Icc 1 J) (hzero : H 1 = 0)
    (hH : ConcaveOn ℝ (Set.Ici 1) H) (hHcont : ∀ x : ℝ, 1 ≤ x → ContinuousAt H x)
    (hG : StrictConvexOn ℝ (Set.Ici 1) G) (hGmono : StrictMonoOn G (Set.Ici 1))
    (hmono : AntitoneOn y (Set.Icc 1 J)) (hY : AntitoneOn Y (Set.Icc 1 J))
    (hbox : ∀ j ∈ Finset.Icc 1 J, 1 ≤ y j ∧ y j ≤ Y j)
    (hactive : 1 < y r) (htail : ∀ j ∈ Set.Icc 1 J, r < j → y j = 1)
    (hdeficit : ∃ k ∈ Finset.Icc 1 J, y k < Y k)
    (hbudget : (∑ j ∈ Finset.Icc 1 J, H (y j)) ≤ budget)
    (hmax : ∀ z : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 J, 1 ≤ z j ∧ z j ≤ Y j) →
      AntitoneOn z (Set.Icc 1 J) →
      (∑ j ∈ Finset.Icc 1 J, H (z j)) ≤ budget →
      (∑ j ∈ Finset.Icc 1 J, G (z j)) ≤ ∑ j ∈ Finset.Icc 1 J, G (y j)) :
    TheoremK_OptimalChoice r y Y ∧
      (∑ j ∈ Finset.Icc 1 J, H (y j)) = budget ∧
      H (y r) = budget - ∑ j ∈ Finset.Icc 1 (r - 1), H (Y j) := by
  sorry

end LeanLab.Pintz2018.Residual117

namespace LeanLab.Pintz2018.Density117

/-- Theorem J, display 4.36, with the proof of displays 8.1 to 8.4 on page 33. The zeros
are `zeros`, with weights `A j ≥ 1` and values `p j = ψ_j ≥ ψ`; they fall into character
classes `groups` of sizes `n k`. From the estimate 7.20,
`(∑ (A_j ψ_j - ξ))² ≤ ∑ A_j + ξ ∑_{κ ≠ ν} N_ν N_κ + ε (∑ A_j)²`, with `0 ≤ ξ < ψ`,
`ξ ≤ 1` and `ξ + ε ≤ Δ²` for `Δ = ψ - ξ`, the weighted excess satisfies
`∑ (ψ_j - ψ) ≤ (1 - ξ) / (2Δ)`. -/
theorem excess_bound_of_720 {ι κ : Type*} [DecidableEq κ]
    (zeros : Finset ι) (groups : Finset κ) (A p : ι → ℝ) (n : κ → ℕ)
    (psi xi eps : ℝ) (hA : ∀ j ∈ zeros, 1 ≤ A j)
    (hp : ∀ j ∈ zeros, psi ≤ p j) (hDelta : xi < psi) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hgap : xi + eps ≤ (psi - xi) ^ 2) (htotal : (∑ k ∈ groups, n k) = zeros.card)
    (h720 : (∑ j ∈ zeros, (A j * p j - xi)) ^ 2 ≤
      (∑ j ∈ zeros, A j) +
        xi * (∑ i ∈ groups, ∑ j ∈ groups.erase i, (n i : ℝ) * (n j : ℝ)) +
        eps * (∑ j ∈ zeros, A j) ^ 2) :
    (∑ j ∈ zeros, (p j - psi)) ≤ (1 - xi) / (2 * (psi - xi)) := by
  sorry

end LeanLab.Pintz2018.Density117

