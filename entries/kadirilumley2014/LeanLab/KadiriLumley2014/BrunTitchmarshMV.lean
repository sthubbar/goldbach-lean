module

public import LeanLab.KadiriLumley2014.ZeroDefinitions259
public import LeanLab.RamareSaouter2003.Theorem4Parts

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1, page 3 equations 2.6 and 2.7.
The pointwise Brun Titchmarsh bound of the endpoint tails, derived from the named input `RamareSaouter2003.Thm4Parts.MVBrunTitchmarsh`, which is
Montgomery and Vaughan, The Large Sieve, Mathematika 20, 1973, Theorem 2, the same citation the
paper gives on page 3.

The paper bounds `θ(e^u X (1 + δ t)) - θ(X (1 + δ t))` by the logarithm of the top of the
window times the number of primes in it, and the number of primes by Montgomery and Vaughan,
`2 y / log y` with `y = (e^u - 1) X (1 + δ t)`.  Enlarging the logarithm of the top to
`log (e^u X (1 + δ))`, the length to `(e^u - 1) X (1 + δ)` and shrinking the logarithm of the
length to `log (X (e^u - 1))` gives the coefficient of equation 2.7, `tailCoefficient`.
This file proves that chain, conditional on `MVBrunTitchmarsh`.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.BrunTitchmarshMV
open Real Set
open LeanLab.KadiriLumley2014.Task92 LeanLab.RamareSaouter2003.Thm4Parts

/-- Page 3 equations 2.6 and 2.7, the pointwise Brun Titchmarsh bound of the endpoint tails.
Proved conditional on `MVBrunTitchmarsh`, Montgomery and Vaughan 1973 Theorem 2.
The hypotheses `δ ≤ 0.0001`, `u ≤ 0.0001` and `e^38 ≤ X` are kept and
unused: the chain needs only `0 ≤ δ`, `0 < u`, `0 < X`, `1 < X (e^u - 1)` and `t ∈ [0, 1]`. -/
theorem brun_titchmarsh_pointwise_of_MV (hMV : MVBrunTitchmarsh) {δ u X t : ℝ}
    (hδ : 0 ≤ δ) (_hδ1 : δ ≤ 0.0001) (hu : 0 < u) (_hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) (hgap : 1 < X * (Real.exp u - 1))
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t)) ≤ tailCoefficient δ u X := by
  have hX0 : 0 < X := (Real.exp_pos 38).trans_le hX
  have hE : 0 < Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hdt0 : 0 ≤ δ * t := mul_nonneg hδ ht.1
  have hdt1 : δ * t ≤ δ := by nlinarith [ht.2]
  set Z := X * (1 + δ * t) with hZ
  have hXZ : X ≤ Z := by rw [hZ]; nlinarith
  have hZ0 : 0 < Z := hX0.trans_le hXZ
  have hZδ : Z ≤ X * (1 + δ) := by rw [hZ]; nlinarith
  set y := Z * (Real.exp u - 1) with hy
  have hy1 : 1 < y := by
    have : X * (Real.exp u - 1) ≤ y := mul_le_mul_of_nonneg_right hXZ hE.le
    linarith
  have hZy : Z + y = Real.exp u * Z := by rw [hy]; ring
  have hcount := hMV Z y hZ0 hy1
  rw [hZy] at hcount
  have hexpZ : 1 ≤ Real.exp u * Z := by
    have h1 : 1 ≤ Real.exp u := Real.one_le_exp hu.le
    nlinarith [Real.add_one_le_exp (38 : ℝ)]
  have hth := theta_sub_le (x := Z) (z := Real.exp u * Z)
    (by nlinarith [Real.one_le_exp hu.le]) hexpZ
  -- the logarithms
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hLtop0 : 0 ≤ Real.log (Real.exp u * Z) := Real.log_nonneg hexpZ
  have hLtop : Real.log (Real.exp u * Z) ≤ Real.log (Real.exp u * X * (1 + δ)) := by
    apply Real.log_le_log (by positivity)
    have : Real.exp u * Z ≤ Real.exp u * (X * (1 + δ)) :=
      mul_le_mul_of_nonneg_left hZδ (Real.exp_pos u).le
    linarith [show Real.exp u * (X * (1 + δ)) = Real.exp u * X * (1 + δ) by ring]
  have hLbot0 : 0 < Real.log (X * (Real.exp u - 1)) := Real.log_pos hgap
  have hLbot : Real.log (X * (Real.exp u - 1)) ≤ Real.log y := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_right hXZ hE.le
  have hylen : y ≤ (Real.exp u - 1) * X * (1 + δ) := by
    have := mul_le_mul_of_nonneg_right hZδ hE.le
    rw [hy]; linarith [show X * (1 + δ) * (Real.exp u - 1) = (Real.exp u - 1) * X * (1 + δ) by ring]
  have hy0 : 0 ≤ y := by linarith
  -- assemble
  set C : ℝ := (((Finset.Ioc ⌊Z⌋₊ ⌊Real.exp u * Z⌋₊).filter Nat.Prime).card : ℝ) with hC
  have step1 : C * Real.log (Real.exp u * Z) ≤ 2 * y / Real.log y * Real.log (Real.exp u * Z) :=
    mul_le_mul_of_nonneg_right hcount.le hLtop0
  have step2 : 2 * y / Real.log y ≤ 2 * y / Real.log (X * (Real.exp u - 1)) :=
    div_le_div_of_nonneg_left (by linarith) hLbot0 hLbot
  have step3 : 2 * y / Real.log (X * (Real.exp u - 1)) ≤
      2 * ((Real.exp u - 1) * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)) :=
    div_le_div_of_nonneg_right (by linarith) hLbot0.le
  have hq0 : 0 ≤ 2 * ((Real.exp u - 1) * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)) := by
    have : 0 ≤ (Real.exp u - 1) * X * (1 + δ) := by positivity
    positivity
  have step4 : 2 * y / Real.log y * Real.log (Real.exp u * Z) ≤
      2 * ((Real.exp u - 1) * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)) *
        Real.log (Real.exp u * X * (1 + δ)) :=
    mul_le_mul (step2.trans step3) hLtop hLtop0 hq0
  have hfin : 2 * ((Real.exp u - 1) * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)) *
      Real.log (Real.exp u * X * (1 + δ)) = tailCoefficient δ u X := by
    unfold tailCoefficient; ring
  linarith

end LeanLab.KadiriLumley2014.BrunTitchmarshMV
