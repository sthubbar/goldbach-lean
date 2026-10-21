module

public import LeanLab.ExceptionalSet.PintzAlthofer2026Beta

/-!
# P0058 Languasco-Zaccagnini 2016, Lemma 2, explicit

Lab proof, unit U-5857, CLOUD 20261020T0014Z-cloud30. AI wrote this file. No cited input.
Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 p. 3, Lemma 2, quoting eq. (29) of Languasco-Zaccagnini 2012: for
integers `N ≥ 2` and `1 ≤ n ≤ 2N`, with `z = 1/N − 2πiα`,
`∫_{-1/2}^{1/2} e(−nα) z^{−2} dα = n e^{−n/N} + O(1)`, uniformly.

`lemma2`: the error is at most `1/π²`, for every real `N > 0` and `n > 0`, with no upper limit
on `n`. It is the PC's `PintzAlthofer2026Beta.truncated_beta` at `B = 1/2`, the Fourier
inversion of `t e^{−t/N}` on `t > 0` with the tails `|β| > 1/2` bounded explicitly: one input
serves both Pintz-Althöfer (4.14) and Languasco-Zaccagnini Lemma 2.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Real MeasureTheory Set

/-- **Lemma 2, explicit.** `‖∫_{(-1/2, 1/2]} e(−nα) (1/N − 2πiα)^{−2} dα − n e^{−n/N}‖ ≤ 1/π²`. -/
theorem lemma2 {N n : ℝ} (hN : 0 < N) (hn : 0 < n) :
    ‖(∫ α in Ioc (-(1 / 2 : ℝ)) (1 / 2), Complex.exp (((-2 * π * n * α : ℝ) : ℂ) * Complex.I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * π * α : ℝ) : ℂ) * Complex.I) ^ 2))
      - ((n * Real.exp (-n / N) : ℝ) : ℂ)‖ ≤ 1 / π ^ 2 := by
  have h := LeanLab.ExceptionalSet.PintzAlthofer2026Beta.truncated_beta hN
    (by norm_num : (0 : ℝ) < 1 / 2) hn
  have e : 1 / (2 * π ^ 2 * (1 / 2 : ℝ)) = 1 / π ^ 2 := by ring
  rw [e] at h
  exact h

/-- The paper's form: for integers `N ≥ 2`, `1 ≤ n ≤ 2N` the error is `O(1)`, here `≤ 1/π²`. -/
theorem lemma2_paper : ∃ K : ℝ, ∀ N n : ℕ, 2 ≤ N → 1 ≤ n → n ≤ 2 * N →
    ‖(∫ α in Ioc (-(1 / 2 : ℝ)) (1 / 2), Complex.exp (((-2 * π * n * α : ℝ) : ℂ) * Complex.I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * π * α : ℝ) : ℂ) * Complex.I) ^ 2))
      - ((n * Real.exp (-n / N) : ℝ) : ℂ)‖ ≤ K :=
  ⟨1 / π ^ 2, fun N n hN hn _ =>
    lemma2 (by exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast (by omega : 0 < n))⟩

end LeanLab.LZCesaroShort

