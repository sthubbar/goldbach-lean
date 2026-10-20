module

public import LeanLab.PNTPort.PsiChi.SiegelWalfisz
public import LeanLab.HeathBrown1985.Sigma3Weighted
public import LeanLab.HeathBrown1985.Bridge
public import LeanLab.HeathBrown1985.Vinogradov
public import LeanLab.HeathBrown1985.Corollary3
public import LeanLab.PNTPort.BV.FromSW

/-!
# Results of the lab that were CONDITIONAL ON Siegel-Walfisz, now unconditional

Lab proof, unit U-5210, CLOUD 20261019T0514Z-cloud17. AI wrote the Lean code. Each theorem below
applies an existing lab deduction `*_of_siegelWalfisz` to `siegelWalfisz`. Known mathematics,
ineffective constants. Binary Goldbach itself is OPEN; these are almost-all and ternary results.

* `heathBrown_theorem1`: Heath-Brown 1985 Theorem 1, `Σ_{2x < m ≤ 3x} |N₂(m) - x𝔖(m)| ≪ x²(log x)^{-C}`;
* `heathBrown_corollary1`: at most `O(x (log x)^{-C})` even `m ≤ x` are not sums of two primes;
* `goldbach_logPowerSaving`: the exceptional set `E(X) ≪ X / log^A X` for every `A`,
  the van der Corput, Chudakov, Estermann theorem;
* `vinogradov_three_primes`: every sufficiently large odd number is a sum of three primes;
* `three_primes_in_ap`: Heath-Brown's Corollary 3;
* `bombieriVinogradov`: the Bombieri-Vinogradov theorem in the lab's form `BV.BombieriVinogradov`,
  at y = x, without the inner max over y ≤ x;
* `goldbach_densityZero`: the exceptional set has density zero.
-/

@[expose] public section


namespace LeanLab.PNTPort.PsiChi

theorem heathBrown_theorem1 : HeathBrown1985.Theorem1 :=
  HeathBrown1985.theorem1_of_siegelWalfisz siegelWalfisz

theorem heathBrown_corollary1 : HeathBrown1985.Corollary1 :=
  HeathBrown1985.corollary1_of_theorem1 heathBrown_theorem1

theorem goldbach_logPowerSaving : ExceptionalSet.LogPowerSaving :=
  HeathBrown1985.logPowerSaving_of_theorem1 heathBrown_theorem1

theorem vinogradov_three_primes : ∃ C : ℝ, Ternary.TernaryAbove C :=
  HeathBrown1985.vinogradov_of_siegelWalfisz siegelWalfisz

theorem three_primes_in_ap : HeathBrown1985.Corollary3 :=
  HeathBrown1985.corollary3_of_siegelWalfisz siegelWalfisz

theorem bombieriVinogradov : BV.BombieriVinogradov :=
  BV.bombieriVinogradov_of_siegelWalfisz siegelWalfisz

/-- Almost every even number is a sum of two primes, density form. -/
theorem goldbach_densityZero : ExceptionalSet.DensityZero :=
  ExceptionalSet.densityZero_of_logPowerSaving goldbach_logPowerSaving

end LeanLab.PNTPort.PsiChi
