module

public import Mathlib

/-!
# Vinogradov's three primes theorem and almost all binary Goldbach, after Heath-Brown 1985

D. R. Heath-Brown, *The ternary Goldbach problem*, Rev. Mat. Iberoam. 1 (1985) 45–59,
DOI 10.4171/RMI/2. Heath-Brown derives, from the Siegel–Walfisz theorem (his 1.1), the mean
square estimate Theorem 1 for binary Goldbach and three corollaries: almost all even numbers are
sums of two primes (Corollary 1), Vinogradov's three primes theorem (Corollary 2), and infinitely
many three-term arithmetic progressions of primes (Corollary 3).

The target theorems, each proved in the solution with no hypothesis, are:
* `siegelWalfisz`: the Siegel–Walfisz theorem in the form Heath-Brown quotes, for ψ(x; k, l);
* `heathBrown_theorem1`: Theorem 1, `Σ_{2x < m ≤ 3x} |N₂(m) − x 𝔖(m)| ≪_C x² (log x)^{−C}`;
* `heathBrown_corollary1`: Corollary 1, at most `O_C(x (log x)^{−C})` even `m ≤ x` are not sums
  of two primes;
* `goldbach_logPowerSaving`: the same for `E(X)`, the even `4 ≤ n ≤ X` not sums of two primes,
  the theorem of van der Corput, Chudakov and Estermann, 1937–1938;
* `goldbach_densityZero`: `E(X)/X → 0`;
* `vinogradov_three_primes`: every sufficiently large odd number is a sum of three primes;
* `three_primes_in_ap`: Corollary 3.

All constants are ineffective, as in the paper. Binary Goldbach itself is open; nothing here
claims it. "≪" with constants depending on a parameter is read as: for each such parameter
some constant `K`, for every `x ≥ 2`. Lean names keep the namespaces of the lab where the proofs
were written: `ChenExplicit` for the twin prime constant, `PNTPort.PsiChi` for the theorems.
-/

@[expose] public section

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- `n` is a sum of three primes. -/
def IsTernarySum (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

end LeanLab

open Finset

noncomputable section
namespace LeanLab.ChenExplicit

/-- The twin prime constant `∏_{p > 2} (1 − 1/(p − 1)²) ≈ 0.66016`. The product converges
absolutely since `Σ 1/(p − 1)²` converges, so `∏'` takes its true value and not the junk `1`. -/
def twinC : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

end LeanLab.ChenExplicit
end

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- `ψ(x; k, l) = Σ_{n ≤ x, n ≡ l mod k} Λ(n)`. -/
def psi (x : ℝ) (k l : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k), Λ n

/-- Heath-Brown's 1.1, the Siegel–Walfisz theorem: for any `A > 0` there is `c(A) > 0` with
`ψ(x; k, l) = x/φ(k) + O_A(x exp(−c(A) (log x)^{1/2}))` uniformly for `(l, k) = 1` and
`k ≤ (log x)^A`. -/
def SiegelWalfisz : Prop :=
  ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k →
    Nat.Coprime l k → (k : ℝ) ≤ Real.log x ^ A →
      |psi x k l - x / (Nat.totient k : ℝ)| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x))

/-- `N₂(m) = Σ_{p ≤ x, p + p' = m} (log p)(log p')`, with `p, p'` prime. -/
def N2 (x : ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ (p : ℝ) ≤ x),
    Real.log p * Real.log (m - p : ℕ)

/-- The singular series `𝔖(m) = 2 ∏_{p ≥ 3} (1 − 1/(p − 1)²) ∏_{p ∣ m, p ≥ 3} (p − 1)/(p − 2)` for
even `m`, and `0` for odd `m`. The value at `m = 0` is junk and never used: Theorem 1 sums over
`m > 2x ≥ 4`. -/
def singular (m : ℕ) : ℝ :=
  if Even m then 2 * ChenExplicit.twinC *
    ∏ p ∈ m.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))
  else 0

/-- Theorem 1: for any `C > 0`, `Σ_{2x < m ≤ 3x} |N₂(m) − x 𝔖(m)| ≪_C x² (log x)^{−C}`. -/
def Theorem1 : Prop :=
  ∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∑ m ∈ (range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ)), |N2 x m - x * singular m|
      ≤ K * x ^ 2 * Real.log x ^ (-C)

/-- The number of even `m` with `lo < m ≤ hi` that are not a sum of two primes. -/
def excCount (lo hi : ℝ) : ℕ :=
  #{m ∈ range (⌊hi⌋₊ + 1) | lo < ((m : ℕ) : ℝ) ∧ Even m ∧ ¬ IsGoldbachSum m}

/-- Corollary 1: for any `C > 0` there are at most `O_C(x (log x)^{−C})` even integers `m ≤ x`
which are not the sum of two primes. Positive `m` are counted, so `2` is one of them. -/
def Corollary1 : Prop :=
  ∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → (excCount 0 x : ℝ) ≤ K * x * Real.log x ^ (-C)

/-- Corollary 3: there are infinitely many sets of three distinct primes in arithmetic
progression, written `p, p + d, p + 2d` with `d > 0`. -/
def Corollary3 : Prop :=
  {t : ℕ × ℕ | t.1.Prime ∧ (t.1 + t.2).Prime ∧ (t.1 + 2 * t.2).Prime ∧ 0 < t.2}.Infinite

end LeanLab.HeathBrown1985
end

namespace LeanLab.Ternary

/-- Every odd `n ≥ C` is a sum of three primes. -/
def TernaryAbove (C : ℝ) : Prop := ∀ n : ℕ, Odd n → C ≤ n → IsTernarySum n

end LeanLab.Ternary

namespace LeanLab.ExceptionalSet
open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-- `E X`, the number of even `n` with `4 ≤ n ≤ X` that are not a sum of two primes. -/
noncomputable def E (X : ℕ) : ℕ :=
  ((Finset.Icc 4 X).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)).card

/-- Almost all even numbers are sums of two primes: `E X / X → 0`. -/
def DensityZero : Prop := Tendsto (fun X : ℕ => (E X : ℝ) / X) atTop (𝓝 0)

/-- `E X ≪_A X / (log X)^A` for every `A > 0`; here `A` is the exponent and `C` the implied
constant, the reverse of the letters in `Theorem1`. -/
def LogPowerSaving : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → (E X : ℝ) ≤ C * X / Real.log X ^ A

end LeanLab.ExceptionalSet

namespace LeanLab.PNTPort.PsiChi

/-- The Siegel–Walfisz theorem, Heath-Brown's 1.1. -/
theorem siegelWalfisz : HeathBrown1985.SiegelWalfisz := by sorry

/-- Heath-Brown 1985, Theorem 1. -/
theorem heathBrown_theorem1 : HeathBrown1985.Theorem1 := by sorry

/-- Heath-Brown 1985, Corollary 1. -/
theorem heathBrown_corollary1 : HeathBrown1985.Corollary1 := by sorry

/-- Van der Corput, Chudakov, Estermann: `E(X) ≪_A X (log X)^{−A}` for every `A > 0`. -/
theorem goldbach_logPowerSaving : ExceptionalSet.LogPowerSaving := by sorry

/-- Vinogradov 1937, Heath-Brown's Corollary 2: every sufficiently large odd number is a sum of
three primes. `∃ C : ℝ` with every odd `n ≥ C` is the same as sufficiently large, since there are
odd `n ≥ C` for every `C`. -/
theorem vinogradov_three_primes : ∃ C : ℝ, Ternary.TernaryAbove C := by sorry

/-- Heath-Brown 1985, Corollary 3. -/
theorem three_primes_in_ap : HeathBrown1985.Corollary3 := by sorry

/-- Almost every even number is a sum of two primes, density form. -/
theorem goldbach_densityZero : ExceptionalSet.DensityZero := by sorry

end LeanLab.PNTPort.PsiChi
