module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.ChenExplicit.Statements

/-!
P0096 D. R. Heath-Brown, The Ternary Goldbach Problem, Rev. Mat. Iberoam. 1 1985 45-59,
DOI 10.4171/RMI/2, read from the EMS scan 2026-10-16, pages 45 to 52.
STATED: the Siegel-Walfisz input 1.1, Theorem 1, Corollaries 1 to 3, Theorem 2, the function
Λ_Q, the bound 2.5, Lemma 1 as 2.6 and 2.7, Lemma 2 as 2.11. The paper's results are
classical and ineffective; here every analytic result is a `Prop`, no placeholder proof.
"≪" with constants depending on A, B, C is read as: for each such parameter some K, for
every x ≥ 2. L = log x throughout.
PROVED elsewhere in this folder: Corollary 1 from Theorem 1, Bridge.lean; Λ_Q in Ramanujan
sum form, Bridge.lean.
AI-written Lean code, Claude, run 20261016T2204Z-20593. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- `ψ(x; k, l) = Σ_{n ≤ x, n ≡ l mod k} Λ(n)`. -/
def psi (x : ℝ) (k l : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k), Λ n

/-- 1.1, the Siegel-Walfisz theorem as the paper quotes it: for any `A > 0` there is
`C(A) > 0` with `ψ(x; k, l) = x/φ(k) + O(x exp(-C(A) (log x)^{1/2}))` uniformly for
`(l, k) = 1` and `k ≤ (log x)^A`. -/
def SiegelWalfisz : Prop :=
  ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k →
    Nat.Coprime l k → (k : ℝ) ≤ Real.log x ^ A →
      |psi x k l - x / (Nat.totient k : ℝ)| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x))

/-- `N₂(m) = Σ_{p ≤ x, p + p' = m} (log p)(log p')`, `p, p'` prime. -/
def N2 (x : ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ (p : ℝ) ≤ x),
    Real.log p * Real.log (m - p : ℕ)

/-- `𝔖(m) = 2 ∏_{p ≥ 3} (1 - 1/(p-1)²) ∏_{p ∣ m, p ≥ 3} (p-1)/(p-2)` for even `m`, and `0` for
odd `m`. -/
def singular (m : ℕ) : ℝ :=
  if Even m then 2 * ChenExplicit.twinC *
    ∏ p ∈ m.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))
  else 0

/-- Theorem 1: for any `C > 0`, `Σ_{2x < m ≤ 3x} |N₂(m) - x 𝔖(m)| ≪ x² (log x)^{-C}`. -/
def Theorem1 : Prop :=
  ∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∑ m ∈ (range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ)), |N2 x m - x * singular m|
      ≤ K * x ^ 2 * Real.log x ^ (-C)

/-- The number of even `m` with `lo < m ≤ hi` that are not a sum of two primes. -/
def excCount (lo hi : ℝ) : ℕ :=
  #{m ∈ range (⌊hi⌋₊ + 1) | lo < ((m : ℕ) : ℝ) ∧ Even m ∧ ¬ IsGoldbachSum m}

/-- Corollary 1: for any `C > 0` there are at most `O(x (log x)^{-C})` even integers `m ≤ x`
which are not the sum of two primes. Positive `m` are counted, so `2` is one of them. -/
def Corollary1 : Prop :=
  ∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → (excCount 0 x : ℝ) ≤ K * x * Real.log x ^ (-C)

/-- Corollary 2, Vinogradov: every sufficiently large odd number is the sum of three primes. -/
def Corollary2 : Prop := ∃ N : ℕ, ∀ n, Odd n → N ≤ n → IsTernarySum n

/-- Corollary 3: there are infinitely many sets of three distinct primes in arithmetic
progression, written `p, p + d, p + 2d` with `d > 0`. -/
def Corollary3 : Prop :=
  {t : ℕ × ℕ | t.1.Prime ∧ (t.1 + t.2).Prime ∧ (t.1 + 2 * t.2).Prime ∧ 0 < t.2}.Infinite

/-- Theorem 2, a Barban-Davenport-Halberstam theorem: for any `C > 0`,
`Σ_{k ≤ x (log x)^{-C}} Σ_{l ≤ k, (l,k) = 1} |ψ(x;k,l) - x/φ(k)|² ≪ x² (log x)^{8 - C/3}`. -/
def Theorem2 : Prop :=
  ∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∑ k ∈ Icc 1 ⌊x * Real.log x ^ (-C)⌋₊, ∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k),
      (psi x k l - x / (Nat.totient k : ℝ)) ^ 2 ≤ K * x ^ 2 * Real.log x ^ (8 - C / 3)

/-- `Λ_Q(n) = Σ_{q ≤ Q} μ(q)²/φ(q) Σ_{d ∣ (n, q)} d μ(d)`. -/
def LambdaQ (Q : ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊Q⌋₊, ((μ q : ℝ) ^ 2 / (Nat.totient q : ℝ)) *
    ∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ d : ℝ)

/-- The Ramanujan sum `c_q(n)`, by its classical divisor formula
`c_q(n) = Σ_{d ∣ (n, q)} d μ(q/d)`; the paper names `c_q(n)` without a formula. -/
def ramanujan (q n : ℕ) : ℝ := ∑ d ∈ (n.gcd q).divisors, (d : ℝ) * (μ (q / d) : ℝ)

/-- `Δ_Q(n) = Λ_Q(n) - Λ(n)`. -/
def DeltaQ (Q : ℝ) (n : ℕ) : ℝ := LambdaQ Q n - Λ n

/-- `Σ_{n ≤ x, n ≡ l mod k} f(n)`. -/
def apSum (f : ℕ → ℝ) (x : ℝ) (k l : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % k = l % k), f n

/-- 2.5: `Λ_Q(n) ≪ d(n) (log Q)²`, read for `Q ≥ 2`, `n ≥ 1`. -/
def Bound2_5 : Prop :=
  ∃ K : ℝ, ∀ Q : ℝ, 2 ≤ Q → ∀ n : ℕ, 1 ≤ n →
    |LambdaQ Q n| ≤ K * (n.divisors.card : ℝ) * Real.log Q ^ 2

/-- Lemma 1, 2.6: `Σ_{n ≤ x, n ≡ l (k)} Λ_Q(n) = x/φ(k) + O(Q L²) + O(x L (kQ)^{-1} d(k))`
for `(k, l) = 1`, uniformly for `1 ≤ Q, k ≤ x`. -/
def Lemma1_6 : Prop :=
  ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ Q : ℝ, 1 ≤ Q → Q ≤ x → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
    Nat.Coprime l k →
      |apSum (LambdaQ Q) x k l - x / (Nat.totient k : ℝ)| ≤
        K * (Q * Real.log x ^ 2 + x * Real.log x / (k * Q) * (k.divisors.card : ℝ))

/-- Lemma 1, 2.7: `Σ_{n ≤ x, n ≡ l (k)} Δ_Q(n) ≪_A Q L² + x L (kQ)^{-1} (k, l) d(k) + x L^{-A}`
for any `l`, uniformly for `1 ≤ Q, k ≤ x`. -/
def Lemma1_7 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ Q : ℝ, 1 ≤ Q → Q ≤ x → ∀ k l : ℕ, 1 ≤ k →
    (k : ℝ) ≤ x →
      |apSum (DeltaQ Q) x k l| ≤
        K * (Q * Real.log x ^ 2 + x * Real.log x / (k * Q) * (Nat.gcd k l : ℝ) *
          (k.divisors.card : ℝ) + x * Real.log x ^ (-A))

/-- `δ₁(x, k, Q) = Σ_{l=1}^{k} |Σ_{n ≤ x, n ≡ l (k)} Δ_Q(n)|`. -/
def delta1 (x : ℝ) (k : ℕ) (Q : ℝ) : ℝ := ∑ l ∈ Icc 1 k, |apSum (DeltaQ Q) x k l|

/-- Lemma 2, 2.11: with `Q = L^B` and `K ≤ x Q^{-1}`, `Σ_{k ≤ K} k^{-1} δ₁(x,k,Q) ≪_B x Q^{-1/2} L⁷`. -/
def Lemma2 : Prop :=
  ∀ B : ℝ, 0 < B → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ K : ℝ, K ≤ x / Real.log x ^ B →
    ∑ k ∈ Icc 1 ⌊K⌋₊, delta1 x k (Real.log x ^ B) / k ≤
      C * x * (Real.log x ^ B) ^ (-(1 : ℝ) / 2) * Real.log x ^ 7

/-! ### The cited results, as hypotheses -/

/-- The paper's main results, each cited, never proved here. -/
structure Cited : Prop where
  siegelWalfisz : SiegelWalfisz
  theorem1 : Theorem1
  theorem2 : Theorem2
  corollary2 : Corollary2
  corollary3 : Corollary3

end LeanLab.HeathBrown1985
