module

public import Mathlib

/-!
# Brüdern and Perelli 1998, Theorem 2, from Karacuba's estimate

J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst. Fourier 48 (1998)
353-378, Theorem 2 on page 354. Let `F(x) = exp((log x)^γ)` with `1 < γ < 3/2`. For
`0 < c < 1` and `0 < C < γ - 1` there is `κ > 0` such that the exponential sum
`Σ_{N ≤ n ≤ 2N} e(α F(n))` is `≪ N exp(-κ (log N)^{3-2γ})`, uniformly for
`F(2N)^{-c} ≤ |α| ≤ F(N)^C`.

The statement is proved conditional on the paper's Lemma 10, pages 370 to 371, which is
Theorem 1 of A. A. Karacuba, Estimates for trigonometric sums by Vinogradov's method, and some
applications, Proc. Steklov Inst. Math. 112 (1973) 251-265, as the paper cites it. Lemma 10
is the explicit hypothesis `Lemma10DQ5` of the compared theorem, never an axiom.

Every definition below repeats the definition of the same name in the solution, with the
same `open` lines and local instances. Goldbach's problem remains open and is not claimed here.
-/

@[expose] public section

namespace LeanLab.ExceptionalSet.BrudernPerelli1998
open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-- `F γ x = exp((log x)^γ)`. -/
noncomputable def F (γ x : ℝ) : ℝ := Real.exp (Real.log x ^ γ)

end LeanLab.ExceptionalSet.BrudernPerelli1998

namespace LeanLab.ExceptionalSet.U1539

open Real MeasureTheory Polynomial
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- `e(x) = exp(2πix)`. -/
noncomputable def eC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- The sum of Theorem 2, `Σ_{N ≤ n ≤ 2N} e(α F(n))`. -/
noncomputable def expSumF (γ α : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc N (2 * N), eC (α * F γ n)

/-- Karacuba's class `𝓕(N, θ, Θ, Θ₀, δ)` of Lemma 10, p. 370-371, with its `k` named:
`f` is `k` times differentiable around `[N, 2N]`, `|f^{(k)}/k!| ≤ N^{-Θ₀ k}` there, and some
`S ⊆ {1, ..., k-1}` with `#S ≥ δk` has `N^{-θs} ≤ |f^{(s)}/s!| ≤ N^{-Θs}` on `[N, 2N]`. We ask
for `C^k` on an open set around `[N, 2N]`, which only shrinks the class. -/
def KClass (N : ℕ) (θ Θ Θ₀ δ : ℝ) (f : ℝ → ℝ) (k : ℕ) : Prop :=
  3 ≤ k ∧ (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (2 * N) ⊆ U ∧ ContDiffOn ℝ k f U) ∧
  (∀ x ∈ Set.Icc (N : ℝ) (2 * N), |iteratedDeriv k f x / k.factorial| ≤ (N : ℝ) ^ (-(Θ₀ * k))) ∧
  ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 (k - 1) ∧ δ * k ≤ S.card ∧
    ∀ s ∈ S, ∀ x ∈ Set.Icc (N : ℝ) (2 * N),
      (N : ℝ) ^ (-(θ * s)) ≤ |iteratedDeriv s f x / s.factorial| ∧
      |iteratedDeriv s f x / s.factorial| ≤ (N : ℝ) ^ (-(Θ * s))

/-- Theorem 2, p. 354: for `1 < γ < 3/2`, `0 < c < 1`, `0 < C < γ - 1` there is `κ > 0`
with `Σ_{N ≤ n ≤ 2N} e(αF(n)) ≪ N exp(-κ (log N)^{3-2γ})` uniformly in
`F(2N)^{-c} ≤ |α| ≤ F(N)^C`. -/
def Theorem2 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ c C : ℝ, 0 < c → c < 1 → 0 < C → C < γ - 1 →
    ∃ κ B : ℝ, 0 < κ ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
      F γ (2 * N) ^ (-c) ≤ |α| → |α| ≤ F γ N ^ C →
      ‖expSumF γ α N‖ ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ))

end LeanLab.ExceptionalSet.U1539

namespace LeanLab.ExceptionalSet.U1539

open Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- The named hypothesis: Lemma 10 of Brüdern and Perelli 1998, pages 370 to 371, which is
Theorem 1 of Karacuba 1973 as the paper cites it. For `0 < δ < 1` and `0 < Θ < θ < Θ₀ < 1`
there are `B, c > 0` such that `|Σ_{N < n ≤ 2N} e(f(n))| ≤ B N^{1 - c/k²}` for every `N ≥ 1`
and every `f` in Karacuba's class `KClass N θ Θ Θ₀ δ f k`. -/
def Lemma10DQ5 : Prop :=
  ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ),
      KClass N θ Θ Θ₀ δ f k →
      ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2)

/-- Theorem 2 of Brüdern and Perelli 1998, page 354, conditional on Lemma 10 of the paper,
Karacuba 1973 Theorem 1, taken as the explicit hypothesis `Lemma10DQ5`. -/
theorem theorem2_of_named_dq5 (h10 : Lemma10DQ5) : Theorem2 := by
  sorry

end LeanLab.ExceptionalSet.U1539
