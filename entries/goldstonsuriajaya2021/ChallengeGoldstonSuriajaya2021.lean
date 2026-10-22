module

public import Mathlib

/-!
# An average Goldbach representation formula, Goldston and Suriajaya, Theorem 1

D. A. Goldston and A. I. Suriajaya, *On an average Goldbach representation formula of Fujii*,
arXiv 2110.14250v2, Theorem 1, eq. (11). Write `ψ₂(n) = Σ_{m + m' = n} Λ(m) Λ(m')`, here `G n`.
Unconditionally, for every integer `N ≥ 2`,

`Σ_{n ≤ N} ψ₂(n) = N²/2 − 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) − (2 log 2π − 1/2) N + 2 (ζ'/ζ)(−1)
   − Σ_{k ≥ 1} N^{1−2k}/(k(2k−1)) + E(N)`,

an exact identity, where `ρ` runs over the nontrivial zeros of ζ and, for any `0 < r < 1`, eq. (12),
`E(N) = ∫₀¹ (Ψ(r, α) − I(r, α))² I_N(1/r, −α) dα`, with `Ψ(r, α) = Σ_{n ≥ 1} Λ(n) rⁿ e(nα)`,
`I(r, α) = Σ_{n ≥ 1} rⁿ e(nα)`, `I_N(r, α) = Σ_{1 ≤ n ≤ N} rⁿ e(nα)` and `e(u) = exp(2πiu)`.

The paper's theorem:
* `gs_theorem1_full`: Theorem 1, eq. (11), stated in `ℂ`, for every integer `N ≥ 2` and every
  `0 < r < 1`.
* `gs_theorem1_full_real`: the same identity in `ℝ`, with the real parts of the zero sum, of
  `(ζ'/ζ)(−1)` and of `E(N)`.
* `gs_theorem1_of_full`: Theorem 1, eq. (13), the "in particular" form, the `O(N)` read as one
  constant `K` for all `N ≥ 2` and `0 < r < 1`.

Derived results of this entry, not statements of the paper; they check that the formal statement
says what the paper means:
* `EGS_indep_r`: `E(N)` does not depend on `r`, as the paper's notation `E(N)` presumes.
* `EGS_im_eq_zero`, `logDeriv_zeta_neg_one_im`, `Z1_im_eq_zero`: `E(N)`, `(ζ'/ζ)(−1)` and the zero
  sum are real, so the identity in `ℂ` is the paper's real identity.
* `zeroSum_summable`: the zero sum converges absolutely.
* `trivSum_bounds`: the trivial zero sum lies in `[0, π²/3]` for `N ≥ 1`.
* `gs_theorem1_full_at_two`: the hypotheses are satisfiable; the identity at `N = 2`, `r = 1/2`,
  where the left side is `0`.

The sum over zeros. `NontrivialZero` is the set of zeros of `riemannZeta` in the open strip
`0 < Re ρ < 1`; each distinct zero appears once and is weighted by its multiplicity
`analyticOrderNatAt riemannZeta ρ`, so this is the paper's sum over zeros counted with
multiplicity. `zeroSum` is an unordered `tsum`. `zeroSum_summable`, a derived result of this entry, proves the family summed
in `Z1 x` summable for every `x > 0`, so `Z1 x` is the absolutely convergent sum of the paper and
not Lean's junk value `0`.

Binary Goldbach is open; nothing here claims it. This is an average over `n`, and unconditional.
An AI agent, Claude by Anthropic, wrote the Lean code. Lean names keep the namespaces of the lab
where the proofs were written.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- `G(n) = ∑_{m₁ + m₂ = n} Λ(m₁) Λ(m₂)`, the paper's `ψ₂(n)`; `Λ 0 = 0`, so the ends of the
antidiagonal add 0. -/
def G (n : ℕ) : ℝ := ∑ p ∈ antidiagonal n, Λ p.1 * Λ p.2

end LeanLab.GoldbachAverage

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- Nontrivial zeros of ζ: zeros in the open critical strip. -/
def NontrivialZero : Type := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- `Σ_ρ m(ρ) f(ρ)` over nontrivial zeros with multiplicity `m(ρ)`, an unordered `tsum`. -/
def zeroSum (f : ℂ → ℂ) : ℂ :=
  ∑' ρ : NontrivialZero, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * f ρ.1

/-- `Z1 x = Σ_ρ m(ρ) x^{ρ+1} / (ρ(ρ+1))`, the zero sum of Theorem 1. -/
def Z1 (N : ℝ) : ℂ := zeroSum (fun ρ => (N : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))

end LeanLab.GoldbachAverage

open Finset Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- `e(u) = exp(2πiu)`. -/
def eAdd (u : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * u)

/-- `Ψ(r, α) = Σ_n Λ(n) r^n e(αn)`. -/
def PsiGen (r α : ℝ) : ℂ := ∑' n : ℕ, (Λ n : ℂ) * (r : ℂ) ^ n * eAdd (α * n)

/-- `I(r, α) = Σ_n r^n e(αn)`, from `n = 1` as Goldston-Suriajaya's Λ-free comparison sum. -/
def IGen (r α : ℝ) : ℂ := ∑' n : ℕ, (if n = 0 then 0 else (r : ℂ) ^ n * eAdd (α * n))

/-- `I_N(r, α) = Σ_{n ≤ N} r^n e(αn)`. -/
def IGenN (N : ℕ) (r α : ℝ) : ℂ := ∑ n ∈ Icc 1 N, (r : ℂ) ^ n * eAdd (α * n)

/-- `E(N) = ∫_0^1 (Ψ(r,α) - I(r,α))² I_N(1/r, -α) dα`, eq. (12), for `0 < r < 1`; the radius `r` is
an argument here, and `EGS_indep_r` proves the value does not depend on it. -/
def EGS (N : ℕ) (r : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, (PsiGen r α - IGen r α) ^ 2 * IGenN N (1 / r) (-α)

end LeanLab.GoldbachAverage

open Finset Complex
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section
namespace LeanLab.GoldbachAverage.U1440

/-- The trivial zero sum of eq. (11), `Σ_{k ≥ 1} N^{1-2k}/(k(2k-1))`, written with `k + 1`
for `k ≥ 0`. -/
def trivSum (N : ℝ) : ℝ :=
  ∑' k : ℕ, N ^ (1 - 2 * ((k : ℝ) + 1)) / (((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) - 1))

/-- **Goldston-Suriajaya Theorem 1, eq. (11)**, unconditional, stated in `ℂ`: for every integer
`N ≥ 2` and every `0 < r < 1`,
`Σ_{n ≤ N} ψ₂(n) = N²/2 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) - (2 log 2π - 1/2) N + 2 (ζ'/ζ)(-1)
   - Σ_{k ≥ 1} N^{1-2k}/(k(2k-1)) + E(N)`. -/
theorem gs_theorem1_full (N : ℕ) (hN : 2 ≤ N) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    ((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) =
      (N : ℂ) ^ 2 / 2 - 2 * Z1 N - ((2 * Real.log (2 * π) - 1 / 2 : ℝ) : ℂ) * N
        + 2 * (deriv riemannZeta (-1) / riemannZeta (-1)) - ((trivSum N : ℝ) : ℂ)
        + EGS N r := by
  sorry

/-- **Goldston-Suriajaya Theorem 1, eq. (11), as an identity of real numbers**, the real parts of
the terms of `gs_theorem1_full`, which are all real. -/
theorem gs_theorem1_full_real (N : ℕ) (hN : 2 ≤ N) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    ∑ n ∈ range (N + 1), G n =
      (N : ℝ) ^ 2 / 2 - 2 * (Z1 N).re - (2 * Real.log (2 * π) - 1 / 2) * N
        + 2 * (deriv riemannZeta (-1) / riemannZeta (-1)).re - trivSum N
        + (EGS N r).re := by
  sorry

/-- **Derived result of this entry**: `E(N)` does not depend on the radius `0 < r < 1`. -/
theorem EGS_indep_r (N : ℕ) {r r' : ℝ} (hr0 : 0 < r) (hr : r < 1) (hr0' : 0 < r') (hr' : r' < 1) :
    EGS N r = EGS N r' := by
  sorry

/-- **Derived result of this entry**: `E(N)` is real. -/
theorem EGS_im_eq_zero (N : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r < 1) : (EGS N r).im = 0 := by
  sorry

/-- **Derived result of this entry**: the constant `(ζ'/ζ)(-1)` is real. -/
theorem logDeriv_zeta_neg_one_im : (deriv riemannZeta (-1) / riemannZeta (-1)).im = 0 := by
  sorry

/-- **Derived result of this entry**: the zero sum `Σ_ρ N^{ρ+1}/(ρ(ρ+1))` is real for `N ≥ 2`. -/
theorem Z1_im_eq_zero (N : ℕ) (hN : 2 ≤ N) : (Z1 N).im = 0 := by
  sorry

/-- **Derived result of this entry**: the zero sum in `Z1 x` converges absolutely: for every real
`x > 0` the family `ρ ↦ m(ρ) x^{ρ+1}/(ρ(ρ+1))` over the nontrivial zeros is summable, so `Z1 x` is its
genuine unordered sum, not the junk value `0`. The paper uses this absolute convergence. -/
theorem zeroSum_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun ρ : NontrivialZero => (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      ((x : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1)))) := by
  sorry

/-- **Derived result of this entry**: `0 ≤ Σ_{k ≥ 1} N^{1-2k}/(k(2k-1)) ≤ π²/3` for `N ≥ 1`. -/
theorem trivSum_bounds {N : ℝ} (hN : 1 ≤ N) : 0 ≤ trivSum N ∧ trivSum N ≤ π ^ 2 / 3 := by
  sorry

/-- **Goldston-Suriajaya Theorem 1, eq. (13)**, the "in particular" form, deduced here from eq. (11),
`Σ_{n ≤ N} ψ₂(n) = N²/2 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) + E(N) + O(N)`, the `O(N)` read as one constant
`K` for all integers `N ≥ 2` and all `0 < r < 1`. -/
theorem gs_theorem1_of_full : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ r : ℝ, 0 < r → r < 1 →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N - EGS N r‖ ≤ K * N := by
  sorry

/-- **Derived result of this entry, a non-vacuity check**: the identity at `N = 2`, `r = 1/2`,
where `Σ_{n ≤ 2} ψ₂(n) = 0`. -/
theorem gs_theorem1_full_at_two :
    (0 : ℂ) = (2 : ℂ) ^ 2 / 2 - 2 * Z1 2 - ((2 * Real.log (2 * π) - 1 / 2 : ℝ) : ℂ) * 2
        + 2 * (deriv riemannZeta (-1) / riemannZeta (-1)) - ((trivSum 2 : ℝ) : ℂ)
        + EGS 2 (1 / 2) := by
  sorry

end LeanLab.GoldbachAverage.U1440
