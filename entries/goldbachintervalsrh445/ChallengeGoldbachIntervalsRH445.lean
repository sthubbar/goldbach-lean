module

public import Mathlib

/-!
# CONDITIONAL: Goldbach numbers in intervals of length 4.45 log² x under RH

S. Hubbard, *Goldbach numbers in intervals of length 4.45 log² x under the Riemann Hypothesis*,
preprint, aiXiv.online 2610.02672, aiXiv.science aixiv.261025.000001, Hexagon 2610.00542. It
improves the constant 123 of A. Chirre and M. V. Hagen, *On Goldbach numbers in short
intervals*, arXiv 2512.23534, Theorem 1, to 4.45, by the method of Chirre and Hagen.

The target theorem, `LeanLab.Routes.U1508.goldbach_445_hsw_gZ`: assume the Riemann Hypothesis,
Mathlib's `RiemannHypothesis`, the paper's own hypothesis. Then for every real `x ≥ 3` there is a
Goldbach number `n`, a sum of two odd primes, with `x < n < x + 4.45 (log x)²`.

CONDITIONAL. Besides RH, the theorem takes these cited inputs as explicit hypotheses, never as
axioms. They are statements about `gZ`, the ordinates of the nontrivial zeros of ζ counted with
multiplicity, and are transcriptions by the Lean Lab, not Mathlib results:
* `SmoothT2.ExplicitA gZ Z δ`, under RH, for every `0 < δ ≤ 10⁻¹³`: the truncated explicit
  formula of Montgomery and Vaughan, *Multiplicative Number Theory I*, (12.1), applied at `y` and
  `(1+δ)y`, along a sequence of finite sets `Z n` of zeros;
* `SmoothT2.HadamardK gZ`, under RH: `Σ_{γ' ∈ s} 4/(4 + (γ - γ')²) ≤ log |γ|` for every finite
  set `s` of zeros, a consequence of the Hadamard product;
* `SmoothT2.Ordinates14 gZ`: every ordinate has `|γ| ≥ 14`, the first zero being at 14.1347…;
* `Lemma26B.BPTN gZ`, under RH: the zero count of Brent, Platt and Trudgian, J. Number Theory
  238 (2022), Lemma 1, for `T ≥ 10¹³`;
* `Dudek2014.SigmaH.HSWN70 gZ` and `PNTPort.ExplicitPsi1.FirstDiff.HSWHead14 gZ`: the zero count
  of Hasanalizade, Shen and Wong, arXiv 2107.06506, Corollary 1.2, for `T ≥ 70` and `T ≥ 14`;
* `EvenGoldbachUpTo (4 * 10 ^ 18)`: every even `n` with `4 ≤ n ≤ 4·10¹⁸` is a sum of two primes,
  the computation of Oliveira e Silva, Herzog and Pardi, Math. Comp. 83 (2014).

Binary Goldbach is open; nothing here claims it. AI wrote the Lean code, Claude, Anthropic.
Lean names keep the namespaces of the lab where the proofs were written; every definition below
is restated under its exact name and in the same `open` context as in the solution files.
-/

@[expose] public section

/-! ### Goldbach sums, `LeanLab/Common/Goldbach.lean` -/

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- Binary Goldbach holds for every even `n` with `4 ≤ n ≤ N`. -/
def EvenGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n, Even n → 4 ≤ n → n ≤ N → IsGoldbachSum n

end LeanLab

/-! ### Goldbach numbers, `LeanLab/ChirreHagen2025/Statements.lean` -/

namespace LeanLab.ChirreHagen2025
open Real Chebyshev

/-- The paper's Goldbach number: a positive integer that is the sum of two odd primes. -/
def IsGoldbachNumber (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p + q = n

end LeanLab.ChirreHagen2025

/-! ### The zeros of ζ, `LeanLab/PNTPort/ExplicitPsi1/ZeroSum.lean` and `DudekTrudgian.lean` -/

namespace LeanLab.PNTPort.ExplicitPsi1

open Complex Filter Topology Set

local notation "ζ" => riemannZeta

/-- The zeros of ζ with `Re ρ ≥ -1/2`. These are exactly the nontrivial zeros: ζ has no zero on
`[-1/2, 0]` or on `Re s ≥ 1`, and Mathlib's value of `riemannZeta` at the pole `s = 1` is not
zero. -/
def Zall : Set ℂ := {ρ | ζ ρ = 0 ∧ -1 / 2 ≤ ρ.re}

end LeanLab.PNTPort.ExplicitPsi1

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Complex
open LeanLab.PNTPort.ExplicitPsi1

local notation "ζ" => riemannZeta

/-- The nontrivial zeros of ζ with multiplicity, as an index type: a zero `ρ` of order `m(ρ)`
contributes `m(ρ)` indices. -/
abbrev ZIdx := Σ ρ : Zall, Fin (analyticOrderNatAt ζ (ρ : ℂ))

/-- Their ordinates, `γ = Im ρ`. -/
noncomputable def gZ (i : ZIdx) : ℝ := ((i.1 : ℂ)).im

end LeanLab.PNTPort.ExplicitPsi1.Trivial

/-! ### The kernel and the zero polynomial, `LeanLab/ChirreHagen2025/SmoothKernel.lean` and
`SmoothY.lean` -/

namespace LeanLab.ChirreHagen2025.SmoothKernel
open Complex MeasureTheory Set

/-- The kernel `4/(4 + t²)`. -/
noncomputable def K (t : ℝ) : ℝ := 4 / (4 + t ^ 2)

/-- `P(y) = Σ_i c_i y^{1/2 + iγ_i}`, a finite sum over `s`. -/
noncomputable def P {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) (y : ℝ) : ℂ :=
  ∑ i ∈ s, c i * (y : ℂ) ^ ((1 / 2 : ℂ) + (γ i : ℂ) * I)

end LeanLab.ChirreHagen2025.SmoothKernel

/-! ### `𝒱(δ, y)`, `LeanLab/ChirreHagen2025/Local36.lean` -/

namespace LeanLab.ChirreHagen2025.Local36
open Real Chebyshev

/-- `𝒱(δ, y) = ψ((1+δ)y) - ψ(y) - δ y`, with `ψ` Mathlib's Chebyshev function. -/
noncomputable def V (δ y : ℝ) : ℝ := ψ ((1 + δ) * y) - ψ y - δ * y

end LeanLab.ChirreHagen2025.Local36

/-! ### The explicit formula and the Hadamard input, `LeanLab/ChirreHagen2025/SmoothTheorem2.lean` -/

namespace LeanLab.ChirreHagen2025.SmoothT2
open Complex MeasureTheory Set Filter Topology
open LeanLab.ChirreHagen2025.SmoothKernel
open LeanLab.ChirreHagen2025.Local36 (V)

/-- `B_δ(y) = -(1/2)(log(1 - ((1+δ)y)^-2) - log(1 - y^-2))`, the contribution of the trivial
zeros and of `log(1 - y⁻²)` to `ψ((1+δ)y) - ψ(y) - δy`. -/
noncomputable def Bf (δ y : ℝ) : ℝ :=
  -(1 / 2) * (Real.log (1 - (((1 + δ) * y) ^ 2)⁻¹) - Real.log (1 - (y ^ 2)⁻¹))

variable {ι : Type*}

/-- `ρ = 1/2 + iγ`. -/
noncomputable def rho (γ : ι → ℝ) (i : ι) : ℂ := 1 / 2 + (γ i : ℂ) * I

/-- `c_ρ = ((1+δ)^ρ - 1)/ρ`. -/
noncomputable def cδ (γ : ι → ℝ) (δ : ℝ) (i : ι) : ℂ :=
  (((1 + δ : ℝ) : ℂ) ^ rho γ i - 1) / rho γ i

/-- Cited, the explicit formula: Montgomery-Vaughan (12.1) at `y` and `(1+δ)y`, as the paper's
display for `A_δ`. For almost every `y ≥ 2`, the finite sums `Σ_{ρ ∈ Z n} c_ρ y^ρ`, with every
`ρ = 1/2 + iγ`, tend to `-(𝒱(δ, y) - B_δ(y))` as `n → ∞`. -/
def ExplicitA (γ : ι → ℝ) (Z : ℕ → Finset ι) (δ : ℝ) : Prop :=
  ∀ᵐ y ∂volume, 2 ≤ y →
    Tendsto (fun n => P (Z n) (cδ γ δ) γ y) atTop (𝓝 (-((V δ y - Bf δ y : ℝ) : ℂ)))

/-- Cited: `Σ_{γ' ∈ s} 4/(4 + (γ - γ')²) ≤ log |γ|` for every ordinate `γ` and every finite set
`s` of ordinates. -/
def HadamardK (γ : ι → ℝ) : Prop :=
  ∀ (s : Finset ι) (i : ι), ∑ j ∈ s, K (γ i - γ j) ≤ Real.log |γ i|

/-- Every ordinate has `|γ| ≥ 14`. -/
def Ordinates14 (γ : ι → ℝ) : Prop := ∀ i, 14 ≤ |γ i|

end LeanLab.ChirreHagen2025.SmoothT2

/-! ### The Brent-Platt-Trudgian count, `LeanLab/ChirreHagen2025/Lemma26BPT.lean` -/

namespace LeanLab.ChirreHagen2025.Lemma26B
open MeasureTheory Set Filter Topology Real

variable {ι : Type*}

/-- The main term `M(T) = (T/2π) log(T/(2πe)) + 7/8`. -/
noncomputable def Mt (T : ℝ) : ℝ := T / (2 * π) * log (T / (2 * π * exp 1)) + 7 / 8

/-- Brent-Platt-Trudgian Lemma 1, `|Q(T)| ≤ 0.137 log T + 0.443 log log T + 1.588 + 0.2/T`. -/
noncomputable def Rt (T : ℝ) : ℝ := 0.137 * log T + 0.443 * log (log T) + 1.588 + 0.2 / T

/-- Cited, Brent-Platt-Trudgian JNT 238 (2022) Lemma 1, `N(T) = M(T) + Q(T)`, as counts over any
finite set of the ordinates, both signs: at most `2(M(T) + R(T))` with `|γ| ≤ T`, and at most
`2((M(t) + R(t)) - (M(T) - R(T)))` with `T < |γ| ≤ t`, for `10^13 ≤ T ≤ t`. -/
def BPTN (γ : ι → ℝ) : Prop :=
  (∀ T : ℝ, 10 ^ 13 ≤ T → ∀ s : Finset ι,
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ 2 * (Mt T + Rt T)) ∧
  (∀ T t : ℝ, 10 ^ 13 ≤ T → T ≤ t → ∀ s : Finset ι,
    ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤ 2 * ((Mt t + Rt t) - (Mt T - Rt T)))

end LeanLab.ChirreHagen2025.Lemma26B

/-! ### The Hasanalizade-Shen-Wong count, `LeanLab/ChirreHagen2025/Lemma26HSW.lean`,
`LeanLab/Dudek2014/SigmaHSW.lean` and `LeanLab/PNTPort/ExplicitPsi1/FirstDiffHSW.lean` -/

namespace LeanLab.ChirreHagen2025.Lemma26H
open MeasureTheory Set Filter Topology Real

variable {ι : Type*}

/-- The main term `M(T) = (T/2π) log(T/(2πe)) + 7/8`. -/
noncomputable def Mt (T : ℝ) : ℝ := T / (2 * π) * log (T / (2 * π * exp 1)) + 7 / 8

/-- The Hasanalizade-Shen-Wong error `0.1038 log T + 0.2573 log log T + 9.3675` with the `7/8`
of `M(T)` added, `R(T) = 0.1038 log T + 0.2573 log log T + 10.2425`. -/
noncomputable def Rt (T : ℝ) : ℝ := 0.1038 * log T + 0.2573 * log (log T) + 10.2425

end LeanLab.ChirreHagen2025.Lemma26H

namespace LeanLab.Dudek2014.SigmaH
open MeasureTheory Set Filter Topology Real
open LeanLab.ChirreHagen2025.Lemma26H (Mt Rt)

variable {ι : Type*}

/-- Cited, Hasanalizade-Shen-Wong arXiv 2107.06506 Corollary 1.2,
`|N(T) - (T/2π) log(T/(2πe))| ≤ 0.1038 log T + 0.2573 log log T + 9.3675`, in its `N(T)` form
with the `7/8` moved into the error, as counts over any finite set of the ordinates, both signs,
for `70 ≤ T ≤ t`. -/
def HSWN70 (γ : ι → ℝ) : Prop :=
  (∀ T : ℝ, 70 ≤ T → ∀ s : Finset ι,
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ 2 * (Mt T + Rt T)) ∧
  (∀ T t : ℝ, 70 ≤ T → T ≤ t → ∀ s : Finset ι,
    ((s.filter (fun i => T < |γ i| ∧ |γ i| ≤ t)).card : ℝ) ≤ 2 * ((Mt t + Rt t) - (Mt T - Rt T)))

end LeanLab.Dudek2014.SigmaH

namespace LeanLab.PNTPort.ExplicitPsi1.FirstDiff
open MeasureTheory Set Filter Topology Real
open LeanLab.ChirreHagen2025.Lemma26H (Mt Rt)

variable {ι : Type*}

/-- Cited, the upper bound of Hasanalizade-Shen-Wong Corollary 1.2 for `T ≥ 14`, `7/8` in the
error as in `SigmaH.HSWN70`, as counts over any finite set of the ordinates, both signs. -/
def HSWHead14 (γ : ι → ℝ) : Prop :=
  ∀ T : ℝ, 14 ≤ T → ∀ s : Finset ι, ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ 2 * (Mt T + Rt T)

end LeanLab.PNTPort.ExplicitPsi1.FirstDiff

/-! ### The theorem, `LeanLab/Routes/U1508Compose445.lean` -/

namespace LeanLab.Routes.U1508
open Real Chebyshev
open LeanLab.ChirreHagen2025
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx)
open LeanLab.Dudek2014.SigmaH (HSWN70)

/-- CONDITIONAL. Under RH, for every real `x ≥ 3` there is a Goldbach number `n`, a sum of two
odd primes, with `x < n < x + 4.45 (log x)²`, given the cited inputs as hypotheses: the explicit
formula `ExplicitA` for every `0 < δ ≤ 10⁻¹³` and `HadamardK`, both under RH; `Ordinates14`;
the Brent-Platt-Trudgian count `BPTN` under RH; the even Goldbach check up to `4·10¹⁸`; and the
Hasanalizade-Shen-Wong counts `HSWN70` and `HSWHead14`; all for the ordinates `gZ` of the
nontrivial zeros of ζ with multiplicity, `Z` any sequence of finite sets of them. -/
theorem goldbach_445_hsw_gZ {Z : ℕ → Finset ZIdx}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA gZ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK gZ) (h14 : SmoothT2.Ordinates14 gZ)
    (hB : RiemannHypothesis → Lemma26B.BPTN gZ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hN : HSWN70 gZ) (hHd : HSWHead14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.45 * Real.log x ^ 2 := by
  sorry

end LeanLab.Routes.U1508
