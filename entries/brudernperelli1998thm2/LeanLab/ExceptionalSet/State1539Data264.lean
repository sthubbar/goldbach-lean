module

public import Mathlib
public import LeanLab.ExceptionalSet.BrudernPerelli1998

/-!
Unit U-1539, run 20261026T0403Z-9802, STATE job for P0082, track T1.
J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 no. 2 (1998) 353-378, doi 10.5802/aif.1621,
open access https://aif.centre-mersenne.org/item/10.5802/aif.1621.pdf .

AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.

Source: the open access PDF fetched in the cloud this run, 27 pages, text layer plus page
images rendered at 120 and 300 dpi for every display used below. Page numbers are journal pages.
Theorem 1, p. 354, is already sealed as `BrudernPerelli1998.Theorem1`, CITED there.

This file adds the paper's other main result and its named lemmas as sealed statements:
* Theorem 2, p. 354, CITED.
* Lemma 1, p. 355-356; Lemma 4, p. 359; Lemmas 6 and 7, p. 362; Lemma 8, p. 365;
  Lemma 9, p. 368; Lemmas 11 to 16, p. 372-376: open statements.
* Lemma 10, p. 370-371, Karacuba's Theorem 1, CITED.
* NOT STATED: Lemmas 2 and 3, p. 358, which restate Montgomery-Vaughan (6.17) and (7.1) and
  depend on the unnamed constant of the zero-free region (9); Lemma 5, p. 360, whose Γ_j are
  defined only through the upper bounds (14) and (15), so no definite quantity is bounded.

Where the paper's quantifiers fix one κ̃ for all of §4 to §7, the statements below say
"there is some κ > 0" separately in each lemma, after δ is fixed. This is weaker than the
paper and so stays true if the paper is right.

QUESTIONs, recorded in STATEMENTS.md:
* Lemma 12, display (50), p. 373, prints 2^{2t+j}; the proof on p. 373-374 and its use on
  p. 374-375 give s^{2t+j}. The printed form is FALSE: `not_lemma12Printed` below, at
  s = 4, t = 0, j = 1, ξ = 4, where q₄'(4) = 50 > 48 = 2 q₃(4). `Lemma12` uses s^{2t+j}.
* Lemmas 15 and 16 are printed for N < x ≤ 2N, while Lemma 10 needs N ≤ x ≤ 2N; the proof
  of Lemma 15 on p. 376 starts "for N ≤ x ≤ 2N", so we state the closed range.
  Lemma 16 uses Lemma 15, so it needs N ≥ 10, which we add.
-/

@[expose] public section

namespace LeanLab.ExceptionalSet.U1539

open Real MeasureTheory Polynomial
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Definitions -/

/-- `e(x) = exp(2πix)`. -/
noncomputable def eC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- The sum of Theorem 2, `Σ_{N ≤ n ≤ 2N} e(α F(n))`. -/
noncomputable def expSumF (γ α : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc N (2 * N), eC (α * F γ n)

/-- The factorial polynomial `q_s(x) = x(x-1)...(x-s+1)`, display (42), p. 371. -/
noncomputable def q (s : ℕ) : ℝ[X] := descPochhammer ℝ s

/-- The polynomials `Q_{s,t}` of Lemma 11, p. 372, given by the recursion its proof derives:
`Q_{0,0} = 1`, and `Q_{s+1,t} = (ξ - s) Q_{s,t} + (γ-1) ξ Q'_{s,t-1} - (t-1) Q_{s,t-1}`,
display (46), with the `t-1` terms absent at `t = 0`, display (48). Our `Q_{0,0} = 1` makes
`Q_{1,0} = ξ` as on p. 372. -/
noncomputable def Q (γ : ℝ) : ℕ → ℕ → ℝ[X]
  | 0, t => if t = 0 then 1 else 0
  | s + 1, t => (X - C (s : ℝ)) * Q γ s t +
      (if t = 0 then 0 else
        C (γ - 1) * X * derivative (Q γ s (t - 1)) - C ((t : ℝ) - 1) * Q γ s (t - 1))

/-- `ξ(x) = γ (log x)^{γ-1}`, p. 372. -/
noncomputable def xi (γ x : ℝ) : ℝ := γ * Real.log x ^ (γ - 1)

/-- The Fourier coefficient `ȟ(n) = ∫_0^1 h(α) e(-αn) dα` of Lemma 1, p. 356. -/
noncomputable def hcheck (h : ℝ → ℂ) (n : ℤ) : ℂ := ∫ α in (0 : ℝ)..1, h α * eC (-(α * n))

/-- The Fourier transform `K̂(α) = ∫ K(β) e(-αβ) dβ` of Lemma 1, p. 356. -/
noncomputable def ftR (K : ℝ → ℂ) (α : ℝ) : ℂ := ∫ β, K β * eC (-(α * β))

/-- `S(α) = Σ_{P < p ≤ X} log p e(αp)`, p. 357. -/
noncomputable def Sp (P X α : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, (Real.log p : ℂ) * eC (α * p)

/-- The major arcs `𝔑`: all real `α` with `|qα - a| ≤ P X⁻¹`, `(a, q) = 1`, `1 ≤ q ≤ P`,
p. 357. -/
def majorArcs (P X : ℝ) : Set ℝ :=
  {α | ∃ q : ℕ, ∃ a : ℤ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ Int.gcd a q = 1 ∧ |q * α - a| ≤ P / X}

/-- `R₁(m) = ∫_{𝔐} S(α)² e(-αm) dα` with `𝔐 = 𝔑 ∩ [0,1]`, display (7), p. 357. -/
noncomputable def R1 (P X : ℝ) (m : ℤ) : ℂ :=
  ∫ α in majorArcs P X ∩ Set.Icc 0 1, Sp P X α ^ 2 * eC (-(α * m))

/-- `ν_n = [F(n)]`, p. 354. -/
noncomputable def nu (γ : ℝ) (n : ℕ) : ℤ := ⌊F γ n⌋

/-- `ν°_n`, the odd one of `ν_n, ν_n + 1`, p. 362. -/
noncomputable def nuOdd (γ : ℝ) (n : ℕ) : ℤ := if Odd (nu γ n) then nu γ n else nu γ n + 1

/-- `ℰ = exp(κ (log N)^{3-2γ})`, p. 359. -/
noncomputable def calE (γ κ : ℝ) (N : ℕ) : ℝ := Real.exp (κ * Real.log N ^ (3 - 2 * γ))

/-- The kernel `K(α)` of display (3), p. 356, with `sinc x = sin x / x`. -/
noncomputable def Kfun (Δ α : ℝ) : ℝ :=
  (1 / Δ) * Real.sinc (Real.pi * α) ^ 2
    - (1 / Δ) * (1 - Δ) ^ 2 * Real.sinc (Real.pi * (1 - Δ) * α) ^ 2

/-- `Φ_e(α) = Σ_{N/2 < n ≤ N, ν_n even} e(αF(n))`, display (36), p. 368. -/
noncomputable def Phie (γ : ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n)), eC (α * F γ n)

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

/-! ### Statements as Props -/

/-- Theorem 2, p. 354: for `1 < γ < 3/2`, `0 < c < 1`, `0 < C < γ - 1` there is `κ > 0`
with `Σ_{N ≤ n ≤ 2N} e(αF(n)) ≪ N exp(-κ (log N)^{3-2γ})` uniformly in
`F(2N)^{-c} ≤ |α| ≤ F(N)^C`. -/
def Theorem2 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ c C : ℝ, 0 < c → c < 1 → 0 < C → C < γ - 1 →
    ∃ κ B : ℝ, 0 < κ ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
      F γ (2 * N) ^ (-c) ≤ |α| → |α| ≤ F γ N ^ C →
      ‖expSumF γ α N‖ ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ))

/-- Lemma 1, p. 355-356: `h` of period 1, integrable on `[0,1]`; `K ∈ L¹` continuous with
`K̂` supported in `[-1,1]`. Then `∫ h K e(-αv) = K̂({v}) ȟ([v]) + K̂({v}-1) ȟ([v]+1)`. -/
def Lemma1 : Prop :=
  ∀ h K : ℝ → ℂ, Function.Periodic h 1 → IntervalIntegrable h volume 0 1 →
    Integrable K → Continuous K → (∀ α : ℝ, 1 < |α| → ftR K α = 0) →
    ∀ v : ℝ, ∫ α, h α * K α * eC (-(α * v)) =
      ftR K (Int.fract v) * hcheck h ⌊v⌋ + ftR K (Int.fract v - 1) * hcheck h (⌊v⌋ + 1)

/-- Lemma 4, p. 359: for `F(N)^{-1/2} < |α| ≤ 1` and `0 ≤ z₂ < z₁ ≤ 1`,
`#{N/2 < n ≤ N : z₂ ≤ {αF(n)} < z₁} = (z₁ - z₂)N/2 + O(N exp(-κ̃ (log N)^{3-2γ}))`. -/
def Lemma4 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ κ B : ℝ, 0 < κ ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
    F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ z₁ z₂ : ℝ, 0 ≤ z₂ → z₂ < z₁ → z₁ ≤ 1 →
      |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
        - (z₁ - z₂) * N / 2| ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ))

/-- Lemma 6, p. 362, with `X = F(N)` and `P = X^{6δ}`: for all but `O(N ℰ^{-1/12})` values of
`n ∈ [N/2, N]`, `R₁(ν°_n) ≪ X ℰ^{-1/8}`. -/
def Lemma6 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∃ κ B : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
          B * F γ N * calE γ κ N ^ (-(1 / 8 : ℝ)) <
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)‖)).card : ℝ)
        ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ))

/-- Lemma 7, p. 362: for small `δ`, for all but `O(N ℰ^{-1/12})` values of `n` with
`X/2 < F(n) ≤ X`, `R₁(ν_n) + R₁(ν_n + 1) ≫ X ℰ^{-1/10}`. `R₁` is real; we bound its real part.
All such `n` are below `2N + 1`, so filtering `range (2N+1)` loses none. -/
def Lemma7 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∃ κ c₀ B : ℝ, 0 < κ ∧ 0 < c₀ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (((Finset.range (2 * N + 1)).filter (fun n : ℕ =>
          F γ N / 2 < F γ n ∧ F γ n ≤ F γ N ∧
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) + R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re
            < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ)
        ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ))

/-- Lemma 8, p. 365: for small `δ` and `Δ = ℰ^{-1/8}`, for all but `O(N ℰ^{-1/12})` values of
`n` with `X/2 < ν_n ≤ X`, `∫_𝔑 S(α)² K(α) e(-αF(n)) dα ≫ X ℰ^{-1/10}`, real part. -/
def Lemma8 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∃ κ c₀ B : ℝ, 0 < κ ∧ 0 < c₀ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (((Finset.range (2 * N + 1)).filter (fun n : ℕ =>
          F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N ∧
          (∫ α in majorArcs (F γ N ^ (6 * δ)) (F γ N),
              Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 * (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)
                * eC (-(α * F γ n))).re
            < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ)
        ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ))

/-- Lemma 9, p. 368: if `|α| ≤ X^δ` and `|Φ_e(α)| > N ℰ^{-1/3}` then some integer `h` has
`|h| ≤ ℰ^{2/3}` and `|α - h/2| ≤ X^{δ-1}`. -/
def Lemma9 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ, |α| ≤ F γ N ^ δ →
      N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖Phie γ N α‖ →
      ∃ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (2 / 3 : ℝ) ∧ |α - h / 2| ≤ F γ N ^ (δ - 1)

/-- Lemma 10, p. 370-371, Karacuba: for `0 < δ < 1` and `0 < Θ < θ < Θ₀ < 1` there are
`B, c > 0` with `|Σ_{N < n ≤ 2N} e(f(n))| ≤ B N^{1 - c/k²}` for every `f` in the class. -/
def Lemma10 : Prop :=
  ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ),
      KClass N θ Θ Θ₀ δ f k →
      ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2)

/-- Lemma 11, p. 372: for `γ > 0` and `s ≥ 1`, `Q_{s,t}` has degree at most `s - t` and no
constant term for `t ≤ s - 1`, `Q_{s,0} = q_s`, `Q_{s+1,s}(ξ) = q_s(γ-1) ξ`, display (45),
and `F^{(s)}(x) = F(x) x^{-s} Σ_{t=0}^{s-1} (log x)^{-t} Q_{s,t}(γ (log x)^{γ-1})` for `x > 1`. -/
def Lemma11 : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ s : ℕ, 1 ≤ s →
    (∀ t < s, (Q γ s t).natDegree ≤ s - t ∧ (Q γ s t).coeff 0 = 0) ∧
    Q γ s 0 = q s ∧ Q γ (s + 1) s = C ((q s).eval (γ - 1)) * X ∧
    ∀ x : ℝ, 1 < x → iteratedDeriv s (F γ) x =
      F γ x / x ^ s * ∑ t ∈ Finset.range s, (Real.log x ^ t)⁻¹ * (Q γ s t).eval (xi γ x)

/-- Lemma 12, p. 373, with `s^{2t+j}` in (50), see the QUESTION in the header:
for `1 < γ < 2`, `0 ≤ t ≤ s-1`, `t + j ≤ s`, `ξ ≥ s`: `|Q_{s,t}^{(j)}(ξ)| ≤ s^{2t+j} q_{s-t-j}(ξ)`,
and `Q_{s,t}^{(s-t+1)} = 0`, display (51). -/
def Lemma12 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 2 → ∀ s t j : ℕ, t < s → t + j ≤ s →
    derivative^[s - t + 1] (Q γ s t) = 0 ∧
    ∀ ξ : ℝ, (s : ℝ) ≤ ξ →
      |(derivative^[j] (Q γ s t)).eval ξ| ≤ (s : ℝ) ^ (2 * t + j) * (q (s - t - j)).eval ξ

/-- Display (50) exactly as printed, with `2^{2t+j}`. It is false, see `not_lemma12Printed`. -/
def Lemma12Printed : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 2 → ∀ s t j : ℕ, t < s → t + j ≤ s → ∀ ξ : ℝ, (s : ℝ) ≤ ξ →
    |(derivative^[j] (Q γ s t)).eval ξ| ≤ (2 : ℝ) ^ (2 * t + j) * (q (s - t - j)).eval ξ

/-- Lemma 13, p. 375: for `1 < γ < 2`, `s ≥ 1`, `F^{(s)}(x) = F(x) x^{-s} (q_s(ξ) + E(x))` where,
for `ξ ≥ s` and `s² ≤ (log x)/2`, `|E(x)| ≤ 2s² (log x)^{-1} q_{s-1}(ξ)`. -/
def Lemma13 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 2 → ∀ s : ℕ, 1 ≤ s → ∀ x : ℝ, 1 < x →
    (s : ℝ) ≤ xi γ x → (s : ℝ) ^ 2 ≤ Real.log x / 2 →
    |iteratedDeriv s (F γ) x * x ^ s / F γ x - (q s).eval (xi γ x)| ≤
      2 * (s : ℝ) ^ 2 / Real.log x * (q (s - 1)).eval (xi γ x)

/-- Lemma 14, p. 375: for `1 < γ < 3/2` there is `x₀` such that `F^{(s)}(x)/s! ≥ F(x)/(2x^s)`
for all `s` and all `x ≥ x₀` with `γ (log x)^{γ-1} ≥ s`. -/
def Lemma14 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ x₀ : ℝ, ∀ s : ℕ, ∀ x : ℝ, x₀ ≤ x → (s : ℝ) ≤ xi γ x →
    F γ x / (2 * x ^ s) ≤ iteratedDeriv s (F γ) x / s.factorial

/-- Lemma 15, p. 375, on the closed range `N ≤ x ≤ 2N` of its proof: for `γ > 1`, `N ≥ 10`,
`|F^{(s)}(x)/s!| ≤ 2 (2/N)^s F(3N)`. -/
def Lemma15 : Prop :=
  ∀ γ : ℝ, 1 < γ → ∀ N : ℝ, 10 ≤ N → ∀ s : ℕ, ∀ x : ℝ, N ≤ x → x ≤ 2 * N →
    |iteratedDeriv s (F γ) x / s.factorial| ≤ 2 * (2 / N) ^ s * F γ (3 * N)

/-- Lemma 16 (a), p. 376, with `N ≥ 10` from Lemma 15 and the closed range: `α = N^{-A} > 0`,
`0 < ϑ < 1`, and `s(1-ϑ) + A ≥ ((s+1) log 2)/log N + (log 3N)^γ/log N`, display (53), give
`|αF^{(s)}(x)/s!| ≤ N^{-ϑs}` on `[N, 2N]`. -/
def Lemma16a : Prop :=
  ∀ γ : ℝ, 1 < γ → ∀ N : ℝ, 10 ≤ N → ∀ α ϑ A : ℝ, 0 < α → 0 < ϑ → ϑ < 1 → α = N ^ (-A) →
    ∀ s : ℕ, ((s : ℝ) + 1) * Real.log 2 / Real.log N + Real.log (3 * N) ^ γ / Real.log N
        ≤ s * (1 - ϑ) + A →
    ∀ x : ℝ, N ≤ x → x ≤ 2 * N →
      |α * iteratedDeriv s (F γ) x / s.factorial| ≤ N ^ (-(ϑ * s))

/-- Lemma 16 (b), p. 376, closed range, `N` large as Lemma 14 needs: `s ≤ γ (log N)^{γ-1}` and
`s(1-ϑ) + A ≤ (log N)^{γ-1} - log 2/log N`, display (54), give `|αF^{(s)}(x)/s!| ≥ N^{-ϑs}`. -/
def Lemma16b : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ N₁ : ℝ, ∀ N : ℝ, N₁ ≤ N →
    ∀ α ϑ A : ℝ, 0 < α → 0 < ϑ → ϑ < 1 → α = N ^ (-A) →
    ∀ s : ℕ, (s : ℝ) ≤ xi γ N →
      s * (1 - ϑ) + A ≤ Real.log N ^ (γ - 1) - Real.log 2 / Real.log N →
    ∀ x : ℝ, N ≤ x → x ≤ 2 * N →
      N ^ (-(ϑ * s)) ≤ |α * iteratedDeriv s (F γ) x / s.factorial|

/-! ### Proved facts: the printed (50) fails, and vacuity instances -/

theorem Q_succ_zero (γ : ℝ) (s : ℕ) : Q γ (s + 1) 0 = (X - C (s : ℝ)) * Q γ s 0 := by
  simp [Q]

/-- The printed display (50) fails at `s = 4, t = 0, j = 1, ξ = 4`: `Q_{4,0} = q₄` and
`q₄'(4) = 50 > 48 = 2^1 q₃(4)`. -/
theorem not_lemma12Printed : ¬ Lemma12Printed := by
  intro h
  have := h (3 / 2) (by norm_num) (by norm_num) 4 0 1 (by norm_num) (by norm_num) 4 le_rfl
  simp only [Q, Function.iterate_one, q] at this
  norm_num [descPochhammer_succ_right, derivative_mul] at this

/-- Vacuity for `Theorem2`: its hypotheses hold at `γ = 5/4, c = 1/2, C = 1/8, N = 1, α = 1`. -/
theorem vacuity_theorem2 :
    ∃ γ c C : ℝ, 1 < γ ∧ γ < 3 / 2 ∧ 0 < c ∧ c < 1 ∧ 0 < C ∧ C < γ - 1 ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∃ α : ℝ, F γ (2 * N) ^ (-c) ≤ |α| ∧ |α| ≤ F γ N ^ C := by
  refine ⟨5 / 4, 1 / 2, 1 / 8, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, 1, le_rfl, 1, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ F (5 / 4) (2 * ((1 : ℕ) : ℝ)) := by
      unfold F
      exact Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _)
    simpa using Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
  · have h1 : F (5 / 4) (1 : ℝ) = 1 := by
      simp [F, Real.zero_rpow (by norm_num : (5 / 4 : ℝ) ≠ 0)]
    rw [Nat.cast_one, h1]
    simp

/-- Vacuity for `KClass`: `f = id` is in `𝓕(1, 1/2, 1/4, 3/4, 1/4)` with `k = 3`, `S = {1}`. -/
theorem vacuity_KClass : KClass 1 (1 / 2) (1 / 4) (3 / 4) (1 / 4) id 3 := by
  have h1 : iteratedDeriv 1 (id : ℝ → ℝ) = fun _ => 1 := by
    rw [iteratedDeriv_one]; funext x; simp
  have h3 : iteratedDeriv 3 (id : ℝ → ℝ) = fun _ => 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
    funext x; simp
  refine ⟨le_rfl, ⟨Set.univ, isOpen_univ, Set.subset_univ _, contDiff_id.contDiffOn⟩, ?_, ?_⟩
  · intro x _; simp [h3]
  · refine ⟨{1}, by decide, by norm_num, ?_⟩
    intro s hs x _
    simp only [Finset.mem_singleton] at hs
    subst hs
    simp [h1]

/-- Vacuity for `Lemma4`: at `N = 2` the range `F(N)^{-1/2} < |α| ≤ 1` contains `α = 1`. -/
theorem vacuity_lemma4 : F (5 / 4) ((2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
  have h1 : (1 : ℝ) < F (5 / 4) ((2 : ℕ) : ℝ) := by
    unfold F
    have hp : 0 < Real.log ((2 : ℕ) : ℝ) ^ (5 / 4 : ℝ) :=
      Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
    have := Real.add_one_lt_exp hp.ne'
    linarith
  simpa using Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num)

/-- Vacuity for the major arcs of Lemmas 6 to 8: `0 ∈ 𝔑` when `P ≥ 1` and `X > 0`. -/
theorem vacuity_majorArcs {P X : ℝ} (hP : 1 ≤ P) (hX : 0 < X) : (0 : ℝ) ∈ majorArcs P X :=
  ⟨1, 0, le_rfl, by simpa using hP, by simp, by simp; positivity⟩

/-- Vacuity for `Lemma13`: at `γ = 5/4`, `s = 1`, `x = e²` the hypotheses
`ξ ≥ s` and `s² ≤ (log x)/2` hold. -/
theorem vacuity_lemma13 :
    (1 : ℝ) ≤ xi (5 / 4) (Real.exp 2) ∧ ((1 : ℕ) : ℝ) ^ 2 ≤ Real.log (Real.exp 2) / 2 := by
  refine ⟨?_, by simp⟩
  unfold xi
  rw [Real.log_exp]
  have : (1 : ℝ) ≤ (2 : ℝ) ^ ((5 / 4 : ℝ) - 1) := Real.one_le_rpow (by norm_num) (by norm_num)
  nlinarith

/-- Vacuity for `Lemma16a`: display (53) holds for `s = 0` and `A` large, at `N = 10`. -/
theorem vacuity_lemma16a (γ : ℝ) : ∃ A : ℝ, 0 < (10 : ℝ) ^ (-A) ∧
    (((0 : ℕ) : ℝ) + 1) * Real.log 2 / Real.log 10 + Real.log (3 * 10) ^ γ / Real.log 10
      ≤ ((0 : ℕ) : ℝ) * (1 - 1 / 2) + A :=
  ⟨(((0 : ℕ) : ℝ) + 1) * Real.log 2 / Real.log 10 + Real.log (3 * 10) ^ γ / Real.log 10,
    Real.rpow_pos_of_pos (by norm_num) _, by simp⟩

/-- Vacuity for `Lemma16b`: display (54) holds for `s = 0` and suitable `A`, at any `N > 0`. -/
theorem vacuity_lemma16b (γ N : ℝ) (hN : 0 < N) : ∃ A : ℝ, 0 < N ^ (-A) ∧
    ((0 : ℕ) : ℝ) * (1 - 1 / 2) + A ≤ Real.log N ^ (γ - 1) - Real.log 2 / Real.log N :=
  ⟨Real.log N ^ (γ - 1) - Real.log 2 / Real.log N, Real.rpow_pos_of_pos hN _, by simp⟩

end LeanLab.ExceptionalSet.U1539
