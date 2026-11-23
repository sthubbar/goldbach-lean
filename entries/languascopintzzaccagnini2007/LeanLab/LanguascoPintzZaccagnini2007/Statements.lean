module

public import Mathlib

/-!
P0045 A. Languasco, J. Pintz, A. Zaccagnini, "On the sum of two primes and k powers of two",
last preprint of Bull. London Math. Soc. 39 (2007) 771-780, read 2026-10-18 from papers/P0045.pdf,
pages 1 to 10, the Theorem on page 2 checked on the rendered page image.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. The Theorem is an almost-all result for two primes and k powers of 2.

Readings. `X` is a natural number, `L = log_2 X` as in the paper, powers of two run over
`ν ∈ [1, ⌊L⌋]`. `R''_k(N)` is the Λ-weighted count of page 2. `(log X)^10` is the natural logarithm,
the base only changes the implied constant. `C(k, N)` is the series (23) of page 8; the paper's proof
makes it, and the implied constant, independent of η, so the Theorem is read with `∃ C K` before `∀ η`.
`ξ(d) = min {μ ≥ 1 : 2^μ ≡ 1 mod d}` for odd `d`, page 7 (μ ≥ 1 so that ξ(1) = 1).
-/

@[expose] public section

namespace LeanLab.LPZ2007
open Finset Real
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `L = log_2 X`, page 1. -/
def Lg (X : ℕ) : ℝ := Real.logb 2 X

/-- The range `[1, L]` of the exponents, as natural numbers. -/
def Lp (X : ℕ) : ℕ := ⌊Lg X⌋₊

/-- `R''_k(N) = ∑ Λ(m₁) Λ(m₂)` over `m₁, m₂ ≤ X`, `ν ∈ [1, L]^k`, `m₁ + m₂ + 2^{ν₁} + … + 2^{ν_k} = N`,
page 2. -/
def Rpp (k X N : ℕ) : ℝ :=
  ∑ m₁ ∈ range (X + 1), ∑ m₂ ∈ range (X + 1),
    ∑ ν ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 (Lp X)),
      if m₁ + m₂ + ∑ i, 2 ^ ν i = N then Λ m₁ * Λ m₂ else 0

/-- The exceptional even `N ∈ [1, X]` for a main term `C N * N * L^k` and tolerance `η`. -/
def Exc (k X : ℕ) (C : ℕ → ℝ) (η : ℝ) : Finset ℕ :=
  (Icc 1 X).filter (fun N => Even N ∧ η * N * Lg X ^ k < |Rpp k X N - C N * N * Lg X ^ k|)

/-- The Theorem, page 2: `k ≥ 1`; there is `C(k, N) ∈ [1, 2]` and `K` such that for every `η > 0` and
`X ≥ X₀(k, η)` all even `N ∈ [1, X]` satisfy `|R''_k(N) - C(k, N) N L^k| ≤ η N L^k` apart from at most
`K X^{3/5} (log X)^10` exceptions. -/
def MainTheorem : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ → ℝ, (∀ N, Even N → 1 ≤ C N ∧ C N ≤ 2) ∧ ∃ K : ℝ, ∀ η : ℝ, 0 < η →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ((Exc k X C η).card : ℝ) ≤ K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10

/-- `ξ(d) = min {μ ≥ 1 : 2^μ ≡ 1 mod d}`, page 7. -/
def xi (d : ℕ) : ℕ := sInf {μ : ℕ | 1 ≤ μ ∧ 2 ^ μ ≡ 1 [MOD d]}

/-- `f(d) = ∏_{p | d, p > 2} (p - 2)^{-1}`, page 8. -/
def fd (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors.filter (fun p => 2 < p), 1 / ((p : ℝ) - 2)

/-- Odd squarefree positive integers, the `Σ'` of the paper. -/
def OddSqf (d : ℕ) : Prop := 0 < d ∧ Odd d ∧ Squarefree d

/-- The series (26), page 9, as a function on odd squarefree `d`. -/
def seriesTerm (d : ℕ) : ℝ := if OddSqf d then fd d / xi d else 0

/-- Lemma 6.1, page 9, after Romanov: the series (26) converges. Cited. -/
def Lemma61 : Prop := Summable seriesTerm

/-- Page 9: the value of (26) is at most `1.9378`, Corollary 1 of Khalfallah and Pintz. Cited. -/
def Lemma61Bound : Prop := ∑' d, seriesTerm d ≤ 1.9378

/-- `𝔖(n) = ∏_{p ∤ n} (1 - 1/(p-1)²) ∏_{p | n} p/(p-1)`, page 2, as one product over all primes. -/
def Sing (n : ℕ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime},
    if p.1 ∣ n then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2

/-- `A(m, r) = ∑_{ν ∈ [1, L'], 2^ν < m, r | m - 2^ν} 𝔖(m - 2^ν)`, `L' = L - √L`, (13) page 7. -/
def Amr (X m r : ℕ) : ℝ :=
  ∑ ν ∈ (Icc 1 ⌊Lg X - Real.sqrt (Lg X)⌋₊).filter (fun ν => 2 ^ ν < m ∧ r ∣ m - 2 ^ ν),
    Sing (m - 2 ^ ν)

/-- Lemma 6.2, page 9, in the form its proof gives and Section 4 uses with `r ≫ L²`: for `ε > 0`
there are `r₀, X₀` with `A(m, r) ≤ ε L` for `X ≥ X₀`, `m ∈ [X/2, X]` and odd `r ≥ r₀`. As printed,
with no lower bound on `r`, it is false at `r = 1`: VERIFY U-0999, run 20261019T0202Z-9877,
since every term is at least `2c0`; `r₀` added then. Its proof on pages 9 to 10 is cited. -/
def Lemma62 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r₀ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ m r : ℕ, (X : ℝ) / 2 ≤ m → m ≤ X →
    0 < r → Odd r → r₀ ≤ r → Amr X m r ≤ ε * Lg X

/- The Theorem of page 2 AS PRINTED is NOT cited any more: VERIFY U-0999, run 20261019T0202Z-9877,
found `MainTheorem` false twice, on all of `[1, X]` with `L = log_2 X`, QUESTION Q1 of the PC
LPZ2007 folder, and through F-0038, the true constant `2c0 C(k, N)` exceeds 2 on a positive share
of `N`. An open proof of it made the module inconsistent. The repaired, cited form is
`lpz_main_J_twoC0` in LeanLab/LPZ2007/Repaired.lean, PC folder.
The old cited line for it was removed. -/

/- Lemma 6.1, Romanov. RETIRED 2026-10-19 by AUDIT U-1082, PC run 20261019T1603Z-20267: PROVED as
`lemma61_proved : Lemma61` in Lemma61.lean, no cited input, which imports this file, so the proof
cannot sit here. Nothing used the cited form. The old cited line was removed. -/


/- Lemma 6.2 in the repaired form `Lemma62`. RETIRED 2026-10-19 by AUDIT U-1082, PC run
20261019T1603Z-20267: PROVED as `lemma62_proved : Lemma62` in Lemma62.lean, no cited input. Nothing
used the cited form. The old cited line was removed. -/

end

end LeanLab.LPZ2007

