module

public import Mathlib

/-!
# Song 2020, Theorem 1, from Pan and Pan's Lemma 3

Yanbo Song, The ternary Goldbach-Vinogradov theorem with almost equal Piatetski-Shapiro
primes, arXiv 2012.06322 v1, 2020. Theorem 1: for `44/45 < γ < 1` every large enough odd `n`
is `p₁ + p₂ + p₃` with each `pᵢ` a Piatetski-Shapiro prime `[m^{1/γ}]` and `|pᵢ - n/3| ≤ y`,
for every `y > n^{(52 - 45γ)/8}`. The proof in Section 4, page 9, rests on the asymptotic
formula `R(n) = 𝔖₃(n) 3y²/log³ n + O(y²/log⁴ n)`.

The one cited input is the paper's Lemma 3, Theorem 3 of C. D. Pan and C. B. Pan, Goldbach
Conjecture, Science Press, Beijing, 1988, taken at the exponent `7/8` as the explicit
hypothesis `Lemma3 (7 / 8)`, never as an axiom.

* `songWindow_margin_of_lemma3`: Theorem 1 for every window `y > n^{(52 - 45γ)/8 + δ}` with
  `δ > 0`, from `Lemma3 (7 / 8)` alone.
* `asymptotic_margin_of_lemma3`: the asymptotic formula of page 9 on the same windows, from
  `Lemma3 (7 / 8)` alone.
* `songTheorem1_of_lemma3_logTransfer`: Theorem 1 at the exact window, from `Lemma3 (7 / 8)`
  and the transfer step `LogTransferDQ` of page 9 at the exact threshold, a second hypothesis.

Every definition below repeats the definition of the same name in the solution, with the
same `open` lines and local instances. Binary Goldbach is open and is not claimed here.
AI agents wrote the Lean code, see `PORTING.md`.
-/

@[expose] public section

namespace LeanLab.Song2020

/-- Piatetski-Shapiro prime for `γ`: a prime `p` with `p = [m^{1/γ}]` for some `m ≥ 1`. -/
def IsPSPrime (γ : ℝ) (p : ℕ) : Prop :=
  p.Prime ∧ ∃ m : ℕ, 1 ≤ m ∧ (p : ℤ) = ⌊(m : ℝ) ^ (1 / γ)⌋

/-- `n` is a sum of three Piatetski-Shapiro primes for `γ`, each within `y` of `n/3`. -/
def IsAlmostEqualPSTernary (γ : ℝ) (n : ℕ) (y : ℝ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, IsPSPrime γ p₁ ∧ IsPSPrime γ p₂ ∧ IsPSPrime γ p₃ ∧ p₁ + p₂ + p₃ = n ∧
    |(p₁ : ℝ) - n / 3| ≤ y ∧ |(p₂ : ℝ) - n / 3| ≤ y ∧ |(p₃ : ℝ) - n / 3| ≤ y

/-- For every large enough odd `n`, every `y > n^θ` admits a representation. -/
def SongWindow (γ θ : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n → ∀ y : ℝ, (n : ℝ) ^ θ < y →
    IsAlmostEqualPSTernary γ n y

/-- The paper's window exponent `(52 − 45γ)/8`. -/
noncomputable def songExponent (γ : ℝ) : ℝ := (52 - 45 * γ) / 8

/-- Song 2020, Theorem 1. -/
def SongTheorem1 : Prop :=
  ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → SongWindow γ (songExponent γ)

end LeanLab.Song2020

namespace LeanLab.Song2020.State1562

open LeanLab.Song2020
open scoped Classical

noncomputable section

/-- `e(x) = exp(2πix)`. -/
def eC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- The primes `p` with `|p - n/3| < y`. -/
def windowPrimes (n : ℕ) (y : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun p => p.Prime ∧ |(p : ℝ) - (n : ℝ) / 3| < y)

/-- The Piatetski-Shapiro weight `(1/γ) p^{1-γ}`. -/
def psWeight (γ : ℝ) (p : ℕ) : ℝ := (1 / γ) * (p : ℝ) ^ (1 - γ)

/-- `f(α) = Σ_{|p-n/3|<y, p ∈ A_{1/γ}} (1/γ) p^{1-γ} e(αp)`. -/
def fS (γ : ℝ) (n : ℕ) (y α : ℝ) : ℂ :=
  ∑ p ∈ (windowPrimes n y).filter (fun p => IsPSPrime γ p),
    (psWeight γ p : ℂ) * eC (α * p)

/-- `g(α) = Σ_{|p-n/3|<y} e(αp)`. -/
def gS (n : ℕ) (y α : ℝ) : ℂ :=
  ∑ p ∈ windowPrimes n y, eC (α * p)

/-- The local factor of `𝔖₃(n)` at a prime `p`. -/
def singFactor (n p : ℕ) : ℝ :=
  if p ∣ n then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3

/-- `𝔖₃(n) = Π_{p|n} (1 - 1/(p-1)²) Π_{p∤n} (1 + 1/(p-1)³)`. -/
def singular3 (n : ℕ) : ℝ := ∏' p : Nat.Primes, singFactor n p

/-- The main term `𝔖₃(n) · 3y² / log³ n`. -/
def mainTerm (n : ℕ) (y : ℝ) : ℝ := singular3 n * (3 * y ^ 2 / Real.log n ^ 3)

/-- `R(n) = ∫₀¹ f(α)³ e(-nα) dα`, the weighted count of Section 4. -/
def RS (γ : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, fS γ n y α ^ 3 * eC (-(n * α))

/-- `∫₀¹ g(α)³ e(-nα) dα`. -/
def gCube (n : ℕ) (y : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, gS n y α ^ 3 * eC (-(n * α))

/-- Lemma 3 of the paper, Theorem 3 of Pan and Pan 1988, for windows `y ≥ n^θ`:
`∫₀¹ g³ e(-nα) = 𝔖₃(n) 3y²/log³ n + O(y²/log⁴ n)`, restricted to odd `n` and `y ≤ n/3`. -/
def Lemma3 (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n → ∀ y : ℝ, (n : ℝ) ^ θ ≤ y → y ≤ (n : ℝ) / 3 →
    ‖gCube n y - (mainTerm n y : ℂ)‖ ≤ C * (y ^ 2 / Real.log n ^ 4)

end

end LeanLab.Song2020.State1562

namespace LeanLab.Song2020.Flag1734

open LeanLab.Song2020 LeanLab.Song2020.State1562

noncomputable section

/-- The transfer step of page 9 at the exact threshold, a hypothesis: for
`y > n^{(52 - 45γ)/8}` some bound `D` on `|f(α) - g(α)|` for every `α` has
`2 D (∫₀¹ |f|² + ∫₀¹ |g|²) ≤ C y² / log⁴ n`. -/
def LogTransferDQ : Prop :=
  ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
      ∃ D : ℝ, 0 ≤ D ∧ (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) ∧
        2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
          (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
            C * (y ^ 2 / Real.log (n : ℝ) ^ 4)

end

end LeanLab.Song2020.Flag1734

namespace LeanLab.Song2020.Palomar1122Song

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Song 2020, Theorem 1 with any positive window margin `δ`: for `44/45 < γ < 1` every large
enough odd `n` is a sum of three Piatetski-Shapiro primes within `y` of `n/3` for every
`y > n^{(52 - 45γ)/8 + δ}`, from the paper's Lemma 3 at exponent `7/8`. -/
theorem songWindow_margin_of_lemma3 (H3 : Lemma3 (7 / 8))
    (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (δ : ℝ) (hδ : 0 < δ)
    (hθ : songExponent γ + δ < 1) : SongWindow γ (songExponent γ + δ) := by
  sorry

/-- Song 2020, the asymptotic formula of page 9 for `R(n)` on windows
`n^{(52 - 45γ)/8 + δ} ≤ y ≤ n/3` with `δ > 0`, from the paper's Lemma 3 at exponent `7/8`. -/
theorem asymptotic_margin_of_lemma3 (H3 : Lemma3 (7 / 8))
    (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ (songExponent γ + δ) ≤ y → y ≤ (n : ℝ) / 3 →
      ‖RS γ n y - (mainTerm n y : ℂ)‖ ≤ C * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by
  sorry

/-- Song 2020, Theorem 1 at the exact window `y > n^{(52 - 45γ)/8}`, from the paper's Lemma 3
at exponent `7/8` and the transfer step `LogTransferDQ` of page 9 as a second hypothesis. -/
theorem songTheorem1_of_lemma3_logTransfer (H3 : Lemma3 (7 / 8))
    (HL : Flag1734.LogTransferDQ) : SongTheorem1 := by
  sorry

end

end LeanLab.Song2020.Palomar1122Song
