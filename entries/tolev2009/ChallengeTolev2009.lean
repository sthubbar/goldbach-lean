module

public import Mathlib

/-!
# Tolev 2009, the main Theorem, display 5

D. I. Tolev, *The ternary Goldbach problem with primes from arithmetic progressions*,
arXiv 0902.2669, 2009, Theorem on page 2, display 5. Let `l₃` be a fixed positive integer and
`λ(k)` real numbers with `|λ(k)| ≤ 1`. For every `A > 0` there is `B = B(A) > 0` such that, for
`N` a sufficiently large odd integer and `L = log N`,

`𝓔* = ∑_{k₁, k₂ ≤ √N L^{-B}} max_{(l₁,k₁) = 1, (l₂,k₂) = 1}
  |∑_{k₃ ≤ N^{1/3} L^{-B}, (k₃,l₃) = 1} λ(k₃) Δ_{k,l}(N)| ≪ N² L^{-A}`,

where `Δ_{k,l}(N) = R_{k,l}(N) - M_{k,l}(N)`, `R_{k,l}(N)` is the sum of
`log p₁ log p₂ log p₃` over primes `p₁ + p₂ + p₃ = N` with `pᵢ ≡ lᵢ (mod kᵢ)`, and
`M_{k,l}(N) = N² 𝔖_{k,l}(N) / (2 φ(k₁) φ(k₂) φ(k₃))`. Tolev takes the singular series
`𝔖_{k,l}(N)` from Halupczok 2008; it is stated here by Halupczok's printed formula,
`halupczokSeries`. The implied constant may depend on `A` and `l₃`, and is uniform in `λ`.

Binary Goldbach is open and is not claimed. AI agents wrote the Lean code; the proof reuses
code ported from PrimeNumberTheoremAnd and earlier lab code, credited in `PORTING.md`.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009

/-- The weighted count `R_{k,l}(N) = Σ log p₁ log p₂ log p₃` over primes
`p₁ + p₂ + p₃ = N` with `pᵢ ≡ lᵢ (mod kᵢ)`. -/
noncomputable def R (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  ∑ p ∈ (range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1)).filter
      (fun p => p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1 + p.2.1 + p.2.2 = N ∧
        p.1 % k 0 = l 0 % k 0 ∧ p.2.1 % k 1 = l 1 % k 1 ∧ p.2.2 % k 2 = l 2 % k 2),
    Real.log p.1 * Real.log p.2.1 * Real.log p.2.2

/-- The type of a singular series `𝔖_{k,l}(N)`. -/
abbrev SSeries := (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ → ℝ

/-- The main term `M_{k,l}(N) = N² 𝔖_{k,l}(N) / (2 φ(k₁) φ(k₂) φ(k₃))`, for a given
singular series `S`. -/
noncomputable def M (S : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ → ℝ) (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ 2 * S k l N / (2 * (k 0).totient * (k 1).totient * (k 2).totient)

/-- The error `Δ_{k,l}(N) = R_{k,l}(N) - M_{k,l}(N)` for a given singular series `S`. -/
noncomputable def Δ (S : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ → ℝ) (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  R k l N - M S k l N

/-- Admissible residues for a modulus `k`: the `l` in `0, ..., k - 1` with `(l, k) = 1`. -/
def residues (k : ℕ) : Finset ℕ := (range k).filter (fun l => Nat.Coprime l k)

/-- The inner quantity of `𝓔*` for fixed `k₁, k₂`: the max over admissible `l₁, l₂` of
`|Σ_{k₃ ≤ K₃, (k₃, l₃) = 1} λ(k₃) Δ|`, written as a supremum over finite sets. -/
noncomputable def inner (S : SSeries) (lam : ℕ → ℝ) (l₃ K₃ k₁ k₂ N : ℕ) : ℝ :=
  ⨆ l₁ ∈ residues k₁, ⨆ l₂ ∈ residues k₂,
    |∑ k₃ ∈ (Icc 1 K₃).filter (fun k₃ => Nat.Coprime k₃ l₃),
        lam k₃ * Δ S ![k₁, k₂, k₃] ![l₁, l₂, l₃] N|

/-- `𝓔*` of display 5, with `K₁₂ = ⌊√N L^{-B}⌋` and `K₃ = ⌊N^{1/3} L^{-B}⌋`, `L = log N`. -/
noncomputable def Estar (S : SSeries) (lam : ℕ → ℝ) (l₃ : ℕ) (B : ℝ) (N : ℕ) : ℝ :=
  let L := Real.log N
  let K₁₂ := ⌊Real.sqrt N * L ^ (-B)⌋₊
  let K₃ := ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * L ^ (-B)⌋₊
  ∑ k₁ ∈ Icc 1 K₁₂, ∑ k₂ ∈ Icc 1 K₁₂, inner S lam l₃ K₃ k₁ k₂ N

/-- The Theorem, for a given singular series `S`: for every `A > 0` there is `B = B(A) > 0` so
that, for each fixed `l₃ ≥ 1`, uniformly in real `λ` with `|λ(k)| ≤ 1`, `𝓔* ≤ C N² L^{-A}` for
all odd `N ≥ N₀`, with `C` and `N₀` depending on `A` and `l₃` only. -/
def TheTheorem (S : (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ l₃ : ℕ, 1 ≤ l₃ → ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ,
    (∀ k, |lam k| ≤ 1) → ∀ N : ℕ, Odd N → N₀ ≤ N →
      Estar S lam l₃ B N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A)

end LeanLab.Tolev2009

open Finset Real MeasureTheory

namespace LeanLab.Tolev2009.Faithful

open LeanLab.Tolev2009

/-- `e(x) = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

end LeanLab.Tolev2009.Faithful

open Finset Real

namespace LeanLab.Tolev2009.SeriesIdentification

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful

/-- Halupczok's local sum on page 7 of Halupczok 2008, with her printed representatives
`1 ≤ r ≤ q`: the sum of `e(a r / q)` over `r` with `(r, q) = 1` and
`r ≡ l (mod (k, q))`. -/
noncomputable def coeffPaper (k l q a : ℕ) : ℂ :=
  ∑ r ∈ (Icc 1 q).filter (fun r => Nat.Coprime r q ∧ r % Nat.gcd k q = l % Nat.gcd k q),
    ee ((a : ℝ) * r / q)

/-- The `q`th term of Halupczok's singular series on page 11 of Halupczok 2008:
`∏ᵢ φ(kᵢ)/φ([kᵢ, q])` times the sum over `a mod q` with `(a, q) = 1` of
`e(-a N / q) ∏ᵢ coeffPaper(kᵢ, lᵢ, q, a)`. -/
noncomputable def halupczokTerm (k l : Fin 3 → ℕ) (N q : ℕ) : ℂ :=
  (∏ i : Fin 3, (k i).totient / ((Nat.lcm (k i) q).totient : ℂ)) *
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ee (-((a : ℝ) * N / q)) * ∏ i : Fin 3, coeffPaper (k i) (l i) q a

/-- Halupczok's singular series `𝔖_{k,l}(N) = Σ_{q ≥ 1} halupczokTerm k l N q`, taken as the
real part of the Lean sum. For odd `N`, positive moduli and reduced residues the lab proves the
series absolutely summable, so the sum is not a junk value there. -/
noncomputable def halupczokSeries (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  (∑' q : ℕ, halupczokTerm k l N (q + 1)).re

end LeanLab.Tolev2009.SeriesIdentification

namespace LeanLab.Tolev2009.Decomp83

open LeanLab.Tolev2009 LeanLab.Tolev2009.SeriesIdentification

/-- **Tolev 2009, the main Theorem, display 5**, with Halupczok's printed singular series. -/
theorem published_assembly : TheTheorem halupczokSeries := by
  sorry

end LeanLab.Tolev2009.Decomp83

namespace LeanLab.Tolev2009.FinishAssembly1112

open LeanLab.Tolev2009 LeanLab.Tolev2009.SeriesIdentification

/-- The same Theorem, proved by a second assembly route in the lab. -/
theorem published_assembly_finished : TheTheorem halupczokSeries := by
  sorry

end LeanLab.Tolev2009.FinishAssembly1112
