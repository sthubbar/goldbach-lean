module

public import Mathlib

/-!
# Sums of two primes and k powers of two, after Languasco, Pintz and Zaccagnini 2007

A. Languasco, J. Pintz and A. Zaccagnini, *On the sum of two primes and k powers of two*,
Bull. London Math. Soc. 39 (2007) 771 to 780. For `k ≥ 1` the paper studies
`R''_k(N)`, the weighted number of representations `N = m₁ + m₂ + 2^{ν₁} + … + 2^{ν_k}` with
`Λ(m₁) Λ(m₂)` weights, `m₁, m₂ ≤ X` and `ν_i ∈ [1, L]`, `L = log₂ X`, and proves that
`R''_k(N)` is asymptotic to its main term for all but `O(X^{3/5} (log X)^{10})` even `N ≤ X`.

The main term printed in the paper's Theorem is `C(k, N) N L^k` with `C(k, N) ∈ [1, 2]`. In the form
proved here the coefficient is `2 c₀ C(k, N)`, `c₀` the twin prime constant, which is the factor
that display 2 of the paper supplies; and the range of `N` is the even numbers of
`J(X) = [2X/3, X]`. This is `RepairedMainJ131`. Corollary 4.2 of the paper, the major arc
asymptotic for the binary integral with a bounded set of exceptional moduli, is
`Cor42OnWindow131 evenJ131`. The consequence for prime representations that the abstract states,
that all but `O(X^{3/5} (log X)^{10})` even `N ≤ X` are sums of two primes and `k` powers of two,
is `global_primes_of_three_inputs`; the paper has no numbered corollary for it, and it follows
from the main theorem on `J(X)` by the dyadic covering of `[1, X]` that the paper's remark after
the Theorem describes.

All three are proved from three results of the literature that the paper cites, each taken as an
explicit hypothesis, never as an axiom:
* `Lemma41Statement481`: Lemma 4.1 of the paper, quoted there from Pintz, ELAZ 2004, Theorem 10,
  the explicit formula for the major arc integral;
* `JutilaTheorem18_481`: Jutila 1977, Theorem 1, display 1.8, the zero density bound for
  primitive characters;
* `IwaniecTheorem2_1123`: Iwaniec 1974, Theorem 2, page 97, the zero free region, read for
  nonreal characters.
The real zero bound of Pintz 1976 and Goldfeld and Schinzel 1975, which the paper also cites, is
proved in the solution from Siegel's theorem, so it is not a hypothesis. Binary Goldbach is open
and is not claimed.
-/

@[expose] public section

namespace LeanLab.LPZ2007
open Finset Real
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `L = log₂ X`, journal page 771. -/
def Lg (X : ℕ) : ℝ := Real.logb 2 X

/-- The range `[1, L]` of the exponents `ν_i`, as natural numbers. -/
def Lp (X : ℕ) : ℕ := ⌊Lg X⌋₊

/-- `R''_k(N) = ∑ Λ(m₁) Λ(m₂)` over `m₁, m₂ ≤ X`, `ν ∈ [1, L]^k`,
`m₁ + m₂ + 2^{ν₁} + … + 2^{ν_k} = N`, journal page 772. -/
def Rpp (k X N : ℕ) : ℝ :=
  ∑ m₁ ∈ range (X + 1), ∑ m₂ ∈ range (X + 1),
    ∑ ν ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 (Lp X)),
      if m₁ + m₂ + ∑ i, 2 ^ ν i = N then Λ m₁ * Λ m₂ else 0

/-- `ξ(d) = min {μ ≥ 1 : 2^μ ≡ 1 mod d}`, the order of 2 modulo odd `d`. -/
def xi (d : ℕ) : ℕ := sInf {μ : ℕ | 1 ≤ μ ∧ 2 ^ μ ≡ 1 [MOD d]}

/-- `f(d) = ∏_{p ∣ d, p > 2} (p - 2)⁻¹`. -/
def fd (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors.filter (fun p => 2 < p), 1 / ((p : ℝ) - 2)

/-- Odd squarefree positive integers, the range of the primed sums of the paper. -/
def OddSqf (d : ℕ) : Prop := 0 < d ∧ Odd d ∧ Squarefree d

/-- The singular series `𝔖(n) = ∏_{p ∤ n} (1 - 1/(p-1)²) ∏_{p ∣ n} p/(p-1)`, written as one
product over all primes. For even `n` it is `2 c₀ ∏_{p > 2, p ∣ n} (p-1)/(p-2)`. -/
def Sing (n : ℕ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime},
    if p.1 ∣ n then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2

end

end LeanLab.LPZ2007

section

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannGoldbach

/-- The number of primes `p < n` with `n - p` prime, the number of ordered representations of `n`
as a sum of two primes. -/
noncomputable def r (n : ℕ) : ℕ := #{p ∈ range n | p.Prime ∧ (n - p).Prime}

end LeanLab.SchnirelmannGoldbach

end

section

open Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

noncomputable section
namespace LeanLab.ChenExplicit

/-- The twin prime constant `c₀ = ∏_{p > 2} (1 - 1/(p-1)²)`. -/
def twinC : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

end LeanLab.ChenExplicit

end

end

namespace LeanLab.LPZ2007
open Finset Real

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `j(d, k, N)` with `k + 1` exponents: the number of `ν ∈ [1, ξ(d)]^{k+1}` with
`d ∣ N - 2^{ν₁} - … - 2^{ν_{k+1}}`. -/
def jcount (d k N : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin (k + 1) => Icc 1 (xi d))).filter
    (fun ν => (d : ℤ) ∣ (N : ℤ) - ∑ i, (2 : ℤ) ^ ν i)).card

end

end LeanLab.LPZ2007

namespace LeanLab.LPZ2007
open Finset Real

attribute [local instance] Classical.propDecidable

/-- The term of the series defining `C(k, N)`: `f(d) j(d, k - 1, N) / ξ(d)^k` for odd squarefree
`d`, and `0` otherwise. -/
noncomputable def Ckterm (k N d : ℕ) : ℝ :=
  if OddSqf d then fd d * (jcount d (k - 1) N : ℝ) / (xi d : ℝ) ^ k else 0

/-- The paper's constant `C(k, N)`, the sum over odd squarefree `d` of `Ckterm`. -/
noncomputable def Ck (k N : ℕ) : ℝ := ∑' d, Ckterm k N d

end LeanLab.LPZ2007

namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- `e(t) = exp(2 π i t)`. -/
def phase131 (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- The prime exponential sum `S(α) = ∑_{m ≤ X} Λ(m) e(m α)`. -/
def primeSum131 (X : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 X, (Λ m : ℝ) * phase131 ((m : ℝ) * α)

/-- The power of two sum `G(α) = ∑ e(2^ν α)` over `1 ≤ ν ≤ L - √L`. -/
def powerSum131 (X : ℕ) (α : ℝ) : ℂ :=
  ∑ ν ∈ Icc 1 ⌊Lg X - Real.sqrt (Lg X)⌋₊, phase131 ((2 : ℝ) ^ ν * α)

/-- `Q = X / P`. -/
def arcQ131 (X : ℕ) (P : ℝ) : ℝ := X / P

/-- The major arcs: the intervals of radius `1/(qQ)` about reduced `a/q` with `q ≤ P`. -/
def majorArcs131 (X : ℕ) (P : ℝ) : Set ℝ :=
  {α | ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ a ∈ Icc 1 q ∧ Nat.Coprime a q ∧
    α ∈ Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * arcQ131 X P))
      ((a : ℝ) / q + 1 / ((q : ℝ) * arcQ131 X P))}

/-- The real part of the major arc integral of `S(α)² G(α)^k e(-N α)`. -/
def majorContribution131 (k X N : ℕ) (P : ℝ) : ℝ :=
  (∫ α in majorArcs131 X P,
    primeSum131 X α ^ 2 * powerSum131 X α ^ k * phase131 (-(N : ℝ) * α)).re

/-- The even integers of `J(X) = [2X/3, X]`. -/
def evenJ131 (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun N : ℕ => Even N ∧ 2 * (X : ℝ) / 3 ≤ N)

/-- The coefficient of the main term with the factor `2 c₀`: `2 c₀ C(k, N)`. -/
def coefficient131 (k N : ℕ) : ℝ := 2 * LeanLab.ChenExplicit.twinC * Ck k N

/-- The admissible range `X^{2/5} ≤ P ≤ X^{41/100}` of the major arc parameter `P`. -/
def AdmissibleP131 (X : ℕ) (P : ℝ) : Prop :=
  (X : ℝ) ^ ((2 : ℝ) / 5) ≤ P ∧ P ≤ (X : ℝ) ^ ((41 : ℝ) / 100)

/-- The main theorem of the paper on `J(X)`, with coefficient `2 c₀ C(k, N)`: for `k ≥ 1` there is
`K` such that for every `η > 0` and every large `X`, at most `K X^{3/5} (log X)^{10}` even `N` in
`J(X)` have `|R''_k(N) - 2 c₀ C(k, N) N L^k| > η N L^k`. -/
def RepairedMainJ131 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((evenJ131 X).filter (fun N : ℕ =>
        η * N * Lg X ^ k < |Rpp k X N - coefficient131 k N * N * Lg X ^ k|)).card : ℝ) ≤
      K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10

end

end LeanLab.LPZ2007

namespace LeanLab.LPZ2007

open Finset Real Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- The exponent tuples `ν ∈ [1, M]^k`. -/
def exponentTuples131 (k M : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ => Icc 1 M)

end

end LeanLab.LPZ2007

namespace LeanLab.LPZ2007

open Finset Real Filter

noncomputable section

/-- The number of representations `N = p₁ + p₂ + 2^{ν₁} + … + 2^{ν_k}` with `p₁, p₂` prime and
`ν ∈ [1, L]^k`, `L = ⌊log₂ X⌋`. When `2^{ν₁} + … + 2^{ν_k} > N` the truncated difference is `0`,
which has no representation as a sum of two primes. -/
def primeRepresentationCount131 (k X N : ℕ) : ℕ :=
  ∑ ν ∈ exponentTuples131 k (Lp X), LeanLab.SchnirelmannGoldbach.r (N - ∑ i, 2 ^ ν i)

end

end LeanLab.LPZ2007

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- The even `N ≤ X` that are not of the form `p₁ + p₂ + 2^{ν₁} + … + 2^{ν_k}` with
`ν_i ∈ [1, log₂ X]`. -/
def allPrimeExceptions131 (k X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun N => Even N ∧ primeRepresentationCount131 k X N = 0)

end

end LeanLab.LPZ2007

namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- The binary major arc integral `R_M(n)`, the integral of `S(α)² e(-n α)` over the major
arcs, that is `majorContribution131` at `k = 0`. -/
def binaryMajor131 (X n : ℕ) (P : ℝ) : ℝ := majorContribution131 0 X n P

/-- `q'`, the product of the odd primes dividing `q`, without multiplicity. -/
def oddRad131 (r : ℕ) : ℕ := ∏ p ∈ r.primeFactors.filter (fun p => 2 < p), p

/-- At most `K₁` exceptional moduli, each with `r' ≥ c L²`, Corollary 4.2 and display 10. -/
def ExceptionalModuli131 (K₁ : ℕ) (c : ℝ) (X : ℕ) (E : Finset ℕ) : Prop :=
  E.card ≤ K₁ ∧ ∀ r ∈ E, c * Lg X ^ 2 ≤ oddRad131 r

/-- Display 9: no exceptional modulus `r ∈ E` divides `C* n`. -/
def Nonexceptional131 (Cstar : ℕ) (E : Finset ℕ) (n : ℕ) : Prop :=
  ∀ r ∈ E, ¬ r ∣ Cstar * n

/-- Corollary 4.2 of the paper for the binary integral on a window `W X` of even `n`: for every
`η > 0` there are constants, and for every large `X` an admissible `P` and an exceptional set
`E`, such that `|R_M(n) - n 𝔖(n)| ≤ η n 𝔖(n)` for the `n` of the window not divisible by the
moduli of `E`, and `|R_M(n)| ≤ A n 𝔖(n)` for all `n` of the window. -/
def Cor42OnWindow131 (W : ℕ → Finset ℕ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ (K₁ Cstar : ℕ) (c A : ℝ), 0 < Cstar ∧ 0 < c ∧ 0 ≤ A ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ ExceptionalModuli131 K₁ c X E ∧
        (∀ n ∈ W X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
        (∀ n ∈ W X, |binaryMajor131 X n P| ≤ A * n * Sing n)

end

end LeanLab.LPZ2007

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-- The Dirichlet L function `L(s, χ)` of Mathlib, with `0` at the unused modulus `0`. -/
def Lfun481 {r : ℕ} (χ : DirichletCharacter ℂ r) (s : ℂ) : ℂ :=
  if h : r = 0 then 0 else haveI : NeZero r := ⟨h⟩; DirichletCharacter.LFunction χ s

/-- Display 8: zeros `ρ` of `L(s, χ)` for primitive `χ` modulo `r ≤ P` with
`1 - H / log X ≤ Re ρ < 1` and `|Im ρ| ≤ T`. -/
def zeroBox481 (X : ℕ) (H T P : ℝ) : Set (Σ r : ℕ, DirichletCharacter ℂ r × ℂ) :=
  {z | 1 ≤ z.1 ∧ (z.1 : ℝ) ≤ P ∧ z.2.1.IsPrimitive ∧ Lfun481 z.2.1 z.2.2 = 0 ∧
    1 - H / Real.log X ≤ z.2.2.re ∧ z.2.2.re < 1 ∧ |z.2.2.im| ≤ T}

/-- The Gamma quotient and power of one pair contribution,
`Γ(s) Γ(t) / Γ(s + t) n^{s + t - 1}`. -/
def gammaPair481 (s t : ℂ) (n : ℕ) : ℂ :=
  (Complex.Gamma s * Complex.Gamma t / Complex.Gamma (s + t)) *
    (n : ℂ) ^ (s + t - 1)

/-- The pole at `1` has weight one and every zero has weight minus one. -/
def zeroSign481 {K : ℕ} (i : Fin (K + 1)) : ℂ := if i = 0 then 1 else -1

/-- Cited input. Languasco, Pintz and Zaccagnini 2007, Lemma 4.1, journal pages 774 and 775,
quoted there from J. Pintz, *Recent results on the Goldbach conjecture*, Proceedings ELAZ 2004,
Steiner, Stuttgart 2006, pages 220 to 254, Theorem 10: the real part of the explicit formula
for the binary major arc integral, `R_M(n)` equals the sum over the pole and the zeros of
display 8, with generalized singular series `Sg`, up to `O(X e^{-cH} + X / √T)` uniformly in `n`.
The zeros are counted with multiplicity at most their analytic order. The list of zeros need not
contain every zero of display 8, and `‖Sg i j n‖ ≤ ε` is asked only when `r_i` or `r_j` does not
divide `C(ε) n`, without the conductor condition; both make the hypothesis weaker than the
printed lemma. -/
def Lemma41Statement481 : Prop :=
  ∃ c ε₀ B H₀ T₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ 0 ≤ B ∧
    ∃ Cε : ℝ → ℕ, (∀ ε, 0 < Cε ε) ∧
    ∀ H T : ℝ, H₀ ≤ H → T₀ ≤ T →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∃ P : ℝ, AdmissibleP131 X P ∧
        ∃ (K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
          (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ),
          (z 0).1 = 1 ∧ (z 0).2.2 = 1 ∧
          (∀ i, i ≠ 0 → z i ∈ zeroBox481 X H T P) ∧
          (∀ w, ((univ.filter (fun i => i ≠ 0 ∧ z i = w)).card : ℕ) ≤
            analyticOrderNatAt (Lfun481 w.2.1) w.2.2) ∧
          (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) ∧
          (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) ∧
          (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
            (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) ∧
          ∀ n ∈ evenJ131 X,
            |binaryMajor131 X n P -
              (∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
                gammaPair481 (z i).2.2 (z j).2.2 n).re| ≤
              B * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T)

end
end LeanLab.LPZ2007

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- Jutila 1977, page 46: the rectangle `R(α, T)` with the index set of `N*(α, T, Q)`, that is a
modulus `1 ≤ q ≤ Q`, a primitive character modulo `q` and a zero of its L function with
`α ≤ σ ≤ 1` and `|t| ≤ T`. -/
def jutilaRect481 (α T Q : ℝ) : Set (Σ r : ℕ, DirichletCharacter ℂ r × ℂ) :=
  {z | 1 ≤ z.1 ∧ (z.1 : ℝ) ≤ Q ∧ z.2.1.IsPrimitive ∧ Lfun481 z.2.1 z.2.2 = 0 ∧
    α ≤ z.2.2.re ∧ z.2.2.re ≤ 1 ∧ |z.2.2.im| ≤ T}

/-- Cited input. M. Jutila, *On Linnik's constant*, Math. Scand. 41 (1977), page 46,
Theorem 1, display 1.8: for `4/5 ≤ α ≤ 1` and `T ≥ 1`,
`N*(α, T, Q) ≪_ε (Q² T)^{(2 + ε)(1 - α)}`, the implied constant depending on `ε` only.
`N*` is written as the sum of analytic multiplicities over any finite set of distinct triples of a
modulus, a primitive character and a zero in the rectangle, which is the count with
multiplicity. -/
def JutilaTheorem18_481 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ α T Q : ℝ, 4 / 5 ≤ α → α ≤ 1 → 1 ≤ T →
    ∀ F : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      (∀ z ∈ F, z ∈ jutilaRect481 α T Q) →
      (∑ z ∈ F, (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) ≤
        C * (Q ^ 2 * T) ^ ((2 + ε) * (1 - α))

end

end LeanLab.LPZ2007

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- Cited input. H. Iwaniec, *On zeros of Dirichlet's L series*, Invent. Math. 23 (1974) 97 to
104, page 97, Theorem 2, read for nonreal characters: for `q ≥ 3`, `d = ∏_{p ∣ q} p`,
`l = log q(|t| + 3)` and `θ⁻¹ = 4·10⁴ (log d + (l log 2l)^{3/4})`, Theorem 2 allows a zero with
`Re ρ > 1 - θ` only for one real character modulo `q`, so `L(s, χ)` has no zero with
`Re s > 1 - θ` when `χ` takes a nonreal value. -/
def IwaniecTheorem2_1123 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ χ : DirichletCharacter ℂ r, (∃ a, (χ a).im ≠ 0) → ∀ s : ℂ,
    1 - 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
      (Real.log ((r : ℝ) * (|s.im| + 3)) *
        Real.log (2 * Real.log ((r : ℝ) * (|s.im| + 3)))) ^ (3 / 4 : ℝ))) < s.re →
    Lfun481 χ s ≠ 0

/-- Languasco, Pintz and Zaccagnini 2007, Corollary 4.2, on the even numbers of `J(X)`, from
the Pintz explicit formula, Jutila's density theorem and Iwaniec's zero free region. -/
theorem cor42_of_three_inputs (hexp : Lemma41Statement481) (hjut : JutilaTheorem18_481)
    (hiw : IwaniecTheorem2_1123) : Cor42OnWindow131 evenJ131 := by
  sorry

/-- Languasco, Pintz and Zaccagnini 2007, the main theorem on the even numbers of `J(X)` with
coefficient `2 c₀ C(k, N)`, from the same three cited inputs. -/
theorem repaired_mainJ131_of_three_inputs (hexp : Lemma41Statement481)
    (hjut : JutilaTheorem18_481) (hiw : IwaniecTheorem2_1123) : RepairedMainJ131 := by
  sorry

/-- Languasco, Pintz and Zaccagnini 2007, the consequence of the Theorem for sums of two primes
and `k` powers of two: for `k ≥ 1`, all but `O(X^{3/5} (log X)^{10})` even `N ≤ X` are
`p₁ + p₂ + 2^{ν₁} + … + 2^{ν_k}` with `ν_i ∈ [1, log₂ X]`, from the same three cited inputs. -/
theorem global_primes_of_three_inputs (hexp : Lemma41Statement481)
    (hjut : JutilaTheorem18_481) (hiw : IwaniecTheorem2_1123) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (allPrimeExceptions131 k X).card ≤ C * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
  sorry

end

end LeanLab.LPZ2007
