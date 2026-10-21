module

public import Mathlib

/-!
# Wu 2008, Lemma 2.2, with the range of Υ₁₁ repaired

J. Wu, *Chen's double sieve, Goldbach's conjecture and the twin prime problem, 2*,
Acta Arith. 131 (2008) 367–387, arXiv 0709.3764, Lemma 2.2, inequality (2.2), p. 371.

Wu's inequality is the combinatorial input of his lower bound D₁,₂(N) ≥ 0.899 Θ(N) for the number
of primes p ≤ N with N − p a product of at most two primes. Its printed proof drops part of the
range of the last triple sum: the Buchstab step gives p₄ < N^{1/2−3κ₁}, the printed Υ₁₁ runs only
over p₄ < N^{1/2−2κ₁}/p₃. This entry states and proves the lemma with the full range.

Readings, all stated explicitly in the definitions below:
* `S A e D y` is Wu's S(A_e; P(D), y): the members of `A` divisible by `e` with no prime factor
  `q < y` that is coprime to `D`. Wu's P(z) uses p ≤ z; the strict `<` used here is the one the
  proof needs, a boundary convention.
* Υ₉ sifts by P(N p₁ p₂) at level (N/p₁p₂)^{1/2}, and Υ₁₀, Υ₁₁ by P(N p₁) at level p₂. Wu prints
  P(N p₁) for Υ₉ and P(N) for Υ₁₀, Υ₁₁; with those printed sets the three sums vanish identically.
* Wu's O(N^{1−κ₁}) is made explicit: `lemma22_sum` has the exact error `4 * Esq`, the count of
  non-squarefree sifted members, and `lemma22_wuA` bounds it by `4 N/(N^κ₁ − 1)` for Wu's
  sequence A = {N − p}.
* The statement holds for every N > 1, not only for large N, and for any κ₁, κ₂ satisfying Wu's
  hypotheses, `Admissible`, with the last one weakened from `<` to `≤`.
-/

open Finset
open scoped ArithmeticFunction.Omega

@[expose] public noncomputable section
open scoped Classical

namespace GoldbachLean.Wu2008.WuSieve

/-- `a` survives sifting by `P(D) = {q prime : q ∤ D}` up to `y`: no prime `q < y` with `q ∤ D`
divides `a`. -/
def Sifted (D : ℕ) (y : ℝ) (a : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → (q : ℝ) < y → ¬ q ∣ D → ¬ q ∣ a

/-- Wu's sieve function `S(A_e; P(D), y)`: the number of `a ∈ A` with `e ∣ a` that survive
sifting by `P(D)` up to `y`. -/
def S (A : Finset ℕ) (e D : ℕ) (y : ℝ) : ℕ :=
  #{a ∈ A | e ∣ a ∧ Sifted D y a}

/-- The primes `p` with `w ≤ p < z` and `(p, N) = 1`. -/
def PS (N : ℕ) (w z : ℝ) : Finset ℕ :=
  {p ∈ range ⌈z⌉₊ | p.Prime ∧ w ≤ p ∧ (p : ℝ) < z ∧ p.Coprime N}

end GoldbachLean.Wu2008.WuSieve

namespace GoldbachLean.Wu2008.WuReal

/-- Wu's κ₁ = 1/13.27. -/
def wk1 : ℝ := 100 / 1327
/-- Wu's κ₂ = 1/8.24. -/
def wk2 : ℝ := 100 / 824
/-- The exponent `1/2 − 3κ₁`. -/
def em (k1 : ℝ) : ℝ := 1 / 2 - 3 * k1
/-- The exponent `1/3`. -/
def e13 : ℝ := 1 / 3

/-- Wu's hypotheses for Lemma 2.2: κ₂ > κ₁ ≥ 1/18, 3κ₁ + κ₂ < 1/2, and 3κ₁ − κ₂ < 1/6, the last
weakened here to `≤`. -/
def Admissible (k1 k2 : ℝ) : Prop :=
  1 / 18 ≤ k1 ∧ k1 < k2 ∧ 3 * k1 + k2 < 1 / 2 ∧ 3 * k1 - k2 ≤ 1 / 6

/-- Wu's own values are admissible. -/
theorem wu_admissible : Admissible wk1 wk2 := by
  sorry

end GoldbachLean.Wu2008.WuReal

namespace GoldbachLean.Wu2008.WuSum
open GoldbachLean.Wu2008.WuSieve (Sifted S PS)
open GoldbachLean.Wu2008.WuReal (e13 em Admissible)

/-- Pairs `(p₁, p₂)` of primes below `N`, both coprime to `N`, satisfying `C p₁ p₂`. -/
def P2 (N : ℕ) (C : ℕ → ℕ → Prop) : Finset (ℕ × ℕ) :=
  {q ∈ range N ×ˢ range N | q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N ∧ C q.1 q.2}

/-- Quadruples `(p₁, p₂, p₃, p₄)` of primes below `N`, all coprime to `N`, satisfying `C`. -/
def P4 (N : ℕ) (C : ℕ → ℕ → ℕ → ℕ → Prop) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {q ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N | q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧
    q.2.2.2.Prime ∧ q.1.Coprime N ∧ q.2.1.Coprime N ∧ q.2.2.1.Coprime N ∧ q.2.2.2.Coprime N ∧
    C q.1 q.2.1 q.2.2.1 q.2.2.2}

variable (A : Finset ℕ) (N : ℕ) (k1 k2 : ℝ)

/-- Υ₁ = S(A; P(N), N^κ₁). -/
def Y1 : ℕ := S A 1 N ((N : ℝ) ^ k1)
/-- Υ₂ = S(A; P(N), N^κ₂). -/
def Y2 : ℕ := S A 1 N ((N : ℝ) ^ k2)
/-- Υ₃ = Σ_{N^κ₁ ≤ p < N^{1/3}, (p,N)=1} S(A_p; P(N), N^κ₁). -/
def Y3 : ℕ := ∑ p ∈ PS N ((N : ℝ) ^ k1) ((N : ℝ) ^ e13), S A p N ((N : ℝ) ^ k1)
/-- Υ₄ = Σ_{N^κ₁ ≤ p < N^{1/2−3κ₁}, (p,N)=1} S(A_p; P(N), N^κ₁). -/
def Y4 : ℕ := ∑ p ∈ PS N ((N : ℝ) ^ k1) ((N : ℝ) ^ em k1), S A p N ((N : ℝ) ^ k1)
/-- The range of Υ₅: N^κ₁ ≤ p₁ < p₂ < N^κ₂. -/
def C5 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ p₁ < p₂ ∧ (p₂ : ℝ) < (N : ℝ) ^ k2
/-- Υ₅ = Σ_{N^κ₁ ≤ p₁ < p₂ < N^κ₂} S(A_{p₁p₂}; P(N), N^κ₁). -/
def Y5 : ℕ := ∑ q ∈ P2 N (C5 N k1 k2), S A (q.1 * q.2) N ((N : ℝ) ^ k1)
/-- The range of Υ₆: N^κ₁ ≤ p₁ < N^κ₂ ≤ p₂ < N^{1/2−3κ₁}. -/
def C6 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ (p₁ : ℝ) < (N : ℝ) ^ k2 ∧
  (N : ℝ) ^ k2 ≤ p₂ ∧ (p₂ : ℝ) < (N : ℝ) ^ em k1
/-- Υ₆ = Σ_{N^κ₁ ≤ p₁ < N^κ₂ ≤ p₂ < N^{1/2−3κ₁}} S(A_{p₁p₂}; P(N), N^κ₁). -/
def Y6 : ℕ := ∑ q ∈ P2 N (C6 N k1 k2), S A (q.1 * q.2) N ((N : ℝ) ^ k1)
/-- The range of Υ₇: N^{1/2−3κ₁} ≤ p₁ < p₂ < (N/p₁)^{1/2}, written p₁ p₂² < N. -/
def C7 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ em k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₁ * p₂ ^ 2 < N
/-- Υ₇ = Σ S(A_{p₁p₂}; P(Np₁), p₂) over the range `C7`. -/
def Y7 : ℕ := ∑ q ∈ P2 N (C7 N k1), S A (q.1 * q.2) (N * q.1) q.2
/-- The range of Υ₈: N^κ₁ ≤ p₁ < N^{1/3} ≤ p₂ < (N/p₁)^{1/2}. -/
def C8 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ (p₁ : ℝ) < (N : ℝ) ^ e13 ∧
  (N : ℝ) ^ e13 ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
/-- Υ₈ = Σ S(A_{p₁p₂}; P(Np₁), p₂) over the range `C8`. -/
def Y8 : ℕ := ∑ q ∈ P2 N (C8 N k1), S A (q.1 * q.2) (N * q.1) q.2
/-- The range of Υ₉: N^κ₂ ≤ p₁ < N^{1/2−3κ₁} ≤ p₂ < (N/p₁)^{1/2}. -/
def C9 (p₁ p₂ : ℕ) : Prop := (N : ℝ) ^ k2 ≤ p₁ ∧ (p₁ : ℝ) < (N : ℝ) ^ em k1 ∧
  (N : ℝ) ^ em k1 ≤ p₂ ∧ p₁ * p₂ ^ 2 < N
/-- Υ₉ = Σ S(A_{p₁p₂}; P(Np₁p₂), (N/p₁p₂)^{1/2}) over the range `C9`, the intended sieve set. -/
def Y9 : ℕ := ∑ q ∈ P2 N (C9 N k1 k2),
  S A (q.1 * q.2) (N * q.1 * q.2) (Real.sqrt ((N : ℝ) / (q.1 * q.2)))
/-- The range of Υ₁₀: N^κ₁ ≤ p₁ < p₂ < p₃ < p₄ < N^κ₂. -/
def C10 (p₁ p₂ p₃ p₄ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧ p₃ < p₄ ∧
  (p₄ : ℝ) < (N : ℝ) ^ k2
/-- Υ₁₀ = Σ S(A_{p₁p₂p₃p₄}; P(Np₁), p₂) over the range `C10`, the intended sieve set. -/
def Y10 : ℕ := ∑ q ∈ P4 N (C10 N k1 k2),
  S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1
/-- The repaired range of Υ₁₁: N^κ₁ ≤ p₁ < p₂ < p₃ < N^κ₂ ≤ p₄ < N^{1/2−3κ₁}. Wu prints the
shorter p₄ < N^{1/2−2κ₁}/p₃. -/
def C11 (p₁ p₂ p₃ p₄ : ℕ) : Prop := (N : ℝ) ^ k1 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧
  (p₃ : ℝ) < (N : ℝ) ^ k2 ∧ (N : ℝ) ^ k2 ≤ p₄ ∧ (p₄ : ℝ) < (N : ℝ) ^ em k1
/-- Υ₁₁ = Σ S(A_{p₁p₂p₃p₄}; P(Np₁), p₂) over the repaired range `C11`. -/
def Y11 : ℕ := ∑ q ∈ P4 N (C11 N k1 k2),
  S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1

/-- D₁,₂ for `A`: the number of `a ∈ A` with at most two prime factors counted with multiplicity. -/
def D12 : ℕ := #{a ∈ A | Ω a ≤ 2}
/-- The error term: members of `A` sifted at `N^κ₁` that are not squarefree. -/
def Esq : ℕ := #{a ∈ A | Sifted N ((N : ℝ) ^ k1) a ∧ ¬ Squarefree a}

/-- **Wu 2008, Lemma 2.2, (2.2), with Υ₁₁ repaired**, for any finite set `A` of integers
`0 < a < N` coprime to `N`, any `N > 1` and any admissible `κ₁, κ₂`. -/
theorem lemma22_sum (hA : Admissible k1 k2) (hN : 1 < N)
    (hAN : ∀ a ∈ A, 0 < a ∧ a < N ∧ a.Coprime N) :
    (3 * Y1 A N k1 + Y2 A N k2 + Y5 A N k1 k2 + Y6 A N k1 k2 : ℤ) - Y3 A N k1 - Y4 A N k1
      - 2 * Y7 A N k1 - Y8 A N k1 - Y9 A N k1 k2 - Y10 A N k1 k2 - Y11 A N k1 k2
      ≤ 4 * D12 A + 4 * Esq A N k1 := by
  sorry

/-- Wu's sequence `A = {N − p : p < N prime, p ∤ N}`. -/
def wuA : Finset ℕ := ((range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)).image (fun p => N - p)

/-- **(2.2) for Wu's own sequence `A = {N − p}`, with Υ₁₁ repaired and the error explicit:**
Wu's `O(N^{1−κ₁})` is at most `4N/(N^κ₁ − 1)`. -/
theorem lemma22_wuA (hA : Admissible k1 k2) (hN : 1 < N) (hNk : 1 < (N : ℝ) ^ k1) :
    (3 * Y1 (wuA N) N k1 + Y2 (wuA N) N k2 + Y5 (wuA N) N k1 k2 + Y6 (wuA N) N k1 k2 : ℝ)
      - Y3 (wuA N) N k1 - Y4 (wuA N) N k1 - 2 * Y7 (wuA N) N k1 - Y8 (wuA N) N k1
      - Y9 (wuA N) N k1 k2 - Y10 (wuA N) N k1 k2 - Y11 (wuA N) N k1 k2
      ≤ 4 * D12 (wuA N) + 4 * (N / ((N : ℝ) ^ k1 - 1)) := by
  sorry

end GoldbachLean.Wu2008.WuSum

/-! ## Li 2024, Lemma 3.1: Wu's Lemma 2.2 at κ₁ = 1/11.49, κ₂ = 1/6.18, with the range of S₁₅
repaired. R. Li, arXiv 2405.05727 v4, Mathematical Reports 2026. -/

noncomputable section
namespace GoldbachLean.Li2024.Lemma31

open GoldbachLean.Wu2008.WuReal GoldbachLean.Wu2008.WuSum

/-- Li's κ₁ = 1/11.49. -/
def lk1 : ℝ := 100 / 1149
/-- Li's κ₂ = 1/6.18. -/
def lk2 : ℝ := 100 / 618

/-- Li's parameters satisfy Wu's hypotheses. -/
theorem li_admissible : Admissible lk1 lk2 := by
  sorry

/-- **Li 2024, Lemma 3.1, with S₁₅'s range repaired**, for A = {N − p}, explicit error. -/
theorem lemma31_repaired (N : ℕ) (hN : 1 < N) (hNk : 1 < (N : ℝ) ^ lk1) :
    (3 * Y1 (wuA N) N lk1 + Y2 (wuA N) N lk2 + Y5 (wuA N) N lk1 lk2 + Y6 (wuA N) N lk1 lk2 : ℝ)
      - Y3 (wuA N) N lk1 - Y4 (wuA N) N lk1 - 2 * Y7 (wuA N) N lk1 - Y8 (wuA N) N lk1
      - Y9 (wuA N) N lk1 lk2 - Y10 (wuA N) N lk1 lk2 - Y11 (wuA N) N lk1 lk2
      ≤ 4 * D12 (wuA N) + 4 * (N / ((N : ℝ) ^ lk1 - 1)) := by
  sorry

end GoldbachLean.Li2024.Lemma31
end
