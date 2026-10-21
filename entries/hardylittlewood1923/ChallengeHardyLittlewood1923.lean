module

public import Mathlib

/-!
# Sums of primes, Hardy and Littlewood 1923, Theorems B to F, unconditionally

G. H. Hardy and J. E. Littlewood, *Some problems of 'Partitio Numerorum'; III: On the expression
of a number as a sum of primes*, Acta Math. 44 (1923) 1-70. Hardy and Littlewood proved their
Theorems under Hypothesis R, a form of the generalized Riemann hypothesis for Dirichlet
L-functions. Every theorem below is stated, and proved in the solution, with NO hypothesis:
the unconditional input is Vinogradov's estimate for exponential sums over primes and the
Siegel-Walfisz theorem. Theorem A of the paper, (3.113), is not formalized here: on Hypothesis R
it gives `ν_r(n) = n^{r-1} 𝔖_r/(r-1)! + O(n^{r-1+Θ-3/4} (log n)^B)` with the singular series
`𝔖_r` of (3.114); Theorem B is its consequence with `𝔖_r` summed as a product, Lemma 12.

Notation, page 6 of the paper. `Nr r n` is `N_r(n)`, the number of ordered `r`-tuples of primes
with sum `n`, (1.45); `nur r n` is `ν_r(n) = Σ log ϖ₁ ⋯ log ϖ_r` over the same tuples, (1.46).
`Br r n = ∏_{p ∣ n, p odd} ((p-1)^r + (-1)^r (p-1))/((p-1)^r - (-1)^r)` and
`Cr r = ∏_{ϖ ≥ 3} (1 - (-1)^r/(ϖ-1)^r)` are the product and the constant of (3.32).

The compared theorems are:
* `theoremB`, (3.32): for every `r ≥ 3` and `n ≡ r mod 2`,
  `ν_r(n) ∼ (2 C_r/(r-1)!) n^{r-1} Br r n`; `theoremB3` and `theoremB4` are the cases `r = 3, 4`
  written out; `theoremB_unlike`, (3.31): `ν_r(n) = o(n^{r-1})` when `n`, `r` have unlike parity.
* `theoremC`, (3.51): for `r ≥ 3` and `n ≡ r mod 2`, `N_r(n) ∼ ν_r(n)/(log n)^r`.
* `theoremD`, (3.61): the number `N̄₃(n)` of ordered triples of odd primes with sum `n`, for odd
  `n`, is `∼ C₃ n²/(log n)³ ∏_{p ∣ n} (p-1)(p-2)/(p²-3p+3)`; `theoremD_ternary`: every large odd
  `n` is a sum of three odd primes.
* `theoremE`, (3.63): the number `N̄₄(n)` of ordered 4-tuples of odd primes with sum `n`, for even
  `n`, is `∼ (1/3) C₄ n³/(log n)⁴ ∏_{p ∣ n, p odd} (p-1)(p²-3p+3)/((p-2)(p²-2p+2))`;
  `theoremE_four`: every large even `n` is a sum of four odd primes; `theoremE_assigned`: one of
  the four may be any prescribed odd prime.
* `theoremF`, (4.21) to (4.23): if `N₂(n) ∼ A n/(log n)² Br 2 n` for even `n` and
  `N₂(n) = o(n/(log n)²)` for odd `n`, then `A = 2 C₂`; `printed_423_false`: the printed (4.23),
  which also equates `2 C₂` with the product `C₂`, contains a misprint, since `2 C₂ ≠ C₂`.

Every `∼` is written in the `ε` form: for every `ε > 0`, eventually `|X - Y| ≤ ε Y`. Ternary
Goldbach is Helfgott's theorem; binary Goldbach is open, and nothing here claims it. Lean names
keep the namespaces of the lab where the proofs were written. An AI agent, Claude by Anthropic,
wrote the Lean code.
-/

@[expose] public section

/-! ### Theorem C notation, `LeanLab/HardyLittlewood1923/TheoremC.lean` -/

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter

/-- N_r(n), (1.45): ordered r-tuples of primes with sum n. -/
noncomputable def Nr (r n : ℕ) : ℕ :=
  #((Fintype.piFinset fun _ : Fin r => Finset.range (n + 1)).filter
    (fun t => (∀ i, (t i).Prime) ∧ ∑ i, t i = n))

/-- ν_r(n), (1.46). -/
noncomputable def nur (r n : ℕ) : ℝ :=
  ∑ t ∈ (Fintype.piFinset fun _ : Fin r => Finset.range (n + 1)).filter
    (fun t => (∀ i, (t i).Prime) ∧ ∑ i, t i = n), ∏ i, Real.log (t i)

/-- Theorem C, (3.51). -/
def theoremC_stmt : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → n % 2 = r % 2 →
    |(Nr r n : ℝ) * Real.log n ^ r - nur r n| ≤ ε * nur r n

end LeanLab.HardyLittlewood1923

/-! ### Theorem D notation, `LeanLab/HardyLittlewood1923/TheoremD.lean` -/

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter

attribute [local instance] Classical.propDecidable

/-- `N̄₃(n)`: ordered triples of odd primes with sum `n`, repetitions allowed. -/
noncomputable def N3bar (n : ℕ) : ℕ :=
  #{t ∈ (range (n + 1)) ×ˢ (range (n + 1)) | (t.1.Prime ∧ t.2.Prime ∧ n - t.1 - t.2 ≠ 0 ∧
    (n - t.1 - t.2).Prime ∧ t.1 + t.2 ≤ n) ∧ (Odd t.1 ∧ Odd t.2 ∧ Odd (n - t.1 - t.2))}

/-- (3.62) `C₃ = ∏_{ϖ ≥ 3 prime} (1 + 1/(ϖ - 1)³)`, the factor at `2` replaced by `1`. -/
noncomputable def C3 : ℝ :=
  ∏' p : {p : ℕ // p.Prime}, if p = ⟨2, Nat.prime_two⟩ then 1 else 1 + 1 / ((p : ℝ) - 1) ^ 3

/-- The product in (3.61), over the prime divisors of `n`. -/
noncomputable def Pi3 (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) * ((p : ℝ) - 2) / ((p : ℝ) ^ 2 - 3 * p + 3)

/-- Theorem D, (3.61), in the `ε` form of `∼`. -/
def theoremD_stmt : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, Odd n → n₀ ≤ n →
    |(N3bar n : ℝ) - C3 * (n : ℝ) ^ 2 / Real.log n ^ 3 * Pi3 n| ≤
      ε * (C3 * (n : ℝ) ^ 2 / Real.log n ^ 3 * Pi3 n)

/-- **Hardy-Littlewood 1923, Theorem D, (3.61)**, with no hypothesis. -/
theorem theoremD : theoremD_stmt := by
  sorry

/-- Theorem D, first sentence: every large odd number is the sum of three odd primes. -/
theorem theoremD_ternary : ∃ n₀ : ℕ, ∀ n, Odd n → n₀ ≤ n → 0 < N3bar n := by
  sorry

end LeanLab.HardyLittlewood1923

/-! ### Theorem E notation, `LeanLab/HardyLittlewood1923/TheoremEStatements.lean` -/

namespace LeanLab.HardyLittlewood1923

open Real Finset

attribute [local instance] Classical.propDecidable

/-- `N̄₄(n)`: ordered 4-tuples of odd primes with sum `n`, repetitions allowed. -/
noncomputable def N4bar (n : ℕ) : ℕ :=
  #{t ∈ (range (n + 1)) ×ˢ ((range (n + 1)) ×ˢ (range (n + 1))) |
    t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 + t.2.1 + t.2.2 < n ∧
    (n - t.1 - t.2.1 - t.2.2).Prime ∧
    Odd t.1 ∧ Odd t.2.1 ∧ Odd t.2.2 ∧ Odd (n - t.1 - t.2.1 - t.2.2)}

/-- (3.64) `C₄ = ∏_{ϖ ≥ 3 prime} (1 - 1/(ϖ - 1)⁴)`. -/
noncomputable def C4 : ℝ :=
  ∏' p : {p : ℕ // p.Prime}, if p = ⟨2, Nat.prime_two⟩ then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 4

/-- The product in (3.63), over the odd prime divisors of `n`. -/
noncomputable def Pi4 (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2),
    ((p : ℝ) - 1) * ((p : ℝ) ^ 2 - 3 * p + 3) / (((p : ℝ) - 2) * ((p : ℝ) ^ 2 - 2 * p + 2))

/-- Theorem E, (3.63), in the `ε` form of `∼`, over even `n`. -/
def theoremE_stmt : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, Even n → n₀ ≤ n →
    |(N4bar n : ℝ) - C4 * (n : ℝ) ^ 3 / (3 * Real.log n ^ 4) * Pi4 n| ≤
      ε * (C4 * (n : ℝ) ^ 3 / (3 * Real.log n ^ 4) * Pi4 n)

end LeanLab.HardyLittlewood1923

/-! ### Theorem B notation, `LeanLab/HardyLittlewood1923/TheoremB34.lean` -/

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter

/-- The product in (3.32), over the odd prime divisors of `n`, as written in the paper. -/
noncomputable def Br (r n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (· ≠ 2),
    (((p : ℝ) - 1) ^ r + (-1) ^ r * ((p : ℝ) - 1)) / (((p : ℝ) - 1) ^ r - (-1) ^ r)

/-- The constant `C_r = ∏_{ϖ ≥ 3} (1 - (-1)^r/(ϖ-1)^r)` of (3.32), the factor at `2` set to `1`. -/
noncomputable def Cr (r : ℕ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime}, if p = ⟨2, Nat.prime_two⟩ then 1 else 1 - (-1 : ℝ) ^ r / ((p : ℝ) - 1) ^ r

/-- **Hardy-Littlewood 1923, Theorem B, (3.32), r = 3**, with no hypothesis. -/
theorem theoremB3 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, Odd n → n₀ ≤ n →
    |nur 3 n - 2 * Cr 3 / 2 * (n : ℝ) ^ 2 * Br 3 n| ≤ ε * (2 * Cr 3 / 2 * (n : ℝ) ^ 2 * Br 3 n) := by
  sorry

/-- **Hardy-Littlewood 1923, Theorem B, (3.32), r = 4**, with no hypothesis. -/
theorem theoremB4 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, Even n → n₀ ≤ n →
    |nur 4 n - 2 * Cr 4 / 6 * (n : ℝ) ^ 3 * Br 4 n| ≤ ε * (2 * Cr 4 / 6 * (n : ℝ) ^ 3 * Br 4 n) := by
  sorry

end LeanLab.HardyLittlewood1923

/-! ### Theorem B for every `r ≥ 3`, `LeanLab/HardyLittlewood1923/TheoremBAll.lean` -/

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter

/-- The main term of (3.32), `(2 C_r/(r-1)!) n^{r-1} Br r n`. -/
noncomputable def Mr (r n : ℕ) : ℝ :=
  2 * Cr r / (Nat.factorial (r - 1) : ℝ) * (n : ℝ) ^ (r - 1) * Br r n

/-- **Theorem B, (3.32)**, for one `r`, in the `ε` form of `∼`. -/
def theoremB_stmt (r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n % 2 = r % 2 → n₀ ≤ n →
    |nur r n - Mr r n| ≤ ε * Mr r n

/-- **Hardy-Littlewood 1923, Theorem B, (3.32), for every `r ≥ 3`**, with no hypothesis:
if `r ≥ 3` and `n ≡ r mod 2` then
`ν_r(n) ∼ (2 C_r/(r-1)!) n^{r-1} ∏_{p ∣ n, p odd} ((p-1)^r + (-1)^r (p-1))/((p-1)^r - (-1)^r)`. -/
theorem theoremB : ∀ r : ℕ, 3 ≤ r → theoremB_stmt r := by
  sorry

/-- **Theorem B, (3.31)**: `ν_r(n) = o(n^{r-1})` for `r ≥ 3` and `n`, `r` of unlike parity. -/
theorem theoremB_unlike : ∀ r : ℕ, 3 ≤ r → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ,
    n % 2 ≠ r % 2 → n₀ ≤ n → nur r n ≤ ε * (n : ℝ) ^ (r - 1) := by
  sorry

/-- **Hardy-Littlewood 1923, Theorem C, (3.51)**: for `r ≥ 3` and `n ≡ r mod 2`,
`N_r(n) ∼ ν_r(n)/(log n)^r`, with no hypothesis. -/
theorem theoremC : theoremC_stmt := by
  sorry

end LeanLab.HardyLittlewood1923

/-! ### Theorem E, `LeanLab/HardyLittlewood1923/TheoremE.lean` and `TheoremEAssigned.lean` -/

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter

/-- **Hardy-Littlewood 1923, Theorem E, (3.63)**, with no hypothesis. -/
theorem theoremE : theoremE_stmt := by
  sorry

/-- Theorem E, first sentence: every large even number is the sum of four odd primes. -/
theorem theoremE_four : ∃ n₀ : ℕ, ∀ n, Even n → n₀ ≤ n → 0 < N4bar n := by
  sorry

end LeanLab.HardyLittlewood1923

namespace LeanLab.HardyLittlewood1923

open Finset

attribute [local instance] Classical.propDecidable

/-- Theorem E's assigned prime: for each odd prime `q`, every large even `n` is
`q + p₁ + p₂ + p₃` with `p₁, p₂, p₃` odd primes. -/
theorem theoremE_assigned (q : ℕ) (hq : q.Prime) (hqo : Odd q) :
    ∃ n₀ : ℕ, ∀ n, Even n → n₀ ≤ n → ∃ a b c : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧
      Odd a ∧ Odd b ∧ Odd c ∧ q + a + b + c = n := by
  sorry

end LeanLab.HardyLittlewood1923

/-! ### Theorem F, `LeanLab/HardyLittlewood1923/TheoremF.lean` -/

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter

/-- The main term of (4.21), `n/(log n)² ∏_{p ∣ n, p odd} (p-1)/(p-2)`. -/
noncomputable def M2 (n : ℕ) : ℝ := (n : ℝ) / Real.log n ^ 2 * Br 2 n

/-- (4.21) with the constant `A`, in the `ε` form of `∼`. -/
def hyp421 (A : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, Even n → n₀ ≤ n → |(Nr 2 n : ℝ) - A * M2 n| ≤ ε * M2 n

/-- (4.22), `N₂(n) = o(n/(log n)²)` for odd `n`. -/
def hyp422 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, ¬ Even n → n₀ ≤ n → (Nr 2 n : ℝ) ≤ ε * ((n : ℝ) / Real.log n ^ 2)

/-- **Hardy-Littlewood 1923, Theorem F**: (4.21) and (4.22) force `A = 2 C₂`, (4.23). -/
theorem theoremF (A : ℝ) (h1 : hyp421 A) (h2 : hyp422) : A = 2 * Cr 2 := by
  sorry

/-- The printed (4.23) reads `A = 2 C₂ = ∏_{ϖ ≥ 3} (1 - 1/(ϖ-1)²)`; the second equality is a
misprint, since the product is `C₂` itself, (4.12), and `2 C₂ ≠ C₂` as `C₂ > 0`. -/
theorem printed_423_false : 2 * Cr 2 ≠ Cr 2 := by
  sorry

end LeanLab.HardyLittlewood1923
