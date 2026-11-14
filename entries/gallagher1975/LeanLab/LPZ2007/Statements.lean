module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.Linnik.Statements
public import LeanLab.PNTPort.Vinogradov.MinorArcs

/-!
P0045 A. Languasco, J. Pintz, A. Zaccagnini, "On the sum of two primes and k powers of two",
Bull. London Math. Soc. 39 (2007), 771-780. READ AS THE AUTHORS' LAST PREPRINT, not the journal
version: /home/claude/work/papers/P0045.pdf, 12 pages, pdftotext plus rendered pages 1-6, 9, 10.
Every constant below is the PREPRINT's and must be rechecked against the journal.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here is Goldbach: `R''_k(N) > 0` says `N` is two prime POWERS
plus `k` powers of two, and the main theorem is an almost-all statement with exceptions.

Encoding choices, stated honestly:
* `L = log_2 X` is `Lg X`; `L' = L - √L` is `Lp X`; `ν ∈ [1, L]` is `1 ≤ ν ≤ ⌊L⌋₊`.
* `J(X) = [2X/3, X]` is `InJ X`.
* `≪`, `O(·)` and "sufficiently large" are explicit existential constants `B`, `X0`.
* `ξ(d) = min{μ : 2^μ ≡ 1 mod d}` is read with `μ ≥ 1`, as `orderOf (2 : ZMod d)`; with `μ = 0`
  allowed every `ξ(d)` would be `0`. For odd `d` both readings with `μ ≥ 1` agree.
* `Σ'` over odd squarefree `d` is a `tsum` over `ℕ` with the other terms set to `0`.
* The major arcs need a parameter `P ∈ [X^0.4, X^0.41]` chosen by Lemma 4.1; statements that
  the paper proves for that `P` say `∃ P`, statements valid for every such `P` say `∀ P`.
* Lemma 4.1 and Corollary 4.2: the "generalised exceptional characters" are not defined fully in
  the paper. We quantify existentially over the finite family of moduli, characters, zeros,
  conductors and generalised singular series. This is WEAKER than the paper, which names the
  family; it is implied by the paper.
* Lemma 6.2 as printed has no lower bound on `r` and no `X` large; it is then false for `r = 1`,
  see QUESTION Q2 in STATEMENTS.md. We cite the form its proof gives: `r ≥ r0(ε)`, `X ≥ X0(ε)`.
* The Theorem as printed, on `[1, X]` with `L = log_2 X`, is kept as a `def` only, QUESTION Q1.
  The cited form is Section 5's: even `N ∈ J(X)`.
* QUESTION Q3: (17) drops the factor `2c0` of `S(n) = 2c0 Σ_{d|n} μ²(d) f(d)`. The cited
  `MainJ` keeps the preprint's `C(k,N)` literally, a `def` only since VERIFY U-0999;
  `MainJ_twoC0` is the corrected reading, cited through Repaired.lean.
-/

@[expose] public section

open Finset Real MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.LPZ2007

/-! ### Section 1, p.1-2: notation and counting functions -/

/-- `L = log_2 X`, Section 1 p.1. -/
def Lg (X : ℝ) : ℝ := Real.logb 2 X

/-- `L' = L - √L`, Section 1 p.2. -/
def Lp (X : ℝ) : ℝ := Lg X - √(Lg X)

/-- `N ∈ J(X) = [2X/3, X]`, Section 1 p.1. -/
def InJ (X : ℝ) (N : ℕ) : Prop := 2 * X / 3 ≤ N ∧ (N : ℝ) ≤ X

/-- Exponent tuples `(ν_1, ..., ν_k) ∈ [1, M]^k`. -/
def tuples (k M : ℕ) : Finset (Fin k → ℕ) := Fintype.piFinset fun _ => Icc 1 M

/-- `2^{ν_1} + ... + 2^{ν_k}`. -/
def pow2sum {k : ℕ} (ν : Fin k → ℕ) : ℕ := ∑ i, 2 ^ ν i

open Classical in
/-- `r''_k(N) = |{(p1, p2, ν) ∈ 𝔓² × [1, L]^k : N = p1 + p2 + 2^{ν1} + ... + 2^{νk}}|`, p.1.
Primes summing to at most `N` are at most `N`, so ranging them over `[0, N]` loses nothing. -/
def rpp (k : ℕ) (X : ℝ) (N : ℕ) : ℕ :=
  #{x ∈ (range (N + 1) ×ˢ range (N + 1)) ×ˢ tuples k ⌊Lg X⌋₊ |
      x.1.1.Prime ∧ x.1.2.Prime ∧ N = x.1.1 + x.1.2 + pow2sum x.2}

open Classical in
/-- `r(N) = |{(p1, p2) ∈ 𝔓² : N = p1 + p2}|`, p.2. -/
def rg (N : ℕ) : ℕ :=
  #{x ∈ range (N + 1) ×ˢ range (N + 1) | x.1.Prime ∧ x.2.Prime ∧ x.1 + x.2 = N}

/-- `t_k(N) = |{ν ∈ [1, L]^k : N = 2^{ν1} + ... + 2^{νk}}|`, p.2. -/
def tk (k : ℕ) (X : ℝ) (N : ℕ) : ℕ := #{ν ∈ tuples k ⌊Lg X⌋₊ | pow2sum ν = N}

/-- `t'_k(N)`, the same with `ν ∈ [1, L']^k`, p.2. -/
def tk' (k : ℕ) (X : ℝ) (N : ℕ) : ℕ := #{ν ∈ tuples k ⌊Lp X⌋₊ | pow2sum ν = N}

/-- `R''_k(N) = Σ_{m1, m2 ≤ X, ν ∈ [1,L]^k, m1 + m2 + 2^{ν1} + ... + 2^{νk} = N} Λ(m1) Λ(m2)`,
p.2. `Λ(0) = 0`, so starting `m` at `1` loses nothing. -/
def Rpp (k : ℕ) (X : ℝ) (N : ℕ) : ℝ :=
  ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊, ∑ ν ∈ tuples k ⌊Lg X⌋₊,
    if m1 + m2 + pow2sum ν = N then Λ m1 * Λ m2 else 0

/-- `R(N) = Σ_{m1, m2 ≤ X, m1 + m2 = N} Λ(m1) Λ(m2)`, p.2. -/
def Rg (X : ℝ) (N : ℕ) : ℝ :=
  ∑ m1 ∈ Icc 1 ⌊X⌋₊, ∑ m2 ∈ Icc 1 ⌊X⌋₊, if m1 + m2 = N then Λ m1 * Λ m2 else 0

/-- `𝔖(n) = ∏_{p ∤ n} (1 - 1/(p-1)²) ∏_{p | n} p/(p-1)`, p.2. -/
def sing (n : ℕ) : ℝ :=
  ∏' p : Nat.Primes, if (p : ℕ) ∣ n then (p : ℝ) / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2

/-- `2c0 = 2 ∏_{p > 2} (1 - 1/(p-1)²)`, the twin-prime constant, (2) p.2. -/
def twoC0 : ℝ :=
  2 * ∏' p : Nat.Primes, if (p : ℕ) = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2

/-- (2) p.2: for even `n`, `𝔖(n) = 2c0 ∏_{p | n, p > 2} (p-1)/(p-2)`. We add `n ≠ 0`. -/
def Eq2 : Prop :=
  ∀ n : ℕ, Even n → n ≠ 0 →
    sing n = twoC0 * ∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)

-- (2) is PROVED as `eq2_proof` in `LeanLab/LPZ2007/Elementary.lean`.

/-! ### Section 2, p.3: exponential sums and arcs -/

/-- `e(x) = exp(2πix)`. -/
def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- `S(α) = Σ_{1 ≤ m ≤ X} Λ(m) e(mα)`, p.3. -/
def Sx (X α : ℝ) : ℂ := ∑ m ∈ Icc 1 ⌊X⌋₊, (Λ m : ℂ) * e (m * α)

/-- `G(α) = Σ_{1 ≤ m ≤ L'} e(2^m α)`, p.3. -/
def Gx (X α : ℝ) : ℂ := ∑ m ∈ Icc 1 ⌊Lp X⌋₊, e (2 ^ m * α)

/-- The major arcs `𝔐 = ∪_{q ≤ P} ∪_{a ≤ q, (a,q) = 1} [a/q - 1/(qQ), a/q + 1/(qQ)]`,
`Q = X/P`, p.3. -/
def majorArcs (X P : ℝ) : Set ℝ :=
  {α | ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q ∧
    (a : ℝ) / q - 1 / (q * (X / P)) ≤ α ∧ α ≤ (a : ℝ) / q + 1 / (q * (X / P))}

/-- The minor arcs `𝔪 = [Q^{-1}, 1 + Q^{-1}] \ 𝔐`, p.3. -/
def minorArcs (X P : ℝ) : Set ℝ := Set.Icc (P / X) (1 + P / X) \ majorArcs X P

/-- The range `P ∈ [X^0.4, X^0.41]` of p.3. -/
def PRange (X P : ℝ) : Prop := X ^ (0.4 : ℝ) ≤ P ∧ P ≤ X ^ (0.41 : ℝ)

/-- `R_𝔐(n) = ∫_𝔐 S²(α) e(-nα) dα`, (4) p.3. -/
def RM (X P : ℝ) (n : ℕ) : ℂ := ∫ α in majorArcs X P, Sx X α ^ 2 * e (-(n * α))

/-- `R''_𝔐(N) = ∫_𝔐 S²(α) G^k(α) e(-Nα) dα`, (5) p.4. -/
def RMpp (k : ℕ) (X P : ℝ) (N : ℕ) : ℂ :=
  ∫ α in majorArcs X P, Sx X α ^ 2 * Gx X α ^ k * e (-(N * α))

/-- `R''_𝔪(N) = ∫_𝔪 S²(α) G^k(α) e(-Nα) dα`, (6) p.4. -/
def Rmpp (k : ℕ) (X P : ℝ) (N : ℕ) : ℂ :=
  ∫ α in minorArcs X P, Sx X α ^ 2 * Gx X α ^ k * e (-(N * α))

/-- (3) with (5), (6), p.3-4: `R''_k(N) = R''_𝔐(N) + R''_𝔪(N) + O(N L^{k-1/2} log log N)`
for even `N ∈ J(X)`, every admissible `P`. The real part of the right side is used. -/
def Eq3 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ P : ℝ, PRange X P →
    ∀ N : ℕ, Even N → InJ X N →
      |Rpp k X N - (RMpp k X P N + Rmpp k X P N).re| ≤
        B * N * Lg X ^ ((k : ℝ) - 1 / 2) * Real.log (Real.log N)

/-! ### Section 3, p.4: minor arcs -/

/-- Section 3 p.4: for `α ∈ 𝔪`, `S(α) ≪ X^{4/5} L^4`, from Lemma 6.3. -/
def MinorBound : Prop :=
  ∃ B X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ P : ℝ, PRange X P → ∀ α ∈ minorArcs X P,
    ‖Sx X α‖ ≤ B * X ^ (4 / 5 : ℝ) * Lg X ^ 4

open Classical in
/-- Section 3 p.4: `Σ_{N ∈ J(X)} |R''_𝔪(N)|² ≪ X^{13/5} L^{2k+9}`. -/
def MinorL2 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ P : ℝ, PRange X P →
    ∑ N ∈ (Icc 1 ⌊X⌋₊).filter (fun N : ℕ => 2 * X / 3 ≤ (N : ℝ)), ‖Rmpp k X P N‖ ^ 2 ≤
      B * X ^ (13 / 5 : ℝ) * Lg X ^ (2 * k + 9)

open Classical in
/-- The exceptional set of (7). -/
def Exc7 (k : ℕ) (X P : ℝ) : Finset ℕ :=
  (Icc 1 ⌊X⌋₊).filter (fun N : ℕ => Even N ∧ InJ X N ∧ N * Lg X ^ ((k : ℝ) - 1 / 2) ≤ ‖Rmpp k X P N‖)

/-- (7) p.4: `|{N ∈ J(X) : N even, |R''_𝔪(N)| ≥ N L^{k-1/2}}| ≪ X^{3/5} L^{10}`. -/
def Eq7 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ P : ℝ, PRange X P →
    ((Exc7 k X P).card : ℝ) ≤ B * X ^ (3 / 5 : ℝ) * Lg X ^ 10

/-! ### Section 4, p.4-8: major arcs -/

/-- `L(s, χ)`, with the junk value `0` for modulus `0`. -/
def Lfun {r : ℕ} (χ : DirichletCharacter ℂ r) (s : ℂ) : ℂ :=
  if h : r = 0 then 0 else haveI : NeZero r := ⟨h⟩; DirichletCharacter.LFunction χ s

/-- Zeros in the domain (8) p.4 of `L(s, χ)`, `χ` primitive mod `r ≤ P`:
`ρ = 1 - δ + iγ`, `δ ≤ H / log X`, `|γ| ≤ T`. As a set, so without multiplicity. -/
def EZero (X H T P : ℝ) : Set (Σ r : ℕ, DirichletCharacter ℂ r × ℂ) :=
  {z | 1 ≤ z.1 ∧ (z.1 : ℝ) ≤ P ∧ z.2.1.IsPrimitive ∧ Lfun z.2.1 z.2.2 = 0 ∧
    1 - H / Real.log X ≤ z.2.2.re ∧ |z.2.2.im| ≤ T}

/-- Jutila as quoted p.5: `0 ≤ K ≤ C0 e^{4H}` if `T ≤ P ≤ √X`. Counted without multiplicity,
so weaker than the quote; `H, T ≥ 1` and `X` large added. Jutila's paper not read. -/
def JutilaBound : Prop :=
  ∃ C0 : ℝ, ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X0 : ℝ, ∀ X P : ℝ, X0 ≤ X → T ≤ P → P ≤ √X →
    (EZero X H T P).Finite ∧ ((EZero X H T P).ncard : ℝ) ≤ C0 * Real.exp (4 * H)

/- Jutila 1977, as quoted p.5, cited. -/
/- CODEX task48 preserves the exact JutilaBound Prop above.
Old cited declaration: `theorem jutila : JutilaBound`, with a placeholder proof. -/
/-- Pintz 1976 and Goldfeld-Schinzel 1975 as quoted p.5: if `L(1 - δ, χ) = 0` for real
`δ > 0` and real `χ` mod `r`, then `δ ≫ r^{-1/2}`. -/
def RealZeroBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r, (∀ a, (χ a).im = 0) →
    ∀ δ : ℝ, 0 < δ → Lfun χ (1 - δ) = 0 → c * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ

/- Pintz, Goldfeld-Schinzel as quoted p.5, cited. -/
/- CODEX task48 preserves the exact RealZeroBound Prop above.
Old cited declaration: `theorem realZeroBound : RealZeroBound`, with a placeholder proof. -/

/-- `A(ρ_i)`, p.5: `1` for the pole `ρ_0 = 1`, `-1` for the exceptional zeros. -/
def Aw {K : ℕ} (i : Fin (K + 1)) : ℂ := if i = 0 then 1 else -1

/-- Lemma 4.1 (Explicit Formula), p.5, which is Theorem 10 of Pintz [18], with the paper's
choice `ϑ = 0.41`, `P ∈ [X^{0.4}, X^{0.41}]`. Index `0` is the pole `ρ_0 = 1` of `ζ`, the
primitive character mod 1. The family, the conductors `cond(χ_i χ_j)` and the generalised
singular series `𝔖(χ_i, χ_j, n)` are existential, see the header. -/
def Lemma41 : Prop :=
  ∃ c ε0 B H0 T0 : ℝ, 0 < c ∧ 0 < ε0 ∧ ∃ Cε : ℝ → ℕ, (∀ ε, 1 ≤ Cε ε) ∧ ∀ H T : ℝ, H0 ≤ H → T0 ≤ T →
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∃ P : ℝ, PRange X P ∧
    ∃ (K : ℕ) (r : Fin (K + 1) → ℕ) (χ : (i : Fin (K + 1)) → DirichletCharacter ℂ (r i))
      (ρ : Fin (K + 1) → ℂ) (cond : Fin (K + 1) → Fin (K + 1) → ℕ)
      (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ),
      r 0 = 1 ∧ ρ 0 = 1 ∧ (∀ i, i ≠ 0 → (⟨r i, χ i, ρ i⟩ : Σ r : ℕ, DirichletCharacter ℂ r × ℂ) ∈
        EZero X H T P) ∧
      (∀ n, Sg 0 0 n = sing n) ∧ (∀ i j n, ‖Sg i j n‖ ≤ sing n) ∧
      (∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ i j n,
        ¬ (r i ∣ Cε ε * n ∧ r j ∣ Cε ε * n ∧ (cond i j : ℝ) < ε ^ (-3 : ℤ)) → ‖Sg i j n‖ ≤ ε) ∧
      ∀ n : ℕ, Even n → InJ X n →
        ‖RM X P n - ∑ i, ∑ j, Sg i j n * Aw i * Aw j *
            (Complex.Gamma (ρ i) * Complex.Gamma (ρ j) / Complex.Gamma (ρ i + ρ j)) *
            (n : ℂ) ^ (ρ i + ρ j - 1)‖ ≤ B * (X * Real.exp (-c * H) + X / √T)

/- Lemma 4.1 p.5, Pintz [18] Theorem 10, cited. -/
/- CODEX task48 preserves the exact Lemma41 Prop above.
Old cited declaration: `theorem lemma41 : Lemma41`, with a placeholder proof. -/
/-- `q'`, the product of the odd prime factors of `q` without multiplicity, p.6. -/
def oddRad (q : ℕ) : ℕ := ∏ p ∈ q.primeFactors.filter (2 < ·), p

/-- Corollary 4.2 p.6. For `η` small there are `C*(η)`, `C1(η)` and a family of at most
`C1(η)` exceptional moduli `r_i` with `r_i' ≫ L²` such that for even `n ∈ J(X)`:
`r_i ∤ C*(η) n` for all `i` gives `|R_𝔐(n) - n𝔖(n)| ≤ η n 𝔖(n)`; and always
`R_𝔐(n) ≪ n𝔖(n)`. The moduli are existential, see the header. -/
def Cor42 : Prop :=
  ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 → ∃ (Cstar C1 : ℕ) (c B X0 : ℝ), 1 ≤ Cstar ∧ 0 < c ∧
    ∀ X : ℝ, X0 ≤ X → ∃ P : ℝ, PRange X P ∧ ∃ rs : Finset ℕ, rs.card ≤ C1 ∧
      (∀ r ∈ rs, c * Lg X ^ 2 ≤ oddRad r) ∧
      (∀ n : ℕ, Even n → InJ X n → (∀ r ∈ rs, ¬ r ∣ Cstar * n) →
        ‖RM X P n - n * sing n‖ ≤ η * n * sing n) ∧
      (∀ n : ℕ, Even n → InJ X n → ‖RM X P n‖ ≤ B * n * sing n)

/- Corollary 4.2 p.6, cited. -/
/- CODEX task48 preserves the exact Cor42 Prop above.
Old cited declaration: `theorem cor42 : Cor42`, with a placeholder proof. -/
/-- Davenport Ch. 5 as quoted p.6: a real primitive character mod `r` has `r = A r'`,
`A ∈ {1, 4, 8}`. -/
def RealPrimitiveModulus : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → (∀ a, (χ a).im = 0) →
    r = oddRad r ∨ r = 4 * oddRad r ∨ r = 8 * oddRad r

/- Davenport as quoted p.6, cited. -/
/- CODEX task48 preserves the exact RealPrimitiveModulus Prop above.
Old cited declaration: `theorem realPrimitiveModulus : RealPrimitiveModulus`, with a placeholder proof. -/
/-- Iwaniec's zero-free region as quoted p.6: for non-real primitive `χ` mod `r`, `L(s, χ)` has
no zero with `ℜs > 1 - 1/B`, `B = 4·10^4 (log(2r') + (ℓ log(2ℓ))^{3/4})`, `ℓ = log(r(|t|+2))`. -/
def iwB (r : ℕ) (t : ℝ) : ℝ :=
  let ℓ := Real.log (r * (|t| + 2))
  4 * 10 ^ 4 * (Real.log (2 * oddRad r) + (ℓ * Real.log (2 * ℓ)) ^ (3 / 4 : ℝ))

def IwaniecZeroFree : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → (∃ a, (χ a).im ≠ 0) →
    ∀ s : ℂ, 1 - 1 / iwB r s.im < s.re → Lfun χ s ≠ 0

/- Iwaniec 1974 as quoted p.6, cited; Iwaniec's paper not read. -/
/- CODEX task48 preserves the exact IwaniecZeroFree Prop above.
Old cited declaration: `theorem iwaniec : IwaniecZeroFree`, with a placeholder proof. -/
/-! ### Section 4 p.7-8 and Section 6 p.9: the arithmetic of `C(k, N)` -/

/-- `f(d) = ∏_{p | d, p > 2} (p - 2)^{-1}`, p.7 and Lemma 6.1 p.9. -/
def fd (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors.filter (2 < ·), 1 / ((p : ℝ) - 2)

/-- `ξ(d) = min{μ ≥ 1 : 2^μ ≡ 1 mod d}`, p.8, as the order of `2` mod `d`. -/
def xi (d : ℕ) : ℕ := orderOf (2 : ZMod d)

/-- `d` odd and squarefree, the range of `Σ'`. -/
def OddSqf (d : ℕ) : Prop := Odd d ∧ Squarefree d

open Classical in
/-- The term `f(d)/ξ(d)` of (26), zero off odd squarefree `d`. -/
def romanovTerm (d : ℕ) : ℝ := if OddSqf d then fd d / xi d else 0

/-- `j(d, k, N) = Σ_{1 ≤ ν_i ≤ ξ(d), d | N - 2^{ν1} - ... - 2^{νk}} 1`, (18) p.8. -/
def jd (d k N : ℕ) : ℕ := #{ν ∈ tuples k (xi d) | (d : ℤ) ∣ (N : ℤ) - pow2sum ν}

open Classical in
/-- `C(k, N) = Σ'_{d ≥ 1} f(d) j(d, k, N) / ξ(d)^k`, (23) p.8. -/
def Ckn (k N : ℕ) : ℝ := ∑' d : ℕ, if OddSqf d then fd d * jd d k N / (xi d : ℝ) ^ k else 0

/-- Lemma 6.1 p.9, Romanov [21]: `Σ'_{d ≥ 1} f(d)/ξ(d)` converges. -/
def Lemma61 : Prop := Summable romanovTerm

/- Lemma 6.1 p.9, cited. -/
/- CODEX task48 moved this exact name to Lemma61Port.lean with a proof.
Old cited declaration: `theorem lemma61 : Lemma61`, with a placeholder proof. -/

/-- Khalfallah-Pintz [7] Corollary 1, quoted p.9: the series (26) is at most `1.9378`. -/
def KPBound : Prop := ∑' d, romanovTerm d ≤ 1.9378

/- Khalfallah-Pintz as quoted p.9, cited. -/
/- CODEX task48 preserves the exact KPBound Prop above.
Old cited declaration: `theorem kpBound : KPBound`, with a placeholder proof. -/
open Classical in
/-- Montgomery [15] §17 p.152 as used p.10: `Σ'_{d ≤ D} f(d) ≪ log D`. -/
def MontgomerySum : Prop :=
  ∃ C : ℝ, ∀ D : ℕ, 2 ≤ D → ∑ d ∈ (Icc 1 D).filter OddSqf, fd d ≤ C * Real.log D

/- Montgomery as used p.10, cited. -/
/- CODEX task48 moved this exact name to MontgomerySumProof.lean with a proof.
Old cited declaration: `theorem montgomerySum : MontgomerySum`, with a placeholder proof. -/

open Classical in
/-- `A(m, r) = Σ_{ν ∈ [1, L'], 2^ν < m, r | m - 2^ν} 𝔖(m - 2^ν)`, (13) p.7. -/
def Amr (X : ℝ) (m r : ℕ) : ℝ :=
  ∑ ν ∈ (Icc 1 ⌊Lp X⌋₊).filter (fun ν => 2 ^ ν < m ∧ r ∣ m - 2 ^ ν), sing (m - 2 ^ ν)

/-- Lemma 6.2 p.9 AS PRINTED: `m ∈ [X/2, X]`, `r` odd, `ε > 0` give `A(m, r) ≤ εL`.
Kept as a `def` only: QUESTION Q2, false for `r = 1`. -/
def Lemma62Literal : Prop :=
  ∀ X : ℝ, ∀ m : ℕ, X / 2 ≤ m → (m : ℝ) ≤ X → ∀ r : ℕ, Odd r → ∀ ε : ℝ, 0 < ε →
    Amr X m r ≤ ε * Lg X

/-- Lemma 6.2 p.9 in the form its proof (27)-(30) gives and Section 4 uses with `r ≫ L²`:
for every `ε > 0` there are `r0, X0` with `A(m, r) ≤ εL` for odd `r ≥ r0`, `X ≥ X0`. -/
def Lemma62 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r0 : ℕ, ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ m : ℕ, X / 2 ≤ m → (m : ℝ) ≤ X →
    ∀ r : ℕ, Odd r → r0 ≤ r → Amr X m r ≤ ε * Lg X

/- Lemma 6.2 p.9, repaired form, cited. -/
/- CODEX task48 moved this exact name to Lemma62Port.lean with a proof.
Old cited declaration: `theorem lemma62 : Lemma62`, with a placeholder proof. -/

/-- Lemma 6.3 p.10, Vaughan [22] Theorem 3.1: for `q ≤ X`, `(a, q) = 1`, `|α - a/q| < q^{-2}`,
`S(α) ≪ (X/√q + √(Xq) + X^{4/5}) log^4 X`. We add `X ≥ 2`. -/
def Lemma63 : Prop :=
  ∃ B : ℝ, ∀ X : ℝ, 2 ≤ X → ∀ α : ℝ, ∀ a q : ℕ, 1 ≤ q → (q : ℝ) ≤ X → Nat.Coprime a q →
    |α - a / q| < 1 / (q : ℝ) ^ 2 →
      ‖Sx X α‖ ≤ B * (X / √q + √(X * q) + X ^ (4 / 5 : ℝ)) * Real.log X ^ 4

/-- Lemma 6.3 p.10, proved from the lab Vaughan bound with constant 24300. -/
theorem lemma63 : Lemma63 := by
  refine ⟨24300, fun X hX α a q hq hqX hcop happrox => ?_⟩
  let N := ⌊X⌋₊
  have hX0 : 0 < X := by linarith
  have hNX : (N : ℝ) ≤ X := Nat.floor_le hX0.le
  have hqN : q ≤ N := Nat.le_floor hqX
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hNr : (1 : ℝ) ≤ N := by
    exact_mod_cast (hq.trans hqN)
  have hcop' : IsCoprime (a : ℤ) (q : ℤ) := by
    rwa [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
  have happrox' : |α - (a : ℤ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
    simpa only [NNRat.cast_divNat, Int.cast_natCast] using happrox.le
  have hv := LeanLab.PNTPort.Vinogradov.vinogradov_minor hq hcop' happrox' hqN
  have hS : Sx X α = LeanLab.PNTPort.Vinogradov.S N α := by
    unfold Sx LeanLab.PNTPort.Vinogradov.S
    apply sum_congr rfl
    intro m _
    congr 1
    unfold e LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  rw [hS]
  have hlX : 0 ≤ log X := log_nonneg (by linarith)
  have hlog : 1 + log N ≤ 3 * log X := by
    have h1 := log_le_log (by linarith : (0 : ℝ) < N) hNX
    have h2 := log_le_log (by norm_num : (0 : ℝ) < 2) hX
    linarith [Real.log_two_gt_d9]
  have hpow : (1 + log N) ^ 4 ≤ 81 * log X ^ 4 := by
    calc (1 + log N) ^ 4 ≤ (3 * log X) ^ 4 :=
        pow_le_pow_left₀ (by linarith [log_nonneg hNr]) hlog 4
      _ = 81 * log X ^ 4 := by ring
  have ht1 : (N : ℝ) / √q ≤ X / √q := by
    exact div_le_div_of_nonneg_right hNX (sqrt_nonneg _)
  have ht2 : (N : ℝ) ^ (4 / 5 : ℝ) ≤ X ^ (4 / 5 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNX (by norm_num)
  have ht3 : √((N : ℝ) * q) ≤ √(X * q) :=
    sqrt_le_sqrt (mul_le_mul_of_nonneg_right hNX hqr.le)
  have hbase : (N : ℝ) / √q + (N : ℝ) ^ (4 / 5 : ℝ) + √((N : ℝ) * q) ≤
      X / √q + √(X * q) + X ^ (4 / 5 : ℝ) := by linarith
  calc ‖LeanLab.PNTPort.Vinogradov.S N α‖ ≤
      300 * ((N : ℝ) / √q + (N : ℝ) ^ (4 / 5 : ℝ) + √((N : ℝ) * q)) *
        (1 + log N) ^ 4 := hv
    _ ≤ 300 * (X / √q + √(X * q) + X ^ (4 / 5 : ℝ)) * (81 * log X ^ 4) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hbase (by norm_num)
      · exact hpow
      · positivity
      · positivity
    _ = 24300 * (X / √q + √(X * q) + X ^ (4 / 5 : ℝ)) * log X ^ 4 := by ring


/-- (25) p.8: `R''_𝔐(N) = C(k, N) N L^k (1 + O(η))` for every even `N ∈ J(X)`, without
exceptions, with the `P` of Lemma 4.1. Preprint constant, see QUESTION Q3. -/
def Eq25 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
    ∃ P : ℝ, PRange X P ∧ ∀ N : ℕ, Even N → InJ X N →
      ‖RMpp k X P N - Ckn k N * N * Lg X ^ k‖ ≤ B * η * N * Lg X ^ k

/- (25) p.8 as printed is NOT cited any more: VERIFY U-0999, run 20261019T0202Z-9877, agreed
with F-0038 that the printed constant lacks `2c0`, so `Eq25` is false if F-0038 holds and a
a placeholder proof for it made the module inconsistent. The cited input is `eq25_twoC0` in Repaired.lean.
Old line, kept as text: `theorem eq25 : Eq25`, with a placeholder proof. -/

/-! ### The Theorem, p.2, and Section 5, p.9 -/

open Classical in
/-- Even `N ∈ J(X)` violating `|R''_k(N) - C(k,N) N L^k| ≤ η N L^k`. -/
def ExcJ (k : ℕ) (X η : ℝ) : Finset ℕ :=
  (Icc 1 ⌊X⌋₊).filter (fun N : ℕ => Even N ∧ InJ X N ∧
    η * N * Lg X ^ k < |Rpp k X N - Ckn k N * N * Lg X ^ k|)

/-- Section 5 p.9, the form the proof gives: for `k ≥ 1` there is `B` with, for every `η > 0`
and `X > X0(k, η)`, at most `B X^{3/5} (log X)^{10}` even `N ∈ J(X)` with
`|R''_k(N) - C(k,N) N L^k| > η N L^k`. -/
def MainJ : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
    ((ExcJ k X η).card : ℝ) ≤ B * X ^ (3 / 5 : ℝ) * Real.log X ^ 10

/- The paper's Theorem p.2 and Section 5 p.9, on `J(X)`, preprint constant `C(k, N)`, is NOT
cited any more: false if F-0038 holds, see the note at (25). The repaired Theorem is
`lpz_main_J_twoC0` in Repaired.lean, CONDITIONAL ON `eq3`, `eq7`, `eq25_twoC0`.
Old line, kept as text: `theorem lpz_main_J : MainJ`, with a placeholder proof. -/

open Classical in
/-- The Theorem p.2 AS PRINTED: all even `N ∈ [1, X]`, `L = log_2 X`. A `def` only,
QUESTION Q1: for `N ≈ X^{1/2}` the size is `N (log_2 N)^k`, not `N L^k`. -/
def MainLiteral : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
    (((Icc 1 ⌊X⌋₊).filter (fun N : ℕ => Even N ∧
      η * N * Lg X ^ k < |Rpp k X N - Ckn k N * N * Lg X ^ k|)).card : ℝ) ≤
        B * X ^ (3 / 5 : ℝ) * Real.log X ^ 10

open Classical in
/-- The Theorem p.2 read through its dyadic remark p.3: all even `N ∈ [1, X]` with
`log_2 N` in place of `L`. A `def`; it should follow from `MainJ` by the dyadic argument. -/
def MainDyadic : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
    (((Icc 1 ⌊X⌋₊).filter (fun N : ℕ => Even N ∧
      η * N * Lg (N : ℝ) ^ k < |Rpp k X N - Ckn k N * N * Lg (N : ℝ) ^ k|)).card : ℝ) ≤
        B * X ^ (3 / 5 : ℝ) * Real.log X ^ 10

open Classical in
/-- `MainJ` with the factor `2c0` that QUESTION Q3 says (17) dropped. A `def` only. -/
def MainJ_twoC0 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
    (((Icc 1 ⌊X⌋₊).filter (fun N : ℕ => Even N ∧ InJ X N ∧
      η * N * Lg X ^ k < |Rpp k X N - twoC0 * Ckn k N * N * Lg X ^ k|)).card : ℝ) ≤
        B * X ^ (3 / 5 : ℝ) * Real.log X ^ 10

/-- Gallagher [2] as quoted p.1: for `k ≥ 2` and even `N ≥ N_k`,
`r''_k(N) = 2 N log_2^k N / log² N (1 + O(log² k / k))`, `O` absolute. Gallagher not read. -/
def GallagherAsymp : Prop :=
  ∃ A : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Even N → Nk ≤ N →
    |(rpp k N N : ℝ) - 2 * N * Lg (N : ℝ) ^ k / Real.log N ^ 2| ≤
      A * (Real.log k ^ 2 / k) * (2 * N * Lg (N : ℝ) ^ k / Real.log N ^ 2)

/- Gallagher 1975 as quoted p.1, cited. -/
/- CODEX task48 preserves the exact GallagherAsymp Prop above.
Old cited declaration: `theorem gallagherAsymp : GallagherAsymp`, with a placeholder proof. -/
end LeanLab.LPZ2007

