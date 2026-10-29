module

public import LeanLab.BS2022GRH.U7154UN
public import LeanLab.BS2022GRH.RangeCheck13375
public import LeanLab.AlmostPrimeSums.Statements

/-!
BS2022GRH, P0021, idea I-0088, unit U-1561, PC run 20261026T2003Z-2973: the GRH Chen THRESHOLD
itself, stated, and the journal's chain of results as named leaves.

Source: Bordignon, Starichkova, An explicit version of Chen's theorem assuming the Generalized
Riemann Hypothesis, The Ramanujan Journal 64 (2024) 1213-1242, repo copy papers/P0021-journal.pdf,
read from its text layer, from page images rendered this run (pp. 1214, 1221, 1227, 1239, 1240)
and from the PC file `Lean Lab/papers/I-0088 GRH Chen threshold/journal_extract.md`.

The journal's Corollary 1, p. 1214: every even integer N > exp(exp(14)) can be represented as the
sum of a prime and a square-free number η > 1 with at most two prime factors, under GRH.
The lab's I-0088 line re-chooses the Section 5.4 parameters inside the authors' method,
α₁ = α₂ = α₃ = 0.00256, A = 10, u = 1500, ε = 1/8349, C₁ = 112, C₂ = 114, ε₁ = 10⁻²⁰, and gets the
same conclusion for every even N ≥ exp(exp 13.375), `ChenThreshold13375`.

Leaves, with GRH as an explicit argument where the paper assumes it:
* `LinearSieveT4`, Theorem 4 p. 1218 with Table 1 pp. 1217-1218, restricted to the ranges used.
* `Lemma3J`, Lemma 3 p. 1215, GRH primes in progressions.
* `epsJ` display (6) and `Lemma7J`, Lemma 7 p. 1221; `Eps1500`, ε(1500) < 1/8349.
* `Lemma9J`, Lemma 9 p. 1227, Chen's weighted inequality: PROVED, from `U7153.lemma10`.
* `Thm5J`, `Thm6J`, `Thm7J`, Theorems 5, 6, 7, pp. 1228, 1231, 1234-1235.
* `Bracket13375`, the Section 5.4 combination of the three exact brackets at the new parameters
  is at least `Journal.K3J` − 10⁻⁵, a one-sided lower bound; PROVED in Cert1567.
* `section55_step`, Section 5.5 p. 1241, π₂'(N) ≥ π₂(N) − √N − 1: PROVED.

`chenThreshold13375_of_leaves`: the threshold, CONDITIONAL ON `Thm5J`, `Thm6J`, `Thm7J`,
`LinearSieveT4 (1/8349) 112 114`, `Eps1500` and `Bracket13375`; it uses the PROVED
`Journal.theorem3_positive_main`, `Journal.conditions_13375`, `Journal.display25_first`,
`Journal.display25_third`, `U7153.lemma10`, `two_fifths_le_UNfull`.
The derivation of Theorems 5, 6, 7 from GRH, Sections 4 and 5.1 to 5.3 of the paper, is OPEN in
the lab; the lab's unproved placeholder for it is removed from this copy.

Normalisation: the journal prints U_N = e^{-γ} ∏_{p>2}(1 − 1/(p−1)²) ∏_{p>2, p|N}(p−1)/(p−2),
pp. 1214 and 1227, while V(x) = ∏_{p<x, p∤N}(1 − 1/(p−1)) is asymptotic to 2e^{-γ}C₂Π_N/log x by
Mertens. The leaves use the lab's `UNfull = ChenExplicit.U = 2e^{-γ}C₂Π_N`; the printed
(e^{-γ}C₂)^{-1} in the negligible error terms is kept, which only weakens those bounds.

AI-written Lean code, Claude, for the Lean Lab, PC run 20261026T2003Z-2973, unit U-1561.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH.ChenThresholdGRH
open Real Finset Classical

/-- GRH for Dirichlet L-functions, the lab's existing predicate. -/
abbrev GRH : Prop := LeanLab.DERZ1997.GRH

/-! ### The threshold statements -/

/-- η > 1, square-free, with at most two prime factors: Corollary 1's summand, p. 1214. -/
def IsSqfreeP2 (m : ℕ) : Prop :=
  1 < m ∧ Squarefree m ∧ ArithmeticFunction.cardFactors m ≤ 2

/-- `N = p + η` with `p` prime and `η` as in `IsSqfreeP2`. -/
def ChenSqfreeRep (N : ℕ) : Prop := ∃ p m : ℕ, p.Prime ∧ N = p + m ∧ IsSqfreeP2 m

/-- **Journal Corollary 1, p. 1214**, CITED: under GRH every even N > exp(exp 14) is p + η. -/
def CorollaryOneJ : Prop :=
  GRH → ∀ N : ℕ, Even N → exp (exp 14) < (N : ℝ) → ChenSqfreeRep N

/-- **The I-0088 threshold**: under GRH every even N ≥ exp(exp 13.375) is a prime plus a
square-free η > 1 with at most two prime factors. -/
def ChenThreshold13375 : Prop :=
  GRH → ∀ N : ℕ, Even N → exp (exp 13.375) ≤ (N : ℝ) → ChenSqfreeRep N

/-- The same with only `Ω m ≤ 2`, `m ≠ 0`, prime factors counted with multiplicity. -/
def ChenThreshold13375Omega : Prop :=
  GRH → ∀ N : ℕ, Even N → exp (exp 13.375) ≤ (N : ℝ) →
    ∃ p m : ℕ, p.Prime ∧ N = p + m ∧ Nat.IsAtMostAlmostPrime 2 m

/-! ### Display (6) and Lemma 7, p. 1221 -/

/-- Display (6): ε(u₀) = exp(1.131·10⁻⁷ + (u₀/(u₀ − 2) + 0.501) Σ_{p ≥ u₀} 1/p²) − 1. -/
noncomputable def epsJ (u : ℝ) : ℝ :=
  exp (1.131e-7 + (u / (u - 2) + 0.501) *
    ∑' p : {p : ℕ // p.Prime ∧ u ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2) - 1

/-- **Lemma 7 with display (6)**, CITED: for z > exp 2753 and 400 ≤ u₀ ≤ u < z,
∏_{u ≤ p < z} (1 − 1/(p − 1))⁻¹ < (1 + ε(u₀)) log z / log u, and ε(u₀) < 1/63. -/
def Lemma7J : Prop :=
  ∀ z u₀ u : ℝ, exp 2753 < z → 400 ≤ u₀ → u₀ ≤ u → u < z →
    (∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - 1 / ((p : ℝ) - 1))⁻¹ < (1 + epsJ u₀) * (log z / log u)) ∧ epsJ u₀ < 1 / 63

/-- **ε(1500) < 1/8349**, numeric certificate, proved in this entry; value 1/8349.32 by U-1172. -/
def Eps1500 : Prop := epsJ 1500 < 1 / 8349

/-! ### Lemma 3, p. 1215 -/

/-- **Lemma 3**, CITED from Ernvall-Hytönen and Palojärvi: under GRH, for 3 ≤ d ≤ √X₂,
N ≥ X₂ and (a, d) = 1, |π(N; d, a) − li(N)/φ(d)| ≤ q_G(X₂) √N log N. -/
def Lemma3J : Prop :=
  GRH → ∀ (d a : ℕ) (X₂ N : ℝ), 3 ≤ d → (d : ℝ) ≤ √X₂ → X₂ ≤ N → Nat.Coprime a d →
    |((((range (⌊N⌋₊ + 1)).filter (fun p => p.Prime ∧ p % d = a % d)).card : ℕ) : ℝ)
        - liPV N / (d.totient : ℝ)| ≤ qG X₂ * √N * log N

/-! ### Theorem 4, the linear sieve, p. 1218, with Table 1 -/

/-- **Theorem 4**, CITED from [1, Theorem 6 and Table 1], in the ranges the paper uses:
F(s) = 2e^γ/s for 1 ≤ s ≤ 3 and f(s) = 2e^γ log(s − 1)/s for 2 ≤ s ≤ 4. Finite support,
g_n(d) = ∏_{p | d} g_n(p), Q a finite subset of the sifting primes, condition (2) with ε.
Conclusions with ≤ and ≥ in place of the printed < and >. -/
def LinearSieveT4 (ε C₁ C₂ : ℝ) : Prop :=
  ∀ (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℕ → ℝ) (z D : ℝ),
    (∀ n, 0 ≤ a n) → (∀ n, n ∉ supp → a n = 0) → (∀ p ∈ P, p.Prime) → (↑Q ⊆ P) →
    (∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) → 0 < ε → ε < 1 / 63 → 2 ≤ z →
    (∀ n u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g n p)⁻¹ ≤ (1 + ε) * (log z / log u)) →
    let Pz := (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ (p : ℝ) < z)
    let S := ∑ n ∈ supp.filter (fun n => ∀ p ∈ Pz, ¬ p ∣ n), a n
    let X := ∑ n ∈ supp, a n * ∏ p ∈ Pz, (1 - g n p)
    let r := fun d : ℕ => (∑ n ∈ supp.filter (fun n => d ∣ n), a n)
      - ∑ n ∈ supp, a n * ∏ p ∈ d.primeFactors, g n p
    let R := ∑ T ∈ Pz.powerset.filter (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < (∏ p ∈ Q, p : ℕ) * D),
      |r (∏ p ∈ T, p)|
    let s := log D / log z
    (z ≤ D → s ≤ 3 → S ≤ (2 * exp eulerMascheroniConstant / s + ε * C₁ * exp 2 * hS s) * X + R) ∧
    (z ^ 2 ≤ D → s ≤ 4 →
      (2 * exp eulerMascheroniConstant * log (s - 1) / s - ε * C₂ * exp 2 * hS s) * X - R ≤ S)

/-! ### Constants of Lemmas 5, 12, 13 and display (31) -/

/-- p_G of Lemma 12, p. 1229. -/
noncomputable def pGJ (X : ℝ) : ℝ := 0.608 * (0.02 + qG X)
/-- c_G of Lemma 13, p. 1230. -/
noncomputable def cGJ (X : ℝ) : ℝ := pGJ X + 0.85 / (√X * log (log X))
/-- M_φ of Lemma 5, p. 1216. -/
noncomputable def Mphi (x : ℝ) : ℝ :=
  1 + 1.333 / log x + min (2.44 / (√x * log x)) (11 / (√x * log x ^ 2))
/-- M_{φ₀}(Y) = M_φ((√Y/(2 log 2 q_G(Y) log Y))^{1/3}), Lemma 8, p. 1223. -/
noncomputable def Mphi0 (Y : ℝ) : ℝ :=
  Mphi ((√Y / (2 * log 2 * qG Y * log Y)) ^ (1 / 3 : ℝ))
/-- m̄(N, A, w), display (31), pp. 1239-1240, with D* = √N / log^{A+1} N. -/
noncomputable def mbarJ (N A w : ℝ) : ℝ :=
  2 * Mphi (√N / log N ^ (A + 1)) *
    (2 / log 2 + qG w ^ (1 / 3 : ℝ) * (2 * log 2) ^ (-(2 / 3) : ℝ) *
        (2 ^ (1 / 3 : ℝ) * log N ^ (A + 1) * log (2 * w) ^ (1 / 3 : ℝ) / w ^ (1 / 6 : ℝ)) *
        (1 + Mphi0 w)
      + log N ^ (A + 1) * (w ^ (-(1 / 2) : ℝ) + (2 * w / N) ^ (1 / 2 : ℝ)) / log 2
      + Mphi0 w * ((2 * qG (2 * w) * log 2) ^ (-(2 / 3) : ℝ) *
          (log N ^ (A + 1) / (w ^ (2 / 3 : ℝ) * log w ^ (2 / 3 : ℝ)))
        + 0.69205 * (2 * qG (2 * w) * log 2) ^ (-(1 / 3) : ℝ) *
          (log N ^ (A + 2) / (2 * w ^ (5 / 6 : ℝ) * log w ^ (1 / 3 : ℝ) *
            log (log √N - (A + 1) * log (log N))))))

/-- (e^{-γ} ∏_{p>2}(1 − 1/(p−1)²))⁻¹, as printed in Theorems 5, 6, 7. -/
noncomputable def invTw : ℝ := (exp (-eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC)⁻¹

/-! ### The brackets of Theorems 5, 6, 7 -/

/-- Theorem 5's bracket, p. 1228. -/
noncomputable def B5J (α A ε C₂ X₂ N : ℝ) : ℝ :=
  (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) *
      (2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α)
        - ε * C₂ * (3 * exp (8 * α - 2) / (4 - 8 * α)))
    - 1 / 8 * (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))⁻¹ * invTw * cGJ X₂ / log N ^ (A - 2)

/-- Theorem 6's l₁, p. 1231. -/
noncomputable def l1J (α ε C₁ X₂ : ℝ) : ℝ :=
  (1 + 5e-5) * (1 + 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) * rX X₂ *
    (exp eulerMascheroniConstant / 4 *
        ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) + 512 / (kA α * log X₂ ^ 2))
      + (log (8 / 3) + 64 / log X₂ ^ 2) * ε * C₁ * exp 2 * hS (kA α))
/-- Theorem 6's l₂. -/
noncomputable def l2J (X₂ : ℝ) : ℝ := cGJ X₂ / 8 * (0.50007 + 1 / log X₂) * invTw
/-- Theorem 6's l₃. -/
noncomputable def l3J (α ε C₁ X₂ : ℝ) : ℝ :=
  (1 + 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) *
    (2 * exp eulerMascheroniConstant / kA α + ε * C₁ * exp 2 * hS (kA α)) * cGJ X₂
/-- Theorem 6's bracket l₁ + l₂/log^{A−3} N + l₃/log^{A−1} N. -/
noncomputable def B6J (α A ε C₁ X₂ N : ℝ) : ℝ :=
  l1J α ε C₁ X₂ + l2J X₂ / log N ^ (A - 3) + l3J α ε C₁ X₂ / log N ^ (A - 1)

/-- Theorem 7's bracket, pp. 1234-1235; it depends on X₂, not on N. -/
noncomputable def B7J (α A ε C₁ X₂ ε₁ : ℝ) : ℝ :=
  (1 + 0.06 * log X₂ / X₂ ^ (1 / 6 : ℝ)) *
      (2 / (1 / 2 - α) * exp eulerMascheroniConstant + 3 * ε * C₁) * (1 + ε₁) *
      (log (X₂ ^ (1 / 3 : ℝ)) * (liPV (X₂ ^ (1 / 3 : ℝ))
        + X₂ ^ (1 / 6 : ℝ) * log (X₂ ^ (1 / 3 : ℝ)) / (8 * π)) / X₂ ^ (1 / 3 : ℝ)) *
      (LeanLab.ChenExplicit.BJS.cbar + 36 / log X₂ ^ 2 + (log (8 / 3) + 64 / log X₂ ^ 2) *
        (log √(1 + ε₁) / (log (X₂ ^ (1 / 3 : ℝ)) ^ 2 - log √(1 + ε₁) ^ 2) + 27 / log X₂ ^ 2))
    + invTw * (1 + ε₁) / (log (1 + ε₁) * log X₂ ^ (A - 4)) *
      (0.053 * mbarJ X₂ A (X₂ ^ (1 / 8 : ℝ)) * (1 + ε₁) ^ (-(1 / 2) : ℝ)
        + 0.08 * X₂ ^ (-(1 / 8) : ℝ) * log X₂ ^ (A + 1))

/-! ### Conditions (19), (21), (25) -/

/-- (19) and (21) without the range of α: log X₂ ≥ (A+1)/α, X₂^α/log^{A+1} X₂ ≥ e^u,
400 ≤ u ≤ 10⁸. -/
def Cond19 (α A u X₂ : ℝ) : Prop :=
  (A + 1) / α ≤ log X₂ ∧ exp u ≤ X₂ ^ α / log X₂ ^ (A + 1) ∧ 400 ≤ u ∧ u ≤ 1e8

/-- (25) without the range of α. -/
def Cond25 (α A u X₂ : ℝ) : Prop :=
  max ((A + 1) / α) (48 * (A + 4 / 3)) ≤ log X₂ ∧ exp u ≤ X₂ ^ α / log X₂ ^ (A + 1) ∧
    0.44 ≤ X₂ ^ (1 / 48 : ℝ) / log X₂ ^ (A + 4 / 3) ∧ 400 ≤ u ∧ u ≤ 1e8

/-! ### Theorems 5, 6, 7, CITED, with GRH and the linear sieve as arguments -/

/-! Version 2 change, decided 2026-10-28 with Steve Hubbard: each of `Thm5J`, `Thm6J`, `Thm7J`
now also takes `0 ≤ C₁ → 0 ≤ C₂ →` right after the sieve hypothesis. Table 1 of the paper gives
positive C₁, C₂ only, so this is faithful; it costs the instance at C₁ = 112, C₂ = 114 nothing, and
it closes any route where a sieve witness with a negative constant would make B5J or B6J
degenerate. -/

/-- **Theorem 5**, p. 1228: S(A, ℙ, z) > 8 U_N N/log² N · B5. -/
def Thm5J : Prop :=
  ∀ (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ), GRH → LinearSieveT4 ε C₁ C₂ → 0 ≤ C₁ → 0 ≤ C₂ → epsJ u ≤ ε → 0 < ε → ε < 1 / 63 →
    0 < α → α < 1 / 8 → 0 < A → Cond19 α A u X₂ → 4e18 ≤ X₂ → X₂ ≤ (n : ℝ) → Even n →
    8 * (UNfull n * n / log n ^ 2) * B5J α A ε C₂ X₂ n < (U7153.SA n : ℝ)

/-- **Theorem 6**, pp. 1231-1232: Σ_{z ≤ q < y, q ∤ N} S(A_q, ℙ, z) ≤ 8 U_N N/log² N · B6. -/
def Thm6J : Prop :=
  ∀ (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ), GRH → LinearSieveT4 ε C₁ C₂ → 0 ≤ C₁ → 0 ≤ C₂ → epsJ u ≤ ε → 0 < ε → ε < 1 / 63 →
    0 < α → α < 1 / 24 → 0 < A → Cond19 α A u X₂ → exp (exp 10) ≤ X₂ → X₂ ≤ (n : ℝ) → Even n →
    ∑ q ∈ (U7153.Qset n).filter (fun q => ¬ q ∣ n), (U7153.SAq n q : ℝ)
      ≤ 8 * (UNfull n * n / log n ^ 2) * B6J α A ε C₁ X₂ n

/-- **Theorem 7**, pp. 1234-1235: S(B, ℙ, y) ≤ U_N N/log² N · B7. -/
def Thm7J : Prop :=
  ∀ (α A u ε C₁ C₂ X₂ ε₁ : ℝ) (n : ℕ), GRH → LinearSieveT4 ε C₁ C₂ → 0 ≤ C₁ → 0 ≤ C₂ → epsJ u ≤ ε → 0 < ε → ε < 1 / 63 →
    0 < ε₁ → ε₁ < 1 → 0 < α → α < 1 / 16 → 0 < A → Cond25 α A u X₂ → exp (exp 10) ≤ X₂ →
    X₂ ≤ (n : ℝ) → Even n →
    (U7153.SB n : ℝ) ≤ UNfull n * n / log n ^ 2 * B7J α A ε C₁ X₂ ε₁

/-! ### Lemma 9, p. 1227, PROVED -/

/-- **Lemma 9**, Chen's weighted inequality. -/
def Lemma9J : Prop :=
  ∀ n : ℕ, (2 : ℝ) ^ 24 ≤ n →
    (U7153.SA n : ℝ) - 1 / 2 * ∑ q ∈ U7153.Qset n, (U7153.SAq n q : ℝ) - 1 / 2 * (U7153.SB n : ℝ)
      - 2 * (n : ℝ) ^ (7 / 8 : ℝ) - (n : ℝ) ^ (1 / 3 : ℝ) < U7153.pi2 n

theorem lemma9J_holds : Lemma9J := fun n hn => U7153.lemma10 n hn

/-! ### Section 5.4 combination at the new parameters, numeric certificate -/

/-- **The bracket certificate**, proved in this entry: at α = 0.00256, A = 10, ε = 1/8349, C₁ = 112,
C₂ = 114, ε₁ = 10⁻²⁰, X₂ = exp(exp 13.375), the combination 8·B5 − ½·8·B6 − ½·B7 of the exact
brackets is at least K3J − 10⁻⁵ for every N ≥ X₂. Python total 1.535·10⁻⁴ against K3J 1.596·10⁻⁴. -/
def Bracket13375 : Prop :=
  ∀ n : ℕ, exp (exp 13.375) ≤ (n : ℝ) →
    Journal.K3J 0.00256 (exp eulerMascheroniConstant) (1 / 8349) 112 114
        LeanLab.ChenExplicit.BJS.cbar - 1e-5
      ≤ 8 * B5J 0.00256 10 (1 / 8349) 114 (exp (exp 13.375)) n
        - 1 / 2 * (8 * B6J 0.00256 10 (1 / 8349) 112 (exp (exp 13.375)) n)
        - 1 / 2 * B7J 0.00256 10 (1 / 8349) 112 (exp (exp 13.375)) 1e-20

/-! ### Section 5.5, PROVED -/

/-- π₂'(N): primes p < N with N − p a square-free prime or product of two primes. -/
noncomputable def pi2' (n : ℕ) : ℕ :=
  ((range n).filter (fun p => p.Prime ∧ U7153.IsP2 (n - p) ∧ Squarefree (n - p))).card

lemma sq_of_P2_not_sqfree {m : ℕ} (h : U7153.IsP2 m) (hns : ¬ Squarefree m) :
    ∃ q : ℕ, q.Prime ∧ m = q * q := by
  rcases h with hp | ⟨a, b, ha, hb, rfl⟩
  · exact absurd hp.prime.squarefree hns
  · by_cases hab : a = b
    · exact ⟨a, ha, by rw [hab]⟩
    · exfalso; apply hns
      rw [Nat.squarefree_mul_iff]
      exact ⟨(Nat.coprime_primes ha hb).2 hab, ha.prime.squarefree, hb.prime.squarefree⟩

/-- **Section 5.5**, p. 1241: π₂'(N) ≥ π₂(N) − √N − 1. -/
theorem section55_step (n : ℕ) : (U7153.pi2 n : ℝ) - √(n : ℝ) - 1 ≤ pi2' n := by
  have key : U7153.pi2 n ≤ pi2' n + Nat.sqrt n := by
    unfold U7153.pi2 pi2'
    set F := (range n).filter (fun p => p.Prime ∧ U7153.IsP2 (n - p)) with hF
    have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun p => Squarefree (n - p))
    have h1 : (F.filter (fun p => Squarefree (n - p))).card ≤
        ((range n).filter (fun p => p.Prime ∧ U7153.IsP2 (n - p) ∧ Squarefree (n - p))).card := by
      apply Finset.card_le_card
      intro p hp
      simp only [hF, Finset.mem_filter] at hp ⊢
      exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2, hp.2⟩
    have h2 : (F.filter (fun p => ¬ Squarefree (n - p))).card ≤ Nat.sqrt n := by
      have hmem : ∀ p ∈ F.filter (fun p => ¬ Squarefree (n - p)),
          p < n ∧ ∃ q : ℕ, q.Prime ∧ n - p = q * q := by
        intro p hp
        simp only [hF, Finset.mem_filter, Finset.mem_range] at hp
        exact ⟨hp.1.1, sq_of_P2_not_sqfree hp.1.2.2 hp.2⟩
      calc (F.filter (fun p => ¬ Squarefree (n - p))).card
          ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
            apply Finset.card_le_card_of_injOn (fun p => Nat.sqrt (n - p))
            · intro p hp
              obtain ⟨hpn, q, hq, hsq⟩ := hmem p hp
              simp only [Finset.coe_Icc, Set.mem_Icc]
              rw [hsq, Nat.sqrt_eq]
              refine ⟨hq.one_lt.le, Nat.le_sqrt.2 ?_⟩
              omega
            · intro p hp p' hp' heq
              obtain ⟨hpn, q, hq, hsq⟩ := hmem p hp
              obtain ⟨hpn', q', hq', hsq'⟩ := hmem p' hp'
              simp only [hsq, hsq', Nat.sqrt_eq] at heq
              subst heq
              omega
        _ = Nat.sqrt n := by simp
    omega
  have hs : (Nat.sqrt n : ℝ) ≤ √(n : ℝ) := Real.nat_sqrt_le_real_sqrt
  have : (U7153.pi2 n : ℝ) ≤ pi2' n + Nat.sqrt n := by exact_mod_cast key
  linarith

/-- A positive π₂'(N) gives the representation of Corollary 1. -/
lemma rep_of_pi2' {n : ℕ} (h : 0 < pi2' n) : ChenSqfreeRep n := by
  unfold pi2' at h
  obtain ⟨p, hp⟩ := Finset.card_pos.1 h
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpn, hpr, hP2, hsq⟩ := hp
  refine ⟨p, n - p, hpr, by omega, ?_, hsq, ?_⟩
  · rcases hP2 with hq | ⟨a, b, ha, hb, hab⟩
    · exact hq.one_lt
    · rw [hab]; nlinarith [ha.two_le, hb.two_le]
  · rcases hP2 with hq | ⟨a, b, ha, hb, hab⟩
    · rw [ArithmeticFunction.cardFactors_apply_prime hq]; norm_num
    · rw [hab, ArithmeticFunction.cardFactors_mul ha.ne_zero hb.ne_zero,
        ArithmeticFunction.cardFactors_apply_prime ha, ArithmeticFunction.cardFactors_apply_prime hb]

/-! ### Theorem 6's sum over q ∤ N equals Lemma 9's sum over all q -/

lemma SAq_eq_zero {n q : ℕ} (hq : q.Prime) (hqn : q ∣ n) : U7153.SAq n q = 0 := by
  unfold U7153.SAq
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a ha hqa
  unfold U7153.Aset at ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpn, hpr, hpN⟩ := hp
  have h1 : q ∣ n - (n - p) := Nat.dvd_sub hqn hqa.1
  rw [Nat.sub_sub_self (by omega)] at h1
  have : q = p := (Nat.prime_dvd_prime_iff_eq hq hpr).1 h1
  exact hpN (this ▸ hqn)

lemma sum_Qset_filter (n : ℕ) :
    ∑ q ∈ (U7153.Qset n).filter (fun q => ¬ q ∣ n), (U7153.SAq n q : ℝ)
      = ∑ q ∈ U7153.Qset n, (U7153.SAq n q : ℝ) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : q ∣ n
  · rw [SAq_eq_zero (Finset.mem_filter.1 hq).2.1 h]; simp
  · simp [h]

/-! ### The parameters at log log X₂ = 13.375, PROVED, vacuity of the leaves' hypotheses -/

lemma exp44_ge : (4e18 : ℝ) ≤ exp 44 := by
  have h1 := Real.exp_one_gt_d9
  have e : exp (44 : ℝ) = exp 1 ^ 44 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : (2.7182818283 : ℝ) ^ 44 ≤ exp 1 ^ 44 := pow_le_pow_left₀ (by norm_num) h1.le 44
  have h2 : (4e18 : ℝ) ≤ 2.7182818283 ^ 44 := by norm_num
  linarith

theorem X2_ranges : (4e18 : ℝ) ≤ exp (exp 13.375) ∧ exp (exp 10) ≤ exp (exp 13.375) := by
  have h := Journal.exp13375_ge
  refine ⟨exp44_ge.trans (exp_le_exp.2 (by linarith)), ?_⟩
  exact exp_le_exp.2 (exp_le_exp.2 (by norm_num))

lemma ratio_exp (α B c : ℝ) :
    exp (exp c) ^ α / log (exp (exp c)) ^ B = exp (exp c * α - c * B) := by
  rw [log_exp, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_sub]

theorem cond19_13375 : Cond19 0.00256 10 1500 (exp (exp 13.375)) := by
  have h := Journal.conditions_13375
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · rw [log_exp]; norm_num at h ⊢; linarith [h.2]
  · rw [ratio_exp]; apply exp_le_exp.2; linarith [h.1]

theorem cond25_13375 : Cond25 0.00256 10 1500 (exp (exp 13.375)) := by
  have h := Journal.conditions_13375
  have h1 := Journal.display25_first
  have h3 := Journal.display25_third
  refine ⟨by rw [log_exp]; exact h1, ?_, ?_, by norm_num, by norm_num⟩
  · rw [ratio_exp]; apply exp_le_exp.2; linarith [h.1]
  · rw [ratio_exp]
    have e : (0.44 : ℝ) = exp (log 0.44) := (exp_log (by norm_num)).symm
    rw [e]; apply exp_le_exp.2; linarith

/-- Vacuity instance of the threshold: an even N ≥ exp(exp 13.375) exists. -/
theorem threshold_nonvacuous : ∃ N : ℕ, Even N ∧ exp (exp 13.375) ≤ (N : ℝ) := by
  refine ⟨2 * ⌈exp (exp 13.375)⌉₊, even_two_mul _, ?_⟩
  have h := Nat.le_ceil (exp (exp 13.375))
  have h0 : (0 : ℝ) ≤ ⌈exp (exp 13.375)⌉₊ := Nat.cast_nonneg _
  push_cast; linarith

/-! ### Error terms at log N ≥ e^{13.375}, PROVED -/

lemma error_13375 {N : ℝ} (hN : 0 < N) (hL : exp 13.375 ≤ log N) :
    2 * N ^ (7 / 8 : ℝ) + N ^ (1 / 3 : ℝ) + √N + 1 < 3.6e-5 * (N / log N ^ 2) := by
  have h0 := Journal.exp13375_ge
  have r78 : N ^ (7 / 8 : ℝ) = exp (log N * (7 / 8)) := by rw [rpow_def_of_pos hN]
  have r13 : N ^ (1 / 3 : ℝ) = exp (log N * (1 / 3)) := by rw [rpow_def_of_pos hN]
  have rs : √N = exp (log N * (1 / 2)) := by rw [sqrt_eq_rpow, rpow_def_of_pos hN]
  have eN : N = exp (log N) := (exp_log hN).symm
  rw [r78, r13, rs]
  set L := log N with hLd
  have hL0 : 0 < L := by linarith
  have h13 : exp (L * (1 / 3)) ≤ exp (L * (7 / 8)) := exp_le_exp.2 (by nlinarith)
  have h12 : exp (L * (1 / 2)) ≤ exp (L * (7 / 8)) := exp_le_exp.2 (by nlinarith)
  have h1 : 1 ≤ exp (L * (7 / 8)) := one_le_exp (by positivity)
  have ha : 0 < exp (L * (7 / 8)) := exp_pos _
  have hb : L ^ 4 / 98304 ≤ exp (L / 8) := by
    have := exp_ge_four (t := L / 8) (by positivity)
    have e : (L / 8) ^ 4 / 24 = L ^ 4 / 98304 := by ring
    linarith
  have hab : N = exp (L * (7 / 8)) * exp (L / 8) := by
    rw [← exp_add]; rw [eN]; congr 1; ring
  have hL2 : 2e10 ≤ L ^ 2 := by nlinarith
  have hbL : 5 * L ^ 2 < 3.6e-5 * exp (L / 8) := by
    have : 5 * L ^ 2 < 3.6e-5 * (L ^ 4 / 98304) := by
      nlinarith [mul_le_mul_of_nonneg_left hL2 (sq_nonneg L)]
    linarith
  have hL2' : 0 < L ^ 2 := by positivity
  have key : 5 * exp (L * (7 / 8)) < 3.6e-5 * (N / L ^ 2) := by
    rw [hab, show 3.6e-5 * (exp (L * (7 / 8)) * exp (L / 8) / L ^ 2)
        = exp (L * (7 / 8)) * (3.6e-5 * exp (L / 8)) / L ^ 2 by ring, lt_div_iff₀ hL2']
    nlinarith
  linarith

/-! ### The assembly -/

/-- **The I-0088 threshold, CONDITIONAL** ON Theorems 5, 6, 7, the linear sieve at
ε = 1/8349 with C₁ = 112, C₂ = 114, ε(1500) < 1/8349 and the bracket certificate. Lemma 9,
the Section 5.5 step, the main-term margin K3J > 10⁻⁴, the parameter conditions, U_N ≥ 2/5 and
the error terms are PROVED. -/
theorem chenThreshold13375_of_leaves (h5 : Thm5J) (h6 : Thm6J) (h7 : Thm7J)
    (hT4 : LinearSieveT4 (1 / 8349) 112 114) (hε : Eps1500) (hB : Bracket13375) :
    ChenThreshold13375 := by
  intro hG n hev hn
  obtain ⟨hX18, hX10⟩ := X2_ranges
  have c19 := cond19_13375
  have c25 := cond25_13375
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (exp_pos _) hn
  have hL : exp 13.375 ≤ log (n : ℝ) := by
    rw [← log_exp (exp 13.375)]; exact log_le_log (exp_pos _) hn
  have h24 : (2 : ℝ) ^ 24 ≤ n := by linarith
  have H5 := h5 0.00256 10 1500 (1 / 8349) 112 114 (exp (exp 13.375)) n hG hT4 (by norm_num) (by norm_num) hε.le (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) c19 hX18 hn hev
  have H6 := h6 0.00256 10 1500 (1 / 8349) 112 114 (exp (exp 13.375)) n hG hT4 (by norm_num) (by norm_num) hε.le (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) c19 hX10 hn hev
  have H7 := h7 0.00256 10 1500 (1 / 8349) 112 114 (exp (exp 13.375)) 1e-20 n hG hT4 (by norm_num) (by norm_num) hε.le (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) c25 hX10 hn hev
  rw [sum_Qset_filter] at H6
  have H9 := U7153.lemma10 n h24
  have HB := hB n hn
  have hK := Journal.theorem3_positive_main
  have hU := two_fifths_le_UNfull n
  have hE := error_13375 hn0 hL
  have h55 := section55_step n
  set c := UNfull n * n / log (n : ℝ) ^ 2 with hc
  set q := (n : ℝ) / log (n : ℝ) ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hcq : 2 / 5 * q ≤ c := by
    rw [hc, hq, mul_div_assoc]; exact mul_le_mul_of_nonneg_right hU hq0
  have hc0 : 0 ≤ c := by linarith
  have HBc := mul_le_mul_of_nonneg_left HB hc0
  have hKc := mul_le_mul_of_nonneg_left hK.le hc0
  have hpos : (0 : ℝ) < pi2' n := by nlinarith
  exact rep_of_pi2' (by exact_mod_cast hpos)

/-! ### Links to the lab's existing statements, PROVED -/

theorem omega_of_sqfree (h : ChenThreshold13375) : ChenThreshold13375Omega := by
  intro hG N he hN
  obtain ⟨p, m, hp, hpm, hm1, -, hΩ⟩ := h hG N he hN
  exact ⟨p, m, hp, hpm, by omega, hΩ⟩

/-- The threshold gives the journal's Corollary 1 at exp(exp 14). -/
theorem corollaryOneJ_of_threshold (h : ChenThreshold13375) : CorollaryOneJ := by
  intro hG N he hN
  refine h hG N he (le_trans ?_ hN.le)
  exact exp_le_exp.2 (exp_le_exp.2 (by norm_num))

/-- The threshold gives the lab's cited `bordignonStarichkova_GRH` at exp(exp 15.85). -/
theorem bsGRH_of_threshold (h : ChenThreshold13375) :
    LeanLab.AlmostPrimeSums.bordignonStarichkova_GRH := by
  intro hG N he hN
  have := omega_of_sqfree h hG N he
    (le_trans (exp_le_exp.2 (exp_le_exp.2 (by norm_num))) hN.le)
  exact this


end LeanLab.BS2022GRH.ChenThresholdGRH
