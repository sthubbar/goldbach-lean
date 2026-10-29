module

public import Mathlib

/-!
# CONDITIONAL: a GRH Chen threshold at exp(exp 13.375), after Bordignon and Starichkova

M. Bordignon and V. Starichkova, *An explicit version of Chen's theorem assuming the Generalized
Riemann Hypothesis*, Ramanujan J. 64 (2024) 1213-1242, doi 10.1007/s11139-024-00866-x. Their
Corollary 1, p. 1214: under GRH every even integer N > exp(exp 14) is the sum of a prime and a
square-free number η > 1 with at most two prime factors. Keeping the authors' method and
re-choosing the Section 5.4 parameters, α₁ = α₂ = α₃ = 0.00256, A = 10, u = 1500,
ε = 1/8349, C₁ = 112, C₂ = 114, ε₁ = 10⁻²⁰, gives the same conclusion for every even
N ≥ exp(exp 13.375), `ChenThreshold13375`.

The target theorems:
* `Cert1575.chenThreshold13375_of_deep_closed`, the headline, CONDITIONAL. GRH, the paper's own
  hypothesis, is the premise inside `ChenThreshold13375`. Four results the paper cites or proves
  with deep analytic input are taken as explicit hypotheses of the theorem, never as axioms:
  - `Thm5J`, `Thm6J`, `Thm7J`: the journal's Theorems 5, 6 and 7, pp. 1228, 1231-1232 and
    1234-1235, the lower bound for S(A, ℙ, z) and the upper bounds for the sum of S(A_q, ℙ, z)
    and for S(B, ℙ, y), each with GRH and the linear sieve as premises;
  - `LinearSieveT4 (1/8349) 112 114`: the journal's Theorem 4, p. 1218, the explicit linear sieve
    of Bordignon, Johnston and Starichkova, with the Table 1 row ε⁻¹ = 6100, C₁ = 112, C₂ = 114,
    in the ranges of s the paper uses.
  They are transcriptions by the Lean Lab, not Mathlib results.
* `Cert1575.eps1500`, PROVED: ε(1500) < 1/8349 for the ε(u₀) of display (6), p. 1221.
* `Cert1567.bracket13375_holds`, PROVED: the Section 5.4 combination of the three brackets at
  the new parameters is at least `Journal.K3J` − 10⁻⁵, a one-sided lower bound.
* `ChenThresholdGRH.lemma9J_holds`, PROVED and unconditional: the journal's Lemma 9, Chen's
  weighted inequality, for every n ≥ 2²⁴.

Normalisation of U_N. The journal prints U_N = e^{-γ} ∏_{p>2}(1 − 1/(p−1)²) ∏_{p>2, p|N}
(p−1)/(p−2), pp. 1214 and 1227, while V(x) = ∏_{p<x, p∤N}(1 − 1/(p−1)) is asymptotic to
2e^{-γ}C₂Π_N/log x by Mertens' theorem. Here `UNfull n = ChenExplicit.U n` is
2e^{-γ}C₂Π_N, with the factor 2, and the transcribed Theorems 5, 6, 7 are stated with this
U_N. The printed factor (e^{-γ}C₂)⁻¹, `invTw`, in their negligible error terms is kept as
printed.

Binary Goldbach is open; nothing here claims it. AI wrote the Lean code, Claude, Anthropic.
Lean names keep the namespaces of the lab where the proofs were written; every definition below
is restated under its exact name and in the same `open` context as in the solution files.
-/

@[expose] public section

/-! ### GRH, `LeanLab/DERZ1997/Statements.lean` -/

namespace LeanLab.DERZ1997

/-- GRH for Dirichlet L-functions, as P0011 states it: all non-trivial zeros of all
Dirichlet L-functions have real part 1/2. Zeros are taken in the open strip `0 < Re s < 1`;
for an imprimitive character the extra Euler factor zeros lie on `Re s = 0`, so they are
excluded, and `q = 1` gives the Riemann zeta function. -/
def GRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

end LeanLab.DERZ1997

/-! ### The twin prime constant and `U_N`, `LeanLab/ChenExplicit/Statements.lean` -/

open Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

noncomputable section
namespace LeanLab.ChenExplicit

/-- The twin prime constant `∏_{p > 2} (1 - 1/(p-1)²)`. -/
def twinC : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- `U_N = 2 e^{-γ} ∏_{p>2} (1 - 1/(p-1)²) ∏_{p>2, p ∣ N} (p-1)/(p-2)`, equation (2) of P0009
and the display after Theorem 1.1 of P0010. -/
def U (N : ℕ) : ℝ :=
  2 * Real.exp (-Real.eulerMascheroniConstant) * twinC *
    ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

end LeanLab.ChenExplicit

end

/-! ### `c̄`, `LeanLab/ChenExplicit/BJSCbar.lean` -/

open Finset Real intervalIntegral

noncomputable section
namespace LeanLab.ChenExplicit.BJS

/-- `c̄`, Lemma 52. -/
def cbar : ℝ := ∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))

end LeanLab.ChenExplicit.BJS

end

/-! ### `q_G` of Lemma 3, `LeanLab/BS2022GRH/Constants.lean` -/

open Real Finset

set_option exponentiation.threshold 2000

noncomputable section
namespace LeanLab.BS2022GRH

/-- q_G of Lemma 3. -/
def qG (X : ℝ) : ℝ :=
  0.165 + 12.683 / log X + 254.980 / (log X) ^ 2 + 2607.854 / (log X) ^ 3 + 11605.056 / (log X) ^ 4
  + 1.314 * log X / X ^ ((1 : ℝ) / 4) + 0.092 * log (log X) / X ^ ((1 : ℝ) / 4)
  + 60.883 / X ^ ((1 : ℝ) / 4) + 8.250 * log (log X) / (X ^ ((1 : ℝ) / 4) * log X)
  + 939.260 / (X ^ ((1 : ℝ) / 4) * log X) - 237.934 / (sqrt X * log X)

end LeanLab.BS2022GRH

end

/-! ### `k_α`, `h(s)`, `r(X)`, `LeanLab/BS2022GRH/Thm6Factor.lean` -/

namespace LeanLab.BS2022GRH

open Real

/-- `k_x = 8 (1/6 - x)` of Theorem 6. -/
noncomputable def kA (α : ℝ) : ℝ := 8 * (1 / 6 - α)

/-- `h(s)` of the linear sieve statement, Section 2: `e⁻²` on `[1,2]`, `e^{-s}` on `[2,3]`,
`3 s⁻¹ e^{-s}` for `s ≥ 3`. -/
noncomputable def hS (s : ℝ) : ℝ :=
  if s ≤ 2 then exp (-2) else if s ≤ 3 then exp (-s) else 3 / s * exp (-s)

/-- `X^{1/8} / (X^{1/8} - 1)`. -/
noncomputable def rX (X : ℝ) : ℝ := X ^ (1 / 8 : ℝ) / (X ^ (1 / 8 : ℝ) - 1)

end LeanLab.BS2022GRH

/-! ### The logarithmic integral, `LeanLab/BS2022GRH/LiPV.lean` -/

namespace LeanLab.BS2022GRH

open Real MeasureTheory Filter Topology Set intervalIntegral

/-- The truncated principal value integral. -/
noncomputable def liPart (x e : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1 - e, 1 / log t) + ∫ t in 1 + e..x, 1 / log t

/-- **The principal value logarithmic integral**,
`li x = lim_{ε → 0+} (∫₀^{1-ε} + ∫_{1+ε}^x) dt / log t`. -/
noncomputable def liPV (x : ℝ) : ℝ := limUnder (𝓝[>] (0 : ℝ)) (liPart x)

end LeanLab.BS2022GRH

/-! ### `U_N`, `LeanLab/BS2022GRH/U7154UN.lean` -/

namespace LeanLab.BS2022GRH

open Real

/-- `U_N = 2 e^{-γ} C₂ ∏_{p>2, p|N} (p-1)/(p-2)`: the journal prints `U_N` without the
factor 2; this is the normalisation in which its Lemma 10, `V(x) ~ U_N / log x`, holds. -/
noncomputable def UNfull (n : ℕ) : ℝ := LeanLab.ChenExplicit.U n

end LeanLab.BS2022GRH

/-! ### Theorem 3's main-term constant, `LeanLab/BS2022GRH/JournalMargin.lean` -/

namespace LeanLab.BS2022GRH.Journal

open Real

/-- Theorem 3's main-term constant in the journal version: `K3` with `(1 + 5·10⁻⁵) l₁`. -/
noncomputable def K3J (α g ε C₁ C₂ cb : ℝ) : ℝ :=
  8 * (2 * g * log (3 - 8 * α) / (4 - 8 * α) - ε * C₂ * 3 * exp (8 * α - 2) / (4 - 8 * α))
  - 1 / 2 * (8 * ((1 + 5e-5) * (g / 4 * (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α)
      + log (8 / 3) * ε * C₁)))
  - 1 / 2 * ((2 * g / (1 / 2 - α) + 3 * ε * C₁) * cb)

end LeanLab.BS2022GRH.Journal

/-! ### The sieve sets of Lemma 9, `LeanLab/BS2022GRH/U7153Lemma10.lean` -/

namespace LeanLab.BS2022GRH.U7153

open Real Finset Classical

/-- `z = N^{1/8}`. -/
noncomputable def zz (n : ℕ) : ℝ := (n : ℝ) ^ (1 / 8 : ℝ)

/-- `y = N^{1/3}`. -/
noncomputable def yy (n : ℕ) : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)

/-- `a` has no prime factor `r < x` with `r ∤ N`, i.e. `(a, P(x)) = 1` for
`P(x) = ∏_{p < x, p ∈ ℙ} p`, `ℙ = {p ∤ N}`, as on the journal page 1227. -/
def NoSmallP (n : ℕ) (x : ℝ) (a : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → (r : ℝ) < x → ¬ r ∣ n → ¬ r ∣ a

/-- `A = {N − p : p ≤ N, p ∈ ℙ}`, `ℙ` the primes `p ∤ N`. -/
noncomputable def Aset (n : ℕ) : Finset ℕ :=
  ((range (n + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ n)).image (fun p => n - p)

/-- `S(A,P,z)`. -/
noncomputable def SA (n : ℕ) : ℕ := ((Aset n).filter (NoSmallP n (zz n))).card

/-- `S(A_q,P,z)`. -/
noncomputable def SAq (n q : ℕ) : ℕ :=
  ((Aset n).filter (fun a => q ∣ a ∧ NoSmallP n (zz n) a)).card

/-- The primes `q` with `z ≤ q < y`, all `≤ N`. -/
noncomputable def Qset (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun q => q.Prime ∧ zz n ≤ q ∧ (q : ℝ) < yy n)

/-- The triples `(p₁, p₂, p₃)` of primes defining `B`. -/
noncomputable def Triples (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((range n ×ˢ range n) ×ˢ range n).filter (fun t =>
    t.1.1.Prime ∧ t.1.2.Prime ∧ t.2.Prime ∧ zz n ≤ t.1.1 ∧ (t.1.1 : ℝ) < yy n ∧
    yy n ≤ t.1.2 ∧ t.1.2 ≤ t.2 ∧ t.1.1 * t.1.2 * t.2 < n ∧ Nat.Coprime (t.1.1 * t.1.2 * t.2) n)

/-- `B = {N − p₁p₂p₃ : z ≤ p₁ < y ≤ p₂ ≤ p₃, p₁p₂p₃ < N, (p₁p₂p₃, N) = 1}`. -/
noncomputable def Bset (n : ℕ) : Finset ℕ :=
  (Triples n).image (fun t => n - t.1.1 * t.1.2 * t.2)

/-- `S(B,P,y)`. -/
noncomputable def SB (n : ℕ) : ℕ := ((Bset n).filter (NoSmallP n (yy n))).card

/-- `m` is a prime or a product of two primes. -/
def IsP2 (m : ℕ) : Prop := m.Prime ∨ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ m = p₁ * p₂

/-- `π₂(N)`: primes `p < N` with `N − p` a prime or a product of two primes. -/
noncomputable def pi2 (n : ℕ) : ℕ := ((range n).filter (fun p => p.Prime ∧ IsP2 (n - p))).card

end LeanLab.BS2022GRH.U7153

/-! ### The threshold, the cited inputs and the brackets, `LeanLab/BS2022GRH/ChenThresholdGRH.lean` -/

namespace LeanLab.BS2022GRH.ChenThresholdGRH

open Real Finset Classical

/-- GRH for Dirichlet L-functions, the lab's existing predicate. -/
abbrev GRH : Prop := LeanLab.DERZ1997.GRH

/-- η > 1, square-free, with at most two prime factors: Corollary 1's summand, p. 1214. -/
def IsSqfreeP2 (m : ℕ) : Prop :=
  1 < m ∧ Squarefree m ∧ ArithmeticFunction.cardFactors m ≤ 2

/-- `N = p + η` with `p` prime and `η` as in `IsSqfreeP2`. -/
def ChenSqfreeRep (N : ℕ) : Prop := ∃ p m : ℕ, p.Prime ∧ N = p + m ∧ IsSqfreeP2 m

/-- **The I-0088 threshold**: under GRH every even N ≥ exp(exp 13.375) is a prime plus a
square-free η > 1 with at most two prime factors. -/
def ChenThreshold13375 : Prop :=
  GRH → ∀ N : ℕ, Even N → exp (exp 13.375) ≤ (N : ℝ) → ChenSqfreeRep N

/-- Display (6): ε(u₀) = exp(1.131·10⁻⁷ + (u₀/(u₀ − 2) + 0.501) Σ_{p ≥ u₀} 1/p²) − 1. -/
noncomputable def epsJ (u : ℝ) : ℝ :=
  exp (1.131e-7 + (u / (u - 2) + 0.501) *
    ∑' p : {p : ℕ // p.Prime ∧ u ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2) - 1

/-- **ε(1500) < 1/8349**, the numeric input of Section 5.4 at u = 1500; PROVED in this entry,
`LeanLab.BS2022GRH.Cert1575.eps1500`. -/
def Eps1500 : Prop := epsJ 1500 < 1 / 8349

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

/-- (19) and (21) without the range of α: log X₂ ≥ (A+1)/α, X₂^α/log^{A+1} X₂ ≥ e^u,
400 ≤ u ≤ 10⁸. -/
def Cond19 (α A u X₂ : ℝ) : Prop :=
  (A + 1) / α ≤ log X₂ ∧ exp u ≤ X₂ ^ α / log X₂ ^ (A + 1) ∧ 400 ≤ u ∧ u ≤ 1e8

/-- (25) without the range of α. -/
def Cond25 (α A u X₂ : ℝ) : Prop :=
  max ((A + 1) / α) (48 * (A + 4 / 3)) ≤ log X₂ ∧ exp u ≤ X₂ ^ α / log X₂ ^ (A + 1) ∧
    0.44 ≤ X₂ ^ (1 / 48 : ℝ) / log X₂ ^ (A + 4 / 3) ∧ 400 ≤ u ∧ u ≤ 1e8

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

/-- **Lemma 9**, Chen's weighted inequality. -/
def Lemma9J : Prop :=
  ∀ n : ℕ, (2 : ℝ) ^ 24 ≤ n →
    (U7153.SA n : ℝ) - 1 / 2 * ∑ q ∈ U7153.Qset n, (U7153.SAq n q : ℝ) - 1 / 2 * (U7153.SB n : ℝ)
      - 2 * (n : ℝ) ^ (7 / 8 : ℝ) - (n : ℝ) ^ (1 / 3 : ℝ) < U7153.pi2 n

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

/-- **Lemma 9 of the paper, PROVED, unconditional**: Chen's weighted inequality,
`π₂(n) > S(A) − ½ Σ_q S(A_q) − ½ S(B) − 2n^{7/8} − n^{1/3}` for every `n ≥ 2²⁴`. -/
theorem lemma9J_holds : Lemma9J := by
  sorry

end LeanLab.BS2022GRH.ChenThresholdGRH

/-! ### The bracket certificate, `LeanLab/BS2022GRH/Cert1567.lean` -/

namespace LeanLab.BS2022GRH.Cert1567

open Real MeasureTheory LeanLab.BS2022GRH LeanLab.BS2022GRH.ChenThresholdGRH

/-- **`Bracket13375`, PROVED**: the Section 5.4 combination `8·B5 − ½·8·B6 − ½·B7` of the
brackets of Theorems 5, 6, 7 at the new parameters is at least `K3J − 10⁻⁵` for every
`N ≥ exp(exp 13.375)`. -/
theorem bracket13375_holds : Bracket13375 := by
  sorry

end LeanLab.BS2022GRH.Cert1567

/-! ### The threshold, `LeanLab/BS2022GRH/Cert1575Closed.lean` -/

namespace LeanLab.BS2022GRH.Cert1575

open LeanLab.BS2022GRH.ChenThresholdGRH

/-- **`Eps1500`, PROVED**: `ε(1500) < 1/8349`, display (6) of the paper at `u₀ = 1500`. -/
theorem eps1500 : Eps1500 := by
  sorry

/-- **The GRH Chen threshold at `exp(exp 13.375)`, CONDITIONAL** ON the cited Theorems 5, 6, 7
of Bordignon and Starichkova, `Thm5J`, `Thm6J`, `Thm7J`, and the cited linear sieve Theorem 4 at
`ε = 1/8349`, `C₁ = 112`, `C₂ = 114`, `LinearSieveT4 (1/8349) 112 114`, all explicit hypotheses.
GRH itself is the premise inside `ChenThreshold13375`. -/
theorem chenThreshold13375_of_deep_closed (h5 : Thm5J) (h6 : Thm6J) (h7 : Thm7J)
    (hT4 : LinearSieveT4 (1 / 8349) 112 114) : ChenThreshold13375 := by
  sorry

end LeanLab.BS2022GRH.Cert1575
