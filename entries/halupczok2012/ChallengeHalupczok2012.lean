module

public import Mathlib

/-!
# Halupczok 2012, Theorem 1.2 repaired, CONDITIONAL on two cited results

K. Halupczok, *Goldbach's problem with primes in arithmetic progressions and in short
intervals*, J. Théor. Nombres Bordeaux 25, 2013, no. 2, pages 331 to 351, doi 10.5802/jtnb.839,
arXiv 1212.4406. Theorem 1.2, pages 333 to 334, is a Bombieri-Vinogradov type mean value
theorem for the ternary Goldbach problem with `p₁` in an arithmetic progression `a mod q` and
`p₁, p₂` in short intervals `[X₁, X₁ + Y₁]`, `[X₂, X₂ + Y₂]`: summed over `q ≤ Q`, the prime
sum `ternSum` differs from its expected main term `T(n, q, a) Y₁ Y₂` by `≪ Y₁ Y₂ L^{-A}`.

The defect. As printed, the sum runs over all `q ≤ Q`, with no condition `(a, q) = 1`, and the
printed `T(n, q, a)` does not vanish when `(a, q) > 1`. For such `q ≤ X₁` the prime sum is
empty, so for `a = 3` the single term `q = 3` is about `0.767 Y₁ Y₂`, larger than the claimed
bound. The printed statement is false as written.

The repair, two equivalent forms, both proved here:
* `theorem2Zeroed_U1510`: the sum over ALL `q ≤ Q`, as printed, with the main term `T0`, which is
  `T` when `(a, q) = 1` and `0` otherwise, as the paper's binary singular series `S(r, q, a)` of
  display 1 is. One harmless hypothesis `Q ≤ X₁` is added; the paper's bound on `Q` implies it
  for large `X₁`.
* `theorem2_U1510`: the sum restricted to `q ≤ Q` with `(a, q) = 1`, with the printed `T`.

CONDITIONAL. Both theorems take two cited results of other authors as explicit hypotheses,
never as axioms; they are the inputs the paper's own proof quotes:
* `PPS1984Remark`: the printed Remark on p. 530 of A. Perelli, J. Pintz and S. Salerno,
  *Bombieri's theorem in short intervals*, Ann. Scuola Norm. Sup. Pisa Cl. Sci. 4, 11, 1984,
  529 to 539, in its reading with constants uniform in the interval length. The paper quotes
  this result as its Theorem 2.1, p. 338; `theorem3_of_remark` proves that the Remark implies the
  paper's Theorem 2.1, written `Theorem3`.
* `PP1993Goldbach`: the Goldbach analogue of Theorem 3 of A. Perelli and J. Pintz, *On the
  exceptional set for Goldbach's problem in short intervals*, J. London Math. Soc. 2, 47, 1993,
  41 to 49, established in its sections 3 to 5 but not printed as a numbered theorem. The paper
  states the result it needs as its Theorem 2.3, p. 339, and says it is an adaptation of the
  proof in that reference; `theorem5_of_PP1993` proves that `PP1993Goldbach` implies the paper's
  Theorem 2.3, written `Theorem5`.

Binary Goldbach is open; nothing here claims it, and ternary Goldbach is a theorem of Helfgott.
An AI agent, Claude by Anthropic, wrote the Lean code. Lean names keep the namespaces of the
lab where the proofs were written; `Theorem2` is the arXiv numbering of Theorem 1.2.

Conventions. `[X, X+Y]` is the set of integers `m` with `X < m ≤ X + Y`, and `L = log Y₂`. Every
`≪`, `≫`, `≍` in a hypothesis is a universally quantified constant `c > 0`; every `≪` in a
conclusion an existential constant `C`, and sufficiently large an existential threshold `Y0`.
-/

@[expose] public section

section

open Finset
open scoped Classical

namespace LeanLab.Halupczok2012

/-- The integers `k` with `X < k ≤ X + R`, the paper's interval `[X, X + R]`. -/
noncomputable def kRange (X R : ℝ) : Finset ℕ :=
  (Icc 0 ⌈X + R⌉₊).filter (fun k => X < k ∧ (k : ℝ) ≤ X + R)

/-- `∑ log p₂ log p₃` over primes `p₂ + p₃ = m` with `X₂ < p₂ ≤ X₂ + Y` and `p₂ ≡ a₂ mod q₂`. -/
noncomputable def binSumAP (X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (m : ℕ) : ℝ :=
  ∑ p ∈ (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ X2 < p ∧ (p : ℝ) ≤ X2 + Y ∧
      (p : ℤ) ≡ a2 [ZMOD q2]),
    Real.log p * Real.log ((m - p : ℕ) : ℝ)

/-- `∑ log p₂ log p₃` over primes `p₂ + p₃ = m` with `X₂ < p₂ ≤ X₂ + Y`. -/
noncomputable def binSum (X2 Y : ℝ) (m : ℕ) : ℝ := binSumAP X2 Y 1 0 m

/-- The twin prime constant `∏_{p ≠ 2} (1 - 1/(p-1)²)`, a `tprod` over all primes; the product
converges absolutely, so the `tprod` is its value. -/
noncomputable def twinC : ℝ :=
  ∏' p : Nat.Primes, (if (p : ℕ) = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- The binary singular series `𝔖(r)` of the paper, display 2: `0` for odd `r`, and for even
`r` it is `2 C₂ ∏_{p ∣ r, p > 2} (p - 1)/(p - 2)`, with `C₂ = twinC`. -/
noncomputable def S (r : ℕ) : ℝ :=
  if Even r then 2 * twinC * ∏ p ∈ r.primeFactors.filter (· ≠ 2), (((p : ℝ) - 1) / ((p : ℝ) - 2))
  else 0

/-- The ternary singular series `T(n, q, a)` of Theorem 1.2, as printed after the theorem:
`φ(q)⁻¹` times the product over all primes of the local factor, `1 - 1/(p-1)²` if `p ∣ n, p ∤ q`
or `p ∤ n - a, p ∣ q`; `1 + 1/(p-1)³` if `p ∤ n, p ∤ q`; and `p/(p-1)` otherwise. -/
noncomputable def T (n q : ℕ) (a : ℤ) : ℝ :=
  (1 / (Nat.totient q : ℝ)) * ∏' p : Nat.Primes,
    (if ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ∣ q) ∨ (¬ ((p : ℕ) : ℤ) ∣ (n - a) ∧ (p : ℕ) ∣ q) then
        1 - 1 / ((p : ℝ) - 1) ^ 2
      else if ¬ (p : ℕ) ∣ n ∧ ¬ (p : ℕ) ∣ q then 1 + 1 / ((p : ℝ) - 1) ^ 3
      else (p : ℝ) / ((p : ℝ) - 1))

/-- The prime sum of Theorem 1.2: `∑ log p₁ log p₂ log p₃` over primes `p₁ + p₂ + p₃ = n` with
`X₁ < p₁ ≤ X₁ + Y₁`, `X₂ < p₂ ≤ X₂ + Y₂` and `p₁ ≡ a mod q`. -/
noncomputable def ternSum (n : ℕ) (X1 Y1 X2 Y2 : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ x ∈ ((range (n + 1)) ×ˢ (range (n + 1))).filter (fun x =>
      x.1.Prime ∧ x.2.Prime ∧ x.1 + x.2 ≤ n ∧ (n - x.1 - x.2).Prime ∧
      X1 < x.1 ∧ (x.1 : ℝ) ≤ X1 + Y1 ∧ X2 < x.2 ∧ (x.2 : ℝ) ≤ X2 + Y2 ∧ (x.1 : ℤ) ≡ a [ZMOD q]),
    Real.log x.1 * Real.log x.2 * Real.log ((n - x.1 - x.2 : ℕ) : ℝ)

/-- The hypotheses of Theorem 1.2, with constants `c 0` to `c 6`, `B` and `L = log Y₂`: `n` odd,
`X₁ ≥ Y₁ ≫ X₁^{3/5+ε₁}`, `X₂ ≥ Y₂ ≫ X₂^{7/12+ε₂}`, `Y₂^{1/3+ε} ≪ Y₁ ≪ Y₂ ≍ n - X₁ - Y₁ - X₂ - Y₂ ≥ 0`
and `1 ≤ Q ≪ Y₁ X₁^{-1/2} L^{-B}`. The condition `1 ≤ Q` only excludes an empty sum. -/
def Thm2Hyp (ε ε1 ε2 B : ℝ) (c : Fin 7 → ℝ) (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ) : Prop :=
  Odd n ∧ Y1 ≤ X1 ∧ c 0 * X1 ^ (3 / 5 + ε1) ≤ Y1 ∧ Y2 ≤ X2 ∧ c 1 * X2 ^ (7 / 12 + ε2) ≤ Y2 ∧
  c 2 * Y2 ^ (1 / 3 + ε) ≤ Y1 ∧ Y1 ≤ c 3 * Y2 ∧
  0 ≤ (n : ℝ) - X1 - Y1 - X2 - Y2 ∧ c 4 * Y2 ≤ (n : ℝ) - X1 - Y1 - X2 - Y2 ∧
  (n : ℝ) - X1 - Y1 - X2 - Y2 ≤ c 5 * Y2 ∧
  1 ≤ Q ∧ Q ≤ c 6 * Y1 * X1 ^ (-(1 / 2) : ℝ) * Real.log Y2 ^ (-B)

/-- Theorem 1.2 in its coprime reading: under `Thm2Hyp`, `Q ≪ Y₁^{3/2} (n - X₁)^{-1/2}` and a
fixed integer `a ≤ n - X₁ - Y₁`, the sum over `q ≤ Q` with `(a, q) = 1` of
`|ternSum - T(n, q, a) Y₁ Y₂|` is `≪ Y₁ Y₂ L^{-A}`, `B` depending on `A` and the `ε`'s. -/
def Theorem2 : Prop :=
  ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 → ∃ B : ℝ, 0 < B ∧
  ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∀ c7 : ℝ, 0 < c7 → ∀ a : ℤ, ∃ C Y0 : ℝ,
  ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 → Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q →
    Q ≤ c7 * Y1 ^ (3 / 2 : ℝ) * ((n : ℝ) - X1) ^ (-(1 / 2) : ℝ) → (a : ℝ) ≤ (n : ℝ) - X1 - Y1 →
    ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      |ternSum n X1 Y1 X2 Y2 q a - T n q a * Y1 * Y2| ≤ C * Y1 * Y2 * Real.log Y2 ^ (-A)

end LeanLab.Halupczok2012

end

namespace LeanLab.Halupczok2012

open Finset

/-- The repaired main term: `T(n, q, a)` when `(a, q) = 1`, and `0` when `(a, q) > 1`. -/
noncomputable def T0 (n q : ℕ) (a : ℤ) : ℝ := if Int.gcd a q = 1 then T n q a else 0

/-- Theorem 1.2 repaired: the sum over ALL `q ≤ Q`, as printed, with the main term `T0` in
place of `T`, under the same hypotheses as `Theorem2` plus `Q ≤ X₁`. -/
def Theorem2Zeroed : Prop :=
  ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 → ∃ B : ℝ, 0 < B ∧
  ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∀ c7 : ℝ, 0 < c7 → ∀ a : ℤ, ∃ C Y0 : ℝ,
  ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 → Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q →
    Q ≤ c7 * Y1 ^ (3 / 2 : ℝ) * ((n : ℝ) - X1) ^ (-(1 / 2) : ℝ) → (a : ℝ) ≤ (n : ℝ) - X1 - Y1 →
    Q ≤ X1 →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, |ternSum n X1 Y1 X2 Y2 q a - T0 n q a * Y1 * Y2|
      ≤ C * Y1 * Y2 * Real.log Y2 ^ (-A)

end LeanLab.Halupczok2012

namespace LeanLab.Halupczok2012

open Finset

/-- The paper's Theorem 2.3, p. 339, which it states as an adaptation of Perelli and Pintz 1993:
for `Y^{1/3+ε} ≪ R ≪ Y ≍ 2X₁ - X₂ - Y ≥ 0`, `R ≤ X₁` and `X₂^{7/12+ε₂} ≪ Y ≤ X₂`,
`∑_{X₁ < k ≤ X₁ + R} (binSum X₂ Y (2k) - 𝔖(2k) Y)² ≪ R Y² L^{-A}` with `L = log Y`. -/
def Theorem5 : Prop :=
  ∀ A ε ε2 : ℝ, 0 < A → 0 < ε → 0 < ε2 →
  ∀ c1 c2 c3 c4 c5 : ℝ, 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → 0 < c5 →
  ∃ C Y0 : ℝ, ∀ X1 X2 Y R : ℝ, Y0 ≤ Y →
    c1 * X2 ^ (7 / 12 + ε2) ≤ Y → Y ≤ X2 → c2 * Y ^ (1 / 3 + ε) ≤ R → R ≤ c3 * Y → R ≤ X1 →
    0 ≤ 2 * X1 - X2 - Y → c4 * Y ≤ 2 * X1 - X2 - Y → 2 * X1 - X2 - Y ≤ c5 * Y →
    ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
      C * R * Y ^ 2 * Real.log Y ^ (-A)

/-- `∑ log p` over primes `X < p ≤ X + Y` with `p ≡ a mod q`. -/
noncomputable def thetaAP (X Y : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ p ∈ (range (⌈X + Y⌉₊ + 1)).filter (fun p : ℕ => p.Prime ∧ X < p ∧ (p : ℝ) ≤ X + Y ∧
    (p : ℤ) ≡ a [ZMOD q]), Real.log p

/-- The paper's Theorem 2.1, p. 338, quoted from Perelli, Pintz and Salerno 1984: for
`X ≥ Y ≫ X^{3/5+ε}` and `Q ≪ Y X^{-1/2} (log X)^{-B}`,
`∑_{q ≤ Q} max_{(a,q)=1} |thetaAP X Y q a - Y/φ(q)| ≪ Y L^{-A}` with `L = log Y`; the maximum is
written as an arbitrary choice `a q` of a reduced residue for each `q`. -/
def Theorem3 : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧ ∀ c1 c2 : ℝ, 0 < c1 → 0 < c2 →
  ∃ C Y0 : ℝ, ∀ X Y Q : ℝ, Y0 ≤ Y → Y ≤ X → c1 * X ^ (3 / 5 + ε) ≤ Y →
    Q ≤ c2 * Y * X ^ (-(1 / 2) : ℝ) * Real.log X ^ (-B) →
    ∀ a : ℕ → ℤ, (∀ q, Int.gcd (a q) q = 1) →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, |thetaAP X Y q (a q) - Y / q.totient| ≤ C * Y * Real.log Y ^ (-A)

end LeanLab.Halupczok2012

namespace LeanLab.Halupczok2012

open Finset

/-- `ψ(z; q, a) = ∑ Λ(n)` over `1 ≤ n ≤ z` with `n ≡ a mod q`, as on p. 529 of Perelli, Pintz
and Salerno 1984. -/
noncomputable def psiAP (z : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ∑ n ∈ (Ioc 0 ⌊z⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD q]),
    ArithmeticFunction.vonMangoldt n

/-- The summand `|ψ(z + h; q, a) - ψ(z; q, a) - h/φ(q)|` of display 2 of Perelli, Pintz and
Salerno 1984, p. 529. -/
noncomputable def ppsTerm (z h : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  |psiAP (z + h) q a - psiAP z q a - h / q.totient|

/-- CITED HYPOTHESIS, not proved here: the printed Remark on p. 530 of Perelli, Pintz and
Salerno 1984, which says display 2 holds whenever `Q ≤ y x^{-1/2} (log x)^{-B}` and
`y ≥ x^{3/5} (log x)^C` with `C = C(A)`. Read with one implied constant for all such `y ≤ x`:
for every `A > 0` there are `D`, `B > 0`, `C` and `x0` such that for `x ≥ x0`,
`x^{3/5} (log x)^D ≤ y ≤ x` and `Q ≤ y x^{-1/2} (log x)^{-B}`,
`∑_{q ≤ Q} max_{(a,q)=1} max_{0 < h ≤ y} max_{x/2 < z ≤ x} ppsTerm z h q a ≤ C y (log x)^{-A}`,
the three maxima written as arbitrary choice functions `a, h, z` of `q`. -/
def PPS1984Remark : Prop :=
  ∀ A : ℝ, 0 < A → ∃ D B : ℝ, 0 < B ∧ ∃ C x0 : ℝ, ∀ x y Q : ℝ, x0 ≤ x →
    x ^ (3 / 5 : ℝ) * Real.log x ^ D ≤ y → y ≤ x →
    Q ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) →
    ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
    (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A)

end LeanLab.Halupczok2012

namespace LeanLab.Halupczok2012

open Finset
open scoped ArithmeticFunction.vonMangoldt Classical

/-- The summation condition of `R*(2n, N, Y)` and `M*(2n, N, Y)` of Perelli and Pintz 1993,
p. 43, for `m = 2n`, `h` the first summand and `k = m - h`: `N - Y < h ≤ N` and `k ≤ Y`. -/
def ppCond (m : ℕ) (N Y : ℝ) (h : ℕ) : Prop :=
  N - Y < (h : ℝ) ∧ (h : ℝ) ≤ N ∧ ((m - h : ℕ) : ℝ) ≤ Y

/-- `R*(2n, N, Y) = ∑ Λ(h) Λ(k)` over `h + k = 2n`, `h, k ≥ 1`, with `ppCond`, Perelli and Pintz
1993, p. 43, with `m = 2n`. -/
noncomputable def ppR (m : ℕ) (N Y : ℝ) : ℝ :=
  ∑ h ∈ (Ioo 0 m).filter (ppCond m N Y), Λ h * Λ (m - h)

/-- `M*(2n, N, Y)`, the number of pairs `h + k = 2n`, `h, k ≥ 1`, with `ppCond`, Perelli and
Pintz 1993, p. 43, with `m = 2n`. -/
noncomputable def ppM (m : ℕ) (N Y : ℝ) : ℝ :=
  (((Ioo 0 m).filter (ppCond m N Y)).card : ℝ)

/-- CITED HYPOTHESIS, not proved here: the Goldbach analogue of Theorem 3 of Perelli and Pintz
1993, which their displays 1, 3, 4 and 5 in sections 3 to 5, pp. 44 to 46, establish, though
it is not printed as a numbered theorem: for `ε, A > 0`, `N^{7/12+ε} ≤ Y ≤ N` and
`H = Y^{1/3+ε}`, `∑_{N < 2n ≤ N + H} (R*(2n) - 𝔖(2n) M*(2n))² ≪ H Y² (log N)^{-A}` for
`N ≥ N0(ε, A)`. -/
def PP1993Goldbach : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ, N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        (ppR (2 * k) N Y - S (2 * k) * ppM (2 * k) N Y) ^ 2 ≤
      C * Y ^ (1 / 3 + ε) * Y ^ 2 * Real.log N ^ (-A)

end LeanLab.Halupczok2012

namespace LeanLab.Halupczok2012

/-- **Halupczok 2012, Theorem 1.2 repaired, CONDITIONAL on `PPS1984Remark` and
`PP1993Goldbach`**, both explicit hypotheses: the sum over all `q ≤ Q` with the main term `T0`. -/
theorem theorem2Zeroed_U1510 (hR : PPS1984Remark) (hPP : PP1993Goldbach) :
    Theorem2Zeroed := by
  sorry

/-- **Halupczok 2012, Theorem 1.2 in its coprime reading, CONDITIONAL on `PPS1984Remark` and
`PP1993Goldbach`**, both explicit hypotheses: the sum over `q ≤ Q` with `(a, q) = 1`. -/
theorem theorem2_U1510 (hR : PPS1984Remark) (hPP : PP1993Goldbach) : Theorem2 := by
  sorry

/-- Derived result of this entry, not a theorem of the paper: the printed Remark of Perelli, Pintz
and Salerno 1984, as `PPS1984Remark`, implies the paper's quoted Theorem 2.1, written `Theorem3`. -/
theorem theorem3_of_remark (hR : PPS1984Remark) : Theorem3 := by
  sorry

/-- Derived result of this entry, not a theorem of the paper: the Goldbach analogue of Perelli and
Pintz 1993 Theorem 3, as `PP1993Goldbach`, implies the paper's quoted Theorem 2.3, written
`Theorem5`. -/
theorem theorem5_of_PP1993 (hPP : PP1993Goldbach) : Theorem5 := by
  sorry

end LeanLab.Halupczok2012
