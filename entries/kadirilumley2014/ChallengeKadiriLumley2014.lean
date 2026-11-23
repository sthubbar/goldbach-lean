module

public import Mathlib

/-!
# Short effective intervals containing primes

Statements from H. Kadiri and A. Lumley, Short effective intervals containing primes,
Integers 14, 2014, A61, arXiv 1407.7902.

Theorem 1.1 of the paper says that for each row of its Table 2, with threshold `x0` and
denominator `Δ`, every real `x > x0` has a prime `p` with `(1 - 1/Δ) x < p < x`. Corollary 1.2
deduces that every odd number between 5 and `1966196911 · 4 · 10^18` is a sum of three primes.

The compared theorems are conditional. Each cited input is an explicit hypothesis, never an
axiom:

* `EvenGoldbachUpTo (4 * 10 ^ 18)`, the verification of even Goldbach up to `4 · 10^18` by
  Oliveira e Silva, Herzog and Pardi 2014;
* `MVBrunTitchmarsh`, Theorem 2 of Montgomery and Vaughan 1973, the Brun Titchmarsh inequality;
* the bound `|θ(t) - t| < 0.05 t / log² t` for `t ≥ 122568683`, the row `η = 0.05` of
  Theorem 5.2 of Dusart 2010, or in `row_of_inputs` its consequence `CostaEstimate`, the bound of
  Costa Pereira 1985 Theorem 5 that the paper cites as Lemma 2.1;
* the inequality of display 2.64 of the paper, with the true absolute sum over the nontrivial
  zeros of ζ, at the Table 2 rows used, at `X = x0 / (e^u (1 + δ))` and with the printed `a`
  raised by one unit of its last digit, slightly stronger than the display at the paper's exact
  `a` and `X0`. The paper checks this display numerically; here it is a
  hypothesis at each row.

The weighted zero series inside `zeroError` is proved summable, with `zeroError` its sum, for
every positive `m`, `δ`, `u` and `X` and so at every Table 2 row where display 2.64 is asked, in
`zeroError_hasSum` and `row_zeroError_hasSum`. Hence the zero contribution in each display 2.64
hypothesis is the true sum and cannot vanish by default.

`corollary57_of_inputs` is Corollary 1.2 with Table 2 row 57 in place of row 60, so its range
`1886389443 · 4 · 10^18` is about 4 percent below the printed range. Ternary Goldbach itself is
known unconditionally by Helfgott's work; binary Goldbach is open. AI wrote this Lean code.
-/

@[expose] public section

namespace LeanLab

/-- `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- `n` is a sum of three primes. -/
def IsTernarySum (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

/-- Binary Goldbach holds for every even `n` with `4 ≤ n ≤ N`. -/
def EvenGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n, Even n → 4 ≤ n → n ≤ N → IsGoldbachSum n

end LeanLab

namespace LeanLab.RamareSaouter2003.Thm4Parts

open Real Chebyshev Finset

/-- Montgomery and Vaughan 1973, Theorem 2: for real `x > 0` and `y > 1`, the number of primes
in `]x, x + y]` is less than `2 y / log y`. -/
def MVBrunTitchmarsh : Prop :=
  ∀ x y : ℝ, 0 < x → 1 < y →
    ((((Ioc ⌊x⌋₊ ⌊x + y⌋₊).filter Nat.Prime).card : ℕ) : ℝ) < 2 * y / Real.log y

end LeanLab.RamareSaouter2003.Thm4Parts

namespace LeanLab.KadiriLumley2014
open Real

/-- Theorem 1.1 for one Table 2 row: for every `x > x0` there is a prime `p` with
`(1 - 1/Δ) x < p < x`. -/
def KLRow (x0 Δ : ℝ) : Prop :=
  ∀ x : ℝ, x0 < x → ∃ p : ℕ, p.Prime ∧ (1 - 1 / Δ) * x < p ∧ (p : ℝ) < x

end LeanLab.KadiriLumley2014

namespace LeanLab.KadiriLumley2014.Task64
open Real

/-- The even verification bound `4 · 10^18` of Corollary 1.2. -/
def evenBase : ℕ := 4 * 10 ^ 18

end LeanLab.KadiriLumley2014.Task64

namespace LeanLab.KadiriLumley2014.Task64
open Real

/-- One printed row of Table 2. A zero log index denotes the threshold `4 · 10^18`, any other
index `k` the threshold `e^k`. The column δ is stored in units of `10^-12`, σ in hundredths and
`a` in ten thousandths; `gapDenom` is the printed Δ. -/
structure PrintedRow where
  logIndex : ℕ
  m : ℕ
  deltaUnits : ℕ
  height : ℕ
  sigmaUnits : ℕ
  aUnits : ℕ
  gapDenom : ℕ
  deriving DecidableEq, Repr

/-- All twenty rows of Table 2, transcribed from the paper. -/
def tableTwo : List PrintedRow := [
  ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩,
  ⟨43, 5, 33490, 291316980, 92, 2147, 38753947⟩,
  ⟨44, 6, 23300, 488509984, 92, 2324, 61162616⟩,
  ⟨45, 7, 16280, 797398875, 92, 2494, 95381241⟩,
  ⟨46, 8, 11340, 1284120197, 92, 2651, 148306019⟩,
  ⟨47, 9, 8080, 1996029891, 92, 2836, 227619375⟩,
  ⟨48, 11, 6000, 3204848430, 93, 3050, 346582570⟩,
  ⟨49, 15, 4682, 5415123831, 93, 3275, 518958776⟩,
  ⟨50, 20, 3889, 8466793105, 93, 3543, 753575355⟩,
  ⟨51, 28, 3625, 12399463961, 93, 3849, 1037917449⟩,
  ⟨52, 39, 3803, 16139006408, 93, 4127, 1313524036⟩,
  ⟨53, 48, 4088, 18290358817, 93, 4301, 1524171138⟩,
  ⟨54, 54, 4311, 19412056863, 93, 4398, 1670398039⟩,
  ⟨55, 56, 4386, 19757119193, 93, 4445, 1770251249⟩,
  ⟨56, 59, 4508, 20210075547, 93, 4481, 1838818070⟩,
  ⟨57, 59, 4506, 20219045843, 93, 4496, 1886389443⟩,
  ⟨58, 61, 4590, 20495459359, 93, 4514, 1920768795⟩,
  ⟨59, 61, 4589, 20499925573, 93, 4522, 1946282821⟩,
  ⟨60, 61, 4588, 20504393735, 93, 4527, 1966196911⟩,
  ⟨150, 64, 4685, 21029543983, 96, 4641, 2442159714⟩]

/-- The threshold `x0` of a printed row. -/
noncomputable def PrintedRow.threshold (r : PrintedRow) : ℝ :=
  if r.logIndex = 0 then evenBase else Real.exp r.logIndex

end LeanLab.KadiriLumley2014.Task64

namespace LeanLab.KadiriLumley2014.Task64
open Real

/-- Costa Pereira 1985 Theorem 5, cited as Lemma 2.1 of the paper: for `x ≥ e^38`,
`0.999 √x + x^{1/3} < ψ(x) - θ(x) < 1.001 √x + x^{1/3}`. -/
def CostaEstimate : Prop := ∀ x : ℝ, Real.exp 38 ≤ x →
  0.999 * Real.sqrt x + x ^ (1 / 3 : ℝ) < Chebyshev.psi x - Chebyshev.theta x ∧
  Chebyshev.psi x - Chebyshev.theta x < 1.001 * Real.sqrt x + x ^ (1 / 3 : ℝ)

end LeanLab.KadiriLumley2014.Task64

namespace LeanLab.KadiriLumley2014.Task64
open Real Set MeasureTheory intervalIntegral

/-- The smooth weight `f_m(t) = (4 t (1 - t))^m` of section 3.1 of the paper. -/
def weight (m : ℕ) (t : ℝ) : ℝ := (4 * t * (1 - t)) ^ m

end LeanLab.KadiriLumley2014.Task64

namespace LeanLab.KadiriLumley2014.Task64
open Real Set MeasureTheory intervalIntegral

/-- The endpoint mass of the weight on `[0, a]` and `[1 - a, 1]`, equation 2.3 of the paper. -/
noncomputable def tailMass (m : ℕ) (a : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..a, weight m t) + (∫ t in (1 - a)..1, weight m t)

end LeanLab.KadiriLumley2014.Task64

namespace LeanLab.KadiriLumley2014.Task64
open Real Set

/-- The exact rational δ of a printed row. -/
def PrintedRow.deltaQ (r : PrintedRow) : ℚ := r.deltaUnits / 10 ^ 12

/-- The exact rational lower end of the printed `a`. -/
def PrintedRow.aQ (r : PrintedRow) : ℚ := r.aUnits / 10000

/-- The exact rational `u`, from `δ = m u`. -/
def PrintedRow.uQ (r : PrintedRow) : ℚ := r.deltaQ / r.m

end LeanLab.KadiriLumley2014.Task64

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- The normalized weight integral in equation 2.17 of the paper. -/
noncomputable def weightTransform (m : ℕ) (δ : ℝ) (s : ℂ) : ℂ :=
  (∫ t in (0 : ℝ)..1, ((1 + δ * t : ℝ) : ℂ) ^ s * (weight m t : ℂ)) /
    ((∫ t in (0 : ℝ)..1, weight m t : ℝ) : ℂ)

/-- The smoothing transform G of equation 2.17 of the paper. -/
noncomputable def smoothingG (m : ℕ) (δ u : ℝ) (s : ℂ) : ℂ :=
  ((Complex.exp (s * u) - 1) / s) / ((Real.exp u - 1 : ℝ) : ℂ) * weightTransform m δ s

end LeanLab.KadiriLumley2014.Task92

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- The enlarged Brun Titchmarsh coefficient of equation 2.7 of the paper. -/
noncomputable def tailCoefficient (δ u X : ℝ) : ℝ :=
  2 * (1 + δ) * (Real.exp u - 1) *
    (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1))) * X

/-- The absolute summand of equation 2.19 of the paper at a nontrivial zero `ρ` of ζ,
counted with multiplicity. -/
noncomputable def zeroSummand (m : ℕ) (δ u X : ℝ)
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) : ℝ :=
  (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖smoothingG m δ u ρ‖ *
    X ^ ((ρ : ℂ).re - 1)

/-- The absolute sum over the nontrivial zeros of ζ in equation 2.19 of the paper. -/
noncomputable def zeroError (m : ℕ) (δ u X : ℝ) : ℝ :=
  ∑' ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}, zeroSummand m δ u X ρ

end LeanLab.KadiriLumley2014.Task92

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- The normalized `X` for a Table 2 row, `x0 / (e^u (1 + δ))`, at which display 2.64 is
asked; it is slightly below the paper's least `X0 = x0 / (e^u (1 + δ (1 - a)))`. -/
noncomputable def rowEndpointX (r : PrintedRow) : ℝ :=
  r.threshold / (Real.exp r.uQ * (1 + (r.deltaQ : ℝ)))

end LeanLab.KadiriLumley2014.Task92

namespace LeanLab.KadiriLumley2014.PalomarEntry
open Real Set MeasureTheory
open LeanLab.KadiriLumley2014.Task64 LeanLab.KadiriLumley2014.Task92

/-- One row of Table 2 of Theorem 1.1, from the Costa Pereira bound, the Montgomery and Vaughan
inequality, and display 2.64 of the paper at `rowEndpointX r`, with the printed `a` raised by one unit of its
last digit. -/
theorem row_of_inputs (hC : CostaEstimate)
    (hMV : LeanLab.RamareSaouter2003.Thm4Parts.MVBrunTitchmarsh)
    {r : PrintedRow} (hr : r ∈ tableTwo)
    (hE : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r))) :
    KLRow r.threshold r.gapDenom := by
  sorry

end LeanLab.KadiriLumley2014.PalomarEntry

namespace LeanLab.KadiriLumley2014.PalomarEntry57
open Real
open LeanLab.KadiriLumley2014.Task64 LeanLab.KadiriLumley2014.Task92

/-- Corollary 1.2 with Table 2 row 57 in place of row 60: every odd `n` with
`5 < n < 1886389443 · 4 · 10^18` is a sum of three primes, from the even verification to
`4 · 10^18`, Montgomery and Vaughan 1973 Theorem 2, Dusart 2010 Theorem 5.2 at `η = 0.05`, and
display 2.64 at the Table 2 rows `log 4 · 10^18` and 57. -/
theorem corollary57_of_inputs (hEven : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hMV : LeanLab.RamareSaouter2003.Thm4Parts.MVBrunTitchmarsh)
    (hDus : ∀ t : ℝ, 122568683 ≤ t →
      |Chebyshev.theta t - t| < 0.05 * t / Real.log t ^ 2)
    (h0 : let r : PrintedRow := ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩
      (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
        tailCoefficient r.deltaQ r.uQ (rowEndpointX r) *
            tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
        (Real.exp r.uQ - 1) * rowEndpointX r *
          (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)))
    (h57 : let r : PrintedRow := ⟨57, 59, 4506, 20219045843, 93, 4496, 1886389443⟩
      (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
        tailCoefficient r.deltaQ r.uQ (rowEndpointX r) *
            tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
        (Real.exp r.uQ - 1) * rowEndpointX r *
          (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r))) :
    ∀ n : ℕ, Odd n → 5 < n → n < 1886389443 * (4 * 10 ^ 18) → IsTernarySum n := by
  sorry

end LeanLab.KadiriLumley2014.PalomarEntry57

namespace LeanLab.KadiriLumley2014.PalomarKL45
open Real
open LeanLab.KadiriLumley2014.Task64 LeanLab.KadiriLumley2014.Task92

/-- Table 2 row 45 of Theorem 1.1 in natural number form: for every natural `y > e^45` there is
a prime `p < y` with `95381241 (y - p) < y`, from Montgomery and Vaughan 1973 Theorem 2, Dusart
2010 Theorem 5.2 at `η = 0.05`, and display 2.64 at row 45. -/
theorem kl45_of_inputs
    (hMV : LeanLab.RamareSaouter2003.Thm4Parts.MVBrunTitchmarsh)
    (hDus : ∀ t : ℝ, 122568683 ≤ t →
      |Chebyshev.theta t - t| < 0.05 * t / Real.log t ^ 2)
    (h45 : let r : PrintedRow := ⟨45, 7, 16280, 797398875, 92, 2494, 95381241⟩
      (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
        tailCoefficient r.deltaQ r.uQ (rowEndpointX r) *
            tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
        (Real.exp r.uQ - 1) * rowEndpointX r *
          (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r))) :
    ∀ y : ℕ, Real.exp 45 < y → ∃ p : ℕ, p.Prime ∧ p < y ∧ 95381241 * (y - p) < y := by
  sorry

end LeanLab.KadiriLumley2014.PalomarKL45

namespace LeanLab.KadiriLumley2014.PalomarSummable
open Real
open LeanLab.KadiriLumley2014.Task64 LeanLab.KadiriLumley2014.Task92

/-- For positive degree `m` and positive `δ`, `u`, `X`, the weighted zero series of equation
2.19 is summable and `zeroError m δ u X` is its sum. -/
theorem zeroError_hasSum {m : ℕ} (hm : 0 < m) {δ u X : ℝ}
    (hδ : 0 < δ) (hu : 0 < u) (hX : 0 < X) :
    HasSum (zeroSummand m δ u X) (zeroError m δ u X) := by
  sorry

/-- At every row of Table 2, the weighted zero series of equation 2.19 at the row's normalized
`X`, the point where display 2.64 is asked, is summable and `zeroError` there is its sum. -/
theorem row_zeroError_hasSum {r : PrintedRow} (hr : r ∈ tableTwo) :
    HasSum (zeroSummand r.m r.deltaQ r.uQ (rowEndpointX r))
      (zeroError r.m r.deltaQ r.uQ (rowEndpointX r)) := by
  sorry

end LeanLab.KadiriLumley2014.PalomarSummable
