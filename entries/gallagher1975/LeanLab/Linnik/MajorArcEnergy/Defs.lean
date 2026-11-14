module

public import LeanLab.Linnik.Decomp482b

/-!
Gallagher 1975 P0094 pp.128 to 131, displays 3 to 13.
Definitions for the pair decomposition of the major arc integral:
the family of primitive characters, induced characters chi_q, the sums c_n,
the arc integrals I_{n,q}, the pair sums J_n and their coefficient sums C_n.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.MajorArcEnergy

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b

/-- A character of modulus k + 1, indexed by k. Gallagher p.128 after display 3. -/
abbrev PChar := Σ k : ℕ, DirichletCharacter ℂ (k + 1)

/-- Gallagher 1975 p.128 after display 3: all primitive characters to conductors at most P.
The conductor is k + 1 with k below the floor of P, as in `correctedEnergy`. -/
noncomputable def family (P : ℝ) : Finset PChar :=
  (range ⌊P⌋₊).sigma fun k =>
    (univ : Finset (DirichletCharacter ℂ (k + 1))).filter fun χ => χ.IsPrimitive

/-- The principal character to modulus 1, written 1 on p.130. -/
noncomputable def one : PChar := ⟨0, 1⟩

/-- Gallagher 1975 p.128: chi_q, the character mod q induced by chi when its modulus divides q.
The value off that case is never used. -/
noncomputable def induced (x : PChar) (q : ℕ) : DirichletCharacter ℂ q :=
  if h : x.1 + 1 ∣ q then DirichletCharacter.changeLevel h x.2 else 1

/-- Gallagher 1975 p.128: c_n(chi) equals the sum over a from 1 to q of chi(a) e(an/q).
The residue a equal to q is replaced by a equal to 0, which gives the same term. -/
noncomputable def cn {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℤ) : ℂ :=
  ∑ a ∈ range q, χ a * LeanLab.PNTPort.LargeSieve.e ((a : ℝ) * n / q)

/-- Gallagher 1975 p.128: tau(chi) equals c_1(chi). -/
noncomputable def tau {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := cn χ 1

/-- Gallagher 1975 p.128: the q coefficient of J_n(chi, chi'),
c_n(conj chi_q chi'_q) times conj tau(conj chi_q) times tau(conj chi'_q). -/
noncomputable def pairCoeff (n : ℤ) (q : ℕ) (x y : PChar) : ℂ :=
  cn ((induced x q)⁻¹ * induced y q) n * star (tau (induced x q)⁻¹) * tau (induced y q)⁻¹

/-- Gallagher 1975 p.128: I_{n,q}(chi, chi') is the integral over |beta| at most 1/(qQ),
with Q equal to N/P, of conj A(chi, beta) A(chi', beta) e(n beta). -/
noncomputable def arcIntegral (N : ℕ) (P : ℝ) (n : ℤ) (q : ℕ) (x y : PChar) : ℂ :=
  ∫ β in Set.Icc (-(P / (q * N))) (P / (q * N)),
    star (primeAmplitude x.2 N β) * primeAmplitude y.2 N β *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * β)

/-- The moduli q at most P that are multiples of the lcm of the two conductors, p.128. -/
noncomputable def pairModuli (P : ℝ) (x y : PChar) : Finset ℕ :=
  (Icc 1 ⌊P⌋₊).filter fun q => Nat.lcm (x.1 + 1) (y.1 + 1) ∣ q

/-- Gallagher 1975 p.128 below display 3: J_n(chi, chi'). -/
noncomputable def pairSum (N : ℕ) (P : ℝ) (n : ℤ) (x y : PChar) : ℂ :=
  ∑ q ∈ pairModuli P x y,
    (1 / (q.totient : ℂ) ^ 2) * pairCoeff n q x y * arcIntegral N P n q x y

/-- Gallagher 1975 p.129 below display 4: C_n(chi, chi'). -/
noncomputable def pairWeight (P : ℝ) (n : ℤ) (x y : PChar) : ℝ :=
  ∑ q ∈ pairModuli P x y, (1 / (q.totient : ℝ) ^ 2) * ‖pairCoeff n q x y‖

/-- Gallagher 1975 p.128 norm: ||A(chi)|| over |beta| at most 1/Q equal to P/N. -/
noncomputable def ampNorm (N : ℕ) (P : ℝ) (x : PChar) : ℝ :=
  Real.sqrt (∫ β in Set.Icc (-(P / N)) (P / N), ‖primeAmplitude x.2 N β‖ ^ 2)

/-- Gallagher 1975 p.130: ||R|| where A(1) equals T plus R. -/
noncomputable def remNorm (N : ℕ) (P : ℝ) : ℝ :=
  Real.sqrt (∫ β in Set.Icc (-(P / N)) (P / N),
    ‖primeAmplitude one.2 N β - principalMain N β‖ ^ 2)

/-- Gallagher 1975 p.130 display 11: the truncated singular series,
the sum over q at most P of (mu(q)/phi(q))^2 c_q(n). -/
noncomputable def singTrunc (P : ℝ) (n : ℤ) : ℂ :=
  ∑ q ∈ Icc 1 ⌊P⌋₊, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
    LeanLab.Linnik.Decomp1532b.ramanujanSum q n

end LeanLab.Linnik.MajorArcEnergy
