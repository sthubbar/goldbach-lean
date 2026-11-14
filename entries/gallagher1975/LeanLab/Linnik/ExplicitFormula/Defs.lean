module

public import Mathlib

/-!
# Explicit formula for primitive Dirichlet L-functions: definitions

Route burst 2026-11-12, session 6, branch claude/Linnik-explicit-formula. AI wrote the Lean code.
Binary Goldbach is OPEN; this is analytic infrastructure for Gallagher 1975 Theorem 3, display 14,
toward Linnik's theorem on primes and powers of 2.

Source: Davenport, Multiplicative Number Theory, 3rd ed., ch. 17 and 19, in the Cesaro form the lab
already proved for zeta in `LeanLab.PNTPort.ExplicitPsi1`, with the kernel `1/((s+1)(s+2))` in place
of `1/(s(s+1))`, so that no residue at `s = 0` from the kernel appears and the zero sum includes the
trivial zero at `0` of an even character as an ordinary term.

The Mellin transform of `w(y) = y(1 - y)` on `[0, 1]`, zero for `y > 1`, is
`∫₀¹ y^(s-1) y (1-y) dy = 1/((s+1)(s+2))`, so
`Σ χ(n) Λ(n) w(n/x) = (1/2πi) ∫_(2) -L'/L(s, χ) x^s /((s+1)(s+2)) ds`.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex Finset

/-- The Cesaro kernel `w(y) = y (1 - y)` for `y ≤ 1`, zero for `y > 1`. -/
noncomputable def wK (y : ℝ) : ℝ := if y ≤ 1 then y * (1 - y) else 0

/-- `S(x, χ) = Σ_{n ≤ x} χ(n) Λ(n) w(n/x)`. -/
noncomputable def cesaroChi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ range (⌊x⌋₊ + 1), χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * (wK (n / x) : ℂ)

/-- The integrand `F(s) = -L'/L(s, χ) x^s / ((s+1)(s+2))`. -/
noncomputable def Fchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  -(deriv χ.LFunction s / χ.LFunction s) * ((x : ℂ) ^ s / ((s + 1) * (s + 2)))

/-- The zeros of `L(s, χ)` with `Re ρ ≥ -1/2`, the point `1` excluded since Mathlib's `LFunction`
of the trivial character takes a junk value at its pole. -/
def Zall {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Set ℂ :=
  {ρ | χ.LFunction ρ = 0 ∧ -1 / 2 ≤ ρ.re ∧ ρ ≠ 1}

/-- The multiplicity of `ρ` as a zero of `L(s, χ)`, Mathlib's analytic order. -/
noncomputable def mult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt χ.LFunction ρ

/-- The zero term `m(ρ) x^ρ / ((ρ+1)(ρ+2))`. -/
noncomputable def zterm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (ρ : ℂ) : ℂ :=
  (mult χ ρ : ℂ) * ((x : ℂ) ^ ρ / ((ρ + 1) * (ρ + 2)))

/-- `b(n) = n χ(n) Λ(n)`, the coefficient seen by the doubled kernel. -/
noncomputable def bCoef {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  (n : ℂ) * χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- `J(x) = x² S(x, χ) = Σ_{n ≤ x} b(n) (x - n)`. -/
noncomputable def Jchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  (x : ℂ) ^ 2 * cesaroChi χ x

/-- `D_ρ(u) = u^(ρ+2) / ((ρ+1)(ρ+2))`, so that `x² zterm = m(ρ) D_ρ(x)` and `D_ρ'' = u^ρ`. -/
noncomputable def Dz (ρ : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ (ρ + 2) / ((ρ + 1) * (ρ + 2))

/-- A copy of `LeanLab.Linnik.Decomp486c.correctedCoefficient`, Gallagher 1975 pp.130 and 131,
restated here so that this folder does not import Decomp486c; the two agree by `rfl`. -/
noncomputable def corrCoef {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (r : ℕ) (γ : ℝ) (m : ℕ) : ℂ :=
  (if m.Prime then χ m else 0) -
    (if q = 1 then (if 1 < m then (1 / Real.log m : ℂ) else 0) else 0) +
    (if q = r ∧ χ.LFunction (γ : ℂ) = 0 then
      (if 1 < m then (((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) : ℂ) else 0) else 0)

open Classical in
/-- The zeros in `Zall χ` up to height `T`, as a finset when that set is finite, else empty;
for primitive `χ` it is finite by `zeros_rect_finite`. -/
noncomputable def zerosTo {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Finset ℂ :=
  if h : {ρ | ρ ∈ Zall χ ∧ |ρ.im| ≤ T}.Finite then h.toFinset else ∅

lemma wK_of_le {y : ℝ} (hy : y ≤ 1) : wK y = y * (1 - y) := by simp [wK, hy]

lemma wK_of_gt {y : ℝ} (hy : 1 < y) : wK y = 0 := by simp [wK, not_le.mpr hy]

end LeanLab.Linnik.ExplicitFormula
