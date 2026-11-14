module

public import Mathlib
public import LeanLab.BhowmikGrimmelt2026.Minor84
public import LeanLab.BhowmikGrimmelt2026.GallagherStandard261
public import LeanLab.Common.Goldbach
public import LeanLab.ExceptionalSet.Statements
public import LeanLab.LanguascoPerelli1996.Statements
public import LeanLab.DERZ1997.Statements

/-!
P0029 G. Bhowmik and L. Grimmelt 2026, "The exceptional set of the Goldbach problem",
arXiv 2607.27282 v2, 33 pages. Unit U-0959, run 20261018T1603Z-12862.

The paper is mostly a survey. Its new results are the fully explicit major arc formula of
Section 7, Proposition 7.5, and Theorem 8.2 of Section 8 on Siegel zeros under a sparse
Hardy-Littlewood hypothesis. It proves NO new exponent for the exceptional set: the best
exponent it states is Pintz's `|E(X)| < X^0.72`, p. 25, which the lab's Zhao 2025 bound
`X^{7/10}` already beats, see `zhao_beats_survey` below.

Every constant below was read on the rendered page images, 150 and 300 dpi.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Analytic inputs remain cited here. Lemma 7.2 is proved in
Lemma72Proof.lean by CODEX task46 from Poisson summation, without a cited input.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-! ## Basic objects -/

/-- Ramanujan sum `c_q(n) = Σ_{a mod q, (a,q)=1} e(an/q)`, p. 26 line above (7.4). -/
noncomputable def ramanujan (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ee ((a : ℝ) * n / q)

/-- The singular series, (2.9) with `R → ∞`, p. 6, and p. 12:
`𝔖(N) = Σ_q μ(q)² c_q(N) / φ(q)²`. The Ramanujan sum is real, we take its real part. -/
noncomputable def singular (N : ℕ) : ℝ :=
  ∑' q : ℕ, (((moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2) * (ramanujan q N).re

/-- `r₂(N) = Σ_{n₁+n₂=N} Λ(n₁)Λ(n₂)`, p. 9. -/
noncomputable def r2 (N : ℕ) : ℝ := ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)), vonMangoldt x.1 * vonMangoldt x.2

/-- `E₂(N) = r₂(N) − N𝔖(N)`, p. 13. -/
noncomputable def E2 (N : ℕ) : ℝ := r2 N - N * singular N

/-- (1.1), p. 1: `𝓔(X) = {2 < N ≤ X, N even, N ≠ p₁ + p₂}`. -/
noncomputable def calE (X : ℕ) : Finset ℕ :=
  (Finset.Ioc 2 X).filter (fun N => Even N ∧ ¬ IsGoldbachSum N)

/-- PROVED: the paper's `|𝓔(X)|` is the lab's `ExceptionalSet.E X`. -/
theorem card_calE (X : ℕ) : (calE X).card = E X := by
  unfold calE LeanLab.ExceptionalSet.E
  congr 1
  ext N
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, he, hg⟩
    refine ⟨⟨?_, h2⟩, he, hg⟩
    obtain ⟨k, hk⟩ := he; omega
  · rintro ⟨⟨h1, h2⟩, he, hg⟩
    exact ⟨⟨by omega, h2⟩, he, hg⟩

/-! ## Section 2: the Hardy-Littlewood conjecture -/

/-- Conjecture 2.1, p. 7: for even `N → ∞`, `r₂(N) ∼ 𝔖(N) N`. A conjecture, not asserted. -/
def HLConjecture : Prop :=
  Tendsto (fun n : ℕ => r2 (2 * n) / ((2 * n : ℕ) * singular (2 * n))) atTop (𝓝 1)

/-! ## Section 3: Hardy-Littlewood under a zero-free hypothesis -/

/-- "every zero of every Dirichlet L-function has real part at most Θ", p. 9. Zeros are taken
in the open strip `0 < Re s < 1`: trivial zeros have `Re s ≤ 0 ≤ Θ` anyway, and the strip
avoids the junk value of Mathlib's `LFunction` of a principal character at `s = 1`. -/
def ZeroBound (Θ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re ≤ Θ

/-- Theorem 3.1, p. 9: if `ZeroBound Θ` with `Θ < 3/4`, then `|𝓔(X)| ≪_ε X^{2Θ − 1/2 + ε}`. -/
def Theorem31 : Prop :=
  ∀ Θ : ℝ, Θ < 3 / 4 → ZeroBound Θ → ∀ ε : ℝ, 0 < ε → PowerBound (2 * Θ - 1 / 2 + ε)

/-- (3.8), p. 13: under the hypothesis of Theorem 3.1, `Σ_{N≤X} |E₂(N)|² ≪ X^{3/2+2Θ+ε}`. -/
def MeanSquare38 : Prop :=
  ∀ Θ : ℝ, Θ < 3 / 4 → ZeroBound Θ → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
    ∑ N ∈ Finset.Icc 1 X, (E2 N) ^ 2 ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)

/-! ## Section 4: Siegel-Walfisz and Vinogradov -/

-- Proposition 4.1 is proved in Decomp84.lean with its original statement.

-- Lemma 4.2 with its original logarithm power nine is proved in Minor84.lean.

/-- Theorem 4.3, Chudakov, van der Corput, Estermann, p. 17: `|𝓔(X)| ≪_A X (log X)^{-A}`. -/
def theorem43_stmt : Prop := LogPowerSaving
-- PROVED unconditional as `theorem43` in BhowmikGrimmelt2026/Discharged.lean, audit U-1058.

/-! ## Section 5: power saving -/

/-- A primitive character, packaged with its modulus `r + 1`. -/
abbrev PChar := Σ r : ℕ, DirichletCharacter ℂ (r + 1)

/-- Real valued character. -/
def IsRealChar {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop := ∀ a, (χ a).im = 0

/-- "a Siegel zero of level R", p. 18: a primitive real character of conductor at most `R`
with a real zero `β > 1 − 1/log R`; we also ask `β < 1`. -/
def SiegelZero (R : ℝ) (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (β : ℝ) : Prop :=
  χ.IsPrimitive ∧ IsRealChar χ ∧ (r : ℝ) ≤ R ∧ 1 - 1 / Real.log R < β ∧ β < 1 ∧
    DirichletCharacter.LFunction χ β = 0

/-- `Σ_{r ≤ R} Σ*_{χ mod r} F(r, χ)`, the sum over primitive characters of modulus at most `R`. -/
noncomputable def primSum (R : ℝ) (F : ∀ r : ℕ, [NeZero r] → DirichletCharacter ℂ r → ℝ) : ℝ :=
  ∑ r ∈ Finset.range ⌊R⌋₊, ∑ χ : DirichletCharacter ℂ (r + 1),
    if χ.IsPrimitive then F (r + 1) χ else 0

/-- `max_{I ⊂ [1,N]} |Σ_{n ∈ I} f(n)| / (|I| + N/R)`, over real intervals `I = [x, y]`. -/
noncomputable def intervalMax (N : ℕ) (R : ℝ) (f : ℕ → ℂ) : ℝ :=
  ⨆ (x : ℝ) (y : ℝ) (_ : 1 ≤ x ∧ x ≤ y ∧ y ≤ N),
    ‖∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊y⌋₊, f n‖ / ((y - x) + N / R)

/-- Proposition 5.2, Gallagher, p. 18, parts (1) and (2). -/
def Prop52 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, ∀ R : ℝ,
    2 ≤ Real.exp (Real.sqrt (Real.log N)) → Real.exp (Real.sqrt (Real.log N)) ≤ R → R ≤ N →
    ((¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ), SiegelZero R r χ β) →
      primSum R (fun _ _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) ≤
        C * Real.exp (-c * Real.log N / Real.log R)) ∧
    (∀ (r₀ : ℕ) [NeZero r₀] (χ₀ : DirichletCharacter ℂ r₀) (β : ℝ), SiegelZero R r₀ χ₀ β →
      primSum R (fun r _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - (if χ = 1 then 1 else 0) +
          (if r = r₀ ∧ HEq χ χ₀ then (n : ℂ) ^ ((β : ℂ) - 1) else 0))) ≤
        C * (1 - β) * Real.log N * Real.exp (-c * Real.log N / Real.log R))

/-- Lemma 5.3, Gallagher, p. 19, AS PRINTED: the factor is `η`, the window `(x − η^{-1}, x]`.
Not asserted: `not_gallagherPrinted` in `Gallagher.lean` refutes it. -/
def GallagherPrinted : Prop :=
  ∃ C : ℝ, ∀ (N : ℕ) (a : ℕ → ℂ) (η : ℝ), 0 < η →
    ∫ β in (-η)..η, ‖∑ n ∈ Finset.Icc 1 N, a n * ee (β * n)‖ ^ 2 ≤
      C * ∫ x in (0 : ℝ)..(2 * N),
        η * ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => x - η⁻¹ < n ∧ (n : ℝ) ≤ x), a n‖ ^ 2

/-- Gallagher's lemma in its standard form, Gallagher 1970 Lemma 1, Montgomery's Topics
Lemma 1.9: factor `η²`, window of length `1/(2η)`. NOT from this paper; the paper's own
display (5.3) uses the factor `η²`. -/
def GallagherStandard : Prop :=
  ∃ C : ℝ, ∀ (N : ℕ) (a : ℕ → ℂ) (η : ℝ), 0 < η →
    ∫ β in (-η)..η, ‖∑ n ∈ Finset.Icc 1 N, a n * ee (β * n)‖ ^ 2 ≤
      C * η ^ 2 * ∫ x : ℝ,
        ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x + 1 / (2 * η)), a n‖ ^ 2

/-- Gallagher 1970, standard form, proved by specialization of the real frequency theorem. -/
theorem gallagherStandard : GallagherStandard := by
  exact ⟨Real.pi ^ 2, gallagher_standard_explicit261⟩

/-! ## Section 6: zero density and Pintz -/

/-- Theorem 6.1, Linnik, p. 21: the least prime `≡ a mod q` is `O(q^L)`. -/
def Theorem61 : Prop :=
  ∃ L C : ℝ, ∀ q : ℕ, 1 ≤ q → ∀ a : ℕ, Nat.Coprime a q →
    ∃ p : ℕ, p.Prime ∧ p % q = a % q ∧ (p : ℝ) ≤ C * (q : ℝ) ^ L

/-- `N(σ, T)`, p. 21, the zeros `ρ` of `ζ` with `Re ρ ≥ σ`, `|Im ρ| ≤ T`, as a set. -/
noncomputable def zetaN (σ T : ℝ) : ℕ :=
  Set.ncard {ρ : ℂ | riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T}

/-- `V(X, H) = ∫_X^{2X} |Σ_{x<n≤x+H} Λ(n) − H|² dx`, p. 22. -/
noncomputable def V (X H : ℝ) : ℝ :=
  ∫ x in X..(2 * X), (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, vonMangoldt n - H) ^ 2

/-- Theorem 6.2, p. 22: `N(σ,T) ≪ T^{A(1−σ)} (log T)^B` gives `V(X, X^θ) = o(X^{2θ} X)` for
`θ > 1 − 2/A`. The density hypothesis is read for `1/2 ≤ σ ≤ 1`, `T ≥ 2`. -/
def Theorem62 : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B →
    (∃ C : ℝ, ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaN σ T : ℝ) ≤ C * T ^ (A * (1 - σ)) * Real.log T ^ B) →
    ∀ θ : ℝ, 1 - 2 / A < θ →
      Tendsto (fun X : ℝ => V X (X ^ θ) / ((X ^ θ) ^ 2 * X)) atTop (𝓝 0)

/-- Gauss sum of the conjugate character, `τ(χ̄) = Σ_{m mod q} χ̄(m) e(m/q)`, p. 11. -/
noncomputable def tauConj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m : ZMod q, starRingEnd ℂ (χ m) * ee ((m.val : ℝ) / q)

/-- `c_χ(N)` for `χ mod q`. The paper never defines it; OUR READING is the twisted Ramanujan
sum `Σ_{a mod q} χ(a) e(aN/q)`, which is `c_q(N)` for the principal character. -/
noncomputable def cChi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℤ) : ℂ :=
  ∑ a : ZMod q, χ a * ee ((a.val : ℝ) * N / q)

/-- The term of modulus `q` in (6.4), (5.1), (7.10):
`A_q(N; χ₁, χ₂) = τ(\overline{χ₁χ₀^{(q)}}) τ(\overline{χ₂χ₀^{(q)}}) c_{χ₁χ₂χ₀^{(q)}}(N) / φ(q)²`,
zero unless `[r₁, r₂] | q`. -/
noncomputable def Aq {r₁ r₂ : ℕ} (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (N : ℤ) (q : ℕ) [NeZero q] : ℂ :=
  if h : r₁ ∣ q ∧ r₂ ∣ q then
    tauConj (DirichletCharacter.changeLevel h.1 χ₁) * tauConj (DirichletCharacter.changeLevel h.2 χ₂) *
      cChi (DirichletCharacter.changeLevel h.1 χ₁ * DirichletCharacter.changeLevel h.2 χ₂) N /
      (Nat.totient q : ℂ) ^ 2
  else 0

/-- The generalised singular series (6.4), p. 23. -/
noncomputable def genSing {r₁ r₂ : ℕ} (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (N : ℤ) : ℂ :=
  ∑' q : ℕ, Aq χ₁ χ₂ N (q + 1)

/-- (6.5), p. 23, Pintz's Main Lemma: `|𝔖(χ₁, χ₂, N)| ≤ 𝔖(N)` for primitive characters. -/
def Bound65 : Prop :=
  ∀ (r₁ r₂ : ℕ) [NeZero r₁] [NeZero r₂] (χ₁ : DirichletCharacter ℂ r₁)
    (χ₂ : DirichletCharacter ℂ r₂), χ₁.IsPrimitive → χ₂.IsPrimitive →
    ∀ N : ℕ, 1 ≤ N → ‖genSing χ₁ χ₂ N‖ ≤ singular N

/-- The generalised exceptional zeros (6.2), (6.3), p. 23. -/
def calEZ (H T R X : ℝ) : Set (ℂ × PChar) :=
  {p | p.2.2.IsPrimitive ∧ ((p.2.1 + 1 : ℕ) : ℝ) ≤ R ∧
    DirichletCharacter.LFunction p.2.2 p.1 = 0 ∧ 1 - H / Real.log X ≤ p.1.re ∧ |p.1.im| ≤ T}

/-- `R_χ(β) = Σ_{n≤N} (Λ(n)χ(n) − 1_{χ=χ₀}) e(βn)`, p. 19. -/
noncomputable def Rchi (N : ℕ) {r : ℕ} (χ : DirichletCharacter ℂ r) (β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ((vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0) * ee (β * n)

/-- `E_𝔐(N)`, (5.1), p. 19. -/
noncomputable def EM (N : ℕ) (R : ℝ) : ℂ :=
  ∑ r₁ ∈ Finset.range ⌊R⌋₊, ∑ r₂ ∈ Finset.range ⌊R⌋₊,
    ∑ χ₁ : DirichletCharacter ℂ (r₁ + 1), ∑ χ₂ : DirichletCharacter ℂ (r₂ + 1),
      if χ₁.IsPrimitive ∧ χ₂.IsPrimitive then
        ∑ q ∈ Finset.range ⌊R⌋₊, Aq χ₁ χ₂ N (q + 1) *
          ∫ β in Set.Ioo (-(R / ((q + 1 : ℕ) * N))) (R / ((q + 1 : ℕ) * N)),
            Rchi N χ₁ β * Rchi N χ₂ β * ee (-(β * N))
      else 0

/-- `B(ϱ₁, ϱ₂) = Γ(ϱ₁)Γ(ϱ₂)/Γ(ϱ₁+ϱ₂)`, (6.9) and p. 30. -/
noncomputable def betaC (ϱ₁ ϱ₂ : ℂ) : ℂ :=
  Complex.Gamma ϱ₁ * Complex.Gamma ϱ₂ / Complex.Gamma (ϱ₁ + ϱ₂)

/-- Theorem 6.3, Pintz's explicit formula for the major arcs, (6.8), p. 24. OUR READING of the
quantifiers: `c` and `C` depend on `ε, ϑ` only, `X` large in terms of `H, T`; the sum over
`𝓔 × 𝓔` is over the set, as the paper writes it, `finsum`. -/
def Theorem63 : Prop :=
  ∀ ε ϑ : ℝ, 0 < ε → ε < ϑ → ϑ < 4 / 9 - ε → ∃ c C : ℝ, 0 < c ∧
    ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ N : ℕ, Even N →
      X / 2 ≤ N → (N : ℝ) ≤ X →
      ‖EM N (X ^ ϑ) - ∑ᶠ (p : (ℂ × PChar) × (ℂ × PChar))
          (_ : p.1 ∈ calEZ H T (X ^ ϑ) X ∧ p.2 ∈ calEZ H T (X ^ ϑ) X),
          genSing p.1.2.2 p.2.2.2 N * betaC p.1.1 p.2.1 * (N : ℂ) ^ (p.1.1 + p.2.1 - 1)‖ ≤
        C * (X * Real.exp (-c * H) + X / Real.sqrt T + X ^ (1 - ε))

/-! ## Section 7: a fully explicit formula -/

/-- Definition 7.1, p. 26: `G` smooth, non-negative, supported in `[-2,2]`, a positive constant on
`[-1,1]`, `∫ G = 1`; evenness is assumed in the proof of Lemma 7.2. -/
structure IsMajorWeight (G : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G
  nonneg : ∀ x, 0 ≤ G x
  supp : Function.support G ⊆ Set.Icc (-2) 2
  const : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1, G x = c
  integral_one : ∫ x, G x = 1
  even : ∀ x, G (-x) = G x

/-- `G_T(x) = T^{-1} G(x/T)`, p. 26. -/
noncomputable def GT (G : ℝ → ℝ) (T x : ℝ) : ℝ := T⁻¹ * G (x / T)

/-- `b_R(n) = Σ_{q≤R} c_q(n) G_{T_q}(n)`, (7.3), p. 26. -/
noncomputable def bR (G : ℝ → ℝ) (R : ℝ) (T : ℕ → ℝ) (n : ℤ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊R⌋₊, ramanujan q n * GT G (T q) n

/-- `b̂_R(α) = Σ_{n∈ℤ} b_R(n) e(−αn)`, p. 26. -/
noncomputable def bRhat (G : ℝ → ℝ) (R : ℝ) (T : ℕ → ℝ) (α : ℝ) : ℂ :=
  ∑' n : ℤ, bR G R T n * ee (-(α * n))

/-- Lemma 7.2, (7.5), p. 26, with `T_q = ηNq/R`. -/
def Lemma72 : Prop :=
  ∀ G : ℝ → ℝ, IsMajorWeight G → ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ (N : ℕ) (R η : ℝ),
    1 ≤ R → 0 < η → η ≤ 1 → 10 * R ^ 2 ≤ η * N → ∀ α : ℝ,
      (MajorArc N R α → ‖bRhat G R (fun q => η * N * q / R) α - 1‖ ≤
          C * (η ^ 2 + R ^ 2 * (η * N / R ^ 2) ^ (-A))) ∧
      (¬ MajorArc N R α → ‖bRhat G R (fun q => η * N * q / R) α‖ ≤
          C * (1 + R ^ 2 * (η * N / R ^ 2) ^ (-A)))

-- Lemma 7.2 is proved as lemma72 in Lemma72Proof.lean.
-- CODEX task46 replaced the cited placeholder with the exact proved statement.

/-- `φ ∈ C_c^∞(1/5, 4/5)`, `φ ≥ 0`, `∫₀¹ φ(t)φ(1−t) dt = 1`, (7.1), p. 25. -/
structure IsPhi (ϕ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϕ
  nonneg : ∀ x, 0 ≤ ϕ x
  compact : HasCompactSupport ϕ
  supp : tsupport ϕ ⊆ Set.Ioo (1 / 5) (4 / 5)
  norm_one : ∫ t in (0 : ℝ)..1, ϕ t * ϕ (1 - t) = 1

/-- `S_φ(α) = Σ_n Λ(n) φ(n/N) e(αn)`, (7.2), p. 25; `φ(n/N) = 0` for `n > N`. -/
noncomputable def Sphi (ϕ : ℝ → ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)

/-- `r_φ(N) = Σ_{n₁+n₂=N} Λ(n₁)φ(n₁/N)Λ(n₂)φ(n₂/N)`, p. 25. -/
noncomputable def rphi (ϕ : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
    vonMangoldt x.1 * ϕ (x.1 / N) * (vonMangoldt x.2 * ϕ (x.2 / N))

/-- Lemma 7.3, (7.8), p. 26. The paper leaves `T_q` open; OUR READING takes `T_q = ηXq/R` of
Proposition 7.5 and the hypothesis `10R² ≤ ηX`. QUESTION in STATEMENTS.md: the Parseval step
treats `S_φ` as independent of `N`, but (7.2) has `φ(n/N)`. -/
def Lemma73 : Prop :=
  ∀ ϕ G : ℝ → ℝ, IsPhi ϕ → IsMajorWeight G → ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 / 2 → ∃ C : ℝ,
    ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖(rphi ϕ N : ℂ) - ∫ α in (0 : ℝ)..1,
          Sphi ϕ N α ^ 2 * bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ) + η ^ 4) * (X : ℝ) ^ 3 * Real.log X ^ 5

/-- Multiplicity of a zero, the analytic order of `L(s, χ)` at `ρ`. -/
noncomputable def mult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/-- `∫₀^∞ Ψ(t) t^{s−1} dt`. -/
noncomputable def mellinR (Ψ : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) * (t : ℂ) ^ (s - 1)

/-- Lemma 7.4, smoothed explicit formula, (7.12), p. 27. Zeros counted with multiplicity. The
dependence "only on A and the C^∞ seminorms of Ψ" is a uniform `C` for all `Ψ` whose `k`-th
derivative is bounded by `M k`. -/
def Lemma74 : Prop :=
  ∀ A : ℝ, 0 < A → ∀ M : ℕ → ℝ, ∃ C : ℝ, ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → ∀ (S : ℝ) (Ψ : ℝ → ℝ), 1 ≤ S → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ →
      HasCompactSupport Ψ → tsupport Ψ ⊆ Set.Ioi S → (∀ k x, |iteratedDeriv k Ψ x| ≤ M k) →
      ‖∑' n : ℕ, (vonMangoldt n : ℂ) * χ n * (Ψ n : ℂ) -
          (if χ = 1 then ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) else 0) +
          ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ‖ ≤
        C * S ^ (-A)

/-- `I_q^φ(N; ρ₁, ρ₂)`, (7.14), p. 28, with `T = T_q`. -/
noncomputable def Iphi (ϕ G : ℝ → ℝ) (N T : ℝ) (ρ₁ ρ₂ : ℂ) : ℂ :=
  ∫ u₁ in Set.Ioi (0 : ℝ), ∫ u₂ in Set.Ioi (0 : ℝ),
    ((ϕ (u₁ / N) * ϕ (u₂ / N) * GT G T (N - u₁ - u₂) : ℝ) : ℂ) *
      (u₁ : ℂ) ^ (ρ₁ - 1) * (u₂ : ℂ) ^ (ρ₂ - 1)

/-- `B_φ(ρ₁, ρ₂)`, (7.18), p. 29. -/
noncomputable def Bphi (ϕ : ℝ → ℝ) (ρ₁ ρ₂ : ℂ) : ℂ :=
  ∫ σ in (0 : ℝ)..1, ((ϕ σ * ϕ (1 - σ) : ℝ) : ℂ) * (σ : ℂ) ^ (ρ₁ - 1) * ((1 - σ : ℝ) : ℂ) ^ (ρ₂ - 1)

/-- Lemma 7.6, (7.19) and (7.20), p. 29, for `0 < Re ρᵢ ≤ 1` and `1 ≤ T ≤ N`. -/
def Lemma76 : Prop :=
  ∀ ϕ G : ℝ → ℝ, IsPhi ϕ → IsMajorWeight G →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 →
      ‖Iphi ϕ G N T ρ₁ ρ₂‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + (|ρ₁.im| + |ρ₂.im|) * T / N) ^ (-A)) ∧
    (∃ C : ℝ, ∀ N T : ℝ, 1 ≤ T → T ≤ N → ∀ ρ₁ ρ₂ : ℂ,
      0 < ρ₁.re → ρ₁.re ≤ 1 → 0 < ρ₂.re → ρ₂.re ≤ 1 → |(ρ₁ + ρ₂).im| * T ≤ N →
      ‖Iphi ϕ G N T ρ₁ ρ₂ - Bphi ϕ ρ₁ ρ₂ * (N : ℂ) ^ (ρ₁ + ρ₂ - 1)‖ ≤
        C * N ^ ((ρ₁ + ρ₂).re - 1) * (1 + |(ρ₁ + ρ₂).im|) * T / N)

/-- `𝒵_R`, p. 28: pairs `(ρ, χ)`, `χ` primitive of conductor at most `R`, `ρ` any zero. -/
def ZR (R : ℝ) : Set (ℂ × PChar) :=
  {p | p.2.2.IsPrimitive ∧ ((p.2.1 + 1 : ℕ) : ℝ) ≤ R ∧ DirichletCharacter.LFunction p.2.2 p.1 = 0}

/-- Multiplicity of the zero in a pair. -/
noncomputable def multP (p : ℂ × PChar) : ℕ := mult p.2.2 p.1

/-- The trivial character `χ₀^{(1)}`. -/
noncomputable def chi1 : DirichletCharacter ℂ 1 := 1

/-- `𝓜(N; R)`, (7.15), p. 28, zeros with multiplicity. -/
noncomputable def Mterm (ϕ G : ℝ → ℝ) (N : ℕ) (R : ℝ) (T : ℕ → ℝ) : ℂ :=
  -∑' p : ZR R, (multP p : ℂ) * ∑ q ∈ Finset.range ⌊R⌋₊,
    (Aq chi1 p.1.2.2 N (q + 1) * Iphi ϕ G N (T (q + 1)) 1 p.1.1 +
      Aq p.1.2.2 chi1 N (q + 1) * Iphi ϕ G N (T (q + 1)) p.1.1 1)

/-- `𝒵(N; R)`, (7.16), p. 28, zeros with multiplicity. -/
noncomputable def Zterm (ϕ G : ℝ → ℝ) (N : ℕ) (R : ℝ) (T : ℕ → ℝ) : ℂ :=
  ∑' p : ZR R × ZR R, ((multP p.1 * multP p.2 : ℕ) : ℂ) * ∑ q ∈ Finset.range ⌊R⌋₊,
    Aq p.1.1.2.2 p.2.1.2.2 N (q + 1) * Iphi ϕ G N (T (q + 1)) p.1.1.1 p.2.1.1

/-- Proposition 7.5, (7.17), p. 28, the new fully explicit formula:
`R = X^ϑ`, `0 < ϑ < 4/9`, `η = R^{-1/4}`, `T_q = ηXq/R`. -/
def Prop75 : Prop :=
  ∀ ϕ G : ℝ → ℝ, IsPhi ϕ → IsMajorWeight G → ∀ ϑ : ℝ, 0 < ϑ → ϑ < 4 / 9 → ∃ C : ℝ,
    ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, ‖(rphi ϕ N : ℂ) - N * singular N -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5

/-! ## Section 8: a sparse Hardy-Littlewood conjecture and Siegel zeros -/

/-- (8.1), p. 30, from Pintz [20] Main Lemma: for even `N`,
`|𝔖(χ₀^{(1)}, χ̃, N)| ≪ 𝔖(N) r̃/φ(r̃)²`, and `𝔖(χ̃, χ̃, N) = χ̃(−1) 𝔖(N)` if `r̃ | N`. -/
def Facts81 : Prop :=
  (∃ C : ℝ, ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → IsRealChar χ →
    ∀ N : ℕ, Even N → 2 ≤ N →
      ‖genSing chi1 χ N‖ ≤ C * singular N * r / (Nat.totient r : ℝ) ^ 2) ∧
  (∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → IsRealChar χ →
    ∀ N : ℕ, Even N → 2 ≤ N → r ∣ N → genSing χ χ N = χ (-1) * singular N)

/-- Proposition 8.1, exceptional-zero Goldbach formula, (8.3), pp. 30 and 31:
`2/5 ≤ ϑ < 4/9`, `R = X^ϑ`, `𝓛 = log X`, `r̃ ≤ R`, `β̃ = 1 − δ̃`, `0 < δ̃ < h/𝓛`. The
implied constant `C` depends only on `ϑ`; the number of exceptions is `O_ε(X^{3/5+ε})`. -/
def Prop81 : Prop :=
  ∀ ϑ : ℝ, 2 / 5 ≤ ϑ → ϑ < 4 / 9 → ∃ h c' ε₀ C : ℝ, 0 < h ∧ 0 < c' ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ X : ℝ, 2 ≤ X →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δ : ℝ), χ.IsPrimitive → IsRealChar χ →
      (r : ℝ) ≤ X ^ ϑ → 0 < δ → δ < h / Real.log X →
      DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) = 0 →
      ((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun N => Even N ∧
          ¬ ‖(r2 N : ℂ) - singular N * N -
              genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            C * (singular N * X * (δ * Real.log X) ^ c' +
              singular N * N * r / (Nat.totient r : ℝ) ^ 2 + X ^ (1 - ε₀)))).card : ℕ) : ℝ) ≤
        Cε * X ^ (3 / 5 + ε)

/-- Theorem 8.2, p. 31, the paper's new theorem: fix `A > 5/2`, `δ ∈ (0,1)`; there are
`c = c(δ) > 0` and `r₀ = r₀(A, δ)` such that for `r̃ ≥ r₀`, `X = r̃^A`, if
`δ𝔖(N)N ≤ r₂(N) ≤ (2−δ)𝔖(N)N` for all but at most `X^{3/5}` even `N ∈ [X/2, X]` with `r̃ | N`,
then no primitive real `χ̃ mod r̃` has a real zero `β̃ > 1 − c/log X`. -/
def Theorem82 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 5 / 2 < A → ∃ r₀ : ℕ,
    ∀ (r : ℕ) [NeZero r], r₀ ≤ r →
      ((((Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊).filter (fun N => Even N ∧ r ∣ N ∧
          ¬ (δ * singular N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * singular N * N))).card : ℕ) : ℝ) ≤
        ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) →
      ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → IsRealChar χ →
        ∀ β : ℝ, DirichletCharacter.LFunction χ β = 0 → β ≤ 1 - c / Real.log ((r : ℝ) ^ A)

/-! ## PROVED: links to the lab and the paper's arithmetic -/

/-- GRH, the lab's `DERZ1997.GRH`, gives `ZeroBound (1/2)`. -/
theorem zeroBound_half_of_GRH (h : LeanLab.DERZ1997.GRH) : ZeroBound (1 / 2) :=
  fun q _ χ s hs h0 h1 => le_of_eq (h q χ s hs h0 h1)

theorem zeroBound_mono {Θ Θ' : ℝ} (hΘ : Θ ≤ Θ') (h : ZeroBound Θ) : ZeroBound Θ' :=
  fun q _ χ s hs h0 h1 => (h q χ s hs h0 h1).trans hΘ

/-- Theorem 3.1 at `Θ = 1/2`: GRH gives `|𝓔(X)| ≪ X^{1/2+ε}`, the Hardy-Littlewood bound the
lab states as `LanguascoPerelli1996.hardyLittlewood`. CONDITIONAL ON Theorem 3.1 and GRH. -/
theorem hl_of_GRH (h : Theorem31) (hG : LeanLab.DERZ1997.GRH) :
    ∀ ε : ℝ, 0 < ε → PowerBound (1 / 2 + ε) := by
  intro ε hε
  have := h (1 / 2) (by norm_num) (zeroBound_half_of_GRH hG) ε hε
  convert this using 2; ring

/-- The exponent of Theorem 3.1 is below 1 exactly when `Θ < 3/4`. -/
theorem thm31_exponent_lt_one (Θ : ℝ) : 2 * Θ - 1 / 2 < 1 ↔ Θ < 3 / 4 := by
  constructor <;> intro h <;> linarith

/-- Theorem 3.1 beats Zhao's `7/10` exactly when `Θ < 3/5`, and Pintz's `0.72` when `Θ < 0.61`. -/
theorem thm31_beats_zhao (Θ : ℝ) : 2 * Θ - 1 / 2 < 7 / 10 ↔ Θ < 3 / 5 := by
  constructor <;> intro h <;> linarith

theorem thm31_beats_pintz (Θ : ℝ) : 2 * Θ - 1 / 2 < 0.72 ↔ Θ < 0.61 := by
  constructor <;> intro h <;> norm_num at * <;> linarith

/-- CONDITIONAL ON Theorem 3.1: `ZeroBound Θ` with `Θ < 3/5` gives Zhao's `PowerBound (7/10)`. -/
theorem zhao_of_theorem31 (h : Theorem31) {Θ : ℝ} (hΘ : Θ < 3 / 5) (hZ : ZeroBound Θ) :
    PowerBound (7 / 10) := by
  have := h Θ (by linarith) hZ (7 / 10 - (2 * Θ - 1 / 2)) (by linarith)
  convert this using 2; ring

/-- Theorem 5.1 gives Theorem 4.3, through the lab's chain. -/
theorem theorem43_of_theorem51 (h : PowerSaving) : LogPowerSaving :=
  LeanLab.ExceptionalSet.estermann_of_montgomeryVaughan h

/-- The consequence of Proposition 6.4 gives Theorem 5.1, with `δ = 0.121` via Lu. -/
theorem theorem51_of_prop64 (h : EventuallyBelow 0.72) : PowerSaving :=
  LeanLab.ExceptionalSet.montgomeryVaughan_of_lu (LeanLab.ExceptionalSet.lu_of_pintz h)

/-- The survey's best exponent is `0.72`; the lab's Zhao 2025, `7/10 < 0.72`, implies it. -/
theorem zhao_beats_survey (h : PowerBound (7 / 10)) : EventuallyBelow 0.72 ∧ (7 / 10 : ℝ) < 0.72 :=
  ⟨LeanLab.ExceptionalSet.pintz_of_zhao h, by norm_num⟩

/-- Every exceptional set statement of the survey from Pintz's `X^{0.72}`. -/
theorem survey_chain (h : EventuallyBelow 0.72) :
    PowerSaving ∧ LogPowerSaving ∧ DensityZero := by
  have h1 := theorem51_of_prop64 h
  have h2 := theorem43_of_theorem51 h1
  exact ⟨h1, h2, LeanLab.ExceptionalSet.densityZero_of_estermann h2⟩

/-- Proposition 6.4 arithmetic, p. 25: `ϑ < 0.28` leaves `X^{1−ϑ}` minor arc exceptions with
`1 − ϑ > 0.72`; so these exceptions give `X^{0.72+ε}` for every `ε`, not `X^{0.72}` itself. -/
theorem prop64_exponent {ϑ : ℝ} (h : ϑ < 0.28) : (0.72 : ℝ) < 1 - ϑ := by
  norm_num at *; linarith

theorem pintz_eps_of_minor (h : ∀ ϑ : ℝ, ϑ < 0.28 → PowerBound (1 - ϑ)) :
    ∀ ε : ℝ, 0 < ε → PowerBound (0.72 + ε) := by
  intro ε hε
  have := h (0.28 - ε) (by linarith)
  convert this using 2; norm_num; ring

/-- Theorem 6.2 arithmetic, p. 22: for `X > 1`, `A > 0`, `H = X^θ`, `H^A > X^{A−2}` iff
`θ > 1 − 2/A`. -/
theorem thm62_iff {X A θ : ℝ} (hX : 1 < X) (hA : 0 < A) :
    X ^ (A - 2) < (X ^ θ) ^ A ↔ 1 - 2 / A < θ := by
  rw [← Real.rpow_mul (by linarith), Real.rpow_lt_rpow_left_iff hX]
  constructor
  · intro h
    have : 1 - θ < 2 / A := by rw [lt_div_iff₀ hA]; linarith
    linarith
  · intro h
    have : 1 - θ < 2 / A := by linarith
    rw [lt_div_iff₀ hA] at this; linarith

/-- Guth-Maynard `A = 30/13` gives `θ > 2/15`; Huxley `A = 12/5` gives `θ > 1/6`. -/
theorem guthMaynard_huxley :
    1 - 2 / (30 / 13 : ℝ) = 2 / 15 ∧ 1 - 2 / (12 / 5 : ℝ) = 1 / 6 ∧ (2 / 15 : ℝ) < 1 / 6 := by
  norm_num

/-- Proposition 8.1, p. 31: the minor arc term `X^{1+ε}/R` is dominated by `X^{3/5+ε}` exactly
when `ϑ ≥ 2/5`. -/
theorem prop81_minor_iff (ϑ : ℝ) : 1 - ϑ ≤ 3 / 5 ↔ 2 / 5 ≤ ϑ := by
  constructor <;> intro h <;> linarith

/-- Theorem 8.2 arithmetic, p. 31: for `A > 5/2`, `1/A < 2/5`, the chosen
`ε = (1 − 1/A − 3/5)/2` is positive and `3/5 + ε < 1 − 1/A`. -/
theorem thm82_arith {A : ℝ} (hA : 5 / 2 < A) :
    1 / A < 2 / 5 ∧ 0 < (1 - 1 / A - 3 / 5) / 2 ∧ 3 / 5 + (1 - 1 / A - 3 / 5) / 2 < 1 - 1 / A := by
  have hA0 : 0 < A := by linarith
  have h1 : 1 / A < 2 / 5 := by rw [div_lt_div_iff₀ hA0 (by norm_num)]; linarith
  refine ⟨h1, by linarith, by linarith⟩

/-- Theorem 8.2, p. 31: `r̃ = X^{1/A} < X^{2/5} = R`, here `r < (r^A)^{2/5}` for `r > 1`. -/
theorem thm82_cond_lt_R {A r : ℝ} (hA : 5 / 2 < A) (hr : 1 < r) : r < (r ^ A) ^ (2 / 5 : ℝ) := by
  rw [← Real.rpow_mul (by linarith)]
  conv_lhs => rw [← Real.rpow_one r]
  rw [Real.rpow_lt_rpow_left_iff hr]; linarith

/-- (7.9) from (7.8), p. 27: `X^{3−ϑ}` dominates `X^{13/5}` exactly when `ϑ ≤ 2/5`. -/
theorem eq79_dominant_iff (ϑ : ℝ) : (13 / 5 : ℝ) ≤ 3 - ϑ ↔ ϑ ≤ 2 / 5 := by
  constructor <;> intro h <;> linarith

/-- (7.9) from (7.8): with `R = X^ϑ`, `η = R^{-1/4}`, the bracket of (7.8) times `X³` is
`2X^{3−ϑ} + X^{13/5}`. -/
theorem eq79_arith {X ϑ : ℝ} (hX : 0 < X) :
    ((X ^ ϑ)⁻¹ + X ^ (-(2 / 5) : ℝ) + ((X ^ ϑ) ^ (-(1 / 4) : ℝ)) ^ 4) * X ^ 3 =
      2 * X ^ (3 - ϑ) + X ^ (13 / 5 : ℝ) := by
  have h4 : ((X ^ ϑ) ^ (-(1 / 4) : ℝ)) ^ 4 = (X ^ ϑ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_neg_one,
      ← Real.rpow_mul hX.le, ← Real.rpow_mul hX.le]
    norm_num
  rw [h4, ← Real.rpow_neg hX.le, ← Real.rpow_natCast X 3]
  have e1 : X ^ (-ϑ) * X ^ ((3 : ℕ) : ℝ) = X ^ (3 - ϑ) := by
    rw [← Real.rpow_add hX]; norm_num; ring_nf
  have e2 : X ^ (-(2 / 5) : ℝ) * X ^ ((3 : ℕ) : ℝ) = X ^ (13 / 5 : ℝ) := by
    rw [← Real.rpow_add hX]; norm_num
  linear_combination 2 * e1 + e2

/-- Chebyshev's step, p. 13 and p. 17: if `Σ f² ≤ B` then at most `B/m²` points have `|f| ≥ m`. -/
theorem card_le_of_sum_sq {s : Finset ℕ} {f : ℕ → ℝ} {B m : ℝ} (hm : 0 < m)
    (hB : ∑ n ∈ s, f n ^ 2 ≤ B) : ((s.filter (fun n => m ≤ |f n|)).card : ℝ) ≤ B / m ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have h1 : ((s.filter (fun n => m ≤ |f n|)).card : ℝ) * m ^ 2 ≤
      ∑ n ∈ s.filter (fun n => m ≤ |f n|), f n ^ 2 := by
    have := Finset.card_nsmul_le_sum (s.filter (fun n => m ≤ |f n|)) (fun n => f n ^ 2) (m ^ 2)
      (fun n hn => by
        rw [Finset.mem_filter] at hn
        have : m ^ 2 ≤ |f n| ^ 2 := by gcongr; exact hn.2
        simpa [sq_abs] using this)
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ n ∈ s.filter (fun n => m ≤ |f n|), f n ^ 2 ≤ ∑ n ∈ s, f n ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => sq_nonneg _)
  linarith

/-- The Hardy-Littlewood step of p. 13: from a mean square bound `B` for `E₂`, the `N ≤ X`
with `N𝔖(N) ≥ 2m` and `r₂(N) ≤ N𝔖(N)/2` number at most `B/m²`. -/
theorem exceptions_of_meanSquare {X : ℕ} {B m : ℝ} (hm : 0 < m)
    (hB : ∑ N ∈ Finset.Icc 1 X, (E2 N) ^ 2 ≤ B) :
    (((Finset.Icc 1 X).filter (fun N => 2 * m ≤ N * singular N ∧
        r2 N ≤ N * singular N / 2)).card : ℝ) ≤ B / m ^ 2 := by
  refine le_trans ?_ (card_le_of_sum_sq hm hB)
  exact_mod_cast Finset.card_le_card (fun N hN => by
    rw [Finset.mem_filter] at hN ⊢
    refine ⟨hN.1, ?_⟩
    unfold E2
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hN.2.1, hN.2.2])]
    linarith [hN.2.1, hN.2.2])

/-- The paper's dyadic count, even `N ∈ [X/2, X]` not a sum of two primes, as the lab's
`LanguascoPerelli1996.EH (X/2) (X/2)`. -/
noncomputable def Edy (X : ℝ) : ℕ := LeanLab.LanguascoPerelli1996.EH (X / 2) (X / 2)

/-- Dyadic to cumulative: `#{even N ∈ [X/2, X] exceptional} ≤ C X^a` for large `X`, `a > 0`,
gives the lab's `PowerBound a`. -/
theorem powerBound_of_dyadic_half {a C X₀ : ℝ} (ha : 0 < a)
    (h : ∀ X : ℝ, X₀ ≤ X → (Edy X : ℝ) ≤ C * X ^ a) : PowerBound a := by
  refine LeanLab.LanguascoPerelli1996.powerBound_of_dyadic (X0 := max (X₀ / 2) 0)
    (C := C * 2 ^ a) ha (fun Y hY => ?_)
  have hY0 : 0 ≤ Y := le_trans (le_max_right _ _) hY
  have hYX : X₀ ≤ 2 * Y := by linarith [le_max_left (X₀ / 2) 0]
  have := h (2 * Y) hYX
  simp only [Edy, show 2 * Y / 2 = Y by ring] at this
  rw [Real.mul_rpow (by norm_num) hY0] at this
  linarith

/-- `B_φ(1,1) = 1` by the normalisation (7.1); the paper writes `c_φ`, p. 29. -/
theorem Bphi_one_one {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) : Bphi ϕ 1 1 = 1 := by
  unfold Bphi
  simp only [sub_self, Complex.cpow_zero, mul_one]
  rw [intervalIntegral.integral_ofReal, hϕ.norm_one]; simp

end LeanLab.BhowmikGrimmelt2026
