module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.ExceptionalSet.Statements
public import LeanLab.DERZ1997.Statements

/-!
P0071 A. Languasco, A. Perelli, A pair correlation hypothesis and the exceptional set in
Goldbach's problem, Mathematika 43 (1996), 349-361, published version, Padova repository.
Formulas read on rendered page images.

* `GMC θ`, the pair correlation type hypothesis (4), p. 350, as a Lean `Prop`.
* Theorem 1, estimate (3), Theorem 2, Theorem 3, Theorem 4, Corollary 2, Lemmas 1 and 2 of
  Section 3: CITED. Hardy and Littlewood under GRH: CITED.
* Corollary 1, p. 351: CONDITIONAL ON `GMC θ` and the cited Theorems 2 and 3. The derivation
  of the first assertion from Theorems 2 and 3, and of the second from the first by
  subdivision, are PROVED here, as is the passage to the lab's `ExceptionalSet.E`.

The zero sums use `∑ᶠ` over the set of non-trivial zeros with `abs γ ≤ T`, weighted by the
analytic order; that set is finite, a fact not proved here, and `∑ᶠ` would read `0` otherwise.

AI-written Lean code, Claude, 2026-10-18, run 20261018T1603Z-12862.
Checked only by the Lean kernel. Binary Goldbach is OPEN; GRH and GMC are unproved hypotheses.
-/

@[expose] public section

namespace LeanLab.LanguascoPerelli1996
open Real Filter Topology ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-! ### Zeros, Gauss sums, the pair correlation function, Section 1 p. 349 -/

/-- `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- Montgomery's weight `w(u) = 4/(4+u²)`. -/
noncomputable def w (u : ℝ) : ℝ := 4 / (4 + u ^ 2)

/-- Non-trivial zeros `ρ` of `L(s,χ)` with `abs (Im ρ) ≤ T`, taken in `0 < Re s < 1`. -/
def ntZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Set ℂ :=
  {ρ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

/-- Multiplicity of a zero. -/
noncomputable def mult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/-- `τ(χ) = Σ_a χ(a) e(a/q)`. -/
noncomputable def tau {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  gaussSum χ ZMod.stdAddChar

/-- `Σ_{abs γ₁, abs γ₂ ≤ T} X^{i(γ₁-γ₂)} w(γ₁-γ₂)`, zeros counted with multiplicity. -/
noncomputable def pairSum {q : ℕ} [NeZero q] (X T : ℝ) (χ₁ χ₂ : DirichletCharacter ℂ q) : ℂ :=
  ∑ᶠ (ρ₁ ∈ ntZeros χ₁ T) (ρ₂ ∈ ntZeros χ₂ T),
    ((mult χ₁ ρ₁ * mult χ₂ ρ₂ : ℕ) : ℂ) *
      Complex.exp (Complex.I * ((ρ₁.im - ρ₂.im : ℝ) : ℂ) * (Real.log X : ℂ)) *
      (w (ρ₁.im - ρ₂.im) : ℂ)

/-- `F` AS PRINTED on p. 349: `Σ_{χ₁,χ₂ mod q} χ₁(a) χ̄₂(a) τ(χ̄₁) τ(χ₂) Σ X^{i(γ₁-γ₂)} w(γ₁-γ₂)`;
`χ⁻¹` is `χ̄`. A `def` only: it does not satisfy the paper's own identity (11), p. 354, see `F`. -/
noncomputable def FPrinted (X T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) : ℂ :=
  ∑ χ₁ : DirichletCharacter ℂ q, ∑ χ₂ : DirichletCharacter ℂ q,
    χ₁ (a : ZMod q) * starRingEnd ℂ (χ₂ (a : ZMod q)) * tau χ₁⁻¹ * tau χ₂ * pairSum X T χ₁ χ₂

/-- `F(X,T;q,a)` as identity (11), p. 354, defines it: `F = ∫ |Σ_χ χ(a)τ(χ̄) Σ_γ X^{iγ}e^{iγv}|²
e^{-2|v|} dv` expands to `Σ_{χ₁,χ₂} χ₁(a) χ̄₂(a) τ(χ̄₁) conj(τ(χ̄₂)) Σ X^{i(γ₁-γ₂)} w(γ₁-γ₂)`, and
`conj(τ(χ̄₂)) = χ₂(-1) τ(χ₂)`, not the printed `τ(χ₂)`. Changed from the printed form by audit
U-0965, run 20261019T0202Z-9877: with the printed `F` the diagonal carries `χ(-1)` and the cited
Theorem 1 asymptotic was false, an unsound placeholder proof. -/
noncomputable def F (X T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) : ℂ :=
  ∑ χ₁ : DirichletCharacter ℂ q, ∑ χ₂ : DirichletCharacter ℂ q,
    χ₁ (a : ZMod q) * starRingEnd ℂ (χ₂ (a : ZMod q)) * tau χ₁⁻¹ * starRingEnd ℂ (tau χ₂⁻¹) *
      pairSum X T χ₁ χ₂

abbrev GRH : Prop := LeanLab.DERZ1997.GRH

/-- **Theorem 1**, p. 350. Under GRH, for `A > 1`, `F(X,T;q,a) ~ (1/π) φ(q)² T log X`
uniformly for `X log X ≤ T ≤ X^A` and `q ≤ X log^{-4} X`. -/
def Theorem1 : Prop :=
  GRH → ∀ A : ℝ, 1 < A → ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ T : ℝ,
    X * Real.log X ≤ T → T ≤ X ^ A → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X / Real.log X ^ 4 →
    ∀ a : ℕ, Nat.Coprime a q →
      ‖F X T q a - ((1 / π * (Nat.totient q : ℝ) ^ 2 * T * Real.log X : ℝ) : ℂ)‖ ≤
        η * (1 / π * (Nat.totient q : ℝ) ^ 2 * T * Real.log X)

/-- Estimate (3), p. 350: `F(X,T;q,a) ≪_A q² T log X` for `X ≤ T ≤ X^A`, `q ≤ X log^{-3} X`. -/
def Estimate3 : Prop :=
  GRH → ∀ A : ℝ, 1 < A → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ T : ℝ, X ≤ T → T ≤ X ^ A →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X / Real.log X ^ 3 → ∀ a : ℕ, Nat.Coprime a q →
      ‖F X T q a‖ ≤ C * (q : ℝ) ^ 2 * T * Real.log X

/-- **The hypothesis `GMC(θ)`**, (4), p. 350. Assume GRH, `θ ∈ (0, 1/2]`, `V = X^{1-θ}/q`; then
for every `ε > 0`, `F(X,T;q,a) ≪_ε q² T X^ε` uniformly for `V ≤ T ≤ X`, `q ≤ X^θ`, `(a,q) = 1`. -/
def GMC (θ : ℝ) : Prop :=
  GRH ∧ ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ (q : ℕ) [NeZero q],
    (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q → ∀ T : ℝ, X ^ (1 - θ) / q ≤ T → T ≤ X →
      ‖F X T q a‖ ≤ C * (q : ℝ) ^ 2 * T * X ^ ε

/-- **`GMC(θ;ξ)`**, p. 351, `ξ = ξ(X,q) ∈ (0, 1/2]`, `W = Xξ/2`. -/
def GMCxi (θ : ℝ) (ξ : ℝ → ℕ → ℝ) : Prop :=
  GRH ∧ (∀ X q, 0 < ξ X q ∧ ξ X q ≤ 1 / 2) ∧
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ (q : ℕ) [NeZero q],
    (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q → ∀ T : ℝ, X * ξ X q / 2 ≤ T → T ≤ X →
      ‖F X T q a‖ ≤ C * (q : ℝ) ^ 2 * T * X ^ ε

/-! ### The exceptional set and the exponential sums, p. 350 -/

/-- `E(X,H)`, the number of even `2n ∈ [X, X+H]` that are not a sum of two primes. -/
noncomputable def EH (X H : ℝ) : ℕ :=
  ((Finset.Icc ⌈X⌉₊ ⌊X + H⌋₊).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)).card

/-- `S(α) = Σ_{X/4 ≤ n ≤ 2X} Λ(n) e(nα)`; the lower limit `X/4` is checked on the image. -/
noncomputable def S (X α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊, (Λ n : ℂ) * e (n * α)

/-- `T(α) = Σ_{X/4 ≤ n ≤ 2X} e(nα)`. -/
noncomputable def Tsum (X α : ℝ) : ℂ := ∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊2 * X⌋₊, e (n * α)

/-- `μ(q)/φ(q)`. -/
noncomputable def muPhi (q : ℕ) : ℝ := ((moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ)

/-- `R(η;q,a) = S(a/q + η) - μ(q)/φ(q) T(η)`. -/
noncomputable def R (X η : ℝ) (q a : ℕ) : ℂ :=
  S X ((a : ℝ) / q + η) - (muPhi q : ℂ) * Tsum X η

/-- `I(X,Q;q,a) = ∫_{-1/qQ}^{1/qQ} abs R(η;q,a)² dη`. -/
noncomputable def Ival (X Q : ℝ) (q a : ℕ) : ℝ :=
  ∫ η in (-(1 / (q * Q)))..(1 / (q * Q)), ‖R X η q a‖ ^ 2

/-- Hypothesis (5) for a choice `Q = Q(X)`: `I(X,Q;q,a) ≪_ε X^{1+ε}/(qQ)` uniformly for
`q ≤ Q`, `(a,q) = 1`, for every `ε > 0`. -/
def Bound5 (Q : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q X →
    ∀ a : ℕ, Nat.Coprime a q → Ival X (Q X) q a ≤ C * X ^ (1 + ε) / (q * Q X)

/-- **Theorem 2**, p. 350. Assume GRH, `ε > 0`, `X^ε ≤ Q ≤ X^{1/2}/2`, and (5). Then
`E(X, 4Q²) ≪_ε X^ε`. Read with the paper's convention that `ε` is arbitrarily small and may
change: a fixed `ε₀` in the range of `Q`, (5) for every `ε`, the conclusion for every `ε`. -/
def Theorem2 : Prop :=
  GRH → ∀ ε0 : ℝ, 0 < ε0 → ∀ Q : ℝ → ℝ,
    (∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X → X ^ ε0 ≤ Q X ∧ Q X ≤ X ^ (1 / 2 : ℝ) / 2) → Bound5 Q →
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X → (EH X (4 * Q X ^ 2) : ℝ) ≤ C * X ^ ε

/-- **Theorem 3**, p. 351. For `θ ∈ (0, 1/2]`, `Q = X^θ/2`, `GMC(θ)` implies (5). -/
def Theorem3 : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → GMC θ → Bound5 (fun X => X ^ θ / 2)

/-! ### Corollary 1 and its parts, p. 351 -/

/-- First assertion of Corollary 1: `E(X, X^{2θ}) ≪_ε X^ε`. -/
def ShortBound (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X → (EH X (X ^ (2 * θ)) : ℝ) ≤ C * X ^ ε

/-- `E(X) = E(X,X) ≪_ε X^{b+ε}`, the paper's `E(X)` counts `[X, 2X]`. -/
def DyadicBound (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X → (EH X X : ℝ) ≤ C * X ^ (b + ε)

/-! ### Theorem 4, Corollary 2, Lemmas 1 and 2 -/

/-- **Theorem 4**, p. 351. Under `GMC(θ;ξ)`, for every `ε > 0`,
`S(a/q + η) = μ(q)/φ(q) T(η) + O_ε(X^{1/2+ε}(1 + (Xξ)^{1/2}))`, `q ≤ X^θ`, `abs η ≤ ξ`. -/
def Theorem4 : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ ξ : ℝ → ℕ → ℝ, GMCxi θ ξ →
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ →
      ∀ a : ℕ, Nat.Coprime a q → ∀ η : ℝ, |η| ≤ ξ X q →
        ‖R X η q a‖ ≤ C * X ^ (1 / 2 + ε) * (1 + (X * ξ X q) ^ (1 / 2 : ℝ))

/-- **Corollary 2**, p. 352. Under `GMC(θ)`, `Q = X^θ/2`, for every `ε > 0`,
`S(a/q + η) = μ(q)/φ(q) T(η) + O_ε(X^{1+ε}/(qQ)^{1/2})`, `q ≤ Q`, `abs η ≤ 1/(qQ)`. -/
def Corollary2 : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → GMC θ →
    ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ X ^ θ / 2 → ∀ a : ℕ, Nat.Coprime a q → ∀ η : ℝ, |η| ≤ 1 / (q * (X ^ θ / 2)) →
        ‖R X η q a‖ ≤ C * X ^ (1 + ε) / (q * (X ^ θ / 2)) ^ (1 / 2 : ℝ)


/-- `Σ_χ χ(a) τ(χ̄) Σ_{U < abs γ ≤ T} y^{iγ}`, the sum of Lemmas 1 and 2, Section 3. -/
noncomputable def zSum (y U T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) : ℂ :=
  ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
    ∑ᶠ ρ ∈ ntZeros χ T \ {ρ | |ρ.im| ≤ U},
      (mult χ ρ : ℂ) * Complex.exp (Complex.I * (ρ.im : ℂ) * (Real.log y : ℂ))

/-- **Lemma 1**, p. 354: `∫_{αX}^{βX} abs (Σ_χ χ(a)τ(χ̄) Σ_{abs γ ≤ T} y^{iγ})² dy ≪ X F(X,T;q,a)`
for `c ≤ α < β ≤ C`. GRH is added as a hypothesis, the setting of Section 3. -/
def Lemma1 : Prop :=
  GRH → ∀ c C : ℝ, 0 < c → c < C → ∃ K : ℝ, ∀ X : ℝ, 0 < X → ∀ T : ℝ, 0 ≤ T →
    ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q → ∀ α β : ℝ, c ≤ α → α < β → β ≤ C →
      ∫ y in (α * X)..(β * X), ‖zSum y (-1) T q a‖ ^ 2 ≤ K * X * ‖F X T q a‖

/-- **Lemma 2**, p. 354: for `T > U ≥ 0` and `T ≥ 1`,
`Σ_χ χ(a)τ(χ̄) Σ_{U < abs γ ≤ T} X^{iγ} ≪ T^{1/2} max_{U ≤ u ≤ T} F(X,u;q,a)^{1/2}`.
The page prints only `T > U ≥ 0`; `T ≥ 1` is the paper's large parameter convention for
its `≪` bound, used on p. 355 when display (12) is absorbed into display (13).
Amended by unit U-1566, DECISION 2026-10-26T1900Z. -/
def Lemma2 : Prop :=
  GRH → ∃ K : ℝ, ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T → 1 ≤ T →
    ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q → ∀ M : ℝ,
      (∀ u, U ≤ u → u ≤ T → ‖F X u q a‖ ≤ M) →
        ‖zSum X U T q a‖ ≤ K * T ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ)



/-- Vacuity instance for the amended Lemma 2: the hypotheses
`0 < X`, `0 ≤ U`, `U < T`, `1 ≤ T`, `Nat.Coprime a q` hold at `X = 1, U = 0, T = 1, q = 1, a = 1`. -/
theorem lemma2_hyps_satisfiable :
    ∃ X U T : ℝ, ∃ q a : ℕ, 0 < X ∧ 0 ≤ U ∧ U < T ∧ 1 ≤ T ∧ 0 < q ∧ Nat.Coprime a q :=
  ⟨1, 0, 1, 1, 1, by norm_num, le_rfl, by norm_num, le_rfl, by norm_num, by norm_num⟩

/-! ### PROVED: Theorems 2 and 3 give the first assertion of Corollary 1 -/

theorem four_Q_sq {X θ : ℝ} (hX : 0 < X) : 4 * (X ^ θ / 2) ^ 2 = X ^ (2 * θ) := by
  rw [show 4 * (X ^ θ / 2) ^ 2 = (X ^ θ) ^ (2 : ℕ) by ring, ← Real.rpow_natCast,
    ← Real.rpow_mul hX.le]
  norm_num [mul_comm]

theorem Q_range {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1 / 2) :
    ∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X →
      X ^ (θ / 2) ≤ X ^ θ / 2 ∧ X ^ θ / 2 ≤ X ^ (1 / 2 : ℝ) / 2 := by
  refine ⟨max 1 ((2 : ℝ) ^ (2 / θ)), fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hX2 : (2 : ℝ) ^ (2 / θ) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := by linarith
  constructor
  · have h2 : (2 : ℝ) ≤ X ^ (θ / 2) := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (2 / θ)) ^ (θ / 2) := by
            rw [← Real.rpow_mul (by norm_num)]
            rw [show 2 / θ * (θ / 2) = 1 by field_simp]; norm_num
        _ ≤ X ^ (θ / 2) := Real.rpow_le_rpow (by positivity) hX2 (by linarith)
    have hsplit : X ^ θ = X ^ (θ / 2) * X ^ (θ / 2) := by
      rw [← Real.rpow_add hXpos]; ring_nf
    have hp : 0 < X ^ (θ / 2) := Real.rpow_pos_of_pos hXpos _
    rw [hsplit]; nlinarith
  · have := Real.rpow_le_rpow_of_exponent_le hX1 h1
    linarith

/-- Corollary 1, first assertion, from Theorems 2 and 3: `GMC(θ)` gives `E(X,X^{2θ}) ≪ X^ε`. -/
theorem shortBound_of_theorems (h2 : Theorem2) (h3 : Theorem3) {θ : ℝ} (h0 : 0 < θ)
    (h1 : θ ≤ 1 / 2) (hG : GMC θ) : ShortBound θ := by
  intro ε hε
  obtain ⟨C, X0, hC⟩ := h2 hG.1 (θ / 2) (by linarith) (fun X => X ^ θ / 2) (Q_range h0 h1)
    (h3 θ h0 h1 hG) ε hε
  refine ⟨C, max X0 1, fun X hX => ?_⟩
  have hXpos : 0 < X := by linarith [le_max_right X0 1]
  have := hC X (le_trans (le_max_left _ _) hX)
  simpa [four_Q_sq hXpos] using this

/-! ### PROVED: the second assertion of Corollary 1 from the first, by subdivision -/

theorem EH_subdivide {β ε C X0 : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (h : ∀ Y : ℝ, X0 ≤ Y → (EH Y (Y ^ β) : ℝ) ≤ C * Y ^ ε) :
    ∀ X : ℝ, max X0 1 ≤ X → (EH X X : ℝ) ≤ (2 * 2 ^ ε * C) * X ^ (1 - β + ε) := by
  intro X hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : X0 ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 0 < X := by linarith
  have hXb : 0 < X ^ β := Real.rpow_pos_of_pos hXpos β
  have hprod : X ^ (1 - β) * X ^ β = X := by
    rw [← Real.rpow_add hXpos]; norm_num
  set m := ⌊X ^ (1 - β)⌋₊ + 1 with hm
  let Y : ℕ → ℝ := fun j => X + j * X ^ β
  have hYge : ∀ j, X ≤ Y j := fun j => by
    have : (0 : ℝ) ≤ j * X ^ β := by positivity
    simp only [Y]; linarith
  have hYle : ∀ j ∈ Finset.range m, Y j ≤ 2 * X := by
    intro j hj
    have hj' : j ≤ ⌊X ^ (1 - β)⌋₊ := by
      have := Finset.mem_range.mp hj; omega
    have hjr : (j : ℝ) ≤ X ^ (1 - β) :=
      le_trans (by exact_mod_cast hj') (Nat.floor_le (by positivity))
    have : (j : ℝ) * X ^ β ≤ X ^ (1 - β) * X ^ β := by gcongr
    simp only [Y]; linarith
  -- the covering
  have hsub : (Finset.Icc ⌈X⌉₊ ⌊X + X⌋₊).filter (fun n => Even n ∧ ¬ IsGoldbachSum n) ⊆
      (Finset.range m).biUnion (fun j =>
        (Finset.Icc ⌈Y j⌉₊ ⌊Y j + Y j ^ β⌋₊).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hlo, hhi⟩, hP⟩ := hn
    have hnX : X ≤ n := Nat.ceil_le.mp hlo
    have hn2 : (n : ℝ) ≤ X + X :=
      le_trans (by exact_mod_cast hhi) (Nat.floor_le (by linarith))
    set t : ℝ := ((n : ℝ) - X) / X ^ β with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hXb.le
    have htX : t * X ^ β = n - X := by rw [ht]; field_simp
    have htle : t ≤ X ^ (1 - β) := by
      rw [ht, div_le_iff₀ hXb, hprod]; linarith
    rw [Finset.mem_biUnion]
    refine ⟨⌊t⌋₊, ?_, ?_⟩
    · rw [Finset.mem_range, hm]
      have := Nat.floor_le_floor htle
      omega
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.ceil_le.mpr ?_, Nat.le_floor ?_⟩, hP⟩
      · have : (⌊t⌋₊ : ℝ) * X ^ β ≤ t * X ^ β := by
          gcongr; exact Nat.floor_le ht0
        simp only [Y]; linarith
      · have hlt : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
        have : t * X ^ β ≤ ((⌊t⌋₊ : ℝ) + 1) * X ^ β := by gcongr
        have hXY : X ^ β ≤ Y ⌊t⌋₊ ^ β :=
          Real.rpow_le_rpow hXpos.le (hYge _) hβ0.le
        simp only [Y] at hXY ⊢
        nlinarith
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcardR : (EH X X : ℝ) ≤ ∑ j ∈ Finset.range m, (EH (Y j) (Y j ^ β) : ℝ) := by
    unfold EH; exact_mod_cast hcard
  have hterm : ∀ j ∈ Finset.range m, (EH (Y j) (Y j ^ β) : ℝ) ≤ C * (2 ^ ε * X ^ ε) := by
    intro j hj
    refine (h (Y j) (le_trans hX0 (hYge j))).trans ?_
    rw [← Real.mul_rpow (by norm_num) hXpos.le]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith [hYge j]) (hYle j hj) hε) hC
  have hsum := hcardR.trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hm1 : (m : ℝ) ≤ 2 * X ^ (1 - β) := by
    have h1 : (1 : ℝ) ≤ X ^ (1 - β) := Real.one_le_rpow hX1 (by linarith)
    have h2 : (⌊X ^ (1 - β)⌋₊ : ℝ) ≤ X ^ (1 - β) := Nat.floor_le (by positivity)
    rw [hm]; push_cast; linarith
  have hexp : X ^ (1 - β + ε) = X ^ (1 - β) * X ^ ε := Real.rpow_add hXpos _ _
  rw [hexp]
  have hpos : 0 ≤ C * (2 ^ ε * X ^ ε) := by positivity
  calc (EH X X : ℝ) ≤ m * (C * (2 ^ ε * X ^ ε)) := hsum
    _ ≤ (2 * X ^ (1 - β)) * (C * (2 ^ ε * X ^ ε)) := by gcongr
    _ = 2 * 2 ^ ε * C * (X ^ (1 - β) * X ^ ε) := by ring

/-- Corollary 1, second assertion from the first, the paper's subdivision of `[X, 2X]` into
`≪ X^{1-2θ}` intervals `[Y_j, Y_j + Y_j^{2θ}]`. -/
theorem dyadicBound_of_shortBound {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1 / 2) (h : ShortBound θ) :
    DyadicBound (1 - 2 * θ) := by
  intro ε hε
  obtain ⟨C, X0, hC⟩ := h ε hε
  refine ⟨2 * 2 ^ ε * max C 0, max (max X0 1) 1, fun X hX => ?_⟩
  refine EH_subdivide (X0 := max X0 1) (by linarith) (by linarith) hε.le (le_max_right _ _)
    (fun (Y : ℝ) hY => ?_) X hX
  have hY1 : (1 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
  exact (hC Y (le_trans (le_max_left _ _) hY)).trans (mul_le_mul_of_nonneg_right
    (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))

/-! ### PROVED: from the paper's `E(X) = E(X,X)` to the lab's `ExceptionalSet.E` -/

theorem E_le_half (N : ℕ) :
    LeanLab.ExceptionalSet.E N ≤ LeanLab.ExceptionalSet.E (N / 2) +
      EH ((N : ℝ) / 2) ((N : ℝ) / 2) := by
  unfold LeanLab.ExceptionalSet.E EH
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
  by_cases hle : n ≤ N / 2
  · left; exact ⟨⟨hn.1.1, hle⟩, hn.2⟩
  · right
    refine ⟨⟨Nat.ceil_le.mpr ?_, Nat.le_floor ?_⟩, hn.2⟩
    · have : N < 2 * n := by omega
      have : (N : ℝ) < 2 * n := by exact_mod_cast this
      linarith
    · have : (n : ℝ) ≤ N := by exact_mod_cast hn.1.2
      linarith

/-- A dyadic bound `E(X,X) ≤ C X^a`, `a > 0`, gives the lab's `PowerBound a`. -/
theorem powerBound_of_dyadic {a C X0 : ℝ} (ha : 0 < a)
    (h : ∀ X : ℝ, X0 ≤ X → (EH X X : ℝ) ≤ C * X ^ a) :
    LeanLab.ExceptionalSet.PowerBound a := by
  set C' := max C 0
  have h2a : (1 : ℝ) < 2 ^ a := Real.one_lt_rpow (by norm_num) ha
  set B := 2 * max X0 1
  set K := max B (C' / (2 ^ a - 1))
  have hKB : B ≤ K := le_max_left _ _
  have hKC : C' / (2 ^ a - 1) ≤ K := le_max_right _ _
  have hC' : 0 ≤ C' := le_max_right _ _
  have hB1 : (2 : ℝ) ≤ B := by simp only [B]; linarith [le_max_right X0 1]
  have claim : ∀ N : ℕ, (LeanLab.ExceptionalSet.E N : ℝ) ≤ K * (N : ℝ) ^ a := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      rcases Nat.eq_zero_or_pos N with rfl | hNpos
      · simp [LeanLab.ExceptionalSet.E, Real.zero_rpow ha.ne']
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
      have hNa : (1 : ℝ) ≤ (N : ℝ) ^ a := Real.one_le_rpow hN1 ha.le
      by_cases hsmall : (N : ℝ) ≤ B
      · have hE : (LeanLab.ExceptionalSet.E N : ℝ) ≤ N := by
          exact_mod_cast LeanLab.ExceptionalSet.E_le N
        have hK0 : 0 ≤ K := by linarith
        nlinarith
      · push Not at hsmall
        have hhalf : X0 ≤ (N : ℝ) / 2 := by
          have := le_max_left X0 1; simp only [B] at hsmall; linarith
        have hlt : N / 2 < N := Nat.div_lt_self hNpos (by norm_num)
        have ih' := ih (N / 2) hlt
        have hdiv : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := Nat.cast_div_le
        have hpow : ((N / 2 : ℕ) : ℝ) ^ a ≤ ((N : ℝ) / 2) ^ a :=
          Real.rpow_le_rpow (by positivity) hdiv ha.le
        have hK0 : 0 ≤ K := by linarith
        have hEH : (EH ((N : ℝ) / 2) ((N : ℝ) / 2) : ℝ) ≤ C' * ((N : ℝ) / 2) ^ a :=
          (h _ hhalf).trans (by gcongr; exact le_max_left _ _)
        have hsplit := E_le_half N
        have hsplitR : (LeanLab.ExceptionalSet.E N : ℝ) ≤ LeanLab.ExceptionalSet.E (N / 2) +
            (EH ((N : ℝ) / 2) ((N : ℝ) / 2) : ℝ) := by exact_mod_cast hsplit
        have hhalfpow : ((N : ℝ) / 2) ^ a = (N : ℝ) ^ a / 2 ^ a :=
          Real.div_rpow (by positivity) (by norm_num) a
        have h2pos : (0 : ℝ) < 2 ^ a := by positivity
        have hKC' : C' ≤ K * (2 ^ a - 1) := by
          rwa [div_le_iff₀ (by linarith)] at hKC
        calc (LeanLab.ExceptionalSet.E N : ℝ)
            ≤ K * ((N : ℝ) / 2) ^ a + C' * ((N : ℝ) / 2) ^ a := by
              have : K * ((N / 2 : ℕ) : ℝ) ^ a ≤ K * ((N : ℝ) / 2) ^ a := by gcongr
              linarith
          _ = (K + C') * ((N : ℝ) ^ a / 2 ^ a) := by rw [hhalfpow]; ring
          _ ≤ (K * 2 ^ a) * ((N : ℝ) ^ a / 2 ^ a) := by
              gcongr; linarith
          _ = K * (N : ℝ) ^ a := by field_simp
  exact ⟨K, fun X _ => claim X⟩

/-- `E(X) ≪ X^{b+ε}` on the paper's count gives `PowerBound (b+ε)` on the lab's count. -/
theorem powerBound_of_dyadicBound {b : ℝ} (hb : 0 ≤ b) (h : DyadicBound b) :
    ∀ ε : ℝ, 0 < ε → LeanLab.ExceptionalSet.PowerBound (b + ε) := by
  intro ε hε
  obtain ⟨C, X0, hC⟩ := h ε hε
  exact powerBound_of_dyadic (by linarith) hC

/-- The implication itself, PROVED: Theorems 2 and 3 and `GMC(θ)` give the lab bound. -/
theorem lab_powerBound_of_theorems (h2 : Theorem2) (h3 : Theorem3) {θ : ℝ} (h0 : 0 < θ)
    (h1 : θ ≤ 1 / 2) (hG : GMC θ) :
    ∀ ε : ℝ, 0 < ε → LeanLab.ExceptionalSet.PowerBound (1 - 2 * θ + ε) :=
  powerBound_of_dyadicBound (by linarith)
    (dyadicBound_of_shortBound h0 h1 (shortBound_of_theorems h2 h3 h0 h1 hG))

/-! ### PROVED: exponent arithmetic of p. 351-352 and comparison with the lab chain -/

/-- `GMC(θ)` improves on Hardy and Littlewood's `1/2` exactly when `θ > 1/4`, p. 351. -/
theorem beats_HL_iff (θ : ℝ) : 1 - 2 * θ < 1 / 2 ↔ 1 / 4 < θ := by
  constructor <;> intro h <;> linarith

/-- `GMC(θ)` improves on Zhao's `7/10` exactly when `θ > 3/20`. -/
theorem beats_zhao_iff (θ : ℝ) : 1 - 2 * θ < 7 / 10 ↔ 3 / 20 < θ := by
  constructor <;> intro h <;> linarith

/-- With `θ = 1/2`, `4Q² = X`, the full dyadic interval, and the exponent `1 - 2θ` is `0`. -/
theorem extreme_case : 1 - 2 * (1 / 2 : ℝ) = 0 ∧ 3 - 2 * (1 / 2 : ℝ) = 2 := by norm_num

/-- `GMC(θ)` for `θ > 3/20` gives Zhao's bound and the lab's whole older chain, PROVED from
Theorems 2 and 3 as hypotheses. -/
theorem zhao_of_theorems (h2 : Theorem2) (h3 : Theorem3) {θ : ℝ} (h0 : 3 / 20 < θ)
    (h1 : θ ≤ 1 / 2) (hG : GMC θ) : LeanLab.ExceptionalSet.PowerBound (7 / 10) := by
  have := lab_powerBound_of_theorems h2 h3 (by linarith) h1 hG (2 * θ - 3 / 10) (by linarith)
  convert this using 2; ring

/-- `GMC(1/2)` gives `E(X) ≪ X^ε` for every `ε`, on the lab's count, from Theorems 2, 3. -/
theorem eps_of_theorems_half (h2 : Theorem2) (h3 : Theorem3) (hG : GMC (1 / 2)) :
    ∀ ε : ℝ, 0 < ε → LeanLab.ExceptionalSet.PowerBound ε := by
  intro ε hε
  have := lab_powerBound_of_theorems h2 h3 (by norm_num) le_rfl hG ε hε
  convert this using 2; ring

end LeanLab.LanguascoPerelli1996

open LeanLab.LanguascoPerelli1996 in
section
end
