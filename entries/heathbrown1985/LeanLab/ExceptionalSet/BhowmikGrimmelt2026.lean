module

public import Mathlib
public import LeanLab.ExceptionalSet.Statements

/-!
P0029 Bhowmik, Grimmelt, The exceptional set of the Goldbach problem, arXiv 2607.27282v2,
13 Aug 2026, read from papers/P0029.pdf, unit U-5041. Mostly a survey; the new results are the
fully explicit major arc formula of Section 7, Proposition 7.5, and Theorem 8.2 of Section 8:
a sparse Hardy-Littlewood hypothesis at the multiples of a conductor `r̃` rules out a Siegel zero
of conductor `r̃`.

Stated here, cited with `sorry`:
* Theorem 3.1, Hardy-Littlewood: zero-free for `Re s > Θ`, `Θ < 3/4`, gives `|E(X)| ≪ X^{2Θ-1/2+ε}`.
* Theorem 4.3, Chudakov, van der Corput, Estermann: `|E(X)| ≪_A X (log X)^{-A}`; the lab's `LogPowerSaving`.
* Theorem 5.1, Montgomery-Vaughan: `|E(X)| ≪ X^{1-δ}`; the lab's `PowerSaving`.
* Proposition 6.4 with the minor arcs, Pintz: `|E(X)| < X^{0.72}` for large `X`; the lab's `EventuallyBelow 0.72`.
* Theorem 8.2, new: `theorem82`.
* `Prop81AtMultiples`: what the proof of Theorem 8.2 on page 32 takes from Proposition 8.1, the
  identity `𝔖(χ̃, χ̃, N) = χ̃(-1) 𝔖(N)` of (8.1) and the choice of `c = c(δ)`; a cited Prop, not a
  statement of Proposition 8.1 itself, which needs Pintz's generalised singular series (6.4).

PROVED, no cited input: `C0_pos`, `Sing_pos`, `sq_eq_one_of_dirichlet_neg_one`, `dichotomy`,
`exists_good_multiple`. PROVED CONDITIONAL ON `Prop81AtMultiples`: `theorem82_of_prop81`.
Not stated: Lemmas 7.2, 7.3, 7.6 and Proposition 7.5, which need the zero sums `M(N; R)`, `Z(N; R)`
over zeros of all Dirichlet L-functions of conductor at most `R`; see STATEMENTS.md.

Binary Goldbach is OPEN; this paper bounds the exceptions and links them to Siegel zeros.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction

noncomputable section

/-! ### Definitions, Section 2 -/

/-- `r₂(N) = ∑_{n₁ + n₂ = N} Λ(n₁) Λ(n₂)`, page 4. -/
def r2 (N : ℕ) : ℝ := ∑ n ∈ range (N + 1), Λ n * Λ (N - n)

/-- `C₀ = ∏_{p > 2} (1 - 1/(p-1)²)`, as in Pintz2021/Statements.lean. -/
def C0 : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)

/-- The Hardy-Littlewood singular series for even `N`,
`𝔖(N) = 2 C₀ ∏_{p ∣ N, p > 2} (p-1)/(p-2)`, Conjecture 2.1. -/
def Sing (N : ℕ) : ℝ :=
  2 * C0 * ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2))

/-- A primitive real character of conductor `r` whose L-function has a real zero `β` with
`b < β < 1`, the object Theorem 8.2 rules out with `b = 1 - c / log X`. `β < 1` loses nothing,
since `L(s, χ) ≠ 0` for `Re s ≥ 1` and nontrivial `χ`. -/
def HasRealZeroAbove (r : ℕ) [NeZero r] (b : ℝ) : Prop :=
  ∃ χ : DirichletCharacter ℂ r, χ.IsPrimitive ∧ (∀ a, (χ a).im = 0) ∧
    ∃ β : ℝ, b < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ β = 0

/-- The even `N ∈ [X/2, X]` with `r ∣ N`. -/
def evenMult (r : ℕ) (X : ℝ) : Finset ℕ :=
  (Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun N => Even N ∧ r ∣ N)

/-- Hypothesis (8.4): `δ 𝔖(N) N ≤ r₂(N) ≤ (2 - δ) 𝔖(N) N` for all but at most `X^{3/5}` even
`N ∈ [X/2, X]` with `r ∣ N`. -/
def HL84 (r : ℕ) (δ X : ℝ) : Prop :=
  (((evenMult r X).filter (fun N =>
      ¬ (δ * Sing N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * Sing N * N))).card : ℝ) ≤ X ^ (3 / 5 : ℝ)

/-! ### The survey theorems, cited -/

/-- Every zero of every Dirichlet L-function has real part at most `Θ`. The point `s = 1` is left
out, since Mathlib's value there for a principal character is a convention at the pole. -/
def ZeroFreeBeyond (Θ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), Θ < s.re → s ≠ 1 →
    DirichletCharacter.LFunction χ s ≠ 0

/-- Theorem 3.1, Hardy-Littlewood. For `1/2 ≤ Θ < 3/4`; below `1/2` the hypothesis is false. -/
def Theorem31 : Prop :=
  ∀ Θ : ℝ, 1 / 2 ≤ Θ → Θ < 3 / 4 → ZeroFreeBeyond Θ →
    ∀ ε : ℝ, 0 < ε → PowerBound (2 * Θ - 1 / 2 + ε)


/-- Theorem 4.3, Chudakov, van der Corput, Estermann. -/
def theorem43_stmt : Prop := LogPowerSaving
-- PROVED unconditional as `theorem43` in ExceptionalSet/Discharged.lean, audit U-1058.



/-! ### Section 8 -/

/-- Theorem 8.2. Fix `A > 5/2` and `δ ∈ (0, 1)`. There are `c = c(δ) > 0` and `r₀ = r₀(A, δ)` such
that for every `r̃ ≥ r₀`, with `X = r̃^A`, if (8.4) holds then no primitive real character modulo
`r̃` has a real zero `β > 1 - c / log X`. The quantifiers follow the printed dependence: `c` before `A`. -/
def Theorem82 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 5 / 2 < A → ∃ r0 : ℕ, ∀ (r : ℕ) [NeZero r], r0 ≤ r →
    HL84 r δ ((r : ℝ) ^ A) → ¬ HasRealZeroAbove r (1 - c / Real.log ((r : ℝ) ^ A))


/-- What the proof of Theorem 8.2, page 32, takes from Proposition 8.1, the identity
`𝔖(χ̃, χ̃, N) = χ̃(-1) 𝔖(N)` for `r̃ ∣ N` of (8.1) and the choice of `c(δ)`: at a Siegel zero, outside a
set `B` small enough that some even multiple survives (8.4)'s exceptions, every even multiple `N`
of `r̃` in `[X/2, X]` has `r₂(N) = (1 + χ̃(-1) b) 𝔖(N) N + E` with `b = 1 + O(c)`, here
`|b - 1| < 3δ/4`, and `|E| ≤ (δ/4) 𝔖(N) N`. CITED, a packaging of the paper's argument. -/
def Prop81AtMultiples : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 5 / 2 < A → ∃ r0 : ℕ, ∀ (r : ℕ) [NeZero r], r0 ≤ r →
    ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → (∀ a, (χ a).im = 0) →
    (∃ β : ℝ, 1 - c / Real.log ((r : ℝ) ^ A) < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ β = 0) →
    ∃ B : Finset ℕ, (B.card : ℝ) + ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) < (evenMult r ((r : ℝ) ^ A)).card ∧
      ∀ N ∈ evenMult r ((r : ℝ) ^ A), N ∉ B → ∃ b E : ℝ, |b - 1| < 3 * δ / 4 ∧
        |E| ≤ δ / 4 * (Sing N * N) ∧ r2 N = (1 + (χ (-1)).re * b) * (Sing N * N) + E

/-! ### Proved parts -/

lemma summable_inv_sq_sub_one :
    Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => -(1 / ((p.1 : ℝ) - 1) ^ 2)) := by
  have hs : Summable (fun n : ℕ => 4 / (n : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 4
  refine Summable.of_norm_bounded (hs.comp_injective Subtype.coe_injective) (fun p => ?_)
  have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast p.2.2
  have hp1 : 0 < (p.1 : ℝ) - 1 := by linarith
  rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity), Function.comp_apply]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma C0_factor_pos (p : {p : ℕ // p.Prime ∧ 2 < p}) : 0 < 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 := by
  have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast p.2.2
  have h : 1 / ((p.1 : ℝ) - 1) ^ 2 < 1 := by
    rw [div_lt_one (by nlinarith)]; nlinarith
  linarith

/-- `C₀ > 0`. -/
theorem C0_pos : 0 < C0 := by
  have hsum := Real.summable_log_one_add_of_summable summable_inv_sq_sub_one
  have hpos : ∀ p : {p : ℕ // p.Prime ∧ 2 < p}, 0 < 1 + -(1 / ((p.1 : ℝ) - 1) ^ 2) := fun p => by
    have := C0_factor_pos p; linarith
  have := Real.rexp_tsum_eq_tprod hpos hsum
  unfold C0
  simp only [← sub_eq_add_neg] at this
  rw [← this]; exact Real.exp_pos _

/-- `𝔖(N) > 0`. -/
theorem Sing_pos (N : ℕ) : 0 < Sing N := by
  unfold Sing
  have hprod : 0 < ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2)) := by
    apply prod_pos
    intro p hp
    rw [mem_filter] at hp
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
    have : 0 < (p : ℝ) - 2 := by linarith
    positivity
  have := C0_pos
  positivity

/-- For a Dirichlet character, `χ(-1) = ±1`. -/
theorem sq_eq_one_of_dirichlet_neg_one {r : ℕ} (χ : DirichletCharacter ℂ r) :
    χ (-1) = 1 ∨ χ (-1) = -1 := by
  have h : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  exact mul_self_eq_one_iff.mp h

/-- The final step on page 32. If `r₂ = (1 + s b) M + E` with `s = ±1`, `|b - 1| < 3δ/4` and
`|E| ≤ (δ/4) M`, `M > 0`, then (8.4) at this `N`, `δ M ≤ r₂ ≤ (2 - δ) M`, fails. -/
theorem dichotomy {δ M b E r s : ℝ} (hM : 0 < M) (hs : s = 1 ∨ s = -1)
    (hb : |b - 1| < 3 * δ / 4) (hE : |E| ≤ δ / 4 * M) (hr : r = (1 + s * b) * M + E) :
    ¬ (δ * M ≤ r ∧ r ≤ (2 - δ) * M) := by
  rintro ⟨hlo, hhi⟩
  rw [abs_lt] at hb
  rw [abs_le] at hE
  rcases hs with rfl | rfl
  · nlinarith
  · nlinarith

/-- Pigeonhole on page 32: more even multiples than `|B|` plus the `X^{3/5}` exceptions of (8.4)
leave a multiple outside `B` where (8.4)'s inequalities hold. -/
theorem exists_good_multiple {r : ℕ} {δ X : ℝ} (B : Finset ℕ) (h84 : HL84 r δ X)
    (hcard : (B.card : ℝ) + X ^ (3 / 5 : ℝ) < (evenMult r X).card) :
    ∃ N ∈ evenMult r X, N ∉ B ∧ δ * Sing N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * Sing N * N := by
  by_contra hno
  push Not at hno
  have hsub : evenMult r X ⊆ B ∪ (evenMult r X).filter (fun N =>
      ¬ (δ * Sing N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * Sing N * N)) := by
    intro N hN
    by_cases hB : N ∈ B
    · exact mem_union_left _ hB
    · apply mem_union_right
      rw [mem_filter]
      refine ⟨hN, fun h => ?_⟩
      exact absurd h.2 (not_le.mpr (hno N hN hB h.1))
  have h1 := card_le_card hsub
  have h2 := card_union_le B ((evenMult r X).filter (fun N =>
      ¬ (δ * Sing N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * Sing N * N)))
  have h3 : ((evenMult r X).card : ℝ) ≤ B.card + ((evenMult r X).filter (fun N =>
      ¬ (δ * Sing N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * Sing N * N))).card := by
    exact_mod_cast h1.trans h2
  unfold HL84 at h84
  linarith

/-- (8.4) holds when there are at most `X^{3/5}` even multiples at all. -/
theorem HL84_of_card_le {r : ℕ} {δ X : ℝ} (h : ((evenMult r X).card : ℝ) ≤ X ^ (3 / 5 : ℝ)) :
    HL84 r δ X := by
  unfold HL84
  exact le_trans (by exact_mod_cast card_filter_le _ _) h

/-- Vacuity test: the hypothesis (8.4) can hold, here at `r = 1`, `X = 1`, any `δ`. -/
theorem vacuity_HL84 (δ : ℝ) : HL84 1 δ 1 := by
  apply HL84_of_card_le
  rw [Real.one_rpow]
  have hc : 1 ≤ ⌈(1 : ℝ) / 2⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; norm_num)
  have : (evenMult 1 1).card ≤ 1 := by
    unfold evenMult
    refine (card_filter_le _ _).trans ?_
    rw [Nat.card_Icc, Nat.floor_one]; omega
  exact_mod_cast this

/-- Theorem 8.2 from the page 32 consequence of Proposition 8.1. CONDITIONAL ON
`Prop81AtMultiples`. -/
theorem theorem82_of_prop81 (h81 : Prop81AtMultiples) : Theorem82 := by
  intro δ hδ hδ1
  obtain ⟨c, hc, hA⟩ := h81 δ hδ hδ1
  refine ⟨c, hc, fun A hA52 => ?_⟩
  obtain ⟨r0, hr0⟩ := hA A hA52
  refine ⟨max r0 1, fun r _ hr h84 => ?_⟩
  rintro ⟨χ, hprim, hreal, hzero⟩
  obtain ⟨B, hBcard, hBN⟩ := hr0 r (le_of_max_le_left hr) χ hprim hreal hzero
  obtain ⟨N, hN, hNB, hlo, hhi⟩ := exists_good_multiple B h84 hBcard
  obtain ⟨b, E, hb, hE, hrN⟩ := hBN N hN hNB
  have hNpos : (0 : ℝ) < N := by
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast le_of_max_le_right hr
    have hX : (1 : ℝ) ≤ (r : ℝ) ^ A := Real.one_le_rpow hr1 (by linarith)
    unfold evenMult at hN
    rw [mem_filter, mem_Icc] at hN
    have hc : 0 < ⌈(r : ℝ) ^ A / 2⌉₊ := Nat.ceil_pos.mpr (by linarith)
    exact_mod_cast lt_of_lt_of_le hc hN.1.1
  have hM : 0 < Sing N * N := mul_pos (Sing_pos N) hNpos
  have hs : (χ (-1)).re = 1 ∨ (χ (-1)).re = -1 := by
    rcases sq_eq_one_of_dirichlet_neg_one χ with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  refine dichotomy hM hs hb hE hrN ⟨?_, ?_⟩
  · linarith [show δ * Sing N * N = δ * (Sing N * N) by ring]
  · linarith [show (2 - δ) * Sing N * N = (2 - δ) * (Sing N * N) by ring]

end

end LeanLab.ExceptionalSet.BG2026

