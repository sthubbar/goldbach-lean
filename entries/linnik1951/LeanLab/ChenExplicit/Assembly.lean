module

public import LeanLab.ChenExplicit.Bridge
public import LeanLab.ChenExplicit.Reductions

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Assembly of BJS Theorem 3 (arXiv 2207.09452, P0009, v6) from its sieve estimates, via the proved
Lemma 37 of Bridge.lean. The analytic inputs, Theorems 44, 50, 51 of the paper, are HYPOTHESES,
stated as `def ... : Prop` with symbolic constants `cA N, cQ N, cB N`, because their explicit
constants depend on a dozen auxiliary functions of Sections 4-6 (x₁, c₂, c₃, c₄, ε₁, ε₂, a(X₂),
l(X₂), m(X₃), ...) and on the case split `k₁ < K_δ(x₁(N))` on the exceptional modulus.
PROVED here: an explicit lower bound `U_N ⩾ 1/1000`, via `twinC ⩾ e^{-6}`, and
`BJS3_of_sieveBounds`: the three sieve bounds plus the Section 9 numerical margin imply `BJS3`.
-/

@[expose] public section

open Finset Real
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

noncomputable section
namespace LeanLab.ChenExplicit

lemma tsum_inv_sub_one_sq_le :
    ∑' n : ℕ, 1 / ((n : ℝ) - 1) ^ 2 ≤ 3 := by
  have hs := summable_inv_sub_one_sq
  rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  have hz := hasSum_zeta_two
  have h1 : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hz
    simpa using this
  have h2 : ∑' n : ℕ, (1 : ℝ) / (((n + 1 + 1 : ℕ) : ℝ) - 1) ^ 2 = π ^ 2 / 6 := by
    rw [← h1.tsum_eq]; congr 1; ext n; push_cast; ring_nf
  simp only [Nat.cast_zero, Nat.cast_one, zero_add] at h2 ⊢
  rw [h2]
  have := pi_lt_d2
  have := pi_pos
  norm_num
  nlinarith

/-- **Explicit lower bound for the twin prime constant**, `twinC ⩾ e^{-6}` (true value 0.66016...).
Proof: `log(1 − x) ⩾ −2x` for `x ⩽ 1/2` and `Σ_p 1/(p−1)² ⩽ Σ_n 1/(n−1)² = 1 + π²/6 ⩽ 3`. -/
theorem twinC_ge : exp (-6) ≤ twinC := by
  set f : {p : ℕ // p.Prime ∧ 2 < p} → ℝ := fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2 with hf
  set x : {p : ℕ // p.Prime ∧ 2 < p} → ℝ := fun p => 1 / ((p : ℝ) - 1) ^ 2 with hx
  have hge : ∀ p : {p : ℕ // p.Prime ∧ 2 < p}, (2 : ℝ) ≤ (p : ℝ) - 1 := by
    intro p
    have : (3 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.2
    linarith
  have hx4 : ∀ p, x p ≤ 1 / 4 := by
    intro p
    have h2 := hge p
    simp only [hx]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hx0 : ∀ p, 0 ≤ x p := fun p => by simp only [hx]; positivity
  have hpos : ∀ p, 0 < f p := by
    intro p; have := hx4 p; simp only [hf]; simp only [hx] at this; linarith
  have hs : Summable x := summable_inv_sub_one_sq.subtype _
  have hlog : Summable (fun p => Real.log (f p)) := by
    have := Real.summable_log_one_add_of_summable hs.neg
    refine this.congr fun p => ?_
    simp only [hf, hx]; ring_nf
  have hpt : ∀ p, -2 * x p ≤ Real.log (f p) := by
    intro p
    have h1 := Real.one_sub_inv_le_log_of_pos (hpos p)
    have hxp := hx4 p
    have hx0p := hx0 p
    have hfp : f p = 1 - x p := rfl
    rw [hfp] at h1 ⊢
    have h3 : (1 - x p)⁻¹ ≤ 1 + 2 * x p := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]; nlinarith
    linarith
  have hsum1 : ∑' p, -2 * x p ≤ ∑' p, Real.log (f p) :=
    Summable.tsum_le_tsum hpt (hs.mul_left (-2)) hlog
  rw [tsum_mul_left] at hsum1
  have hsub : ∑' p, x p ≤ ∑' n : ℕ, 1 / ((n : ℝ) - 1) ^ 2 :=
    Summable.tsum_subtype_le (fun n : ℕ => 1 / ((n : ℝ) - 1) ^ 2) {p | p.Prime ∧ 2 < p}
      (fun n => by positivity) summable_inv_sub_one_sq
  have h3 := tsum_inv_sub_one_sq_le
  have hT : twinC = exp (∑' p, Real.log (f p)) := by
    rw [Real.rexp_tsum_eq_tprod hpos hlog]; rfl
  rw [hT]
  exact exp_le_exp.mpr (by linarith)

/-- **`U_N ⩾ 1/1000`** for every `N`, from `γ < 2/3` and `twinC ⩾ e^{-6}`. -/
theorem U_ge (N : ℕ) : (1 : ℝ) / 1000 ≤ U N := by
  unfold U
  have h1 := one_le_oddFactor N
  have h2 := twinC_ge
  have hγ := eulerMascheroniConstant_lt_two_thirds
  have h3 : exp (-1) ≤ exp (-eulerMascheroniConstant) := exp_le_exp.mpr (by linarith)
  have h7 : exp 7 ≤ 2000 := by
    have := exp_one_lt_d9
    have e : exp 7 = exp 1 ^ 7 := by rw [exp_one_pow]; norm_num
    rw [e]
    calc exp 1 ^ 7 ≤ (2.7182818286 : ℝ) ^ 7 := pow_le_pow_left₀ (exp_pos 1).le this.le 7
      _ ≤ 2000 := by norm_num
  have h4 : (1 : ℝ) / 1000 ≤ 2 * exp (-1) * exp (-6) := by
    rw [mul_assoc, ← exp_add]
    have : exp (-1 + -6) = (exp 7)⁻¹ := by rw [← exp_neg]; norm_num
    rw [this]
    have := exp_pos 7
    rw [show 2 * (exp 7)⁻¹ = 2 / exp 7 by ring, le_div_iff₀ this]
    linarith
  calc (1 : ℝ) / 1000 ≤ 2 * exp (-1) * exp (-6) * 1 := by linarith
    _ ≤ _ := by
      apply mul_le_mul _ h1 zero_le_one (by have := twinC_pos; positivity)
      apply mul_le_mul _ h2 (by positivity) (by positivity)
      linarith

lemma exp_32_7_gt : (6 * 10 ^ 13 : ℝ) ≤ exp (327 / 10) := by
  have := exp_one_gt_d9
  have e : exp 32 = exp 1 ^ 32 := by rw [exp_one_pow]; norm_num
  have h1 : exp 32 ≤ exp (327 / 10) := exp_le_exp.mpr (by norm_num)
  have h2 : (2.7182818283 : ℝ) ^ 32 ≤ exp 1 ^ 32 := pow_le_pow_left₀ (by norm_num) this.le 32
  have h3 : (6 * 10 ^ 13 : ℝ) ≤ (2.7182818283 : ℝ) ^ 32 := by norm_num
  linarith

lemma big_exp (L : ℝ) (hL : exp (327 / 10) ≤ L) : 3 * 10 ^ 15 * L ^ 2 ≤ exp (L / 8) := by
  have hL6 := exp_32_7_gt
  have hL0 : 0 ≤ L / 8 := by linarith
  have h := Real.pow_div_factorial_le_exp (L / 8) hL0 4
  have hf : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at h
  have hL2 : (36 * 10 ^ 26 : ℝ) ≤ L ^ 2 := by nlinarith
  have : 3 * 10 ^ 15 * L ^ 2 ≤ (L / 8) ^ 4 / 24 := by
    have : (L / 8) ^ 4 / 24 = L ^ 2 * L ^ 2 / 98304 := by ring
    rw [this, le_div_iff₀ (by norm_num)]
    nlinarith [sq_nonneg L]
  linarith

/-- `z = N^{1/8}`, equation (104). -/
abbrev zN (N : ℕ) : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8)

/-- `y = N^{1/3}`, equation (104). -/
abbrev yN (N : ℕ) : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3)

/-- The main term `U_N N / log² N` of Theorem 3. -/
abbrev mainTerm (N : ℕ) : ℝ := U N * N / Real.log N ^ 2

/-- **BJS Theorem 44** (lower bound for `S(A, P(z))`, Section 6), symbolic constant `cA N`:
for even `N > exp exp 32.7`, `S(A, P(z)) > cA(N) · U_N N / log² N`. In the paper,
`cA(N) = 8 · (|A| log N / N) · [bracket of case (a) or (b)]`, with `|A|` replaced by `N / log N`
once the bracket is positive (Section 9, using (125)). HYPOTHESIS. -/
def Thm44Bound (cA : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp (327 / 10)) < N → cA N * mainTerm N < SA N (zN N)

/-- **BJS Theorem 50** (upper bound for `Σ_{z⩽q<y, q∤N} S(A_q, P(z))`, Section 7), symbolic
constant `cQ N`: the sum is `< cQ(N) · U_N N / log² N`; in the paper
`cQ(N) = 2 · (8.0004 (1 + 32.02/log² N)(l₁ + l₂) + l/(2e^γ ∏(1 − 1/(p−1)²) log N))`,
starred variants in case (b). HYPOTHESIS. -/
def Thm50Bound (cQ : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp (327 / 10)) < N → (sumSAq N (zN N) (yN N) : ℝ) < cQ N * mainTerm N

/-- **BJS Theorem 51** (upper bound for `S(B, P(y))`, Section 8), symbolic constant `cB N`.
HYPOTHESIS. -/
def Thm51Bound (cB : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp (327 / 10)) < N → (SB N (zN N) (yN N) : ℝ) < cB N * mainTerm N

/-- **Section 9 numerics**, symbolic form: with `X₂ = exp exp 32.7`, `X₃ = exp exp 30.62`,
`δ = 1.478`, `α₁ = α₂ = α₃ = 10⁻⁵`, `ε₀ = 10⁻⁴`, the paper finds the combination
`cA − cQ/2 − cB/2` is at least `1/10` when `k₁ < K_δ(x₁(N))` and at least `2·10⁻⁴` otherwise.
We ask for a margin of `10⁻¹²` above `2·10⁻⁴`, which absorbs the terms `2N^{7/8} + N^{1/3}` of
Lemma 37. HYPOTHESIS; this is the numeric inequality that remains. -/
def Section9Margin (cA cQ cB : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp (327 / 10)) < N →
    2 / 10000 + 1 / 10 ^ 12 ≤ cA N - cQ N / 2 - cB N / 2

/-- **Theorem 3 from its sieve inputs.** BJS Theorems 44, 50, 51 with constants `cA, cQ, cB`
satisfying the Section 9 margin imply `BJS3`. The combinatorial step is the proved `lemma37`
(here through `chen_inequality`); the error `2N^{7/8} + N^{1/3}` is absorbed using `U_N ⩾ 1/1000`
and `log N > e^{32.7}`. -/
theorem BJS3_of_sieveBounds (cA cQ cB : ℕ → ℝ) (hA : Thm44Bound cA) (hQ : Thm50Bound cQ)
    (hB : Thm51Bound cB) (hm : Section9Margin cA cQ cB) : BJS3 := by
  intro N hEven hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  set L := Real.log N with hLdef
  have hL : exp (327 / 10) < L := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have hL6 := exp_32_7_gt
  have hL0 : 0 < L := by linarith
  have hNe : (N : ℝ) = exp L := (exp_log hpos).symm
  have hz : zN N = exp (L / 8) := by
    simp only [zN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hy : yN N = exp (L / 3) := by
    simp only [yN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hz2 : 2 ≤ zN N := by
    rw [hz]; have := add_one_le_exp (L / 8); linarith
  have hy0 : 0 < yN N := by rw [hy]; exact exp_pos _
  have hy3 : (N : ℝ) ≤ yN N ^ 3 := by
    rw [hy, ← exp_nat_mul, hNe]; apply exp_le_exp.mpr; push_cast; linarith
  have hchen := chen_inequality N (zN N) (yN N) hz2 hy0 hy3
  have h1 := hA N hEven hN
  have h2 := hQ N hEven hN
  have h3 := hB N hEven hN
  have hmN := hm N hEven hN
  have hU := U_ge N
  have hL2 : 0 < L ^ 2 := by positivity
  have hM0 : 0 < mainTerm N := by
    have := U_pos N
    simp only [mainTerm]; positivity
  -- the error terms of Lemma 37
  have hE : 2 * (N : ℝ) / zN N + yN N ≤ 1 / 10 ^ 12 * mainTerm N := by
    have hbig := big_exp L hL.le
    have e1 : 2 * (N : ℝ) / zN N = 2 * exp (7 * L / 8) := by
      rw [hz, hNe, mul_div_assoc, ← exp_sub]; ring_nf
    have e2 : yN N ≤ exp (7 * L / 8) := by rw [hy]; exact exp_le_exp.mpr (by linarith)
    have e3 : exp L = exp (7 * L / 8) * exp (L / 8) := by rw [← exp_add]; ring_nf
    have hM : 1 / 1000 * exp L / L ^ 2 ≤ mainTerm N := by
      simp only [mainTerm]; rw [← hLdef, ← hNe]
      apply div_le_div_of_nonneg_right _ hL2.le
      rw [hNe]; exact mul_le_mul_of_nonneg_right hU (exp_pos _).le
    have h7 := exp_pos (7 * L / 8)
    have : 3 * exp (7 * L / 8) ≤ 1 / 10 ^ 12 * (1 / 1000 * exp L / L ^ 2) := by
      rw [e3, show 1 / 10 ^ 12 * (1 / 1000 * (exp (7 * L / 8) * exp (L / 8)) / L ^ 2) =
        exp (7 * L / 8) * exp (L / 8) / (10 ^ 15 * L ^ 2) by ring, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hbig h7.le]
    linarith
  have hfin := mul_le_mul_of_nonneg_right hmN hM0.le
  have hgoal : (2 / 10000 : ℝ) * U N * N / Real.log N ^ 2 = 2 / 10000 * mainTerm N := by
    simp only [mainTerm]; ring
  rw [hgoal]
  nlinarith

end LeanLab.ChenExplicit
