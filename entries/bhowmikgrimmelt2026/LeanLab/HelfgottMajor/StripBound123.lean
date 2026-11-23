module

public import Mathlib

/-!
Route burst 2026-11-12c, step gaussian_explicit_estimate p4, leaf Residue123.strip_bound_4_19.
P0014 Helfgott, Major arcs for Goldbach's problem, page 36, displays 4.18 and 4.19: by partial
summation, abs L(s, χ) is at most 2√3 √M(q) on the closed disc of radius 5/8 about 9/8, where
M(q) is the largest absolute value of a partial sum of χ.

What this file does, all PROVED, Mathlib only.
1. The partial summation formula of display 4.18 on the half plane Re s > 0, for a nontrivial
   Dirichlet character: `LFunction_eq_tsum` and `LFunction_eq_head_add_tail`. Mathlib knows the
   Dirichlet series only for Re s > 1; the formula is carried to Re s > 0 by the identity
   principle, both sides being analytic there.
2. The bound of display 4.18 in its corrected form: `norm_LFunction_le`.
3. Display 4.19 on the disc: `strip_bound_of_le` and `strip_bound_4_19`.

QUESTION, recorded for P0014 page 36. Display 4.18 as printed does not follow term by term.
First, the printed difference n^(-s) - (n+1)^(-s+1) should read n^(-s) - (n+1)^(-s). Second,
the printed bound M(q) N^(-σ) for the tail uses abs(n^(-s) - (n+1)^(-s)) at most
n^(-σ) - (n+1)^(-σ), which is false for non real s; the true bound carries the factor
abs s / σ, which reaches 9/√56 = 1.2027 on the disc. Third, N = M(q)/3 need not be an integer,
and the range 1/2 ≤ σ < 1 does not cover the disc, where σ goes up to 7/4.
The final display 4.19 is nevertheless TRUE as printed, with the same constant 2√3. The proof
here keeps the paper's partial summation and repairs the three points: for N + 1 ≥ 13 the factor
(abs s / σ) (N+1)^(-(σ - 1/2)) is at most 1 on the disc, since abs s ^ 2 ≤ 9σ/4 - 7/8 there;
for M(q) ≥ 64 the integer N = ceil(M(q)/3) works because the head sum is at most 2√N - 1, the
-1 absorbing the rounding; and for M(q) < 64 the fixed choices N = 0, 5, 12 work.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.StripBound123
open Filter Topology

/-! ## The basic estimate for a difference of two powers -/

/-- PROVED. For 0 < a ≤ b and Re s = σ > 0, a^(-s) - b^(-s) = s ∫_a^b x^(-s-1) dx, so its norm
is at most abs s times the integral of x^(-σ-1). This is the step behind the tail of P0014
display 4.18. -/
lemma norm_cpow_sub_cpow_le_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ}
    (hs : 0 < s.re) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ * ∫ x : ℝ in a..b, x ^ (-s.re - 1) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]; intro h; exact absurd h.1 (not_le.mpr ha)
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hne : -s - 1 ≠ -1 := by
    intro h; apply hs0; have := congrArg (fun z => -(z + 1)) h; simpa using this
  have hI : ∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1) = ((b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)) / (-s) := by
    rw [integral_cpow (Or.inr ⟨hne, h0⟩)]; simp
  have e : (a : ℂ) ^ (-s) - (b : ℂ) ^ (-s) = s * ∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1) := by
    rw [hI]; field_simp; ring
  rw [e, norm_mul]
  have hn : ‖∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1)‖ ≤ ∫ x : ℝ in a..b, x ^ (-s.re - 1) := by
    calc ‖∫ x : ℝ in a..b, (x : ℂ) ^ (-s - 1)‖
        ≤ ∫ x in a..b, ‖(x : ℂ) ^ (-s - 1)‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ x in a..b, x ^ (-s.re - 1) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hab] at hx
        have hx0 : 0 < x := ha.trans_le hx.1
        simp [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  gcongr

/-- PROVED. The sharp form: the norm of a^(-s) - b^(-s) is at most
(abs s / σ)(a^(-σ) - b^(-σ)). The factor abs s / σ is missing in the printed display 4.18. -/
lemma norm_cpow_sub_cpow_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ} (hs : 0 < s.re) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ / s.re * (a ^ (-s.re) - b ^ (-s.re)) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]; intro h; exact absurd h.1 (not_le.mpr ha)
  have hR : ∫ x : ℝ in a..b, x ^ (-s.re - 1) = (b ^ (-s.re) - a ^ (-s.re)) / (-s.re) := by
    rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]; simp
  have h := norm_cpow_sub_cpow_le_integral ha hab hs
  rw [hR] at h
  have e : ‖s‖ * ((b ^ (-s.re) - a ^ (-s.re)) / (-s.re)) =
      ‖s‖ / s.re * (a ^ (-s.re) - b ^ (-s.re)) := by
    field_simp; ring
  rw [e] at h; exact h

/-- PROVED. The crude form, used only for locally uniform convergence: the norm of
a^(-s) - b^(-s) is at most abs s (b - a) a^(-σ-1). -/
lemma norm_cpow_sub_cpow_le_crude {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ} (hs : 0 < s.re) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ * ((b - a) * a ^ (-s.re - 1)) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]; intro h; exact absurd h.1 (not_le.mpr ha)
  have h := norm_cpow_sub_cpow_le_integral ha hab hs
  refine h.trans ?_
  gcongr
  have hmono : ∫ x : ℝ in a..b, x ^ (-s.re - 1) ≤ ∫ _x : ℝ in a..b, a ^ (-s.re - 1) := by
    apply intervalIntegral.integral_mono_on hab
      (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)) intervalIntegrable_const
    intro x hx
    exact Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)
  simpa using hmono

/-! ## The tail of display 4.18 -/

/-- PROVED. Partial sums of the norms of the tail of P0014 display 4.18 from n = N + 1 on:
they telescope, and are at most M (abs s / σ)(N + 1)^(-σ) when the partial sums A(n) are
bounded by M. -/
lemma tail_sum_range_le {A : ℕ → ℂ} {M : ℝ} (hA : ∀ n, ‖A n‖ ≤ M) {s : ℂ} (hs : 0 < s.re)
    (N K : ℕ) :
    ∑ n ∈ Finset.range K, ‖A (n + N + 1) *
        (((n + N + 1 : ℕ) : ℂ) ^ (-s) - ((n + N + 2 : ℕ) : ℂ) ^ (-s))‖ ≤
      M * (‖s‖ / s.re) * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hA 0)
  have hg : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hterm : ∀ n : ℕ, ‖A (n + N + 1) *
        (((n + N + 1 : ℕ) : ℂ) ^ (-s) - ((n + N + 2 : ℕ) : ℂ) ^ (-s))‖ ≤
      M * (‖s‖ / s.re) * (((n + N + 1 : ℕ) : ℝ) ^ (-s.re) - ((n + 1 + N + 1 : ℕ) : ℝ) ^ (-s.re)) := by
    intro n
    have hk := norm_cpow_sub_cpow_le (a := ((n + N + 1 : ℕ) : ℝ)) (b := ((n + 1 + N + 1 : ℕ) : ℝ))
      (by positivity) (by push_cast; linarith) hs
    rw [Complex.ofReal_natCast, Complex.ofReal_natCast] at hk
    rw [norm_mul, show n + N + 2 = n + 1 + N + 1 by ring, mul_assoc]
    exact mul_le_mul (hA _) hk (norm_nonneg _) hM0
  calc _ ≤ ∑ n ∈ Finset.range K, M * (‖s‖ / s.re) *
        (((n + N + 1 : ℕ) : ℝ) ^ (-s.re) - ((n + 1 + N + 1 : ℕ) : ℝ) ^ (-s.re)) :=
        Finset.sum_le_sum (fun n _ => hterm n)
    _ = M * (‖s‖ / s.re) *
        (((0 + N + 1 : ℕ) : ℝ) ^ (-s.re) - ((K + N + 1 : ℕ) : ℝ) ^ (-s.re)) := by
        rw [← Finset.mul_sum,
          Finset.sum_range_sub' (fun n : ℕ => ((n + N + 1 : ℕ) : ℝ) ^ (-s.re))]
    _ ≤ M * (‖s‖ / s.re) * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := by
        rw [zero_add]
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM0 hg)
        have : 0 ≤ ((K + N + 1 : ℕ) : ℝ) ^ (-s.re) := by positivity
        linarith

/-- PROVED. The tail series of display 4.18 converges absolutely for Re s > 0. -/
lemma tail_summable {A : ℕ → ℂ} {M : ℝ} (hA : ∀ n, ‖A n‖ ≤ M) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Summable (fun n : ℕ => ‖A (n + N + 1) *
        (((n + N + 1 : ℕ) : ℂ) ^ (-s) - ((n + N + 2 : ℕ) : ℂ) ^ (-s))‖) :=
  summable_of_sum_range_le (fun _ => norm_nonneg _) (tail_sum_range_le hA hs N)

/-- PROVED. The tail of display 4.18 from n = N + 1 on has norm at most
M (abs s / σ)(N + 1)^(-σ). The paper prints M N^(-σ); see the QUESTION in the file header. -/
lemma norm_tail_le {A : ℕ → ℂ} {M : ℝ} (hA : ∀ n, ‖A n‖ ≤ M) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∑' n : ℕ, A (n + N + 1) *
        (((n + N + 1 : ℕ) : ℂ) ^ (-s) - ((n + N + 2 : ℕ) : ℂ) ^ (-s))‖ ≤
      M * (‖s‖ / s.re) * ((N + 1 : ℕ) : ℝ) ^ (-s.re) :=
  (norm_tsum_le_tsum_norm (tail_summable hA hs N)).trans
    (Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) (tail_sum_range_le hA hs N))

/-! ## Summation by parts, finite form -/

/-- PROVED. Finite summation by parts, the algebra of P0014 display 4.18: with A(n) the partial
sums of c, the sum of A(n)(n^(-s) - (n+1)^(-s)) for n from 1 to N equals the sum of c(n) n^(-s)
for n from 1 to N minus A(N)(N+1)^(-s). -/
lemma abel_finite (A c : ℕ → ℂ) (h0 : A 0 = 0) (hstep : ∀ n, A (n + 1) = A n + c (n + 1))
    (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, A (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) =
      ∑ n ∈ Finset.range N, c (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-s) -
        A N * ((N + 1 : ℕ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hstep N]
    ring

/-! ## The partial summation formula for L(s, χ) on Re s > 0 -/

section character
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

omit [NeZero q] in
/-- PROVED. The partial sums of χ satisfy the recursion used in `abel_finite`. -/
lemma partialSum_succ (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q) =
      ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) + χ ((n + 1 : ℕ) : ZMod q) :=
  Finset.sum_Icc_succ_top (by omega) _

omit [NeZero q] in
/-- PROVED. The trivial bound: the partial sum of χ up to n has norm at most n. -/
lemma norm_partialSum_le_self (n : ℕ) : ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤ n := by
  calc _ ≤ ∑ m ∈ Finset.Icc 1 n, ‖χ (m : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 n, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
    _ = n := by simp

/-- PROVED. The sum of a function on ZMod q over q consecutive integers is the full sum. Same
statement as Residue123.sum_range_shift, repeated here to keep this file on Mathlib only. -/
lemma sum_range_shift (f : ZMod q → ℂ) (c : ℕ) :
    ∑ m ∈ Finset.range q, f ((c + m : ℕ) : ZMod q) = ∑ a, f a := by
  apply Finset.sum_nbij' (fun m => ((c + m : ℕ) : ZMod q)) (fun a => (a - (c : ZMod q)).val)
  · intro m _; simp
  · intro a _; simpa using ZMod.val_lt (a - (c : ZMod q))
  · intro m hm
    have hm' : m < q := Finset.mem_range.mp hm
    simp only [Nat.cast_add, add_sub_cancel_left]
    exact ZMod.val_cast_of_lt hm'
  · intro a _
    simp only [Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id]
    ring
  · intro m _; rfl

/-- PROVED. Page 36: the sum of χ(n) over any interval of length q is 0 for χ nontrivial, so
the partial sums have period q. -/
lemma partialSum_add_period (hχ : χ ≠ 1) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 (n + q), χ (m : ZMod q) = ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) := by
  have e : ∀ k : ℕ, ∑ m ∈ Finset.Icc 1 k, χ (m : ZMod q) =
      ∑ j ∈ Finset.range k, χ ((1 + j : ℕ) : ZMod q) := by
    intro k
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp
  rw [e, e, Finset.sum_range_add]
  have h := sum_range_shift (fun a => χ a) (1 + n)
  have h2 : ∑ x ∈ Finset.range q, χ ((1 + (n + x) : ℕ) : ZMod q) =
      ∑ m ∈ Finset.range q, χ ((1 + n + m : ℕ) : ZMod q) := by
    apply Finset.sum_congr rfl; intro x _; congr 2; ring
  rw [h2, h, MulChar.sum_eq_zero_of_ne_one hχ, add_zero]

/-- PROVED. The partial sums of a nontrivial character are bounded, here by q. -/
lemma norm_partialSum_le_modulus (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤ q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < q
    · exact (norm_partialSum_le_self χ n).trans (by exact_mod_cast hn.le)
    · have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      have e : n = (n - q) + q := by omega
      rw [e, partialSum_add_period χ hχ]
      exact ih (n - q) (by omega)

/-- PROVED. M(q) dominates every partial sum: the supremum in the definition of M(q) is over a
bounded set. -/
lemma norm_partialSum_le_iSup (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      ⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ :=
  le_ciSup (f := fun n : ℕ => ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖)
    ⟨q, by rintro _ ⟨k, rfl⟩; exact norm_partialSum_le_modulus χ hχ k⟩ n

/-- PROVED. P0014 display 4.18 with N = 0, for Re s > 1, where L(s, χ) is its Dirichlet series:
L(s, χ) is the sum over n ≥ 1 of (the partial sum of χ up to n) times (n^(-s) - (n+1)^(-s)). -/
lemma LFunction_eq_tsum_of_one_lt (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s =
      ∑' n : ℕ, (∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)) *
        (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) := by
  have hs0 : 0 < s.re := by linarith
  set A : ℕ → ℂ := fun n => ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) with hA
  have hAb : ∀ n, ‖A n‖ ≤ q := norm_partialSum_le_modulus χ hχ
  -- the tail series converges
  have hsum : Summable (fun n : ℕ => A (n + 1) *
      (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))) :=
    Summable.of_norm (by simpa using tail_summable hAb hs0 0)
  have h1 := hsum.hasSum.tendsto_sum_nat
  -- the boundary term tends to zero
  have h2 : Tendsto (fun K : ℕ => A K * ((K + 1 : ℕ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun K : ℕ => (q : ℝ) * ((K + 1 : ℕ) : ℝ) ^ (-s.re))
    · intro K
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      simp only [Complex.neg_re]
      exact mul_le_mul_of_nonneg_right (hAb K) (by positivity)
    · have h3 : Tendsto (fun K : ℕ => ((K + 1 : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
      have h4 := (tendsto_rpow_neg_atTop hs0).comp h3
      simpa using h4.const_mul (q : ℝ)
  -- the Dirichlet series
  have hL := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs).hasSum.tendsto_sum_nat
  have hL' := hL.comp (tendsto_add_atTop_nat 1)
  have hEq : ∀ K : ℕ, ∑ n ∈ Finset.range (K + 1), LSeries.term (fun n : ℕ => χ (n : ZMod q)) s n =
      ∑ n ∈ Finset.range K, A (n + 1) *
        (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) +
      A K * ((K + 1 : ℕ) : ℂ) ^ (-s) := by
    intro K
    rw [abel_finite A (fun n => χ (n : ZMod q)) (by simp [hA]) (fun n => partialSum_succ χ n) s K,
      Finset.sum_range_succ']
    have : LSeries.term (fun n : ℕ => χ (n : ZMod q)) s 0 = 0 := by simp
    rw [this, add_zero, sub_add_cancel]
    apply Finset.sum_congr rfl
    intro n _
    rw [LSeries.term_of_ne_zero (by omega), Complex.cpow_neg, div_eq_mul_inv]
  have hlim : Tendsto (fun K : ℕ => ∑ n ∈ Finset.range (K + 1),
      LSeries.term (fun n : ℕ => χ (n : ZMod q)) s n) atTop
      (𝓝 (∑' n : ℕ, A (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)))) := by
    have := h1.add h2
    rw [add_zero] at this
    exact this.congr (fun K => (hEq K).symm)
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact tendsto_nhds_unique hL' hlim

/-- PROVED. P0014 display 4.18 with N = 0, on the whole half plane Re s > 0. Both sides are
analytic on Re s > 0 and agree for Re s > 1, so the identity principle applies. -/
theorem LFunction_eq_tsum (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s =
      ∑' n : ℕ, (∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)) *
        (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) := by
  set A : ℕ → ℂ := fun n => ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) with hA
  have hAb : ∀ n, ‖A n‖ ≤ q := norm_partialSum_le_modulus χ hχ
  set δ : ℝ := s.re / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set R : ℝ := ‖s‖ + 3 with hR
  set U : Set ℂ := {w : ℂ | δ < w.re} ∩ Metric.ball 0 R with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt δ).inter (convex_ball 0 R)).isPreconnected
  have hsU : s ∈ U := by
    refine ⟨by simp only [Set.mem_ofPred_eq, hδ]; linarith, ?_⟩
    simp only [Metric.mem_ball, dist_zero_right, hR]; linarith
  have hzU : s + 2 ∈ U := by
    refine ⟨by simp only [Set.mem_ofPred_eq, hδ, Complex.add_re, Complex.re_ofNat]; linarith, ?_⟩
    simp only [Metric.mem_ball, dist_zero_right, hR]
    calc ‖s + 2‖ ≤ ‖s‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ < ‖s‖ + 3 := by norm_num
  -- the series is analytic on U
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, A (n + 1) *
      (((n + 1 : ℕ) : ℂ) ^ (-w) - ((n + 2 : ℕ) : ℂ) ^ (-w))) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ => (q : ℝ) * (R * ((n + 1 : ℕ) : ℝ) ^ (-δ - 1)))
    · have h := (Real.summable_nat_rpow (p := -δ - 1)).mpr (by linarith)
      exact (((summable_nat_add_iff 1).mpr h).mul_left R).mul_left (q : ℝ)
    · intro n
      apply Differentiable.differentiableOn
      apply Differentiable.const_mul
      apply Differentiable.sub
      · exact differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast (by omega : n + 1 ≠ 0)))
      · exact differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast (by omega : n + 2 ≠ 0)))
    · exact hUo
    · intro n w hw
      have hw1 : δ < w.re := hw.1
      have hw2 : ‖w‖ < R := by simpa using hw.2
      have hk := norm_cpow_sub_cpow_le_crude (a := ((n + 1 : ℕ) : ℝ)) (b := ((n + 2 : ℕ) : ℝ))
        (by positivity) (by push_cast; linarith) (hδ0.trans hw1)
      rw [Complex.ofReal_natCast, Complex.ofReal_natCast] at hk
      rw [norm_mul]
      have hba : ((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) = 1 := by push_cast; ring
      rw [hba, one_mul] at hk
      have hpow : ((n + 1 : ℕ) : ℝ) ^ (-w.re - 1) ≤ ((n + 1 : ℕ) : ℝ) ^ (-δ - 1) :=
        Real.rpow_le_rpow_of_exponent_le (by push_cast; linarith) (by linarith)
      have h5 : ‖w‖ * ((n + 1 : ℕ) : ℝ) ^ (-w.re - 1) ≤ R * ((n + 1 : ℕ) : ℝ) ^ (-δ - 1) :=
        mul_le_mul hw2.le hpow (by positivity) (by positivity)
      exact mul_le_mul (hAb _) (hk.trans h5) (norm_nonneg _) (by positivity)
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUo
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (s + 2)] (fun w : ℂ => ∑' n : ℕ, A (n + 1) *
      (((n + 1 : ℕ) : ℂ) ^ (-w) - ((n + 2 : ℕ) : ℂ) ^ (-w))) := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : s + 2 ∈ {w : ℂ | 1 < w.re} := by
      simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.re_ofNat]; linarith
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact LFunction_eq_tsum_of_one_lt χ hχ hw
  exact hf.eqOn_of_preconnected_of_eventuallyEq (hdiff.analyticOnNhd hUo) hUc hzU hev hsU

/-- PROVED. P0014 display 4.18, first three lines, for Re s > 0 and any N ≥ 0, in the corrected
form with n^(-s) - (n+1)^(-s): L(s, χ) is the sum of χ(n) n^(-s) for n ≤ N, minus the partial
sum up to N times (N+1)^(-s), plus the tail over n ≥ N + 1. -/
theorem LFunction_eq_head_add_tail (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    DirichletCharacter.LFunction χ s =
      ∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s) -
        (∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s) +
      ∑' n : ℕ, (∑ m ∈ Finset.Icc 1 (n + N + 1), χ (m : ZMod q)) *
        (((n + N + 1 : ℕ) : ℂ) ^ (-s) - ((n + N + 2 : ℕ) : ℂ) ^ (-s)) := by
  set A : ℕ → ℂ := fun n => ∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q) with hA
  have hAb : ∀ n, ‖A n‖ ≤ q := norm_partialSum_le_modulus χ hχ
  have hsum : Summable (fun n : ℕ => A (n + 1) *
      (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))) :=
    Summable.of_norm (by simpa using tail_summable hAb hs 0)
  rw [LFunction_eq_tsum χ hχ hs, ← hsum.sum_add_tsum_nat_add N,
    abel_finite A (fun n => χ (n : ZMod q)) (by simp [hA]) (fun n => partialSum_succ χ n) s N]

/-- PROVED. P0014 display 4.18, last line, in its corrected form, for Re s = σ > 0 and N ≥ 0:
abs L(s, χ) is at most the sum of n^(-σ) for n ≤ N, plus N (N+1)^(-σ), plus
M (abs s / σ)(N+1)^(-σ), where M bounds the partial sums of χ. -/
theorem norm_LFunction_le (hχ : χ ≠ 1) {M : ℝ}
    (hM : ∀ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤ M) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) ^ (-s.re) + N * ((N + 1 : ℕ) : ℝ) ^ (-s.re) +
        M * (‖s‖ / s.re) * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := by
  rw [LFunction_eq_head_add_tail χ hχ hs N]
  have h1 : ‖∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s)‖ ≤
      ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    simp only [Complex.neg_re]
    calc ‖χ ((n + 1 : ℕ) : ZMod q)‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re)
        ≤ 1 * ((n + 1 : ℕ) : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (by positivity)
      _ = _ := one_mul _
  have h2 : ‖(∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s)‖ ≤
      N * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    simp only [Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (norm_partialSum_le_self χ N) (by positivity)
  have h3 := norm_tail_le hM hs N
  calc _ ≤ ‖∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s) -
        (∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s)‖ +
      ‖∑' n : ℕ, (∑ m ∈ Finset.Icc 1 (n + N + 1), χ (m : ZMod q)) *
        (((n + N + 1 : ℕ) : ℂ) ^ (-s) - ((n + N + 2 : ℕ) : ℂ) ^ (-s))‖ := norm_add_le _ _
    _ ≤ _ := by
      have := norm_sub_le
        (∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s))
        ((∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s))
      linarith

end character

/-! ## The disc of radius 5/8 about 9/8 -/

/-- PROVED. On the closed disc of radius 5/8 about 9/8, P0014 page 36, the real part σ is at
least 1/2 and abs s ^ 2 is at most 9σ/4 - 7/8. -/
lemma disc_facts {s : ℂ} (hs : s ∈ Metric.closedBall (9 / 8 : ℂ) (5 / 8)) :
    1 / 2 ≤ s.re ∧ ‖s‖ ^ 2 ≤ 9 / 4 * s.re - 7 / 8 := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hs
  have h1 : ‖s - 9 / 8‖ ^ 2 ≤ (5 / 8) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
  rw [Complex.sq_norm, Complex.normSq_apply] at h1
  have h98 : ((9 : ℂ) / 8) = ((9 / 8 : ℝ) : ℂ) := by push_cast; ring
  have hre : (s - 9 / 8).re = s.re - 9 / 8 := by rw [h98, Complex.sub_re, Complex.ofReal_re]
  have him : (s - 9 / 8).im = s.im := by rw [h98, Complex.sub_im, Complex.ofReal_im, sub_zero]
  rw [hre, him] at h1
  constructor
  · nlinarith [mul_self_nonneg s.im]
  · rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith

/-- PROVED. On the disc, abs s / σ is at most 9/√56, here in the form abs s ≤ 1.2027 σ. This
is the factor missing in the printed display 4.18. -/
lemma norm_le_of_disc {s : ℂ} (hs : s ∈ Metric.closedBall (9 / 8 : ℂ) (5 / 8)) :
    ‖s‖ ≤ 1.2027 * s.re := by
  obtain ⟨h1, h2⟩ := disc_facts hs
  by_contra h
  push Not at h
  have h3 : (1.2027 * s.re) ^ 2 < ‖s‖ ^ 2 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
  nlinarith [sq_nonneg (9 * s.re - 7), sq_nonneg s.re]

lemma exp_five_halves_le : Real.exp (5 / 2) ≤ 13 := by
  have h1 : Real.exp (5 / 2) ^ 2 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h3 : Real.exp 1 ^ 5 < 169 :=
    lt_of_lt_of_le (pow_lt_pow_left₀ h2 (Real.exp_pos 1).le (by norm_num)) (by norm_num)
  nlinarith [Real.exp_pos (5 / 2 : ℝ)]

/-- PROVED. For x ≥ 13 and s on the disc, (abs s / σ) x^(-σ) is at most x^(-1/2): the decay of
x^(-(σ - 1/2)) pays for the factor abs s / σ. This repairs the tail term of display 4.18. -/
lemma factor_le_of_thirteen {s : ℂ} (hs : s ∈ Metric.closedBall (9 / 8 : ℂ) (5 / 8)) {x : ℝ}
    (hx : 13 ≤ x) : ‖s‖ / s.re * x ^ (-s.re) ≤ x ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨h1, h2⟩ := disc_facts hs
  have hσ : 0 < s.re := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : 5 / 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact exp_five_halves_le.trans hx
  have hpow : 1 + 5 * (s.re - 1 / 2) ≤ x ^ (2 * (s.re - 1 / 2)) := by
    rw [Real.rpow_def_of_pos hx0]
    have h := Real.add_one_le_exp (Real.log x * (2 * (s.re - 1 / 2)))
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (sub_nonneg.mpr h1)]
  have hxu : x ^ (2 * (s.re - 1 / 2)) = (x ^ (s.re - 1 / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have hxu0 : 0 < x ^ (s.re - 1 / 2) := Real.rpow_pos_of_pos hx0 _
  have hle : ‖s‖ ≤ s.re * x ^ (s.re - 1 / 2) := by
    by_contra h
    push Not at h
    have h5 : (s.re * x ^ (s.re - 1 / 2)) ^ 2 < ‖s‖ ^ 2 :=
      pow_lt_pow_left₀ h (by positivity) (by norm_num)
    have h3 : 9 / 4 * s.re - 7 / 8 ≤ s.re ^ 2 * (1 + 5 * (s.re - 1 / 2)) := by
      nlinarith [mul_nonneg (sq_nonneg (s.re - 1 / 2)) (show (0 : ℝ) ≤ 5 * s.re + 7 / 2 by linarith)]
    have h4 : s.re ^ 2 * (1 + 5 * (s.re - 1 / 2)) ≤ s.re ^ 2 * (x ^ (s.re - 1 / 2)) ^ 2 := by
      rw [← hxu]; exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    nlinarith
  have hsplit : x ^ (-s.re) = x ^ (-(1 / 2 : ℝ)) * (x ^ (s.re - 1 / 2))⁻¹ := by
    rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]; congr 1; ring
  rw [hsplit]
  have e : ‖s‖ / s.re * (x ^ (-(1 / 2 : ℝ)) * (x ^ (s.re - 1 / 2))⁻¹) =
      x ^ (-(1 / 2 : ℝ)) * (‖s‖ / (s.re * x ^ (s.re - 1 / 2))) := by
    field_simp
  rw [e]
  have h6 : ‖s‖ / (s.re * x ^ (s.re - 1 / 2)) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hle
  nlinarith [Real.rpow_pos_of_pos hx0 (-(1 / 2 : ℝ))]

/-! ## The head sum -/

lemma rpow_neg_le_inv_sqrt {σ x : ℝ} (hσ : 1 / 2 ≤ σ) (hx : 1 ≤ x) :
    x ^ (-σ) ≤ (Real.sqrt x)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-- PROVED. The sum of 1/√n for n from 1 to N is at most 2√N - 1, for N ≥ 1. The paper uses
N^(1 - 1/2)/(1 - 1/2) = 2√N; the extra -1 is what absorbs the rounding of N to an integer. -/
lemma sum_inv_sqrt_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range N, (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ ≤ 2 * Real.sqrt N - 1 := by
  induction N, hN using Nat.le_induction with
  | base => simp; norm_num
  | succ N hN ih =>
    rw [Finset.sum_range_succ]
    have ha : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hb : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have ha2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by positivity)
    have hb2 : Real.sqrt ((N + 1 : ℕ) : ℝ) ^ 2 = N + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have key : (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ ≤
        2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt N) := by
      rw [inv_eq_one_div, div_le_iff₀ hb]
      nlinarith [sq_nonneg (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt N)]
    linarith

lemma head_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ 2 * Real.sqrt N - 1 :=
  (Finset.sum_le_sum fun n _ => rpow_neg_le_inv_sqrt hσ
    (by push_cast; linarith [n.cast_nonneg (α := ℝ)])).trans (sum_inv_sqrt_le N hN)

lemma inv_sqrt_le {x y c : ℝ} (hy : 0 < y) (h : y ^ 2 ≤ x) (hc : 1 ≤ c * y) :
    (Real.sqrt x)⁻¹ ≤ c := by
  have h1 : y ≤ Real.sqrt x := Real.le_sqrt_of_sq_le h
  have h2 : (Real.sqrt x)⁻¹ ≤ y⁻¹ := inv_anti₀ hy h1
  have h3 : y⁻¹ ≤ c := by rw [inv_eq_one_div, div_le_iff₀ hy]; exact hc
  exact h2.trans h3

/-! ## Display 4.19 -/

section character
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- PROVED. Display 4.18 on the disc with a general N ≥ 1: if (abs s / σ)(N+1)^(-σ) is at most
k/√(N+1), then abs L(s, χ) is at most 2√N - 1 + (N + k M)/√(N+1). With k = 1 this is the
paper's N^(1-1/2)/(1-1/2) + N^(1-σ) + M N^(-σ), slightly sharpened. -/
theorem norm_LFunction_le_of_factor (hχ : χ ≠ 1) {M : ℝ}
    (hM : ∀ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤ M) {s : ℂ}
    (hs : s ∈ Metric.closedBall (9 / 8 : ℂ) (5 / 8)) (N : ℕ) (hN : 1 ≤ N) {k : ℝ}
    (hk : ‖s‖ / s.re * ((N + 1 : ℕ) : ℝ) ^ (-s.re) ≤ k * (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      2 * Real.sqrt N - 1 + (N + k * M) * (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ := by
  obtain ⟨h1, -⟩ := disc_facts hs
  have hσ : 0 < s.re := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h := norm_LFunction_le χ hχ hM hσ N
  have ha := head_le h1 N hN
  have hb : (N : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-s.re) ≤ N * (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ :=
    mul_le_mul_of_nonneg_left (rpow_neg_le_inv_sqrt h1 (by push_cast; linarith [N.cast_nonneg (α := ℝ)]))
      (Nat.cast_nonneg N)
  have hc : M * (‖s‖ / s.re) * ((N + 1 : ℕ) : ℝ) ^ (-s.re) ≤
      M * (k * (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hk hM0
  calc _ ≤ _ := h
    _ ≤ 2 * Real.sqrt N - 1 + N * (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ +
        M * (k * (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹) := by linarith
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- PROVED. P0014 display 4.19, page 36: for χ nontrivial mod q and M any bound for the norms
of the partial sums of χ, abs L(s, χ) is at most 2√3 √M on the closed disc of radius 5/8 about
9/8. The paper sets N = M/3; here N = 0 for M ≤ 8.29, N = 5 for M up to 20, N = 12 for M up to
64, and N = ceil(M/3) from there on. See the QUESTION in the file header. -/
theorem strip_bound_of_le (hχ : χ ≠ 1) {M : ℝ}
    (hM : ∀ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤ M) {s : ℂ}
    (hs : s ∈ Metric.closedBall (9 / 8 : ℂ) (5 / 8)) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 2 * Real.sqrt 3 * Real.sqrt M := by
  obtain ⟨h1, -⟩ := disc_facts hs
  have hσ : 0 < s.re := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hg : ‖s‖ / s.re ≤ 1.2027 := by
    rw [div_le_iff₀ hσ]; exact norm_le_of_disc hs
  have hg0 : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hσ.le
  set t := Real.sqrt M with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = M := Real.sq_sqrt hM0
  set r := Real.sqrt 3 with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr1 : 1.73205 ≤ r := Real.le_sqrt_of_sq_le (by norm_num)
  rcases le_total M 8.29 with hA | hA
  · -- N = 0
    have h := norm_LFunction_le χ hχ hM hσ 0
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_add,
      Nat.cast_one, Real.one_rpow, mul_one, add_zero] at h
    have h2 : M * (‖s‖ / s.re) ≤ M * 1.2027 := mul_le_mul_of_nonneg_left hg hM0
    have ht3 : t ≤ 2.88 := by nlinarith
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht3), mul_nonneg ht0 (sub_nonneg.mpr hr1)]
  rcases le_total M 20 with hB | hB
  · -- N = 5
    have hk : ‖s‖ / s.re * ((5 + 1 : ℕ) : ℝ) ^ (-s.re) ≤
        1.2027 * (Real.sqrt ((5 + 1 : ℕ) : ℝ))⁻¹ :=
      mul_le_mul hg (rpow_neg_le_inv_sqrt h1 (by norm_num)) (by positivity) (by norm_num)
    have h := norm_LFunction_le_of_factor χ hχ hM hs 5 (by norm_num) hk
    rw [show ((5 + 1 : ℕ) : ℝ) = 6 by norm_num, show ((5 : ℕ) : ℝ) = 5 by norm_num] at h
    have hX : (Real.sqrt 6)⁻¹ ≤ 0.40825 :=
      inv_sqrt_le (y := 2.44948) (by norm_num) (by norm_num) (by norm_num)
    have hX0 : 0 ≤ (Real.sqrt 6)⁻¹ := by positivity
    have h5 : Real.sqrt 5 ≤ 2.2361 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hlo : 2.879 ≤ t := by rw [ht]; exact Real.le_sqrt_of_sq_le (by linarith)
    have hhi : t ≤ 4.4722 := by rw [ht]; exact Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
    have hprod := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
    have h7 : (5 + 1.2027 * M) * (Real.sqrt 6)⁻¹ ≤ (5 + 1.2027 * M) * 0.40825 :=
      mul_le_mul_of_nonneg_left hX (by linarith)
    have h8 : 3.4641 * t ≤ 2 * r * t := by nlinarith
    nlinarith
  rcases le_total M 64 with hC | hC
  · -- N = 12
    have hk : ‖s‖ / s.re * ((12 + 1 : ℕ) : ℝ) ^ (-s.re) ≤
        1 * (Real.sqrt ((12 + 1 : ℕ) : ℝ))⁻¹ := by
      rw [one_mul, Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
      exact factor_le_of_thirteen hs (by norm_num)
    have h := norm_LFunction_le_of_factor χ hχ hM hs 12 (by norm_num) hk
    rw [show ((12 + 1 : ℕ) : ℝ) = 13 by norm_num, show ((12 : ℕ) : ℝ) = 12 by norm_num,
      one_mul] at h
    have hX : (Real.sqrt 13)⁻¹ ≤ 0.27736 :=
      inv_sqrt_le (y := 3.60555) (by norm_num) (by norm_num) (by norm_num)
    have h12 : Real.sqrt 12 ≤ 3.46411 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hlo : 4.4721 ≤ t := by rw [ht]; exact Real.le_sqrt_of_sq_le (by linarith)
    have hhi : t ≤ 8 := by rw [ht]; exact Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
    have hprod := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
    have h7 : (12 + M) * (Real.sqrt 13)⁻¹ ≤ (12 + M) * 0.27736 :=
      mul_le_mul_of_nonneg_left hX (by linarith)
    have h8 : 3.4641 * t ≤ 2 * r * t := by nlinarith
    nlinarith
  · -- N = ceil(M/3), the paper's choice
    set N : ℕ := ⌈M / 3⌉₊ with hNdef
    have hN1 : M / 3 ≤ N := Nat.le_ceil _
    have hN2 : (N : ℝ) < M / 3 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hNpos : 1 ≤ N := by
      have : (0 : ℝ) < N := by linarith
      exact_mod_cast this
    have hk : ‖s‖ / s.re * ((N + 1 : ℕ) : ℝ) ^ (-s.re) ≤
        1 * (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ := by
      rw [one_mul, Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
      exact factor_le_of_thirteen hs (by push_cast; linarith)
    have h := norm_LFunction_le_of_factor χ hχ hM hs N hNpos hk
    rw [one_mul] at h
    set a := Real.sqrt N with ha
    have ha2 : a ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
    have ha4 : 4 ≤ a := Real.le_sqrt_of_sq_le (by linarith)
    have ht8 : 8 ≤ t := by rw [ht]; exact Real.le_sqrt_of_sq_le (by linarith)
    have hle : (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ ≤ a⁻¹ :=
      inv_anti₀ (by linarith) (Real.sqrt_le_sqrt (by push_cast; linarith))
    have h7 : ((N : ℝ) + M) * (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ ≤ ((N : ℝ) + M) * a⁻¹ :=
      mul_le_mul_of_nonneg_left hle (by linarith)
    -- the main inequality: 2a - 1 + (a² + t²)/a ≤ 2 r t, that is (r a - t)² ≤ a
    have hd0 : 0 ≤ r * a - t := by
      by_contra hneg
      push Not at hneg
      nlinarith [mul_pos (show 0 < r * a + t by nlinarith) (neg_pos.mpr hneg)]
    have hd1 : r * a - t ≤ 3 / 16 := by
      by_contra hneg
      push Not at hneg
      have hsum : 16 ≤ r * a + t := by nlinarith
      nlinarith [mul_le_mul hsum hneg.le (by norm_num) (by linarith)]
    have hsq : (r * a - t) ^ 2 ≤ a := by nlinarith
    have hfin : 2 * a - 1 + ((N : ℝ) + M) * a⁻¹ ≤ 2 * r * t := by
      have ha0 : 0 < a := by linarith
      rw [← ha2, ← ht2]
      have e : 2 * a - 1 + (a ^ 2 + t ^ 2) * a⁻¹ = (3 * a ^ 2 - a + t ^ 2) / a := by
        field_simp; ring
      rw [e, div_le_iff₀ ha0]
      have e2 : (r * a - t) ^ 2 = r ^ 2 * a ^ 2 - 2 * r * t * a + t ^ 2 := by ring
      rw [hr2] at e2
      linarith
    linarith

/-- PROVED. P0014 displays 4.18 and 4.19, page 36, the lab leaf Residue123.strip_bound_4_19 with
the body of charSumMax written out: for χ primitive mod q, q not 1, and s in the closed disc of
radius 5/8 about 9/8, abs L(s, χ) is at most 2√3 √M(q), M(q) the largest absolute value of a
partial sum of χ. -/
theorem strip_bound_4_19 (hχ : χ.IsPrimitive) (hq : q ≠ 1) (s : ℂ)
    (hs : s ∈ Metric.closedBall (9 / 8 : ℂ) (5 / 8)) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      2 * Real.sqrt 3 * Real.sqrt (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) := by
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
    exact hq hχ.symm
  exact strip_bound_of_le χ hχ1 (norm_partialSum_le_iSup χ hχ1) hs

end character

end LeanLab.HelfgottMajor.StripBound123
