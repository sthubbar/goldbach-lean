module

public import LeanLab.DERZ1997.Decomp1529b
public import LeanLab.DERZ1997.Decomp574a

/-!
Unit P1122-0012, ROUTE BURST burst-20261122 S2, port step 2 toward
davenport_integer_half_formula592 of Bhowmik Grimmelt 2026, P0029.

The character analogue of `perron_F`: the truncated sharp Perron formula for
`ψ(x, χ)` at an INTEGER `x = n ≥ 2` with the half weight at the endpoint,
Davenport, Multiplicative Number Theory, 2nd ed. 1980, ch. 17 pages 105 to 109,
the Lemma on page 105 with its three cases y > 1, y = 1, 0 < y < 1, the choice
`c = 1 + 1/log x` on ch. 17 page 107, and ch. 19 page 116, where the character
plays no part in the estimate of display (3) of section 17.

For every modulus q, every Dirichlet character χ mod q, every integer n ≥ 2 and T ≥ 2,
with c = 1 + 1/log n,

  ‖ (∑_{m < n} Λ(m) χ(m) + (1/2) Λ(n) χ(n))
      - (1/2π) ∫_{-T}^{T} -(L'/L)(c+it, χ) n^(c+it)/(c+it) dt ‖ ≤ 434 (n log² n / T + log n).

The sum shape is exactly that of davenport_integer_half_formula592. The proof reuses the
proved kernel lemmas perron_gt_one, perron_lt_one, perron_one, the sum and integral
interchange perron_character_tsum197, the bridge character_perron_logderiv574 and the
coefficient bound perron_tail_arbitrary266, which holds at every real x ≥ 2: at y = 1
its min term is min 1 (1/0) = 0 under the Lean convention, and the y = 1 term is paid
separately here by perron_one, costing Λ(n) c / T ≤ (3/2) log n.

No open leaf, no new definitions, no new axioms.
AI wrote the Lean code, Claude, 2026-11-22. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.PNTPort.ExplicitPsi1.CharPerronHalf1122
open Complex Real MeasureTheory Set
open LeanLab.DERZ1997.Decomp1529b LeanLab.DERZ1997.Decomp1529b2 LeanLab.DERZ1997.Decomp574a

/-- The half weighted character sum `∑_{m < n} Λ(m) χ(m) + (1/2) Λ(n) χ(n)` written as a
series with the step weight `1, 1/2, 0` for `m < n`, `m = n`, `m > n`.
Davenport ch. 17 page 105, the discontinuity of the Perron kernel at y = 1, and ch. 19
page 116. Finite support bookkeeping. -/
theorem half_weight_tsum1122 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ∑' m : ℕ, χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) *
      (if m < n then 1 else if m = n then (1 / 2 : ℂ) else 0) =
    (∑ m ∈ Finset.range n, (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
      (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) := by
  classical
  have h0 : ∀ m ∉ Finset.range (n + 1), χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) *
      (if m < n then 1 else if m = n then (1 / 2 : ℂ) else 0) = 0 := by
    intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [if_neg (by omega), if_neg (by omega), mul_zero]
  rw [tsum_eq_sum h0, Finset.sum_range_succ, if_neg (lt_irrefl n), if_pos rfl]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    rw [if_pos (Finset.mem_range.mp hm)]
    ring
  · ring

/-- Termwise Perron error at an integer x = n with the half weight: for m ≠ n the kernel
lemma for y = n/m ≠ 1 gives `Λ(m) (n/m)^c min(1, 1/(T |log(n/m)|))`, and for m = n the
kernel at y = 1 gives `|perronI 1 c T - 1/2| ≤ c/T`, so the extra cost `Λ(n) c / T`.
Davenport ch. 17, Lemma, page 105, all three cases, and ch. 19 page 116. -/
theorem half_kernel_error1122 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n)
    {c T : ℝ} (hc : 1 < c) (hT : 0 < T) (m : ℕ) :
    ‖χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) *
        (if m < n then 1 else if m = n then (1 / 2 : ℂ) else 0) -
      χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) * perronI ((n : ℝ) / m) c T‖ ≤
      ArithmeticFunction.vonMangoldt m * ((n : ℝ) / m) ^ c *
          min 1 (1 / (T * |Real.log ((n : ℝ) / m)|)) +
        (if m = n then ArithmeticFunction.vonMangoldt n * c / T else 0) := by
  have hE0 : 0 ≤ ArithmeticFunction.vonMangoldt m * ((n : ℝ) / m) ^ c *
      min 1 (1 / (T * |Real.log ((n : ℝ) / m)|)) := by
    have : 0 ≤ ((n : ℝ) / m) := by positivity
    positivity
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hF : 0 ≤ (if 0 = n then ArithmeticFunction.vonMangoldt n * c / T else 0) := by
      split_ifs
      · have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
        have : 0 < c := by linarith
        positivity
      · exact le_rfl
    simpa using add_nonneg hE0 hF
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : ‖(χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ))‖ ≤
      ArithmeticFunction.vonMangoldt m := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
  by_cases hmn : m = n
  · subst hmn
    rw [if_neg (lt_irrefl m), if_pos rfl, if_pos rfl, div_self hm0.ne']
    rw [show χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) * (1 / 2 : ℂ) -
        χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) * perronI 1 c T =
        -((χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ)) *
          (perronI 1 c T - 1 / 2)) by ring, norm_neg, norm_mul]
    have hk := perron_one (by linarith : 0 < c) hT
    have h1 := mul_le_mul hh hk (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    have h2 : ArithmeticFunction.vonMangoldt m * (c / T) =
        ArithmeticFunction.vonMangoldt m * c / T := by ring
    have hE1 : 0 ≤ ArithmeticFunction.vonMangoldt m * ((m : ℝ) / m) ^ c *
        min 1 (1 / (T * |Real.log ((m : ℝ) / m)|)) := hE0
    rw [div_self hm0.ne'] at hE1
    linarith
  · rw [show (if m = n then ArithmeticFunction.vonMangoldt n * c / T else 0) = 0 from
      if_neg hmn, add_zero]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hne : (m : ℝ) ≠ n := by exact_mod_cast hmn
    have hw : (if m < n then (1 : ℂ) else if m = n then (1 / 2 : ℂ) else 0) =
        (if (m : ℝ) < n then 1 else 0) := by
      by_cases hlt : m < n
      · rw [if_pos hlt, if_pos (by exact_mod_cast hlt)]
      · rw [if_neg hlt, if_neg hmn, if_neg (by exact_mod_cast hlt)]
    rw [hw]
    have hk : ‖perronI ((n : ℝ) / m) c T - (if (m : ℝ) < n then 1 else 0)‖ ≤
        ((n : ℝ) / m) ^ c * min 1 (1 / (T * |Real.log ((n : ℝ) / m)|)) := by
      by_cases hlt : (m : ℝ) < n
      · have hy : 1 < (n : ℝ) / m := (one_lt_div hm0).mpr hlt
        simpa [hlt, abs_of_pos (Real.log_pos hy)] using perron_gt_one hy (by linarith) hT
      · have hlt' : (n : ℝ) < m := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
        have hy : (n : ℝ) / m < 1 := (div_lt_one hm0).mpr hlt'
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have hy0 : 0 < (n : ℝ) / m := div_pos (by linarith) hm0
        simpa [hlt] using perron_lt_one hy0 hy (by linarith) hT
    rw [show χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) *
          (if (m : ℝ) < n then 1 else 0) -
        χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) * perronI ((n : ℝ) / m) c T =
        -((χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ)) *
          (perronI ((n : ℝ) / m) c T - (if (m : ℝ) < n then 1 else 0))) by ring,
      norm_neg, norm_mul]
    exact (mul_le_mul hh hk (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg).trans_eq
      (by ring)

/-- Character Perron formula at an integer x = n ≥ 2 with the half weight, tsum form:
`‖(∑_{m<n} Λχ + (1/2) Λ(n)χ(n)) - ∑' m, χ(m)Λ(m) perronI (n/m) c T‖` is at most the
Perron coefficient tail plus `Λ(n) c / T`.
Davenport ch. 17 pages 105 to 106 and ch. 19 page 116. -/
theorem char_perron_half_tsum1122 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hn : 2 ≤ n) {c T : ℝ} (hc : 1 < c) (hT : 0 < T) :
    ‖((∑ m ∈ Finset.range n, (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
        (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) -
      ∑' m : ℕ, χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) *
        perronI ((n : ℝ) / m) c T‖ ≤
      (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * ((n : ℝ) / m) ^ c *
          min 1 (1 / (T * |Real.log ((n : ℝ) / m)|))) +
        ArithmeticFunction.vonMangoldt n * c / T := by
  classical
  have hx0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let a : ℕ → ℂ := fun m => χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) *
    (if m < n then 1 else if m = n then (1 / 2 : ℂ) else 0)
  let b : ℕ → ℂ := fun m => χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) *
    perronI ((n : ℝ) / m) c T
  let E : ℕ → ℝ := fun m => ArithmeticFunction.vonMangoldt m * ((n : ℝ) / m) ^ c *
    min 1 (1 / (T * |Real.log ((n : ℝ) / m)|))
  let F : ℕ → ℝ := fun m => if m = n then ArithmeticFunction.vonMangoldt n * c / T else 0
  have hE0 : ∀ m, 0 ≤ E m := fun m => by dsimp [E]; positivity
  have hE : Summable E := by
    apply (LeanLab.DERZ1997.Perron136.perron_coeff_summable hx0 hc).of_nonneg_of_le hE0
    intro m
    exact mul_le_of_le_one_right (by positivity) (min_le_left _ _)
  have hF0 : ∀ m ∉ ({n} : Finset ℕ), F m = 0 := by
    intro m hm
    simp only [Finset.mem_singleton] at hm
    simp [F, hm]
  have hF : Summable F := summable_of_ne_finset_zero hF0
  have hFt : ∑' m, F m = ArithmeticFunction.vonMangoldt n * c / T := by
    rw [tsum_eq_sum hF0, Finset.sum_singleton]
    simp [F]
  have ha0 : ∀ m ∉ Finset.range (n + 1), a m = 0 := by
    intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    simp only [a]
    rw [if_neg (by omega), if_neg (by omega), mul_zero]
  have ha : Summable a := summable_of_ne_finset_zero ha0
  have he : ∀ m, ‖a m - b m‖ ≤ E m + F m := fun m =>
    half_kernel_error1122 χ (by omega) hc hT m
  have hd : Summable (fun m => a m - b m) := (hE.add hF).of_norm_bounded he
  have hb : Summable b := by
    convert ha.sub hd using 1
    funext m
    simp
  rw [← half_weight_tsum1122 χ n]
  change ‖∑' m, a m - ∑' m, b m‖ ≤ _
  rw [← ha.tsum_sub hb, ← hFt, ← hE.tsum_add hF]
  exact tsum_of_norm_bounded (hE.add hF).hasSum he

/-- The character analogue of `perron_F`, explicit constant: the truncated sharp Perron
formula for `ψ(n, χ)` at an integer `n ≥ 2` with the half weight at the endpoint and
`c = 1 + 1/log n`, for every modulus q, every χ mod q and every T ≥ 2,
`‖(∑_{m<n} Λ(m)χ(m) + (1/2)Λ(n)χ(n)) - (1/2π)∫_{-T}^{T} -(L'/L)(c+it,χ) n^(c+it)/(c+it) dt‖
≤ 434 (n log² n / T + log n)`.
Davenport ch. 17 pages 105 to 109, Lemma page 105 and display (5) style tail bound,
and ch. 19 page 116. -/
theorem char_perron_half_explicit1122 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : 2 ≤ n) {T : ℝ} (hT : 2 ≤ T) :
    ‖((∑ m ∈ Finset.range n, (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
        (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) -
      (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        -(deriv (DirichletCharacter.LFunction χ)
            (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I) /
          DirichletCharacter.LFunction χ (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I)) *
        (n : ℂ) ^ (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I) /
          (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I))‖ ≤
      434 * ((n : ℝ) * Real.log n ^ 2 / T + Real.log n) := by
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hx
  have hc : 1 < 1 + 1 / Real.log n := by
    have := one_div_pos.mpr hlog
    linarith
  have hc3 : 1 + 1 / Real.log n ≤ 3 := by
    have h1 : 1 / Real.log n ≤ 2 := by
      rw [div_le_iff₀ hlog]
      linarith [Real.log_two_gt_d9]
    linarith
  have hcast : (n : ℂ) = ((n : ℝ) : ℂ) := (Complex.ofReal_natCast n).symm
  rw [hcast, ← character_perron_logderiv574 χ (n : ℝ) (1 + 1 / Real.log n) T hc,
    perron_character_tsum197 χ hx0 hc hT0]
  have h1 := char_perron_half_tsum1122 χ hn hc hT0
  have h2 := perron_tail_arbitrary266 hx hT
  have hL : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have hL0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have h3 : ArithmeticFunction.vonMangoldt n * (1 + 1 / Real.log n) / T ≤
      (3 / 2) * Real.log n := by
    rw [div_le_iff₀ hT0]
    have := mul_le_mul hL hc3 (by linarith) hlog.le
    nlinarith
  have hpos : 0 ≤ (n : ℝ) * Real.log n ^ 2 / T := by positivity
  calc _ ≤ _ := h1
    _ ≤ 432 * ((n : ℝ) * Real.log n ^ 2 / T) + 32 * Real.log n + (3 / 2) * Real.log n :=
      add_le_add h2 h3
    _ ≤ _ := by nlinarith

/-- UNIT P1122-0012. The character analogue of `perron_F`: there is an absolute C such that
for every q, every χ mod q, every integer n ≥ 2 and every T ≥ 2, with c = 1 + 1/log n,
`‖(∑_{m<n} Λ(m)χ(m) + (1/2)Λ(n)χ(n)) - (1/2π)∫_{-T}^{T} -(L'/L)(c+it,χ) n^(c+it)/(c+it) dt‖
≤ C (n log² n / T + log n)`. Davenport ch. 17 pages 105 to 109 and ch. 19 page 116.
PROVED with C = 434. -/
theorem char_perron_half1122 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ), 2 ≤ n → ∀ T : ℝ, 2 ≤ T →
    ‖((∑ m ∈ Finset.range n, (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
        (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) -
      (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        -(deriv (DirichletCharacter.LFunction χ)
            (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I) /
          DirichletCharacter.LFunction χ (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I)) *
        (n : ℂ) ^ (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I) /
          (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I))‖ ≤
      C * ((n : ℝ) * Real.log n ^ 2 / T + Real.log n) :=
  ⟨434, by norm_num, fun _ _ χ _ hn _ hT => char_perron_half_explicit1122 χ hn hT⟩

end LeanLab.PNTPort.ExplicitPsi1.CharPerronHalf1122
