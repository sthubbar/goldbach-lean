module

public import LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122Rect
public import LeanLab.PNTPort.ExplicitPsi1.CharEdges1122

/-!
# The far left edge for primitive `L(s, χ)` vanishes

Unit P1122-0016, ROUTE BURST burst-20261122 session S2, port step 5. AI wrote the Lean code.
Binary Goldbach is OPEN; nothing here bears on it directly. Davenport, Multiplicative Number
Theory, second edition, ch. 19 pp. 116 and 117, the analogue of `TrivialLimit.lean` for the sharp
kernel: with `T` fixed, the left vertical edge `Re s = -2K - 1/2` of the rectangle of
`rect_left_char` contributes nothing as `K → ∞`, for `x > 1`.

* `logDeriv_far_left_leaf`, PROVED, formerly a LEAF of class EASY: Davenport p. 116 to 117,
  `L'/L(s, χ) = O(log(q|s|))` on the lines `Re s = -2K - 1/2`, derived here from
  `CharEdges1122.logDeriv_far_left1122` of the sibling unit edges1122 with `C = 2A`.
* `left_edge_tendsto_zero`, which takes that bound for the given `χ` as a hypothesis, and
  `left_edge_tendsto_zero_of_leaf`, which discharges it, so it is unconditional:
  `∫_{-T}^{T} -(L'/L)(σ_K + it) x^{σ_K + it}/(σ_K + it) dt → 0`, `σ_K = -2K - 1/2`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122

open Complex Filter Topology Set MeasureTheory
open scoped Real

/-- Davenport, Multiplicative Number Theory, second edition, ch. 19 pp. 116 and 117, the display
`L'(s, χ)/L(s, χ) = O[log(q|s|)]` in `Re s ≤ -1` with circles of radius `1/2` about the trivial
zeros excluded, here on the lines `Re s = -2K - 1/2`, `K ≥ 1`. PROVED, formerly a LEAF of class
EASY: it is a corollary of `CharEdges1122.logDeriv_far_left1122`, which bounds
`‖L'/L(s, χ)‖ ≤ A log(q(‖s‖ + 2))` for primitive `χ` on `Re s ≤ -1/2` with `1/2 ≤ ‖s + j‖` for all
integers `j`. The points `-2K - 1/2 + it` satisfy this because their real part is a half
integer, and `q(‖s‖ + 2) ≤ q(2K + |t| + 2) + q ≤ (q(2K + |t| + 2))^2` gives `C = 2A`. -/
theorem logDeriv_far_left_leaf : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ K : ℕ, 1 ≤ K → ∀ t : ℝ,
      ‖deriv (DirichletCharacter.LFunction χ) ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I) /
          DirichletCharacter.LFunction χ ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)‖ ≤
        C * Real.log ((q : ℝ) * (2 * K + |t| + 2)) := by
  obtain ⟨A, hA, h⟩ := LeanLab.PNTPort.ExplicitPsi1.CharEdges1122.logDeriv_far_left1122
  refine ⟨2 * A, by positivity, fun q _ χ hprim _ K hK t => ?_⟩
  set σ : ℝ := -2 * (K : ℝ) - 1 / 2 with hσ
  set s : ℂ := ((σ : ℝ) : ℂ) + t * I with hs
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hre : s.re ≤ -1 / 2 := by rw [hsre, hσ]; linarith
  have hj : ∀ j : ℤ, 1 / 2 ≤ ‖s + j‖ := by
    intro j
    have hle : |(s + j).re| ≤ ‖s + j‖ := Complex.abs_re_le_norm _
    have hre' : (s + j).re = (j : ℝ) - 2 * K - 1 / 2 := by
      simp [hsre, hσ]; ring
    rw [hre'] at hle
    have hm : (1 / 2 : ℝ) ≤ |((j - 2 * (K : ℤ) : ℤ) : ℝ) - 1 / 2| := by
      rcases le_or_gt (j - 2 * (K : ℤ)) 0 with h0 | h0
      · have : ((j - 2 * (K : ℤ) : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h0
        rw [abs_of_neg (by linarith)]; linarith
      · have : (1 : ℝ) ≤ ((j - 2 * (K : ℤ) : ℤ) : ℝ) := by exact_mod_cast h0
        rw [abs_of_pos (by linarith)]; linarith
    have hcast : ((j - 2 * (K : ℤ) : ℤ) : ℝ) - 1 / 2 = (j : ℝ) - 2 * K - 1 / 2 := by
      push_cast; ring
    rw [hcast] at hm
    linarith
  obtain ⟨_, hb⟩ := h q χ hprim s hre hj
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set Y : ℝ := 2 * K + |t| + 2 with hY
  have hY4 : 4 ≤ Y := by rw [hY]; linarith [abs_nonneg t]
  have hnorm : ‖s‖ ≤ 2 * K + 1 / 2 + |t| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = 2 * K + 1 / 2 + |t| := by
        rw [hsre, hsim, hσ, abs_of_neg (by linarith)]; ring
  have hpos : 0 < (q : ℝ) * (‖s‖ + 2) := by positivity
  have hqY : 4 ≤ (q : ℝ) * Y := by nlinarith
  have hle : (q : ℝ) * (‖s‖ + 2) ≤ ((q : ℝ) * Y) ^ 2 := by
    have h1 : (q : ℝ) * (‖s‖ + 2) ≤ (q : ℝ) * Y + q := by nlinarith
    nlinarith
  have hlog : Real.log ((q : ℝ) * (‖s‖ + 2)) ≤ 2 * Real.log ((q : ℝ) * Y) := by
    rw [← Real.log_rpow (by linarith) 2]
    exact Real.log_le_log hpos (by rw [Real.rpow_two]; exact hle)
  calc ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
      ≤ A * Real.log ((q : ℝ) * (‖s‖ + 2)) := hb
    _ ≤ A * (2 * Real.log ((q : ℝ) * Y)) := mul_le_mul_of_nonneg_left hlog hA
    _ = 2 * A * Real.log ((q : ℝ) * (2 * K + |t| + 2)) := by rw [hY]; ring

/-- `x^{-2K}` beats any linear growth in `K`. -/
lemma tendsto_lin_mul_rpow {x : ℝ} (hx : 1 < x) (c₀ c₁ : ℝ) :
    Tendsto (fun K : ℕ => (c₀ + c₁ * K) * x ^ (-2 * (K : ℝ) - 1 / 2)) atTop (𝓝 0) := by
  have hx0 : 0 < x := by linarith
  set r : ℝ := (x⁻¹) ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    have : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
    have : 0 < x⁻¹ := by positivity
    rw [hr]; nlinarith
  have hr2 : x ^ (-2 : ℝ) = r := by
    rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hr,
      inv_pow]
  have hpow : ∀ K : ℕ, x ^ (-2 * (K : ℝ) - 1 / 2) = x ^ (-(1 / 2 : ℝ)) * r ^ K := by
    intro K
    rw [← hr2, ← Real.rpow_natCast (x ^ (-2 : ℝ)) K, ← Real.rpow_mul hx0.le,
      ← Real.rpow_add hx0]
    congr 1
    ring
  have h0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 (by rw [abs_of_nonneg hr0]; exact hr1)
  have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 (by rw [abs_of_nonneg hr0]; exact hr1)
  have h := ((h0.const_mul c₀).add (h1.const_mul c₁)).const_mul (x ^ (-(1 / 2 : ℝ)))
  simp only [mul_zero, add_zero] at h
  refine h.congr (fun K => ?_)
  rw [hpow]
  simp only [pow_zero, one_mul, pow_one]
  ring

/-- **The far left edge vanishes.** Davenport ch. 19 pp. 116 and 117, CONDITIONAL on the
bound of the leaf `logDeriv_far_left_leaf` for this `χ`, taken as the hypothesis `hB`:
for primitive `χ ≠ 1`, `x > 1` and fixed `T > 0`,
`∫_{-T}^{T} -(L'/L)(σ_K + it, χ) x^{σ_K + it}/(σ_K + it) dt → 0` as `K → ∞`,
`σ_K = -2K - 1/2`. -/
theorem left_edge_tendsto_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, 1 ≤ K → ∀ t : ℝ,
      ‖deriv (DirichletCharacter.LFunction χ) ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I) /
          DirichletCharacter.LFunction χ ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)‖ ≤
        C * Real.log ((q : ℝ) * (2 * K + |t| + 2)))
    {x T : ℝ} (hx : 1 < x) (hT : 0 < T) :
    Tendsto (fun K : ℕ => ∫ t in (-T)..T,
      (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s)
        ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := hB
  have hx0 : 0 < x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  -- the pointwise majorant on the edge
  set M : ℕ → ℝ := fun K => C * (Real.log q + (2 * K + T + 2)) * x ^ (-2 * (K : ℝ) - 1 / 2)
    with hM
  have hpt : ∀ K : ℕ, 1 ≤ K → ∀ t ∈ Set.uIoc (-T) T,
      ‖(fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s)
        ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)‖ ≤ M K := by
    intro K hK t ht
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have htT : |t| ≤ T := by
      rw [Set.uIoc_of_le (by linarith)] at ht
      exact abs_le.mpr ⟨ht.1.le, ht.2⟩
    set s : ℂ := (((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I with hs
    have hsre : s.re = -2 * (K : ℝ) - 1 / 2 := by simp [hs]
    have hsn : 1 ≤ ‖s‖ := by
      have := abs_re_le_norm s
      rw [hsre, abs_of_neg (by linarith)] at this
      linarith
    have hxs : ‖(x : ℂ) ^ s‖ = x ^ (-2 * (K : ℝ) - 1 / 2) := by
      rw [norm_cpow_eq_rpow_re_of_pos hx0, hsre]
    have hL := hC K hK t
    have hlog : Real.log ((q : ℝ) * (2 * K + |t| + 2)) ≤ Real.log q + (2 * K + T + 2) := by
      rw [Real.log_mul (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < 2 * (K : ℝ) + |t| + 2 by positivity)
      linarith
    have hxp : 0 ≤ x ^ (-2 * (K : ℝ) - 1 / 2) := Real.rpow_nonneg hx0.le _
    simp only
    rw [norm_div, norm_mul, norm_neg, hxs]
    calc ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ *
          x ^ (-2 * (K : ℝ) - 1 / 2) / ‖s‖
        ≤ ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ *
          x ^ (-2 * (K : ℝ) - 1 / 2) := div_le_self (by positivity) hsn
      _ ≤ (C * (Real.log q + (2 * K + T + 2))) * x ^ (-2 * (K : ℝ) - 1 / 2) := by
          gcongr
          exact hL.trans (mul_le_mul_of_nonneg_left hlog hC0)
      _ = M K := by rw [hM]
  have hbound : ∀ K : ℕ, 1 ≤ K → ‖∫ t in (-T)..T,
      (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s)
        ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)‖ ≤ M K * |T - -T| :=
    fun K hK => intervalIntegral.norm_integral_le_of_norm_le_const (hpt K hK)
  have hM0 : Tendsto (fun K : ℕ => M K * |T - -T|) atTop (𝓝 0) := by
    have := (tendsto_lin_mul_rpow hx (C * (Real.log q + T + 2)) (2 * C)).mul_const |T - -T|
    rw [zero_mul] at this
    refine this.congr (fun K => ?_)
    rw [hM]; ring
  refine squeeze_zero_norm' ?_ hM0
  filter_upwards [eventually_ge_atTop 1] with K hK
  exact hbound K hK

/-- CONDITIONAL on `logDeriv_far_left_leaf`: the far left edge vanishes for every primitive
`χ ≠ 1`, `x > 1`, `T > 0`, Davenport ch. 19 pp. 116 and 117. It becomes unconditional once
`CharEdges1122` of the sibling unit edges1122 is on main, either by closing the leaf from
`CharEdges1122.logDeriv_far_left1122` or as the subsequence `K ↦ 2K` of
`CharEdges1122.char_left_edge_tendsto1122`, whose edges are `Re s = -(K + 1/2)`. -/
theorem left_edge_tendsto_zero_of_leaf {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {x T : ℝ} (hx : 1 < x) (hT : 0 < T) :
    Tendsto (fun K : ℕ => ∫ t in (-T)..T,
      (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s)
        ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := logDeriv_far_left_leaf
  exact left_edge_tendsto_zero ⟨C, hC0, fun K hK t => hC q χ hprim hχ K hK t⟩ hx hT

end LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122
