module

public import LeanLab.PNTPort.ExplicitPsi1.CharRect1122
public import LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122Left

/-!
# The contour shift at a good height for primitive `L(s, χ)`, Davenport ch. 19 pp. 116 and 117

ROUTE BURST burst-20261122 session S73. AI wrote the Lean code in this file. Binary Goldbach is
OPEN; this file is analytic infrastructure for the character explicit formula of
BhowmikGrimmelt2026 Theorem 3.1.

Davenport, Multiplicative Number Theory, second edition, ch. 19 pp. 116 and 117: with
`c = 1 + 1/log x`, `x = n ≥ 2`, and a height `T' ≥ 2` at which `|L'/L(σ ± iT', χ)| ≤ K` on
`-1/2 ≤ σ ≤ 2`, the truncated Perron integral `J = (1/2πi) ∫_{c-iT'}^{c+iT'} -L'/L(s) xˢ/s ds`
equals the residue sum `-Σ_{|γ|<T'} m(ρ) x^ρ/ρ - (1 - a) log x - b(χ) + Σ_m x^(a-2m)/(2m - a)`
up to the horizontal integrals, which are `O((K + 1) x/T')` on `-1/2 ≤ σ ≤ c` and
`O(log(qT')/T')` on `σ ≤ -1/2`, the far left edge tending to `0`.

* `near_horizontal_bound`: the horizontal integral on `-1/2 ≤ σ ≤ c`, Davenport p. 116, from
  `CharEdges1122.char_horizontal_edge1122` with `|L'/L| ≤ K` on `σ ≤ 2` and
  `CharEdges1122.logDeriv_L_right1122` on `σ ≥ 3/2`, and `x^c = e x`.
* `far_horizontal_bound`: the horizontal integral on `σ₀ ≤ σ ≤ -1/2`, Davenport p. 117, from
  `CharEdges1122.logDeriv_far_left1122`, `L'/L(s, χ) = O(log q|s|)`, integrated exactly against
  `x^σ`.
* `contour_bound`: the statement of the LEAF `CharHalfAssembly1122.contour_good_height_leaf` with
  its four definitions unfolded, from the residue sums `CharRect1122.char_rect_explicit_*` on
  `[-1/2, c] × [-T', T']`, `CharTrivial1122.tendsto_rect_left_char` on
  `[-2K - 1/2, -1/2] × [-T', T']`, and `CharTrivial1122.left_edge_tendsto_zero_of_leaf`.
No new definitions, no cited input, no open leaf.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.CharContour1122

open Complex Filter Topology Set MeasureTheory
open scoped Real

/-- `log x ≥ 1/2` for `x ≥ 2`. -/
lemma half_le_log {x : ℝ} (hx : 2 ≤ x) : 1 / 2 ≤ Real.log x := by
  have := Real.log_two_gt_d9
  have : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  linarith

/-- `x^(1 + 1/log x) ≤ 3x` for `x ≥ 2`: `x^(1/log x) = e`. -/
lemma rpow_c_le {x : ℝ} (hx : 2 ≤ x) : x ^ (1 + 1 / Real.log x) ≤ 3 * x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := by linarith [half_le_log hx]
  rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0,
    mul_one_div_cancel hl.ne']
  have := Real.exp_one_lt_d9
  nlinarith

/-- Davenport, Multiplicative Number Theory, second edition, ch. 19 p. 116: the horizontal
integral of the sharp kernel `-L'/L(s, χ) xˢ/s` along `-1/2 ≤ σ ≤ c = 1 + 1/log x` at a height
`y`, `|y| ≥ 2`, where `|L'/L(σ + iy, χ)| ≤ K` for `-1/2 ≤ σ ≤ 2`, is `O((K + 1) x/|y|)`. On
`2 ≤ σ ≤ c` the bound `|L'/L| ≤ -ζ'/ζ(3/2)` of `CharEdges1122.logDeriv_L_right1122` is used. -/
theorem near_horizontal_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x → ∀ y K : ℝ, y ≠ 0 → 0 ≤ K →
      (∀ σ ∈ Icc (-1 / 2 : ℝ) 2,
        ‖deriv χ.LFunction (σ + y * I) / χ.LFunction (σ + y * I)‖ ≤ K) →
      ‖∫ σ in (-1 / 2 : ℝ)..(1 + 1 / Real.log x),
        -(deriv χ.LFunction ((σ : ℂ) + y * I) / χ.LFunction ((σ : ℂ) + y * I)) *
          (x : ℂ) ^ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I)‖ ≤
        A * ((K + 1) * x / |y|) := by
  obtain ⟨CR, hCR, hR⟩ := CharEdges1122.logDeriv_L_right1122
  refine ⟨11 * (1 + CR), by positivity, ?_⟩
  intro q _ χ x hx y K hy hK hb
  have hl := half_le_log hx
  have hl0 : 0 < Real.log x := by linarith
  set c : ℝ := 1 + 1 / Real.log x with hc
  have hinv : 1 / Real.log x ≤ 2 := by
    rw [div_le_iff₀ hl0]; linarith
  have hinv0 : 0 < 1 / Real.log x := by positivity
  have hσc : (-1 / 2 : ℝ) ≤ c := by rw [hc]; linarith
  have hB : ∀ σ ∈ Icc (-1 / 2 : ℝ) c,
      ‖deriv χ.LFunction ((σ : ℂ) + y * I) / χ.LFunction ((σ : ℂ) + y * I)‖ ≤ K + CR := by
    intro σ hσ
    rcases le_total σ 2 with h2 | h2
    · exact (hb σ ⟨hσ.1, h2⟩).trans (by linarith)
    · have hre : ((σ : ℂ) + y * I).re = σ := by simp
      have := hR q χ ((σ : ℂ) + y * I) (by rw [hre]; linarith)
      linarith
  have h := CharEdges1122.char_horizontal_edge1122 χ (x := x) (by linarith) hσc hy hB
  refine h.trans ?_
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hxc : x ^ c ≤ 3 * x := rpow_c_le hx
  have hlen : c - -1 / 2 ≤ 7 / 2 := by rw [hc]; linarith
  have hlen0 : 0 ≤ c - -1 / 2 := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hxc0 : 0 ≤ x ^ c := Real.rpow_nonneg hx0 _
  rw [div_le_iff₀ hy0]
  have hrw : 11 * (1 + CR) * ((K + 1) * x / |y|) * |y| = 11 * (1 + CR) * ((K + 1) * x) := by
    field_simp
  rw [hrw]
  have e1 : (K + CR) * x ^ c * (c - -1 / 2) ≤ (K + CR) * (3 * x) * (7 / 2) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hxc (by positivity)) hlen hlen0
    positivity
  have e2 : (K + CR) ≤ (1 + CR) * (K + 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right e2 hx0]

/-- `log(a + u) ≤ log a + u` for `a ≥ 1`, `u ≥ 0`. -/
lemma log_add_le {a u : ℝ} (ha : 1 ≤ a) (hu : 0 ≤ u) : Real.log (a + u) ≤ Real.log a + u := by
  have ha0 : 0 < a := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (a + u) / a by positivity)
  rw [Real.log_div (by linarith) ha0.ne'] at h
  have : (a + u) / a - 1 = u / a := by field_simp; ring
  rw [this] at h
  have : u / a ≤ u := div_le_self hu ha
  linarith

/-- Davenport, Multiplicative Number Theory, second edition, ch. 19 p. 117: the horizontal
integral of the sharp kernel along `σ₀ ≤ σ ≤ -1/2` at a height `|y| ≥ 2` is
`O(log(q|y|)/|y|)`, uniformly in `σ₀`, for primitive `χ` and `x ≥ 2`. Here
`|L'/L(s, χ)| ≤ A log(q(|s| + 2)) ≤ A (log(q(|y| + 2)) - σ)` by
`CharEdges1122.logDeriv_far_left1122`, and `∫_{-∞}^{-1/2} (ℓ - σ) x^σ dσ` is computed from the
primitive `x^σ ((ℓ - σ)/log x + 1/log² x)`. -/
theorem far_horizontal_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ x : ℝ, 2 ≤ x → ∀ y : ℝ, 2 ≤ |y| →
      ∀ σ₀ : ℝ, σ₀ ≤ -1 / 2 →
      ‖∫ σ in σ₀..(-1 / 2 : ℝ),
        -(deriv χ.LFunction ((σ : ℂ) + y * I) / χ.LFunction ((σ : ℂ) + y * I)) *
          (x : ℂ) ^ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I)‖ ≤
        A * (Real.log ((q : ℝ) * |y|) / |y|) := by
  obtain ⟨A0, hA0, hA⟩ := CharEdges1122.logDeriv_far_left1122
  refine ⟨16 * A0, by positivity, ?_⟩
  intro q _ χ hprim x hx y hy σ₀ hσ₀
  have hx0 : 0 < x := by linarith
  have hl := half_le_log hx
  set lam : ℝ := Real.log x with hlamdef
  have hlam0 : 0 < lam := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hy0 : 0 < |y| := by linarith
  set ℓ : ℝ := Real.log ((q : ℝ) * (|y| + 2)) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by nlinarith)
  set g : ℝ → ℝ := fun σ => A0 / |y| * ((ℓ - σ) * Real.exp (lam * σ)) with hg
  set G : ℝ → ℝ := fun σ => A0 / |y| * (Real.exp (lam * σ) * ((ℓ - σ) / lam + 1 / lam ^ 2))
    with hG
  have hgc : Continuous g := by rw [hg]; fun_prop
  -- pointwise bound
  have hpt : ∀ σ ∈ Set.uIoc σ₀ (-1 / 2 : ℝ),
      ‖-(deriv χ.LFunction ((σ : ℂ) + y * I) / χ.LFunction ((σ : ℂ) + y * I)) *
          (x : ℂ) ^ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I)‖ ≤ g σ := by
    intro σ hσ
    rw [Set.uIoc_of_le hσ₀] at hσ
    have hσ1 : σ ≤ -1 / 2 := hσ.2
    set s : ℂ := (σ : ℂ) + y * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsim : s.im = y := by simp [hs]
    have hj : ∀ j : ℤ, 1 / 2 ≤ ‖s + j‖ := by
      intro j
      have h := Complex.abs_im_le_norm (s + j)
      have e : (s + j).im = y := by simp [hs]
      rw [e] at h
      linarith
    obtain ⟨-, hB⟩ := hA q χ hprim s (by rw [hsre]; exact hσ1) hj
    have hsn : ‖s‖ ≤ -σ + |y| := by
      have := Complex.norm_le_abs_re_add_abs_im s
      rw [hsre, hsim, abs_of_neg (by linarith)] at this
      exact this
    have hsy : |y| ≤ ‖s‖ := by
      have := Complex.abs_im_le_norm s
      rwa [hsim] at this
    have hlog : Real.log ((q : ℝ) * (‖s‖ + 2)) ≤ ℓ - σ := by
      have h4 : Real.log ((q : ℝ) * (‖s‖ + 2)) ≤ Real.log q + Real.log (|y| + 2 + -σ) := by
        rw [← Real.log_mul (by positivity) (by linarith)]
        exact Real.log_le_log (by have := norm_nonneg s; positivity)
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      have h5 := log_add_le (a := |y| + 2) (u := -σ) (by linarith) (by linarith)
      have h6 : ℓ = Real.log q + Real.log (|y| + 2) := by
        rw [hℓ, Real.log_mul (by positivity) (by linarith)]
      linarith
    have hxs : ‖(x : ℂ) ^ s‖ = Real.exp (lam * σ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hsre, Real.rpow_def_of_pos hx0]
    rw [norm_div, norm_mul, norm_neg, hxs, hg]
    have hLb : ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ A0 * (ℓ - σ) :=
      hB.trans (mul_le_mul_of_nonneg_left hlog hA0)
    have he : 0 < Real.exp (lam * σ) := Real.exp_pos _
    rw [div_le_iff₀ (by linarith)]
    calc ‖deriv χ.LFunction s / χ.LFunction s‖ * Real.exp (lam * σ)
        ≤ A0 * (ℓ - σ) * Real.exp (lam * σ) := mul_le_mul_of_nonneg_right hLb he.le
      _ = A0 / |y| * ((ℓ - σ) * Real.exp (lam * σ)) * |y| := by field_simp
      _ ≤ A0 / |y| * ((ℓ - σ) * Real.exp (lam * σ)) * ‖s‖ := by
          apply mul_le_mul_of_nonneg_left hsy
          have : 0 ≤ ℓ - σ := by linarith
          positivity
  have hint := intervalIntegral.norm_integral_le_of_norm_le hσ₀
    (Filter.Eventually.of_forall (fun σ hσ => hpt σ (by rwa [Set.uIoc_of_le hσ₀])))
    (hgc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
  refine hint.trans ?_
  -- the primitive
  have hderiv : ∀ σ ∈ Set.uIcc σ₀ (-1 / 2 : ℝ), HasDerivAt G (g σ) σ := by
    intro σ _
    have h1 : HasDerivAt (fun σ => Real.exp (lam * σ)) (Real.exp (lam * σ) * lam) σ := by
      have := ((hasDerivAt_id σ).const_mul lam).exp
      simpa using this
    have h2 : HasDerivAt (fun σ : ℝ => (ℓ - σ) / lam + 1 / lam ^ 2) (-1 / lam) σ := by
      have := (((hasDerivAt_id σ).const_sub ℓ).div_const lam).add_const (1 / lam ^ 2)
      simpa [neg_div] using this
    have h3 := (h1.mul h2).const_mul (A0 / |y|)
    convert h3 using 1
    rw [hg]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hgc.intervalIntegrable (μ := MeasureTheory.volume) _ _)]
  have hGσ₀ : 0 ≤ G σ₀ := by
    rw [hG]
    have : 0 ≤ ℓ - σ₀ := by linarith
    positivity
  have hGtop : G (-1 / 2) ≤ A0 / |y| * (2 * ℓ + 5) := by
    rw [hG]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have he : Real.exp (lam * (-1 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he0 : 0 < Real.exp (lam * (-1 / 2)) := Real.exp_pos _
    have hi : 1 / lam ≤ 2 := by rw [div_le_iff₀ hlam0]; linarith
    have hi0 : 0 < 1 / lam := by positivity
    have hi2 : 1 / lam ^ 2 ≤ 4 := by
      rw [show 1 / lam ^ 2 = (1 / lam) ^ 2 by ring]; nlinarith
    have hin : 0 ≤ (ℓ - -1 / 2) / lam + 1 / lam ^ 2 := by
      have : 0 ≤ ℓ - -1 / 2 := by linarith
      positivity
    have hb : (ℓ - -1 / 2) / lam + 1 / lam ^ 2 ≤ 2 * ℓ + 5 := by
      rw [div_eq_mul_one_div (ℓ - -1 / 2)]
      nlinarith
    calc Real.exp (lam * (-1 / 2)) * ((ℓ - -1 / 2) / lam + 1 / lam ^ 2)
        ≤ 1 * ((ℓ - -1 / 2) / lam + 1 / lam ^ 2) := mul_le_mul_of_nonneg_right he hin
      _ ≤ 2 * ℓ + 5 := by linarith
  -- `2ℓ + 5 ≤ 16 log(q|y|)`
  have hqy : 2 ≤ (q : ℝ) * |y| := by nlinarith
  have hlqy : 1 / 2 ≤ Real.log ((q : ℝ) * |y|) := half_le_log hqy
  have hℓle : ℓ ≤ 1 + Real.log ((q : ℝ) * |y|) := by
    have h1 : ℓ ≤ Real.log (2 * ((q : ℝ) * |y|)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num) (by positivity)] at h1
    have := Real.log_two_lt_d9
    linarith
  have hfin : A0 / |y| * (2 * ℓ + 5) ≤ 16 * A0 * (Real.log ((q : ℝ) * |y|) / |y|) := by
    have hk : 2 * ℓ + 5 ≤ 16 * Real.log ((q : ℝ) * |y|) := by linarith
    have := mul_le_mul_of_nonneg_left hk (show 0 ≤ A0 / |y| by positivity)
    calc A0 / |y| * (2 * ℓ + 5) ≤ A0 / |y| * (16 * Real.log ((q : ℝ) * |y|)) := this
      _ = _ := by ring
  linarith

/-- `‖1/(2πi)‖ ≤ 1`. -/
lemma norm_inv_two_pi_I_le : ‖(1 / (2 * (π : ℂ) * I))‖ ≤ 1 := by
  rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one,
    div_le_one (by positivity)]
  linarith [Real.pi_gt_three]

/-- `‖1/(2π)‖ ≤ 1`. -/
lemma norm_inv_two_pi_le : ‖(1 / (2 * (π : ℂ)))‖ ≤ 1 := by
  rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_one (by positivity)]
  linarith [Real.pi_gt_three]

/-- The contour algebra of Davenport ch. 19 pp. 116 and 117, for any integrand `F`: the right
edge `(1/2π) ∫_{-T}^{T} F(c + it) dt` minus the residue integral over `[-1/2, c] × [-T, T]` and
minus the limit `tr` of the residue integrals over `[-2K - 1/2, -1/2] × [-T, T]` is bounded by
the four horizontal integrals once the far left edges tend to `0`. -/
theorem contour_core (F : ℂ → ℂ) (c T B1 B2 : ℝ) (tr : ℂ)
    (hR2 : Tendsto (fun K : ℕ => RectangleIntegral' F ⟨-2 * (K : ℝ) - 1 / 2, -T⟩ ⟨-1 / 2, T⟩)
      atTop (𝓝 tr))
    (hleft : Tendsto (fun K : ℕ => ∫ t in (-T)..T,
      F ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)) atTop (𝓝 0))
    (hH1b : ‖∫ σ in (-1 / 2 : ℝ)..c, F ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B1)
    (hH1t : ‖∫ σ in (-1 / 2 : ℝ)..c, F ((σ : ℂ) + (T : ℂ) * I)‖ ≤ B1)
    (hH2b : ∀ K : ℕ, ‖∫ σ in (-2 * (K : ℝ) - 1 / 2)..(-1 / 2 : ℝ),
      F ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B2)
    (hH2t : ∀ K : ℕ, ‖∫ σ in (-2 * (K : ℝ) - 1 / 2)..(-1 / 2 : ℝ),
      F ((σ : ℂ) + (T : ℂ) * I)‖ ≤ B2) :
    ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T, F ((c : ℂ) + t * I)) -
      RectangleIntegral' F ⟨-1 / 2, -T⟩ ⟨c, T⟩ - tr‖ ≤ 2 * B1 + 2 * B2 := by
  set P : ℂ := (1 / (2 * π) : ℂ) * (∫ t in (-T)..T, F ((c : ℂ) + t * I)) with hP
  set R1 : ℂ := RectangleIntegral' F ⟨-1 / 2, -T⟩ ⟨c, T⟩ with hR1
  have hid : ∀ K : ℕ, P - R1 - tr =
      (RectangleIntegral' F ⟨-2 * (K : ℝ) - 1 / 2, -T⟩ ⟨-1 / 2, T⟩ - tr) -
      (1 / (2 * π * I)) * ((∫ σ in (-1 / 2 : ℝ)..c, F ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) -
        (∫ σ in (-1 / 2 : ℝ)..c, F ((σ : ℂ) + (T : ℂ) * I)) +
        (∫ σ in (-2 * (K : ℝ) - 1 / 2)..(-1 / 2 : ℝ), F ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) -
        (∫ σ in (-2 * (K : ℝ) - 1 / 2)..(-1 / 2 : ℝ), F ((σ : ℂ) + (T : ℂ) * I))) +
      (1 / (2 * π) : ℂ) * ∫ t in (-T)..T, F ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I) := by
    intro K
    rw [hP, hR1]
    simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  set ε : ℕ → ℝ := fun K =>
    ‖RectangleIntegral' F ⟨-2 * (K : ℝ) - 1 / 2, -T⟩ ⟨-1 / 2, T⟩ - tr‖ +
      ‖∫ t in (-T)..T, F ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)‖ with hε
  have hbound : ∀ K : ℕ, ‖P - R1 - tr‖ ≤ ε K + (2 * B1 + 2 * B2) := by
    intro K
    rw [hid K, hε]
    set a := ∫ σ in (-1 / 2 : ℝ)..c, F ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)
    set b' := ∫ σ in (-1 / 2 : ℝ)..c, F ((σ : ℂ) + (T : ℂ) * I)
    set d := ∫ σ in (-2 * (K : ℝ) - 1 / 2)..(-1 / 2 : ℝ), F ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)
    set e := ∫ σ in (-2 * (K : ℝ) - 1 / 2)..(-1 / 2 : ℝ), F ((σ : ℂ) + (T : ℂ) * I)
    set f := ∫ t in (-T)..T, F ((((-2 * (K : ℝ) - 1 / 2) : ℝ) : ℂ) + t * I)
    set r := RectangleIntegral' F ⟨-2 * (K : ℝ) - 1 / 2, -T⟩ ⟨-1 / 2, T⟩ - tr
    have hd : ‖d‖ ≤ B2 := hH2b K
    have he : ‖e‖ ≤ B2 := hH2t K
    have h4 : ‖a - b' + d - e‖ ≤ 2 * B1 + 2 * B2 := by
      have := norm_sub_le (a - b' + d) e
      have := norm_add_le (a - b') d
      have := norm_sub_le a b'
      linarith [hH1b, hH1t]
    have hk1 : ‖(1 / (2 * π * I)) * (a - b' + d - e)‖ ≤ 2 * B1 + 2 * B2 := by
      rw [norm_mul]
      calc ‖(1 / (2 * (π : ℂ) * I))‖ * ‖a - b' + d - e‖ ≤ 1 * ‖a - b' + d - e‖ :=
            mul_le_mul_of_nonneg_right norm_inv_two_pi_I_le (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h4
    have hk2 : ‖(1 / (2 * π) : ℂ) * f‖ ≤ ‖f‖ := by
      rw [norm_mul]
      calc ‖(1 / (2 * (π : ℂ)))‖ * ‖f‖ ≤ 1 * ‖f‖ :=
            mul_le_mul_of_nonneg_right norm_inv_two_pi_le (norm_nonneg _)
        _ = ‖f‖ := one_mul _
    have := norm_add_le (r - (1 / (2 * π * I)) * (a - b' + d - e)) ((1 / (2 * π) : ℂ) * f)
    have := norm_sub_le r ((1 / (2 * π * I)) * (a - b' + d - e))
    show _ ≤ ‖r‖ + ‖f‖ + (2 * B1 + 2 * B2)
    linarith
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have h1 := (hR2.sub_const tr).norm
    have h2 := hleft.norm
    rw [sub_self, norm_zero] at h1
    rw [norm_zero] at h2
    simpa [hε] using h1.add h2
  have hlim : Tendsto (fun K => ε K + (2 * B1 + 2 * B2)) atTop (𝓝 (2 * B1 + 2 * B2)) := by
    simpa using hεt.add_const (2 * B1 + 2 * B2)
  exact ge_of_tendsto' hlim hbound

lemma not_even_of_odd' {q : ℕ} {χ : DirichletCharacter ℂ q} (h : χ.Odd) : ¬ χ.Even := by
  intro he
  have h1 : χ (-1) = 1 := he
  have h2 : χ (-1) = -1 := h
  rw [h1] at h2
  norm_num at h2

open Classical in
/-- Davenport, Multiplicative Number Theory, second edition, ch. 19 pp. 116 and 117, the contour
argument leading to display (4) at a good height `T'`: the statement of
`CharHalfAssembly1122.contour_good_height_leaf` with `perronJ`, `zeroLog`, `trivSum` and `IsB`
unfolded. PROVED from `contour_core`, the residue sums `CharRect1122.char_rect_explicit_even_primitive`
and `char_rect_explicit_of_ne_zero`, `CharTrivial1122.tendsto_rect_left_char`,
`CharTrivial1122.left_edge_tendsto_zero_of_leaf`, `near_horizontal_bound` and
`far_horizontal_bound`. -/
theorem contour_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ T' K : ℝ, 2 ≤ T' → 0 ≤ K →
      (∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ τ ∈ ({T', -T'} : Set ℝ),
        χ.LFunction (σ + τ * I) ≠ 0 ∧
        ‖deriv χ.LFunction (σ + τ * I) / χ.LFunction (σ + τ * I)‖ ≤ K) →
      ∀ b : ℂ, ((χ.Odd ∧ b = deriv (DirichletCharacter.LFunction χ) 0 /
          DirichletCharacter.LFunction χ 0) ∨
        (χ.Even ∧ Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b))) →
      ∀ n : ℕ, 2 ≤ n → ∀ Z' : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z' ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T') →
      ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T')..T',
          -(deriv (DirichletCharacter.LFunction χ)
              (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I) /
            DirichletCharacter.LFunction χ (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I)) *
          (n : ℂ) ^ (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I) /
            (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I)) +
        (∑ ρ ∈ Z', (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
            (n : ℂ) ^ ρ / ρ) + ((if χ.Even then Real.log n else 0 : ℝ) : ℂ) + b -
          ((if χ.Even then -(1 / 2) * Real.log (1 - ((n : ℝ)⁻¹) ^ 2)
            else (1 / 2) * (Real.log (1 + (n : ℝ)⁻¹) - Real.log (1 - (n : ℝ)⁻¹)) : ℝ) : ℂ)‖ ≤
        D * ((K + 1) * n / T' + Real.log ((q : ℝ) * T') / T' + Real.log n) := by
  obtain ⟨A1, hA1, h1⟩ := near_horizontal_bound
  obtain ⟨A2, hA2, h2⟩ := far_horizontal_bound
  obtain ⟨AL, -, hfl⟩ := CharEdges1122.logDeriv_far_left1122
  refine ⟨2 * A1 + 2 * A2, by positivity, ?_⟩
  intro q _ χ hprim hχ T' K hT' hK hgood b hb n hn Z' hZ'
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm]
  have hx2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx1 : (1 : ℝ) < n := by linarith
  have hx0 : (0 : ℝ) < n := by linarith
  have hlx := half_le_log hx2
  have hT0 : 0 < T' := by linarith
  have hc1 : 1 < 1 + 1 / Real.log n := by
    have : 0 < 1 / Real.log (n : ℝ) := by
      have : 0 < Real.log (n : ℝ) := by linarith
      positivity
    linarith
  have hc0 : 0 < 1 + 1 / Real.log n := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  -- the parity
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1) := by
    rcases χ.even_or_odd with h | h
    · exact ⟨0, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨1, Or.inr ⟨h, rfl⟩⟩
  have hre1 : ∀ z : ℂ, 1 ≤ z.re → DirichletCharacter.LFunction χ z ≠ 0 := fun z h =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h
  have hgoodz : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 2 → (z.im = T' ∨ z.im = -T') →
      DirichletCharacter.LFunction χ z ≠ 0 := by
    intro z h1 h2 h3
    have hm : z.im ∈ ({T', -T'} : Set ℝ) := by
      rcases h3 with h | h <;> rw [h] <;> simp
    have := (hgood z.re ⟨h1, h2⟩ z.im hm).1
    rwa [Complex.re_add_im] at this
  -- the border of `[-1/2, c] × [-T', T']`
  have hbd : ∀ z ∈ RectangleBorder (⟨-1 / 2, -T'⟩ : ℂ) ⟨1 + 1 / Real.log n, T'⟩,
      DirichletCharacter.LFunction χ z ≠ 0 := by
    intro z hz
    have hzR := (mem_rect (c := 1 + 1 / Real.log n) (T := T') (by linarith) hT0.le).1
      (rectangleBorder_subset_rectangle _ _ hz)
    rcases border_cases hz with h | h | h | h
    · by_cases h1 : 1 ≤ z.re
      · exact hre1 z h1
      · exact hgoodz z hzR.1.1 (by linarith) (Or.inr h)
    · refine (hfl q χ hprim z (by rw [h]) (fun j => ?_)).1
      have hh := Complex.abs_re_le_norm (z + j)
      have e : (z + j).re = -1 / 2 + j := by simp [h]
      rw [e] at hh
      rcases le_or_gt 1 j with hj | hj
      · have : (1 : ℝ) ≤ j := by exact_mod_cast hj
        rw [abs_of_nonneg (by linarith)] at hh; linarith
      · have : (j : ℝ) ≤ 0 := by exact_mod_cast (by omega : j ≤ 0)
        rw [abs_of_neg (by linarith)] at hh; linarith
    · by_cases h1 : 1 ≤ z.re
      · exact hre1 z h1
      · exact hgoodz z hzR.1.1 (by linarith) (Or.inl h)
    · exact hre1 z (by rw [h]; linarith)
  -- the zeros inside
  have hZset : (CharRect1122.charZeros_rect_finite χ hχ (1 + 1 / Real.log n) T').toFinset.erase 0
      = Z' := by
    ext ρ
    rw [Finset.mem_erase, Set.Finite.mem_toFinset, hZ']
    constructor
    · rintro ⟨hne, hR, hz⟩
      have hR' := (mem_rect (c := 1 + 1 / Real.log n) (T := T') (by linarith) hT0.le).1 hR
      have hz : DirichletCharacter.LFunction χ ρ = 0 := hz
      have hre0 : 0 < ρ.re := by
        by_contra hneg
        push_neg at hneg
        obtain ⟨k, hk⟩ :=
          (CharTrivial1122.LFunction_eq_zero_iff_of_re_nonpos hprim hχ ha hneg).1 hz
        have hkre := congrArg Complex.re hk
        simp at hkre
        have hlt : ((a + 2 * k : ℕ) : ℝ) < 1 := by push_cast; linarith [hR'.1.1]
        have hnat : a + 2 * k = 0 := by
          have : a + 2 * k < 1 := by exact_mod_cast hlt
          omega
        have ha0 : a = 0 := by omega
        have hk0 : k = 0 := by omega
        subst ha0 hk0
        apply hne
        rw [hk]; simp
      have hre1' : ρ.re < 1 := by
        by_contra h
        push_neg at h
        exact hre1 ρ h hz
      have him : |ρ.im| < T' := by
        have hle : |ρ.im| ≤ T' := abs_le.mpr hR'.2
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exfalso
          refine hgoodz ρ (by linarith) (by linarith) ?_ hz
          rcases abs_eq (by linarith : (0 : ℝ) ≤ T') |>.1 h with h' | h'
          · exact Or.inl h'
          · exact Or.inr h'
      exact ⟨hz, hre0, hre1', him⟩
    · rintro ⟨hz, hre0, hre1', him⟩
      refine ⟨fun h => by rw [h] at hre0; simp at hre0, ?_, hz⟩
      rw [mem_rect (c := 1 + 1 / Real.log n) (T := T') (by linarith) hT0.le]
      rw [abs_lt] at him
      exact ⟨⟨by linarith, by linarith⟩, ⟨him.1.le, him.2.le⟩⟩
  -- the residue integral over `[-1/2, c] × [-T', T']`
  have hR1 : RectangleIntegral' (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * ((n : ℝ) : ℂ) ^ s / s)
        ⟨-1 / 2, -T'⟩ ⟨1 + 1 / Real.log n, T'⟩ =
      -(((if χ.Even then Real.log n else 0 : ℝ) : ℂ) + b) -
        ∑ ρ ∈ Z', (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
          ((n : ℝ) : ℂ) ^ ρ / ρ := by
    rcases hb with ⟨ho, rfl⟩ | ⟨he, hlim⟩
    · have h0 := (CharTrivial1122.residue_zero_odd hprim hχ ho hx0).1
      have hR := CharRect1122.char_rect_explicit_of_ne_zero χ hχ hx0 hc0 hT0 h0 hbd
      have hZ0 : (CharRect1122.charZeros_rect_finite χ hχ (1 + 1 / Real.log n) T').toFinset
          = Z' := by
        rw [← hZset, Finset.erase_eq_of_notMem]
        rw [Set.Finite.mem_toFinset]
        exact fun h => h0 h.2
      rw [if_neg (not_even_of_odd' ho), hR, hZ0]
      simp
    · obtain ⟨b0, hb0, hR⟩ :=
        CharRect1122.char_rect_explicit_even_primitive χ hχ hprim he hx0 hc0 hT0 hbd
      have hbb : b0 = b := tendsto_nhds_unique hb0 hlim
      rw [if_pos he, hR, hZset, hbb]
  -- the trivial zeros
  have hR2 := CharTrivial1122.tendsto_rect_left_char hprim hχ ha hx1 hT0
  have htr : (if a = 0 then ((-(1 / 2) * Real.log (1 - ((n : ℝ)⁻¹) ^ 2) : ℝ) : ℂ)
        else (((1 / 2) * (Real.log (1 + (n : ℝ)⁻¹) - Real.log (1 - (n : ℝ)⁻¹)) : ℝ) : ℂ)) =
      ((if χ.Even then -(1 / 2) * Real.log (1 - ((n : ℝ)⁻¹) ^ 2)
        else (1 / 2) * (Real.log (1 + (n : ℝ)⁻¹) - Real.log (1 - (n : ℝ)⁻¹)) : ℝ) : ℂ) := by
    rcases ha with ⟨he, rfl⟩ | ⟨ho, rfl⟩
    · rw [if_pos rfl, if_pos he]
    · rw [if_neg one_ne_zero, if_neg (not_even_of_odd' ho)]
  rw [htr] at hR2
  have hleft := CharTrivial1122.left_edge_tendsto_zero_of_leaf hprim hχ hx1 hT0
  -- the horizontal bounds
  have hK1b := h1 q χ n hx2 (-T') K (by linarith) hK
    (fun σ hσ => (hgood σ hσ (-T') (by simp)).2)
  have hK1t := h1 q χ n hx2 T' K (by linarith) hK
    (fun σ hσ => (hgood σ hσ T' (by simp)).2)
  rw [abs_neg, abs_of_pos hT0] at hK1b
  rw [abs_of_pos hT0] at hK1t
  have hK2b := fun Kn : ℕ => h2 q χ hprim n hx2 (-T') (by rw [abs_neg, abs_of_pos hT0]; exact hT')
    (-2 * (Kn : ℝ) - 1 / 2) (by have := (Nat.cast_nonneg Kn : (0 : ℝ) ≤ Kn); linarith)
  have hK2t := fun Kn : ℕ => h2 q χ hprim n hx2 T' (by rw [abs_of_pos hT0]; exact hT')
    (-2 * (Kn : ℝ) - 1 / 2) (by have := (Nat.cast_nonneg Kn : (0 : ℝ) ≤ Kn); linarith)
  simp only [abs_neg, abs_of_pos hT0] at hK2b hK2t
  have hcore := contour_core (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * ((n : ℝ) : ℂ) ^ s / s)
    (1 + 1 / Real.log n) T' (A1 * ((K + 1) * n / T')) (A2 * (Real.log ((q : ℝ) * T') / T'))
    _ hR2 hleft hK1b hK1t hK2b hK2t
  rw [hR1] at hcore
  have e : ∀ P S zl tr : ℂ, P + S + zl + b - tr = P - (-(zl + b) - S) - tr := by
    intros; ring
  rw [e]
  refine hcore.trans ?_
  have hlq : 0 ≤ Real.log ((q : ℝ) * T') := Real.log_nonneg (by nlinarith)
  have t1 : 0 ≤ (K + 1) * n / T' := by positivity
  have t2 : 0 ≤ Real.log ((q : ℝ) * T') / T' := by positivity
  have t3 : 0 ≤ Real.log (n : ℝ) := by linarith
  nlinarith [mul_nonneg hA1 t2, mul_nonneg hA1 t3, mul_nonneg hA2 t1, mul_nonneg hA2 t3]

end LeanLab.PNTPort.ExplicitPsi1.CharContour1122
