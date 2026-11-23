module

public import LeanLab.Linnik.ExplicitFormula.LeftHalf

/-!
# Character edges of the explicit formula rectangle, Davenport ch 19 pages 116 to 117

AI wrote the Lean code. Binary Goldbach is OPEN.
Burst burst-20261122 S2, unit P1122-0014, port step 4 toward the cited leaf
`davenport_integer_half_formula592` of P0029. Model: `ExplicitPsi1.Edges.norm_HInt_le` and
`ExplicitPsi1.LeftZeta`, `ExplicitPsi1.TrivialLimit`. The kernel is the SHARP one,
`-(L'/L)(s, χ) x^s / s`, written inline.

(a) Horizontal edges, Davenport page 116: `char_horizontal_edge1122`,
`char_horizontal_edge_height1122`, `char_horizontal_integrable1122`. The good height bound
`‖L'/L‖ ≤ B` on the segment is an explicit hypothesis, as in the unit statement.

(b) The far left, Davenport pages 116 to 117: for primitive `χ`, off discs of radius `1/2`
around the integers in `Re s ≤ -1/2`, `|L'/L(s, χ)| ≤ A log(q(|s| + 2))`
(`logDeriv_far_left1122`), from

* `logDeriv_fe_far1122`: the functional equation differentiated logarithmically, Mathlib's
  `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`;
* `digamma_growth1122`: Stirling, `|ψ(w)| ≤ K log(|w| + 2)` on `Re w ≥ 1/2`;
* `norm_cot_pi_le1122`: `cot(πw)` bounded off discs of radius `1/4` at the integers, used with
  the reflection formula `digamma_one_sub`;
* `logDeriv_L_right1122`: `|L'/L(u, χ)| ≤ C` on `Re u ≥ 3/2`.

Then `char_left_edge1122` bounds the left vertical integral on `Re s = -U` and
`char_left_edge_tendsto1122` shows it tends to `0` along `U = K + 1/2`, `K → ∞`.
No open leaf, no new definitions, no cited input.
-/

@[expose] public section


open Complex Set Filter Topology MeasureTheory
open scoped Real
open LeanLab.Linnik.ExplicitFormula

namespace LeanLab.PNTPort.ExplicitPsi1.CharEdges1122


/-- (a) horizontal edge. -/
theorem char_horizontal_edge1122 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σL c y B : ℝ} (hx : 1 ≤ x) (hσ : σL ≤ c) (hy : y ≠ 0)
    (hb : ∀ σ ∈ Icc σL c,
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + y * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + y * I)‖ ≤ B) :
    ‖∫ σ in σL..c,
      -(deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + y * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + y * I)) *
          (x : ℂ) ^ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I)‖ ≤
      B * x ^ c * (c - σL) / |y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hb σL ⟨le_rfl, hσ⟩)
  have hpt : ∀ σ ∈ Set.uIoc σL c,
      ‖-(deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + y * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + y * I)) *
          (x : ℂ) ^ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I)‖ ≤ B * x ^ c / |y| := by
    intro σ hσ'
    rw [Set.uIoc_of_le hσ] at hσ'
    have hσI : σ ∈ Icc σL c := ⟨hσ'.1.le, hσ'.2⟩
    rw [norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : ((σ : ℂ) + y * I).re = σ := by simp
    rw [hre]
    have hn : |y| ≤ ‖(σ : ℂ) + y * I‖ := by
      have hh := Complex.abs_im_le_norm ((σ : ℂ) + y * I)
      simpa using hh
    have hp : x ^ σ ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx hσ'.2
    have hnum : ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + y * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + y * I)‖ * x ^ σ ≤ B * x ^ c :=
      mul_le_mul (hb σ hσI) hp (Real.rpow_nonneg hx0.le _) hB
    exact div_le_div₀ (mul_nonneg hB (Real.rpow_nonneg hx0.le _)) hnum hy0 hn
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (by linarith : 0 ≤ c - σL)] at hh
  calc _ ≤ B * x ^ c / |y| * (c - σL) := hh
    _ = _ := by ring

/-- `‖cot(πw)‖ ≤ 3` once `|Im w| ≥ 1`. -/
lemma norm_cot_pi_le_of_im {w : ℂ} (h : 1 ≤ |w.im|) : ‖Complex.cot (π * w)‖ ≤ 3 := by
  rw [Complex.cot_pi_eq_exp_ratio]
  set E := Complex.exp (2 * π * I * w) with hE
  have hEn : ‖E‖ = Real.exp (-(2 * π * w.im)) := by
    rw [hE, Complex.norm_exp]; congr 1; simp
  have hpi := Real.pi_gt_three
  rw [norm_div, norm_mul, Complex.norm_I, one_mul]
  rcases le_or_gt 0 w.im with h0 | h0
  · rw [abs_of_nonneg h0] at h
    have hsmall : ‖E‖ ≤ 1 / 2 := by
      rw [hEn]
      have := Real.exp_neg_one_lt_half
      have : Real.exp (-(2 * π * w.im)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have h1 : ‖E + 1‖ ≤ 3 / 2 := (norm_add_le _ _).trans (by simp; linarith)
    have h2 : 1 / 2 ≤ ‖1 - E‖ := by
      have := norm_sub_norm_le (1 : ℂ) E; simp at this; linarith
    rw [div_le_iff₀ (by linarith)]; linarith
  · rw [abs_of_neg h0] at h
    have hbig : 2 ≤ ‖E‖ := by
      rw [hEn]
      have : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      have : Real.exp 1 ≤ Real.exp (-(2 * π * w.im)) := Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have h1 : ‖E + 1‖ ≤ ‖E‖ + 1 := (norm_add_le _ _).trans (by simp)
    have h2 : ‖E‖ - 1 ≤ ‖1 - E‖ := by
      have := norm_sub_norm_le E (1 : ℂ); rw [norm_sub_rev] at this; simp at this; linarith
    rw [div_le_iff₀ (by linarith)]; linarith

lemma cot_pi_sub_int (z : ℂ) (m : ℤ) : Complex.cot (π * (z + m)) = Complex.cot (π * z) := by
  rw [Complex.cot_pi_eq_exp_ratio, Complex.cot_pi_eq_exp_ratio]
  have : Complex.exp (2 * π * I * (z + m)) = Complex.exp (2 * π * I * z) := by
    rw [show 2 * π * I * (z + m) = 2 * π * I * z + m * (2 * π * I) by ring, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [this]

/-- Davenport ch 19 page 117 needs `cot(πw)` bounded off discs of radius 1/4 around the integers. -/
theorem norm_cot_pi_le1122 : ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, (∀ m : ℤ, 1 / 4 ≤ ‖w - m‖) →
    ‖Complex.cot (π * w)‖ ≤ M := by
  set S : Set ℂ := {z | |z.re| ≤ 1 / 2 ∧ |z.im| ≤ 1 ∧ 1 / 4 ≤ ‖z‖} with hS
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · apply IsClosed.inter
      · exact isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
      apply IsClosed.inter
      · exact isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
      · exact isClosed_le continuous_const continuous_norm
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨2, fun z hz => ?_⟩
      simp only [Metric.mem_closedBall, dist_zero_right]
      obtain ⟨h1, h2, -⟩ := hz
      have := Complex.norm_le_abs_re_add_abs_im z
      linarith
  set g : ℂ → ℂ := fun z =>
    (Complex.exp (2 * π * I * z) + 1) / (I * (1 - Complex.exp (2 * π * I * z))) with hg
  have hgc : ContinuousOn g S := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    refine mul_ne_zero I_ne_zero (sub_ne_zero.mpr fun he => ?_)
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he.symm
    have hz' : z = n := by
      have h2 : (2 * π * I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, I_ne_zero]
      apply mul_left_cancel₀ h2; rw [hn]; ring
    obtain ⟨h1, -, h3⟩ := hz
    rw [hz'] at h1 h3
    simp at h1 h3
    have : n = 0 := by
      have h1' : |(n : ℝ)| < 1 := by linarith
      have : |n| < 1 := by exact_mod_cast h1'
      rw [abs_lt] at this; omega
    rw [this] at h3; norm_num at h3
  obtain ⟨M0, hM0⟩ := hSc.exists_bound_of_continuousOn hgc
  refine ⟨max M0 3, by positivity, fun w hw => ?_⟩
  rcases le_or_gt 1 |w.im| with him | him
  · exact (norm_cot_pi_le_of_im him).trans (le_max_right _ _)
  set m : ℤ := round w.re with hm
  set z : ℂ := w - m with hz
  have hzS : z ∈ S := by
    refine ⟨?_, ?_, hw m⟩
    · have : z.re = w.re - m := by simp [hz]
      rw [this, hm]
      exact abs_sub_round w.re
    · have : z.im = w.im := by simp [hz]
      rw [this]; exact him.le
  have e : Complex.cot (π * w) = g z := by
    rw [show w = z + m by rw [hz]; ring, cot_pi_sub_int, Complex.cot_pi_eq_exp_ratio]
  rw [e]
  exact (hM0 z hzS).trans (le_max_left _ _)


/-- Horizontal edge at a good height `T' = |y| ≥ T > 0`: the bound of
`char_horizontal_edge1122` with `1/T` in place of `1/|y|`, the form used in Davenport ch 19
page 116 with `B = O(log² qT)`. -/
theorem char_horizontal_edge_height1122 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σL c y B T : ℝ} (hx : 1 ≤ x) (hσ : σL ≤ c) (hT : 0 < T) (hyT : T ≤ |y|)
    (hb : ∀ σ ∈ Icc σL c,
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + y * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + y * I)‖ ≤ B) :
    ‖∫ σ in σL..c,
      -(deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + y * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + y * I)) *
          (x : ℂ) ^ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I)‖ ≤
      B * x ^ c * (c - σL) / T := by
  have hy : y ≠ 0 := by intro h; rw [h, abs_zero] at hyT; linarith
  refine (char_horizontal_edge1122 χ hx hσ hy hb).trans ?_
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hb σL ⟨le_rfl, hσ⟩)
  have : 0 ≤ B * x ^ c * (c - σL) := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) c
    have : 0 ≤ c - σL := by linarith
    positivity
  exact div_le_div_of_nonneg_left this hT hyT

/-- The horizontal edge integrand is interval integrable when `χ ≠ 1`, `y ≠ 0` and `L(s, χ)` has
no zero on the segment; compare `DERZ1997.Decomp574a.character_horizontal_integral574`. -/
theorem char_horizontal_integrable1122 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {x σL c y : ℝ} (hx : 0 < x) (hy : y ≠ 0)
    (hz : ∀ σ ∈ Set.uIcc σL c, DirichletCharacter.LFunction χ ((σ : ℂ) + y * I) ≠ 0) :
    IntervalIntegrable (fun σ : ℝ =>
      -(deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + y * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + y * I)) *
          (x : ℂ) ^ ((σ : ℂ) + y * I) / ((σ : ℂ) + y * I)) MeasureTheory.volume σL c := by
  set L := DirichletCharacter.LFunction χ
  set s : ℝ → ℂ := fun σ => (σ : ℂ) + y * I with hs
  have hsn (σ : ℝ) : s σ ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp [hs] at hh
    exact hy hh
  have hLA (z : ℂ) : AnalyticAt ℂ L z :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hderiv : Continuous (deriv L) :=
    continuous_iff_continuousAt.mpr fun z => (hLA z).deriv.continuousAt
  have hLc : Continuous L := (DirichletCharacter.differentiable_LFunction hχ).continuous
  have hsc : Continuous s := by rw [hs]; fun_prop
  have hcont : ContinuousOn (fun σ : ℝ => -(deriv L (s σ) / L (s σ)) * (x : ℂ) ^ (s σ) / s σ)
      (Set.uIcc σL c) := by
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · exact ((hderiv.comp hsc).continuousOn.div (hLc.comp hsc).continuousOn
          (fun σ hσ => hz σ hσ)).neg
      · exact (Continuous.const_cpow hsc
          (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).continuousOn
    · exact hsc.continuousOn
    · intro σ _; exact hsn σ
  exact hcont.intervalIntegrable

lemma continuousAt_digamma_of_re_pos {w : ℂ} (hw : 0 < w.re) : ContinuousAt digamma w := by
  have hA := LeanLab.PNTPort.ZetaZeros.gamma_analyticAt hw
  have e : digamma = fun z => deriv Gamma z / Gamma z := by
    funext z; rw [digamma_def, logDeriv_apply]
  rw [e]
  exact hA.deriv.continuousAt.div hA.continuousAt
    (LeanLab.PNTPort.ZetaZeros.gamma_ne_zero_of_re_pos hw)

/-- Stirling on the band `1/2 ≤ Re w ≤ 2`. -/
lemma digamma_band : ∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 2 →
    ‖digamma w‖ ≤ K * Real.log (|w.im| + 3) + K := by
  obtain ⟨K1, hK1, hst⟩ := LeanLab.PNTPort.ZetaZeros.digamma_strip
  set S : Set ℂ := {w | 1 / 2 ≤ w.re ∧ w.re ≤ 2 ∧ |w.im| ≤ 1} with hS
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · apply IsClosed.inter
      · exact isClosed_le continuous_const Complex.continuous_re
      apply IsClosed.inter
      · exact isClosed_le Complex.continuous_re continuous_const
      · exact isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨3, fun z hz => ?_⟩
      simp only [Metric.mem_closedBall, dist_zero_right]
      obtain ⟨h1, h2, h3⟩ := hz
      have := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_nonneg (by linarith : 0 ≤ z.re)] at this
      linarith
  have hc : ContinuousOn digamma S := fun z hz =>
    (continuousAt_digamma_of_re_pos (by have := hz.1; linarith)).continuousWithinAt
  obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hc
  refine ⟨K1 + 2 + max M 0, by positivity, fun w h1 h2 => ?_⟩
  have hl0 : 0 ≤ Real.log (|w.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg w.im])
  have hK1l : 0 ≤ K1 * Real.log (|w.im| + 3) := by positivity
  have hrest : 0 ≤ (2 + max M 0) * Real.log (|w.im| + 3) := by positivity
  rcases le_or_gt 1 |w.im| with him | him
  · have key : ‖digamma w‖ ≤ K1 * Real.log (|w.im| + 3) + 2 := by
      rcases le_or_gt 0 w.im with h0 | h0
      · rw [abs_of_nonneg h0] at him ⊢
        have := hst w.im him w.re (by linarith) h2
        rwa [re_add_im] at this
      · rw [abs_of_neg h0] at him ⊢
        have := hst (-w.im) him w.re (by linarith) h2
        have e : w = starRingEnd ℂ ((w.re : ℂ) + ((-w.im : ℝ) : ℂ) * I) := by
          apply Complex.ext <;> simp
        have e2 : digamma w = starRingEnd ℂ (digamma ((w.re : ℂ) + ((-w.im : ℝ) : ℂ) * I)) := by
          rw [← LeanLab.Linnik.ExplicitFormula.digamma_conj', ← e]
        rw [e2, Complex.norm_conj]
        exact this
    nlinarith [le_max_right M 0]
  · have := hM w ⟨h1, h2, him.le⟩
    nlinarith [le_max_left M 0, le_max_right M 0]

/-- Davenport ch 19 page 117, Stirling: `|ψ(w)| ≤ K log(|w| + 2)` on `Re w ≥ 1/2`. -/
theorem digamma_growth1122 : ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, 1 / 2 ≤ w.re →
    ‖digamma w‖ ≤ K * Real.log (‖w‖ + 2) := by
  obtain ⟨K0, hK0, hb⟩ := digamma_band
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * K0 + 1 + (K0 + 1) / Real.log 2, by positivity, fun w hw => ?_⟩
  set L := Real.log (‖w‖ + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [norm_nonneg w])
  have hL0 : 0 ≤ L := hl2.le.trans hL2
  have hc : (K0 + 1) ≤ (K0 + 1) / Real.log 2 * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; nlinarith
  have him3 : ∀ y : ℝ, |y| ≤ ‖w‖ → Real.log (|y| + 3) ≤ 2 * L := by
    intro y hy
    rw [hL, ← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [Real.rpow_two]
    nlinarith [norm_nonneg w, abs_nonneg y]
  have hwim : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  rcases le_or_gt w.re 2 with h2 | h2
  · have := hb w hw h2
    have := him3 w.im hwim
    nlinarith
  -- shift down by `n = ⌊Re w⌋ - 1`
  set k : ℕ := ⌊w.re⌋₊ with hk
  have hk2 : 2 ≤ k := Nat.le_floor (by push_cast; linarith)
  have hkle : (k : ℝ) ≤ w.re := Nat.floor_le (by linarith)
  have hklt : w.re < k + 1 := Nat.lt_floor_add_one _
  set n : ℕ := k - 1 with hn
  have hncast : (n : ℝ) = k - 1 := by rw [hn, Nat.cast_sub (by omega)]; simp
  set w0 : ℂ := w - n with hw0
  have hw0re : w0.re = w.re - n := by simp [hw0]
  have hw0im : w0.im = w.im := by simp [hw0]
  have hr1 : 1 ≤ w0.re := by rw [hw0re, hncast]; linarith
  have hr2 : w0.re ≤ 2 := by rw [hw0re, hncast]; linarith
  have hnm : ∀ m : ℕ, w0 ≠ -(m : ℂ) := by
    intro m h; have := congrArg Complex.re h; simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hrec := digamma_apply_add_nat hnm n
  rw [show w0 + n = w by rw [hw0]; ring] at hrec
  have hsum : ‖∑ j ∈ Finset.range n, (w0 + j)⁻¹‖ ≤ 1 + Real.log n := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j ∈ Finset.range n, ‖(w0 + j)⁻¹‖ ≤ ((j : ℝ) + 1)⁻¹ := by
      intro j _
      rw [norm_inv]
      apply inv_anti₀ (by positivity)
      have := Complex.re_le_norm (w0 + j)
      simp at this
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    have hh := harmonic_le_one_add_log n
    have e : ((harmonic n : ℚ) : ℝ) = ∑ j ∈ Finset.range n, ((j : ℝ) + 1)⁻¹ := by
      simp [harmonic]
    rw [← e]; exact hh
  have hn1 : 1 ≤ n := by omega
  have hlogn : Real.log n ≤ L := by
    apply Real.log_le_log (by exact_mod_cast hn1)
    have := Complex.re_le_norm w
    rw [hncast]; linarith
  have hd0 := hb w0 (by linarith) hr2
  rw [hw0im] at hd0
  have := him3 w.im hwim
  rw [hrec]
  calc ‖digamma w0 + ∑ j ∈ Finset.range n, (w0 + j)⁻¹‖
      ≤ ‖digamma w0‖ + ‖∑ j ∈ Finset.range n, (w0 + j)⁻¹‖ := norm_add_le _ _
    _ ≤ (K0 * Real.log (|w.im| + 3) + K0) + (1 + Real.log n) := add_le_add hd0 hsum
    _ ≤ _ := by nlinarith


/-- `log(‖z‖ + 2)` grows at most like `2 log(‖s‖ + 2)` when `‖z‖ ≤ ‖s‖ + 2`. -/
lemma log_norm_add_two_le {z s : ℂ} (h : ‖z‖ ≤ ‖s‖ + 2) :
    Real.log (‖z‖ + 2) ≤ 2 * Real.log (‖s‖ + 2) := by
  rw [← Real.log_rpow (by positivity), Real.rpow_two]
  apply Real.log_le_log (by positivity)
  nlinarith [norm_nonneg s, norm_nonneg z]

/-- Davenport ch 19 page 117: `Γℝ'/Γℝ(z) = O(log(|z| + 2))` on `Re z ≥ 1`. -/
theorem logDeriv_Gammaℝ_right1122 : ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℂ, 1 ≤ z.re →
    ‖logDeriv Gammaℝ z‖ ≤ A * Real.log (‖z‖ + 2) := by
  obtain ⟨K, hK, hψ⟩ := digamma_growth1122
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlpi : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  refine ⟨2 / Real.log 2 + K, by positivity, fun z hz => ?_⟩
  set L := Real.log (‖z‖ + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
  have hnp : ∀ m : ℕ, z / 2 ≠ -m := by
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [LeanLab.Linnik.ExplicitFormula.logDeriv_Gammaℝ hnp]
  have hre : 1 / 2 ≤ (z / 2).re := by simp; linarith
  have hd := hψ (z / 2) hre
  have hn2 : Real.log (‖z / 2‖ + 2) ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg z]
  have h1 : 2 ≤ 2 / Real.log 2 * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; linarith
  calc _ ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ + ‖digamma (z / 2) / 2‖ := norm_add_le _ _
    _ ≤ 3 / 2 + K * L / 2 := by
        rw [norm_div, norm_div, norm_neg, Complex.norm_ofNat]
        gcongr
        exact hd.trans (mul_le_mul_of_nonneg_left hn2 hK)
    _ ≤ (2 / Real.log 2 + K) * L := by
        have : 0 ≤ K * L := mul_nonneg hK (hl2.le.trans hL2)
        nlinarith

/-- Davenport ch 19 page 117: `Γℝ'/Γℝ(z) = O(log(|z| + 2))` on `Re z ≤ 1/2` off the discs of
radius `1/2` around the integers, by the reflection formula for `ψ`. -/
theorem logDeriv_Gammaℝ_left1122 : ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℂ, z.re ≤ 1 / 2 →
    (∀ j : ℤ, 1 / 2 ≤ ‖z + j‖) → ‖logDeriv Gammaℝ z‖ ≤ A * Real.log (‖z‖ + 2) := by
  obtain ⟨K, hK, hψ⟩ := digamma_growth1122
  obtain ⟨M, hM, hcot⟩ := norm_cot_pi_le1122
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlpi : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  refine ⟨(2 + 4 * M) / Real.log 2 + K, by positivity, fun z hz hj => ?_⟩
  set L := Real.log (‖z‖ + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
  set w : ℂ := z / 2 with hw
  have hwm : ∀ m : ℤ, 1 / 4 ≤ ‖w - m‖ := by
    intro m
    have h := hj (-(2 * m))
    have e : w - m = (z + ((-(2 * m) : ℤ) : ℂ)) / 2 := by rw [hw]; push_cast; ring
    rw [e, norm_div, Complex.norm_ofNat]; linarith
  have hwn : ∀ n : ℤ, w ≠ n := by
    intro n h
    have := hwm n
    rw [h, sub_self, norm_zero] at this; norm_num at this
  have hnp : ∀ m : ℕ, z / 2 ≠ -m := by
    intro m h; apply hwn (-m); rw [hw, h]; push_cast; ring
  rw [LeanLab.Linnik.ExplicitFormula.logDeriv_Gammaℝ hnp]
  have hrefl := digamma_one_sub hwn
  have e : digamma w = digamma (1 - w) - π * Complex.cot (π * w) := by rw [hrefl]; ring
  have hre : 1 / 2 ≤ (1 - w).re := by simp [hw]; linarith
  have hd := hψ (1 - w) hre
  have hn1 : ‖1 - w‖ ≤ ‖z‖ + 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [hw, norm_div, Complex.norm_ofNat, norm_one]; linarith [norm_nonneg z]
  have hd' : ‖digamma (1 - w)‖ ≤ K * (2 * L) :=
    hd.trans (mul_le_mul_of_nonneg_left (log_norm_add_two_le hn1) hK)
  have hc := hcot w hwm
  have hpc : ‖(π : ℂ) * Complex.cot (π * w)‖ ≤ 4 * M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact mul_le_mul Real.pi_le_four hc (norm_nonneg _) (by norm_num)
  have hdw : ‖digamma w‖ ≤ 2 * K * L + 4 * M := by
    rw [e]; refine (norm_sub_le _ _).trans ?_; linarith
  have h1 : 2 + 4 * M ≤ (2 + 4 * M) / Real.log 2 * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; nlinarith
  calc _ ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ + ‖digamma w / 2‖ := norm_add_le _ _
    _ ≤ 3 / 2 + (2 * K * L + 4 * M) / 2 := by
        rw [norm_div, norm_div, norm_neg, Complex.norm_ofNat]
        gcongr
    _ ≤ ((2 + 4 * M) / Real.log 2 + K) * L := by nlinarith

/-- The gamma factor of a character is `Γℝ(s + a)` with `a ∈ {0, 1}`. -/
lemma gammaFactor_eq_shift {q : ℕ} (χ : DirichletCharacter ℂ q) : ∃ a : ℕ, a ≤ 1 ∧
    DirichletCharacter.gammaFactor χ = fun s => Gammaℝ (s + a) := by
  rcases χ.even_or_odd with he | ho
  · exact ⟨0, by norm_num, funext fun s => by rw [he.gammaFactor_def]; simp⟩
  · exact ⟨1, le_rfl, funext fun s => by rw [ho.gammaFactor_def]; simp⟩

lemma Gammaℝ_differentiableAt_of_ne {z : ℂ} (h : Gammaℝ z ≠ 0) : DifferentiableAt ℂ Gammaℝ z := by
  have hd : DifferentiableAt ℂ (fun s => ((Gammaℝ s)⁻¹)⁻¹) z :=
    (differentiable_Gammaℝ_inv z).inv (inv_ne_zero h)
  simpa only [inv_inv] using hd

lemma logDeriv_gammaFactor_eq {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ℕ}
    (ha : DirichletCharacter.gammaFactor χ = fun s => Gammaℝ (s + a)) {s : ℂ}
    (hs : Gammaℝ (s + a) ≠ 0) :
    logDeriv (DirichletCharacter.gammaFactor χ) s = logDeriv Gammaℝ (s + a) := by
  rw [ha]
  have e : (fun s => Gammaℝ (s + a)) = Gammaℝ ∘ fun s : ℂ => s + a := rfl
  rw [e, logDeriv_comp (f := Gammaℝ) (g := fun s : ℂ => s + (a : ℂ)) (Gammaℝ_differentiableAt_of_ne hs)
    (differentiableAt_id.add_const _)]
  simp

lemma Gammaℝ_ne_zero_of_not_nonpos_int {z : ℂ} (h : ∀ n : ℕ, z ≠ -n) : Gammaℝ z ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
  exact h (2 * n) (by rw [hn]; push_cast; ring)

/-- Davenport ch 19 page 117, the gamma factor of `L(s, χ)` on the far left:
`γ'/γ(s, χ) = O(log(|s| + 2))` for `Re s ≤ -1/2` off discs of radius `1/2` at the integers. -/
theorem logDeriv_gammaFactor_left1122 : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q)
    (s : ℂ), s.re ≤ -1 / 2 → (∀ j : ℤ, 1 / 2 ≤ ‖s + j‖) →
      ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ ≤ A * Real.log (‖s‖ + 2) := by
  obtain ⟨A, hA, hb⟩ := logDeriv_Gammaℝ_left1122
  refine ⟨2 * A, by positivity, fun q χ s hs hj => ?_⟩
  obtain ⟨a, ha1, ha⟩ := gammaFactor_eq_shift χ
  have hz : ∀ j : ℤ, 1 / 2 ≤ ‖s + a + j‖ := by
    intro j; have := hj (a + j); push_cast at this; rwa [add_assoc]
  have hne : Gammaℝ (s + a) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_not_nonpos_int
    intro n h
    have := hz n
    rw [h] at this; push_cast at this; simp at this; norm_num at this
  rw [logDeriv_gammaFactor_eq χ ha hne]
  have hre : (s + a).re ≤ 1 / 2 := by
    simp; have : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
    linarith
  refine (hb _ hre hz).trans ?_
  have hn : ‖s + a‖ ≤ ‖s‖ + 2 := by
    refine (norm_add_le _ _).trans ?_
    have : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
    simp; linarith
  have := log_norm_add_two_le hn
  nlinarith

/-- Davenport ch 19 page 117, the gamma factor of `L(1 - s, χ̄)` with `Re(1 - s) ≥ 3/2`. -/
theorem logDeriv_gammaFactor_right1122 : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q)
    (u : ℂ), 3 / 2 ≤ u.re →
      ‖logDeriv (DirichletCharacter.gammaFactor χ) u‖ ≤ A * Real.log (‖u‖ + 2) := by
  obtain ⟨A, hA, hb⟩ := logDeriv_Gammaℝ_right1122
  refine ⟨2 * A, by positivity, fun q χ u hu => ?_⟩
  obtain ⟨a, ha1, ha⟩ := gammaFactor_eq_shift χ
  have hre : 1 ≤ (u + a).re := by
    simp; have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  have hne : Gammaℝ (u + a) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [logDeriv_gammaFactor_eq χ ha hne]
  refine (hb _ hre).trans ?_
  have hn : ‖u + a‖ ≤ ‖u‖ + 2 := by
    refine (norm_add_le _ _).trans ?_
    have : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
    simp; linarith
  have := log_norm_add_two_le hn
  nlinarith

/-- Davenport ch 16 and ch 19 page 117: `|L'/L(u, χ)| ≤ -ζ'/ζ(3/2)` on `Re u ≥ 3/2`,
uniformly in `χ`, from the Dirichlet series of `L'/L`. -/
theorem logDeriv_L_right1122 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (u : ℂ), 3 / 2 ≤ u.re →
      ‖deriv χ.LFunction u / χ.LFunction u‖ ≤ C := by
  have hsum : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hsumN : Summable fun n =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ :=
    summable_norm_iff.mpr hsum
  refine ⟨∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun q _ χ s hs => ?_⟩
  have hre : 1 < s.re := by linarith
  have hconv : -deriv χ.LFunction s / χ.LFunction s =
      LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hre
    rw [DirichletCharacter.LFunction_eq_LSeries χ hre]
    convert h.symm using 3
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  have hpt : ∀ n, ‖LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ ≤
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (3 / 2 : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · exact le_rfl
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hp : (n : ℝ) ^ (3 / 2 : ℂ).re ≤ (n : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by simpa using hs)
      apply div_le_div₀ (norm_nonneg _) _ (by positivity) hp
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hsum2 : Summable fun n =>
      ‖LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumN
  rw [← norm_neg, ← neg_div, hconv, LSeries]
  exact (norm_tsum_le_tsum_norm hsum2).trans (hsum2.tsum_le_tsum hpt hsumN)

/-- elementary: the gamma factor of `χ` is nonzero at a non-integer. -/
lemma gammaFactor_ne_zero_of_not_int {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h : ∀ n : ℤ, s ≠ n) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  obtain ⟨a, -, ha⟩ := gammaFactor_eq_shift χ
  rw [ha]
  apply Gammaℝ_ne_zero_of_not_nonpos_int
  intro n hn
  exact h (-(n : ℤ) - a) (by push_cast; linear_combination hn)

/-- Davenport ch 19 page 117, the functional equation differentiated logarithmically on the
far left: for primitive `χ`, `Re s < 0` and `s` not an integer, `L(s, χ) ≠ 0` and
`L'/L(s, χ) = -log q - γ'/γ(1 - s, χ̄) - γ'/γ(s, χ) - L'/L(1 - s, χ̄)`.
Port of `Linnik.ExplicitFormula.logDeriv_fe_strip` with `Im s ≠ 0` replaced by `s ∉ ℤ`. -/
theorem logDeriv_fe_far1122 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {s : ℂ} (hre : s.re < 0) (hint : ∀ n : ℤ, s ≠ n) :
    χ.LFunction s ≠ 0 ∧ deriv χ.LFunction s / χ.LFunction s =
      -(Real.log q : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)
        - logDeriv (DirichletCharacter.gammaFactor χ) s
        - deriv (χ⁻¹).LFunction (1 - s) / (χ⁻¹).LFunction (1 - s) := by
  set s0 := s with hs0def
  have hs0ne : s0 ≠ 0 := by simpa using hint 0
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  set A : ℂ → ℂ := fun s => DirichletCharacter.rootNumber χ * (q : ℂ) ^ ((1 - s) - 1 / 2) with hA
  set ref : ℂ → ℂ := fun s => 1 - s with href
  set B : ℂ → ℂ := DirichletCharacter.gammaFactor χ⁻¹ ∘ ref with hB
  set Cc : ℂ → ℂ := (χ⁻¹).LFunction ∘ ref with hCc
  have hev : χ.LFunction =ᶠ[nhds s0] A * B * Cc / DirichletCharacter.gammaFactor χ := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds
      (show s0.re < 1 by linarith), isOpen_ne.mem_nhds hs0ne] with s hs hsne
    have hs : s.re < 1 := hs
    have hsne : s ≠ 0 := hsne
    have hr1 : 0 < (1 - s).re := by simp; linarith
    have h1ne : 1 - s ≠ 0 := by intro e; rw [e] at hr1; simp at hr1
    have hfe := hχ.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at hfe
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hsne), hfe,
      completed_eq_L_mul_gf χ⁻¹ (Or.inl h1ne) (gf_ne_zero_of_re_pos χ⁻¹ hr1)]
    simp only [Pi.mul_apply, Pi.div_apply, hA, hB, hCc, href, Function.comp_apply]
    ring
  have hr1 : 0 < (1 - s0).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hrefd : DifferentiableAt ℂ ref s0 := (differentiableAt_const _).sub differentiableAt_id
  have hderef : deriv ref s0 = -1 := by
    have hd : HasDerivAt ref (-1) s0 := by
      simpa using (hasDerivAt_id s0).const_sub (1 : ℂ)
    exact hd.deriv
  have hgfi := gf_ne_zero_of_re_pos χ⁻¹ hr1
  have hgfid : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ⁻¹) (ref s0) :=
    gf_diff_of_ne χ⁻¹ hgfi
  have hL1 : (1 - s0) ≠ 1 := by intro e; apply hs0ne; linear_combination -e
  have hLi : (χ⁻¹).LFunction (ref s0) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inr hL1)
      (by simp [href]; linarith)
  have hLid : DifferentiableAt ℂ (χ⁻¹).LFunction (ref s0) :=
    DirichletCharacter.differentiableAt_LFunction χ⁻¹ _ (Or.inl hL1)
  have hgf0 := gammaFactor_ne_zero_of_not_int χ hint
  have hgf0d := gf_diff_of_ne χ hgf0
  have hAne : A s0 ≠ 0 := mul_ne_zero (rootNumber_ne_zero' hχ) (cpow_ne_zero_iff.mpr (Or.inl hq0))
  have hAd : HasDerivAt A (DirichletCharacter.rootNumber χ *
      ((q : ℂ) ^ ((1 - s0) - 1 / 2) * Complex.log q * (-1))) s0 := by
    have h1 : HasDerivAt (fun s : ℂ => (1 - s) - 1 / 2) (-1) s0 := by
      simpa using ((hasDerivAt_id s0).const_sub (1 : ℂ)).sub_const (1 / 2 : ℂ)
    exact (h1.const_cpow (Or.inl hq0)).const_mul _
  have hBne : B s0 ≠ 0 := hgfi
  have hCne : Cc s0 ≠ 0 := hLi
  have hBd : DifferentiableAt ℂ B s0 := hgfid.comp s0 hrefd
  have hCd : DifferentiableAt ℂ Cc s0 := hLid.comp s0 hrefd
  have hlogA : logDeriv A s0 = -(Real.log q : ℂ) := by
    rw [logDeriv_apply, hAd.deriv, Complex.natCast_log]
    simp only [hA]
    have hc : (q : ℂ) ^ ((1 - s0) - 1 / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hq0)
    rw [div_eq_iff (mul_ne_zero (rootNumber_ne_zero' hχ) hc)]
    ring
  refine ⟨?_, ?_⟩
  · rw [hev.eq_of_nhds]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hgf0
  rw [← logDeriv_apply, (logDeriv_congr_nhds hev).eq_of_nhds,
    logDeriv_div (f := A * B * Cc) (g := DirichletCharacter.gammaFactor χ) s0
      (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hgf0
      ((hAd.differentiableAt.mul hBd).mul hCd) hgf0d,
    logDeriv_mul (f := A * B) (g := Cc) s0 (mul_ne_zero hAne hBne) hCne
      (hAd.differentiableAt.mul hBd) hCd,
    logDeriv_mul (f := A) (g := B) s0 hAne hBne hAd.differentiableAt hBd, hlogA,
    hB, hCc, logDeriv_comp hgfid hrefd, logDeriv_comp hLid hrefd, hderef]
  simp only [href, logDeriv_apply]
  ring

/-- **Davenport ch 19 pages 116 to 117**: for primitive `χ` mod `q`, in the half plane
`Re s ≤ -1/2` with discs of radius `1/2` around the integers removed, `L(s, χ) ≠ 0` and
`|L'/L(s, χ)| ≤ A log(q(|s| + 2))`, uniformly in `q` and `χ`. Davenport states
`L'/L(s, χ) = O(log(q|s|))` for `σ ≤ -1` off the trivial zeros; it follows from the functional
equation differentiated logarithmically, Stirling for `ψ` and the reflection formula. -/
theorem logDeriv_far_left1122 : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ s : ℂ, s.re ≤ -1 / 2 →
      (∀ j : ℤ, 1 / 2 ≤ ‖s + j‖) →
        χ.LFunction s ≠ 0 ∧
          ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ A * Real.log (q * (‖s‖ + 2)) := by
  obtain ⟨A1, hA1, hl⟩ := logDeriv_gammaFactor_left1122
  obtain ⟨A2, hA2, hr⟩ := logDeriv_gammaFactor_right1122
  obtain ⟨C, hC, hL⟩ := logDeriv_L_right1122
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + 2 * A2 + A1 + C / Real.log 2, by positivity, fun q _ χ hχ s hs hj => ?_⟩
  have hint : ∀ n : ℤ, s ≠ n := by
    intro n h
    have := hj (-n)
    rw [h] at this; push_cast at this; simp at this; norm_num at this
  obtain ⟨hne, hfe⟩ := logDeriv_fe_far1122 hχ (by linarith) hint
  refine ⟨hne, ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set ℓ := Real.log (q * (‖s‖ + 2)) with hℓ
  have hs2 : (2 : ℝ) ≤ ‖s‖ + 2 := by linarith [norm_nonneg s]
  have hlq : Real.log q ≤ ℓ := Real.log_le_log (by linarith) (by nlinarith)
  have hls : Real.log (‖s‖ + 2) ≤ ℓ := Real.log_le_log (by linarith) (by nlinarith)
  have hl2ℓ : Real.log 2 ≤ ℓ := (Real.log_le_log (by norm_num) hs2).trans hls
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hls0 : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith)
  have h1 : ‖(Real.log q : ℂ)‖ ≤ ℓ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlq0]; exact hlq
  have hre1 : 3 / 2 ≤ (1 - s).re := by simp; linarith
  have hn1 : ‖1 - s‖ ≤ ‖s‖ + 2 := by
    refine (norm_sub_le _ _).trans ?_; simp; linarith
  have h2 : ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ ≤ 2 * A2 * ℓ := by
    refine (hr q χ⁻¹ (1 - s) hre1).trans ?_
    have := log_norm_add_two_le hn1
    nlinarith
  have h3 : ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ ≤ A1 * ℓ :=
    (hl q χ s hs hj).trans (mul_le_mul_of_nonneg_left hls hA1)
  have h4 : ‖deriv (χ⁻¹).LFunction (1 - s) / (χ⁻¹).LFunction (1 - s)‖ ≤ C / Real.log 2 * ℓ := by
    refine (hL q χ⁻¹ (1 - s) hre1).trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hl2ℓ hC
  rw [hfe]
  calc _ ≤ ‖(Real.log q : ℂ)‖ + ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ +
        ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ +
        ‖deriv (χ⁻¹).LFunction (1 - s) / (χ⁻¹).LFunction (1 - s)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_sub_le _ _).trans (add_le_add (by rw [norm_neg]) le_rfl)) le_rfl))
          le_rfl)
    _ ≤ ℓ + 2 * A2 * ℓ + A1 * ℓ + C / Real.log 2 * ℓ := by gcongr
    _ = _ := by ring

/-- **The left edge, Davenport ch 19 page 117 with ch 17**: on the line `Re s = -U`,
`U ≥ 1/2` at distance at least `1/2` from the integers, the sharp kernel integral over
`|t| ≤ T` is at most `2T · A log(q(U + T + 2)) x^{-U}/U`, for primitive `χ` and `x ≥ 1`. -/
theorem char_left_edge1122 : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ x U T : ℝ, 1 ≤ x → 1 / 2 ≤ U →
      (∀ j : ℤ, 1 / 2 ≤ |U - j|) → 0 ≤ T →
      ‖∫ t in (-T)..T,
        -(deriv χ.LFunction (((-U : ℝ) : ℂ) + t * I) / χ.LFunction (((-U : ℝ) : ℂ) + t * I)) *
          (x : ℂ) ^ (((-U : ℝ) : ℂ) + t * I) / (((-U : ℝ) : ℂ) + t * I)‖ ≤
        2 * T * (A * Real.log (q * (U + T + 2)) * x ^ (-U) / U) := by
  obtain ⟨A, hA, hb⟩ := logDeriv_far_left1122
  refine ⟨A, hA, fun q _ χ hχ x U T hx hU hUj hT => ?_⟩
  have hx0 : 0 < x := by linarith
  have hU0 : 0 < U := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpt : ∀ t ∈ Set.uIoc (-T) T,
      ‖-(deriv χ.LFunction (((-U : ℝ) : ℂ) + t * I) / χ.LFunction (((-U : ℝ) : ℂ) + t * I)) *
          (x : ℂ) ^ (((-U : ℝ) : ℂ) + t * I) / (((-U : ℝ) : ℂ) + t * I)‖ ≤
        A * Real.log (q * (U + T + 2)) * x ^ (-U) / U := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hta : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
    set s : ℂ := ((-U : ℝ) : ℂ) + t * I with hs
    have hsre : s.re = -U := by simp [hs]
    have hsim : s.im = t := by simp [hs]
    have hj : ∀ j : ℤ, 1 / 2 ≤ ‖s + j‖ := by
      intro j
      have h := Complex.abs_re_le_norm (s + j)
      have e : (s + j).re = -(U - j) := by simp [hs]; ring
      rw [e, abs_neg] at h
      linarith [hUj j]
    obtain ⟨-, hB⟩ := hb q χ hχ s (by rw [hsre]; linarith) hj
    have hsn : ‖s‖ ≤ U + T := by
      have := Complex.norm_le_abs_re_add_abs_im s
      rw [hsre, hsim, abs_neg, abs_of_pos hU0] at this
      linarith
    have hsU : U ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rwa [hsre, abs_neg, abs_of_pos hU0] at this
    have hlog : Real.log (q * (‖s‖ + 2)) ≤ Real.log (q * (U + T + 2)) :=
      Real.log_le_log (by have := norm_nonneg s; positivity) (by gcongr)
    have hl0 : 0 ≤ Real.log (q * (U + T + 2)) :=
      Real.log_nonneg (by nlinarith)
    rw [norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hsre]
    have hnum : ‖deriv χ.LFunction s / χ.LFunction s‖ * x ^ (-U) ≤
        A * Real.log (q * (U + T + 2)) * x ^ (-U) :=
      mul_le_mul_of_nonneg_right (hB.trans (mul_le_mul_of_nonneg_left hlog hA))
        (Real.rpow_nonneg hx0.le _)
    exact div_le_div₀ (by positivity) hnum hU0 hsU
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [show |T - -T| = 2 * T by rw [abs_of_nonneg (by linarith)]; ring] at hh
  calc _ ≤ _ := hh
    _ = _ := by ring

/-- The lines `Re s = -(K + 1/2)` keep distance `1/2` from the integers. -/
lemma half_le_abs_sub_int (K : ℕ) (j : ℤ) : 1 / 2 ≤ |((K : ℝ) + 1 / 2) - j| := by
  have e : ((K : ℝ) + 1 / 2) - j = (((K : ℤ) - j : ℤ) : ℝ) + 1 / 2 := by push_cast; ring
  rw [e]
  rcases le_or_gt 0 ((K : ℤ) - j) with h | h
  · have h' : (0 : ℝ) ≤ (((K : ℤ) - j : ℤ) : ℝ) := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have h1 : (K : ℤ) - j ≤ -1 := by omega
    have h' : (((K : ℤ) - j : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h1
    rw [abs_of_neg (by linarith)]; linarith

/-- **The left edge vanishes in the limit, Davenport ch 19 page 117 with ch 17**: for primitive
`χ`, `x > 1` and fixed `T ≥ 0`, the sharp kernel integral over `Re s = -(K + 1/2)`,
`|t| ≤ T`, tends to `0` as `K → ∞`. -/
theorem char_left_edge_tendsto1122 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {x T : ℝ} (hx : 1 < x) (hT : 0 ≤ T) :
    Tendsto (fun K : ℕ => ∫ t in (-T)..T,
      -(deriv χ.LFunction (((-((K : ℝ) + 1 / 2) : ℝ) : ℂ) + t * I) /
          χ.LFunction (((-((K : ℝ) + 1 / 2) : ℝ) : ℂ) + t * I)) *
        (x : ℂ) ^ (((-((K : ℝ) + 1 / 2) : ℝ) : ℂ) + t * I) /
          (((-((K : ℝ) + 1 / 2) : ℝ) : ℂ) + t * I)) atTop (𝓝 0) := by
  obtain ⟨A, hA, hb⟩ := char_left_edge1122
  have hx0 : 0 < x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  set D : ℝ := 2 * Real.log q + 2 * T + 5 with hD
  have hxi0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  have hxi1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  refine squeeze_zero_norm (a := fun K : ℕ => 2 * T * (A * D * x⁻¹ ^ K)) (fun K => ?_) ?_
  · set U : ℝ := (K : ℝ) + 1 / 2 with hU
    have hU2 : 1 / 2 ≤ U := by rw [hU]; linarith [Nat.cast_nonneg (α := ℝ) K]
    have hU0 : 0 < U := by linarith
    refine (hb q χ hχ x U T hx.le hU2 (half_le_abs_sub_int K) hT).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have hpos : 0 < q * (U + T + 2) := by positivity
    have hlog : Real.log (q * (U + T + 2)) ≤ D * U := by
      rw [Real.log_mul (by positivity) (by linarith)]
      have := Real.log_le_sub_one_of_pos (show 0 < U + T + 2 by linarith)
      nlinarith
    have hl0 : 0 ≤ Real.log (q * (U + T + 2)) := Real.log_nonneg (by nlinarith)
    have hpow : x ^ (-U) ≤ x⁻¹ ^ K := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hx0.le]
      exact Real.rpow_le_rpow_of_exponent_le hx.le (by rw [hU]; linarith)
    have hxU : 0 ≤ x ^ (-U) := Real.rpow_nonneg hx0.le _
    rw [mul_assoc A, mul_assoc A, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hA
    rw [div_le_iff₀ hU0]
    calc Real.log (q * (U + T + 2)) * x ^ (-U) ≤ (D * U) * x⁻¹ ^ K :=
          mul_le_mul hlog hpow hxU (by positivity)
      _ = _ := by ring
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hxi0 hxi1).const_mul (2 * T * (A * D))
    simp only [mul_zero] at h
    convert h using 2 with K
    ring

end LeanLab.PNTPort.ExplicitPsi1.CharEdges1122
