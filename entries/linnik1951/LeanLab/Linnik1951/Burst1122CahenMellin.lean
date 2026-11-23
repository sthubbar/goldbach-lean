module

public import LeanLab.Linnik1951.SPLIT_grh_mellin_transfer519
public import LeanLab.Linnik1951.Mellin473

/-!
P0093 Ju. V. Linnik 1951, Mat. Sbornik 28, pages 156 and 159, equations 4.1 and 5.1.
Proves the Cahen Mellin identity on the line re s = 2 for the character prime power series.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

open MeasureTheory Set Filter Complex Metric

namespace LeanLab.Linnik1951.Task519

/-- Textbook Euler integral with complex rate, used at P0093 page 156: the Laplace
integrand of the Gamma function is continuous on the positive half line. -/
lemma laplace_continuousOn_b1122x (s z : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-z * t)) (Ioi 0) := by
  apply ContinuousOn.mul
  · exact Complex.continuous_ofReal.continuousOn.cpow_const
      (fun t ht => Complex.ofReal_mem_slitPlane.mpr ht)
  · fun_prop

/-- Textbook Euler integral with complex rate, used at P0093 page 156: the Laplace
integrand is integrable on the positive half line when re s and re z are positive. -/
lemma laplace_integrable_b1122x {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-z * t)) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * Real.exp (-z.re * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := s.re - 1) (b := z.re) (by linarith) (by norm_num) hz
  refine Integrable.mono' hb ((laplace_continuousOn_b1122x s z).aestronglyMeasurable
    measurableSet_Ioi) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp

/-- Textbook Euler integral with complex rate, used at P0093 page 156: the Laplace
transform of t to the s minus 1 is complex differentiable in the rate z on re z > 0,
by differentiation under the integral sign. -/
lemma laplace_differentiable_b1122x {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-w * t)) z := by
  let F : ℂ → ℝ → ℂ := fun w t => (t : ℂ) ^ (s - 1) * Complex.exp (-w * t)
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (t : ℂ) ^ (s - 1) * (Complex.exp (-w * t) * (-t))
  let r : ℝ := z.re / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hm : ∀ w : ℂ, AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) :=
    fun w => (laplace_continuousOn_b1122x s w).aestronglyMeasurable measurableSet_Ioi
  have hm' : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    dsimp [F']
    simp only [← mul_assoc]
    exact (laplace_continuousOn_b1122x s z).mul
      (show ContinuousOn (fun t : ℝ => -(t : ℂ)) (Ioi 0) by fun_prop)
  have hb : IntegrableOn (fun t : ℝ => t ^ s.re * Real.exp (-r * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := s.re) (b := r) (by linarith) (by norm_num) hr
  have hd : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ w ∈ ball z r,
      HasDerivAt (fun w => F w t) (F' w t) w := by
    apply Eventually.of_forall
    intro t w _
    dsimp [F, F']
    simpa using (((hasDerivAt_id w).neg.mul_const (t : ℂ)).cexp).const_mul
      ((t : ℂ) ^ (s - 1))
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ w ∈ ball z r,
      ‖F' w t‖ ≤ t ^ s.re * Real.exp (-r * t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    intro w hw
    have hw' : r ≤ w.re := by
      have hn : ‖w - z‖ < r := by simpa [dist_eq_norm] using hw
      have hre := Complex.abs_re_le_norm (w - z)
      have hre' := (abs_le.mp (le_trans hre hn.le)).1
      simp only [sub_re] at hre'
      dsimp [r] at *
      linarith
    dsimp [F']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    have he : (-w * (t : ℂ)).re = -w.re * t := by simp
    rw [he]
    have hp : t ^ (s.re - 1) * t = t ^ s.re := by
      conv_lhs => arg 2; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      ring
    calc _ = (t ^ (s.re - 1) * t) * Real.exp (-w.re * t) := by simp; ring
      _ = t ^ s.re * Real.exp (-w.re * t) := by rw [hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hw') ht.le))
        (Real.rpow_nonneg ht.le _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := ball z r) (μ := volume.restrict (Ioi 0))
    (ball_mem_nhds z hr) (Eventually.of_forall hm)
    (laplace_integrable_b1122x hs hz) hm' hbound hb hd
  exact h.2.differentiableAt

/-- Textbook Euler integral with complex rate, Whittaker and Watson 12.2, used at
P0093 page 156: for re s > 0 and re z > 0 the Laplace integral of t to the s minus 1
equals z to the minus s times Gamma s. Proved by the identity theorem in z from
the real rate case in Mathlib. -/
theorem laplace_eq_b1122x {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-z * t)) =
      z ^ (-s) * Complex.Gamma s := by
  set L : ℂ → ℂ := fun w => ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-w * t)
    with hLdef
  change L z = _
  have hReal : ∀ r : ℝ, 0 < r → L (r : ℂ) = (r : ℂ) ^ (-s) * Complex.Gamma s := by
    intro r hr
    have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
    simpa only [hLdef, one_div, Complex.inv_cpow_ofReal_nonneg hr.le,
      Complex.cpow_neg, Complex.ofReal_neg, Complex.ofReal_mul, neg_mul] using h
  have hL : AnalyticOnNhd ℂ L {w : ℂ | 0 < w.re} :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (laplace_differentiable_b1122x hs hw).differentiableWithinAt)
      (isOpen_lt continuous_const Complex.continuous_re)
  have hR : AnalyticOnNhd ℂ (fun w : ℂ => w ^ (-s) * Complex.Gamma s)
      {w : ℂ | 0 < w.re} := by
    apply DifferentiableOn.analyticOnNhd _
      (isOpen_lt continuous_const Complex.continuous_re)
    intro w hw
    have hp : DifferentiableAt ℂ (fun u : ℂ => u ^ (-s)) w :=
      differentiableAt_id.cpow_const (Complex.mem_slitPlane_iff.mpr (Or.inl hw))
    exact (hp.mul_const _).differentiableWithinAt
  have hc : (1 : ℂ) ∈ closure
      ({w : ℂ | L w = w ^ (-s) * Complex.Gamma s} \ {1}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let d : ℝ := min (ε / 2) 1
    have hd : 0 < d := lt_min (by linarith) (by norm_num)
    refine ⟨((1 + d : ℝ) : ℂ), ?_, ?_⟩
    · constructor
      · exact hReal _ (by linarith)
      · simp only [mem_singleton_iff]
        intro h
        have h' := congr_arg Complex.re h
        simp only [Complex.ofReal_re, Complex.one_re] at h'
        linarith
    · rw [dist_eq_norm]
      have he : ((1 + d : ℝ) : ℂ) - 1 = (d : ℂ) := by push_cast; ring
      rw [norm_sub_rev, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have he := hL.eqOn_of_preconnected_of_mem_closure hR
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := (1 : ℂ)) (by simp) hc
  exact he hz

/-- P0093 page 157 Gamma decay on the line re s = 2: by Gamma of s plus one equal to
s Gamma s and the strip bound at re s = 1, Gamma of 2 + it is at most
2 sqrt 2 pi times one plus |t| cubed times e to the minus pi |t| / 2. -/
lemma gamma_two_line_bound_b1122x (t : ℝ) :
    ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * Real.sqrt (2 * Real.pi) * ((1 + |t|) ^ 3 * Real.exp (-(Real.pi * |t| / 2))) := by
  set s1 : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I with hs1
  have hs1ne : s1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hs1] at this
  have he : (2 : ℂ) + (t : ℂ) * Complex.I = s1 + 1 := by rw [hs1]; ring
  rw [he, Complex.Gamma_add_one s1 hs1ne, norm_mul]
  have hre : s1.re = 1 := by simp [hs1]
  have him : s1.im = t := by simp [hs1]
  have hg := LeanLab.Linnik1951.gamma_absolute_decay442 s1 (by rw [hre]; norm_num)
    (by rw [hre]; norm_num)
  rw [him] at hg
  have hn1 : ‖s1‖ ≤ 1 + |t| := by
    calc ‖s1‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 + |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          norm_one]
  have hn2 : ‖s1 + 1‖ ≤ 2 + |t| := by
    have he2 : s1 + 1 = (2 : ℂ) + (t : ℂ) * Complex.I := by rw [hs1]; ring
    rw [he2]
    calc ‖(2 : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
          norm_add_le _ _
      _ = 2 + |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        norm_num
  have hE : 0 ≤ Real.exp (-(Real.pi * |t| / 2)) := (Real.exp_pos _).le
  have hS : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have ht : 0 ≤ |t| := abs_nonneg t
  have hpoly : (1 + |t|) * (2 + |t|) ≤ 2 * (1 + |t|) ^ 3 := by
    nlinarith [sq_nonneg |t|, pow_nonneg ht 3]
  calc ‖s1‖ * ‖Complex.Gamma s1‖
      ≤ (1 + |t|) * (Real.sqrt (2 * Real.pi) * (2 + |t|) *
          Real.exp (-(Real.pi * |t| / 2))) := by
        apply mul_le_mul hn1 (hg.trans ?_) (norm_nonneg _) (by positivity)
        gcongr
    _ = Real.sqrt (2 * Real.pi) * ((1 + |t|) * (2 + |t|)) *
          Real.exp (-(Real.pi * |t| / 2)) := by ring
    _ ≤ Real.sqrt (2 * Real.pi) * (2 * (1 + |t|) ^ 3) *
          Real.exp (-(Real.pi * |t| / 2)) := by gcongr
    _ = _ := by ring

/-- P0093 page 156 kernel on the line re s = 2: for re z > 0 the function
t to z to the minus 2 + it times Gamma of 2 + it is continuous. -/
lemma kernel_two_continuous_b1122x {z : ℂ} (hz : 0 < z.re) :
    Continuous (fun t : ℝ => z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  apply Continuous.mul
  · exact Continuous.const_cpow (by fun_prop) (Or.inl hz0)
  · apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · fun_prop
    intro n he
    have hre := congrArg Complex.re he
    simp at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- P0093 page 156 kernel on the line re s = 2: for re z > 0, so that |arg z| is
less than pi / 2, the Mellin kernel z to the minus s times Gamma s is integrable
along re s = 2, by the Gamma decay e to the minus pi |t| / 2 against the growth
e to the |arg z| |t| of z to the minus s. -/
lemma kernel_two_integrable_b1122x {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun t : ℝ => z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have harg : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  set δ : ℝ := Real.pi / 2 - |Complex.arg z| with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set C : ℝ := ‖z‖ ^ (-2 : ℝ) * (2 * Real.sqrt (2 * Real.pi)) with hC
  refine ((LeanLab.Linnik1951.exp_decay_cubic_integrable473 δ hδ).const_mul C).mono'
    (kernel_two_continuous_b1122x hz).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hcp : ‖z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      ‖z‖ ^ (-2 : ℝ) * Real.exp (|Complex.arg z| * |t|) := by
    rw [Complex.norm_cpow_of_ne_zero hz0]
    have hre : (-((2 : ℂ) + (t : ℂ) * Complex.I)).re = -2 := by simp
    have him : (-((2 : ℂ) + (t : ℂ) * Complex.I)).im = -t := by simp
    rw [hre, him, div_eq_mul_inv, ← Real.exp_neg]
    gcongr
    have h1 : -(Complex.arg z * -t) = Complex.arg z * t := by ring
    rw [h1, ← abs_mul]
    exact le_abs_self _
  have hg := gamma_two_line_bound_b1122x t
  rw [norm_mul]
  calc ‖z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))‖ *
        ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (‖z‖ ^ (-2 : ℝ) * Real.exp (|Complex.arg z| * |t|)) *
        (2 * Real.sqrt (2 * Real.pi) *
          ((1 + |t|) ^ 3 * Real.exp (-(Real.pi * |t| / 2)))) :=
        mul_le_mul hcp hg (norm_nonneg _) (by positivity)
    _ = C * (Real.exp (-(δ * |t|)) * (1 + |t|) ^ 3) := by
        rw [hC, hδdef]
        have hx : Real.exp (|Complex.arg z| * |t|) * Real.exp (-(Real.pi * |t| / 2)) =
            Real.exp (-((Real.pi / 2 - |Complex.arg z|) * |t|)) := by
          rw [← Real.exp_add]; congr 1; ring
        calc _ = ‖z‖ ^ (-2 : ℝ) * (2 * Real.sqrt (2 * Real.pi)) *
              ((Real.exp (|Complex.arg z| * |t|) * Real.exp (-(Real.pi * |t| / 2))) *
                (1 + |t|) ^ 3) := by ring
          _ = _ := by rw [hx]

/-- P0093 page 159 equation 5.1, Cahen Mellin inversion for one frequency on the
line re s = 2: for re z > 0 and x > 0, one over 2 pi times the integral of
x to the minus s times z to the minus s times Gamma s is e to the minus z x. -/
theorem cahen_single_b1122x {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
        (z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)) =
      Complex.exp (-z * x) := by
  let f : ℝ → ℂ := fun y => Complex.exp (-z * y)
  have hm : ∀ s : ℂ, 0 < s.re → mellin f s = z ^ (-s) * Complex.Gamma s := by
    intro s hs
    simpa only [mellin, f, smul_eq_mul] using laplace_eq_b1122x hs hz
  have h2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hline : ∀ t : ℝ, mellin f (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
        Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [h2]
    exact hm _ (by simp)
  have hc : MellinConvergent f ((2 : ℝ) : ℂ) := by
    simpa only [MellinConvergent, f, smul_eq_mul] using
      laplace_integrable_b1122x (s := ((2 : ℝ) : ℂ)) (by simp) hz
  have hv : Complex.VerticalIntegrable (mellin f) 2 := by
    unfold Complex.VerticalIntegrable
    simp only [hline]
    exact kernel_two_integrable_b1122x hz
  have h := mellinInv_mellin_eq 2 f hx hc hv (by dsimp [f]; fun_prop)
  unfold mellinInv at h
  simp only [hline, smul_eq_mul, Complex.real_smul] at h
  simpa only [h2, f] using h

/-- P0093 page 159 before equation 5.1: the k + 1 st power term of the
logarithmic Euler series is one over k + 1 times chi of p to the k + 1
times the power p to the k + 1 raised to minus s. -/
lemma euler_term_eq_b1122x {q : ℕ} (χ : DirichletCharacter ℂ q) (p k : ℕ) (s : ℂ) :
    (χ p * (p : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1) =
      ((k : ℂ) + 1)⁻¹ * χ (p ^ (k + 1)) * ((((p : ℝ) ^ (k + 1) : ℝ)) : ℂ) ^ (-s) := by
  have h1 : ((p : ℂ) ^ (-s)) ^ (k + 1) = ((((p : ℝ) ^ (k + 1) : ℝ)) : ℂ) ^ (-s) := by
    rw [← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]
    push_cast
    rfl
  rw [mul_pow, h1, map_pow, div_eq_mul_inv]
  ring

/-- P0093 page 159 before equation 5.1: on re s = 2 each Euler term has norm at most
p to the minus 2 times 2 to the minus k. -/
lemma euler_term_norm_b1122x {q : ℕ} (χ : DirichletCharacter ℂ q) (p : Nat.Primes) (k : ℕ)
    (t : ℝ) :
    ‖(χ (p : ℕ) * (((p : ℕ) : ℂ)) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) ^ (k + 1) /
        ((k : ℂ) + 1)‖ ≤ (((p : ℕ) : ℝ) ^ 2)⁻¹ * (1 / 2 : ℝ) ^ k := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hp0 : 0 < (p : ℕ) := p.2.pos
  set r : ℝ := (((p : ℕ) : ℝ) ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 / 2 := by
    rw [hr]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hbase : ‖χ (p : ℕ) * (((p : ℕ) : ℂ)) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))‖ ≤ r := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp0]
    have hre : (-((2 : ℂ) + (t : ℂ) * Complex.I)).re = -2 := by simp
    rw [hre]
    have hrp : ((p : ℕ) : ℝ) ^ (-2 : ℝ) = r := by
      rw [hr, Real.rpow_neg (by positivity)]
      norm_cast
    rw [hrp]
    calc ‖χ (p : ℕ)‖ * r ≤ 1 * r :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) hr0
      _ = r := one_mul r
  have hk : (1 : ℝ) ≤ ‖((k : ℂ) + 1)‖ := by
    have : ((k : ℂ) + 1) = (((k + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    exact this
  rw [norm_div, norm_pow]
  calc ‖χ (p : ℕ) * (((p : ℕ) : ℂ)) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))‖ ^ (k + 1) /
        ‖((k : ℂ) + 1)‖
      ≤ ‖χ (p : ℕ) * (((p : ℕ) : ℂ)) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))‖ ^ (k + 1) :=
        div_le_self (by positivity) hk
    _ ≤ r ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg _) hbase _
    _ = r * r ^ k := by ring
    _ ≤ r * (1 / 2 : ℝ) ^ k := by
        gcongr

/-- P0093 page 159 before equation 5.1: the sum over primes of p to the minus 2
converges. -/
lemma summable_prime_inv_sq_b1122x :
    Summable (fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  exact h.comp_injective Subtype.val_injective

/-- P0093 page 156 display after equation 4.1 and page 159 before equation 5.1:
on re s = 2 the Mellin integral of z to the minus s times Gamma s times G s, with G
the logarithmic Euler series of L of s and chi, is the damped prime power series
with exponential phases. -/
theorem cahen_mellin_line_two_proof_b1122 (N : ℕ) (hN : 1 ≤ N) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (G : ℂ → ℂ)
    (hGs : ∀ s : ℂ, 1 < s.re → G s = ∑' p : Nat.Primes, ∑' k : ℕ,
      (χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)) (α : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-((2 : ℂ) + (t : ℂ) * Complex.I)) * Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) *
          G ((2 : ℂ) + (t : ℂ) * Complex.I)
      = ∑' p : Nat.Primes, ∑' k : ℕ,
          (((k : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (k + 1)) *
            (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) : ℂ) *
              Complex.exp
                ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 1))) : ℝ) * Complex.I)) := by
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hzdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hz : 0 < z.re := by
    rw [hzdef]; simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; simp [hNpos]
  set K : ℝ → ℂ := fun t => z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) with hKdef
  have hK : Integrable K := kernel_two_integrable_b1122x hz
  have hKc : Continuous K := kernel_two_continuous_b1122x hz
  set T : Nat.Primes → ℕ → ℝ → ℂ := fun p k t =>
    (χ (p : ℕ) * (((p : ℕ) : ℂ)) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I))) ^ (k + 1) /
      ((k : ℂ) + 1) with hTdef
  set u : Nat.Primes → ℕ → ℝ := fun p k => (((p : ℕ) : ℝ) ^ 2)⁻¹ * (1 / 2 : ℝ) ^ k with hudef
  have hTb : ∀ p k t, ‖T p k t‖ ≤ u p k := fun p k t => euler_term_norm_b1122x χ p k t
  have hu : ∀ p, Summable (u p) := fun p => summable_geometric_two.mul_left _
  have hu0 : ∀ p k, 0 ≤ u p k := fun p k => by rw [hudef]; positivity
  have hus : ∀ p, ∑' k, u p k = 2 * (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro p; rw [hudef]; simp only; rw [tsum_mul_left, tsum_geometric_two]; ring
  have hTc : ∀ p k, Continuous (T p k) := by
    intro p k
    rw [hTdef]
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    apply Continuous.div_const
    apply Continuous.pow
    apply Continuous.mul continuous_const
    exact Continuous.const_cpow (by fun_prop) (Or.inl hp0)
  set H : Nat.Primes → ℝ → ℂ := fun p t => ∑' k, T p k t with hHdef
  have hHc : ∀ p, Continuous (H p) := fun p => continuous_tsum (hTc p) (hu p) (hTb p)
  have hHb : ∀ p t, ‖H p t‖ ≤ 2 * (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro p t
    rw [← hus p]
    exact tsum_of_norm_bounded (hu p).hasSum (fun k => hTb p k t)
  set IK : ℝ := ∫ t, ‖K t‖ with hIK
  -- inner interchange for fixed p
  have hFint : ∀ p k, Integrable (fun t => K t * T p k t) := by
    intro p k
    refine (hK.norm.mul_const (u p k)).mono' (hKc.mul (hTc p k)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hTb p k t) (norm_nonneg _)
  have hFnorm : ∀ p k, ∫ t, ‖K t * T p k t‖ ≤ IK * u p k := by
    intro p k
    rw [hIK, ← integral_mul_const]
    apply integral_mono (hFint p k).norm (hK.norm.mul_const _)
    intro t
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (hTb p k t) (norm_nonneg _)
  have hIK0 : 0 ≤ IK := integral_nonneg fun t => norm_nonneg _
  have hinner : ∀ p, ∑' k, (∫ t, K t * T p k t) = ∫ t, K t * H p t := by
    intro p
    have hs : Summable fun k => ∫ t, ‖K t * T p k t‖ :=
      Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
        (hFnorm p) ((hu p).mul_left IK)
    rw [integral_tsum_of_summable_integral_norm (hFint p) hs]
    congr 1
    funext t
    rw [hHdef]
    exact tsum_mul_left
  -- outer interchange
  have hGint : ∀ p, Integrable (fun t => K t * H p t) := by
    intro p
    refine (hK.norm.mul_const (2 * (((p : ℕ) : ℝ) ^ 2)⁻¹)).mono'
      (hKc.mul (hHc p)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hHb p t) (norm_nonneg _)
  have hGsum : Summable fun p => ∫ t, ‖K t * H p t‖ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
      (fun p => ?_) ((summable_prime_inv_sq_b1122x.mul_left 2).mul_left IK)
    rw [hIK, ← integral_mul_const]
    apply integral_mono (hGint p).norm (hK.norm.mul_const _)
    intro t
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (hHb p t) (norm_nonneg _)
  have houter : ∑' p, (∫ t, K t * H p t) = ∫ t, ∑' p, K t * H p t :=
    integral_tsum_of_summable_integral_norm hGint hGsum
  -- rewrite the left side
  have hlhs : (fun t : ℝ => z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
      Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I) * G ((2 : ℂ) + (t : ℂ) * Complex.I)) =
      fun t => ∑' p, K t * H p t := by
    funext t
    rw [hGs _ (by simp), tsum_mul_left]
  rw [hlhs, ← houter, ← tsum_mul_left]
  congr 1
  funext p
  rw [← hinner p, ← tsum_mul_left]
  congr 1
  funext k
  -- one term
  have hn : 0 < ((p : ℕ) : ℝ) ^ (k + 1) := by
    have : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    positivity
  have hterm : (fun t => K t * T p k t) = fun t : ℝ =>
      (((k : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (k + 1))) *
        ((((((p : ℕ) : ℝ) ^ (k + 1) : ℝ)) : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
          (z ^ (-((2 : ℂ) + (t : ℂ) * Complex.I)) *
            Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I))) := by
    funext t
    rw [hTdef, hKdef]
    simp only
    rw [euler_term_eq_b1122x χ (p : ℕ) k]
    ring
  have hexp : Complex.exp (-z * ((((p : ℕ) : ℝ) ^ (k + 1) : ℝ) : ℂ)) =
      (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 1) / (N : ℝ))) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 1))) : ℝ) * Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [hzdef]
    push_cast
    ring
  rw [hterm, integral_const_mul, mul_left_comm, cahen_single_b1122x hz hn, hexp]
  ring

end LeanLab.Linnik1951.Task519
