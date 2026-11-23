module

public import LeanLab.PNTPort.ZetaZeros.Digamma

/-!
# The digamma bound on the strip `-1 ≤ Re s ≤ 2`

Lab proof, unit U-5271, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics, no
cited input.

* `norm_Gamma_le_PL2`: by Phragmén-Lindelöf on `1/2 ≤ Re s ≤ 5/2` with the weight `(s + 1)²`,
  `|Γ(s)| ≤ √(2π) |s + 1|² e^{-π Im s / 2}`.
* `digamma_near_three_half`: `|ψ(w)| ≤ K log(t + 3)` for `t ≥ 1`, `‖w - (3/2 + it)‖ ≤ 2/3`.
* `digamma_strip`: `|ψ(σ + it)| ≤ K log(t + 3) + 2` for `t ≥ 1`, `-1 ≤ σ ≤ 2`, by
  `ψ(s + 1) = ψ(s) + 1/s`, Mathlib's `digamma_apply_add_one`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric MeasureTheory
open scoped Real ComplexConjugate

/-- `‖Γ(s)‖ ≤ Γ(1/2) + Γ(5/2)` for `1/2 ≤ Re s ≤ 5/2`. -/
theorem norm_Gamma_strip_le' {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 5 / 2) :
    ‖Gamma s‖ ≤ Real.Gamma (1 / 2) + Real.Gamma (5 / 2) := by
  rw [Gamma_eq_integral (by linarith), GammaIntegral]
  have hI1 := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)
  have hI3 := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 5 / 2)
  have hint := hI1.add hI3
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [Real.Gamma_eq_integral (by norm_num), Real.Gamma_eq_integral (by norm_num),
    ← integral_add hI1 hI3]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  have he : 0 < Real.exp (-x) := Real.exp_pos _
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
    Real.norm_of_nonneg he.le, ← mul_add]
  simp only [sub_re, one_re]
  gcongr
  rcases le_or_gt x 1 with hx1 | hx1
  · have : x ^ (s.re - 1) ≤ x ^ (1 / 2 - 1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
    have : 0 ≤ x ^ (5 / 2 - 1 : ℝ) := Real.rpow_nonneg hx0.le _
    linarith
  · have : x ^ (s.re - 1) ≤ x ^ (5 / 2 - 1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have : 0 ≤ x ^ (1 / 2 - 1 : ℝ) := Real.rpow_nonneg hx0.le _
    linarith

/-- `g(s) = Γ(s) e^{-iπs/2} / (s + 1)²`. -/
noncomputable def gPL2 (s : ℂ) : ℂ := Gamma s * Complex.exp (-(π * I * s / 2)) / (s + 1) ^ 2

lemma one_le_norm_add_one {s : ℂ} (h : 0 ≤ s.re) : 1 ≤ ‖s + 1‖ := by
  have := Complex.abs_re_le_norm (s + 1); simp at this
  rw [abs_of_nonneg (by linarith)] at this; linarith

lemma norm_gPL2_half (t : ℝ) : ‖gPL2 (1 / 2 + t * I)‖ ≤ √(2 * π) := by
  unfold gPL2
  rw [norm_div, norm_mul, norm_exp_PL, norm_pow]
  have him : ((1 / 2 : ℂ) + t * I).im = t := by simp
  rw [him]
  have hden : 1 ≤ ‖(1 / 2 + t * I : ℂ) + 1‖ ^ 2 := by
    have := one_le_norm_add_one (s := (1 / 2 + t * I : ℂ)) (by simp)
    nlinarith
  rw [div_le_iff₀ (by linarith)]
  have := norm_Gamma_half_mul_exp_le t
  have h0 : 0 ≤ √(2 * π) := Real.sqrt_nonneg _
  nlinarith

lemma norm_gPL2_five_half (t : ℝ) : ‖gPL2 (5 / 2 + t * I)‖ ≤ √(2 * π) := by
  unfold gPL2
  have hne : ∀ u : ℝ, (u : ℂ) + t * I ≠ 0 → True := fun _ _ => trivial
  have hG1 : Gamma (3 / 2 + t * I) = (1 / 2 + t * I) * Gamma (1 / 2 + t * I) := by
    rw [show (3 / 2 + t * I : ℂ) = (1 / 2 + t * I) + 1 by ring]
    exact Gamma_add_one _ (by intro h; have := congr_arg Complex.re h; simp at this)
  have hG2 : Gamma (5 / 2 + t * I) = (3 / 2 + t * I) * Gamma (3 / 2 + t * I) := by
    rw [show (5 / 2 + t * I : ℂ) = (3 / 2 + t * I) + 1 by ring]
    exact Gamma_add_one _ (by intro h; have := congr_arg Complex.re h; simp at this)
  rw [hG2, hG1, norm_div, norm_mul, norm_mul, norm_mul, norm_exp_PL, norm_pow]
  have him : ((5 / 2 : ℂ) + t * I).im = t := by simp
  rw [him]
  have hnum : ‖(3 / 2 + t * I : ℂ)‖ * ‖(1 / 2 + t * I : ℂ)‖ ≤ ‖(5 / 2 + t * I : ℂ) + 1‖ ^ 2 := by
    have e1 : ‖(3 / 2 + t * I : ℂ)‖ ≤ ‖(5 / 2 + t * I : ℂ) + 1‖ := by
      rw [Complex.norm_def, Complex.norm_def]; apply Real.sqrt_le_sqrt
      simp [Complex.normSq_apply]; nlinarith
    have e2 : ‖(1 / 2 + t * I : ℂ)‖ ≤ ‖(5 / 2 + t * I : ℂ) + 1‖ := by
      rw [Complex.norm_def, Complex.norm_def]; apply Real.sqrt_le_sqrt
      simp [Complex.normSq_apply]; nlinarith
    rw [sq]; exact mul_le_mul e1 e2 (norm_nonneg _) (norm_nonneg _)
  have hpos : 0 < ‖(5 / 2 + t * I : ℂ) + 1‖ ^ 2 := by
    have := one_le_norm_add_one (s := (5 / 2 + t * I : ℂ)) (by simp; norm_num)
    positivity
  rw [div_le_iff₀ hpos]
  have := norm_Gamma_half_mul_exp_le t
  have h0 : 0 ≤ ‖Gamma (1 / 2 + t * I)‖ * Real.exp (π * t / 2) := by positivity
  calc ‖(3 / 2 + t * I : ℂ)‖ * (‖(1 / 2 + t * I : ℂ)‖ * ‖Gamma (1 / 2 + t * I)‖) *
        Real.exp (π * t / 2)
      = (‖(3 / 2 + t * I : ℂ)‖ * ‖(1 / 2 + t * I : ℂ)‖) *
          (‖Gamma (1 / 2 + t * I)‖ * Real.exp (π * t / 2)) := by ring
    _ ≤ ‖(5 / 2 + t * I : ℂ) + 1‖ ^ 2 * √(2 * π) := mul_le_mul hnum this h0 (by positivity)
    _ = √(2 * π) * ‖(5 / 2 + t * I : ℂ) + 1‖ ^ 2 := by ring

lemma gPL2_differentiableAt {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ gPL2 z := by
  have hne : ∀ m : ℕ, z ≠ -m := by
    intro m h; rw [h] at hz; simp at hz; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h1 : (z + 1) ^ 2 ≠ 0 := by
    apply pow_ne_zero; intro h; have := congr_arg Complex.re h; simp at this; linarith
  unfold gPL2
  exact ((Complex.differentiableAt_Gamma z hne).mul
    (Complex.differentiableAt_exp.comp z (by fun_prop))).div (by fun_prop) h1

theorem norm_gPL2_le {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 5 / 2) : ‖gPL2 s‖ ≤ √(2 * π) := by
  have hcl : closure (re ⁻¹' Ioo (1 / 2 : ℝ) (5 / 2)) ⊆ {z : ℂ | 0 < z.re} := by
    have hsub : re ⁻¹' Ioo (1 / 2 : ℝ) (5 / 2) ⊆ re ⁻¹' Icc (1 / 2 : ℝ) (5 / 2) :=
      preimage_mono Ioo_subset_Icc_self
    have hcl' := closure_minimal hsub (isClosed_Icc.preimage continuous_re)
    intro z hz
    have := hcl' hz
    simp only [mem_preimage, mem_Icc] at this
    simp only [mem_setOf_eq]; linarith [this.1]
  have hfd : DiffContOnCl ℂ gPL2 (re ⁻¹' Ioo (1 / 2 : ℝ) (5 / 2)) :=
    DifferentiableOn.diffContOnCl
      (fun z hz => (gPL2_differentiableAt (hcl hz)).differentiableWithinAt)
  set K : ℝ := Real.Gamma (1 / 2) + Real.Gamma (5 / 2)
  have hB : ∃ c < π / ((5 / 2 : ℝ) - 1 / 2), ∃ B, gPL2 =O[comap (_root_.abs ∘ im) atTop ⊓
      𝓟 (re ⁻¹' Ioo (1 / 2 : ℝ) (5 / 2))] fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1, by have := Real.pi_gt_three; norm_num; linarith, π / 2, ?_⟩
    refine Asymptotics.IsBigO.of_bound K ?_
    refine Filter.eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)
    simp only [mem_preimage, mem_Ioo] at hz
    unfold gPL2
    rw [norm_div, norm_mul, norm_exp_PL, Real.norm_of_nonneg (Real.exp_pos _).le, norm_pow]
    have hG := norm_Gamma_strip_le' (s := z) hz.1.le hz.2.le
    have hden : 1 ≤ ‖z + 1‖ ^ 2 := by
      have := one_le_norm_add_one (s := z) (by linarith); nlinarith
    have hK : 0 ≤ K := by
      have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 5 / 2)
      positivity
    have hexp : Real.exp (π * z.im / 2) ≤ Real.exp (π / 2 * Real.exp (1 * |z.im|)) := by
      apply Real.exp_le_exp.mpr
      have h1 : z.im ≤ |z.im| := le_abs_self _
      have h2 : |z.im| ≤ Real.exp (1 * |z.im|) := by
        rw [one_mul]; linarith [Real.add_one_le_exp |z.im|]
      have hp := Real.pi_pos
      nlinarith
    rw [div_le_iff₀ (by linarith)]
    calc ‖Gamma z‖ * Real.exp (π * z.im / 2) ≤ K * Real.exp (π / 2 * Real.exp (1 * |z.im|)) :=
          mul_le_mul hG hexp (Real.exp_pos _).le hK
      _ ≤ K * Real.exp (π / 2 * Real.exp (1 * |z.im|)) * ‖z + 1‖ ^ 2 := by
          have : 0 ≤ K * Real.exp (π / 2 * Real.exp (1 * |z.im|)) := by positivity
          nlinarith
  refine PhragmenLindelof.vertical_strip hfd hB (fun z hz => ?_) (fun z hz => ?_) h1 h2
  · have e : z = 1 / 2 + z.im * I := by apply Complex.ext <;> simp [hz]
    rw [e]; exact norm_gPL2_half z.im
  · have e : z = 5 / 2 + z.im * I := by apply Complex.ext <;> simp [hz]
    rw [e]; exact norm_gPL2_five_half z.im

/-- **`|Γ(s)| ≤ √(2π) |s + 1|² e^{-π Im s / 2}`** for `1/2 ≤ Re s ≤ 5/2`. -/
theorem norm_Gamma_le_PL2 {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 5 / 2) :
    ‖Gamma s‖ ≤ √(2 * π) * ‖s + 1‖ ^ 2 * Real.exp (-(π * s.im / 2)) := by
  have h := norm_gPL2_le h1 h2
  have hpos : 0 < ‖s + 1‖ ^ 2 := by
    have := one_le_norm_add_one (s := s) (by linarith); positivity
  unfold gPL2 at h
  rw [norm_div, norm_mul, norm_exp_PL, norm_pow, div_le_iff₀ hpos] at h
  have he := Real.exp_pos (π * s.im / 2)
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ he]
  linarith

/-- `|Γ(3/2 + it)| ≥ (√π / 2) e^{-πt/2}` for `t ≥ 0`. -/
theorem norm_Gamma_three_half_ge {t : ℝ} (ht : 0 ≤ t) :
    √π / 2 * Real.exp (-(π * t / 2)) ≤ ‖Gamma (3 / 2 + t * I)‖ := by
  have hG1 : Gamma (3 / 2 + t * I) = (1 / 2 + t * I) * Gamma (1 / 2 + t * I) := by
    rw [show (3 / 2 + t * I : ℂ) = (1 / 2 + t * I) + 1 by ring]
    exact Gamma_add_one _ (by intro h; have := congr_arg Complex.re h; simp at this)
  have h := normSq_Gamma_half t
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hcle : Real.cosh (π * t) ≤ Real.exp (π * t) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(π * t)) ≤ Real.exp (π * t) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith
  have hlow : π * Real.exp (-(π * t)) ≤ ‖Gamma (1 / 2 + t * I)‖ ^ 2 := by
    rw [h, le_div_iff₀ hc]
    have he : Real.exp (-(π * t)) * Real.exp (π * t) = 1 := by rw [← Real.exp_add]; simp
    calc π * Real.exp (-(π * t)) * Real.cosh (π * t)
        ≤ π * Real.exp (-(π * t)) * Real.exp (π * t) :=
          mul_le_mul_of_nonneg_left hcle (by positivity)
      _ = π := by rw [mul_assoc, he, mul_one]
  have hsq : (√π * Real.exp (-(π * t / 2))) ^ 2 = π * Real.exp (-(π * t)) := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [← hsq] at hlow
  have h12 := le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (norm_nonneg _) hlow
  have hhalf : 1 / 2 ≤ ‖(1 / 2 + t * I : ℂ)‖ := by
    have := Complex.abs_re_le_norm (1 / 2 + t * I : ℂ); simp at this; norm_num at this; linarith
  rw [hG1, norm_mul]
  have : 0 ≤ √π * Real.exp (-(π * t / 2)) := by positivity
  nlinarith

/-- **`|ψ(w)| ≤ K log(t + 3)`** for `t ≥ 1`, `‖w - (3/2 + it)‖ ≤ 2/3`. -/
theorem digamma_near_three_half : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → ∀ w : ℂ,
    ‖w - (3 / 2 + t * I)‖ ≤ 2 / 3 → ‖digamma w‖ ≤ K * Real.log (t + 3) := by
  set K0 : ℝ := 16 * (3 / 4) ^ 2 / (3 / 4 - 2 / 3) ^ 3 +
    1 / (((29 / 30) ^ 2 / (4 / 5) - 4 / 5) * Real.log ((29 / 30) / (4 / 5))) with hK0
  have hl : 0 < Real.log ((29 / 30 : ℝ) / (4 / 5)) := Real.log_pos (by norm_num)
  have hK0p : 0 < K0 := by rw [hK0]; positivity
  refine ⟨5 * K0, by positivity, fun t ht w hw => ?_⟩
  set c : ℂ := 3 / 2 + t * I with hc
  have hcre : 0 < c.re := by simp [hc]
  have hGc := gamma_ne_zero_of_re_pos hcre
  set z : ℂ := w - c with hz
  have hzn : ‖z‖ ≤ 2 / 3 := hw
  have hwz : w = c + z := by rw [hz]; ring
  set f : ℂ → ℂ := fun u => Gamma (c + u) / Gamma c with hf
  have hre : ∀ u : ℂ, ‖u‖ ≤ 1 → 1 / 2 ≤ (c + u).re ∧ (c + u).re ≤ 5 / 2 := by
    intro u hu
    have := Complex.abs_re_le_norm u
    have e : (c + u).re = 3 / 2 + u.re := by simp [hc]
    rw [e]; constructor <;> cases abs_cases u.re <;> linarith
  have gA : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1) := by
    intro u hu
    simp only [Metric.mem_closedBall, dist_zero_right] at hu
    have hA : AnalyticAt ℂ (fun x : ℂ => c + x) u := analyticAt_const.add analyticAt_id
    exact (AnalyticAt.comp (g := Gamma) (f := fun x : ℂ => c + x)
      (gamma_analyticAt (w := c + u) (by linarith [(hre u hu).1])) hA).div_const
  have g0 : f 0 = 1 := by simp only [hf, add_zero]; exact div_self hGc
  have hnz : ∀ u : ℂ, ‖u‖ ≤ 1 → f u ≠ 0 := by
    intro u hu
    exact div_ne_zero (gamma_ne_zero_of_re_pos (by linarith [(hre u hu).1])) hGc
  have hfin : (SetOfZeros 1 f).Finite := by
    apply Set.Finite.subset Set.finite_empty
    intro u hu; exact absurd hu.2 (hnz u hu.1)
  set B : ℝ := 30 * (t + 4) ^ 2 with hB
  have hB1 : 1 < B := by rw [hB]; nlinarith
  have hbound : ∀ u : ℂ, ‖u‖ ≤ 29 / 30 → ‖f u‖ ≤ B := by
    intro u hu
    have hu1 : ‖u‖ ≤ 1 := by linarith
    obtain ⟨hr1, hr2⟩ := hre u hu1
    have hG := norm_Gamma_le_PL2 hr1 hr2
    have hlow := norm_Gamma_three_half_ge (t := t) (by linarith)
    have him : t - 1 ≤ (c + u).im := by
      have := Complex.abs_im_le_norm u
      have e : (c + u).im = t + u.im := by simp [hc]
      rw [e]; cases abs_cases u.im <;> linarith
    have hn1 : ‖(c + u) + 1‖ ≤ t + 4 := by
      calc ‖(c + u) + 1‖ = ‖(5 / 2 : ℂ) + t * I + u‖ := by rw [hc]; ring_nf
        _ ≤ ‖(5 / 2 : ℂ)‖ + ‖(t : ℂ) * I‖ + ‖u‖ := norm_add₃_le
        _ ≤ t + 4 := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by linarith)]
            norm_num; linarith
    have hexp : Real.exp (-(π * (c + u).im / 2)) ≤ Real.exp (-(π * t / 2)) * 7.4 := by
      have h1 : Real.exp (-(π * (c + u).im / 2)) ≤ Real.exp (-(π * t / 2) + 2) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, Real.pi_lt_four]
      have h2 : Real.exp 2 ≤ 7.4 := by
        have := Real.exp_one_lt_d9
        have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [e]; nlinarith [Real.exp_pos 1]
      rw [Real.exp_add] at h1
      calc _ ≤ Real.exp (-(π * t / 2)) * Real.exp 2 := h1
        _ ≤ Real.exp (-(π * t / 2)) * 7.4 := by gcongr
    have hs2 : √(2 * π) ≤ 1.5 * √π := by
      rw [Real.sqrt_mul (by norm_num)]
      have : √(2 : ℝ) ≤ 1.5 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have := Real.sqrt_nonneg π
      nlinarith
    have hE := Real.exp_pos (-(π * t / 2))
    have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
    simp only [hf]
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le (by positivity) hlow)]
    calc ‖Gamma (c + u)‖
        ≤ √(2 * π) * ‖(c + u) + 1‖ ^ 2 * Real.exp (-(π * (c + u).im / 2)) := hG
      _ ≤ (1.5 * √π) * (t + 4) ^ 2 * (Real.exp (-(π * t / 2)) * 7.4) := by gcongr
      _ ≤ B * (√π / 2 * Real.exp (-(π * t / 2))) := by
          rw [hB]; nlinarith [mul_pos hsp hE, sq_nonneg (t + 4)]
      _ ≤ B * ‖Gamma c‖ := by gcongr
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) (2 / 3) \ SetOfZeros (4 / 5) f := by
    refine ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hzn, ?_⟩
    rintro ⟨hz1, hz2⟩; exact hnz z (by linarith) hz2
  have key := FinalBound hB1 (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (2 / 3 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : (3 / 4 : ℝ) < 4 / 5)
    (by norm_num : (4 / 5 : ℝ) < 29 / 30) (by norm_num : (29 / 30 : ℝ) < 1) gA g0 hfin
    hbound hzmem
  have hsum : (∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) hfin).toFinset,
      (analyticOrderNatAt f ρ : ℂ) / (z - ρ)) = 0 := by
    apply Finset.sum_eq_zero
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    exact absurd hρ.2 (hnz ρ (by linarith [hρ.1]))
  rw [hsum, sub_zero] at key
  have hwre : 0 < w.re := by rw [hwz]; linarith [(hre z (by linarith)).1]
  have hGw := gamma_ne_zero_of_re_pos hwre
  have hd : deriv f z = deriv Gamma w / Gamma c := by
    have haff : HasDerivAt (fun u : ℂ => c + u) 1 z := by
      simpa using (hasDerivAt_id z).const_add c
    have hG : HasDerivAt Gamma (deriv Gamma w) (c + z) := by
      rw [← hwz]; exact (gamma_analyticAt hwre).differentiableAt.hasDerivAt
    have h := (hG.comp z haff).div_const (Gamma c)
    simp only [hf]
    rw [show (fun u => Gamma (c + u) / Gamma c) = fun u => (Gamma ∘ fun u : ℂ => c + u) u / Gamma c
      from rfl, h.deriv]
    ring
  have hfz : f z = Gamma w / Gamma c := by simp only [hf]; rw [← hwz]
  have hratio : deriv f z / f z = digamma w := by
    rw [hd, hfz, digamma_def, logDeriv_apply]
    field_simp
  rw [hratio] at key
  have hK0' : 16 * (3 / 4 : ℝ) ^ 2 / (3 / 4 - 2 / 3) ^ 3 +
      1 / (((29 / 30) ^ 2 / (4 / 5) - 4 / 5) * Real.log ((29 / 30) / (4 / 5))) = K0 := by
    rw [hK0]
  rw [hK0'] at key
  have hlogB : Real.log B ≤ 5 * Real.log (t + 3) := by
    calc Real.log B ≤ Real.log ((t + 3) ^ 5) :=
          Real.log_le_log (by rw [hB]; positivity) (by
            rw [hB]
            have h4 : (4 : ℝ) ≤ t + 3 := by linarith
            have : (t + 4) ^ 2 ≤ 2 * (t + 3) ^ 2 := by nlinarith
            have h64 : 64 ≤ (t + 3) ^ 3 := by nlinarith [sq_nonneg (t + 3)]
            nlinarith [sq_nonneg (t + 3), pow_pos (by linarith : (0 : ℝ) < t + 3) 2])
      _ = 5 * Real.log (t + 3) := by rw [Real.log_pow]; norm_num
  calc ‖digamma w‖ ≤ K0 * Real.log B := key
    _ ≤ K0 * (5 * Real.log (t + 3)) := by gcongr
    _ = 5 * K0 * Real.log (t + 3) := by ring

lemma not_neg_nat_of_im {s : ℂ} (h : s.im ≠ 0) : ∀ m : ℕ, s ≠ -m := by
  intro m hm; apply h; rw [hm]; simp

/-- **`|ψ(σ + it)| ≤ K log(t + 3) + 2`** for `t ≥ 1`, `-1 ≤ σ ≤ 2`. -/
theorem digamma_strip : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
    ‖digamma (σ + t * I)‖ ≤ K * Real.log (t + 3) + 2 := by
  obtain ⟨K, hK, hb⟩ := digamma_near_three_half
  refine ⟨K, hK, fun t ht σ h1 h2 => ?_⟩
  have hl : 0 ≤ Real.log (t + 3) := Real.log_nonneg (by linarith)
  have hnear : ∀ u : ℝ, 5 / 6 ≤ u → u ≤ 13 / 6 → ‖digamma (u + t * I)‖ ≤ K * Real.log (t + 3) := by
    intro u hu1 hu2
    apply hb t ht
    have e : (u : ℂ) + t * I - (3 / 2 + t * I) = ((u - 3 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have hinv : ∀ u : ℝ, ‖((u : ℂ) + t * I)⁻¹‖ ≤ 1 := by
    intro u
    rw [norm_inv]
    have : 1 ≤ ‖(u : ℂ) + t * I‖ := by
      have := Complex.abs_im_le_norm ((u : ℂ) + t * I); simp at this
      rw [abs_of_nonneg (by linarith)] at this; linarith
    exact inv_le_one_of_one_le₀ this
  have him : ∀ u : ℝ, ((u : ℂ) + t * I).im ≠ 0 := by intro u; simp; linarith
  have hstep : ∀ u : ℝ, digamma ((u : ℂ) + t * I) =
      digamma (((u + 1 : ℝ) : ℂ) + t * I) - ((u : ℂ) + t * I)⁻¹ := by
    intro u
    have := digamma_apply_add_one ((u : ℂ) + t * I) (not_neg_nat_of_im (him u))
    rw [show ((u : ℂ) + t * I + 1) = ((u + 1 : ℝ) : ℂ) + t * I by push_cast; ring] at this
    rw [this]; ring
  rcases le_or_gt (5 / 6) σ with hσ | hσ
  · have := hnear σ hσ (by linarith); linarith
  rcases le_or_gt (-1 / 6) σ with hσ' | hσ'
  · rw [hstep σ]
    have h1' := hnear (σ + 1) (by linarith) (by linarith)
    have h2' := hinv σ
    calc _ ≤ ‖digamma (((σ + 1 : ℝ) : ℂ) + t * I)‖ + ‖((σ : ℂ) + t * I)⁻¹‖ := norm_sub_le _ _
      _ ≤ K * Real.log (t + 3) + 2 := by linarith
  · rw [hstep σ, hstep (σ + 1)]
    have h1' := hnear (σ + 1 + 1) (by linarith) (by linarith)
    have h2' := hinv σ
    have h3' := hinv (σ + 1)
    calc _ ≤ ‖digamma (((σ + 1 + 1 : ℝ) : ℂ) + t * I) - (((σ + 1 : ℝ) : ℂ) + t * I)⁻¹‖ +
          ‖((σ : ℂ) + t * I)⁻¹‖ := norm_sub_le _ _
      _ ≤ (‖digamma (((σ + 1 + 1 : ℝ) : ℂ) + t * I)‖ + ‖(((σ + 1 : ℝ) : ℂ) + t * I)⁻¹‖) +
          ‖((σ : ℂ) + t * I)⁻¹‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ K * Real.log (t + 3) + 2 := by linarith

end LeanLab.PNTPort.ZetaZeros

