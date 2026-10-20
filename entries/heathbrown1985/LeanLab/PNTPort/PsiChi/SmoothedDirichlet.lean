module

public import LeanLab.PNTPort.StrongPNT.MediumPNT

/-! Adapted from the ported PrimeNumberTheoremAnd file LeanLab/PNTPort/StrongPNT/MediumPNT.lean,
   commit c39a751132c88b6e8080b74c74023fd95b3d8be0, Apache License 2.0, original authors the
   PrimeNumberTheoremAnd project contributors: `SmoothedChebyshevDirichlet` and its two auxiliary
   lemmas. Lab change, unit U-5203, CLOUD 20261019T0514Z-cloud17, AI-written: the von Mangoldt
   coefficients are replaced by any `a : ℕ → ℂ` with `‖a n‖ ≤ Λ n`, and the result is specialized
   to the twist `χ Λ` by a Dirichlet character, where the Dirichlet series is `-L'/L(s, χ)`. -/

@[expose] public section

/-!
# The smoothed sum `∑ a(n) w(n/X)` as a vertical integral, for `‖a n‖ ≤ Λ(n)`

* `smoothedSum_eq`: for `‖a n‖ ≤ Λ(n)`, `X > 3`, `0 < ε < 1` and the smoothing `Smooth1 F ε` of the
  StrongPNT port,
  `(1/2πi) ∫_{(σ)} L(a, s) 𝓜(Smooth1 F ε)(s) X^s ds = ∑ a(n) Smooth1 F ε (n/X)`, `σ = 1 + 1/log X`;
* `smoothedChebyshevChi_eq`: the case `a = χ Λ`, with `L(χΛ, s) = -L'/L(s, χ)`.
Known mathematics, Mellin inversion; no cited input.
-/

set_option lang.lemmaCmd true

open Set Function Filter Complex Real MeasureTheory

open ArithmeticFunction (vonMangoldt)
open scoped LSeries.notation

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

namespace LeanLab.PNTPort.PsiChi

/-- The integrand `L(a, s) 𝓜(Smooth1 F ε)(s) X^s`. -/
noncomputable abbrev SmoothedIntegrand (a : ℕ → ℂ) (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) :
    ℂ → ℂ :=
  fun s ↦ LSeries a s * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s

/-- `(1/2πi) ∫_{(1 + 1/log X)}` of the integrand. -/
noncomputable def SmoothedSum (a : ℕ → ℂ) (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedIntegrand a SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

lemma a_zero {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ Λ n) : a 0 = 0 := by
  have := ha 0
  simp only [ArithmeticFunction.map_zero] at this
  exact norm_le_zero_iff.mp this

lemma LSeries_eq_tsum {a : ℕ → ℂ} (ha0 : a 0 = 0) (s : ℂ) :
    LSeries a s = ∑' n : ℕ, a n / (n : ℂ) ^ s := by
  unfold LSeries
  congr 1; ext n
  rcases n with _ | n
  · simp [ha0]
  · simp [LSeries.term]

lemma summable_norm_div {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ Λ n) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ σ := by
  have hΛ := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
    (by simp only [ofReal_re]; linarith)).norm
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hΛ
  rcases n with _ | n
  · simp [a_zero ha]
  · rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), norm_div,
      norm_natCast_cpow_of_pos (Nat.succ_pos n)]
    simp only [ofReal_re, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact div_le_div_of_nonneg_right (ha _) (by positivity)

set_option backward.isDefEq.respectTransparency false in
lemma smoothedSum_aux_tsum_integral {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ Λ n)
    {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), a n / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), a n / (n : ℂ) ^ (σ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by
  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + ↑a * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
    · refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
        SmoothingFpos mass_one hz).continuousAt
    · fun_prop
    · simp only [mapsTo_univ_iff, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith
  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
    norm_cast
  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : X ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simpa [i_eq_zero, a_zero ha] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp[i_eq_zero, x_neq_zero])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]
    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      convert summable_norm_div ha σ_gt using 2 with n
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

set_option backward.isDefEq.respectTransparency false in
/-- **Mellin identity.** For `‖a n‖ ≤ Λ(n)`:
`(1/2πi) ∫_{(1 + 1/log X)} L(a, s) 𝓜(Smooth1 F ε)(s) X^s ds = ∑ a(n) Smooth1 F ε (n/X)`. -/
theorem smoothedSum_eq {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ Λ n) {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    SmoothedSum a SmoothingF ε X = ∑' n, a n * Smooth1 SmoothingF ε (n / X) := by
  dsimp [SmoothedSum, SmoothedIntegrand, VerticalIntegral', VerticalIntegral]
  set σ : ℝ := 1 + (Real.log X)⁻¹
  have log_gt : 1 < Real.log X := logt_gt_one X_gt.le
  have σ_gt : 1 < σ := by
    simp only [σ]
    have : 0 < (Real.log X)⁻¹ := by
      simp only [inv_pos]
      linarith
    linarith
  have σ_le : σ ≤ 2 := by
    simp only [σ]
    have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt
    linarith
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, a n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), a n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, a n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, a n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, a n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, a n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [LSeries_eq_tsum (a_zero ha)]
    rw [← tsum_mul_right, ← tsum_mul_right]
  · congr
    exact smoothedSum_aux_tsum_integral ha diffSmoothingF SmoothingFpos
      suppSmoothingF mass_one (by linarith) εpos ε_lt_one σ_gt σ_le
  · field_simp; congr; ext n; rw [← MeasureTheory.integral_const_mul]; congr; ext t
    by_cases n_ne_zero : n = 0
    · simp [n_ne_zero, a_zero ha]
    rw [mul_div_assoc, mul_assoc]
    congr
    rw [(div_eq_iff ?_).mpr]
    · have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + I * t) ?_ ?_
      · push_cast at this ⊢
        rw [← this, div_mul_cancel₀]
        · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
      · apply div_nonneg (by linarith : 0 ≤ X); simp
      · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, n_ne_zero, false_and,
        not_false_eq_true]
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    conv => rhs; lhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]
  · congr
    ext n
    by_cases n_zero : n = 0
    · simp [n_zero, a_zero ha]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr
    have := mellinInv_mellin_eq σ (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [mellinInv, VerticalIntegral] at this
      convert! this using 4
      · norm_cast
      · rw [mul_comm]
        norm_cast
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
        SmoothingFpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact Smooth1ContinuousAt diffSmoothingF SmoothingFpos suppSmoothingF
        εpos (by positivity)

section Chi

variable {N : ℕ} [NeZero N]

lemma norm_chi_vonMangoldt_le (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖((↗χ * ↗Λ) n : ℂ)‖ ≤ Λ n := by
  simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)

/-- On `Re s > 1`, `L(χΛ, s) = -L'/L(s, χ)` with `L(s, χ)` Mathlib's `LFunction`. -/
lemma LSeries_chi_vonMangoldt_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗χ * ↗Λ) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  congr 2
  refine (Filter.EventuallyEq.deriv_eq ?_).symm
  have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [ho.mem_nhds hs] with z hz
  exact DirichletCharacter.LFunction_eq_LSeries χ hz

/-- The integrand `-L'/L(s, χ) 𝓜(Smooth1 F ε)(s) X^s`. -/
noncomputable abbrev SmoothedChiIntegrand (χ : DirichletCharacter ℂ N) (SmoothingF : ℝ → ℝ)
    (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s *
    𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s

/-- **The smoothed `ψ(X, χ)` as a vertical integral.** For any Dirichlet character `χ`,
`(1/2πi) ∫_{(1 + 1/log X)} -L'/L(s, χ) 𝓜(Smooth1 F ε)(s) X^s ds = ∑ χ(n) Λ(n) Smooth1 F ε (n/X)`. -/
theorem smoothedChebyshevChi_eq (χ : DirichletCharacter ℂ N) {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    VerticalIntegral' (SmoothedChiIntegrand χ SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹) =
      ∑' n : ℕ, χ (n : ZMod N) * Λ n * Smooth1 SmoothingF ε (n / X) := by
  have h := smoothedSum_eq (norm_chi_vonMangoldt_le χ) diffSmoothingF SmoothingFpos
    suppSmoothingF mass_one X_gt εpos ε_lt_one
  have log_gt : 1 < Real.log X := logt_gt_one X_gt.le
  have hσ : 1 < (1 : ℝ) + (Real.log X)⁻¹ := by
    have : 0 < (Real.log X)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  convert h using 1
  dsimp [SmoothedSum, VerticalIntegral', VerticalIntegral]
  congr 3; ext t
  simp only [SmoothedChiIntegrand, SmoothedIntegrand]
  rw [LSeries_chi_vonMangoldt_eq χ (by simpa using hσ)]

end Chi

end LeanLab.PNTPort.PsiChi
