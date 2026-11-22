module

public import LeanLab.KadiriLumley2014.ZeroDefinitions259
public import LeanLab.KadiriLumley2014.SmoothedFormula259
public import LeanLab.KadiriLumley2014.TableRounding
public import LeanLab.KadiriLumley2014.TableCertificates259
public import LeanLab.KadiriLumley2014.BindingRow
public import LeanLab.KadiriLumley2014.OmegaIntegral
public import LeanLab.KadiriLumley2014.WeightTail
public import LeanLab.KadiriLumley2014.CostaSplit
public import LeanLab.KadiriLumley2014.BrunTitchmarshMV

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1, pages 2 and 3, equations 2.4 to 2.8.
The central smoothing interval keeps both prime interval endpoints strict.
AI wrote this Lean code, Codex by OpenAI, 2026-10-26.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- Page 2 before Section 2.1. Theta is constant across a prime-free interval. -/
theorem theta_eq_of_no_prime {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z)
    (h : ∀ p : ℕ, p.Prime → ¬ (y < p ∧ (p : ℝ) ≤ z)) :
    Chebyshev.theta z = Chebyshev.theta y := by
  classical
  unfold Chebyshev.theta
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp0, hpz⟩, hp⟩
    have hpz' : (p : ℝ) ≤ z := (Nat.le_floor_iff (hy.trans hyz)).mp hpz
    have hpy : (p : ℝ) ≤ y := le_of_not_gt (fun hpy => h p hp ⟨hpy, hpz'⟩)
    exact ⟨⟨hp0, (Nat.le_floor_iff hy).mpr hpy⟩, hp⟩
  · rintro ⟨⟨hp0, hpy⟩, hp⟩
    exact ⟨⟨hp0, hpy.trans (Nat.floor_mono hyz)⟩, hp⟩

/-- Page 2 equation 2.5. A positive central weighted difference forces a prime
strictly inside the enclosing interval. No analytic estimate is assumed here. -/
theorem prime_of_central_integral {a b y x : ℝ} {L U w : ℝ → ℝ}
    (hab : a ≤ b)
    (hgeom : ∀ t ∈ Ioo a b, 0 ≤ L t ∧ y ≤ L t ∧ L t ≤ U t ∧ U t < x)
    (hpos : 0 < ∫ t in a..b, (Chebyshev.theta (U t) - Chebyshev.theta (L t)) * w t) :
    ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) < x := by
  by_contra! hnone
  have hz : (∫ t in a..b, (Chebyshev.theta (U t) - Chebyshev.theta (L t)) * w t) = 0 := by
    calc
      _ = ∫ _t in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab
        intro t ht
        obtain ⟨hL, hyL, hLU, hUx⟩ := hgeom t ht
        have heq := theta_eq_of_no_prime hL hLU (fun p hp hmem =>
          (not_lt_of_ge (hnone p hp (hyL.trans_lt hmem.1))) (hmem.2.trans_lt hUx))
        simp only [heq, sub_self, zero_mul]
      _ = 0 := by simp
  linarith


/-- The unnormalized central theta difference from page 2 equation 2.5. -/
noncomputable def centralThetaIntegral (m : ℕ) (δ u X a : ℝ) : ℝ :=
  ∫ t in a..(1 - a),
    (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t))) * weight m t

/-- Page 2 equations 2.1 and 2.5. The central interval lies strictly
below the upper endpoint. Positive delta is essential to this strictness. -/
theorem smoothing_geometry {δ u X a t : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u)
    (hX : 0 < X) (ha : 0 ≤ a) (ht : t ∈ Ioo a (1 - a)) :
    0 ≤ X * (1 + δ * t) ∧
    X * (1 + δ * a) ≤ X * (1 + δ * t) ∧
    X * (1 + δ * t) ≤ Real.exp u * (X * (1 + δ * t)) ∧
    Real.exp u * (X * (1 + δ * t)) < Real.exp u * (X * (1 + δ * (1 - a))) := by
  have ht0 : 0 ≤ t := ha.trans ht.1.le
  have hL : 0 ≤ X * (1 + δ * t) := by positivity
  have he : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  refine ⟨hL, ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left (by nlinarith [ht.1]) hX.le
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right he hL
  · apply mul_lt_mul_of_pos_left _ (Real.exp_pos u)
    apply mul_lt_mul_of_pos_left _ hX
    nlinarith [ht.2]

/-- Page 2 equation 2.5. Central positivity yields a prime between
the parameter endpoints with both inequalities strict. -/
theorem prime_of_smoothing {m : ℕ} {δ u X a : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u)
    (hX : 0 < X) (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hpos : 0 < centralThetaIntegral m δ u X a) :
    ∃ p : ℕ, p.Prime ∧ X * (1 + δ * a) < p ∧
      (p : ℝ) < Real.exp u * (X * (1 + δ * (1 - a))) := by
  exact prime_of_central_integral (by linarith)
    (fun t ht => smoothing_geometry hδ hu hX ha ht) hpos

/-- Page 2 equation 2.1. The denominator formula gives exactly
the lower parameter endpoint. -/
theorem lower_endpoint_identity {δ u X a D : ℝ}
    (hB : 1 + δ * (1 - a) ≠ 0)
    (hD : D = 1 / intervalFraction δ u a) :
    (1 - 1 / D) * (Real.exp u * (X * (1 + δ * (1 - a)))) = X * (1 + δ * a) := by
  rw [hD, one_div_one_div]
  unfold intervalFraction
  rw [Real.exp_neg]
  field_simp [hB, Real.exp_ne_zero]
  ring


/-- The two endpoint theta integrals subtracted in page 3 equations 2.6 and 2.7. -/
noncomputable def tailThetaIntegral (m : ℕ) (δ u X a : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..a,
    (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t))) * weight m t) +
  (∫ t in (1 - a)..1,
    (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t))) * weight m t)

/-- Page 3 equation 2.7. The central integral is the total weighted
average times its mass minus the two endpoint integrals. -/
theorem central_integral_split (m : ℕ) {δ u X a : ℝ}
    (hδ : 0 ≤ δ) (hX : 0 ≤ X) (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    centralThetaIntegral m δ u X a =
      thetaAverage m δ u X * (∫ t in (0 : ℝ)..1, weight m t) -
        tailThetaIntegral m δ u X a := by
  let F := fun t => (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
      Chebyshev.theta (X * (1 + δ * t))) * weight m t
  have hi : IntervalIntegrable F volume 0 1 :=
    weighted_difference_integrable Chebyshev.theta_mono m hδ (Real.exp_nonneg u) hX
  have ha1 : a ≤ 1 := by linarith
  have hmid : a ≤ 1 - a := by linarith
  have h1a : 0 ≤ 1 - a := by linarith
  have h1a1 : 1 - a ≤ 1 := by linarith
  have hi0a : IntervalIntegrable F volume 0 a := hi.mono_set (by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le ha] using
      Icc_subset_Icc le_rfl ha1)
  have hia1a : IntervalIntegrable F volume a (1 - a) := hi.mono_set (by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le hmid] using
      Icc_subset_Icc ha h1a1)
  have hi1a1 : IntervalIntegrable F volume (1 - a) 1 := hi.mono_set (by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le h1a1] using
      Icc_subset_Icc h1a le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi0a hia1a
  have hadd' := intervalIntegral.integral_add_adjacent_intervals (hi0a.trans hia1a) hi1a1
  have hmass := (weight_mass_pos m).ne'
  unfold centralThetaIntegral tailThetaIntegral thetaAverage
  rw [div_mul_cancel₀ _ hmass]
  change (∫ t in a..(1 - a), F t) = (∫ t in (0 : ℝ)..1, F t) -
    ((∫ t in (0 : ℝ)..a, F t) + (∫ t in (1 - a)..1, F t))
  linarith

/-- Page 3 equations 2.13 and 2.14. The psi margin and an endpoint
upper bound imply central positivity. This implication is conditional on CostaEstimate. -/
theorem central_positive_of_psi_margin (hCosta : CostaEstimate)
    (m : ℕ) {δ u X a : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.0001) (hu : 0 ≤ u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (htail : tailThetaIntegral m δ u X a ≤ tailCoefficient δ u X * tailMass m a)
    (hmargin : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
      tailCoefficient δ u X * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t) <
        psiAverage m δ u X) :
    0 < centralThetaIntegral m δ u X a := by
  have hm := weight_mass_pos m
  have htheta := thetaAverage_ge_psiAverage_sub_omega hCosta m hδ hδ1 hu hu1 hX
  rw [central_integral_split m hδ ((Real.exp_pos 38).le.trans hX) ha ha2]
  have hdiv : tailCoefficient δ u X * tailMass m a /
      (∫ t in (0 : ℝ)..1, weight m t) < thetaAverage m δ u X := by linarith
  have hmul := (div_lt_iff₀ hm).mp hdiv
  linarith


/-- Page 2 equation 2.1. A coarse certified bound for the exponential
threshold used in the normalization. -/
theorem exp38_lt_base_quarter : Real.exp 38 < (10 : ℝ) ^ 18 := by
  calc
    Real.exp 38 = Real.exp 1 ^ 38 := by rw [← Real.exp_nat_mul]; norm_num
    _ < (2.7182818286 : ℝ) ^ 38 := by
      exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_nonneg 1) (by norm_num)
    _ < (10 : ℝ) ^ 18 := by norm_num

/-- Page 2 equation 2.1 and page 3 equation 2.7. Rescaling an upper
endpoint above the binary base gives X above exp 38 and a positive log denominator. -/
theorem normalized_domain {δ u a x : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 0.0001)
    (hu : 1 / 10 ^ 12 ≤ u) (hu1 : u ≤ 0.0001)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hx : (4 * 10 ^ 18 : ℝ) < x) :
    let X := x / (Real.exp u * (1 + δ * (1 - a)))
    0 < X ∧ Real.exp 38 ≤ X ∧ 1 < X * (Real.exp u - 1) ∧
      Real.exp u * (X * (1 + δ * (1 - a))) = x := by
  dsimp only
  have hu0 : 0 ≤ u := by linarith
  have hB : 0 < 1 + δ * (1 - a) := by
    have : 0 ≤ δ * (1 - a) := mul_nonneg hδ (by linarith)
    linarith
  have hB2 : 1 + δ * (1 - a) ≤ 2 := by nlinarith [mul_nonneg hδ ha]
  have he : Real.exp u ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 0.0001)
      (by norm_num : (0.0001 : ℝ) < 1)
    have hu' := Real.exp_le_exp.mpr hu1
    norm_num at h
    linarith
  have hS : 0 < Real.exp u * (1 + δ * (1 - a)) := mul_pos (Real.exp_pos u) hB
  have hS4 : Real.exp u * (1 + δ * (1 - a)) ≤ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hB2)]
  have hlarge : (10 : ℝ) ^ 18 < x / (Real.exp u * (1 + δ * (1 - a))) := by
    apply (lt_div_iff₀ hS).mpr
    nlinarith
  refine ⟨by positivity, exp38_lt_base_quarter.le.trans hlarge.le, ?_, ?_⟩
  · have huE : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
    have hE : 1 / (10 : ℝ) ^ 12 ≤ Real.exp u - 1 := hu.trans huE
    have hprod := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ x / (Real.exp u * (1 + δ * (1 - a))))
    nlinarith
  · field_simp


/-- Page 3 equation 2.6. Integrating a pointwise theta bound over
the two endpoint intervals gives its weighted tail bound. -/
theorem tail_bound_of_pointwise (m : ℕ) {δ u X a C : ℝ}
    (hδ : 0 ≤ δ) (hX : 0 ≤ X) (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1,
      Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
        Chebyshev.theta (X * (1 + δ * t)) ≤ C) :
    tailThetaIntegral m δ u X a ≤ C * tailMass m a := by
  let F := fun t => (Chebyshev.theta (Real.exp u * (X * (1 + δ * t))) -
    Chebyshev.theta (X * (1 + δ * t))) * weight m t
  have hi : IntervalIntegrable F volume 0 1 :=
    weighted_difference_integrable Chebyshev.theta_mono m hδ (Real.exp_nonneg u) hX
  have piece : ∀ s b : ℝ, 0 ≤ s → s ≤ b → b ≤ 1 →
      (∫ t in s..b, F t) ≤ C * (∫ t in s..b, weight m t) := by
    intro s b hs hsb hb
    rw [← intervalIntegral.integral_const_mul]
    have his : IntervalIntegrable F volume s b := hi.mono_set (by
      rw [uIcc_of_le hsb, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc hs hb)
    apply intervalIntegral.integral_mono_on hsb his
      (((weight_continuous m).const_mul C).intervalIntegrable _ _)
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hs.trans ht.1, ht.2.trans hb⟩
    exact mul_le_mul_of_nonneg_right (hC t ht01) (weight_nonneg m ht01)
  have hleft := piece 0 a le_rfl ha (by linarith)
  have hright := piece (1 - a) 1 (by linarith) (by linarith) le_rfl
  unfold tailThetaIntegral tailMass
  change (∫ t in (0 : ℝ)..a, F t) + (∫ t in (1 - a)..1, F t) ≤ _
  calc
    _ ≤ C * (∫ t in (0 : ℝ)..a, weight m t) + C * (∫ t in (1 - a)..1, weight m t) :=
      add_le_add hleft hright
    _ = _ := by ring

/-- Page 4 Lemma 2.2 and equations 2.16 to 2.19.
The polynomial-smoothed explicit formula, its absolute zero sum and remainder.
Lemma 2.2 cites Ramare and Saouter 2003 Lemma 4.
Task259 proves this leaf from the integrated explicit formula. -/
theorem smoothed_explicit_lower {m : ℕ} (hm : 2 ≤ m) {δ u X : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hX : Real.exp 38 ≤ X) :
    Summable (zeroSummand m δ u X) ∧
      (Real.exp u - 1) * X * (1 + δ / 2 - zeroError m δ u X) - u / (2 * X) ≤
        psiAverage m δ u X := by
  have hm0 : 0 < m := by omega
  have hX3 : 3 ≤ X := by linarith [Real.add_one_le_exp (38 : ℝ)]
  have hX0 : 0 < X := by linarith
  have hs := Task259.absolute_zero_summable hm0 hδ hu hX0
  exact ⟨hs, Task301.psi_lower_of_explicit_identity m hδ.le hu.le hX3 hs
    (Task259.psiAverage_explicit hm0 hδ hu (by linarith))⟩

/-- Page 3 equation 2.7 and page 9 after equation 2.64. The enlarged
Brun Titchmarsh logarithm quotient decreases in X once X (e^u - 1) exceeds one.
AI wrote this Lean code, 2026-11-12. -/
theorem tail_log_ratio_antitone {δ u Y X : ℝ} (hδ : 0 ≤ δ) (hu : 0 < u)
    (hY : 0 < Y) (hYX : Y ≤ X) (hgap : 1 < Y * (Real.exp u - 1)) :
    Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)) ≤
      Real.log (Real.exp u * Y * (1 + δ)) / Real.log (Y * (Real.exp u - 1)) := by
  have hE : 0 < Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hX : 0 < X := hY.trans_le hYX
  have hc : 0 < Real.exp u * (1 + δ) := by positivity
  have hEc : Real.exp u - 1 ≤ Real.exp u * (1 + δ) := by
    nlinarith [Real.exp_pos u, mul_nonneg (Real.exp_pos u).le hδ]
  have hA : Real.log (Real.exp u - 1) ≤ Real.log (Real.exp u * (1 + δ)) :=
    Real.log_le_log hE hEc
  have hl : Real.log Y ≤ Real.log X := Real.log_le_log hY hYX
  have eX1 : Real.log (Real.exp u * X * (1 + δ)) = Real.log X + Real.log (Real.exp u * (1 + δ)) := by
    rw [show Real.exp u * X * (1 + δ) = X * (Real.exp u * (1 + δ)) by ring,
      Real.log_mul hX.ne' hc.ne']
  have eY1 : Real.log (Real.exp u * Y * (1 + δ)) = Real.log Y + Real.log (Real.exp u * (1 + δ)) := by
    rw [show Real.exp u * Y * (1 + δ) = Y * (Real.exp u * (1 + δ)) by ring,
      Real.log_mul hY.ne' hc.ne']
  have eX2 : Real.log (X * (Real.exp u - 1)) = Real.log X + Real.log (Real.exp u - 1) :=
    Real.log_mul hX.ne' hE.ne'
  have eY2 : Real.log (Y * (Real.exp u - 1)) = Real.log Y + Real.log (Real.exp u - 1) :=
    Real.log_mul hY.ne' hE.ne'
  have hdY : 0 < Real.log (Y * (Real.exp u - 1)) := Real.log_pos hgap
  have hdX : 0 < Real.log (X * (Real.exp u - 1)) := by
    rw [eX2]; rw [eY2] at hdY; linarith
  rw [div_le_div_iff₀ hdX hdY, eX1, eY1, eX2, eY2]
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hl)]

/-- Page 3 equation 2.3. The endpoint mass nu grows with the cut a on [0, 1/2].
AI wrote this Lean code, 2026-11-12. -/
theorem tailMass_mono (m : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    tailMass m a ≤ tailMass m b := by
  unfold tailMass
  rw [weight_tail_symm, weight_tail_symm]
  have hi : ∀ s v : ℝ, IntervalIntegrable (weight m) volume s v :=
    fun s v => (weight_continuous m).intervalIntegrable s v
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a b)
  have hnn : 0 ≤ ∫ t in a..b, weight m t :=
    intervalIntegral.integral_nonneg hab (fun t ht =>
      weight_nonneg m ⟨ha.trans ht.1, by linarith [ht.2]⟩)
  linarith

/-- Page 9 equation 2.64 and the remark before Table 2 that the budget only
improves as X grows. Every term of the normalized budget is monotone in X and
in the cut a, and the absolute zero sum Sigma decreases in X. So the budget at
an admissible point Y below X with a larger cut b implies the budget at X and a.
This is the reduction of the Table 2 check to its least X.
AI wrote this Lean code, 2026-11-12. -/
theorem zero_budget_of_endpoint {m : ℕ} (hm : 0 < m) {δ u a b Y X : ℝ}
    (hδ : 0 < δ) (hu : 0 < u) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2)
    (hY : Real.exp 38 ≤ Y) (hYX : Y ≤ X) (hgap : 1 < Y * (Real.exp u - 1))
    (hend : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt Y +
      tailCoefficient δ u Y * tailMass m b / (∫ t in (0 : ℝ)..1, weight m t) +
        u / (2 * Y) < (Real.exp u - 1) * Y * (1 + δ / 2 - zeroError m δ u Y)) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
      tailCoefficient δ u X * tailMass m a / (∫ t in (0 : ℝ)..1, weight m t) +
        u / (2 * X) < (Real.exp u - 1) * X * (1 + δ / 2 - zeroError m δ u X) := by
  have hY0 : 0 < Y := (Real.exp_pos 38).trans_le hY
  have hX0 : 0 < X := hY0.trans_le hYX
  have hE : 0 < Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hM := weight_mass_pos m
  set M := ∫ t in (0 : ℝ)..1, weight m t
  set E := Real.exp u - 1 with hEdef
  set lam := X / Y with hlam
  have hlam1 : 1 ≤ lam := (one_le_div hY0).mpr hYX
  have hlamY : lam * Y = X := by rw [hlam]; field_simp
  -- the zero sum
  have hz := (zeroError_antitone m δ u hY0 hYX
    (Task259.absolute_zero_summable hm hδ hu hY0)).2
  -- the tail term
  have hr := tail_log_ratio_antitone hδ.le hu hY0 hYX hgap
  have hX1 : 1 < X := by linarith [Real.add_one_le_exp (38 : ℝ)]
  have hrX : 0 ≤ Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * E) := by
    have h1 : 0 < Real.log (X * E) := Real.log_pos (by nlinarith)
    have h2 : 0 < Real.log (Real.exp u * X * (1 + δ)) := by
      apply Real.log_pos
      have he1 : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
      have h3 : 1 < Real.exp u * X := by nlinarith
      nlinarith
    positivity
  have hnu := tailMass_mono m ha hab hb
  have hnua : 0 ≤ tailMass m a := by
    have h4 := tailMass_mono m le_rfl ha (by linarith)
    have h0 : tailMass m 0 = 0 := by simp [tailMass]
    linarith
  have hK : Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * E) * tailMass m a ≤
      Real.log (Real.exp u * Y * (1 + δ)) / Real.log (Y * E) * tailMass m b :=
    mul_le_mul hr hnu hnua (hrX.trans hr)
  have h0 : 0 ≤ 2 * (1 + δ) * E * X := by positivity
  have hL : tailCoefficient δ u X * tailMass m a = (2 * (1 + δ) * E * X) *
      (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * E) * tailMass m a) := by
    unfold tailCoefficient; ring
  have hR : lam * (tailCoefficient δ u Y * tailMass m b / M) = (2 * (1 + δ) * E * X) *
      (Real.log (Real.exp u * Y * (1 + δ)) / Real.log (Y * E) * tailMass m b) / M := by
    unfold tailCoefficient; rw [← hlamY]; ring
  have htail : tailCoefficient δ u X * tailMass m a / M ≤
      lam * (tailCoefficient δ u Y * tailMass m b / M) := by
    rw [hR, hL]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hK h0) hM.le
  -- the square root term
  have hsq : Real.sqrt X ≤ lam * Real.sqrt Y := by
    have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
    have hsXY : Real.sqrt Y ≤ Real.sqrt X := Real.sqrt_le_sqrt hYX
    have e1 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
    have e2 : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0.le
    rw [hlam, div_mul_eq_mul_div, le_div_iff₀ hY0]
    nlinarith [mul_le_mul_of_nonneg_left hsXY (Real.sqrt_nonneg X)]
  -- the u over 2X term
  have hux : u / (2 * X) ≤ lam * (u / (2 * Y)) := by
    have h1 : u / (2 * X) ≤ u / (2 * Y) :=
      div_le_div_of_nonneg_left hu.le (by positivity) (by linarith)
    have h2 : u / (2 * Y) ≤ lam * (u / (2 * Y)) :=
      le_mul_of_one_le_left (by positivity) hlam1
    linarith
  have hω : (0 : ℝ) ≤ 2.05022 * 10 ^ (-3 : ℤ) := by norm_num
  have hmul := mul_lt_mul_of_pos_left hend (by linarith : 0 < lam)
  have hrhs : lam * (E * Y * (1 + δ / 2 - zeroError m δ u Y)) ≤
      E * X * (1 + δ / 2 - zeroError m δ u X) := by
    have he : lam * (E * Y * (1 + δ / 2 - zeroError m δ u Y)) =
        E * X * (1 + δ / 2 - zeroError m δ u Y) := by rw [← hlamY]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hωs := mul_le_mul_of_nonneg_left hsq hω
  have hdist : lam * ((2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt Y +
      tailCoefficient δ u Y * tailMass m b / M + u / (2 * Y)) =
      (2.05022 * 10 ^ (-3 : ℤ)) * (lam * Real.sqrt Y) +
        lam * (tailCoefficient δ u Y * tailMass m b / M) + lam * (u / (2 * Y)) := by ring
  linarith

/-- The least admissible normalized X for a Table 2 row, uniformly in the cut a. -/
noncomputable def rowEndpointX (r : PrintedRow) : ℝ :=
  r.threshold / (Real.exp r.uQ * (1 + (r.deltaQ : ℝ)))

/-- Page 2 equation 2.1. The row endpoint is admissible and lies below every
admissible normalized X of the row. AI wrote this Lean code, 2026-11-12. -/
theorem rowEndpointX_domain {r : PrintedRow} (hr : r ∈ tableTwo) {a X : ℝ}
    (ha : a ∈ Icc (r.aQ : ℝ) ((r.aQ : ℝ) + 1 / 10000)) (hX : Real.exp 38 ≤ X)
    (hx : r.threshold < Real.exp r.uQ * (X * (1 + (r.deltaQ : ℝ) * (1 - a)))) :
    Real.exp 38 ≤ rowEndpointX r ∧ rowEndpointX r ≤ X ∧
      1 < rowEndpointX r * (Real.exp r.uQ - 1) := by
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hδ1 : (r.deltaQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.1
    norm_num at h ⊢
    exact h
  have hu : 1 / (10 : ℝ) ^ 12 ≤ r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    norm_num at h ⊢
    exact h
  have hu1 : (r.uQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    norm_num at h ⊢
    exact h
  have hrpar := (tableTwo_rounding_arithmetic r hr).1
  have haQ : (0 : ℝ) ≤ r.aQ := by exact_mod_cast hrpar.2.2.2.1
  have ha0 : 0 ≤ a := haQ.trans ha.1
  have he : Real.exp (r.uQ : ℝ) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 0.0001)
      (by norm_num : (0.0001 : ℝ) < 1)
    have hu' := Real.exp_le_exp.mpr hu1
    norm_num at h
    linarith
  have hS : 0 < Real.exp r.uQ * (1 + (r.deltaQ : ℝ)) := by positivity
  have hS4 : Real.exp r.uQ * (1 + (r.deltaQ : ℝ)) ≤ 4 := by
    nlinarith [Real.exp_pos (r.uQ : ℝ)]
  have hbase : (4 * 10 ^ 18 : ℝ) ≤ r.threshold := by
    have h := tableTwo_threshold_ge_base hr
    norm_num [evenBase] at h ⊢
    exact h
  have hlow : (10 : ℝ) ^ 18 ≤ rowEndpointX r := by
    unfold rowEndpointX
    rw [le_div_iff₀ hS]
    nlinarith
  refine ⟨exp38_lt_base_quarter.le.trans hlow, ?_, ?_⟩
  · unfold rowEndpointX
    rw [div_le_iff₀ hS]
    have hX0 : 0 < X := (Real.exp_pos 38).trans_le hX
    have h1 : X * (1 + (r.deltaQ : ℝ) * (1 - a)) ≤ X * (1 + (r.deltaQ : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hX0.le
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (r.uQ : ℝ)).le
    nlinarith
  · have huE : (r.uQ : ℝ) ≤ Real.exp r.uQ - 1 := by linarith [Real.add_one_le_exp (r.uQ : ℝ)]
    have hE : 1 / (10 : ℝ) ^ 12 ≤ Real.exp r.uQ - 1 := hu.trans huE
    have hprod := mul_le_mul hlow hE (by norm_num) (by positivity)
    nlinarith

end LeanLab.KadiriLumley2014.Task92
