module

public import LeanLab.KadiriLumley2014.Weight

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 2 equation 2.3 and page 9 weight definition.
Journal INTEGERS 14 A61 pages 3 and 12.
AI wrote this Lean code, Codex by OpenAI, 2026-10-25.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task64
open Real Set MeasureTheory intervalIntegral

/-- The endpoint mass nu of the paper's polynomial weight. -/
noncomputable def tailMass (m : ℕ) (a : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..a, weight m t) + (∫ t in (1 - a)..1, weight m t)

/-- The two endpoint integrals agree by reflection symmetry. -/
theorem weight_tail_symm (m : ℕ) (a : ℝ) :
    (∫ t in (1 - a)..1, weight m t) = ∫ t in (0 : ℝ)..a, weight m t := by
  have h := intervalIntegral.integral_comp_sub_left (weight m) (a := 0) (b := a) 1
  simp only [sub_zero, weight_symm] at h
  exact h.symm

/-- Nu is twice the lower endpoint integral. -/
theorem tailMass_eq_two (m : ℕ) (a : ℝ) :
    tailMass m a = 2 * (∫ t in (0 : ℝ)..a, weight m t) := by
  rw [tailMass, weight_tail_symm]
  ring

/-- The weight is bounded on the lower endpoint interval by its endpoint value. -/
theorem weight_le_at_endpoint (m : ℕ) {a t : ℝ}
    (_ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (ht : t ∈ Icc (0 : ℝ) a) :
    weight m t ≤ weight m a := by
  have ht1 : t ≤ 1 := by linarith [ht.2]
  have hbase0 : 0 ≤ 4 * t * (1 - t) :=
    mul_nonneg (mul_nonneg (by norm_num) ht.1) (sub_nonneg.mpr ht1)
  have hbase : 4 * t * (1 - t) ≤ 4 * a * (1 - a) := by
    nlinarith [mul_nonneg (by linarith [ht.2] : 0 ≤ a - t)
      (by linarith [ht.2] : 0 ≤ 1 - a - t)]
  exact pow_le_pow_left₀ hbase0 hbase m

/-- An explicit elementary endpoint mass bound from the printed a and m. -/
theorem tailMass_le_endpoint (m : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    tailMass m a ≤ 2 * a * (4 * a * (1 - a)) ^ m := by
  have hmono : (∫ t in (0 : ℝ)..a, weight m t) ≤
      ∫ t in (0 : ℝ)..a, weight m a := by
    apply intervalIntegral.integral_mono_on ha
      ((weight_continuous m).intervalIntegrable _ _) intervalIntegrable_const
    intro t ht
    exact weight_le_at_endpoint m ha ha2 ht
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  rw [tailMass_eq_two]
  have hm := mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [weight, mul_assoc] using hm

/-- The endpoint mass is nonnegative and at most the full mass. -/
theorem tailMass_bounds (m : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    0 ≤ tailMass m a ∧ tailMass m a ≤ (∫ t in (0 : ℝ)..1, weight m t) := by
  have hhi : a ≤ 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have h1 : 1 - a ≤ 1 := by linarith
  have hn0 : 0 ≤ ∫ t in (0 : ℝ)..a, weight m t :=
    intervalIntegral.integral_nonneg ha (fun t ht => weight_nonneg m ⟨ht.1, ht.2.trans ha1⟩)
  have hnc : 0 ≤ ∫ t in a..(1 - a), weight m t :=
    intervalIntegral.integral_nonneg hhi (fun t ht => weight_nonneg m ⟨ha.trans ht.1, ht.2.trans h1⟩)
  have hi : ∀ a b : ℝ, IntervalIntegrable (weight m) volume a b :=
    (weight_continuous m).intervalIntegrable
  have hadd :
      (∫ t in (0 : ℝ)..a, weight m t) + (∫ t in a..(1 - a), weight m t) +
        (∫ t in (1 - a)..1, weight m t) = (∫ t in (0 : ℝ)..1, weight m t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a (1 - a)),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 (1 - a)) (hi (1 - a) 1)]
  constructor
  · rw [tailMass_eq_two]
    linarith
  · unfold tailMass
    linarith

/-- The normalized endpoint mass lies between zero and one. -/
theorem tailMass_ratio_bounds (m : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    0 ≤ tailMass m a / (∫ t in (0 : ℝ)..1, weight m t) ∧
    tailMass m a / (∫ t in (0 : ℝ)..1, weight m t) ≤ 1 := by
  have h := tailMass_bounds m ha ha2
  exact ⟨div_nonneg h.1 (weight_mass_pos m).le,
    (div_le_one (weight_mass_pos m)).mpr h.2⟩

end LeanLab.KadiriLumley2014.Task64
