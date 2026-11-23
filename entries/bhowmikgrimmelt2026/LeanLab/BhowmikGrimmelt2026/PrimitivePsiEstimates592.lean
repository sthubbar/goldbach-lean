module

public import LeanLab.BhowmikGrimmelt2026.RouteCount508

/-!
Estimates for the primitive character sharp explicit formula.
Davenport second edition chapter 16 and chapter 19 pages 116 to 118.
These estimates use the proved zero window count. They do not import a zeta contour.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Davenport chapter 16 and chapter 19 page 118.
The reciprocal zero mass in the task window is bounded by log squared.
This keeps the logarithmic bound before the power absorption in RouteCount508. -/
theorem reciprocal_log_square592 (Θ : ℝ) (hΘ : Θ < 3 / 4)
    (hZ : ZeroBound Θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q], q ≤ Nat.sqrt X →
      ∀ χ : DirichletCharacter ℂ q, ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖ ≤ K * Real.log X ^ 2 := by
  obtain ⟨A, hA0, hA⟩ := zero_window_count508
  refine ⟨360 * A, by positivity, ?_⟩
  intro X hX2 q _ hqQ χ T hT Z hZset
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX2
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlog2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hXr
  have hlog : 1 ≤ 2 * Real.log X := by
    have := Real.log_two_gt_d9
    linarith
  have hL0 : 0 ≤ Real.log X := by linarith
  have h3 : 2 * (X : ℝ) + 4 ≤ (X : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hXr) (by positivity : (0 : ℝ) ≤ (X : ℝ) ^ 2 + 2 * X + 2)]
  have hmaps : ∀ ρ ∈ Z, ⌊ρ.im⌋ ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ) := by
    intro ρ hρ
    obtain ⟨-, -, -, him⟩ := (hZset ρ).mp hρ
    have h2 : |ρ.im| ≤ 2 * (X : ℝ) := him.trans hT.2
    obtain ⟨ha, hb⟩ := abs_le.mp h2
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]; push_cast; linarith
    · have hf := Int.floor_le ρ.im
      have : ((⌊ρ.im⌋ : ℤ) : ℝ) ≤ (((2 * X + 1 : ℕ) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  have hfib : ∀ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
      ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) / ‖ρ‖ ≤
        36 * A * Real.log X * (1 / (|(k : ℝ)| + 1)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkR : |(k : ℝ)| ≤ 2 * (X : ℝ) + 1 := by
      rw [abs_le]
      constructor
      · have : ((-((2 * X + 1 : ℕ) : ℤ) : ℤ) : ℝ) ≤ k := by exact_mod_cast hk.1
        push_cast at this; linarith
      · have : ((k : ℤ) : ℝ) ≤ (((2 * X + 1 : ℕ) : ℤ) : ℝ) := by exact_mod_cast hk.2
        push_cast at this; linarith
    have hwin : ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) ≤
        A * Real.log ((q : ℝ) * (|(k : ℝ) + 1 / 2| + 2)) := by
      apply hA q χ ((k : ℝ) + 1 / 2)
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hz, h0, h1, _⟩ := (hZset ρ).mp hρ.1
      refine ⟨hz, h0, h1, ?_⟩
      have e1 := Int.floor_le ρ.im
      have e2 := Int.lt_floor_add_one ρ.im
      rw [hρ.2] at e1 e2
      rw [abs_le]; constructor <;> linarith
    have hlogq : Real.log ((q : ℝ) * (|(k : ℝ) + 1 / 2| + 2)) ≤ 4 * Real.log X := by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
      have hqX : (q : ℝ) ≤ X := by exact_mod_cast hqQ.trans (Nat.sqrt_le_self X)
      have habs : |(k : ℝ) + 1 / 2| ≤ 2 * (X : ℝ) + 2 := by
        have := abs_le.mp hkR
        rw [abs_le]; constructor <;> linarith
      have hle : (q : ℝ) * (|(k : ℝ) + 1 / 2| + 2) ≤ (X : ℝ) ^ 4 := by
        calc (q : ℝ) * (|(k : ℝ) + 1 / 2| + 2) ≤ (X : ℝ) * (2 * (X : ℝ) + 4) :=
              mul_le_mul hqX (by linarith) (by positivity) (by positivity)
          _ ≤ (X : ℝ) * (X : ℝ) ^ 3 := mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = (X : ℝ) ^ 4 := by ring
      calc Real.log ((q : ℝ) * (|(k : ℝ) + 1 / 2| + 2)) ≤ Real.log ((X : ℝ) ^ 4) :=
            Real.log_le_log (mul_pos (by linarith) (by positivity)) hle
        _ = 4 * Real.log X := by rw [Real.log_pow]; norm_num
    have hterm : ∀ ρ ∈ Z.filter (fun ρ => ⌊ρ.im⌋ = k),
        (mult χ ρ : ℝ) / ‖ρ‖ ≤ (mult χ ρ : ℝ) * (9 / (|(k : ℝ)| + 1)) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hz, h0, h1, _⟩ := (hZset ρ).mp hρ.1
      have hn := character_zero_norm_lower508 hΘ hZ χ hz h0 h1
      have him : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
      have e1 := Int.floor_le ρ.im
      have e2 := Int.lt_floor_add_one ρ.im
      rw [hρ.2] at e1 e2
      have hk1 : |(k : ℝ)| ≤ |ρ.im| + 1 := by
        have := le_abs_self ρ.im
        have := neg_abs_le ρ.im
        rw [abs_le]; constructor <;> linarith
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by positivity)]
      linarith
    have hpos : (0 : ℝ) ≤ 9 / (|(k : ℝ)| + 1) := by positivity
    calc ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) / ‖ρ‖
        ≤ ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) * (9 / (|(k : ℝ)| + 1)) :=
          Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ)) * (9 / (|(k : ℝ)| + 1)) := by
          rw [Finset.sum_mul]
      _ ≤ (A * (4 * Real.log X)) * (9 / (|(k : ℝ)| + 1)) :=
          mul_le_mul_of_nonneg_right
            (hwin.trans (mul_le_mul_of_nonneg_left hlogq hA0)) hpos
      _ = 36 * A * Real.log X * (1 / (|(k : ℝ)| + 1)) := by ring
  have hharm : 2 * (1 + Real.log (((2 * X + 1 : ℕ) : ℝ) + 1)) ≤ 10 * Real.log X := by
    have hle : (((2 * X + 1 : ℕ) : ℝ) + 1) ≤ (X : ℝ) ^ 3 := by push_cast; linarith
    have : Real.log (((2 * X + 1 : ℕ) : ℝ) + 1) ≤ 3 * Real.log X := by
      calc Real.log (((2 * X + 1 : ℕ) : ℝ) + 1) ≤ Real.log ((X : ℝ) ^ 3) :=
            Real.log_le_log (by positivity) hle
        _ = 3 * Real.log X := by rw [Real.log_pow]; norm_num
    linarith
  calc ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖
      = ∑ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
          ∑ ρ ∈ Z with ⌊ρ.im⌋ = k, (mult χ ρ : ℝ) / ‖ρ‖ :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
          36 * A * Real.log X * (1 / (|(k : ℝ)| + 1)) := Finset.sum_le_sum hfib
    _ = 36 * A * Real.log X *
          ∑ k ∈ Finset.Icc (-((2 * X + 1 : ℕ) : ℤ)) ((2 * X + 1 : ℕ) : ℤ),
            1 / (|(k : ℝ)| + 1) := by rw [Finset.mul_sum]
    _ ≤ 36 * A * Real.log X * (10 * Real.log X) :=
        mul_le_mul_of_nonneg_left ((int_abs_harmonic508 (2 * X + 1)).trans hharm)
          (by positivity)
    _ = 360 * A * Real.log X ^ 2 := by ring


/-- Davenport page 118. A strip zero list in the unit window has reciprocal mass
at most four times its multiplicity mass under ZeroBound. -/
theorem low_reciprocal_bound592 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (Z : Finset ℂ),
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1) →
      ‖∑ ρ ∈ Z, (mult χ ρ : ℂ) / ρ‖ ≤ B * Real.log (2 * (q : ℝ)) := by
  obtain ⟨A, hA, hcount⟩ := zero_window_count508
  refine ⟨4 * A, by positivity, ?_⟩
  intro q _ χ Z hzeros
  have hc := hcount q χ 0 Z (by simpa using hzeros)
  simp only [abs_zero, zero_add] at hc
  have ht : ∀ ρ ∈ Z, ‖(mult χ ρ : ℂ) / ρ‖ ≤ 4 * (mult χ ρ : ℝ) := by
    intro ρ hρ
    obtain ⟨hz, h0, h1, _⟩ := hzeros ρ hρ
    have hn := character_zero_norm_lower508 hΘ hZ χ hz h0 h1
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ (by linarith : 0 < ‖ρ‖)).mpr
    nlinarith [show (0 : ℝ) ≤ (mult χ ρ : ℝ) from Nat.cast_nonneg _]
  calc ‖∑ ρ ∈ Z, (mult χ ρ : ℂ) / ρ‖ ≤ ∑ ρ ∈ Z, ‖(mult χ ρ : ℂ) / ρ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ Z, 4 * (mult χ ρ : ℝ) := Finset.sum_le_sum ht
    _ = 4 * ∑ ρ ∈ Z, (mult χ ρ : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 4 * (A * Real.log ((q : ℝ) * 2)) := mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = (4 * A) * Real.log (2 * (q : ℝ)) := by rw [mul_comm (q : ℝ) 2]; ring

/-- CONDITIONAL on the displayed regularized partial fraction bound for b.
Davenport page 118: the proved unit window count removes the separate counting
premise from the earlier b_term_bound541 absorption step. -/
theorem b_term_counted_bound592 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (Z : Finset ℂ),
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1) → ∀ (b : ℂ) (A : ℝ),
      ‖b + ∑ ρ ∈ Z, (mult χ ρ : ℂ) / ρ‖ ≤ A * Real.log (2 * (q : ℝ)) →
      ‖b‖ ≤ (A + B) * Real.log (2 * (q : ℝ)) := by
  obtain ⟨B, hB, hlow⟩ := low_reciprocal_bound592 Θ hΘ hZ
  refine ⟨B, hB, ?_⟩
  intro q _ χ Z hzeros b A hpartial
  have he : b = (b + ∑ ρ ∈ Z, (mult χ ρ : ℂ) / ρ) -
      (∑ ρ ∈ Z, (mult χ ρ : ℂ) / ρ) := by ring
  calc ‖b‖ = ‖(b + ∑ ρ ∈ Z, (mult χ ρ : ℂ) / ρ) -
      (∑ ρ ∈ Z, (mult χ ρ : ℂ) / ρ)‖ := congrArg norm he
    _ ≤ ‖b + ∑ ρ ∈ Z, (mult χ ρ : ℂ) / ρ‖ +
        ‖∑ ρ ∈ Z, (mult χ ρ : ℂ) / ρ‖ := norm_sub_le _ _
    _ ≤ A * Real.log (2 * (q : ℝ)) + B * Real.log (2 * (q : ℝ)) :=
      add_le_add hpartial (hlow q χ Z hzeros)
    _ = (A + B) * Real.log (2 * (q : ℝ)) := by ring

/-- Davenport page 117 requires n at least two. The omitted n equal to one case
follows from the reciprocal mass bound without an explicit formula. -/
theorem psi_one_bound592 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ‖(∑ m ∈ Finset.range (1 + 1),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
        ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (1 : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  obtain ⟨C, hC, hrec⟩ := reciprocal_log_square592 Θ hΘ hZ
  refine ⟨C, hC, ?_⟩
  intro X hX q _ hq χ T hT Z hzeros
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ArithmeticFunction.map_zero,
    ArithmeticFunction.vonMangoldt_apply_one, Complex.ofReal_zero, zero_mul, add_zero,
    zero_add, Complex.one_cpow, mul_one]
  calc ‖∑ ρ ∈ Z, (mult χ ρ : ℂ) / ρ‖ ≤ ∑ ρ ∈ Z, ‖(mult χ ρ : ℂ) / ρ‖ := norm_sum_le _ _
    _ = ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖ := by
      apply Finset.sum_congr rfl
      intro ρ _
      rw [norm_div, Complex.norm_natCast]
    _ ≤ C * Real.log X ^ 2 := hrec X hX q hq χ T hT Z hzeros

/-- Davenport page 117 display 4 uses a strict height cutoff. The zeros exactly
at the height cost one logarithm when n is no larger than that height. -/
theorem boundary_zero_bound592 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (T : ℝ), 0 < T → ∀ (n : ℕ), 1 ≤ n → (n : ℝ) ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| = T) →
      ‖∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤
        A * Real.log ((q : ℝ) * (T + 2)) := by
  obtain ⟨A, hA, hcount⟩ := zero_window_count508
  refine ⟨2 * A, by positivity, ?_⟩
  intro q _ χ T hT n hn hnT Z hzeros
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hpos := hcount q χ T (Z.filter (fun ρ => 0 ≤ ρ.im)) (by
    intro ρ hρ
    obtain ⟨hzmem, hsign⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, h0, h1, him⟩ := hzeros ρ hzmem
    rw [abs_of_nonneg hsign] at him
    exact ⟨hz, h0, h1, by simp [him]⟩)
  have hneg := hcount q χ (-T) (Z.filter (fun ρ => ¬ 0 ≤ ρ.im)) (by
    intro ρ hρ
    obtain ⟨hzmem, hsign⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, h0, h1, him⟩ := hzeros ρ hzmem
    rw [abs_of_neg (lt_of_not_ge hsign)] at him
    refine ⟨hz, h0, h1, ?_⟩
    have he : ρ.im - -T = 0 := by linarith
    rw [he, abs_zero]
    norm_num)
  rw [abs_of_pos hT] at hpos
  rw [abs_neg, abs_of_pos hT] at hneg
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun ρ : ℂ => 0 ≤ ρ.im)
    (fun ρ => (mult χ ρ : ℝ))
  have hmass : ∑ ρ ∈ Z, (mult χ ρ : ℝ) ≤ 2 * A * Real.log ((q : ℝ) * (T + 2)) := by
    linarith
  have hterm : ∀ ρ ∈ Z, ‖(mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ (mult χ ρ : ℝ) := by
    intro ρ hρ
    obtain ⟨-, -, h1, him⟩ := hzeros ρ hρ
    have hnorm : T ≤ ‖ρ‖ := by simpa [him] using Complex.abs_im_le_norm ρ
    have hp : (n : ℝ) ^ ρ.re ≤ n := Real.rpow_le_self_of_one_le hn1 h1.le
    have hpow : ‖(n : ℂ) ^ ρ‖ = (n : ℝ) ^ ρ.re := by
      simpa only [Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hn0 ρ
    rw [norm_div, norm_mul, Complex.norm_natCast, hpow]
    apply (div_le_iff₀ (hT.trans_le hnorm)).mpr
    exact mul_le_mul_of_nonneg_left (hp.trans (hnT.trans hnorm)) (by positivity)
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans hmass)

/-- Davenport chapter 19 page 116 and chapter 16. The proved full strip window
count selects a common good height for both horizontal sides without GRH. -/
theorem character_good_height592 :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ T : ℝ, 2 ≤ T → ∃ U ∈ Set.Icc T (T + 1),
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        1 / (C * Real.log ((q : ℝ) * (T + 4))) ≤ |(|ρ.im|) - U| := by
  classical
  obtain ⟨A, hA, hcount⟩ := zero_window_count508
  have hl6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  refine ⟨4 * (2 * A + 1 / Real.log 6), by positivity, ?_⟩
  intro q _ χ hχ T hT
  let t : ℝ := T + 1 / 2
  let L : ℝ := Real.log ((q : ℝ) * (T + 4))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have harg : 6 ≤ (q : ℝ) * (T + 4) := by nlinarith
  have hL6 : Real.log 6 ≤ L := Real.log_le_log (by norm_num) harg
  have hL : 0 < L := hl6.trans_le hL6
  have ht : 0 ≤ t := by dsimp [t]; linarith
  obtain ⟨Z, hZ⟩ := character_zero_finset504 χ (T + 2)
  let G := Z.filter (fun ρ => |(|ρ.im|) - t| ≤ 3 / 4)
  let H := G.image (fun ρ => |ρ.im|)
  have hlog : Real.log ((q : ℝ) * (|t| + 2)) ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [abs_of_nonneg ht]
    dsimp [t]
    nlinarith
  have hp := hcount q χ t (G.filter (fun ρ => 0 ≤ ρ.im)) (by
    intro ρ hρ
    obtain ⟨hg, hsign⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hzmem, hnear⟩ := Finset.mem_filter.mp hg
    obtain ⟨hz, h0, h1, _⟩ := (hZ ρ).mp hzmem
    rw [abs_of_nonneg hsign] at hnear
    exact ⟨hz, h0, h1, by linarith⟩)
  have hm := hcount q χ (-t) (G.filter (fun ρ => ¬ 0 ≤ ρ.im)) (by
    intro ρ hρ
    obtain ⟨hg, hsign⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hzmem, hnear⟩ := Finset.mem_filter.mp hg
    obtain ⟨hz, h0, h1, _⟩ := (hZ ρ).mp hzmem
    rw [abs_of_neg (lt_of_not_ge hsign)] at hnear
    refine ⟨hz, h0, h1, ?_⟩
    have he : ρ.im - -t = -(-ρ.im - t) := by ring
    rw [he, abs_neg]
    linarith)
  rw [abs_neg] at hm
  have hsplit := Finset.sum_filter_add_sum_filter_not G (fun ρ : ℂ => 0 ≤ ρ.im)
    (fun ρ => (mult χ ρ : ℝ))
  have hmass : ∑ ρ ∈ G, (mult χ ρ : ℝ) ≤ 2 * A * L := by
    have hp' := hp.trans (mul_le_mul_of_nonneg_left hlog hA)
    have hm' := hm.trans (mul_le_mul_of_nonneg_left hlog hA)
    linarith
  have hpos (ρ : ℂ) (hρ : ρ ∈ G) : 1 ≤ mult χ ρ := by
    have hz := ((hZ ρ).mp (Finset.mem_filter.mp hρ).1).1
    have hAn (z : ℂ) : AnalyticAt ℂ (DirichletCharacter.LFunction χ) z :=
      (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
    have hU : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ := fun z _ => hAn z
    have h2 : analyticOrderAt (DirichletCharacter.LFunction χ) 2 ≠ ⊤ := by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)))]
      simp
    have htop := hU.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := 2) (y := ρ) (by simp) (by simp) h2
    have hne := analyticOrderAt_ne_zero.mpr ⟨hAn ρ, hz⟩
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
    unfold mult analyticOrderNatAt
    rw [← hm, ENat.toNat_natCast]
    rw [← hm] at hne
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)
  have hcardG : (G.card : ℝ) ≤ 2 * A * L := by
    calc (G.card : ℝ) = ∑ _ρ ∈ G, (1 : ℝ) := by simp
      _ ≤ ∑ ρ ∈ G, (mult χ ρ : ℝ) :=
        Finset.sum_le_sum (fun ρ hρ => by exact_mod_cast hpos ρ hρ)
      _ ≤ _ := hmass
  have hcardHG : (H.card : ℝ) ≤ (G.card : ℝ) := by
    exact_mod_cast (Finset.card_image_le (s := G) (f := fun ρ => |ρ.im|))
  have hcardH : (H.card : ℝ) ≤ 2 * A * L := hcardHG.trans hcardG
  let δ : ℝ := 1 / (4 * ((H.card : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ4 : δ ≤ 1 / 4 := by
    dsimp [δ]
    apply one_div_le_one_div_of_le (by norm_num)
    have hc : (0 : ℝ) ≤ H.card := Nat.cast_nonneg _
    linarith
  have hbudget : 1 / (4 * (2 * A + 1 / Real.log 6) * L) ≤ δ := by
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : 1 ≤ (1 / Real.log 6) * L := by
      rw [one_div_mul_eq_div, le_div_iff₀ hl6]
      simpa only [one_mul] using hL6
    nlinarith
  obtain ⟨U, hU, haway⟩ := finite_good_height541 H T
  refine ⟨U, hU, ?_⟩
  intro ρ hz h0 h1
  apply hbudget.trans
  by_cases hnear : |(|ρ.im|) - t| ≤ 3 / 4
  · have hmem : |ρ.im| ∈ H := by
      apply Finset.mem_image.mpr
      refine ⟨ρ, Finset.mem_filter.mpr ⟨?_, hnear⟩, rfl⟩
      apply (hZ ρ).mpr
      refine ⟨hz, h0, h1, ?_⟩
      have hh := (abs_le.mp hnear).2
      dsimp [t] at hh
      linarith
    have hh := haway |ρ.im| hmem
    rw [abs_sub_comm] at hh
    exact hh
  · have htri := abs_sub_le |ρ.im| U t
    have hut : |U - t| ≤ 1 / 2 := by
      rw [abs_le]
      dsimp [t]
      constructor <;> linarith [hU.1, hU.2]
    have hnear' : 3 / 4 < |(|ρ.im|) - t| := lt_of_not_ge hnear
    linarith

/-- Numerical absorption for Davenport page 117 display 6 in the task window.
All three error terms are absorbed into log squared of X. -/
theorem davenport_log_budget592 {X q n : ℕ} [NeZero q] (hX : 2 ≤ X)
    (hq : q ≤ Nat.sqrt X) (hn : 1 ≤ n) (hnX : n ≤ X)
    {T : ℝ} (hT : T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ))) :
    (n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 + Real.log q + Real.log n ≤
        20 * Real.log X ^ 2 ∧
      Real.log (2 * (q : ℝ)) ≤ 4 * Real.log X ^ 2 ∧
      Real.log ((q : ℝ) * (T + 2)) ≤ 8 * Real.log X ^ 2 := by
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqX : (q : ℝ) ≤ X := by exact_mod_cast hq.trans (Nat.sqrt_le_self X)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnXr : (n : ℝ) ≤ X := by exact_mod_cast hnX
  have hT0 : 0 < T := by linarith [hT.1]
  have hL : 1 / 2 ≤ Real.log X := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hXr
    linarith [Real.log_two_gt_d9]
  have hqlog : Real.log q ≤ Real.log X := Real.log_le_log (by linarith) hqX
  have hnlog : Real.log n ≤ Real.log X := Real.log_le_log (by linarith) hnXr
  have hprod0 : 1 ≤ (q : ℝ) * n * T := by
    have hqn : (1 : ℝ) ≤ (q : ℝ) * n := one_le_mul_of_one_le_of_one_le hq1 hn1
    exact one_le_mul_of_one_le_of_one_le hqn (by linarith [hT.1])
  have hprod : (q : ℝ) * n * T ≤ (X : ℝ) ^ 4 := by
    calc (q : ℝ) * n * T ≤ ((X : ℝ) * X) * (2 * X) :=
          mul_le_mul (mul_le_mul hqX hnXr (by positivity) (by positivity)) hT.2
            (by positivity) (by positivity)
      _ ≤ (X : ℝ) ^ 4 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hXr) (by positivity : (0 : ℝ) ≤ (X : ℝ) ^ 3)]
  have hprodlog : Real.log ((q : ℝ) * n * T) ≤ 4 * Real.log X := by
    calc Real.log ((q : ℝ) * n * T) ≤ Real.log ((X : ℝ) ^ 4) :=
          Real.log_le_log (by linarith) hprod
      _ = 4 * Real.log X := by rw [Real.log_pow]; norm_num
  have hprodlog0 : 0 ≤ Real.log ((q : ℝ) * n * T) := Real.log_nonneg hprod0
  have hratio : (n : ℝ) / T ≤ 1 := (div_le_one hT0).mpr (hnXr.trans hT.1)
  have hsquare : Real.log ((q : ℝ) * n * T) ^ 2 ≤ 16 * Real.log X ^ 2 := by
    nlinarith
  have hratio2 := mul_le_mul_of_nonneg_right hratio (sq_nonneg (Real.log ((q : ℝ) * n * T)))
  have hlow : Real.log (2 * (q : ℝ)) ≤ 2 * Real.log X := by
    calc Real.log (2 * (q : ℝ)) ≤ Real.log ((X : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
      _ = 2 * Real.log X := by rw [Real.log_pow]; norm_num
  have hedge : Real.log ((q : ℝ) * (T + 2)) ≤ 4 * Real.log X := by
    have harg : (q : ℝ) * (T + 2) ≤ (X : ℝ) ^ 4 := by
      calc (q : ℝ) * (T + 2) ≤ (X : ℝ) * (2 * X + 2) :=
            mul_le_mul hqX (by linarith [hT.2]) (by linarith) (by positivity)
        _ ≤ (X : ℝ) ^ 4 := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (X : ℝ) - 2)
            (by positivity : (0 : ℝ) ≤ (X : ℝ) ^ 3 + 2 * (X : ℝ) ^ 2 + 2 * X + 2)]
    calc Real.log ((q : ℝ) * (T + 2)) ≤ Real.log ((X : ℝ) ^ 4) :=
          Real.log_le_log (by positivity) harg
      _ = 4 * Real.log X := by rw [Real.log_pow]; norm_num
  constructor
  · nlinarith
  constructor <;> nlinarith

end LeanLab.BhowmikGrimmelt2026
