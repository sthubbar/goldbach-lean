module

public import LeanLab.BhowmikGrimmelt2026.Statements
public import LeanLab.PNTPort.Perron.Sinc

/-!
Source checks and elementary support for the sharp primitive explicit formula.
P0029 page 11 display 3.5 is smoothed. The sharp route uses Davenport chapter 19.
The reciprocal zero terms at small height must be retained before absorption.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Davenport chapter 19, the Gamma factor has no zero in the right half plane. -/
theorem gamma_factor_ne_zero541 {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  classical
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith

/-- Davenport chapter 19, reflection of a primitive strip zero to the inverse character. -/
theorem primitive_zero_reflection541 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    simpa [h] using h0
  have hc : DirichletCharacter.completedLFunction χ ρ = 0 := by
    have h := χ.LFunction_eq_completed_div_gammaFactor ρ (Or.inl hρ0)
    rw [hρ] at h
    exact (div_eq_zero_iff).mp h.symm |>.resolve_right (gamma_factor_ne_zero541 χ h0)
  have hi : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  have he := hi.completedLFunction_one_sub ρ
  simp only [inv_inv, hc, mul_zero] at he
  have hr : 1 - ρ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (Or.inl hr), he, zero_div]


/-- Davenport chapter 19, strip reflection turns an upper zero bound into a lower bound. -/
theorem primitive_zero_re_lower541 {Θ : ℝ} (hZ : ZeroBound Θ)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : 1 - Θ ≤ ρ.re := by
  have hr := primitive_zero_reflection541 χ hχ hρ h0 h1
  have h := hZ q χ⁻¹ (1 - ρ) hr (by simp; linarith) (by simp; linarith)
  simp only [Complex.sub_re, Complex.one_re] at h
  linarith

/-- The zero bound below three quarters keeps primitive zeros away from the origin. -/
theorem primitive_zero_norm_lower541 {Θ : ℝ} (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : 1 / 4 < ‖ρ‖ := by
  have h := primitive_zero_re_lower541 hZ χ hχ hρ h0 h1
  have hn : ρ.re ≤ ‖ρ‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  linarith

/-- Davenport chapter 19, every reciprocal primitive zero has norm at most four. -/
theorem primitive_zero_inv_bound541 {Θ : ℝ} (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ‖ρ⁻¹‖ ≤ 4 := by
  have hn := primitive_zero_norm_lower541 hΘ hZ χ hχ hρ h0 h1
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖ρ‖)).mpr
  linarith

/-- Finite low zero reciprocal sums cost at most four times their total multiplicity. -/
theorem primitive_low_zero_sum541 {Θ : ℝ} (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZspec : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) :
    ‖∑ ρ ∈ Z, (m ρ : ℂ) / ρ‖ ≤ 4 * ∑ ρ ∈ Z, (m ρ : ℝ) := by
  calc
    _ ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) / ρ‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ Z, 4 * (m ρ : ℝ) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨hz, h0, h1⟩ := hZspec ρ hρ
      have hi := primitive_zero_inv_bound541 hΘ hZ χ hχ hz h0 h1
      rw [div_eq_mul_inv, norm_mul, Complex.norm_natCast]
      calc
        (m ρ : ℝ) * ‖ρ⁻¹‖ ≤ (m ρ : ℝ) * 4 :=
          mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)
        _ = _ := mul_comm _ _
    _ = _ := by rw [Finset.mul_sum]


/-- Davenport chapter 19, the paired high zero term has a square summable majorant. -/
theorem paired_zero_reciprocal_bound541 {ρ : ℂ} (hρ : 1 ≤ |ρ.im|) :
    ‖1 / ρ + 1 / (2 - ρ)‖ ≤ 4 / (1 + ρ.im ^ 2) := by
  have hn : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm _
  have hn2 : |ρ.im| ≤ ‖(2 : ℂ) - ρ‖ := by
    simpa using Complex.abs_im_le_norm ((2 : ℂ) - ρ)
  have hp : 0 < |ρ.im| := lt_of_lt_of_le zero_lt_one hρ
  have h0 : ρ ≠ 0 := norm_pos_iff.mp (hp.trans_le hn)
  have h2 : (2 : ℂ) - ρ ≠ 0 := norm_pos_iff.mp (hp.trans_le hn2)
  have hmul : ρ.im ^ 2 ≤ ‖ρ‖ * ‖(2 : ℂ) - ρ‖ := by
    calc
      _ = |ρ.im| * |ρ.im| := by rw [← sq_abs]; ring
      _ ≤ _ := mul_le_mul hn hn2 (abs_nonneg _) (norm_nonneg _)
  have hs : 1 ≤ ρ.im ^ 2 := by nlinarith [sq_abs ρ.im]
  have he : 1 / ρ + 1 / (2 - ρ) = 2 / (ρ * (2 - ρ)) := by
    field_simp
    ring
  rw [he, norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_div_iff₀ (by positivity : 0 < ‖ρ‖ * ‖(2 : ℂ) - ρ‖)
    (by positivity : 0 < 1 + ρ.im ^ 2)).mpr
  nlinarith



/-- Davenport chapter 17, the vertical Perron kernel at its jump. -/
theorem integral_vertical_reciprocal541 {c : ℝ} (hc : 0 < c) (T : ℝ) :
    (∫ t : ℝ in -T..T, ((c : ℂ) + (t : ℂ) * Complex.I)⁻¹) =
      (2 * Real.arctan (T / c) : ℝ) := by
  have hne (t : ℝ) : (c : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hi : IntervalIntegrable
      (fun t : ℝ => ((c : ℂ) + (t : ℂ) * Complex.I)⁻¹)
      MeasureTheory.volume (-T) T :=
    ((by fun_prop : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I)).inv₀ hne).intervalIntegrable _ _
  have hr := Complex.reCLM.intervalIntegral_comp_comm hi
  have hm := Complex.imCLM.intervalIntegral_comp_comm hi
  simp only [Complex.reCLM_apply] at hr
  simp only [Complex.imCLM_apply] at hm
  apply Complex.ext
  · rw [← hr]
    simp only [Complex.inv_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self,
      add_zero, Complex.normSq_add_mul_I]
    rw [integral_div_sq_add_sq, neg_div, Real.arctan_neg]
    ring
  · rw [← hm]
    simp only [Complex.inv_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
      zero_add, Complex.normSq_add_mul_I, neg_div]
    rw [intervalIntegral.integral_neg, integral_id_div_sq_add_sq hc.ne']
    simp

/-- Davenport chapter 17, the error at the Perron jump is at most c over pi T. -/
theorem perron_jump_bound541 {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖(1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ in -T..T, ((c : ℂ) + (t : ℂ) * Complex.I)⁻¹) - 1 / 2‖ ≤
      c / (Real.pi * T) := by
  rw [integral_vertical_reciprocal541 hc]
  have he : (1 / (2 * Real.pi) : ℂ) * (2 * Real.arctan (T / c) : ℝ) - 1 / 2 =
      ((Real.arctan (T / c) / Real.pi - 1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  have ha := Real.arctan_inv_of_pos (div_pos hT hc)
  rw [inv_div] at ha
  have hh : Real.arctan (T / c) / Real.pi - 1 / 2 =
      -Real.arctan (c / T) / Real.pi := by
    field_simp
    linarith
  rw [hh, abs_div, abs_neg, abs_of_pos Real.pi_pos,
    abs_of_nonneg (Real.arctan_nonneg.mpr (div_pos hc hT).le)]
  calc
    _ ≤ (c / T) / Real.pi :=
      div_le_div_of_nonneg_right (Real.arctan_le_self (div_pos hc hT).le) Real.pi_pos.le
    _ = _ := by ring


open MeasureTheory

/-- Davenport chapter 19, the finite interval exclusion step in choosing a good height. -/
theorem finite_good_height541 (G : Finset ℝ) (X : ℝ) :
    ∃ T ∈ Set.Icc X (X + 1), ∀ γ ∈ G,
      1 / (4 * ((G.card : ℝ) + 1)) ≤ |T - γ| := by
  let δ : ℝ := 1 / (4 * ((G.card : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let U : Set ℝ := ⋃ γ ∈ G, Set.Ioo (γ - δ) (γ + δ)
  have hfin : volume U ≠ ⊤ := by
    apply measure_biUnion_ne_top G.finite_toSet
    intro γ hγ
    simp only [Real.volume_Ioo, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
  have hvol (γ : ℝ) : volume.real (Set.Ioo (γ - δ) (γ + δ)) = 2 * δ := by
    rw [Real.volume_real_Ioo]
    have he : γ + δ - (γ - δ) = 2 * δ := by ring
    rw [he, max_eq_left (by positivity)]
  have hU : volume.real U ≤ (G.card : ℝ) * (2 * δ) := by
    have h := measureReal_biUnion_finset_le (μ := volume) G
      (fun γ => Set.Ioo (γ - δ) (γ + δ))
    simpa only [hvol, Finset.sum_const, nsmul_eq_mul] using h
  have hsmall : (G.card : ℝ) * (2 * δ) < 1 := by
    have hd : 0 < 4 * ((G.card : ℝ) + 1) := by positivity
    have h := (div_lt_iff₀ hd).mpr
      (show (G.card : ℝ) * 2 < 1 * (4 * ((G.card : ℝ) + 1)) by
        have hcard : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
        nlinarith)
    convert h using 1; dsimp [δ]; ring
  have hnot : ¬ Set.Icc X (X + 1) ⊆ U := by
    intro h
    have hv := measureReal_mono (μ := volume) h hfin
    have hI : volume.real (Set.Icc X (X + 1)) = 1 := by
      rw [Real.volume_real_Icc]
      norm_num
    rw [hI] at hv
    linarith
  simp only [Set.subset_def, not_forall] at hnot
  obtain ⟨T, hT, hTU⟩ := hnot
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra h
  have ha : |T - γ| < δ := lt_of_not_ge h
  apply hTU
  simp only [U, Set.mem_iUnion, Set.mem_Ioo]
  refine ⟨γ, hγ, ?_, ?_⟩ <;> have hb := abs_lt.mp ha <;> linarith

/-- Davenport chapter 19, one finite exclusion controls both horizontal sides. -/
theorem finite_symmetric_good_height541 (G : Finset ℂ) {X : ℝ} (hX : 0 ≤ X) :
    ∃ T ∈ Set.Icc X (X + 1), ∀ ρ ∈ G,
      1 / (4 * ((G.card : ℝ) + 1)) ≤ |T - ρ.im| ∧
      1 / (4 * ((G.card : ℝ) + 1)) ≤ |-T - ρ.im| := by
  classical
  let H : Finset ℝ := G.image (fun ρ => |ρ.im|)
  obtain ⟨T, hT, haway⟩ := finite_good_height541 H X
  have ht : 0 ≤ T := hX.trans hT.1
  have hcard : (H.card : ℝ) ≤ (G.card : ℝ) := by
    exact_mod_cast (Finset.card_image_le : H.card ≤ G.card)
  have hδ : 1 / (4 * ((G.card : ℝ) + 1)) ≤ 1 / (4 * ((H.card : ℝ) + 1)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  refine ⟨T, hT, ?_⟩
  intro ρ hρ
  have h := hδ.trans (haway |ρ.im| (Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩))
  constructor
  · exact h.trans (by simpa only [abs_of_nonneg ht] using abs_abs_sub_abs_le_abs_sub T ρ.im)
  · exact h.trans (by simpa only [abs_neg, abs_of_nonneg ht] using abs_abs_sub_abs_le_abs_sub (-T) ρ.im)



/-- CONDITIONAL on the displayed partial fraction correction and multiplicity count.
Davenport chapter 19, absorption of the low zero correction after those inputs. -/
theorem b_term_bound541 {Θ : ℝ} (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZspec : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
    (b : ℂ) (A B : ℝ)
    (hcount : (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ B * Real.log (q + 2))
    (hpartial : ‖b + ∑ ρ ∈ Z, (m ρ : ℂ) / ρ‖ ≤ A * Real.log (q + 2)) :
    ‖b‖ ≤ (A + 4 * B) * Real.log (q + 2) := by
  have hz := primitive_low_zero_sum541 hΘ hZ χ hχ Z m hZspec
  have he : b = (b + ∑ ρ ∈ Z, (m ρ : ℂ) / ρ) -
      (∑ ρ ∈ Z, (m ρ : ℂ) / ρ) := by ring
  calc
    _ = ‖(b + ∑ ρ ∈ Z, (m ρ : ℂ) / ρ) - (∑ ρ ∈ Z, (m ρ : ℂ) / ρ)‖ := congrArg norm he
    _ ≤ ‖b + ∑ ρ ∈ Z, (m ρ : ℂ) / ρ‖ + ‖∑ ρ ∈ Z, (m ρ : ℂ) / ρ‖ := norm_sub_le _ _
    _ ≤ A * Real.log (q + 2) + 4 * ∑ ρ ∈ Z, (m ρ : ℝ) := add_le_add hpartial hz
    _ ≤ A * Real.log (q + 2) + 4 * (B * Real.log (q + 2)) := by gcongr
    _ = _ := by ring



/-- Davenport chapter 17, integration by parts for the finite vertical Perron tail. -/
theorem perron_tail_parts541 {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z ≠ 0)
    (T U : ℝ) :
    (∫ t : ℝ in T..U, Complex.exp (z * t) / ((c : ℂ) + t * Complex.I)) =
      Complex.exp (z * U) / (z * ((c : ℂ) + U * Complex.I)) -
      Complex.exp (z * T) / (z * ((c : ℂ) + T * Complex.I)) +
      Complex.I / z * ∫ t : ℝ in T..U,
        Complex.exp (z * t) / ((c : ℂ) + t * Complex.I) ^ 2 := by
  have hne (t : ℝ) : (c : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hu (t : ℝ) : HasDerivAt
      (fun t : ℝ => ((c : ℂ) + t * Complex.I)⁻¹)
      (-Complex.I / ((c : ℂ) + t * Complex.I) ^ 2) t := by
    have hd : HasDerivAt (fun w : ℂ => (c : ℂ) + w * Complex.I) Complex.I (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (c : ℂ)
    exact (hd.inv (hne t)).comp_ofReal
  have hv (t : ℝ) : HasDerivAt
      (fun t : ℝ => Complex.exp (z * t) / z) (Complex.exp (z * t)) t := by
    have h := (((hasDerivAt_id (t : ℂ)).const_mul z).cexp.div_const z).comp_ofReal
    simpa [hz] using h
  have hu' : IntervalIntegrable
      (fun t : ℝ => -Complex.I / ((c : ℂ) + t * Complex.I) ^ 2)
      MeasureTheory.volume T U := by
    apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) (fun t => pow_ne_zero 2 (hne t))
  have hv' : IntervalIntegrable (fun t : ℝ => Complex.exp (z * t))
      MeasureTheory.volume T U := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => hu t) (fun t _ => hv t) hu' hv'
  have hleft : (∫ t : ℝ in T..U,
      ((c : ℂ) + t * Complex.I)⁻¹ * Complex.exp (z * t)) =
      ∫ t : ℝ in T..U, Complex.exp (z * t) / ((c : ℂ) + t * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hright : (∫ t : ℝ in T..U,
      (-Complex.I / ((c : ℂ) + t * Complex.I) ^ 2) *
        (Complex.exp (z * t) / z)) =
      -(Complex.I / z) * ∫ t : ℝ in T..U,
        Complex.exp (z * t) / ((c : ℂ) + t * Complex.I) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hleft, hright] at h
  convert h using 1; simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- Davenport chapter 17, an explicit finite tail estimate for the oscillating Perron kernel. -/
theorem perron_tail_bound541 {c a T U : ℝ} (hc : 0 < c) (ha : a ≠ 0)
    (hT : 0 < T) (hTU : T ≤ U) :
    ‖∫ t : ℝ in T..U, Complex.exp (((a : ℂ) * Complex.I) * t) /
      ((c : ℂ) + t * Complex.I)‖ ≤ 2 / (|a| * T) := by
  let z : ℂ := (a : ℂ) * Complex.I
  have hz : z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) Complex.I_ne_zero
  have hza : ‖z‖ = |a| := by simp [z, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hap : 0 < |a| := abs_pos.mpr ha
  have hne (t : ℝ) : (c : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have he (t : ℝ) : ‖Complex.exp (z * t)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [z, Complex.mul_re, Complex.mul_im]
  have hd (t : ℝ) (ht : 0 < t) : t ≤ ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
    simpa [abs_of_pos ht] using Complex.abs_im_le_norm ((c : ℂ) + (t : ℂ) * Complex.I)
  have hF : Continuous (fun t : ℝ =>
      Complex.exp (z * t) / ((c : ℂ) + t * Complex.I) ^ 2) :=
    (by fun_prop : Continuous (fun t : ℝ => Complex.exp (z * t))).div
      (by fun_prop) (fun t => pow_ne_zero 2 (hne t))
  have hmaj : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹)
      MeasureTheory.volume T U := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTU
    exact (continuousOn_pow 2).inv₀ (fun t ht => pow_ne_zero 2 (ne_of_gt (hT.trans_le ht.1)))
  have hR : ‖∫ t : ℝ in T..U, Complex.exp (z * t) /
      ((c : ℂ) + t * Complex.I) ^ 2‖ ≤ T⁻¹ - U⁻¹ := by
    calc
      _ ≤ ∫ t : ℝ in T..U,
          ‖Complex.exp (z * t) / ((c : ℂ) + t * Complex.I) ^ 2‖ :=
        intervalIntegral.norm_integral_le_integral_norm hTU
      _ ≤ ∫ t : ℝ in T..U, (t ^ 2)⁻¹ := by
        apply intervalIntegral.integral_mono_on hTU (hF.norm.intervalIntegrable _ _) hmaj
        intro t ht
        have ht0 := hT.trans_le ht.1
        rw [norm_div, norm_pow, he, one_div]
        exact inv_anti₀ (sq_pos_of_pos ht0)
          (pow_le_pow_left₀ ht0.le (hd t ht0) 2)
      _ = _ := LeanLab.PNTPort.Perron.intervalIntegral_inv_sq_of_pos hT hTU
  have hE (t : ℝ) (ht : 0 < t) :
      ‖Complex.exp (z * t) / (z * ((c : ℂ) + t * Complex.I))‖ ≤ 1 / (|a| * t) := by
    rw [norm_div, norm_mul, he, hza]
    exact one_div_le_one_div_of_le (mul_pos hap ht)
      (mul_le_mul_of_nonneg_left (hd t ht) hap.le)
  have hcoef : ‖Complex.I / z‖ = 1 / |a| := by rw [norm_div, Complex.norm_I, hza]
  have hp := perron_tail_parts541 hc hz T U
  change ‖∫ t : ℝ in T..U, Complex.exp (z * t) / ((c : ℂ) + t * Complex.I)‖ ≤ _
  rw [hp]
  calc
    _ ≤ (‖Complex.exp (z * U) / (z * ((c : ℂ) + U * Complex.I))‖ +
        ‖Complex.exp (z * T) / (z * ((c : ℂ) + T * Complex.I))‖) +
        ‖Complex.I / z‖ * ‖∫ t : ℝ in T..U,
          Complex.exp (z * t) / ((c : ℂ) + t * Complex.I) ^ 2‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (le_of_eq (norm_mul _ _)))
    _ ≤ (1 / (|a| * U) + 1 / (|a| * T)) + (1 / |a|) * (T⁻¹ - U⁻¹) := by
      rw [hcoef]
      exact add_le_add (add_le_add (hE U (hT.trans_le hTU)) (hE T hT))
        (mul_le_mul_of_nonneg_left hR (by positivity))
    _ = _ := by field_simp; ring

/-- Davenport chapter 17, the finite Perron tail for the actual complex power kernel. -/
theorem perron_cpow_tail_bound541 {y c T U : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
    (hc : 0 < c) (hT : 0 < T) (hTU : T ≤ U) :
    ‖∫ t : ℝ in T..U, (y : ℂ) ^ ((c : ℂ) + t * Complex.I) /
      ((c : ℂ) + t * Complex.I)‖ ≤ 2 * y ^ c / (T * |Real.log y|) := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have he (t : ℝ) : (y : ℂ) ^ ((c : ℂ) + t * Complex.I) =
      ((y ^ c : ℝ) : ℂ) * Complex.exp (((Real.log y : ℂ) * Complex.I) * t) := by
    rw [Complex.cpow_add _ _ hyc, ← Complex.ofReal_cpow hy.le c,
      Complex.cpow_def_of_ne_zero hyc, ← Complex.ofReal_log hy.le]
    congr 2
    ring
  simp_rw [he, mul_div_assoc]
  rw [intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hy c)]
  have h := perron_tail_bound541 hc (Real.log_ne_zero_of_pos_of_ne_one hy hy1) hT hTU
  calc
    _ ≤ y ^ c * (2 / (|Real.log y| * T)) :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hy.le _)
    _ = _ := by ring


/-- Davenport chapter 19, a quantitative local count gives an explicit good height radius. -/
theorem good_height_of_count541 (G : Finset ℂ) {X L A : ℝ}
    (hX : 1 ≤ X) (hL : 1 ≤ L) (hA : 0 ≤ A) (hcount : (G.card : ℝ) ≤ A * L) :
    ∃ T ∈ Set.Icc X (2 * X), ∀ ρ ∈ G,
      1 / (4 * (A + 1) * L) ≤ |T - ρ.im| ∧
      1 / (4 * (A + 1) * L) ≤ |-T - ρ.im| := by
  obtain ⟨T, hT, haway⟩ := finite_symmetric_good_height541 G (by linarith : 0 ≤ X)
  have hcard : 4 * ((G.card : ℝ) + 1) ≤ 4 * (A + 1) * L := by nlinarith
  have hδ : 1 / (4 * (A + 1) * L) ≤ 1 / (4 * ((G.card : ℝ) + 1)) :=
    one_div_le_one_div_of_le (by positivity) hcard
  refine ⟨T, ⟨hT.1, by linarith [hT.2]⟩, ?_⟩
  intro ρ hρ
  exact ⟨hδ.trans (haway ρ hρ).1, hδ.trans (haway ρ hρ).2⟩

/-- Davenport chapter 17, the symmetric finite Perron integrals have a reciprocal height tail. -/
theorem perron_symmetric_tail_bound541 {y c T U : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
    (hc : 0 < c) (hT : 0 < T) (hTU : T ≤ U) :
    ‖(∫ t : ℝ in -U..U, (y : ℂ) ^ ((c : ℂ) + t * Complex.I) /
        ((c : ℂ) + t * Complex.I)) -
      (∫ t : ℝ in -T..T, (y : ℂ) ^ ((c : ℂ) + t * Complex.I) /
        ((c : ℂ) + t * Complex.I))‖ ≤ 4 * y ^ c / (T * |Real.log y|) := by
  let f : ℝ → ℂ := fun t => (y : ℂ) ^ ((c : ℂ) + t * Complex.I) /
    ((c : ℂ) + t * Complex.I)
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hne (t : ℝ) : (c : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hF : Continuous f :=
    ((by fun_prop : Continuous (fun t : ℝ => (c : ℂ) + t * Complex.I)).const_cpow
      (Or.inl hyc)).div (by fun_prop) hne
  have harg : (y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]
    exact ne_of_lt Real.pi_pos
  have hconj (t : ℝ) : f (-t) = (starRingEnd ℂ) (f t) := by
    dsimp [f]
    rw [map_div₀]
    congr 1
    · have h := Complex.cpow_conj (y : ℂ) ((c : ℂ) + t * Complex.I) harg
      simpa using h
    · simp
  have hnegative : (∫ t : ℝ in -U..-T, f t) =
      (starRingEnd ℂ) (∫ t : ℝ in T..U, f t) := by
    rw [← intervalIntegral.integral_comp_neg (f := f) (a := T) (b := U)]
    simp_rw [hconj]
    exact intervalIntegral.intervalIntegral_conj
  have hp := perron_cpow_tail_bound541 hy hy1 hc hT hTU
  change ‖∫ t : ℝ in T..U, f t‖ ≤ _ at hp
  have hn : ‖∫ t : ℝ in -U..-T, f t‖ ≤ 2 * y ^ c / (T * |Real.log y|) := by
    rw [hnegative, Complex.norm_conj]
    exact hp
  change ‖(∫ t : ℝ in -U..U, f t) - (∫ t : ℝ in -T..T, f t)‖ ≤ _
  rw [intervalIntegral.integral_interval_sub_interval_comm
    (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _),
    intervalIntegral.integral_symm T U, sub_neg_eq_add]
  calc
    _ ≤ ‖∫ t : ℝ in -U..-T, f t‖ + ‖∫ t : ℝ in T..U, f t‖ := norm_add_le _ _
    _ ≤ 2 * y ^ c / (T * |Real.log y|) + 2 * y ^ c / (T * |Real.log y|) := add_le_add hn hp
    _ = _ := by ring


/-- Davenport chapter 17, the finite Perron tails make the symmetric integrals Cauchy. -/
theorem perron_symmetric_cauchy541 {y c : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c) :
    CauchySeq (fun n : ℕ => ∫ t : ℝ in -(n : ℝ)..(n : ℝ),
      (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)) := by
  let K : ℝ := 4 * y ^ c / |Real.log y|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hinv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hb : Filter.Tendsto (fun n : ℕ => K * (n : ℝ)⁻¹) Filter.atTop (nhds 0) := by
    simpa using hinv.const_mul K
  apply LeanLab.PNTPort.Perron.cauchySeq_of_dist_le_of_one_le
    (fun n => mul_nonneg hK (inv_nonneg.mpr (Nat.cast_nonneg n))) hb
  intro n m hn hnm
  rw [dist_eq_norm]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := perron_symmetric_tail_bound541 hy hy1 hc (by linarith : (0 : ℝ) < n)
    (by exact_mod_cast hnm : (n : ℝ) ≤ m)
  convert h using 1; dsimp [K]; ring

/-- Davenport chapter 17, the Perron kernel limit exists with an explicit truncation error.
This does not identify the limit with its step value. -/
theorem perron_limit_exists541 {y c : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c) :
    ∃ L : ℂ, Filter.Tendsto (fun n : ℕ => ∫ t : ℝ in -(n : ℝ)..(n : ℝ),
      (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I))
      Filter.atTop (nhds L) ∧ ∀ n : ℕ, 1 ≤ n →
        ‖(∫ t : ℝ in -(n : ℝ)..(n : ℝ), (y : ℂ) ^ ((c : ℂ) + t * Complex.I) /
          ((c : ℂ) + t * Complex.I)) - L‖ ≤ 4 * y ^ c / ((n : ℝ) * |Real.log y|) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (perron_symmetric_cauchy541 hy hy1 hc)
  refine ⟨L, hL, ?_⟩
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbound : ‖L - (∫ t : ℝ in -(n : ℝ)..(n : ℝ),
      (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I))‖ ≤
      4 * y ^ c / ((n : ℝ) * |Real.log y|) := by
    apply le_of_tendsto (hL.sub_const _).norm
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact perron_symmetric_tail_bound541 hy hy1 hc (by linarith : (0 : ℝ) < n)
      (by exact_mod_cast hm : (n : ℝ) ≤ m)
  rwa [norm_sub_rev] at hbound



/-- Davenport chapter 19, the sharp and half weighted character sums differ by half a log. -/
theorem sharp_half_weight_error541 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖(∑ m ∈ Finset.range (n + 1),
        (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
      ((∑ m ∈ Finset.range n,
        (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
        (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q))‖ ≤
      Real.log n / 2 := by
  rw [Finset.sum_range_succ]
  have he (A v : ℂ) : A + v - (A + (1 / 2 : ℂ) * v) = (1 / 2 : ℂ) * v := by ring
  rw [mul_assoc (1 / 2 : ℂ), he]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have hχ := χ.norm_le_one (n : ZMod q)
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log
  nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n)]



/-- The quarter power remainder in the variable modulus formula cannot be absorbed by log squared.
This compares error budgets and does not refute the sharp formula under a zero bound. -/
theorem quarter_log_exceeds_log_sq541 (C R : ℝ) :
    ∃ x : ℝ, 2 ≤ x ∧ R ≤ x ∧
      C * Real.log x ^ 2 < x ^ (1 / 4 : ℝ) * Real.log x := by
  let t : ℝ := 16 * (|C| + |R| + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht16 : 16 ≤ t := by dsimp [t]; nlinarith [abs_nonneg C, abs_nonneg R]
  have h8 : 8 * C < t := by dsimp [t]; nlinarith [le_abs_self C, abs_nonneg C, abs_nonneg R]
  have hexp : t ^ 2 / 2 ≤ Real.exp t := by
    have h := Real.pow_div_factorial_le_exp t ht.le 2
    norm_num at h
    exact h
  have hdom : 4 * C * t < Real.exp t := by
    have hh : 0 < t * (t - 8 * C) := mul_pos ht (sub_pos.mpr h8)
    nlinarith
  refine ⟨Real.exp (4 * t), ?_, ?_, ?_⟩
  · have h := Real.add_one_le_exp (4 * t)
    linarith
  · have h := Real.add_one_le_exp (4 * t)
    have hR : R ≤ |R| := le_abs_self R
    dsimp [t] at h
    nlinarith [abs_nonneg C, abs_nonneg R]
  · have hp : (Real.exp (4 * t)) ^ (1 / 4 : ℝ) = Real.exp t := by
      rw [← Real.exp_mul]
      congr 1
      ring
    rw [Real.log_exp, hp]
    have h := mul_lt_mul_of_pos_right hdom (show 0 < 4 * t by positivity)
    nlinarith


end LeanLab.BhowmikGrimmelt2026
