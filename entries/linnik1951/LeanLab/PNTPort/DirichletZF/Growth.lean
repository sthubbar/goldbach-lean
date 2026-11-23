module

public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.MellinTransform
import Mathlib

/-!
# Growth of `L(s, χ)` in the half plane `Re s > 0`, `χ` non-principal

Lab proof, unit U-5110. AI wrote this file. Known mathematics, no cited input.

For a non-principal Dirichlet character `χ` mod `N`:
* `norm_sum_Icc_le`: `‖∑_{1 ≤ k ≤ n} χ(k)‖ ≤ N` for every `n`;
* `LFunction_eq_integral`: `L(s, χ) = s ∫_1^∞ A(t) t^{-s-1} dt` for `Re s > 0`, where
  `A(t) = ∑_{1 ≤ k ≤ t} χ(k)`, by partial summation on `Re s > 1` and the identity theorem;
* `norm_LFunction_le`: `‖L(s, χ)‖ ≤ N ‖s‖ / Re s` for `Re s > 0`.
This is the growth input the Borel-Caratheodory route to a zero-free region needs.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Finset Filter Asymptotics MeasureTheory Set
open scoped LSeries.notation

variable {N : ℕ}

/-- A function on `ℕ` of period `N` has the same sum over every block of `N` consecutive
integers. -/
lemma sum_range_shift_of_periodic {M : Type*} [AddCommGroup M] (f : ℕ → M)
    (hf : ∀ n, f (n + N) = f n) (m : ℕ) :
    ∑ k ∈ range N, f (m + k) = ∑ k ∈ range N, f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    obtain ⟨M', rfl⟩ : ∃ M', N = M' + 1 := ⟨N - 1, by omega⟩
    rw [sum_range_succ, sum_range_succ' (fun k ↦ f (m + k))]
    have : f (m + 1 + M') = f (m + (M' + 1)) := by ring_nf
    rw [this, show m + (M' + 1) = m + (M' + 1) from rfl]
    have hp : f (m + (M' + 1)) = f m := hf m
    rw [hp]
    simp only [add_zero]
    have : ∀ k, f (m + 1 + k) = f (m + (k + 1)) := fun k ↦ by ring_nf
    simp only [this]

/-- A full period of a non-principal character sums to zero. -/
lemma sum_range_eq_zero [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∑ k ∈ range N, χ k = 0 := by
  rw [← MulChar.sum_eq_zero_of_ne_one hχ]
  refine sum_nbij' (fun i : ℕ ↦ (i : ZMod N)) (fun a ↦ a.val) ?_ ?_ ?_ ?_ ?_
  · intro i _; exact mem_univ _
  · intro a _; exact mem_range.mpr (ZMod.val_lt a)
  · intro i hi; exact ZMod.val_cast_of_lt (mem_range.mp hi)
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro i _; rfl

/-- Partial sums of a non-principal character are at most `N` in norm. -/
lemma norm_sum_range_le [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ range n, χ k‖ ≤ N := by
  have hper : ∀ m, ∑ k ∈ range (m + N), χ k = ∑ k ∈ range m, χ k := by
    intro m
    rw [sum_range_add, sum_range_shift_of_periodic (fun k ↦ χ k)
      (fun k ↦ by simp) m, sum_range_eq_zero hχ, add_zero]
  have hmod : ∀ n, ∑ k ∈ range n, χ k = ∑ k ∈ range (n % N), χ k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < N
      · rw [Nat.mod_eq_of_lt hn]
      · push Not at hn
        have hN := Nat.pos_of_ne_zero (NeZero.ne N)
        have e : n = (n - N) + N := by omega
        rw [e, hper, ih _ (by omega), Nat.add_mod_right]
  rw [hmod]
  calc ‖∑ k ∈ range (n % N), χ k‖ ≤ ∑ k ∈ range (n % N), ‖χ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range (n % N), (1 : ℝ) := sum_le_sum fun k _ ↦ DirichletCharacter.norm_le_one χ k
    _ = (n % N : ℕ) := by simp
    _ ≤ N := by exact_mod_cast (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))).le

/-- The same over `Icc 1 n`. -/
lemma norm_sum_Icc_le [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Icc 1 n, χ k‖ ≤ N := by
  have h0 : ∑ k ∈ range (n + 1), χ k = χ 0 + ∑ k ∈ Icc 1 n, χ k := by
    rw [sum_range_succ', ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.cast_zero]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun k _ ↦ by rw [add_comm 1 k]
  have hz : χ (0 : ZMod N) = 0 ∨ N = 1 := by
    rcases eq_or_ne N 1 with h | h
    · exact Or.inr h
    · left
      have : ¬ IsUnit (0 : ZMod N) := by
        have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr h
        exact not_isUnit_zero
      exact χ.map_nonunit this
  rcases hz with hz | hN
  · have := norm_sum_range_le hχ (n + 1)
    rwa [h0, hz, zero_add] at this
  · subst hN
    exact absurd (Subsingleton.elim χ 1) hχ

/-- `A(t) = ∑_{1 ≤ k ≤ t} χ(k)`. -/
noncomputable def A (χ : DirichletCharacter ℂ N) (t : ℝ) : ℂ := ∑ k ∈ Icc 1 ⌊t⌋₊, χ k

lemma norm_A_le [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) :
    ‖A χ t‖ ≤ N := norm_sum_Icc_le hχ _

lemma measurable_A (χ : DirichletCharacter ℂ N) : Measurable (A χ) :=
  (measurable_from_nat (f := fun n : ℕ ↦ ∑ k ∈ Icc 1 n, χ k)).comp Nat.measurable_floor

/-- The cut off partial sum function, `A` on `(1, ∞)` and `0` elsewhere. -/
noncomputable def g (χ : DirichletCharacter ℂ N) : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (A χ)

/-- The integral in the representation, as a Mellin transform. -/
lemma integral_eq_mellin (χ : DirichletCharacter ℂ N) (s : ℂ) :
    ∫ t in Ioi (1 : ℝ), A χ t * (t : ℂ) ^ (-(s + 1)) = mellin (g χ) (-s) := by
  rw [mellin]
  have : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • g χ t =
      (Ioi (1 : ℝ)).indicator (fun t ↦ A χ t * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp only [g, indicator_of_mem ht, smul_eq_mul]
      rw [mul_comm]; congr 2; ring
    · simp [g, indicator_of_notMem ht]
  simp_rw [this]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi]
  simp

lemma differentiableAt_mellin_g [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (mellin (g χ)) (-s) := by
  have hmeas : Measurable (g χ) := (measurable_A χ).indicator measurableSet_Ioi
  have hbdd : ∀ t, ‖g χ t‖ ≤ N := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp only [g, indicator_of_mem ht]; exact norm_A_le hχ t
    · simp [g, indicator_of_notMem ht]
  refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    refine ⟨Ioi 0 ∩ Iio (x + 1), inter_mem_nhdsWithin _ (Iio_mem_nhds (by linarith)), ?_⟩
    refine Measure.integrableOn_of_bounded (M := N) ?_ hmeas.aestronglyMeasurable
      (Eventually.of_forall hbdd)
    rw [Ioi_inter_Iio, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  · refine IsBigO.of_bound N (Eventually.of_forall fun t ↦ ?_)
    simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]; exact hbdd t
  · simpa using hs
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have : t ∉ Ioi (1 : ℝ) := fun h ↦ by
      rw [Set.mem_Ioi] at h; linarith [ht.2]
    simp only [g, indicator_of_notMem this]
  · simp

/-- Partial summation on `Re s > 1`. -/
lemma LSeries_eq_integral [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries ↗χ s = s * ∫ t in Ioi (1 : ℝ), A χ t * (t : ℂ) ^ (-(s + 1)) := by
  have hS : LSeriesSummable ↗χ s :=
    (DirichletCharacter.LSeriesSummable_iff (NeZero.ne N) χ).mpr hs
  have hO : (fun n ↦ ∑ k ∈ Icc 1 n, (↗χ : ℕ → ℂ) k) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
    refine IsBigO.of_bound N (Eventually.of_forall fun n ↦ ?_)
    simp only [Real.rpow_zero, norm_one, mul_one]
    exact norm_sum_Icc_le hχ n
  rw [LSeries_eq_mul_integral _ le_rfl (by linarith) hS hO]
  rfl

/-- The integral representation on `Re s > 0`. -/
theorem LFunction_eq_integral [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = s * ∫ t in Ioi (1 : ℝ), A χ t * (t : ℂ) ^ (-(s + 1)) := by
  set U : Set ℂ := {z | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ (fun z ↦ z * mellin (g χ) (-z)) U := by
    intro z hz
    refine (differentiableAt_id.mul ?_).differentiableWithinAt
    exact (differentiableAt_mellin_g hχ hz).comp z differentiableAt_id.neg
  have hL : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have hconv : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by simp [hU]
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds 2] fun z ↦ z * mellin (g χ) (-z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz, LSeries_eq_integral hχ hz,
      integral_eq_mellin]
  have := (hL.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hF.analyticOnNhd hUo)
    hconv h2 hev hs
  rw [this, integral_eq_mellin]

/-- `‖L(s, χ)‖ ≤ N ‖s‖ / Re s` for `Re s > 0`, `χ` non-principal. -/
theorem norm_LFunction_le [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ N * ‖s‖ / s.re := by
  rw [LFunction_eq_integral hχ hs, norm_mul]
  have hint : IntegrableOn (fun t : ℝ ↦ (N : ℝ) * t ^ (-(s.re + 1))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have hle : ‖∫ t in Ioi (1 : ℝ), A χ t * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Ioi (1 : ℝ), (N : ℝ) * t ^ (-(s.re + 1)) := by
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have : (-(s + 1)).re = -(s.re + 1) := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (norm_A_le hχ t) (Real.rpow_nonneg ht0.le _)
  have hval : ∫ t in Ioi (1 : ℝ), (N : ℝ) * t ^ (-(s.re + 1)) = N / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    simp only [Real.one_rpow]
    have : s.re ≠ 0 := hs.ne'
    rw [show -(s.re + 1) + 1 = -s.re by ring]
    field_simp
  calc ‖s‖ * ‖∫ t in Ioi (1 : ℝ), A χ t * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * (N / s.re) := by rw [← hval]; exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = N * ‖s‖ / s.re := by ring

end LeanLab.PNTPort.DirichletZF

