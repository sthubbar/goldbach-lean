module

public import LeanLab.Tolev2009.Base314a
public import LeanLab.Tolev2009.Decomp314b
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 pages 6 to 8, discrete partial summation.
-/

@[expose] public section

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.Progression346
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp286a LeanLab.Tolev2009.Decomp314a
open LeanLab.Tolev2009.Displays14to16

/-- Halupczok page 7, the rational main coefficient in the prime convention. -/
noncomputable def mainCoeff (k l q a : ℕ) : ℂ := localSum k l q a / (k.totient : ℂ)

/-- Halupczok page 7, the rational prime coefficient minus its constant main term.
The zero index contributes zero. -/
noncomputable def atom (k l q a m : ℕ) : ℂ :=
  (if m.Prime ∧ m % k = l % k then (Real.log m : ℂ) * ee ((a : ℝ) / q * m) else 0) -
    if m = 0 then 0 else mainCoeff k l q a

/-- Halupczok pages 6 to 7, maximal rational prefix discrepancy through N.
This retains the exact prime polynomial and its rational coefficient. -/
noncomputable def prefixError (k l q a N : ℕ) : ℝ :=
  (range (N + 1)).sup' (by simp) (fun m => ‖∑ n ∈ range (m + 1), atom k l q a n‖)

/-- Halupczok page 7, a single exponential increment has a linear norm bound. -/
theorem ee_increment (β : ℝ) (m : ℕ) :
    ‖ee (β * (m + 1)) - ee (β * m)‖ ≤ 2 * π * |β| := by
  have he : ee (β * (m + 1)) - ee (β * m) = ee (β * m) * (ee β - 1) := by
    rw [mul_sub, mul_one, ← ee_add]
    congr 2
    ring
  rw [he, norm_mul, norm_ee, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * β)
  have hex : ee β = Complex.exp (Complex.I * (2 * π * β : ℝ)) := by
    unfold ee
    congr 1
    push_cast
    ring
  rw [hex]
  simpa [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos] using h

/-- Halupczok page 7, discrete Abel summation for any bounded prefix sequence. -/
theorem phase_sum_bound (u : ℕ → ℂ) (N : ℕ) (β D : ℝ)
    (hD : 0 ≤ D) (hu : ∀ m ≤ N, ‖∑ n ∈ range (m + 1), u n‖ ≤ D) :
    ‖∑ n ∈ range (N + 1), ee (β * n) * u n‖ ≤
      (1 + 2 * π * |β| * N) * D := by
  have hab := sum_range_by_parts (fun n : ℕ => ee (β * n)) u (N + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hab
  rw [hab]
  calc
    _ ≤ ‖ee (β * N) * ∑ n ∈ range (N + 1), u n‖ +
        ‖∑ i ∈ range N, (ee (β * (i + 1)) - ee (β * i)) *
          ∑ n ∈ range (i + 1), u n‖ := norm_sub_le _ _
    _ ≤ D + ∑ _i ∈ range N, (2 * π * |β|) * D := by
      apply add_le_add
      · simpa only [norm_mul, norm_ee, one_mul] using hu N le_rfl
      · refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
        rw [norm_mul]
        exact mul_le_mul (ee_increment β i) (hu i (Nat.le_of_lt (mem_range.mp hi))) (norm_nonneg _) (by positivity)
    _ = (1 + 2 * π * |β| * N) * D := by simp; ring

/-- Halupczok page 6, the maximal prefix error is nonnegative. -/
theorem prefixError_nonneg (k l q a N : ℕ) : 0 ≤ prefixError k l q a N :=
by
  unfold prefixError
  exact (norm_nonneg _).trans (Finset.le_sup'
    (fun m => ‖∑ n ∈ range (m + 1), atom k l q a n‖)
    (show 0 ∈ range (N + 1) by simp))

/-- Halupczok page 6, every permitted prefix is bounded by the finite maximum. -/
theorem prefix_le (k l q a N m : ℕ) (hm : m ≤ N) :
    ‖∑ n ∈ range (m + 1), atom k l q a n‖ ≤ prefixError k l q a N := by
  unfold prefixError
  exact Finset.le_sup' (fun m => ‖∑ n ∈ range (m + 1), atom k l q a n‖)
    (show m ∈ range (N + 1) from mem_range.mpr (by omega))

/-- Halupczok page 7, rewriting a positive prefix as a zero based finite sum. -/
theorem positive_sum (N : ℕ) (f : ℕ → ℂ) :
    (∑ m ∈ range (N + 1), if m = 0 then 0 else f m) = ∑ m ∈ Icc 1 N, f m := by
  have hs : (range (N + 1)).filter (fun m => m ≠ 0) = Icc 1 N := by
    ext m
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  rw [← hs, sum_filter]
  apply sum_congr rfl
  intro m _
  split_ifs <;> simp_all

/-- Halupczok page 7, the exact finite polynomial to which Abel summation applies. -/
theorem residual_eq_sum (k l N q a : ℕ) (β : ℝ) :
    residual k l N q a β =
      ∑ m ∈ range (N + 1), ee (β * m) * atom k l q a m := by
  have hm : (∑ m ∈ range (N + 1),
      ee (β * m) * (if m = 0 then 0 else mainCoeff k l q a)) =
      mainCoeff k l q a * geometric N β := by
    simp_rw [mul_ite, mul_zero]
    rw [positive_sum]
    simp only [geometric, mul_sum]
    apply sum_congr rfl
    intro m _
    ring
  simp only [atom, mul_sub, sum_sub_distrib]
  rw [hm]
  unfold Decomp314a.residual approx mainCoeff
  congr 1
  simp only [Sexp, sum_filter]
  apply sum_congr rfl
  intro m _
  split_ifs
  · rw [← mul_assoc, mul_comm (ee _) _, mul_assoc, ← ee_add]
    congr 2
    ring
  · simp

/-- Halupczok page 7, partial summation controls the exact prime residual. -/
theorem residual_bound (k l N q a : ℕ) (β : ℝ) :
    ‖residual k l N q a β‖ ≤
      (1 + 2 * π * |β| * N) * prefixError k l q a N := by
  rw [residual_eq_sum]
  exact phase_sum_bound _ N β _ (prefixError_nonneg k l q a N)
    (fun m hm => prefix_le k l q a N m hm)

/-- Halupczok page 8, the positive polynomial of homogeneous error bounds. -/
noncomputable def positivePart (j : ℕ) (b d : Fin 3 → ℝ) : ℝ :=
  if j = 1 then d 0 * b 1 * b 2 + b 0 * d 1 * b 2 + b 0 * b 1 * d 2
  else if j = 2 then d 0 * d 1 * b 2 + d 0 * b 1 * d 2 + b 0 * d 1 * d 2
  else if j = 3 then d 0 * d 1 * d 2 else 0

/-- Halupczok page 8, the positive polynomial has nonnegative coefficients. -/
theorem positivePart_nonneg (j : ℕ) (b d : Fin 3 → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hd : ∀ i, 0 ≤ d i) : 0 ≤ positivePart j b d := by
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  unfold positivePart
  split_ifs <;> positivity

/-- Halupczok page 8, triangle inequality separately in each homogeneous degree. -/
theorem homogeneous_norm_le (j : ℕ) (b d : Fin 3 → ℂ) (B D : Fin 3 → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hD : ∀ i, 0 ≤ D i)
    (hb : ∀ i, ‖b i‖ ≤ B i) (hd : ∀ i, ‖d i‖ ≤ D i) :
    ‖homogeneous j b d‖ ≤ positivePart j B D := by
  have hB0 := hB 0
  have hB1 := hB 1
  have hB2 := hB 2
  have hD0 := hD 0
  have hD1 := hD 1
  have hD2 := hD 2
  unfold homogeneous positivePart
  split_ifs
  · calc
      _ ≤ (‖d 0 * b 1 * b 2‖ + ‖b 0 * d 1 * b 2‖) + ‖b 0 * b 1 * d 2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by simp only [norm_mul]; gcongr <;> first | apply hb | apply hd | apply hB | apply hD | positivity
  · calc
      _ ≤ (‖d 0 * d 1 * b 2‖ + ‖d 0 * b 1 * d 2‖) + ‖b 0 * d 1 * d 2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by simp only [norm_mul]; gcongr <;> first | apply hb | apply hd | apply hB | apply hD | positivity
  · simp only [norm_mul]
    gcongr <;> first | apply hd | apply hD | positivity
  · simp

/-- Halupczok page 7, the elementary geometric polynomial bound. -/
theorem geometric_norm_le (N : ℕ) (β : ℝ) : ‖geometric N β‖ ≤ N := by
  calc
    _ ≤ ∑ m ∈ Icc 1 N, ‖ee (β * m)‖ := norm_sum_le _ _
    _ = N := by simp [norm_ee, Nat.card_Icc]

/-- Halupczok page 8, uniform main term bound on an individual arc. -/
theorem approx_norm_le (k l N q a : ℕ) (β : ℝ) :
    ‖approx k l N q a β‖ ≤ (N : ℝ) * ‖mainCoeff k l q a‖ := by
  simpa only [approx, mainCoeff, norm_mul, mul_comm] using
    mul_le_mul_of_nonneg_left (geometric_norm_le N β) (norm_nonneg (mainCoeff k l q a))

/-- Halupczok pages 7 to 8, the bound after fixing the arc radius. -/
theorem residual_radius_bound (k l N q a : ℕ) (β r : ℝ) (hβ : |β| ≤ r) :
    ‖residual k l N q a β‖ ≤
      (1 + 2 * π * r * N) * prefixError k l q a N := by
  refine (residual_bound k l N q a β).trans ?_
  gcongr
  exact prefixError_nonneg _ _ _ _ _

/-- Halupczok page 8, a static positive bound for one rational arc.
It has no beta variable or integral. The absolute radius includes either orientation. -/
noncomputable def arcEnvelope (j : ℕ) (τ : ℝ) (k l : Fin 3 → ℕ) (N q a : ℕ) : ℝ :=
  (2 * |1 / ((q : ℝ) * τ)|) * positivePart j
    (fun i => (N : ℝ) * ‖mainCoeff (k i) (l i) q a‖)
    (fun i => (1 + 2 * π * |1 / ((q : ℝ) * τ)| * N) *
      prefixError (k i) (l i) q a N)

/-- Halupczok pages 8 to 11, the static positive sum before progression averaging. -/
noncomputable def errorEnvelope (j : ℕ) (Q τ : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    arcEnvelope j τ k l N q a

/-- Halupczok page 8, every static arc envelope is nonnegative. -/
theorem arcEnvelope_nonneg (j : ℕ) (τ : ℝ) (k l : Fin 3 → ℕ) (N q a : ℕ) :
    0 ≤ arcEnvelope j τ k l N q a := by
  unfold arcEnvelope
  apply mul_nonneg (by positivity)
  apply positivePart_nonneg
  · intro i; positivity
  · intro i; exact mul_nonneg (by positivity) (prefixError_nonneg _ _ _ _ _)

/-- Halupczok page 8, the full static error envelope is nonnegative. -/
theorem errorEnvelope_nonneg (j : ℕ) (Q τ : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) :
    0 ≤ errorEnvelope j Q τ k l N := by
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => arcEnvelope_nonneg _ _ _ _ _ _ _

/-- Halupczok page 8, the absolute value of a point in a symmetric arc. -/
theorem abs_le_radius (s β : ℝ) (hβ : β ∈ Set.uIoc (-s) s) : |β| ≤ |s| := by
  have hh := Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hβ)
  rcases hh with hh | hh
  · exact abs_le.mpr ⟨(neg_le_neg (le_abs_self s)).trans hh.1, hh.2.trans (le_abs_self s)⟩
  · exact abs_le.mpr ⟨(neg_abs_le s).trans hh.1, hh.2.trans (neg_le_abs s)⟩

/-- Halupczok page 8, removing one continuous arc integral by the static bound. -/
theorem local_error_bound (j : ℕ) (τ : ℝ) (k l : Fin 3 → ℕ) (N q a : ℕ) :
    ‖∫ β in (-1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)),
      homogeneous j (fun i => approx (k i) (l i) N q a β)
        (fun i => residual (k i) (l i) N q a β) *
          ee (-((N : ℝ) * ((a : ℝ) / q + β)))‖ ≤ arcEnvelope j τ k l N q a := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -1 / ((q : ℝ) * τ)) (b := 1 / ((q : ℝ) * τ))
    (C := positivePart j
      (fun i => (N : ℝ) * ‖mainCoeff (k i) (l i) q a‖)
      (fun i => (1 + 2 * π * |1 / ((q : ℝ) * τ)| * N) *
        prefixError (k i) (l i) q a N))
    (f := fun β => homogeneous j (fun i => approx (k i) (l i) N q a β)
      (fun i => residual (k i) (l i) N q a β) *
        ee (-((N : ℝ) * ((a : ℝ) / q + β)))) (by
      intro β hβ
      rw [norm_mul, norm_ee, mul_one]
      apply homogeneous_norm_le
      · intro i; positivity
      · intro i; exact mul_nonneg (by positivity) (prefixError_nonneg _ _ _ _ _)
      · intro i; exact approx_norm_le _ _ _ _ _ _
      · intro i
        apply residual_radius_bound
        apply abs_le_radius
        simpa only [neg_div] using hβ)
  have hlen : |1 / ((q : ℝ) * τ) - -1 / ((q : ℝ) * τ)| = 2 * |1 / ((q : ℝ) * τ)| := by
    rw [show 1 / ((q : ℝ) * τ) - -1 / ((q : ℝ) * τ) = 2 * (1 / ((q : ℝ) * τ)) by ring, abs_mul]
    norm_num
  rw [hlen] at hb
  simpa only [arcEnvelope, mul_comm] using hb

/-- Halupczok page 8, triangle inequality over rational arcs. -/
theorem errorTerm_bound (j : ℕ) (Q τ : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) :
    |errorTerm j Q τ k l N| ≤ errorEnvelope j Q τ k l N := by
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro q hq
  exact (norm_sum_le _ _).trans (sum_le_sum fun a ha => local_error_bound j τ k l N q a)

/-- Halupczok page 8, bounded weights and maxima transfer to the positive static average. -/
theorem error_mean_bound (j : ℕ) (A : ℝ) (lam : ℕ → ℝ) (l₃ N : ℕ)
    (hlam : ∀ k, |lam k| ≤ 1) :
    EF (fun k l => errorTerm j (Qof A N) (τof A N) k l N) lam l₃ (10 ^ 4 * A) N ≤
      EF (fun k l => errorEnvelope j (Qof A N) (τof A N) k l N)
        (fun _ => 1) l₃ (10 ^ 4 * A) N := by
  simpa only [one_mul] using Decomp314b.EF_dominate
    (fun k l => errorTerm j (Qof A N) (τof A N) k l N)
    (fun k l => errorEnvelope j (Qof A N) (τof A N) k l N)
    lam l₃ (10 ^ 4 * A) 1 N hlam (by norm_num)
    (fun k l => errorEnvelope_nonneg _ _ _ _ _ _)
    (by intro k l hk hl; simpa only [one_mul] using errorTerm_bound j (Qof A N) (τof A N) k l N)

end LeanLab.Tolev2009.Progression346
