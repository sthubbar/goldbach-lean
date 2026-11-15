module

public import LeanLab.Tolev2009.Base314a
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
AI wrote this Lean code. Codex task314.
Binary Goldbach is open.
Source: Halupczok 2008 page 11, the finite geometric singular integral.
The unit interval identity retains the exact lattice endpoint correction.
-/

@[expose] public section

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.Integral314
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp286a LeanLab.Tolev2009.Decomp314a

/-- Halupczok page 11, expand the cubic geometric integrand into integer frequencies. -/
theorem geometric_cube_expand (N : ℕ) (β : ℝ) :
    geometric N β ^ 3 * ee (-((N : ℝ) * β)) =
      ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ w ∈ Icc 1 N,
        ee ((((u : ℤ) + v + w - N : ℤ) : ℝ) * β) := by
  simp only [geometric, pow_succ, pow_zero, one_mul, sum_mul, mul_sum]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  apply sum_congr rfl
  intro w hw
  rw [← ee_add, ← ee_add, ← ee_add]
  congr 1
  push_cast
  ring

/-- Halupczok page 11, the full unit singular integral counts positive lattice triples. -/
theorem full_geometric_integral (N : ℕ) :
    (∫ β in (-1 / 2 : ℝ)..(1 / 2 : ℝ), geometric N β ^ 3 * ee (-((N : ℝ) * β))) =
      ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N, ∑ w ∈ Icc 1 N,
        (if u + v + w = N then (1 : ℂ) else 0) := by
  simp_rw [geometric_cube_expand]
  have hc (u v w : ℕ) : Continuous (fun β : ℝ =>
      ee ((((u : ℤ) + v + w - N : ℤ) : ℝ) * β)) :=
    continuous_ee.comp (continuous_const.mul continuous_id)
  rw [intervalIntegral.integral_finsetSum (fun u _ =>
    (continuous_finsetSum _ fun v _ => continuous_finsetSum _ fun w _ => hc u v w).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro u hu
  rw [intervalIntegral.integral_finsetSum (fun v _ =>
    (continuous_finsetSum _ fun w _ => hc u v w).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro v hv
  rw [intervalIntegral.integral_finsetSum (fun w _ => (hc u v w).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro w hw
  have h := integral_ee (-1 / 2) ((u : ℤ) + v + w - N)
  have ht : (-1 / 2 : ℝ) + 1 = 1 / 2 := by ring
  rw [ht] at h
  rw [h]
  have hiff : ((u : ℤ) + v + w - N = 0) ↔ u + v + w = N := by omega
  simp only [hiff]

/-- Halupczok page 11, one positive frequency is determined by the other two. -/
theorem positive_triple_inner (N u v : ℕ) :
    (∑ w ∈ Icc 1 N, if u + v + w = N then (1 : ℂ) else 0) =
      if u + v < N then 1 else 0 := by
  by_cases h : u + v < N
  · have hw : N - u - v ∈ Icc 1 N := mem_Icc.mpr (by omega)
    have he : ∀ w : ℕ, u + v + w = N ↔ w = N - u - v := by omega
    simp_rw [he]
    simp [h, hw, sum_ite_eq']
  · rw [if_neg h]
    apply sum_eq_zero
    intro w hw
    have h0 : u + v + w ≠ N := by have := mem_Icc.mp hw; omega
    simp [h0]

/-- Halupczok page 11, the number of positive choices for the second frequency. -/
theorem positive_triple_middle (N u : ℕ) :
    (∑ v ∈ Icc 1 N, if u + v < N then (1 : ℂ) else 0) = (N - u - 1 : ℕ) := by
  have hf : (Icc 1 N).filter (fun v => u + v < N) = Icc 1 (N - u - 1) := by
    ext v
    simp only [mem_filter, mem_Icc]
    omega
  rw [← sum_filter, hf]
  simp

/-- Halupczok page 11, exact lattice count form of the full singular integral. -/
theorem full_integral_lattice_count (N : ℕ) :
    (∫ β in (-1 / 2 : ℝ)..(1 / 2 : ℝ), geometric N β ^ 3 * ee (-((N : ℝ) * β))) =
      ∑ u ∈ Icc 1 N, ((N - u - 1 : ℕ) : ℂ) := by
  rw [full_geometric_integral]
  simp_rw [positive_triple_inner, positive_triple_middle]

/-- Halupczok page 11, add the next row of positive lattice points. -/
theorem positive_triple_recurrence (N : ℕ) :
    (∑ u ∈ Icc 1 (N + 1), ((N + 1 - u - 1 : ℕ) : ℂ)) =
      (∑ u ∈ Icc 1 N, ((N - u - 1 : ℕ) : ℂ)) + (N - 1 : ℕ) := by
  rw [sum_Icc_succ_top (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.sub_self, Nat.zero_sub, Nat.cast_zero, add_zero]
  have hp : ∀ u ∈ Icc 1 N,
      ((N + 1 - u - 1 : ℕ) : ℂ) = ((N - u - 1 : ℕ) : ℂ) +
        if u < N then 1 else 0 := by
    intro u hu
    have hu' := mem_Icc.mp hu
    by_cases h : u < N
    · have hh : N + 1 - u - 1 = N - u - 1 + 1 := by omega
      simp [h, hh]
    · have hh : u = N := by omega
      simp [hh]
  rw [sum_congr rfl hp, sum_add_distrib]
  congr 1
  simpa using positive_triple_middle N 0

/-- Halupczok page 11, the full lattice singular integral for N equal to n plus two. -/
theorem full_integral_closed (n : ℕ) :
    (∫ β in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      geometric (n + 2) β ^ 3 * ee (-(((n + 2 : ℕ) : ℝ) * β))) =
      (n : ℂ) * (n + 1) / 2 := by
  rw [full_integral_lattice_count]
  induction n with
  | zero =>
    norm_num only [Nat.zero_add, Nat.cast_zero, zero_mul, zero_div]
    apply sum_eq_zero
    intro u hu
    have hu' := mem_Icc.mp hu
    have hz : 2 - u - 1 = 0 := by omega
    simp [hz]
  | succ n ih =>
    have h : n + 1 + 2 = (n + 2) + 1 := by omega
    rw [h, positive_triple_recurrence, ih]
    rw [show n + 2 - 1 = n + 1 by omega]
    push_cast
    ring

/-- Halupczok page 11, the endpoint correction to N squared over two is at most 2N. -/
theorem full_integral_endpoint_error (N : ℕ) :
    ‖(∫ β in (-1 / 2 : ℝ)..(1 / 2 : ℝ), geometric N β ^ 3 * ee (-((N : ℝ) * β))) -
      ((N : ℂ) ^ 2 / 2)‖ ≤ 2 * N := by
  rcases N with _ | N
  · simp [geometric]
  rcases N with _ | n
  · rw [full_integral_lattice_count]
    norm_num
  have hN : n + 1 + 1 = n + 2 := by omega
  simp only [hN]
  rw [full_integral_closed]
  have he : (n : ℂ) * (n + 1) / 2 - ((n + 2 : ℕ) : ℂ) ^ 2 / 2 =
      ((-3 / 2 * ((n : ℝ) + 2) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Halupczok page 11, the geometric polynomial times its phase increment telescopes. -/
theorem geometric_mul_sub (N : ℕ) (β : ℝ) :
    geometric N β * (ee β - 1) = ee β * (ee β ^ N - 1) := by
  have hp (m : ℕ) : ee (β * m) = ee β ^ m := by
    unfold ee
    push_cast
    rw [show 2 * (π : ℂ) * Complex.I * ((β : ℂ) * m) =
      m * (2 * (π : ℂ) * Complex.I * β) by ring]
    exact Complex.exp_nat_mul _ _
  have hi : Icc 1 N = Ico 1 (N + 1) := by ext n; simp only [mem_Icc, mem_Ico]; omega
  unfold geometric
  simp_rw [hp]
  rw [hi, geom_sum_Ico_mul _ (by omega)]
  simp only [pow_one, pow_succ]
  ring

/-- Halupczok page 11, the phase increment is bounded below away from integer beta. -/
theorem phase_increment_lower (β : ℝ) (hβ : |β| ≤ 1 / 2) :
    4 * |β| ≤ ‖ee β - 1‖ := by
  have hsin := Real.mul_abs_le_abs_sin (x := π * β) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hc : 2 / π * (π * |β|) = 2 * |β| := by field_simp
  rw [hc] at hsin
  have he : ee β = Complex.exp (Complex.I * ((2 * π * β : ℝ) : ℂ)) := by
    unfold ee
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hh : (2 * π * β) / 2 = π * β := by ring
  rw [hh]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Halupczok page 11, the geometric polynomial is at most one over twice absolute beta. -/
theorem geometric_norm_bound (N : ℕ) (β : ℝ) (hβ0 : β ≠ 0) (hβ : |β| ≤ 1 / 2) :
    ‖geometric N β‖ ≤ 1 / (2 * |β|) := by
  have he := congrArg norm (geometric_mul_sub N β)
  simp only [norm_mul, LeanLab.Tolev2009.Displays14to16.norm_ee, one_mul] at he
  have hb : ‖geometric N β‖ * ‖ee β - 1‖ ≤ 2 := by
    rw [he]
    calc
      _ ≤ ‖ee β ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, LeanLab.Tolev2009.Displays14to16.norm_ee]
  have hd := mul_le_mul_of_nonneg_left (phase_increment_lower β hβ) (norm_nonneg (geometric N β))
  apply (le_div_iff₀ (by positivity : 0 < 2 * |β|)).mpr
  nlinarith

/-- Halupczok page 11, cube the geometric bound before estimating the omitted tails. -/
theorem geometric_cube_norm (N : ℕ) (β : ℝ) (hβ0 : β ≠ 0) (hβ : |β| ≤ 1 / 2) :
    ‖geometric N β ^ 3 * ee (-((N : ℝ) * β))‖ ≤ |β| ^ (-3 : ℤ) := by
  rw [norm_mul, norm_pow, LeanLab.Tolev2009.Displays14to16.norm_ee, mul_one]
  have hb := geometric_norm_bound N β hβ0 hβ
  have ha : 0 < |β| := abs_pos.mpr hβ0
  have hh : 1 / (2 * |β|) ≤ 1 / |β| := by
    apply one_div_le_one_div_of_le ha
    linarith
  calc
    _ ≤ (1 / (2 * |β|)) ^ 3 := by gcongr
    _ ≤ (1 / |β|) ^ 3 := by gcongr
    _ = _ := by simp [zpow_neg, div_pow]

/-- Halupczok page 11, integrate the reciprocal cube majorant on a positive tail. -/
theorem positive_tail_bound (f : ℝ → ℂ) (r : ℝ) (hr : 0 < r) (hrh : r ≤ 1 / 2)
    (hb : ∀ x ∈ Set.Ioc r (1 / 2), ‖f x‖ ≤ x ^ (-3 : ℤ)) :
    ‖∫ x in r..(1 / 2 : ℝ), f x‖ ≤ 1 / r ^ 2 := by
  have hzero : (0 : ℝ) ∉ Set.uIcc r (1 / 2) := by
    rw [Set.uIcc_of_le hrh]
    simp only [Set.mem_Icc, not_and_or, not_le]
    exact Or.inl hr
  have hi := intervalIntegral.intervalIntegrable_zpow (μ := volume) (n := (-3 : ℤ)) (Or.inr hzero)
  have hv : (∫ x in r..(1 / 2 : ℝ), x ^ (-3 : ℤ)) = ((r ^ 2)⁻¹ - 4) / 2 := by
    rw [integral_zpow (Or.inr ⟨by norm_num, hzero⟩)]
    norm_num [zpow_neg]
    ring
  calc
    _ ≤ ∫ x in r..(1 / 2 : ℝ), x ^ (-3 : ℤ) :=
      intervalIntegral.norm_integral_le_of_norm_le hrh (Filter.Eventually.of_forall hb) hi
    _ = ((r ^ 2)⁻¹ - 4) / 2 := hv
    _ ≤ _ := by
      rw [one_div]
      have hn : 0 ≤ (r ^ 2)⁻¹ := by positivity
      linarith

/-- Halupczok page 11, the two omitted geometric tails cost at most twice r to minus two. -/
theorem geometric_truncation_tail (N : ℕ) (r : ℝ) (hr : 0 < r) (hrh : r ≤ 1 / 2) :
    ‖(∫ β in (-1 / 2 : ℝ)..(1 / 2 : ℝ), geometric N β ^ 3 * ee (-((N : ℝ) * β))) -
      (∫ β in -r..r, geometric N β ^ 3 * ee (-((N : ℝ) * β)))‖ ≤ 2 / r ^ 2 := by
  let f : ℝ → ℂ := fun β => geometric N β ^ 3 * ee (-((N : ℝ) * β))
  have hc : Continuous f := (continuous_geometric N).pow 3 |>.mul (continuous_ee.comp (by fun_prop))
  have hsplit₁ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-1 / 2) (-r)) (hc.intervalIntegrable (-r) (1 / 2))
  have hsplit₂ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-r) r) (hc.intervalIntegrable r (1 / 2))
  have he : (∫ β in (-1 / 2 : ℝ)..(1 / 2 : ℝ), f β) - (∫ β in -r..r, f β) =
      (∫ β in (-1 / 2 : ℝ)..(-r), f β) + (∫ β in r..(1 / 2 : ℝ), f β) := by
    rw [← hsplit₁, ← hsplit₂]
    abel
  have hp : ‖∫ β in r..(1 / 2 : ℝ), f β‖ ≤ 1 / r ^ 2 := by
    apply positive_tail_bound f r hr hrh
    intro x hx
    have hx0 : 0 < x := hr.trans hx.1
    simpa only [f, abs_of_pos hx0] using geometric_cube_norm N x hx0.ne'
      (by simpa only [abs_of_pos hx0] using hx.2)
  have hm : ‖∫ β in r..(1 / 2 : ℝ), f (-β)‖ ≤ 1 / r ^ 2 := by
    apply positive_tail_bound (fun β => f (-β)) r hr hrh
    intro x hx
    have hx0 : 0 < x := hr.trans hx.1
    simpa only [f, abs_neg, abs_of_pos hx0] using geometric_cube_norm N (-x) (neg_ne_zero.mpr hx0.ne')
      (by simpa only [abs_neg, abs_of_pos hx0] using hx.2)
  have hn : (∫ β in r..(1 / 2 : ℝ), f (-β)) = (∫ β in (-1 / 2 : ℝ)..(-r), f β) := by
    rw [intervalIntegral.integral_comp_neg]
    congr 1
    ring
  rw [hn] at hm
  change ‖(∫ β in (-1 / 2 : ℝ)..(1 / 2 : ℝ), f β) - (∫ β in -r..r, f β)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  convert add_le_add hm hp using 1 <;> ring

/-- Halupczok page 11 and Tolev page 78, the complete finite geometric integral estimate.
The absolute constant four includes the exact lattice endpoint correction. -/
theorem geometric_integral_estimate (N q : ℕ) (τ : ℝ)
    (hq : 1 ≤ q) (hτ : 2 ≤ τ) (hN : (N : ℝ) ≤ τ ^ 2) :
    ‖arcIntegral τ N q - ((N : ℂ) ^ 2 / 2)‖ ≤ 4 * (q : ℝ) ^ 2 * τ ^ 2 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ht : 0 < (q : ℝ) * τ := by positivity
  let r : ℝ := 1 / ((q : ℝ) * τ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrh : r ≤ 1 / 2 := by
    dsimp [r]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hb := geometric_truncation_tail N r hr hrh
  have he := full_integral_endpoint_error N
  have hi : arcIntegral τ N q =
      ∫ β in -r..r, geometric N β ^ 3 * ee (-((N : ℝ) * β)) := by
    unfold arcIntegral r
    congr 1
    ring
  rw [hi]
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (∫ β in -r..r, geometric N β ^ 3 * ee (-((N : ℝ) * β)))
    (∫ β in (-1 / 2 : ℝ)..(1 / 2 : ℝ), geometric N β ^ 3 * ee (-((N : ℝ) * β)))
    ((N : ℂ) ^ 2 / 2)
  rw [norm_sub_rev (∫ β in -r..r, geometric N β ^ 3 * ee (-((N : ℝ) * β)))
    (∫ β in (-1 / 2 : ℝ)..(1 / 2 : ℝ), geometric N β ^ 3 * ee (-((N : ℝ) * β)))] at htri
  have hrpow : 2 / r ^ 2 = 2 * (q : ℝ) ^ 2 * τ ^ 2 := by
    dsimp [r]
    field_simp
  rw [hrpow] at hb
  have hn : (N : ℝ) ≤ (q : ℝ) ^ 2 * τ ^ 2 := by
    have hq2 : 0 ≤ (q : ℝ) ^ 2 - 1 := by nlinarith
    have hprod := mul_nonneg hq2 (sq_nonneg τ)
    nlinarith
  linarith

end LeanLab.Tolev2009.Integral314
