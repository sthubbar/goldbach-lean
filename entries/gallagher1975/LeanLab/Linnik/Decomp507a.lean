module

public import LeanLab.Perelli1996.InverseTotient320
public import LeanLab.PNTPort.BV.Helpers
public import LeanLab.Perelli1996.Totient400
public import LeanLab.Linnik.MajorArcEnergy.Leaves13PairWeight
public import LeanLab.BhowmikGrimmelt2026.Decomp443a

/-!
Gallagher 1975 pp.129 and130, arithmetic support for displays 5 and11.
Montgomery and Vaughan 1975 p.363 equations 6.13 and6.14.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp507a

open Finset Filter
open scoped Topology
open LeanLab.Perelli1996.InverseTotient320

/-- MV p.363 equation 6.13, the elementary weighted reciprocal totient sum. -/
theorem weighted_reciprocal_totient_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      ∑ q ∈ Icc 1 X, (q : ℝ) / (q.totient : ℝ) ^ 2 ≤
        C * (1 + Real.log X) := by
  let T : ℝ := ∑' d : ℕ, correction d / d
  have hT : 0 ≤ T := tsum_nonneg (fun d => by
    exact div_nonneg (correction_nonneg d) (Nat.cast_nonneg _))
  refine ⟨T + 1, by positivity, fun X => ?_⟩
  have heq : (∑ q ∈ Icc 1 X, (q : ℝ) / (q.totient : ℝ) ^ 2) =
      ∑ q ∈ Icc 1 X, ∑ d ∈ q.divisors,
        (correction d / d) * (1 / ((q / d : ℕ) : ℝ)) := by
    apply sum_congr rfl
    intro q hq
    have hq0 := (mem_Icc.mp hq).1
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    calc
      _ = (∑ d ∈ q.divisors, correction d) / q := by
        rw [sum_correction q hq0]
        field_simp
      _ = _ := by
        rw [sum_div]
        apply sum_congr rfl
        intro d hd
        have hdq := Nat.dvd_of_mem_divisors hd
        have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
        rw [Nat.cast_div hdq hd0]
        field_simp
  have hH : ∑ j ∈ Icc 1 X, (1 : ℝ) / j ≤ 1 + Real.log X := by
    have h := harmonic_le_one_add_log X
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simpa only [one_div] using h
  have hD : ∑ d ∈ Icc 1 X, correction d / d ≤ T :=
    summable_correction_div.sum_le_tsum _ (fun d _ =>
      div_nonneg (correction_nonneg d) (Nat.cast_nonneg _))
  rw [heq]
  calc
    _ ≤ (∑ d ∈ Icc 1 X, correction d / d) * ∑ j ∈ Icc 1 X, (1 : ℝ) / j :=
      LeanLab.PNTPort.BV.sum_divisors_le_mul X _ _
        (fun d => div_nonneg (correction_nonneg d) (Nat.cast_nonneg _))
        (fun j => by positivity)
    _ ≤ T * (1 + Real.log X) :=
      mul_le_mul hD hH (sum_nonneg fun _ _ => by positivity) hT
    _ ≤ (T + 1) * (1 + Real.log X) := by
      have := Real.log_natCast_nonneg X
      nlinarith

/-- MV p.363 equations 6.13 and6.14, the divisor interchange for a gcd weight. -/
theorem gcd_weight_swap (s : Finset ℕ) {n : ℕ} (hn : 0 < n) (w : ℕ → ℝ) :
    (∑ q ∈ s, (Nat.gcd q n : ℝ) * w q) =
      ∑ d ∈ n.divisors, (d.totient : ℝ) * ∑ q ∈ s with d ∣ q, w q := by
  have hdiv (q : ℕ) : (Nat.gcd q n).divisors = n.divisors.filter (fun d => d ∣ q) := by
    ext d
    have hg : Nat.gcd q n ≠ 0 := by
      simpa [Nat.gcd_comm] using (Nat.gcd_pos_of_pos_left q hn).ne'
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right q n), hn.ne'⟩, hd.trans (Nat.gcd_dvd_left q n)⟩
    · rintro ⟨⟨hdn, _⟩, hdq⟩
      exact ⟨Nat.dvd_gcd hdq hdn, hg⟩
  have hg (q : ℕ) : (Nat.gcd q n : ℝ) = ∑ d ∈ (Nat.gcd q n).divisors, (d.totient : ℝ) := by
    exact_mod_cast (Nat.sum_totient (Nat.gcd q n)).symm
  simp_rw [hg, hdiv, sum_filter, sum_mul, ite_mul, zero_mul, mul_sum,
    mul_ite, mul_zero]
  rw [sum_comm]

/-- MV p.363 equation 6.13, the contribution from multiples of one divisor. -/
theorem weighted_multiples_le (d X : ℕ) (hd : 0 < d) :
    ∑ q ∈ (Icc 1 X).filter (fun q => d ∣ q),
      (d.totient : ℝ) * ((q : ℝ) / (q.totient : ℝ) ^ 2) ≤
      ((d : ℝ) / d.totient) * ∑ j ∈ Icc 1 X, (j : ℝ) / (j.totient : ℝ) ^ 2 := by
  let S := (Icc 1 X).filter (fun q => d ∣ q)
  have hpoint (q : ℕ) (hq : q ∈ S) :
      (d.totient : ℝ) * ((q : ℝ) / (q.totient : ℝ) ^ 2) ≤
        ((d : ℝ) / d.totient) * (((q / d : ℕ) : ℝ) / ((q / d).totient : ℝ) ^ 2) := by
    obtain ⟨hqI, hdq⟩ := mem_filter.mp hq
    obtain ⟨j, rfl⟩ := hdq
    have hj : 0 < j := by have := (mem_Icc.mp hqI).1; nlinarith
    rw [Nat.mul_div_cancel_left _ hd]
    have hφd : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
    have hφj : (0 : ℝ) < j.totient := by exact_mod_cast Nat.totient_pos.mpr hj
    have hsup : (d.totient : ℝ) * j.totient ≤ (d * j).totient := by
      exact_mod_cast Nat.totient_super_multiplicative d j
    calc
      _ ≤ (d.totient : ℝ) * ((d * j : ℕ) : ℝ) /
          ((d.totient : ℝ) * j.totient) ^ 2 := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by positivity) hsup 2)
      _ = _ := by push_cast; field_simp <;> ring
  have hinj : Set.InjOn (fun q : ℕ => q / d) S := by
    intro a ha b hb hab
    have ha' := Nat.div_mul_cancel (mem_filter.mp ha).2
    have hb' := Nat.div_mul_cancel (mem_filter.mp hb).2
    dsimp only at hab
    rw [hab] at ha'
    omega
  have hsub : S.image (fun q => q / d) ⊆ Icc 1 X := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hj
    obtain ⟨hqI, hdq⟩ := mem_filter.mp hq
    have hq0 := (mem_Icc.mp hqI).1
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hq0 hdq) hd,
      (Nat.div_le_self q d).trans (mem_Icc.mp hqI).2⟩
  calc
    _ ≤ ∑ q ∈ S, ((d : ℝ) / d.totient) *
        (((q / d : ℕ) : ℝ) / ((q / d).totient : ℝ) ^ 2) := sum_le_sum hpoint
    _ = ((d : ℝ) / d.totient) * ∑ j ∈ S.image (fun q => q / d),
        (j : ℝ) / (j.totient : ℝ) ^ 2 := by rw [sum_image hinj, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) (by positivity)

/-- MV p.363 equation 6.13, the weighted gcd sum after the divisor interchange. -/
theorem weighted_gcd_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ (n X : ℕ), 0 < n →
      ∑ q ∈ Icc 1 X, (Nat.gcd q n : ℝ) * ((q : ℝ) / (q.totient : ℝ) ^ 2) ≤
        C * ((n : ℝ) / n.totient) * n.divisors.card * (1 + Real.log X) := by
  obtain ⟨C, hC, hsum⟩ := weighted_reciprocal_totient_sum
  refine ⟨C, hC, fun n X hn => ?_⟩
  rw [gcd_weight_swap _ hn]
  have hlog : 0 ≤ 1 + Real.log X := by have := Real.log_natCast_nonneg X; linarith
  calc
    _ ≤ ∑ d ∈ n.divisors, ((d : ℝ) / d.totient) * (C * (1 + Real.log X)) := by
      apply sum_le_sum
      intro d hd
      rw [mul_sum]
      exact (weighted_multiples_le d X (Nat.pos_of_mem_divisors hd)).trans
        (mul_le_mul_of_nonneg_left (hsum X) (by positivity))
    _ ≤ ∑ _d ∈ n.divisors, ((n : ℝ) / n.totient) * (C * (1 + Real.log X)) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right
        (LeanLab.Perelli1996.Totient400.divisor_totient_ratio_le d n hn
          (Nat.dvd_of_mem_divisors hd)) (mul_nonneg hC.le hlog)
    _ = _ := by simp; ring

/-- MV p.363 equation 6.14, the reciprocal totient tail along multiples of one divisor. -/
theorem totient_multiples_tail :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℝ), 0 < P → ∀ (d : ℕ), 0 < d →
      ∀ s : Finset ℕ, (∀ q ∈ s, 0 < q ∧ P < (q : ℝ)) →
      (d.totient : ℝ) * (∑ q ∈ s with d ∣ q, 1 / (q.totient : ℝ) ^ 2) ≤
        K * ((d : ℝ) / d.totient) / P := by
  obtain ⟨K, hK, htail⟩ := inverse_totient_sq_tail
  refine ⟨K, hK, fun P hP d hd s hs => ?_⟩
  let u := s.filter (fun q => d ∣ q)
  let t := u.image (fun q => q / d)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hdiv (q : ℕ) (hq : q ∈ u) : d ∣ q := (mem_filter.mp hq).2
  have hinj : Set.InjOn (fun q : ℕ => q / d) u := by
    intro a ha b hb hab
    have ha' := Nat.div_mul_cancel (hdiv a ha)
    have hb' := Nat.div_mul_cancel (hdiv b hb)
    dsimp only at hab
    rw [hab] at ha'
    omega
  have ht : ∀ j ∈ t, 0 < j ∧ P / (d : ℝ) < (j : ℝ) := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hj
    have hq0 := (hs q (mem_filter.mp hq).1).1
    refine ⟨Nat.div_pos (Nat.le_of_dvd hq0 (hdiv q hq)) hd, ?_⟩
    apply (div_lt_iff₀ hdR).mpr
    have heq : ((q / d : ℕ) : ℝ) * d = q := by exact_mod_cast Nat.div_mul_cancel (hdiv q hq)
    rw [heq]
    exact (hs q (mem_filter.mp hq).1).2
  have hpoint (q : ℕ) (hq : q ∈ u) :
      (d.totient : ℝ) * (1 / (q.totient : ℝ) ^ 2) ≤
        (1 / (d.totient : ℝ)) * (1 / ((q / d).totient : ℝ) ^ 2) := by
    have hj : 0 < q / d := Nat.div_pos
      (Nat.le_of_dvd (hs q (mem_filter.mp hq).1).1 (hdiv q hq)) hd
    have hjφ : (0 : ℝ) < (q / d).totient := by exact_mod_cast Nat.totient_pos.mpr hj
    have hsup : (d.totient : ℝ) * (q / d).totient ≤ q.totient := by
      have := Nat.totient_super_multiplicative d (q / d)
      rw [Nat.mul_div_cancel' (hdiv q hq)] at this
      exact_mod_cast this
    calc
      _ = (d.totient : ℝ) / (q.totient : ℝ) ^ 2 := by ring
      _ ≤ (d.totient : ℝ) / ((d.totient : ℝ) * (q / d).totient) ^ 2 :=
        div_le_div_of_nonneg_left hdφ.le (by positivity)
          (pow_le_pow_left₀ (by positivity) hsup 2)
      _ = _ := by field_simp
  calc
    _ = ∑ q ∈ u, (d.totient : ℝ) * (1 / (q.totient : ℝ) ^ 2) := mul_sum _ _ _
    _ ≤ ∑ q ∈ u, (1 / (d.totient : ℝ)) * (1 / ((q / d).totient : ℝ) ^ 2) := sum_le_sum hpoint
    _ = (1 / (d.totient : ℝ)) * ∑ j ∈ t, 1 / (j.totient : ℝ) ^ 2 := by
      rw [sum_image hinj, mul_sum]
    _ ≤ (1 / (d.totient : ℝ)) * (K / (P / d)) :=
      mul_le_mul_of_nonneg_left (htail _ (div_pos hP hdR) t ht) (by positivity)
    _ = _ := by field_simp <;> ring

/-- MV p.363 equation 6.14, the gcd majorant has an inverse first power tail. -/
theorem gcd_totient_tail :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℝ), 0 < P → ∀ (n : ℕ), 0 < n →
      ∀ s : Finset ℕ, (∀ q ∈ s, 0 < q ∧ P < (q : ℝ)) →
      (∑ q ∈ s, (Nat.gcd q n : ℝ) / (q.totient : ℝ) ^ 2) ≤
        K * ((n : ℝ) / n.totient) * n.divisors.card / P := by
  obtain ⟨K, hK, htail⟩ := totient_multiples_tail
  refine ⟨K, hK, fun P hP n hn s hs => ?_⟩
  simp_rw [div_eq_mul_inv]
  rw [gcd_weight_swap _ hn]
  calc
    _ ≤ ∑ d ∈ n.divisors, K * ((d : ℝ) / d.totient) / P := by
      apply sum_le_sum
      intro d hd
      simpa only [div_eq_mul_inv, one_mul] using htail P hP d (Nat.pos_of_mem_divisors hd) s hs
    _ ≤ ∑ _d ∈ n.divisors, K * ((n : ℝ) / n.totient) / P := by
      apply sum_le_sum
      intro d hd
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (LeanLab.Perelli1996.Totient400.divisor_totient_ratio_le d n hn
          (Nat.dvd_of_mem_divisors hd)) hK.le) hP.le
    _ = _ := by simp; ring

open LeanLab.Linnik.Decomp1532b (ramanujanSum singSeries)
open LeanLab.Linnik.Decomp466a (totientWeight)
open LeanLab.Linnik.MajorArcEnergy (singTrunc)
open LeanLab.Linnik.MajorArcEnergy.Leaves13PairWeight

/-- Gallagher p.130 display 11, the absolute value of one singular coefficient. -/
theorem singular_coefficient_norm (q : ℕ) (n : ℤ) :
    ‖((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n‖ =
      ((ArithmeticFunction.moebius q : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 * ‖ramanujanSum q n‖ := by
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_intCast,
    Complex.norm_natCast, sq_abs]

/-- Gallagher p.130, a squarefree singular coefficient has the Euler term majorant. -/
theorem singular_coefficient_le_euler {q : ℕ} (hq : Squarefree q) (n : ℤ) :
    ((ArithmeticFunction.moebius q : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 * ‖ramanujanSum q n‖ ≤
      eulerTerm n.natAbs q := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  have hg := Nat.gcd_dvd_left q n.natAbs
  have hcop : Nat.Coprime (q / Nat.gcd q n.natAbs) (Nat.gcd q n.natAbs) :=
    Nat.coprime_of_squarefree_mul (by rwa [Nat.div_mul_cancel hg])
  have hφ : q.totient = (q / Nat.gcd q n.natAbs).totient * (Nat.gcd q n.natAbs).totient := by
    rw [← Nat.totient_mul hcop, Nat.div_mul_cancel hg]
  have hg0 : 0 < Nat.gcd q n.natAbs := Nat.gcd_pos_of_pos_left _ hq0
  have hgφ : (0 : ℝ) < (Nat.gcd q n.natAbs).totient := by
    exact_mod_cast Nat.totient_pos.mpr hg0
  have hqφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hR : ‖ramanujanSum q n‖ ≤ ((Nat.gcd q n.natAbs).totient : ℝ) := by
    rw [LeanLab.Linnik.Decomp1532b.ramanujanSum_squarefree hq n,
      norm_mul, Complex.norm_intCast, Complex.norm_natCast]
    have hm : |((ArithmeticFunction.moebius (q / Nat.gcd q n.natAbs) : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q / Nat.gcd q n.natAbs)
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) hm
  have hmu : (ArithmeticFunction.moebius q : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq
  rw [hmu]
  calc
    _ ≤ 1 / (q.totient : ℝ) ^ 2 * ((Nat.gcd q n.natAbs).totient : ℝ) :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    _ = eulerTerm n.natAbs q := by
      unfold eulerTerm
      rw [hφ]
      push_cast
      field_simp

/-- Gallagher p.130 before display 11, the unweighted absolute singular sum. -/
theorem singular_unweighted_sum (X : ℕ) {n : ℤ} (hn : n ≠ 0) :
    ∑ q ∈ Icc 1 X, ((ArithmeticFunction.moebius q : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 *
      ‖ramanujanSum q n‖ ≤ 4 * totientWeight n := by
  have hsum : (∑ q ∈ Icc 1 X, ((ArithmeticFunction.moebius q : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 *
      ‖ramanujanSum q n‖) ≤
      ∑ q ∈ (Icc 1 X).filter (fun q => Squarefree q ∧ Nat.Coprime q 1), eulerTerm n.natAbs q := by
    rw [sum_filter]
    apply sum_le_sum
    intro q hq
    by_cases hs : Squarefree q
    · rw [if_pos ⟨hs, Nat.coprime_one_right q⟩]
      exact singular_coefficient_le_euler hs n
    · simp [hs, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  refine hsum.trans ((euler_sum_le_prod (m := 1) X).trans ?_)
  have he := euler_prod_le (m := 1) ((Int.natAbs_pos.mpr hn).ne') X
  have hp : n.natAbs.primeFactors.filter (fun p => ¬ p ∣ 1) = n.natAbs.primeFactors := by
    apply filter_true_of_mem
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one
  rw [hp, ← ratio_eq_prod ((Int.natAbs_pos.mpr hn).ne')] at he
  exact he

/-- Gallagher p.130 and MV p.363 equation 6.13, both weighted singular estimates. -/
theorem singular_weighted_sums :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℝ) (n : ℤ), 2 ≤ P → n ≠ 0 →
      (∑ q ∈ Icc 1 ⌊P⌋₊, ((ArithmeticFunction.moebius q : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 *
          ‖ramanujanSum q n‖ * q ≤
        K * totientWeight n * n.natAbs.divisors.card * Real.log P) ∧
      (∑ q ∈ Icc 1 ⌊P⌋₊, ((ArithmeticFunction.moebius q : ℝ)) ^ 2 / (q.totient : ℝ) ^ 2 *
          ‖ramanujanSum q n‖ ≤ K * totientWeight n) := by
  obtain ⟨C, hC, hsum⟩ := weighted_gcd_sum
  refine ⟨3 * C + 4, by positivity, fun P n hP hn => ⟨?_, ?_⟩⟩
  · have hlog2 : (1 / 2 : ℝ) ≤ Real.log P := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hP
      linarith [Real.log_two_gt_d9]
    have hlogX : Real.log ⌊P⌋₊ ≤ Real.log P := Real.log_le_log
      (by exact_mod_cast (show 0 < ⌊P⌋₊ from lt_of_lt_of_le (by decide : 0 < 2) (Nat.le_floor hP)))
      (Nat.floor_le (by linarith))
    calc
      _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, (Nat.gcd q n.natAbs : ℝ) * ((q : ℝ) / (q.totient : ℝ) ^ 2) := by
        apply sum_le_sum
        intro q hq
        have h := LeanLab.Linnik.Decomp1532b.singular_coefficient_norm_le_gcd (mem_Icc.mp hq).1 n
        rw [singular_coefficient_norm] at h
        have hh := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
        convert hh using 1 <;> ring
      _ ≤ C * totientWeight n * n.natAbs.divisors.card * (1 + Real.log ⌊P⌋₊) :=
        hsum n.natAbs ⌊P⌋₊ (Int.natAbs_pos.mpr hn)
      _ ≤ C * totientWeight n * n.natAbs.divisors.card * (3 * Real.log P) := by
        exact mul_le_mul_of_nonneg_left (by linarith)
          (by unfold totientWeight; positivity)
      _ ≤ (3 * C + 4) * totientWeight n * n.natAbs.divisors.card * Real.log P := by
        have hw : 0 ≤ totientWeight n := by unfold totientWeight; positivity
        have ht : (0 : ℝ) ≤ n.natAbs.divisors.card := Nat.cast_nonneg _
        nlinarith [mul_nonneg (mul_nonneg hw ht) (show 0 ≤ Real.log P by linarith)]
  · exact (singular_unweighted_sum ⌊P⌋₊ hn).trans
      (mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ 3 * C + 4)
        (by unfold totientWeight; positivity))

/-- Gallagher p.130 and MV p.363 equation 6.14, the singular series tail. -/
theorem singular_tail :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : ℝ) (n : ℤ), 1 ≤ P → n ≠ 0 →
      ‖singTrunc P n - singSeries n‖ ≤
        K * totientWeight n * n.natAbs.divisors.card / P := by
  obtain ⟨K, hK, htail⟩ := gcd_totient_tail
  refine ⟨K, hK, fun P n hP hn => ?_⟩
  let f : ℕ → ℂ := fun q => ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 /
    (q.totient : ℂ) ^ 2 * ramanujanSum q n
  have hs : Summable f := LeanLab.Linnik.Decomp1532b.summable_singSeries hn
  have hf0 : f 0 = 0 := by simp [f]
  have htrunc : (∑ q ∈ range (⌊P⌋₊ + 1), f q) = singTrunc P n := by
    have he : range (⌊P⌋₊ + 1) = insert 0 (Icc 1 ⌊P⌋₊) := by ext q; simp; omega
    rw [he, sum_insert (by simp), hf0, zero_add]
    rfl
  have hlim : Filter.Tendsto (fun M : ℕ => ∑ q ∈ range M, f q)
      Filter.atTop (nhds (singSeries n)) := hs.hasSum.tendsto_sum_nat
  have hnorm := (hlim.sub (tendsto_const_nhds (x := ∑ q ∈ range (⌊P⌋₊ + 1), f q))).norm
  have hbound : ∀ᶠ M : ℕ in Filter.atTop,
      ‖(∑ q ∈ range M, f q) - ∑ q ∈ range (⌊P⌋₊ + 1), f q‖ ≤
        K * totientWeight n * n.natAbs.divisors.card / P := by
    filter_upwards [Filter.eventually_ge_atTop (⌊P⌋₊ + 1)] with M hM
    rw [← sum_Ico_eq_sub f hM]
    calc
      _ ≤ ∑ q ∈ Ico (⌊P⌋₊ + 1) M, ‖f q‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Ico (⌊P⌋₊ + 1) M, (Nat.gcd q n.natAbs : ℝ) / (q.totient : ℝ) ^ 2 := by
        apply sum_le_sum
        intro q hq
        exact LeanLab.Linnik.Decomp1532b.singular_coefficient_norm_le_gcd
          (by have := (mem_Ico.mp hq).1; omega) n
      _ ≤ _ := htail P (by linarith) n.natAbs (Int.natAbs_pos.mpr hn) _ (by
        intro q hq
        have hq0 := (mem_Ico.mp hq).1
        refine ⟨by omega, ?_⟩
        exact (Nat.lt_floor_add_one P).trans_le (by exact_mod_cast hq0))
  have hh := le_of_tendsto hnorm hbound
  rw [htrunc] at hh
  rwa [norm_sub_rev] at hh

open Finset
open LeanLab.Linnik.MajorArcEnergy
open LeanLab.BhowmikGrimmelt2026

/-- Gallagher p.128, the local c_n sum agrees with the residue Gauss sum convention. -/
theorem cn_eq_cChi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℤ) :
    cn χ n = cChi χ n := by
  unfold cn cChi
  apply Finset.sum_bij (fun (a : ℕ) _ => ((a : ℕ) : ZMod q))
  · intro a _; exact Finset.mem_univ _
  · intro a ha b hb hab
    have := congrArg ZMod.val hab
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] at this
  · intro z _
    exact ⟨z.val, Finset.mem_range.mpr z.val_lt, ZMod.natCast_zmod_val z⟩
  · intro a ha
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
    congr 1
    unfold LeanLab.PNTPort.LargeSieve.e ee
    congr 1
    push_cast
    ring

/-- Gallagher p.129 displays 5 and6, nonzero induced Gauss sums restrict the extra factor. -/
theorem gauss_lift_support {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hd : r ∣ q)
    (hne : gaussSum (DirichletCharacter.changeLevel hd χ) (ZMod.stdAddChar (N := q)) ≠ 0) :
    Squarefree (q / r) ∧ Nat.Coprime (q / r) r := by
  have aux : ∀ d : ℕ, d ≠ 0 → ∀ (q : ℕ) [NeZero q], q = r * d → ∀ hd : r ∣ q,
      gaussSum (DirichletCharacter.changeLevel hd χ) (ZMod.stdAddChar (N := q)) ≠ 0 →
      Squarefree d ∧ Nat.Coprime d r := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd0 q hq0 hq hdq hne
      by_cases hd1 : d = 1
      · subst d; simp
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
      obtain ⟨k, hk⟩ := hpd
      have hk0 : k ≠ 0 := by intro h; simp [h] at hk; exact hd0 hk
      have hklt : k < d := by
        have := Nat.pos_of_ne_zero hk0
        nlinarith [hp.two_le]
      let m := r * k
      haveI : NeZero m := ⟨mul_ne_zero (NeZero.ne r) hk0⟩
      have hq' : q = m * p := by dsimp [m]; rw [hq, hk]; ring
      have hm : r ∣ m := Nat.dvd_mul_right r k
      clear hq
      subst q
      rw [DirichletCharacter.changeLevel_trans χ hm (Nat.dvd_mul_right m p),
        gaussSum_lift_prime443 p hp] at hne
      have hsource : gaussSum (DirichletCharacter.changeLevel hm χ) (ZMod.stdAddChar (N := m)) ≠ 0 :=
        (mul_ne_zero_iff.mp hne).2
      have hvalue : (DirichletCharacter.changeLevel hm χ) (p : ZMod m) ≠ 0 :=
        neg_ne_zero.mp (mul_ne_zero_iff.mp hne).1
      have hunit : IsUnit (p : ZMod m) := by
        by_contra h
        exact hvalue (MulChar.map_nonunit _ h)
      have hcop : Nat.Coprime p (r * k) := (ZMod.isUnit_iff_coprime p m).mp hunit
      have hcopk := hcop.of_dvd_right (dvd_mul_left k r)
      have hcopr := hcop.of_dvd_right (dvd_mul_right r k)
      obtain ⟨hsk, hkr⟩ := ih k hklt hk0 m rfl hm hsource
      rw [hk]
      exact ⟨(Nat.squarefree_mul hcopk).mpr ⟨hp.squarefree, hsk⟩, hcopr.mul_left hkr⟩
  obtain ⟨d, hqd⟩ := hd
  have hd0 : d ≠ 0 := by intro h; simp [h] at hqd; exact NeZero.ne q hqd
  have h := aux d hd0 q hqd ⟨d, hqd⟩ hne
  simpa only [hqd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne r))] using h

/-- Gallagher p.129 display 5, the complete induced character estimate and support. -/
theorem induced_cn {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) (n : ℤ) :
    ‖cn χ n‖ ≤ Real.sqrt χ.conductor * (q.totient : ℝ) /
        ((q / Nat.gcd q n.natAbs).totient : ℝ) ∧
      (cn χ n ≠ 0 → χ.conductor ∣ q / Nat.gcd q n.natAbs ∧
        Squarefree (q / Nat.gcd q n.natAbs / χ.conductor) ∧
        Nat.Coprime (q / Nat.gcd q n.natAbs / χ.conductor) χ.conductor) := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [cn_eq_cChi]
  have hχ := χ.primitiveCharacter_isPrimitive
  have hd := χ.conductor_dvd_level
  by_cases hgood : χ.conductor ∣ q / Nat.gcd q n.natAbs
  · refine ⟨?_, fun hne => ⟨hgood, ?_⟩⟩
    · have h := twisted_fiber_bound_supply443 χ.primitiveCharacter hχ hd n hgood
      rw [χ.changeLevel_primitiveCharacter] at h
      convert h using 1 <;> ring
    · let m := q / Nat.gcd q n.natAbs
      have hmpos : 0 < m := Nat.div_pos (Nat.gcd_le_left _ hq)
        (Nat.gcd_pos_of_pos_left _ hq)
      haveI : NeZero m := ⟨hmpos.ne'⟩
      let ψ := DirichletCharacter.changeLevel hgood χ.primitiveCharacter
      have hmq : m ∣ q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q n.natAbs)
      have he := cChi_gcd_factor443 ψ n rfl
      rw [← DirichletCharacter.changeLevel_trans χ.primitiveCharacter hgood hmq,
        χ.changeLevel_primitiveCharacter] at he
      have hneψ : cChi ψ (n / (Nat.gcd q n.natAbs : ℤ)) ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at he
        exact hne he
      have hnorm := cChi_unit_norm443 ψ _ (gcd_frequency_unit443 (q := q) n)
      have hone : cChi ψ 1 ≠ 0 := by
        intro hz
        rw [hz, norm_zero] at hnorm
        exact hneψ (norm_eq_zero.mp hnorm)
      rw [cChi_int_gauss436] at hone
      simp only [Int.cast_one, AddChar.mulShift_one] at hone
      exact gauss_lift_support χ.primitiveCharacter hgood hone
  · have hz := twisted_fiber_vanish436 χ.primitiveCharacter hχ hd n hgood
    rw [χ.changeLevel_primitiveCharacter] at hz
    rw [hz, norm_zero]
    exact ⟨by positivity, fun h => (h rfl).elim⟩


end LeanLab.Linnik.Decomp507a
