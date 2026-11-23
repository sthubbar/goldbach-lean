module

public import LeanLab.Perelli1996.Totient400

/-!
Perelli 1996, page 481 equation 3.
The finite arithmetic tail reduction isolates the inverse totient squared tail.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Tail320
open Finset
noncomputable section

/-- Page 481 equation 3, grouping the positive majorant by the gcd with m.
CONDITIONAL ON the explicit inverse totient squared tail bound. -/
theorem finite_totient_tail (m : ℕ) (hm : 0 < m) (P K : ℝ) (hP : 0 < P)
    (hK : ∀ x : ℝ, 0 < x → ∀ t : Finset ℕ,
      (∀ r ∈ t, 0 < r ∧ x < (r : ℝ)) →
      (∑ r ∈ t, 1 / (r.totient : ℝ) ^ 2) ≤ K / x)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 0 < q ∧ P < (q : ℝ)) :
    (∑ q ∈ s, 1 / ((q.totient : ℝ) * (q / Nat.gcd q m).totient)) ≤
      K / P * ((m : ℝ) * m.divisors.card / m.totient) := by
  classical
  have hK0 : 0 ≤ K := by
    have h := hK 1 (by norm_num) ∅ (by simp)
    simpa using h
  have hmap : ∀ q ∈ s, Nat.gcd q m ∈ m.divisors := by
    intro q hq
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right q m, hm.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ d ∈ m.divisors, K / P * ((d : ℝ) / d.totient) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
      have hφd : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd0
      let u := s.filter (fun q => Nat.gcd q m = d)
      let t := u.image (fun q => q / d)
      have hdiv (q : ℕ) (hq : q ∈ u) : d ∣ q := by
        have hg := (Finset.mem_filter.mp hq).2
        rw [← hg]
        exact Nat.gcd_dvd_left q m
      have hqpos (q : ℕ) (hq : q ∈ u) : 0 < q :=
        (hs q (Finset.mem_filter.mp hq).1).1
      have hquotpos (q : ℕ) (hq : q ∈ u) : 0 < q / d := by
        apply Nat.div_pos
        · exact Nat.le_of_dvd (hqpos q hq) (hdiv q hq)
        · exact hd0
      have ht : ∀ r ∈ t, 0 < r ∧ P / (d : ℝ) < (r : ℝ) := by
        intro r hr
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
        refine ⟨hquotpos q hq, ?_⟩
        apply (div_lt_iff₀ hdR).mpr
        have hmul : ((q / d : ℕ) : ℝ) * d = (q : ℝ) := by
          exact_mod_cast Nat.div_mul_cancel (hdiv q hq)
        rw [hmul]
        exact (hs q (Finset.mem_filter.mp hq).1).2
      have hinj : Set.InjOn (fun q : ℕ => q / d) u := by
        intro q hq r hr heq
        have hq' := Nat.div_mul_cancel (hdiv q hq)
        have hr' := Nat.div_mul_cancel (hdiv r hr)
        calc q = (q / d) * d := hq'.symm
          _ = (r / d) * d := congrArg (fun x : ℕ => x * d) heq
          _ = r := hr'
      have hpoint : ∀ q ∈ u,
          1 / ((q.totient : ℝ) * (q / Nat.gcd q m).totient) ≤
            (1 / (d.totient : ℝ)) * (1 / ((q / d).totient : ℝ) ^ 2) := by
        intro q hq
        have hg := (Finset.mem_filter.mp hq).2
        have hφr : (0 : ℝ) < (q / d).totient := by
          exact_mod_cast Nat.totient_pos.mpr (hquotpos q hq)
        have hφq : (0 : ℝ) < q.totient := by
          exact_mod_cast Nat.totient_pos.mpr (hqpos q hq)
        have hφ : (d.totient : ℝ) * (q / d).totient ≤ q.totient := by
          have hh := Nat.totient_super_multiplicative (q / d) d
          rw [Nat.div_mul_cancel (hdiv q hq)] at hh
          exact_mod_cast (by simpa [Nat.mul_comm] using hh :
            d.totient * (q / d).totient ≤ q.totient)
        rw [hg]
        calc
          _ ≤ 1 / (((d.totient : ℝ) * (q / d).totient) * (q / d).totient) :=
            one_div_le_one_div_of_le (by positivity)
              (mul_le_mul_of_nonneg_right hφ hφr.le)
          _ = _ := by field_simp <;> ring
      calc
        _ ≤ ∑ q ∈ u, (1 / (d.totient : ℝ)) * (1 / ((q / d).totient : ℝ) ^ 2) :=
          Finset.sum_le_sum hpoint
        _ = (1 / (d.totient : ℝ)) * ∑ r ∈ t, 1 / (r.totient : ℝ) ^ 2 := by
          rw [Finset.mul_sum, Finset.sum_image hinj]
        _ ≤ (1 / (d.totient : ℝ)) * (K / (P / (d : ℝ))) :=
          mul_le_mul_of_nonneg_left (hK _ (div_pos hP hdR) t ht) (by positivity)
        _ = K / P * ((d : ℝ) / d.totient) := by field_simp <;> ring
    _ = K / P * ∑ d ∈ m.divisors, (d : ℝ) / d.totient := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Totient400.sum_divisors_ratio_le m hm)
      (div_nonneg hK0 hP.le)

/-- Page 481 equation 3 for a finite set of signed Ramanujan coefficients.
CONDITIONAL ON the inverse totient squared tail bound. -/
theorem finite_ramanujan_tail (m : ℕ) (hm : 0 < m) (P K : ℝ) (hP : 0 < P)
    (hK : ∀ x : ℝ, 0 < x → ∀ t : Finset ℕ,
      (∀ r ∈ t, 0 < r ∧ x < (r : ℝ)) →
      (∑ r ∈ t, 1 / (r.totient : ℝ) ^ 2) ≤ K / x)
    (s : Finset ℕ) (hs : ∀ q ∈ s, 0 < q ∧ P < (q : ℝ)) :
    ‖∑ q ∈ s, ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) *
      RamanujanInt400.ramanujanSumInt q (-(m : ℤ))‖ ≤
      K / P * ((m : ℝ) * m.divisors.card / m.totient) := by
  have hb := Totient400.norm_coefficient_sum_le s (-(m : ℤ)) (fun q hq => (hs q hq).1)
  simp only [Int.natAbs_neg, Int.natAbs_natCast] at hb
  exact hb.trans (finite_totient_tail m hm P K hP hK s hs)

end
end LeanLab.Perelli1996.Tail320
