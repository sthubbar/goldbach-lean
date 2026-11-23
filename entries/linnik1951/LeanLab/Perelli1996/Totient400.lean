module

public import LeanLab.Perelli1996.RamanujanInt400

/-!
Perelli 1996, page 481, the elementary divisor and coefficient bounds in equation 3.
The coefficient sum bound below is the finite version of the printed first inequality.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Totient400
open Finset
noncomputable section

/-- Page 481 equation 3. The ratio n over phi n increases under divisibility. -/
theorem divisor_totient_ratio_le (d n : ℕ) (hn : 0 < n) (hd : d ∣ n) :
    (d : ℝ) / d.totient ≤ (n : ℝ) / n.totient := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hφn : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hφd : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hdpos
  let f := fun p : ℕ => 1 - (p : ℝ)⁻¹
  have hEuler (u : ℕ) : (u.totient : ℝ) = (u : ℝ) * ∏ p ∈ u.primeFactors, f p := by
    dsimp [f]
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors u)
    push_cast at hh
    exact hh
  have hsub : d.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono hd hn.ne'
  have hnon (p : ℕ) (hp : p ∈ n.primeFactors) : 0 ≤ f p := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    dsimp [f]
    have hi : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
    linarith
  have hle (p : ℕ) (hp : p ∈ n.primeFactors) : f p ≤ 1 := by
    dsimp [f]
    linarith [inv_nonneg.mpr (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hprod : (∏ p ∈ n.primeFactors, f p) ≤ ∏ p ∈ d.primeFactors, f p :=
    Finset.prod_le_prod_of_subset_of_le_one₀ hsub hnon (fun p hp _ => hle p hp)
  have hratio : (n.totient : ℝ) / n ≤ (d.totient : ℝ) / d := by
    rw [hEuler n, hEuler d]
    simpa [hnR.ne', hdR.ne', mul_div_cancel_left₀] using hprod
  apply (div_le_div_iff₀ hφd hφn).mpr
  have hcross := (div_le_div_iff₀ hnR hdR).mp hratio
  nlinarith

/-- Page 481 equation 3, final inequality for the divisor sum. -/
theorem sum_divisors_ratio_le (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, (d : ℝ) / d.totient) ≤
      (n : ℝ) * n.divisors.card / n.totient := by
  calc
    _ ≤ ∑ _d ∈ n.divisors, (n : ℝ) / n.totient :=
      Finset.sum_le_sum (fun d hd => divisor_totient_ratio_le d n hn (Nat.dvd_of_mem_divisors hd))
    _ = _ := by simp; ring

/-- Page 481 equation 3. Finite coefficient sums obey the printed totient majorant.
No convergence claim for an infinite tail is included in this finite identity. -/
theorem norm_coefficient_sum_le (s : Finset ℕ) (m : ℤ) (hs : ∀ q ∈ s, 0 < q) :
    ‖∑ q ∈ s, ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) *
      RamanujanInt400.ramanujanSumInt q m‖ ≤
      ∑ q ∈ s, 1 / ((q.totient : ℝ) * (q / Nat.gcd q m.natAbs).totient) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro q hq
  rw [RamanujanInt400.ramanujanSumInt_eq_natAbs q m (hs q hq)]
  exact Ramanujan400.norm_weighted_ramanujanSum_le q m.natAbs (hs q hq)

end
end LeanLab.Perelli1996.Totient400
