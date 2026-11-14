module

public import LeanLab.PNTSieve.MertensUpper

/-!
# `∏_{p ≤ N} (1 - 1/p) ≥ e^{-16}/log N`

Lab proof, unit U-5329, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
Mertens' product theorem, lower bound with a weak explicit constant. From `sum_inv_primes_le`.

* `log_one_sub_ge`: `-t - 2t² ≤ log(1 - t)` for `0 ≤ t ≤ 1/2`;
* `prod_one_sub_ge_exp`: `∏_S (1 - x_p) ≥ exp(-(Σ_S x_p + 2 Σ_S x_p²))` for `0 ≤ x_p ≤ 1/2`;
* `sum_inv_sq_le_two`: `Σ_{n ≤ N} 1/n² ≤ 2`;
* `prod_one_sub_inv_pred_ge`, U-5330: `∏_{p ∈ S}(1 - 1/(p - 1)) ≥ e^{-36}/log z` for primes `3 ≤ p ≤ z`;
* `mertens_product_ge`: `∏_{p ≤ N} (1 - 1/p) ≥ e^{-16}/log N` for `N ≥ 2`.
The Mertens input of the Rényi route, IDEAS I-5051.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Mertens

open Finset Real

lemma log_one_sub_ge (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : -t - 2 * t ^ 2 ≤ Real.log (1 - t) := by
  have hpos : 0 < 1 - t := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 / (1 - t) by positivity)
  rw [Real.log_div (by norm_num) hpos.ne', Real.log_one, zero_sub] at h
  have e : 1 / (1 - t) - 1 = t / (1 - t) := by field_simp; ring
  rw [e] at h
  have h2 : t / (1 - t) ≤ t + 2 * t ^ 2 := by
    rw [div_le_iff₀ hpos]; nlinarith
  linarith

lemma prod_one_sub_ge_exp {α : Type*} (S : Finset α) (x : α → ℝ) (h0 : ∀ p ∈ S, 0 ≤ x p)
    (h1 : ∀ p ∈ S, x p ≤ 1 / 2) :
    Real.exp (-(∑ p ∈ S, x p + 2 * ∑ p ∈ S, x p ^ 2)) ≤ ∏ p ∈ S, (1 - x p) := by
  have hpos : ∀ p ∈ S, 0 < 1 - x p := fun p hp => by linarith [h1 p hp]
  have hprod : ∏ p ∈ S, (1 - x p) = Real.exp (∑ p ∈ S, Real.log (1 - x p)) := by
    rw [Real.exp_sum]
    exact prod_congr rfl (fun p hp => (Real.exp_log (hpos p hp)).symm)
  rw [hprod, Real.exp_le_exp, mul_sum, ← sum_add_distrib, ← sum_neg_distrib]
  exact sum_le_sum (fun p hp => by linarith [log_one_sub_ge (x p) (h0 p hp) (h1 p hp)])

lemma sum_inv_sq_le_two (N : ℕ) : ∑ n ∈ Icc 1 N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp
  · have hI : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
    rw [hI, ← sum_Ioc_consecutive _ (Nat.zero_le 1) hN]
    have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := N) one_ne_zero hN
    have h1 : ∑ n ∈ Ioc (0 : ℕ) 1, (1 : ℝ) / (n : ℝ) ^ 2 = 1 := by simp
    have h2 : ∑ n ∈ Ioc 1 N, (1 : ℝ) / (n : ℝ) ^ 2 = ∑ n ∈ Ioc 1 N, ((n : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
    have : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    rw [h1, h2]
    norm_num at h
    linarith

/-- `∏_{p ≤ N} (1 - 1/p) ≥ e^{-16}/log N` for `N ≥ 2`. -/
theorem mertens_product_ge (N : ℕ) (hN : 2 ≤ N) :
    Real.exp (-16) / Real.log N ≤ ∏ p ∈ (Icc 1 N).filter Nat.Prime, (1 - (1 : ℝ) / p) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
  have h0 : ∀ p ∈ (Icc 1 N).filter Nat.Prime, 0 ≤ (1 : ℝ) / p := fun p _ => by positivity
  have h1 : ∀ p ∈ (Icc 1 N).filter Nat.Prime, (1 : ℝ) / p ≤ 1 / 2 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
    exact one_div_le_one_div_of_le (by norm_num) h2
  refine le_trans ?_ (prod_one_sub_ge_exp _ _ h0 h1)
  have hs := sum_inv_primes_le N hN
  have hsq : ∑ p ∈ (Icc 1 N).filter Nat.Prime, ((1 : ℝ) / p) ^ 2 ≤ 2 := by
    refine le_trans ?_ (sum_inv_sq_le_two N)
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)).trans
      (le_of_eq (sum_congr rfl (fun n _ => by ring)))
  have hexp : Real.exp (-16) / Real.log N = Real.exp (-(Real.log (Real.log N) + 16)) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (Real.log N)), Real.exp_log hL0]; ring
  rw [hexp, Real.exp_le_exp]
  linarith

lemma inv_pred_le (p : ℕ) (hp : 2 ≤ p) :
    (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / p + 1 / ((p : ℝ) - 1) ^ 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ hp1 (by positivity)]
  nlinarith

/-- The sieve density of `{N - p}`: for any finset `S` of primes with `3 ≤ p ≤ z`,
`∏_{p ∈ S} (1 - 1/(p - 1)) ≥ e^{-36}/log z`, `z ≥ 3`. -/
theorem prod_one_sub_inv_pred_ge (z : ℕ) (hz : 3 ≤ z) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p ∧ p ≤ z) :
    Real.exp (-36) / Real.log z ≤ ∏ p ∈ S, (1 - (1 : ℝ) / ((p : ℝ) - 1)) := by
  have hz3 : (3 : ℝ) ≤ z := by exact_mod_cast hz
  have hL0 : 0 < Real.log z := Real.log_pos (by linarith)
  have h0 : ∀ p ∈ S, 0 ≤ (1 : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have : (3 : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1
    exact div_nonneg zero_le_one (by linarith)
  have h1 : ∀ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / 2 := by
    intro p hp
    have : (3 : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  refine le_trans ?_ (prod_one_sub_ge_exp _ _ h0 h1)
  have hsub : S ⊆ (Icc 1 z).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpr, h3, hpz⟩ := hS p hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hpz⟩, hpr⟩
  -- Σ 1/(p - 1)² ≤ 4 Σ_{n ≤ z} 1/n² ≤ 8
  have hsq : ∑ p ∈ S, ((1 : ℝ) / ((p : ℝ) - 1)) ^ 2 ≤ 8 := by
    have hterm : ∀ p ∈ S, ((1 : ℝ) / ((p : ℝ) - 1)) ^ 2 ≤ 4 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
      intro p hp
      have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1
      rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith
    have h2 : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 2 := by
      refine le_trans ?_ (sum_inv_sq_le_two z)
      exact sum_le_sum_of_subset_of_nonneg (hsub.trans (filter_subset _ _))
        (fun _ _ _ => by positivity)
    have := sum_le_sum hterm
    rw [← mul_sum] at this
    linarith
  -- Σ 1/(p - 1) ≤ Σ_{p ≤ z} 1/p + Σ 1/(p - 1)² ≤ log log z + 12 + 8
  have hlin : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ≤ Real.log (Real.log z) + 20 := by
    have hA : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ≤
        ∑ p ∈ S, (1 / (p : ℝ) + ((1 : ℝ) / ((p : ℝ) - 1)) ^ 2) := by
      apply sum_le_sum; intro p hp
      have := inv_pred_le p (by have := (hS p hp).2.1; omega)
      rw [div_pow, one_pow]; exact this
    rw [sum_add_distrib] at hA
    have hB : ∑ p ∈ S, (1 : ℝ) / p ≤ ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have hC := sum_inv_primes_le z (by omega)
    linarith
  have hexp : Real.exp (-36) / Real.log z = Real.exp (-(Real.log (Real.log z) + 36)) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (Real.log z)), Real.exp_log hL0]; ring
  rw [hexp, Real.exp_le_exp]
  linarith

end LeanLab.PNTSieve.Mertens

