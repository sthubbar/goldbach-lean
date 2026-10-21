module

public import LeanLab.PNTPort.BVMax.RenyiRem
public import LeanLab.PNTSieve.MertensProduct

/-!
# Brun's pure sieve on `{N - p}` with explicit main term

Lab proof, unit U-5336, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics.

* `sum_xDen_le`: `Σ_{p ∈ P} 1/(p - 1) ≤ log log z + 20` for primes `3 ≤ p ≤ z`;
* `renyi_main`: for every `A > 0` there are `B > 0` and `K` with
  `S({N - p}, P) ≥ X (e^{-36}/log z - (log log z + 20)^{r+1}/(r+1)!) - K N/(log N)^A`,
  `X = liD(N - 1)`, for every finset `P` of primes `3 ≤ p ≤ z` not dividing `N`, `z ≥ 3`, odd `r` with
  every `∏T`, `|T| ≤ r`, below `√N/(log N)^B`. The parameter choice that makes the right side positive
  is the last step of Rényi's theorem, IDEAS I-5051;
* `pow_div_factorial_le_exp_neg`, U-5338: `u^n/n! ≤ e^{-n}` for `n ≥ e³ u`;
* `pow_bigOmega_le`, U-5337: `z^{Ω(m)} ≤ m` when every prime factor of `m ≠ 0` is at least `z`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset

lemma sum_xDen_le (z : ℕ) (hz : 3 ≤ z) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 3 ≤ p ∧ p ≤ z) :
    ∑ p ∈ P, xDen p ≤ Real.log (Real.log z) + 20 := by
  have hsub : P ⊆ (Icc 1 z).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpr, h3, hpz⟩ := hP p hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hpz⟩, hpr⟩
  have hx : ∀ p ∈ P, xDen p = 1 / ((p : ℝ) - 1) := fun p hp => by
    simp only [xDen, if_pos (hP p hp).2.1]
  rw [sum_congr rfl hx]
  have hA : ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) ≤ ∑ p ∈ P, (1 / (p : ℝ) + 4 * ((1 : ℝ) / (p : ℝ) ^ 2)) := by
    apply sum_le_sum; intro p hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (hP p hp).2.1
    have := LeanLab.PNTSieve.Mertens.inv_pred_le p (by have := (hP p hp).2.1; omega)
    have h4 : (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 4 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
      rw [mul_one_div, div_le_div_iff₀ (by nlinarith) (by positivity)]; nlinarith
    linarith
  rw [sum_add_distrib, ← mul_sum] at hA
  have hB : ∑ p ∈ P, (1 : ℝ) / p ≤ ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / p :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hC := LeanLab.PNTSieve.Mertens.sum_inv_primes_le z (by omega)
  have hD : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 2 :=
    (sum_le_sum_of_subset_of_nonneg (hsub.trans (filter_subset _ _))
      (fun _ _ _ => by positivity)).trans (LeanLab.PNTSieve.Mertens.sum_inv_sq_le_two z)
  linarith

theorem renyi_main (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∀ z : ℕ, 3 ≤ z → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N ∧ 3 ≤ p ∧ p ≤ z) →
    ∀ r : ℕ, Odd r →
    (∀ T ∈ P.powerset.filter (fun T => T.card ≤ r),
      ∏ p ∈ T, p ≤ ⌊Real.sqrt N / Real.log N ^ B⌋₊) →
    liD ((N - 1 : ℕ) : ℝ) * (Real.exp (-36) / Real.log z -
      (Real.log (Real.log z) + 20) ^ (r + 1) / (r + 1).factorial) -
      K * N / Real.log N ^ A ≤ (LeanLab.PNTSieve.Bonferroni.sifted (goldbachSeq N) P : ℝ) := by
  obtain ⟨B, hB, K, hK⟩ := renyi_sieve_lower A hA
  refine ⟨B, hB, K, fun N hN z hz P hP r hr hTQ => ?_⟩
  have h := hK N hN P (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.1⟩) r hr hTQ
  have hX : 0 ≤ liD ((N - 1 : ℕ) : ℝ) := by
    unfold liD liN
    exact sum_nonneg (fun n _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n))
  have hP' : ∀ p ∈ P, p.Prime ∧ 3 ≤ p ∧ p ≤ z := fun p hp => ⟨(hP p hp).1, (hP p hp).2.2⟩
  have hprod : Real.exp (-36) / Real.log z ≤ ∏ p ∈ P, (1 - xDen p) := by
    have := LeanLab.PNTSieve.Mertens.prod_one_sub_inv_pred_ge z hz P hP'
    refine this.trans (le_of_eq (prod_congr rfl (fun p hp => ?_)))
    simp only [xDen, if_pos (hP p hp).2.2.1]
  have hsum := sum_xDen_le z hz P hP'
  have hs0 : 0 ≤ ∑ p ∈ P, xDen p := sum_nonneg (fun p _ => xDen_nonneg p)
  have hpow : (∑ p ∈ P, xDen p) ^ (r + 1) ≤ (Real.log (Real.log z) + 20) ^ (r + 1) :=
    pow_le_pow_left₀ hs0 hsum _
  have hfac : (0 : ℝ) < (r + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hdiv : (∑ p ∈ P, xDen p) ^ (r + 1) / (r + 1).factorial ≤
      (Real.log (Real.log z) + 20) ^ (r + 1) / (r + 1).factorial :=
    div_le_div_of_nonneg_right hpow hfac.le
  have e1 := mul_le_mul_of_nonneg_left hprod hX
  have e2 := mul_le_mul_of_nonneg_left hdiv hX
  nlinarith

/-- If every prime factor of `m ≠ 0` is at least `z`, then `z^{Ω(m)} ≤ m`; so a survivor of the sieve
up to `z` below `N` has `Ω(m) ≤ log N/log z`. -/
theorem pow_bigOmega_le (m z : ℕ) (hm : m ≠ 0) (hz : ∀ p ∈ m.primeFactorsList, z ≤ p) :
    z ^ (ArithmeticFunction.cardFactors m) ≤ m := by
  rw [ArithmeticFunction.cardFactors_apply]
  conv_rhs => rw [← Nat.prod_primeFactorsList hm]
  simpa using List.pow_length_le_prod m.primeFactorsList z hz

/-- `u^n/n! ≤ e^{-n}` for `u ≥ 0` and `n ≥ e³ u`: the factorial tail of the parameter choice. -/
theorem pow_div_factorial_le_exp_neg (u : ℝ) (hu : 0 ≤ u) (n : ℕ) (hn : Real.exp 3 * u ≤ n) :
    u ^ n / n.factorial ≤ Real.exp (-(n : ℝ)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 := Real.pow_div_factorial_le_exp (n / Real.exp 1) (by positivity) n
  have he1 : n / Real.exp 1 ≤ n :=
    div_le_self hn0 (by have := Real.add_one_le_exp (1 : ℝ); linarith)
  have h2 : (n / Real.exp 1) ^ n / n.factorial ≤ Real.exp n := h1.trans (Real.exp_le_exp.mpr he1)
  have e3 : (n / Real.exp 1) * Real.exp (-2) = n / Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.exp_add, Real.exp_neg]; field_simp
  have hu2 : u ≤ (n / Real.exp 1) * Real.exp (-2) := by
    rw [e3, le_div_iff₀ (Real.exp_pos 3)]; linarith
  have hpow : u ^ n ≤ ((n / Real.exp 1) * Real.exp (-2)) ^ n := pow_le_pow_left₀ hu hu2 n
  rw [mul_pow, ← Real.exp_nat_mul] at hpow
  calc u ^ n / n.factorial ≤ (n / Real.exp 1) ^ n * Real.exp (n * -2) / n.factorial :=
        div_le_div_of_nonneg_right hpow hfac.le
    _ = (n / Real.exp 1) ^ n / n.factorial * Real.exp (n * -2) := by ring
    _ ≤ Real.exp n * Real.exp (n * -2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_add]; ring_nf

end LeanLab.PNTPort.BVMax

