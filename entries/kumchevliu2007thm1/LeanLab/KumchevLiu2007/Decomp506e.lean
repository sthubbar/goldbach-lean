module

public import LeanLab.KumchevLiu2007.Decomp506c
public import LeanLab.KumchevLiu2007.Decomp506d
public import Mathlib.NumberTheory.SelbergSieve

/-!
A concrete weighted sieve model for page 16 sequence A and page 17 display 58.
Zero density primes are omitted from the sieve support. This enlarges the sifted
set and preserves an upper bound. Fiber weights preserve multiplicities exactly.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Task506e

open Real Task506b Task506d
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Page 17, the positive density primes strictly below the roughness cutoff. -/
noncomputable def primeSupport (X δ : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range (⌊Real.exp (Real.log X ^ (1 - δ / 2))⌋₊ + 1)).filter
    (fun p => p.Prime ∧ (p : ℝ) < Real.exp (Real.log X ^ (1 - δ / 2)) ∧ 0 < density n p)

/-- Page 13 sieve setup, the squarefree product of the selected primes. -/
noncomputable def primeProduct (X δ : ℝ) (n : ℕ) : ℕ := (primeSupport X δ n).prod id

/-- Page 13 sieve setup, distinct selected primes have a squarefree product. -/
theorem primeProduct_squarefree (X δ : ℝ) (n : ℕ) : Squarefree (primeProduct X δ n) := by
  unfold primeProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (Finset.mem_filter.mp hp).2.1.squarefree)
  change IsRelPrime p q
  rw [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2.1
    (Finset.mem_filter.mp hq).2.1).mpr hpq

/-- Page 13 sieve setup, every prime divisor of the selected product is selected. -/
theorem prime_mem_of_dvd_product (X δ : ℝ) (n p : ℕ) (hp : p.Prime)
    (hd : p ∣ primeProduct X δ n) : p ∈ primeSupport X δ n := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
  have hqp := (Finset.mem_filter.mp hq).2.1
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq
  simpa only [heq] using hq

/-- Page 16 sequence A, with multiplicity from semiprime products q. -/
noncomputable def sequenceSupport (X B ε : ℝ) (n : ℕ) : Finset ℕ :=
  (semiprimes X B ε).image (fun q => n - q ^ 2)

/-- Page 16 sequence A, the number of semiprime products mapping to a fixed value m. -/
noncomputable def sequenceWeight (X B ε : ℝ) (n m : ℕ) : ℝ :=
  ((semiprimes X B ε).filter (fun q => n - q ^ 2 = m)).card

/-- Page 16, finite fiber summation preserves the sequence multiplicities. -/
theorem sequence_fiber_sum (X B ε : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ sequenceSupport X B ε n, sequenceWeight X B ε n m * f m) =
      ∑ q ∈ semiprimes X B ε, f (n - q ^ 2) := by
  unfold sequenceSupport sequenceWeight
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_fiberwise_of_maps_to' (s := semiprimes X B ε)
      (t := (semiprimes X B ε).image (fun q => n - q ^ 2))
      (g := fun q => n - q ^ 2) (fun q hq => Finset.mem_image_of_mem _ hq) f)

/-- Page 13 and page 17, the explicit finite sequence and density form a BoundingSieve. -/
noncomputable def sieveModel (X B δ ε : ℝ) (n : ℕ) (hn : InH2 n) : BoundingSieve where
  support := sequenceSupport X B ε n
  prodPrimes := primeProduct X δ n
  prodPrimes_squarefree := primeProduct_squarefree X δ n
  weights := sequenceWeight X B ε n
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := primeMass X B ε
  nu := densityFunction n
  nu_mult := density_isMultiplicative n
  nu_pos_of_prime := by
    intro p hp hd
    exact (Finset.mem_filter.mp (prime_mem_of_dvd_product X δ n p hp hd)).2.2.2
  nu_lt_one_of_prime := fun p hp _ => density_prime_lt_one n p hn hp

/-- Page 17, the weighted model progression count is exactly the stated A sub d count. -/
theorem model_multSum (X B δ ε : ℝ) (n d : ℕ) (hn : InH2 n) :
    (sieveModel X B δ ε n hn).multSum d = progressionCount X B ε n d := by
  change (∑ m ∈ sequenceSupport X B ε n, if d ∣ m then sequenceWeight X B ε n m else 0) = _
  have hf := sequence_fiber_sum X B ε n (fun m => if d ∣ m then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one, progressionCount] using hf

/-- Page 17, the model remainder equals the exact distribution error of the sequence. -/
theorem model_rem (X B δ ε : ℝ) (n d : ℕ) (hn : InH2 n) :
    (sieveModel X B δ ε n hn).rem d =
      progressionCount X B ε n d - density n d * primeMass X B ε := by
  rw [BoundingSieve.rem, model_multSum]
  rfl

/-- Page 16 display 56, the weighted sifted sum counts precisely the surviving semiprime products. -/
theorem model_siftedSum (X B δ ε : ℝ) (n : ℕ) (hn : InH2 n) :
    (sieveModel X B δ ε n hn).siftedSum =
      (((semiprimes X B ε).filter (fun q => (primeProduct X δ n).Coprime (n - q ^ 2))).card : ℝ) := by
  change (∑ m ∈ sequenceSupport X B ε n,
    if (primeProduct X δ n).Coprime m then sequenceWeight X B ε n m else 0) = _
  have hf := sequence_fiber_sum X B ε n
    (fun m => if (primeProduct X δ n).Coprime m then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one] using hf

/-- Page 16 display 57, the integral main term is nonnegative. -/
theorem primeMass_nonneg (X B ε : ℝ) : 0 ≤ primeMass X B ε := by
  unfold primeMass
  apply Finset.sum_nonneg
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  apply intervalIntegral.integral_nonneg (le_max_left _ _)
  intro u hu
  have hpu : (p : ℝ) ≤ u := (le_max_left _ _).trans hu.1
  have hlu : 0 < Real.log u := Real.log_pos (hp1.trans_le hpu)
  positivity

/-- Page 13 Lemma 3.7, level support and coefficients of norm at most one
bound the model error by the explicit squarefree remainder sum. -/
theorem model_errSum_le (X B δ ε : ℝ) (n : ℕ) (hn : InH2 n) (μ : ℕ → ℝ)
    (hlevel : ∀ d ∈ (primeProduct X δ n).divisors,
      Y X ε ^ (1 / 9 : ℝ) < (d : ℝ) → μ d = 0)
    (hbound : ∀ d ∈ (primeProduct X δ n).divisors, |μ d| ≤ 1) :
    (sieveModel X B δ ε n hn).errSum μ ≤ remainder X B ε n := by
  let D := Y X ε ^ (1 / 9 : ℝ)
  let S : Finset ℕ := (primeProduct X δ n).divisors.filter (fun (d : ℕ) => (d : ℝ) ≤ D)
  have hS : S ⊆ (primeProduct X δ n).divisors := Finset.filter_subset _ _
  have htruncate : (sieveModel X B δ ε n hn).errSum μ =
      ∑ d ∈ S, |μ d| * |(sieveModel X B δ ε n hn).rem d| := by
    unfold BoundingSieve.errSum
    symm
    apply Finset.sum_subset hS
    intro d hd hdS
    have hlarge : D < (d : ℝ) := by
      by_contra hh
      exact hdS (Finset.mem_filter.mpr ⟨hd, by linarith⟩)
    rw [hlevel d hd hlarge]
    simp
  have hsub : S ⊆ Finset.Icc 1 ⌊D⌋₊ := by
    intro d hd
    have hdd := (Finset.mem_filter.mp hd).1
    have hdD := (Finset.mem_filter.mp hd).2
    refine Finset.mem_Icc.mpr ⟨?_, Nat.le_floor hdD⟩
    exact Nat.pos_of_mem_divisors hdd
  calc _ = ∑ d ∈ S, |μ d| * |(sieveModel X B δ ε n hn).rem d| := htruncate
       _ ≤ ∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
           |progressionCount X B ε n d - density n d * primeMass X B ε| := by
         apply Finset.sum_le_sum
         intro d hd
         have hsq := (sieveModel X B δ ε n hn).squarefree_of_mem_divisors_prodPrimes (hS hd)
         have hmu : (ArithmeticFunction.moebius d : ℝ) ^ 2 = 1 := by
           exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
         rw [hmu, one_mul, model_rem]
         exact mul_le_of_le_one_left (abs_nonneg _) (hbound d (hS hd))
       _ ≤ ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
           |progressionCount X B ε n d - density n d * primeMass X B ε| :=
         Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _))
       _ = remainder X B ε n := rfl

/-- Page 17 display 58, the finite sieve model bound from supplied upper weights.
CONDITIONAL on the explicit weight and main sum hypotheses. -/
theorem model_upper_of_weights (X B δ ε C : ℝ) (n : ℕ) (hn : InH2 n) (μ : ℕ → ℝ)
    (hupper : BoundingSieve.IsUpperMoebius μ)
    (hlevel : ∀ d ∈ (primeProduct X δ n).divisors,
      Y X ε ^ (1 / 9 : ℝ) < (d : ℝ) → μ d = 0)
    (hbound : ∀ d ∈ (primeProduct X δ n).divisors, |μ d| ≤ 1)
    (hmain : (sieveModel X B δ ε n hn).mainSum μ ≤ C * sieveProduct X δ n) :
    (sieveModel X B δ ε n hn).siftedSum ≤
      C * (primeMass X B ε * sieveProduct X δ n) + remainder X B ε n := by
  calc _ ≤ primeMass X B ε * (sieveModel X B δ ε n hn).mainSum μ +
         (sieveModel X B δ ε n hn).errSum μ :=
           (sieveModel X B δ ε n hn).siftedSum_le_mainSum_errSum_of_upperMoebius μ hupper
       _ ≤ primeMass X B ε * (C * sieveProduct X δ n) + remainder X B ε n :=
         add_le_add (mul_le_mul_of_nonneg_left hmain (primeMass_nonneg X B ε))
           (model_errSum_le X B δ ε n hn μ hlevel hbound)
       _ = _ := by ring

end LeanLab.KumchevLiu2007.Task506e
