module

public import LeanLab.KumchevLiu2007.Decomp506g

/-!
Truncated window sieve route for the transition regime of Kumchev and Liu, arXiv 0801.0130.
This file reruns the weighted sieve model of pages 16 and 17, displays 56 to 59, on the
truncated semiprime sequence, the semiprime products q with a real cut a at most q.
The sieve weights and the main sum come unchanged from Task506g.upper_weights, because
the Mathlib main sum depends only on the density and on the product of the sifting primes.
No new definition is made. The truncated sieve is built inside a proof term.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Trunc129

open Real LeanLab.KumchevLiu2007 Task506b Task506c Task506d Task506e Task506f Task506g
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Page 16 sequence A before display 56, truncated window version for an arbitrary finite
set T of products q. Finite fiber summation over the values n minus q squared preserves
the multiplicities. -/
theorem trunc_fiber_sum (T : Finset ℕ) (n : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ T.image (fun q => n - q ^ 2),
        ((T.filter (fun q => n - q ^ 2 = m)).card : ℝ) * f m) =
      ∑ q ∈ T, f (n - q ^ 2) := by
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_fiberwise_of_maps_to' (s := T)
      (t := T.image (fun q => n - q ^ 2))
      (g := fun q => n - q ^ 2) (fun q hq => Finset.mem_image_of_mem _ hq) f)

/-- Page 16 display 56, truncated window version. For any sieve whose support and weights
are the fiber counts of a finite set T, the weighted sifted sum counts the surviving q. -/
theorem trunc_fiber_siftedSum (s : BoundingSieve) (T : Finset ℕ) (n : ℕ)
    (hsup : s.support = T.image (fun q => n - q ^ 2))
    (hw : s.weights = fun m => ((T.filter (fun q => n - q ^ 2 = m)).card : ℝ)) :
    s.siftedSum = ((T.filter (fun q => s.prodPrimes.Coprime (n - q ^ 2))).card : ℝ) := by
  calc s.siftedSum = ∑ m ∈ T.image (fun q => n - q ^ 2),
        ((T.filter (fun q => n - q ^ 2 = m)).card : ℝ) *
          (if s.prodPrimes.Coprime m then (1 : ℝ) else 0) := by
        unfold BoundingSieve.siftedSum
        rw [hsup, hw]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        split_ifs <;> simp
    _ = ∑ q ∈ T, (if s.prodPrimes.Coprime (n - q ^ 2) then (1 : ℝ) else 0) :=
        trunc_fiber_sum T n (fun m => if s.prodPrimes.Coprime m then (1 : ℝ) else 0)
    _ = _ := Finset.sum_boole (fun q => s.prodPrimes.Coprime (n - q ^ 2)) T

/-- Page 17 before display 58, truncated window version. For any sieve whose support and
weights are the fiber counts of a finite set T, the progression sum at modulus d counts
the q in T with d dividing n minus q squared. -/
theorem trunc_fiber_multSum (s : BoundingSieve) (T : Finset ℕ) (n d : ℕ)
    (hsup : s.support = T.image (fun q => n - q ^ 2))
    (hw : s.weights = fun m => ((T.filter (fun q => n - q ^ 2 = m)).card : ℝ)) :
    s.multSum d = ((T.filter (fun q => d ∣ n - q ^ 2)).card : ℝ) := by
  calc s.multSum d = ∑ m ∈ T.image (fun q => n - q ^ 2),
        ((T.filter (fun q => n - q ^ 2 = m)).card : ℝ) *
          (if d ∣ m then (1 : ℝ) else 0) := by
        unfold BoundingSieve.multSum
        rw [hsup, hw]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        split_ifs <;> simp
    _ = ∑ q ∈ T, (if d ∣ n - q ^ 2 then (1 : ℝ) else 0) :=
        trunc_fiber_sum T n (fun m => if d ∣ m then (1 : ℝ) else 0)
    _ = _ := Finset.sum_boole (fun q => d ∣ n - q ^ 2) T

/-- Page 13 Lemma 3.7 and page 17 before display 58, truncated window version. Level
support and coefficients of absolute value at most one bound the sieve error sum by the
explicit squarefree remainder sum of the finite set T. -/
theorem trunc_errSum_le (s : BoundingSieve) (T : Finset ℕ) (n : ℕ) (D : ℝ) (μ : ℕ → ℝ)
    (hsup : s.support = T.image (fun q => n - q ^ 2))
    (hw : s.weights = fun m => ((T.filter (fun q => n - q ^ 2 = m)).card : ℝ))
    (hlevel : ∀ d ∈ s.prodPrimes.divisors, D < (d : ℝ) → μ d = 0)
    (hbound : ∀ d ∈ s.prodPrimes.divisors, |μ d| ≤ 1) :
    s.errSum μ ≤ ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
      |((T.filter (fun q => d ∣ n - q ^ 2)).card : ℝ) - s.nu d * s.totalMass| := by
  let S : Finset ℕ := s.prodPrimes.divisors.filter (fun (d : ℕ) => (d : ℝ) ≤ D)
  have hS : S ⊆ s.prodPrimes.divisors := Finset.filter_subset _ _
  have htruncate : s.errSum μ = ∑ d ∈ S, |μ d| * |s.rem d| := by
    unfold BoundingSieve.errSum
    symm
    apply Finset.sum_subset hS
    intro d hd hdS
    have hlarge : D < (d : ℝ) := by
      by_contra hh
      exact hdS (Finset.mem_filter.mpr ⟨hd, by linarith⟩)
    rw [hlevel d hd hlarge, abs_zero, zero_mul]
  have hsub : S ⊆ Finset.Icc 1 ⌊D⌋₊ := by
    intro d hd
    have hdd := (Finset.mem_filter.mp hd).1
    have hdD := (Finset.mem_filter.mp hd).2
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdd, Nat.le_floor hdD⟩
  calc s.errSum μ = ∑ d ∈ S, |μ d| * |s.rem d| := htruncate
    _ ≤ ∑ d ∈ S, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |((T.filter (fun q => d ∣ n - q ^ 2)).card : ℝ) - s.nu d * s.totalMass| := by
        apply Finset.sum_le_sum
        intro d hd
        have hsq := s.squarefree_of_mem_divisors_prodPrimes (hS hd)
        have hmu : (ArithmeticFunction.moebius d : ℝ) ^ 2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
        rw [hmu, one_mul, BoundingSieve.rem, trunc_fiber_multSum s T n d hsup hw]
        exact mul_le_of_le_one_left (abs_nonneg _) (hbound d (hS hd))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _))

/-- Page 13 sieve setup and page 17 before display 58, truncated window version. For any
finite set T of products q and any real mass M there is a sieve with the fiber counts of
T as weighted support, the page 17 density, the selected prime product and total mass M. -/
theorem trunc_sieve_exists (X δ M : ℝ) (n : ℕ) (hn : InH2 n) (T : Finset ℕ) :
    ∃ s : BoundingSieve, s.support = T.image (fun q => n - q ^ 2) ∧
      s.prodPrimes = primeProduct X δ n ∧
      (s.weights = fun m => ((T.filter (fun q => n - q ^ 2 = m)).card : ℝ)) ∧
      s.totalMass = M ∧ s.nu = densityFunction n :=
  ⟨{ support := T.image (fun q => n - q ^ 2)
     prodPrimes := primeProduct X δ n
     prodPrimes_squarefree := primeProduct_squarefree X δ n
     weights := fun m => ((T.filter (fun q => n - q ^ 2 = m)).card : ℝ)
     weights_nonneg := fun _ => Nat.cast_nonneg _
     totalMass := M
     nu := densityFunction n
     nu_mult := density_isMultiplicative n
     nu_pos_of_prime := fun p hp hd =>
       (Finset.mem_filter.mp (prime_mem_of_dvd_product X δ n p hp hd)).2.2.2
     nu_lt_one_of_prime := fun p hp _ => density_prime_lt_one n p hn hp },
    rfl, rfl, rfl, rfl, rfl⟩

/-- Page 17 display 58, truncated window version of the finite sieve model bound from
supplied upper weights, for an arbitrary finite set T of products q and an arbitrary
nonnegative mass M. The main sum hypothesis is the one of the untruncated model, since the
main sum depends only on the density and the selected prime product. -/
theorem trunc_model_upper (X B δ ε C M : ℝ) (n : ℕ) (hn : InH2 n) (T : Finset ℕ)
    (hM : 0 ≤ M) (μ : ℕ → ℝ)
    (hupper : BoundingSieve.IsUpperMoebius μ)
    (hlevel : ∀ d ∈ (primeProduct X δ n).divisors,
      Y X ε ^ (1 / 9 : ℝ) < (d : ℝ) → μ d = 0)
    (hbound : ∀ d ∈ (primeProduct X δ n).divisors, |μ d| ≤ 1)
    (hmain : (sieveModel X B δ ε n hn).mainSum μ ≤ C * sieveProduct X δ n) :
    ((T.filter (fun q => (primeProduct X δ n).Coprime (n - q ^ 2))).card : ℝ) ≤
      C * (M * sieveProduct X δ n) +
        ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |((T.filter (fun q => d ∣ n - q ^ 2)).card : ℝ) - density n d * M| := by
  obtain ⟨s, hsup, hP, hw, hmass, hnu⟩ := trunc_sieve_exists X δ M n hn T
  have h1 := s.siftedSum_le_mainSum_errSum_of_upperMoebius μ hupper
  have hs := trunc_fiber_siftedSum s T n hsup hw
  rw [hP] at hs
  have hmainS : s.mainSum μ = (sieveModel X B δ ε n hn).mainSum μ := by
    unfold BoundingSieve.mainSum
    rw [hP, hnu]
    rfl
  have herr := trunc_errSum_le s T n (Y X ε ^ (1 / 9 : ℝ)) μ hsup hw
    (by rw [hP]; exact hlevel) (by rw [hP]; exact hbound)
  rw [hnu, hmass] at herr
  have herr' : s.errSum μ ≤
      ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |((T.filter (fun q => d ∣ n - q ^ 2)).card : ℝ) - density n d * M| := herr
  rw [hmass, hmainS] at h1
  rw [← hs]
  calc s.siftedSum ≤ M * (sieveModel X B δ ε n hn).mainSum μ + s.errSum μ := h1
    _ ≤ M * (C * sieveProduct X δ n) +
        ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |((T.filter (fun q => d ∣ n - q ^ 2)).card : ℝ) - density n d * M| :=
        add_le_add (mul_le_mul_of_nonneg_left hmain hM) herr'
    _ = _ := by ring

/-- Page 16 display 57, truncated window version. The truncated integral main term is
nonnegative for every real cut a, since each integral runs from its lower endpoint to a
larger endpoint over a positive integrand. -/
theorem trunc_mass_nonneg (X B ε a : ℝ) :
    0 ≤ (∑ p ∈ primeWindow X B ε, ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p), 1 / Real.log u) := by
  apply Finset.sum_nonneg
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  apply intervalIntegral.integral_nonneg (le_max_left _ _)
  intro u hu
  have h1 : (p : ℝ) ≤ jlo X ε p := le_max_left _ _
  have h2 : jlo X ε p ≤ max (jlo X ε p) (a / p) := le_max_left _ _
  have hpu : (p : ℝ) ≤ u := h1.trans (h2.trans hu.1)
  have hlu : 0 < Real.log u := Real.log_pos (hp1.trans_le hpu)
  exact (one_div_pos.mpr hlu).le

/-- Page 17 before display 58, truncated window version. The squarefree remainder sum of
an arbitrary finite set T with an arbitrary mass M is nonnegative. -/
theorem trunc_rem_nonneg (T : Finset ℕ) (n : ℕ) (D M : ℝ) :
    0 ≤ ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
      |((T.filter (fun q => d ∣ n - q ^ 2)).card : ℝ) - density n d * M| :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _)

/-- Page 17 display 58, truncated window version of the last arithmetic step. A bound with
constant C on the main term and constant one on the remainder gives the bound with the
single constant C plus one. -/
theorem trunc_final_arith (C M V R c : ℝ) (hC : 0 ≤ C) (hMV : 0 ≤ M * V) (hR : 0 ≤ R)
    (h : c ≤ C * (M * V) + R) : c ≤ (C + 1) * (M * V + R) := by
  nlinarith [mul_nonneg hC hR]

/-- Page 17 display 58 with page 13 Lemma 3.7, truncated window version of the Rosser sieve
application of pages 16 and 17, displays 56 to 59. The semiprime sequence is cut to the
products q with a at most q, the main term is the truncated integral mass of display 57
times the sieve product, and the error is the truncated squarefree remainder sum at level
Y to the one ninth. The upper weights are those of Task506g.upper_weights. -/
theorem trunc_rosser (B δ ε : ℝ) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) → ∀ a : ℝ,
      Real.sqrt (Y X ε) / 2 ≤ a → a ≤ Real.sqrt (Y X ε) →
      ((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter
          (fun q => (Task506e.primeProduct X δ n).Coprime (n - q ^ 2))).card : ℝ) ≤
        C * ((∑ p ∈ primeWindow X B ε, ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p), 1 / Real.log u) *
              sieveProduct X δ n +
            (∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
              |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter (fun q => d ∣ n - q ^ 2)).card : ℝ) -
                density n d * (∑ p ∈ primeWindow X B ε, ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p), 1 / Real.log u)|)) := by
  obtain ⟨C, Xw, hC, hw⟩ := upper_weights B δ ε hB hδ hδ1 hε hε1
  refine ⟨C + 1, Xw, by linarith, ?_⟩
  intro X hX n hn _ a _ _
  obtain ⟨μ, hupper, hlevel, hbound, hmain⟩ := hw X hX n hn
  have hM := trunc_mass_nonneg X B ε a
  have hb := trunc_model_upper X B δ ε C _ n hn
    ((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))) hM μ hupper hlevel hbound hmain
  exact trunc_final_arith C _ _ _ _ hC.le (mul_nonneg hM (sieveProduct_nonneg X δ n))
    (trunc_rem_nonneg _ n _ _) hb

/-- Page 16 display 56, truncated window version of the support bridge. For X below n every
sifted window pair has its second coordinate in the semiprime sequence, at least half the
square root of Y by the window, and at least the square root of n minus X because the
first coordinate is below X. So the sifted pair count is at most the sifted count of the
truncated semiprime sequence with cut the larger of these two bounds. -/
theorem trunc_sifted_le (B δ ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) → (n : ℝ) < X + Y X ε →
      siftedCount X B δ ε n ≤
        ((((semiprimes X B ε).filter (fun q : ℕ => max (Real.sqrt (Y X ε) / 2) (Real.sqrt ((n : ℝ) - X)) ≤ (q : ℝ))).filter
          (fun q => (Task506e.primeProduct X δ n).Coprime (n - q ^ 2))).card : ℝ) := by
  obtain ⟨Xp, hp⟩ := Filter.eventually_atTop.mp (rough_support_parameters B ε hB hε)
  refine ⟨Xp, ?_⟩
  intro X hX n _ _ _
  obtain ⟨hY, hwindow, hz, hcube⟩ := hp X hX
  unfold siftedCount
  apply Nat.cast_le.mpr
  apply representation_pairs_le_window _ _ n
  · intro v hv
    obtain ⟨hvW, hmrough, hqnp, hqrough⟩ := Finset.mem_filter.mp hv
    obtain ⟨hvprod, hmlo, hmhi, hqlo, hqhi, hrep⟩ := Finset.mem_filter.mp hvW
    have hqrange := (Finset.mem_product.mp hvprod).2
    have hqsem := rough_pair_semiprime X B ε v.2 hY hwindow hz hcube hqrange hqlo hqhi hqnp hqrough
    have hrepR : (v.1 : ℝ) + (v.2 : ℝ) ^ 2 = (n : ℝ) := by exact_mod_cast hrep
    have hcut : max (Real.sqrt (Y X ε) / 2) (Real.sqrt ((n : ℝ) - X)) ≤ (v.2 : ℝ) := by
      refine max_le hqlo ?_
      exact Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _, by linarith⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hqsem, hcut⟩, ?_⟩
    have hm : n - v.2 ^ 2 = v.1 := by omega
    rw [hm]
    unfold primeProduct
    apply Nat.Coprime.prod_left
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2.1
    have hplt := (Finset.mem_filter.mp hp).2.2.1
    exact hpp.coprime_iff_not_dvd.mpr (fun hd => (not_lt_of_ge (hmrough p hpp hd)) hplt)
  · intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.2.2.2.2

end LeanLab.KumchevLiu2007.Trunc129

