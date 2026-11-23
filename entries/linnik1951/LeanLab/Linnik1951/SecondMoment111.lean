module

public import LeanLab.Linnik1951.Decomp111
public import LeanLab.Romanov.Moment

/-!
P0093 Lemma 3 on page 162. This isolates the outside Romanov input used in Decomp111.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open scoped BigOperators
open Finset

/-- P0093 page 162. Number of solutions of p plus 2 to a positive exponent equals u. -/
noncomputable def primePowerCount111 (u : ℕ) : ℕ := by
  classical
  exact (univ.filter fun t : Fin (u + 1) × Fin (u + 1) =>
    t.1.val.Prime ∧ 1 ≤ t.2.val ∧ u = t.1.val + 2 ^ t.2.val).card

/-- P0093 page 154. Exponentially damped prime Fourier series. -/
noncomputable def primeFourier111 (N : ℕ) (α : ℝ) : ℂ :=
  ∑' p : Nat.Primes,
    (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)

/-- P0093 pages 154 and 161. Exponentially damped positive powers of two Fourier series. -/
noncomputable def powerFourier111 (N : ℕ) (α : ℝ) : ℂ :=
  ∑' m : ℕ,
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)

/-- CITED. P0093 page 162 Lemma 3, equation 7.3. -/
def LemmaThree111 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    (∫ α in (0 : ℝ)..1, ‖primeFourier111 N α * powerFourier111 N α‖ ^ 2) < C * N

/-- P0093 page 162. The count agrees with the existing lab Romanov count. -/
theorem primePowerCount_eq_romanov111 (u : ℕ) :
    primePowerCount111 u = LeanLab.Romanov.repCount u := by
  classical
  unfold primePowerCount111 LeanLab.Romanov.repCount
  apply Finset.card_bij (fun t _ => (t.1.val, t.2.val))
  · intro t ht
    obtain ⟨_, hp, hx, heq⟩ := Finset.mem_filter.mp ht
    exact (LeanLab.Romanov.mem_representations _ _).mpr ⟨hp, hx, heq.symm⟩
  · intro a ha b hb heq
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst heq)
    · exact Fin.ext (congrArg Prod.snd heq)
  · intro t ht
    obtain ⟨hp, hx, heq⟩ := (LeanLab.Romanov.mem_representations _ _).mp ht
    have hpN : t.1 < u + 1 := by
      have hle : t.1 ≤ t.1 + 2 ^ t.2 := Nat.le_add_right _ _
      dsimp [LeanLab.Romanov.f] at heq
      omega
    have hxN : t.2 < u + 1 := by
      have hpow : t.2 < 2 ^ t.2 := Nat.lt_two_pow_self
      dsimp [LeanLab.Romanov.f] at heq
      omega
    refine ⟨(⟨t.1, hpN⟩, ⟨t.2, hxN⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp, hx, heq.symm⟩

/-- LEAF. P0093 page 162 equation 7.5, cited from N. P. Romanov,
On some theorems of additive number theory, Uspekhi Mat. Nauk 1940 issue VII,
reference 4 in P0093. This is an outside published result. -/
theorem romanov_second_moment111 :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      ∑ u ∈ range M, (primePowerCount111 u : ℝ) ^ 2 ≤ C * M := by
  have hR := LeanLab.Romanov.R₁_pos
  refine ⟨4 * (9 + 2 * LeanLab.Romanov.R₁), by positivity, ?_⟩
  intro M
  simp_rw [primePowerCount_eq_romanov111]
  calc
    _ ≤ ∑ u ∈ range (M + 1), (LeanLab.Romanov.repCount u : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ M))
        (fun i hi hnot => sq_nonneg _)
    _ ≤ _ := LeanLab.Romanov.romanov_second_moment M

/-- LEAF. P0093 page 162, substitution of equation 7.5 into equation 7.4.
Finite summation by parts compares a weighted sequence with its prefix bound. -/
theorem geometric_partial_bound111 (a : ℕ → ℝ) (C r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : ∀ n, ∑ i ∈ range n, a i ≤ C * n) (n : ℕ) :
    ∑ i ∈ range n, a i * r ^ i ≤ ∑ i ∈ range n, C * r ^ i := by
  have hparts := sum_range_by_parts' a (fun i => r ^ i) n
  have hcparts := sum_range_by_parts' (fun _ => C) (fun i => r ^ i) n
  simp only [smul_eq_mul, sum_const, card_range, nsmul_eq_mul] at hparts hcparts
  rw [hparts, hcparts]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_right (by simpa only [mul_comm] using ha n) (pow_nonneg hr _)
  · apply sum_le_sum
    intro i hi
    have hdiff : r ^ (i + 1) - r ^ i ≤ 0 := by
      rw [pow_succ]
      nlinarith [pow_nonneg hr i]
    exact mul_le_mul_of_nonpos_right (by simpa only [mul_comm] using ha (i + 1)) hdiff

/-- LEAF. P0093 page 162, substitution of equation 7.5 into equation 7.4.
A nonnegative sequence with linear prefix bounds has a geometric sum bound. -/
theorem geometric_tsum_bound111 (a : ℕ → ℝ) (C r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C) (ha : ∀ n, 0 ≤ a n)
    (hprefix : ∀ n, ∑ i ∈ range n, a i ≤ C * n) :
    (∑' i, a i * r ^ i) ≤ C / (1 - r) := by
  apply Real.tsum_le_of_sum_range_le (fun n => mul_nonneg (ha n) (pow_nonneg hr n))
  intro n
  calc
    _ ≤ ∑ i ∈ range n, C * r ^ i := geometric_partial_bound111 a C r hr hr1.le hprefix n
    _ ≤ ∑' i : ℕ, C * r ^ i :=
      ((summable_geometric_of_lt_one hr hr1).mul_left C).sum_le_tsum _
        (fun i _ => mul_nonneg hC (pow_nonneg hr i))
    _ = C / (1 - r) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1]; ring

/-- LEAF. P0093 page 162, substitution of equation 7.5 into equation 7.4.
The exponential geometric denominator is at most a constant times N. -/
theorem exponential_denominator111 (N : ℝ) (hN : 1 ≤ N) :
    1 / (1 - Real.exp (-2 / N)) ≤ 2 * N := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hx : 0 < 2 / N := div_pos (by norm_num) hNp
  have he : 1 + 2 / N ≤ Real.exp (2 / N) := by simpa only [add_comm] using Real.add_one_le_exp (2 / N)
  have hex : Real.exp (-2 / N) = (Real.exp (2 / N))⁻¹ := by rw [neg_div, Real.exp_neg]
  have hlt : Real.exp (-2 / N) < 1 := Real.exp_lt_one_iff.mpr (by rw [neg_div]; linarith)
  rw [hex]
  apply (div_le_iff₀ (by rw [← hex]; linarith)).mpr
  have hepos := Real.exp_pos (2 / N)
  have heN := mul_le_mul_of_nonneg_left he hNp.le
  have he1 : 1 ≤ Real.exp (2 / N) := by linarith
  have haux := mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr he1)
  field_simp [ne_of_gt hNp] at heN
  apply (mul_le_mul_iff_right₀ hepos).mp
  calc
    Real.exp (2 / N) * 1 ≤ 2 * N * (Real.exp (2 / N) - 1) := by nlinarith
    _ = Real.exp (2 / N) * (2 * N * (1 - (Real.exp (2 / N))⁻¹)) := by
      field_simp


/-- LEAF. P0093 page 162, substitution of equation 7.5 into equation 7.4.
This states the resulting Laplace bound independently of Fourier analysis. -/
theorem laplace_bound111 (a : ℕ → ℝ) (C : ℝ) (N : ℕ)
    (hN : 1 ≤ N) (hC : 0 ≤ C) (ha : ∀ n, 0 ≤ a n)
    (hprefix : ∀ n, ∑ i ∈ range n, a i ≤ C * n) :
    (∑' u : ℕ, a u * Real.exp (-2 * u / N)) ≤ 2 * C * N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hr : 0 ≤ Real.exp (-2 / (N : ℝ)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-2 / (N : ℝ)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (by norm_num) hNp
  have heq : ∀ u : ℕ, Real.exp (-2 * u / (N : ℝ)) = Real.exp (-2 / (N : ℝ)) ^ u := by
    intro u
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [heq]
  calc
    _ ≤ C / (1 - Real.exp (-2 / (N : ℝ))) :=
      geometric_tsum_bound111 a C _ hr hr1 hC ha hprefix
    _ = C * (1 / (1 - Real.exp (-2 / (N : ℝ)))) := by ring
    _ ≤ C * (2 * N) := mul_le_mul_of_nonneg_left (exponential_denominator111 N hNr) hC
    _ = 2 * C * N := by ring

/-- P0093 page 154. Absolute convergence of exponential damping over all natural numbers. -/
theorem damping_summable111 (N : ℕ) (hN : 1 ≤ N) : Summable (fun n : ℕ => Real.exp (-(n : ℝ) / N)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr1 : Real.exp (-1 / (N : ℝ)) < 1 := Real.exp_lt_one_iff.mpr
    (div_neg_of_neg_of_pos (by norm_num) hNp)
  have h := summable_geometric_of_lt_one (Real.exp_pos (-1 / (N : ℝ))).le hr1
  convert h using 1
  ext n
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- P0093 page 154. Absolute convergence of the damped prime Fourier series. -/
theorem prime_fourier_summable111 (N : ℕ) (hN : 1 ≤ N) (α : ℝ)
    :
    Summable (fun p : Nat.Primes =>
      (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)) := by
  have hg := damping_summable111 N hN
  apply Summable.of_norm
  have hp : Summable (fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N)) :=
    hg.comp_injective Nat.Primes.coe_nat_injective
  simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hp


/-- P0093 pages 154 and 161. Absolute convergence of the damped powers of two series. -/
theorem power_fourier_summable111 (N : ℕ) (hN : 1 ≤ N) (α : ℝ)
    :
    Summable (fun m : ℕ =>
      (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)) := by
  have hg := damping_summable111 N hN
  apply Summable.of_norm
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
  have hp := hg.comp_injective hi
  convert hp using 1
  ext m
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Function.comp_apply]

/-- P0093 page 154. The damped prime Fourier series defines a continuous function. -/
theorem continuous_prime_fourier111 (N : ℕ) (hN : 1 ≤ N) : Continuous (primeFourier111 N) := by
  unfold primeFourier111
  apply continuous_tsum
    (u := fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N))
  · intro p
    fun_prop
  · exact (damping_summable111 N hN).comp_injective Nat.Primes.coe_nat_injective
  · intro p α
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), le_refl]

/-- P0093 pages 154 and 161. The damped powers of two series is continuous. -/
theorem continuous_power_fourier111 (N : ℕ) (hN : 1 ≤ N) : Continuous (powerFourier111 N) := by
  unfold powerFourier111
  apply continuous_tsum
    (u := fun m : ℕ => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N))
  · intro m
    fun_prop
  · have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
      (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
    exact (damping_summable111 N hN).comp_injective hi
  · intro m α
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), le_refl]

/-- P0093 page 162 equation 7.4. Abstract Parseval for the continuous product of the two series. -/
theorem fourier_parseval111 (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖primeFourier111 N α * powerFourier111 N α‖ ^ 2) =
      ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun α => primeFourier111 N α * powerFourier111 N α) i‖ ^ 2 := by
  have hf := (continuous_prime_fourier111 N hN).mul (continuous_power_fourier111 N hN)
  have hs : IntervalIntegrable (fun α => ‖primeFourier111 N α * powerFourier111 N α‖ ^ 2)
      MeasureTheory.volume 0 1 := (hf.norm.pow 2).intervalIntegrable 0 1
  have hL2 : MeasureTheory.MemLp (fun α => primeFourier111 N α * powerFourier111 N α) 2
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hs.1
  simpa using (tsum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hL2).symm

/-- P0093 page 162 equation 7.4. Reindex a square norm sum supported on nonpositive frequencies. -/
theorem negative_modes_sum111 (a : ℕ → ℂ) (f : ℤ → ℂ)
    (hf : ∀ i : ℤ, f i = if i ≤ 0 then a i.natAbs else 0) :
    (∑' i : ℤ, ‖f i‖ ^ 2) = ∑' n : ℕ, ‖a n‖ ^ 2 := by
  have hi : Function.Injective (fun n : ℕ => -(n : ℤ)) := neg_injective.comp Nat.cast_injective
  have hsup : Function.support (fun i : ℤ => ‖f i‖ ^ 2) ⊆ Set.range (fun n : ℕ => -(n : ℤ)) := by
    intro i hi'
    by_cases h : i ≤ 0
    · cases i with
      | ofNat n =>
        change (n : ℤ) ≤ 0 at h
        refine ⟨0, ?_⟩
        change -(0 : ℤ) = (n : ℤ)
        omega
      | negSucc n =>
        refine ⟨n + 1, ?_⟩
        change -((n + 1 : ℕ) : ℤ) = Int.negSucc n
        omega
    · simp [Function.mem_support, hf i, h] at hi'
  have h := hi.tsum_eq hsup
  have heq : ∀ n : ℕ, ‖f (-(n : ℤ))‖ ^ 2 = ‖a n‖ ^ 2 := by
    intro n
    rw [hf]
    simp
  simpa only [heq] using h.symm

/-- LEAF. P0093 page 162 equation 7.4. Identify the Fourier coefficients of
the product by grouping prime and positive power pairs with the same sum.
Abstract Parseval, convergence and frequency reindexing are proved separately. -/
theorem fourier_coefficient111 (N : ℕ) (hN : 1 ≤ N) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => primeFourier111 N α * powerFourier111 N α) i =
        if i ≤ 0 then
          ((primePowerCount111 i.natAbs : ℝ) * Real.exp (-(i.natAbs : ℝ) / N) : ℂ)
        else 0 := by
  exact fourier_coefficient_proved357_up111 N hN i

/-- P0093 page 162 equation 7.4. CONDITIONAL only on fourier_coefficient111.
Abstract Parseval and the zero extension reindexing are proved. -/
theorem parseval_second_moment111 (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖primeFourier111 N α * powerFourier111 N α‖ ^ 2) =
      ∑' u : ℕ, (primePowerCount111 u : ℝ) ^ 2 * Real.exp (-2 * u / N) := by
  calc
    _ = ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
          (fun α => primeFourier111 N α * powerFourier111 N α) i‖ ^ 2 :=
      fourier_parseval111 N hN
    _ = ∑' u : ℕ,
          ‖((primePowerCount111 u : ℝ) * Real.exp (-(u : ℝ) / N) : ℂ)‖ ^ 2 :=
      negative_modes_sum111 _ _ (fourier_coefficient111 N hN)
    _ = _ := by
      apply tsum_congr
      intro u
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
      rw [← Real.exp_nat_mul]
      congr 2
      ring

/-- P0093 page 162 Lemma 3. CONDITIONAL only on the Fourier coefficient identification leaf.
The assembly contains no placeholder proof. -/
theorem lemma_three_decomposed111 : LemmaThree111 := by
  obtain ⟨C, hC, hprefix⟩ := romanov_second_moment111
  refine ⟨3 * C, by positivity, ?_⟩
  intro N hN
  rw [parseval_second_moment111 N hN]
  have h := laplace_bound111 (fun u => (primePowerCount111 u : ℝ) ^ 2)
    C N hN hC.le (fun u => sq_nonneg _) hprefix
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  nlinarith


end LeanLab.Linnik1951
