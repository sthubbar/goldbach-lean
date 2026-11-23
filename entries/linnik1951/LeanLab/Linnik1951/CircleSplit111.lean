module

public import LeanLab.Linnik1951.Conventions
public import LeanLab.Romanov.Moment
public import LeanLab.Perelli1996.Kernel
public import LeanLab.Perelli1996.Parseval103

/-!
P0093 page 154 equation 2.2, page 162 Lemma 3 equations 7.3 to 7.5, and
page 167 equations 10.1 and 10.2. Upstream port of the proved circle method
identity and minor arc bound, so that the SPLIT lemmas of error_bound111 in
Decomp111 can be proved without an import cycle.
AI wrote the Lean code. Binary Goldbach is open.
Every declaration here is a renamed copy, suffix _up111, of an already proved
declaration in SecondMoment111, Decomp280b, Decomp357c to Decomp357j,
SPLIT_count_circle_coefficient357 and Circle435, which all import Decomp111
and so cannot be used by it. The romanov_second_moment input is the lab proof
in LeanLab.Romanov.Moment.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-! Ported from Decomp111. -/
section
open LeanLab.Linnik LeanLab.DERZ1997
open Finset

/-- Ordered representations in P0093 equation 2.1, page 154.
The finite bounds lose no representations because each summand is at most N. -/
noncomputable def representationCount111_up111 (k N : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun t : Fin (N + 1) × Fin (N + 1) × (Fin k → Fin (N + 1)) =>
    (t.1.val).Prime ∧ (t.2.1.val).Prime ∧ (∀ i, 1 ≤ (t.2.2 i).val) ∧
      N = t.1.val + t.2.1.val + ∑ i, 2 ^ (t.2.2 i).val).card

/-- The positive scale in P0093 Section 11, page 169. -/
noncomputable def scale111_up111 (k N : ℕ) : ℝ :=
  N * (Real.log N / Real.log 2) ^ (k - 2)

end

/-! Ported from SecondMoment111. -/
section
open scoped BigOperators
open Finset

/-- P0093 page 162. Number of solutions of p plus 2 to a positive exponent equals u. -/
noncomputable def primePowerCount111_up111 (u : ℕ) : ℕ := by
  classical
  exact (univ.filter fun t : Fin (u + 1) × Fin (u + 1) =>
    t.1.val.Prime ∧ 1 ≤ t.2.val ∧ u = t.1.val + 2 ^ t.2.val).card

/-- P0093 page 154. Exponentially damped prime Fourier series. -/
noncomputable def primeFourier111_up111 (N : ℕ) (α : ℝ) : ℂ :=
  ∑' p : Nat.Primes,
    (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)

/-- P0093 pages 154 and 161. Exponentially damped positive powers of two Fourier series. -/
noncomputable def powerFourier111_up111 (N : ℕ) (α : ℝ) : ℂ :=
  ∑' m : ℕ,
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)

/-- CITED. P0093 page 162 Lemma 3, equation 7.3. -/
def LemmaThree111_up111 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    (∫ α in (0 : ℝ)..1, ‖primeFourier111_up111 N α * powerFourier111_up111 N α‖ ^ 2) < C * N

/-- P0093 page 162. The count agrees with the existing lab Romanov count. -/
theorem primePowerCount_eq_romanov111_up111 (u : ℕ) :
    primePowerCount111_up111 u = LeanLab.Romanov.repCount u := by
  classical
  unfold primePowerCount111_up111 LeanLab.Romanov.repCount
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
theorem romanov_second_moment111_up111 :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      ∑ u ∈ range M, (primePowerCount111_up111 u : ℝ) ^ 2 ≤ C * M := by
  have hR := LeanLab.Romanov.R₁_pos
  refine ⟨4 * (9 + 2 * LeanLab.Romanov.R₁), by positivity, ?_⟩
  intro M
  simp_rw [primePowerCount_eq_romanov111_up111]
  calc
    _ ≤ ∑ u ∈ range (M + 1), (LeanLab.Romanov.repCount u : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ M))
        (fun i hi hnot => sq_nonneg _)
    _ ≤ _ := LeanLab.Romanov.romanov_second_moment M

/-- LEAF. P0093 page 162, substitution of equation 7.5 into equation 7.4.
Finite summation by parts compares a weighted sequence with its prefix bound. -/
theorem geometric_partial_bound111_up111 (a : ℕ → ℝ) (C r : ℝ)
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
theorem geometric_tsum_bound111_up111 (a : ℕ → ℝ) (C r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C) (ha : ∀ n, 0 ≤ a n)
    (hprefix : ∀ n, ∑ i ∈ range n, a i ≤ C * n) :
    (∑' i, a i * r ^ i) ≤ C / (1 - r) := by
  apply Real.tsum_le_of_sum_range_le (fun n => mul_nonneg (ha n) (pow_nonneg hr n))
  intro n
  calc
    _ ≤ ∑ i ∈ range n, C * r ^ i := geometric_partial_bound111_up111 a C r hr hr1.le hprefix n
    _ ≤ ∑' i : ℕ, C * r ^ i :=
      ((summable_geometric_of_lt_one hr hr1).mul_left C).sum_le_tsum _
        (fun i _ => mul_nonneg hC (pow_nonneg hr i))
    _ = C / (1 - r) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1]; ring

/-- LEAF. P0093 page 162, substitution of equation 7.5 into equation 7.4.
The exponential geometric denominator is at most a constant times N. -/
theorem exponential_denominator111_up111 (N : ℝ) (hN : 1 ≤ N) :
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
theorem laplace_bound111_up111 (a : ℕ → ℝ) (C : ℝ) (N : ℕ)
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
      geometric_tsum_bound111_up111 a C _ hr hr1 hC ha hprefix
    _ = C * (1 / (1 - Real.exp (-2 / (N : ℝ)))) := by ring
    _ ≤ C * (2 * N) := mul_le_mul_of_nonneg_left (exponential_denominator111_up111 N hNr) hC
    _ = 2 * C * N := by ring

/-- P0093 page 154. Absolute convergence of exponential damping over all natural numbers. -/
theorem damping_summable111_up111 (N : ℕ) (hN : 1 ≤ N) : Summable (fun n : ℕ => Real.exp (-(n : ℝ) / N)) := by
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
theorem prime_fourier_summable111_up111 (N : ℕ) (hN : 1 ≤ N) (α : ℝ)
    :
    Summable (fun p : Nat.Primes =>
      (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)) := by
  have hg := damping_summable111_up111 N hN
  apply Summable.of_norm
  have hp : Summable (fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N)) :=
    hg.comp_injective Nat.Primes.coe_nat_injective
  simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hp

/-- P0093 pages 154 and 161. Absolute convergence of the damped powers of two series. -/
theorem power_fourier_summable111_up111 (N : ℕ) (hN : 1 ≤ N) (α : ℝ)
    :
    Summable (fun m : ℕ =>
      (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)) := by
  have hg := damping_summable111_up111 N hN
  apply Summable.of_norm
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
  have hp := hg.comp_injective hi
  convert hp using 1
  ext m
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Function.comp_apply]

/-- P0093 page 154. The damped prime Fourier series defines a continuous function. -/
theorem continuous_prime_fourier111_up111 (N : ℕ) (hN : 1 ≤ N) : Continuous (primeFourier111_up111 N) := by
  unfold primeFourier111_up111
  apply continuous_tsum
    (u := fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N))
  · intro p
    fun_prop
  · exact (damping_summable111_up111 N hN).comp_injective Nat.Primes.coe_nat_injective
  · intro p α
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), le_refl]

/-- P0093 pages 154 and 161. The damped powers of two series is continuous. -/
theorem continuous_power_fourier111_up111 (N : ℕ) (hN : 1 ≤ N) : Continuous (powerFourier111_up111 N) := by
  unfold powerFourier111_up111
  apply continuous_tsum
    (u := fun m : ℕ => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N))
  · intro m
    fun_prop
  · have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
      (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
    exact (damping_summable111_up111 N hN).comp_injective hi
  · intro m α
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), le_refl]

/-- P0093 page 162 equation 7.4. Abstract Parseval for the continuous product of the two series. -/
theorem fourier_parseval111_up111 (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖primeFourier111_up111 N α * powerFourier111_up111 N α‖ ^ 2) =
      ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun α => primeFourier111_up111 N α * powerFourier111_up111 N α) i‖ ^ 2 := by
  have hf := (continuous_prime_fourier111_up111 N hN).mul (continuous_power_fourier111_up111 N hN)
  have hs : IntervalIntegrable (fun α => ‖primeFourier111_up111 N α * powerFourier111_up111 N α‖ ^ 2)
      MeasureTheory.volume 0 1 := (hf.norm.pow 2).intervalIntegrable 0 1
  have hL2 : MeasureTheory.MemLp (fun α => primeFourier111_up111 N α * powerFourier111_up111 N α) 2
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hs.1
  simpa using (tsum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hL2).symm

/-- P0093 page 162 equation 7.4. Reindex a square norm sum supported on nonpositive frequencies. -/
theorem negative_modes_sum111_up111 (a : ℕ → ℂ) (f : ℤ → ℂ)
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

end

/-! Ported from Decomp280b. -/
section


/-- P0093 page 165 Section 8. Major arcs with Q equal to N to the one tenth
and tau equal to N to the one seventh, clipped to the unit interval. -/
noncomputable def majorArcs280_up111 (N : ℕ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 1 ∧ ∃ r : ℚ, (r.den : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
    |α - r| ≤ 1 / ((r.den : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))}

/-- P0093 pages 162 and 167. Exceptional minor points where T is large. -/
noncomputable def exceptionalArcs280_up111 (N : ℕ) (η : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 1 ∧ α ∉ majorArcs280_up111 N ∧
    (1 - η) * ‖powerFourier111_up111 N 0‖ < ‖powerFourier111_up111 N α‖}

/-- P0093 page 167 before equation 10.1. The remaining minor points. -/
noncomputable def goodMinorArcs280_up111 (N : ℕ) (η : ℝ) : Set ℝ :=
  Set.Icc 0 1 \ (majorArcs280_up111 N ∪ exceptionalArcs280_up111 N η)

/-- P0093 pages 154 and 167 equations 2.2 and 10.2. Real contribution of a
measurable arc set, including the factor e from exponential damping. -/
noncomputable def arcContribution280_up111 (k N : ℕ) (s : Set ℝ) : ℝ :=
  Real.exp 1 * (∫ α in s, primeFourier111_up111 N α ^ 2 * powerFourier111_up111 N α ^ k *
    Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)).re

end

/-! Ported from Decomp357i. -/
section
open Finset

/-- P0093 page 161 equation 7.1. Split at the integer base two logarithm.
The initial terms are at most one and the dyadic tail has sum at most two. -/
theorem power_abs_le_log357_up111 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    ‖powerFourier111_up111 N α‖ ≤ Real.log N / Real.log 2 + 2 := by
  let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let L := Nat.log 2 N
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
  have ha : Summable a := (damping_summable111_up111 N hN).comp_injective hi
  have hL : (L : ℝ) ≤ Real.log N / Real.log 2 := by
    have hpow : (2 : ℝ) ^ L ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) L) hpow
    rw [Real.log_pow] at hlog
    exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog
  have hNpow : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N).le
  have htail (j : ℕ) : a (j + L) ≤ (1 / 2 : ℝ) ^ j := by
    have hratio : (2 : ℝ) ^ j ≤ ((2 ^ (j + L + 1) : ℕ) : ℝ) / N := by
      apply (le_div_iff₀ hpos).mpr
      push_cast
      rw [show j + L + 1 = j + (L + 1) by omega, pow_add]
      exact mul_le_mul_of_nonneg_left hNpow (by positivity)
    calc
      _ ≤ Real.exp (-((2 : ℝ) ^ j)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div]
        exact neg_le_neg hratio
      _ = 1 / Real.exp ((2 : ℝ) ^ j) := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / (2 : ℝ) ^ j := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith [Real.add_one_le_exp ((2 : ℝ) ^ j)]
      _ = _ := (one_div_pow _ _).symm
  have htailSum : (∑' j : ℕ, a (j + L)) ≤ 2 := by
    have hg : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    calc
      _ ≤ ∑' j : ℕ, (1 / 2 : ℝ) ^ j :=
        Summable.tsum_le_tsum htail (ha.comp_injective (add_left_injective L)) hg
      _ = 2 := by rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)]; norm_num
  have hhead : ∑ j ∈ range L, a j ≤ L := by
    calc
      _ ≤ ∑ _j ∈ range L, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Real.exp_le_one_iff.mpr
        rw [neg_div]
        exact neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) hpos.le)
      _ = _ := by simp
  have hnorm : ‖powerFourier111_up111 N α‖ ≤ ∑' j : ℕ, a j := by
    have ht := norm_tsum_le_tsum_norm (power_fourier_summable111_up111 N hN α).norm
    simpa only [powerFourier111_up111, norm_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using ht
  calc
    _ ≤ ∑' j : ℕ, a j := hnorm
    _ = ∑ j ∈ range L, a j + ∑' j : ℕ, a (j + L) := (ha.sum_add_tsum_nat_add L).symm
    _ ≤ L + 2 := add_le_add hhead htailSum
    _ ≤ _ := by linarith

end

/-! Ported from Decomp357c. -/
section
open MeasureTheory Filter
open scoped Topology

/-- P0093 pages 165 and 166. The rational major arcs form a measurable set. -/
theorem measurable_major357_up111 (N : ℕ) : MeasurableSet (majorArcs280_up111 N) := by
  unfold majorArcs280_up111
  simp only [Set.setOf_and, Set.setOf_exists]
  apply measurableSet_Icc.inter
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.inter
  · exact MeasurableSet.const _
  · exact isClosed_le (by fun_prop) continuous_const |>.measurableSet

/-- P0093 page 167 before equation 10.1. The actual large T minor set is measurable. -/
theorem measurable_exceptional357_up111 (N : ℕ) (hN : 1 ≤ N) (η : ℝ) :
    MeasurableSet (exceptionalArcs280_up111 N η) := by
  unfold exceptionalArcs280_up111
  simp only [Set.setOf_and]
  exact measurableSet_Icc.inter ((measurable_major357_up111 N).compl.inter
    (isOpen_lt continuous_const (continuous_power_fourier111_up111 N hN).norm).measurableSet)

end

/-! Ported from Decomp357d. -/
section
open MeasureTheory

/-- P0093 page 167 partition before equation 10.1. Integrating a continuous
function over the unit interval gives the sum of its three arc integrals. -/
theorem integral_circle_partition357_up111 (N : ℕ) (hN : 1 ≤ N) (η : ℝ)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ α in Set.Icc (0 : ℝ) 1, f α) =
      (∫ α in majorArcs280_up111 N, f α) +
      (∫ α in exceptionalArcs280_up111 N η, f α) +
      (∫ α in goodMinorArcs280_up111 N η, f α) := by
  have hM := measurable_major357_up111 N
  have hE := measurable_exceptional357_up111 N hN η
  have hR : MeasurableSet (goodMinorArcs280_up111 N η) :=
    measurableSet_Icc.diff (hM.union hE)
  have hsM : majorArcs280_up111 N ⊆ Set.Icc 0 1 := fun _ h => h.1
  have hsE : exceptionalArcs280_up111 N η ⊆ Set.Icc 0 1 := fun _ h => h.1
  have hsR : goodMinorArcs280_up111 N η ⊆ Set.Icc 0 1 := Set.diff_subset
  have hi : IntegrableOn f (Set.Icc (0 : ℝ) 1) := hf.integrableOn_Icc
  have hd : Disjoint (majorArcs280_up111 N) (exceptionalArcs280_up111 N η) := by
    rw [Set.disjoint_left]
    intro α hM hE
    exact hE.2.1 hM
  have hd' : Disjoint (majorArcs280_up111 N ∪ exceptionalArcs280_up111 N η)
      (goodMinorArcs280_up111 N η) := Set.disjoint_sdiff_right
  have hu : majorArcs280_up111 N ∪ exceptionalArcs280_up111 N η ∪ goodMinorArcs280_up111 N η =
      Set.Icc 0 1 := by
    change _ ∪ (Set.Icc 0 1 \ _) = _
    exact Set.union_diff_cancel (Set.union_subset hsM hsE)
  rw [← hu, setIntegral_union hd' hR
    (hi.mono_set (Set.union_subset hsM hsE)) (hi.mono_set hsR),
    setIntegral_union hd hE (hi.mono_set hsM) (hi.mono_set hsE)]

end

/-! Ported from Decomp357e. -/
section


/-- P0093 page 162 definition of Psi before equation 7.4. Its finite fiber
is contained in the full square of the bounded prime and exponent indices. -/
theorem prime_power_count_le_square357_up111 (u : ℕ) : primePowerCount111_up111 u ≤ (u + 1) ^ 2 := by
  classical
  unfold primePowerCount111_up111
  calc
    _ ≤ (Finset.univ : Finset (Fin (u + 1) × Fin (u + 1))).card := Finset.card_filter_le _ _
    _ = _ := by simp [pow_two]

/-- P0093 page 154 damping and page 162 equation 7.4. A quadratic number
of possible pairs is summable after geometric damping. -/
theorem square_damping_summable357_up111 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun u : ℕ => ((u : ℝ) + 1) ^ 2 * Real.exp (-(u : ℝ) / N)) := by
  let r := Real.exp (-1 / (N : ℝ))
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.mpr
    have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact div_neg_of_neg_of_pos (by norm_num) hpos
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_norm_lt_one hr
  have hs := (h2.add (h1.mul_left 2)).add h0
  apply hs.congr
  intro u
  have hexp : r ^ u = Real.exp (-(u : ℝ) / N) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  simp only [pow_one]
  ring

/-- P0093 page 162 equation 7.4. Exact grouped_summable280 statement.
The crude finite square bound suffices. Romanov is not needed for convergence. -/
theorem grouped_summable_proved357_up111 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun u : ℕ =>
      ((primePowerCount111_up111 u : ℝ) * Real.exp (-(u : ℝ) / N) : ℂ)) := by
  apply Summable.of_norm_bounded (square_damping_summable357_up111 N hN)
  intro u
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (primePowerCount111_up111 u)), abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact_mod_cast prime_power_count_le_square357_up111 u

end

/-! Ported from Decomp357f. -/
section


/-- P0093 page 162 definition of Psi. The unbounded prime and shifted
exponent fiber is equivalent to the bounded pair set used by the finite count. -/
noncomputable def prime_power_fiber_equiv357_up111 (u : ℕ) :
    {t : Nat.Primes × ℕ // (t.1 : ℕ) + 2 ^ (t.2 + 1) = u} ≃
      {t : Fin (u + 1) × Fin (u + 1) //
        t.1.val.Prime ∧ 1 ≤ t.2.val ∧ u = t.1.val + 2 ^ t.2.val} where
  toFun t := by
    have hp_le : (t.val.1 : ℕ) ≤ u := (Nat.le_add_right _ _).trans_eq t.property
    have hp : (t.val.1 : ℕ) < u + 1 := Nat.lt_succ_of_le hp_le
    have hm_le : 2 ^ (t.val.2 + 1) ≤ u := (Nat.le_add_left _ _).trans_eq t.property
    have hm : t.val.2 + 1 < u + 1 :=
      (Nat.lt_two_pow_self.trans_le hm_le).trans (Nat.lt_succ_self u)
    exact ⟨(⟨t.val.1, hp⟩, ⟨t.val.2 + 1, hm⟩),
      t.val.1.property, Nat.succ_le_succ (Nat.zero_le _), t.property.symm⟩
  invFun t := ⟨(⟨t.val.1.val, t.property.1⟩, t.val.2.val - 1), by
    have he : t.val.2.val - 1 + 1 = t.val.2.val := by have := t.property.2.1; omega
    simpa only [he] using t.property.2.2.symm⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · apply Nat.Primes.coe_nat_injective
      rfl
    · simp
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      dsimp
      have := t.property.2.1
      omega

/-- P0093 page 162 equation 7.4. Summing a constant over a prime and power
fiber multiplies it by the exact finite representation count. -/
theorem prime_power_fiber_sum357_up111 (u : ℕ) (z : ℂ) :
    (∑' t : {t : Nat.Primes × ℕ // (t.1 : ℕ) + 2 ^ (t.2 + 1) = u}, z) =
      (primePowerCount111_up111 u : ℂ) * z := by
  classical
  rw [(prime_power_fiber_equiv357_up111 u).tsum_eq (fun _ => z)]
  rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul]
  congr 1
  unfold primePowerCount111_up111
  norm_cast
  exact Fintype.card_subtype _

/-- P0093 page 154 damping and page 162 equation 7.4. The product term
for one prime and one positive power depends only on their natural sum. -/
theorem prime_power_term357_up111 (N : ℕ) (α : ℝ) (p : Nat.Primes) (m : ℕ) :
    ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)) *
    ((Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)) =
    (Real.exp (-(((p : ℕ) + 2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * ((p : ℕ) + 2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I) := by
  have hd : -(((p : ℕ) + 2 ^ (m + 1) : ℕ) : ℝ) / N =
      -((p : ℕ) : ℝ) / N + -((2 ^ (m + 1) : ℕ) : ℝ) / N := by push_cast; ring
  have he : ((-(2 * Real.pi * α * ((p : ℕ) + 2 ^ (m + 1) : ℕ)) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) : ℂ) * Complex.I +
      ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hd, he, Real.exp_add, Complex.ofReal_mul, Complex.exp_add]
  ring

/-- P0093 page 162 equation 7.4. Exact product_grouped280 statement,
proved by absolute convergence and the finite fiber equivalence. -/
theorem product_grouped_proved357_up111 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    primeFourier111_up111 N α * powerFourier111_up111 N α =
      ∑' u : ℕ, (((primePowerCount111_up111 u : ℝ) * Real.exp (-(u : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) := by
  let f : Nat.Primes → ℂ := fun p =>
    (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)
  let g : ℕ → ℂ := fun m =>
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)
  let v : Nat.Primes × ℕ → ℕ := fun t => (t.1 : ℕ) + 2 ^ (t.2 + 1)
  let w : ℕ → ℂ := fun u => (Real.exp (-(u : ℝ) / N) : ℂ) *
    Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)
  have hf : Summable (fun p => ‖f p‖) := (prime_fourier_summable111_up111 N hN α).norm
  have hg : Summable (fun m => ‖g m‖) := (power_fourier_summable111_up111 N hN α).norm
  have hp : (∑' p, f p) * (∑' m, g m) = ∑' t : Nat.Primes × ℕ, f t.1 * g t.2 :=
    tsum_mul_tsum_of_summable_norm hf hg
  have hs := summable_mul_of_summable_norm hf hg
  have hv := hs.hasSum.tsum_fiberwise v
  change (∑' p, f p) * (∑' m, g m) = _
  rw [hp, ← hv.tsum_eq]
  apply tsum_congr
  intro u
  have ht : (∑' t : {t : Nat.Primes × ℕ // v t = u}, f t.val.1 * g t.val.2) =
      ∑' t : {t : Nat.Primes × ℕ // v t = u}, w u := by
    apply tsum_congr
    intro t
    change _ = w u
    rw [show f t.val.1 * g t.val.2 = w (v t.val) from
      prime_power_term357_up111 N α t.val.1 t.val.2, t.property]
  change (∑' t : {t : Nat.Primes × ℕ // v t = u}, f t.val.1 * g t.val.2) = _
  rw [ht]
  change (∑' t : {t : Nat.Primes × ℕ // (t.1 : ℕ) + 2 ^ (t.2 + 1) = u}, w u) = _
  rw [prime_power_fiber_sum357_up111]
  dsimp [w]
  push_cast
  ring

end

/-! Ported from Decomp357g. -/
section
open MeasureTheory

/-- P0093 page 162 equation 7.4. The Fourier coefficient functional is
integration against the negative integer phase on the unit interval. -/
theorem coefficient_integral357_up111 (f : ℝ → ℂ) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f i =
      ∫ α in (0 : ℝ)..1, LeanLab.Perelli1996.Kernel.e (-(i : ℝ) * α) * f α := by
  rw [fourierCoeffOn_eq_integral]
  norm_num only [sub_zero, one_div_one, one_smul]
  apply intervalIntegral.integral_congr
  intro α hα
  dsimp only
  rw [smul_eq_mul]
  congr 1
  rw [fourier_coe_apply]
  unfold LeanLab.Perelli1996.Kernel.e
  push_cast
  ring

/-- P0093 page 162 equation 7.4. Integer phase orthogonality for one
negative natural frequency, reusing the proved lab phase integral. -/
theorem negative_phase_coefficient357_up111 (u : ℕ) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) i =
      if i = -(u : ℤ) then 1 else 0 := by
  rw [coefficient_integral357_up111]
  have hp (α : ℝ) : LeanLab.Perelli1996.Kernel.e (-(i : ℝ) * α) *
      Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I) =
      LeanLab.Perelli1996.Kernel.e (((-i - (u : ℤ) : ℤ) : ℝ) * α) := by
    unfold LeanLab.Perelli1996.Kernel.e
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc,
    LeanLab.Perelli1996.Parseval103.integral_e_int]
  have hz : -i - (u : ℤ) = 0 ↔ i = -(u : ℤ) := by omega
  simp only [hz]

/-- P0093 page 162 equation 7.4. Absolute summability permits termwise
integration against any fixed Fourier phase. -/
theorem coefficient_tsum357_up111 (a : ℕ → ℂ) (ha : Summable a) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => ∑' u : ℕ, a u *
        Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) i =
      ∑' u : ℕ, a u * (if i = -(u : ℤ) then 1 else 0) := by
  let F : ℕ → ℝ → ℂ := fun u α =>
    LeanLab.Perelli1996.Kernel.e (-(i : ℝ) * α) *
      (a u * Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I))
  have hF (u : ℕ) : Continuous (F u) := by
    dsimp [F, LeanLab.Perelli1996.Kernel.e]
    fun_prop
  have hFnorm (u : ℕ) (α : ℝ) : ‖F u α‖ = ‖a u‖ := by
    dsimp [F, LeanLab.Perelli1996.Kernel.e]
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I]
    simp [Complex.norm_exp]
  have hI (u : ℕ) : IntegrableOn (F u) (Set.Ioc (0 : ℝ) 1) :=
    (hF u).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hnormI (u : ℕ) : (∫ α in Set.Ioc (0 : ℝ) 1, ‖F u α‖) = ‖a u‖ := by
    simp only [hFnorm]
    simp
  have hswap := integral_tsum_of_summable_integral_norm hI
    (ha.norm.congr (fun u => (hnormI u).symm))
  rw [coefficient_integral357_up111, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hs (α : ℝ) : LeanLab.Perelli1996.Kernel.e (-(i : ℝ) * α) *
      (∑' u : ℕ, a u * Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) =
      ∑' u : ℕ, F u α := tsum_mul_left.symm
  simp_rw [hs]
  rw [← hswap]
  apply tsum_congr
  intro u
  have heq : (∫ α in Set.Ioc (0 : ℝ) 1, F u α) =
      a u * fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun α => Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) i := by
    rw [coefficient_integral357_up111, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro α hα
    dsimp [F]
    ring
  rw [heq, negative_phase_coefficient357_up111]

/-- P0093 page 162 equation 7.4. Exact negative_series_coefficient280
statement, with no prime or representation count assumption. -/
theorem negative_series_coefficient_proved357_up111 (a : ℕ → ℂ) (ha : Summable a) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => ∑' u : ℕ, a u *
        Complex.exp ((-(2 * Real.pi * α * u) : ℝ) * Complex.I)) i =
      if i ≤ 0 then a i.natAbs else 0 := by
  rw [coefficient_tsum357_up111 a ha i]
  by_cases hi : i ≤ 0
  · rw [if_pos hi]
    have habs : i = -(i.natAbs : ℤ) := by omega
    rw [tsum_eq_single i.natAbs]
    · rw [if_pos habs, mul_one]
    · intro u hu
      have hne : i ≠ -(u : ℤ) := by
        intro heq
        apply hu
        have := congrArg Int.natAbs heq
        simpa using this.symm
      simp [hne]
  · rw [if_neg hi]
    have hne (u : ℕ) : i ≠ -(u : ℤ) := by omega
    simp only [hne, ite_false, mul_zero, tsum_zero]

/-- P0093 page 162 equation 7.4. Exact fourier_coefficient111 statement,
now using only the three clean convergence, grouping and integration proofs. -/
theorem fourier_coefficient_proved357_up111 (N : ℕ) (hN : 1 ≤ N) (i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => primeFourier111_up111 N α * powerFourier111_up111 N α) i =
        if i ≤ 0 then
          ((primePowerCount111_up111 i.natAbs : ℝ) * Real.exp (-(i.natAbs : ℝ) / N) : ℂ)
        else 0 := by
  simp_rw [product_grouped_proved357_up111 N hN]
  exact negative_series_coefficient_proved357_up111 _ (grouped_summable_proved357_up111 N hN) i

end

/-! Ported from Decomp357h. -/
section


/-- P0093 page 162 equation 7.4. Parseval with the proved finite coefficient identity. -/
theorem parseval_second_moment_proved357_up111 (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖primeFourier111_up111 N α * powerFourier111_up111 N α‖ ^ 2) =
      ∑' u : ℕ, (primePowerCount111_up111 u : ℝ) ^ 2 * Real.exp (-2 * u / N) := by
  calc
    _ = ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
          (fun α => primeFourier111_up111 N α * powerFourier111_up111 N α) i‖ ^ 2 :=
      fourier_parseval111_up111 N hN
    _ = ∑' u : ℕ,
          ‖((primePowerCount111_up111 u : ℝ) * Real.exp (-(u : ℝ) / N) : ℂ)‖ ^ 2 :=
      negative_modes_sum111_up111 _ _ (fourier_coefficient_proved357_up111 N hN)
    _ = _ := by
      apply tsum_congr
      intro u
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
      rw [← Real.exp_nat_mul]
      congr 2
      ring

/-- P0093 page 162 Lemma 3. The proved Romanov moment and clean Parseval give the bound. -/
theorem lemma_three_proved357_up111 : LemmaThree111_up111 := by
  obtain ⟨C, hC, hprefix⟩ := romanov_second_moment111_up111
  refine ⟨3 * C, by positivity, ?_⟩
  intro N hN
  rw [parseval_second_moment_proved357_up111 N hN]
  have h := laplace_bound111_up111 (fun u => (primePowerCount111_up111 u : ℝ) ^ 2)
    C N hN hC.le (fun u => sq_nonneg _) hprefix
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  nlinarith

end

/-! Ported from Decomp357j. -/
section
open MeasureTheory

/-- P0093 page 167 equation 10.1. Factor k minus two powers of T from
the arc norm and compare its remaining square integral with the full circle. -/
theorem arc_abs_le_mixed_mass357_up111 (k N : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (s : Set ℝ) (hs : s ⊆ Set.Icc 0 1) (hms : MeasurableSet s)
    (B : ℝ) (hB : 0 ≤ B) (hT : ∀ α ∈ s, ‖powerFourier111_up111 N α‖ ≤ B) :
    |arcContribution280_up111 k N s| ≤ Real.exp 1 * B ^ (k - 2) *
      (∫ α in Set.Icc (0 : ℝ) 1, ‖primeFourier111_up111 N α * powerFourier111_up111 N α‖ ^ 2) := by
  have hS := continuous_prime_fourier111_up111 N hN
  have hP := continuous_power_fourier111_up111 N hN
  have hF : Continuous (fun α : ℝ => primeFourier111_up111 N α ^ 2 *
      powerFourier111_up111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) := by fun_prop
  have hInt : IntegrableOn (fun α : ℝ => primeFourier111_up111 N α ^ 2 *
      powerFourier111_up111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) s :=
    hF.integrableOn_Icc.mono_set hs
  have hMix : IntegrableOn (fun α : ℝ => ‖primeFourier111_up111 N α * powerFourier111_up111 N α‖ ^ 2)
      (Set.Icc (0 : ℝ) 1) := ((hS.mul hP).norm.pow 2).integrableOn_Icc
  unfold arcContribution280_up111
  rw [abs_mul, abs_of_pos (Real.exp_pos 1)]
  calc
    _ ≤ Real.exp 1 * ‖∫ α in s, primeFourier111_up111 N α ^ 2 *
        powerFourier111_up111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * (∫ α in s, ‖primeFourier111_up111 N α ^ 2 *
        powerFourier111_up111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * (∫ α in s, B ^ (k - 2) *
        ‖primeFourier111_up111 N α * powerFourier111_up111 N α‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      apply setIntegral_mono_on hInt.norm ((hMix.mono_set hs).const_mul _) hms
      intro α hα
      simp only [norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]
      have hp : ‖powerFourier111_up111 N α‖ ^ k =
          ‖powerFourier111_up111 N α‖ ^ 2 * ‖powerFourier111_up111 N α‖ ^ (k - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp, mul_pow]
      calc
        _ ≤ ‖primeFourier111_up111 N α‖ ^ 2 *
            (‖powerFourier111_up111 N α‖ ^ 2 * B ^ (k - 2)) := by gcongr; exact hT α hα
        _ = _ := by ring
    _ = Real.exp 1 * B ^ (k - 2) * (∫ α in s,
        ‖primeFourier111_up111 N α * powerFourier111_up111 N α‖ ^ 2) := by rw [integral_const_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hMix (ae_of_all _ (fun α => sq_nonneg _)) (ae_of_all _ hs)) (by positivity)

/-- P0093 page 167 equation 10.1. A fixed power of a bounded additive
logarithmic error costs at most two once the logarithm is sufficiently large. -/
theorem additive_power_le_twice357_up111 (r : ℕ) (t : ℝ) (ht : 0 < t)
    (hlarge : 2 * (r : ℝ) ≤ t * Real.log 2) : (t + 2) ^ r ≤ 2 * t ^ r := by
  have hbase : 1 + 2 / t ≤ Real.exp (2 / t) := by
    simpa only [add_comm] using Real.add_one_le_exp (2 / t)
  have he : (1 + 2 / t) ^ r ≤ Real.exp ((r : ℝ) * (2 / t)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + 2 / t) hbase r
  have hcut : (r : ℝ) * (2 / t) ≤ Real.log 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ ht).mpr
    nlinarith
  have htwo : (1 + 2 / t) ^ r ≤ 2 := by
    have h := he.trans (Real.exp_le_exp.mpr hcut)
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hid : (t + 2) ^ r = t ^ r * (1 + 2 / t) ^ r := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hid, mul_comm 2]
  exact mul_le_mul_of_nonneg_left htwo (by positivity)

/-- P0093 page 167 equation 10.1. Exact minor_error280 statement.
The pointwise complementary bound, clean Lemma 3 and dyadic growth suffice. -/
theorem minor_error_proved357_up111 (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hT : ∀ N : ℕ, ∀ α : ℝ, α ∈ goodMinorArcs280_up111 N η →
      ‖powerFourier111_up111 N α‖ ≤ (1 - η) * ‖powerFourier111_up111 N 0‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 < N →
        |arcContribution280_up111 k N (goodMinorArcs280_up111 N η)| ≤
          C * scale111_up111 k N * (1 - η) ^ (k - 2) := by
  obtain ⟨C0, hC0, hL3⟩ := lemma_three_proved357_up111
  refine ⟨2 * Real.exp 1 * C0, by positivity, ?_⟩
  intro k hk
  let r := k - 2
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.exp (2 * (r : ℝ) + Real.log 2))
  refine ⟨max 2 M, ?_⟩
  intro N hev hN
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hMN : M < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hnR : (M : ℝ) < (N : ℝ) := by exact_mod_cast hMN
  have hlog : 2 * (r : ℝ) + Real.log 2 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos _) (hM.trans hnR).le
    simpa only [Real.log_exp] using h
  let t := Real.log N / Real.log 2
  have ht : 0 < t := div_pos (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
    (Real.log_pos (by norm_num))
  have hlarge : 2 * (r : ℝ) ≤ t * Real.log 2 := by
    dsimp [t]
    rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hp := additive_power_le_twice357_up111 r t ht hlarge
  have hms : MeasurableSet (goodMinorArcs280_up111 N η) :=
    measurableSet_Icc.diff ((measurable_major357_up111 N).union (measurable_exceptional357_up111 N (by omega) η))
  have hb := arc_abs_le_mixed_mass357_up111 k N (by omega) (by omega)
    (goodMinorArcs280_up111 N η) Set.diff_subset hms
    ((1 - η) * (t + 2)) (by positivity) (fun α hα =>
      (hT N α hα).trans (mul_le_mul_of_nonneg_left (power_abs_le_log357_up111 N (by omega) 0) (by linarith)))
  have hm : (∫ α in Set.Icc (0 : ℝ) 1, ‖primeFourier111_up111 N α * powerFourier111_up111 N α‖ ^ 2) ≤ C0 * N := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hL3 N (by omega)).le
  calc
    _ ≤ Real.exp 1 * ((1 - η) * (t + 2)) ^ r * (C0 * N) :=
      hb.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ ≤ Real.exp 1 * ((1 - η) ^ r * (2 * t ^ r)) * (C0 * N) := by
      rw [mul_pow]
      gcongr
    _ = _ := by unfold scale111_up111; dsimp [t, r]; ring

end

/-! Ported from SPLIT_count_circle_coefficient357. -/
section
open MeasureTheory

/-- LEAF. Step 1 of the proof, the orthogonal integral: the integral over the
unit interval of a complex exponential of an integral frequency is one at
frequency zero and zero at every other integral frequency. -/
theorem integral_exp_two_pi_mul_int357_up111 (m : ℤ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      Complex.exp (((2 * Real.pi * α * (m : ℝ)) : ℝ) * Complex.I)) =
      if m = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  by_cases hm : m = 0
  · subst m
    simp
  · simp only [hm, ↓reduceIte]
    let c : ℂ := 2 * Real.pi * (m : ℂ) * Complex.I
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        (Int.cast_ne_zero.mpr hm)) Complex.I_ne_zero
    have heq : (fun α : ℝ => Complex.exp (((2 * Real.pi * α * (m : ℝ)) : ℝ) * Complex.I)) =
        fun α : ℝ => Complex.exp (c * (α : ℂ)) := by
      funext α
      congr 1
      dsimp [c]
      push_cast
      ring
    rw [heq, integral_exp_mul_complex hc]
    have he : Complex.exp c = 1 := by
      have he' : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
        dsimp [c]
        convert Complex.exp_int_mul_two_pi_mul_I m using 1 <;> ring
      simpa using he'
    simp [he, hc]

private theorem tsum_fintype_pi_pow357_up111 (f : ℕ → ℂ)
    (hf : Summable (fun n => ‖f n‖)) (k : ℕ) :
    Summable (fun ν : Fin k → ℕ => ∏ i, f (ν i)) ∧
      (∑' n, f n) ^ k = ∑' ν : Fin k → ℕ, ∏ i, f (ν i) := by
  induction k with
  | zero =>
      constructor
      · exact (hasSum_fintype _).summable
      · simp [tsum_fintype]
  | succ k ih =>
      have hνnorm : Summable (fun ν : Fin k → ℕ => ‖∏ i, f (ν i)‖) := by
        simpa only [norm_prod] using ih.1.norm
      have hprod : Summable (fun z : (Fin k → ℕ) × ℕ =>
          (∏ i, f (z.1 i)) * f z.2) :=
        (hνnorm.mul_norm hf).of_norm
      let e : ((Fin k → ℕ) × ℕ) ≃ (Fin (k + 1) → ℕ) :=
        (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ))
      constructor
      · have hc := Summable.comp_injective
          (f := fun z : (Fin k → ℕ) × ℕ => (∏ i, f (z.1 i)) * f z.2)
          (i := fun x => e.symm x) hprod (fun _ _ h => e.symm.injective h)
        convert hc using 1
        ext ν
        simp [e, Fin.prod_univ_succ, Fin.tail, mul_comm]
      · rw [pow_succ, ih.2]
        calc
          (∑' ν : Fin k → ℕ, ∏ i, f (ν i)) * ∑' n, f n =
              ∑' z : (Fin k → ℕ) × ℕ, (∏ i, f (z.1 i)) * f z.2 :=
            tsum_mul_tsum_of_summable_norm hνnorm hf
          _ = ∑' ν : Fin (k + 1) → ℕ, ∏ i, f (ν i) := by
            simpa [e, Fin.prod_univ_succ, Fin.tail, mul_comm] using
              e.tsum_eq (fun ν : Fin (k + 1) → ℕ => ∏ i, f (ν i))

/-- LEAF. Step 2 of the proof, the pointwise product: at a fixed point of the
unit interval, one copy of the damped prime series squared times k copies of
the damped power-of-two series times the exponential of frequency N is the
absolutely convergent series over prime pairs and exponent tuples whose
frequencies add up. -/
theorem integrand_eq_tsum357_up111 (k N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    primeFourier111_up111 N α ^ 2 * powerFourier111_up111 N α ^ k *
        Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) =
      ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I) := by
  let P : Nat.Primes → ℂ := fun p =>
    (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)
  let Q : ℕ → ℂ := fun m =>
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)
  have hP : Summable (fun p => ‖P p‖) := by
    simpa only [P] using (prime_fourier_summable111_up111 N hN α).norm
  have hQ : Summable (fun m => ‖Q m‖) := by
    simpa only [Q] using (power_fourier_summable111_up111 N hN α).norm
  have hpow := tsum_fintype_pi_pow357_up111 Q hQ k
  have hpairnorm : Summable (fun z : Nat.Primes × Nat.Primes => ‖P z.1 * P z.2‖) :=
    hP.mul_norm hP
  have hpnorm : Summable (fun ν : Fin k → ℕ => ‖∏ i, Q (ν i)‖) := by
    simpa only [norm_prod] using hpow.1.norm
  change (∑' p, P p) ^ 2 * (∑' m, Q m) ^ k *
    Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) = _
  calc
    (∑' p, P p) ^ 2 * (∑' m, Q m) ^ k *
        Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) =
        ((∑' z : Nat.Primes × Nat.Primes, P z.1 * P z.2) *
          (∑' ν : Fin k → ℕ, ∏ i, Q (ν i))) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) := by
              rw [pow_two, tsum_mul_tsum_of_summable_norm hP hP, hpow.2]
    _ = (∑' z : (Nat.Primes × Nat.Primes) × (Fin k → ℕ),
          (P z.1.1 * P z.1.2) * ∏ i, Q (z.2 i)) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) := by
              rw [tsum_mul_tsum_of_summable_norm hpairnorm hpnorm]
    _ = ∑' z : (Nat.Primes × Nat.Primes) × (Fin k → ℕ),
          ((P z.1.1 * P z.1.2) * ∏ i, Q (z.2 i)) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) := by
              rw [tsum_mul_right]
    _ = ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
          ((P t.1 * P t.2.1) * ∏ i, Q (t.2.2 i)) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) := by
              simpa using (Equiv.prodAssoc Nat.Primes Nat.Primes (Fin k → ℕ)).tsum_eq
                (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
                  ((P t.1 * P t.2.1) * ∏ i, Q (t.2.2 i)) *
                    Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I))
    _ = _ := by
      apply tsum_congr
      intro t
      have hdamp :
          ((Real.exp (-((t.1 : ℕ) : ℝ) / N) * Real.exp (-((t.2.1 : ℕ) : ℝ) / N)) *
            ∏ i, Real.exp (-((2 ^ (t.2.2 i + 1) : ℕ) : ℝ) / N)) =
            Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
              ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) := by
        rw [← Real.exp_add, ← Real.exp_sum, ← Real.exp_add]
        congr 1
        push_cast
        simp only [neg_div, Finset.sum_neg_distrib, Finset.mul_sum]
        rw [← Finset.sum_div]
        ring
      have hphase :
          ((Complex.exp ((-(2 * Real.pi * α * (t.1 : ℕ)) : ℝ) * Complex.I) *
            Complex.exp ((-(2 * Real.pi * α * (t.2.1 : ℕ)) : ℝ) * Complex.I)) *
            ∏ i, Complex.exp ((-(2 * Real.pi * α * (2 ^ (t.2.2 i + 1) : ℕ)) : ℝ) * Complex.I)) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) =
            Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
              ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I) := by
        rw [← Complex.exp_add, ← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        simp only [neg_div, neg_mul, Finset.sum_neg_distrib, Finset.mul_sum]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
      dsimp only [P, Q]
      rw [Finset.prod_mul_distrib]
      have hdampC := congrArg (fun x : ℝ => (x : ℂ)) hdamp
      simp only [Complex.ofReal_mul, Complex.ofReal_prod] at hdampC
      calc
        _ = (((Real.exp (-((t.1 : ℕ) : ℝ) / N) : ℂ) *
                (Real.exp (-((t.2.1 : ℕ) : ℝ) / N) : ℂ) *
                ∏ i, (Real.exp (-((2 ^ (t.2.2 i + 1) : ℕ) : ℝ) / N) : ℂ)) *
              (((Complex.exp ((-(2 * Real.pi * α * (t.1 : ℕ)) : ℝ) * Complex.I) *
                  Complex.exp ((-(2 * Real.pi * α * (t.2.1 : ℕ)) : ℝ) * Complex.I)) *
                  ∏ i, Complex.exp ((-(2 * Real.pi * α * (2 ^ (t.2.2 i + 1) : ℕ)) : ℝ) * Complex.I)) *
                Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I))) := by ring
        _ = _ := by rw [hdampC, hphase]

private theorem expanded_fourier_summable357_up111 (k N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    Summable (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
      (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
        ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
      Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
        ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)) := by
  let P : Nat.Primes → ℂ := fun p =>
    (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)
  let Q : ℕ → ℂ := fun m =>
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)
  have hP : Summable (fun p => ‖P p‖) := by
    simpa only [P] using (prime_fourier_summable111_up111 N hN α).norm
  have hQ : Summable (fun m => ‖Q m‖) := by
    simpa only [Q] using (power_fourier_summable111_up111 N hN α).norm
  have hpow := tsum_fintype_pi_pow357_up111 Q hQ k
  have hpairnorm : Summable (fun z : Nat.Primes × Nat.Primes => ‖P z.1 * P z.2‖) :=
    hP.mul_norm hP
  have hpnorm : Summable (fun ν : Fin k → ℕ => ‖∏ i, Q (ν i)‖) := by
    simpa only [norm_prod] using hpow.1.norm
  have hfull : Summable (fun z : (Nat.Primes × Nat.Primes) × (Fin k → ℕ) =>
      (P z.1.1 * P z.1.2) * ∏ i, Q (z.2 i)) :=
    (hpairnorm.mul_norm hpnorm).of_norm
  have hright : Summable (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
      (P t.1 * P t.2.1) * ∏ i, Q (t.2.2 i)) := by
    have hc := Summable.comp_injective
      (f := fun z : (Nat.Primes × Nat.Primes) × (Fin k → ℕ) =>
        (P z.1.1 * P z.1.2) * ∏ i, Q (z.2 i))
      (i := fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
        (Equiv.prodAssoc Nat.Primes Nat.Primes (Fin k → ℕ)).symm t)
      hfull (fun _ _ h => (Equiv.prodAssoc Nat.Primes Nat.Primes (Fin k → ℕ)).symm.injective h)
    exact hc
  refine (hright.mul_right (Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I))).congr ?_
  intro t
  have hdamp :
      ((Real.exp (-((t.1 : ℕ) : ℝ) / N) * Real.exp (-((t.2.1 : ℕ) : ℝ) / N)) *
        ∏ i, Real.exp (-((2 ^ (t.2.2 i + 1) : ℕ) : ℝ) / N)) =
        Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) := by
    rw [← Real.exp_add, ← Real.exp_sum, ← Real.exp_add]
    congr 1
    push_cast
    simp only [neg_div, Finset.sum_neg_distrib]
    rw [← Finset.sum_div]
    ring
  have hphase :
      ((Complex.exp ((-(2 * Real.pi * α * (t.1 : ℕ)) : ℝ) * Complex.I) *
        Complex.exp ((-(2 * Real.pi * α * (t.2.1 : ℕ)) : ℝ) * Complex.I)) *
        ∏ i, Complex.exp ((-(2 * Real.pi * α * (2 ^ (t.2.2 i + 1) : ℕ)) : ℝ) * Complex.I)) *
        Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) =
        Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
          ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  dsimp only [P, Q]
  rw [Finset.prod_mul_distrib]
  have hdampC := congrArg (fun x : ℝ => (x : ℂ)) hdamp
  simp only [Complex.ofReal_mul, Complex.ofReal_prod] at hdampC
  calc
    _ = (((Real.exp (-((t.1 : ℕ) : ℝ) / N) : ℂ) *
            (Real.exp (-((t.2.1 : ℕ) : ℝ) / N) : ℂ) *
            ∏ i, (Real.exp (-((2 ^ (t.2.2 i + 1) : ℕ) : ℝ) / N) : ℂ)) *
          (((Complex.exp ((-(2 * Real.pi * α * (t.1 : ℕ)) : ℝ) * Complex.I) *
              Complex.exp ((-(2 * Real.pi * α * (t.2.1 : ℕ)) : ℝ) * Complex.I)) *
              ∏ i, Complex.exp ((-(2 * Real.pi * α * (2 ^ (t.2.2 i + 1) : ℕ)) : ℝ) * Complex.I)) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I))) := by ring
    _ = _ := by rw [hdampC, hphase]

/-- LEAF. Step 3 of the proof, the exchange of the integral with the sum: the
integral over the unit interval of the expanded series of step 2 is the sum
over the same index set of the termwise integrals, each taken by step 1, so
each term survives exactly when its frequency is N. -/
theorem integral_tsum_swap357_up111 (k N : ℕ) (hN : 1 ≤ N) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)) =
      ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * (if ((t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1)) = N then (1 : ℂ) else 0) := by
  have hnorm (t : Nat.Primes × Nat.Primes × (Fin k → ℕ)) (α : ℝ) :
      ‖(Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
        ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
        Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
          ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)‖ =
        Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) := by
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hweight : Summable (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
      Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
        ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N))) := by
    have h := (expanded_fourier_summable357_up111 k N hN 0).norm
    exact h.congr (fun t => hnorm t 0)
  have hF_int : ∀ t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
      IntegrableOn (fun α : ℝ =>
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
        Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
          ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I))
        (Set.Icc (0 : ℝ) 1) := by
    intro t
    apply Continuous.integrableOn_Icc
    fun_prop
  have hint (t : Nat.Primes × Nat.Primes × (Fin k → ℕ)) :
      (∫ α in Set.Icc (0 : ℝ) 1,
        ‖(Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
          Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
            ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)‖) =
        Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun α _ => hnorm t α)]
    simp
  have hF_sum : Summable (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
      ∫ α in Set.Icc (0 : ℝ) 1,
        ‖(Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
          Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
            ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)‖) := by
    simpa only [hint] using hweight
  rw [← integral_tsum_of_summable_integral_norm hF_int hF_sum]
  apply tsum_congr
  intro t
  rw [integral_const_mul]
  let M : ℤ := (N : ℤ) - ((t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1))
  have hfun : (fun α : ℝ =>
      Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
        ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)) =
      fun α : ℝ => Complex.exp (((2 * Real.pi * α * (M : ℝ)) : ℝ) * Complex.I) := by
    funext α
    congr 2
    dsimp [M]
    push_cast
    ring
  rw [hfun, integral_exp_two_pi_mul_int357_up111 M]
  by_cases ht : (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N
  · have ht' : (N : ℤ) = (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) := by
      exact_mod_cast ht.symm
    have hM : M = 0 := by dsimp [M]; omega
    simp [ht, hM]
  · have ht' : (N : ℤ) ≠ (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) := by
      intro hn
      apply ht
      exact_mod_cast hn.symm
    have hM : M ≠ 0 := by dsimp [M]; omega
    simp [ht, hM]

/-- LEAF. Step 4 of the proof, the count: at frequency N the damping weight of
every surviving tuple is exp of minus one, and the surviving tuples are in
bijection with the ordered representations counted by
representationCount111_up111, so the sum over them is exp of minus one times that
count. -/
theorem tsum_indicator_eq_count357_up111 (k N : ℕ) (hN : 1 ≤ N) :
    (∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * (if ((t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1)) = N then (1 : ℂ) else 0)) =
      (Real.exp (-1) : ℂ) * (representationCount111_up111 k N : ℂ) := by
  classical
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hterm (t : Nat.Primes × Nat.Primes × (Fin k → ℕ)) :
      (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
        ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
        (if (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N then (1 : ℂ) else 0) =
        if (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N then
          (Real.exp (-1) : ℂ) else 0 := by
    by_cases ht : (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N
    · have ht' : ((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast ht
      simp only [ht, if_true, mul_one]
      rw [ht', div_self hNr]
    · simp [ht]
  rw [tsum_congr hterm]
  let R : Finset (Fin (N + 1) × Fin (N + 1) × (Fin k → Fin (N + 1))) :=
    Finset.univ.filter fun t : Fin (N + 1) × Fin (N + 1) × (Fin k → Fin (N + 1)) =>
      (t.1.val).Prime ∧ (t.2.1.val).Prime ∧ (∀ i, 1 ≤ (t.2.2 i).val) ∧
        N = t.1.val + t.2.1.val + ∑ i, 2 ^ (t.2.2 i).val
  let e : {t // t ∈ R} → Nat.Primes × Nat.Primes × (Fin k → ℕ) := fun t =>
    (⟨t.1.1.val, (Finset.mem_filter.mp t.2).2.1⟩,
      (⟨t.1.2.1.val, (Finset.mem_filter.mp t.2).2.2.1⟩,
        fun i => (t.1.2.2 i).val - 1))
  let S : Finset (Nat.Primes × Nat.Primes × (Fin k → ℕ)) := Finset.univ.image e
  have he_inj : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    have hp : a.1.1 = b.1.1 := by
      apply Fin.ext
      exact congrArg (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) => (t.1 : ℕ)) hab
    have hq : a.1.2.1 = b.1.2.1 := by
      apply Fin.ext
      exact congrArg (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) => (t.2.1 : ℕ)) hab
    have hν : a.1.2.2 = b.1.2.2 := by
      funext i
      apply Fin.ext
      have ha := (Finset.mem_filter.mp a.2).2.2.2.1 i
      have hb := (Finset.mem_filter.mp b.2).2.2.2.1 i
      have he := congrArg (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) => t.2.2 i) hab
      dsimp [e] at he
      omega
    exact Prod.ext hp (Prod.ext hq hν)
  have hS (t : Nat.Primes × Nat.Primes × (Fin k → ℕ)) (ht : t ∈ S) :
      (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N := by
    rcases Finset.mem_image.mp ht with ⟨r, _, rfl⟩
    have hr := Finset.mem_filter.mp r.2
    dsimp [e]
    convert hr.2.2.2.2.symm using 1
    have hsum : (∑ i, 2 ^ ((r.1.2.2 i).val - 1 + 1)) =
        ∑ i, 2 ^ (r.1.2.2 i).val := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := hr.2.2.2.1 i
      congr 1
      omega
    exact congrArg (fun x : ℕ => (r.1.1 : ℕ) + (r.1.2.1 : ℕ) + x) hsum
  have hout (t : Nat.Primes × Nat.Primes × (Fin k → ℕ)) (ht : t ∉ S) :
      (if (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N then
        (Real.exp (-1) : ℂ) else 0) = 0 := by
    have hnc : ¬((t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N) := by
      intro htotal
      apply ht
      have hpN : (t.1 : ℕ) < N + 1 := by omega
      have hqN : (t.2.1 : ℕ) < N + 1 := by omega
      have hνN : ∀ i, t.2.2 i + 1 < N + 1 := by
        intro i
        have hle : 2 ^ (t.2.2 i + 1) ≤ ∑ j, 2 ^ (t.2.2 j + 1) :=
          Finset.single_le_sum (f := fun j : Fin k => 2 ^ (t.2.2 j + 1))
            (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        have hpow : t.2.2 i + 1 < 2 ^ (t.2.2 i + 1) := Nat.lt_two_pow_self
        omega
      let r : Fin (N + 1) × Fin (N + 1) × (Fin k → Fin (N + 1)) :=
        (⟨(t.1 : ℕ), hpN⟩, ⟨(t.2.1 : ℕ), hqN⟩, fun i => ⟨t.2.2 i + 1, hνN i⟩)
      have hr : r ∈ R := by
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨t.1.property, t.2.1.property, fun i => by dsimp [r]; omega, htotal.symm⟩
      apply Finset.mem_image.mpr
      refine ⟨⟨r, hr⟩, Finset.mem_univ _, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · funext i
          rfl
    simp [hnc]
  rw [tsum_eq_sum (s := S) hout]
  have hcard : S.card = R.card := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ he_inj, Finset.card_attach]
  have hrep : representationCount111_up111 k N = R.card := by
    rfl
  calc
    (∑ t ∈ S, if (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N then
        (Real.exp (-1) : ℂ) else 0) = ∑ _t ∈ S, (Real.exp (-1) : ℂ) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [if_pos (hS t ht)]
    _ = (S.card : ℂ) * (Real.exp (-1) : ℂ) := by simp
    _ = (Real.exp (-1) : ℂ) * (representationCount111_up111 k N : ℂ) := by
      rw [hcard, ← hrep]
      ring

/-- The circle coefficient, assembled from the four leaves of this file: integrate
the expanded product, swap the integral with the sum, evaluate every termwise
integral, and count the surviving tuples. -/
theorem count_circle_coefficient357_split_up111 (k N : ℕ) (hN : 1 ≤ N) :
    (∫ α in Set.Icc (0 : ℝ) 1, primeFourier111_up111 N α ^ 2 * powerFourier111_up111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) = (Real.exp (-1) : ℂ) * (representationCount111_up111 k N : ℂ) := by
  have hexp : (∫ α in Set.Icc (0 : ℝ) 1, primeFourier111_up111 N α ^ 2 * powerFourier111_up111 N α ^ k *
      Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) =
      ∫ α in Set.Icc (0 : ℝ) 1,
        ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
          (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro α _
    exact integrand_eq_tsum357_up111 k N hN α
  rw [hexp, integral_tsum_swap357_up111 k N hN, tsum_indicator_eq_count357_up111 k N hN]

end

/-! Ported from Circle435. -/
section
open MeasureTheory

/-- P0093 page 154 equation 2.2. Exact original coefficient type
from the newly proved full tuple identity on main. No new decomposition
of this source blocked target is introduced. -/
theorem count_circle_coefficient_proved435_up111 (k N : ℕ) (hN : 1 ≤ N) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      primeFourier111_up111 N α ^ 2 * powerFourier111_up111 N α ^ k *
        Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) =
      (Real.exp (-1) : ℂ) * (representationCount111_up111 k N : ℂ) := by
  exact count_circle_coefficient357_split_up111 k N hN

/-- P0093 page 167 partition before equation 10.1. Exact
circle_partition280 type through the freshly proved coefficient identity
and the existing measurable partition. Both components are proved. -/
theorem circle_partition_proved435_up111 (k N : ℕ) (hN : 1 ≤ N) (η : ℝ) :
    (representationCount111_up111 k N : ℝ) =
      arcContribution280_up111 k N (majorArcs280_up111 N) +
      arcContribution280_up111 k N (exceptionalArcs280_up111 N η) +
      arcContribution280_up111 k N (goodMinorArcs280_up111 N η) := by
  have hS := continuous_prime_fourier111_up111 N hN
  have hT := continuous_power_fourier111_up111 N hN
  have hf : Continuous (fun α : ℝ => primeFourier111_up111 N α ^ 2 * powerFourier111_up111 N α ^ k *
      Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) := by fun_prop
  have hp := integral_circle_partition357_up111 N hN η _ hf
  have hc := congrArg Complex.re (count_circle_coefficient_proved435_up111 k N hN)
  have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.natCast_re, zero_mul] at hc
  have hid : (representationCount111_up111 k N : ℝ) =
      Real.exp 1 * (∫ α in Set.Icc (0 : ℝ) 1, primeFourier111_up111 N α ^ 2 *
        powerFourier111_up111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)).re := by
    rw [hc, ← mul_assoc, he, one_mul]
  rw [hid, hp]
  simp only [arcContribution280_up111, Complex.add_re]
  ring

end


end LeanLab.Linnik1951
