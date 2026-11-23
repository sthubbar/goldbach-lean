module

public import LeanLab.Perelli1996.VaughanInput

/-!
P0083 Perelli 1996, page 482, divisor estimates used in equation 7.
Elementary first moments of Dirichlet convolution powers.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Divisor103
open Finset Real
open LeanLab.Perelli1996.Section2
noncomputable section

/-- The k-fold divisor function divided by its positive argument, extended by zero. -/
def weightedDivisor (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => (divisorCount k n : ℝ) / n, by simp [divisorCount]⟩

/-- Reciprocal weights preserve nonnegativity. -/
theorem weightedDivisor_nonneg (k n : ℕ) : 0 ≤ weightedDivisor k n := by
  unfold weightedDivisor
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- At degree one the weighted divisor function is the reciprocal. -/
theorem weightedDivisor_one (n : ℕ) : weightedDivisor 1 n = 1 / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [weightedDivisor, hn]
  · simp [weightedDivisor, divisorCount, ArithmeticFunction.zeta_apply_ne hn, hn]

/-- Reciprocal weighting commutes with the divisor convolution step. -/
theorem weightedDivisor_succ (k : ℕ) :
    weightedDivisor (k + 1) = weightedDivisor k * weightedDivisor 1 := by
  ext n
  change ((ArithmeticFunction.zeta ^ (k + 1)) n : ℝ) / n = _
  rw [pow_succ, ArithmeticFunction.mul_apply, Nat.cast_sum, Finset.sum_div,
    ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have he : p.2 ≠ 0 := by intro he; simp [he] at hprod; omega
  simp only [Nat.cast_mul, weightedDivisor_one]
  change ((ArithmeticFunction.zeta ^ k) p.1 : ℝ) * (ArithmeticFunction.zeta p.2 : ℝ) / n =
    (((ArithmeticFunction.zeta ^ k) p.1 : ℝ) / p.1) * (1 / (p.2 : ℝ))
  rw [ArithmeticFunction.zeta_apply_ne he, Nat.cast_one, mul_one, ← hprod, Nat.cast_mul]
  ring

/-- The harmonic sum is exactly the degree one weighted divisor partial sum. -/
theorem weightedDivisor_one_sum (N : ℕ) :
    (∑ n ∈ Ioc 0 N, weightedDivisor 1 n) = (harmonic N : ℝ) := by
  simp_rw [weightedDivisor_one, one_div]
  rw [show Ioc 0 N = Icc 1 N by ext n; simp; omega]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- The convolution truncation is bounded by the product of its nonnegative partial sums. -/
theorem convolution_sum_le (f g : ArithmeticFunction ℝ) (N : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ n ∈ Ioc 0 N, (f * g) n) ≤
      (∑ n ∈ Ioc 0 N, f n) * (∑ n ∈ Ioc 0 N, g n) := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter, Finset.sum_mul_sum]
  have heq : (∑ n ∈ Ioc 0 N, ∑ m ∈ Ioc 0 N, f n * g m) =
      ∑ p ∈ Ioc 0 N ×ˢ Ioc 0 N, f p.1 * g p.2 := by rw [Finset.sum_product]
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p hp hnot => mul_nonneg (hf _) (hg _))

/-- The weighted k-fold divisor sum is at most the k-th power of the harmonic sum. -/
theorem weightedDivisor_sum_le (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, weightedDivisor k n) ≤ (harmonic N : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    have heq : ∀ n, weightedDivisor 0 n = if n = 1 then 1 else 0 := by
      intro n
      by_cases hn : n = 1
      · simp [weightedDivisor, divisorCount, hn]
      · simp [weightedDivisor, divisorCount, ArithmeticFunction.one_apply_ne hn, hn]
    simp_rw [heq]
    simp only [Finset.sum_ite_eq', Finset.mem_Ioc]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [weightedDivisor_succ]
    calc
      _ ≤ (∑ n ∈ Ioc 0 N, weightedDivisor k n) * (∑ n ∈ Ioc 0 N, weightedDivisor 1 n) :=
        convolution_sum_le _ _ N (weightedDivisor_nonneg k) (weightedDivisor_nonneg 1)
      _ ≤ (harmonic N : ℝ) ^ k * (harmonic N : ℝ) := by
        rw [weightedDivisor_one_sum]
        exact mul_le_mul_of_nonneg_right ih (by
          rw [← weightedDivisor_one_sum N]
          exact Finset.sum_nonneg (fun n _ => weightedDivisor_nonneg 1 n))
      _ = _ := by rw [pow_succ]
/-- The first moment of the k plus one fold divisor function has a harmonic bound. -/
theorem divisor_first_moment_harmonic (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, (divisorCount (k + 1) n : ℝ)) ≤
      N * (harmonic N : ℝ) ^ k := by
  have hsum : (∑ n ∈ Ioc 0 N, (divisorCount (k + 1) n : ℝ)) =
      ∑ n ∈ Ioc 0 N, (divisorCount k n : ℝ) * ((N / n : ℕ) : ℝ) := by
    have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (ArithmeticFunction.zeta ^ k) N
    change (∑ n ∈ Ioc 0 N, ((ArithmeticFunction.zeta ^ (k + 1)) n : ℝ)) = _
    rw [pow_succ]
    exact_mod_cast h
  rw [hsum]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (divisorCount k n : ℝ) * ((N : ℝ) / n) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Nat.cast_div_le
    _ = (N : ℝ) * ∑ n ∈ Ioc 0 N, weightedDivisor k n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      change _ = N * ((divisorCount k n : ℝ) / n)
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weightedDivisor_sum_le k N) (Nat.cast_nonneg N)

/-- The first moment has the explicit logarithmic bound used in divisor estimates. -/
theorem divisor_first_moment (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, (divisorCount (k + 1) n : ℝ)) ≤
      N * (1 + Real.log N) ^ k := by
  have hhar : 0 ≤ (harmonic N : ℝ) := by
    rw [← weightedDivisor_one_sum]
    exact Finset.sum_nonneg (fun n _ => weightedDivisor_nonneg 1 n)
  exact (divisor_first_moment_harmonic k N).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hhar (harmonic_le_one_add_log N) k) (Nat.cast_nonneg N))

/-- At a prime power, the k-fold divisor count is a multichoose coefficient. -/
theorem divisorCount_prime_pow (k p e : ℕ) (hp : p.Prime) :
    divisorCount k (p ^ e) = k.multichoose e := by
  induction k generalizing e with
  | zero =>
    cases e with
    | zero => simp [divisorCount]
    | succ e =>
      have hne : p ^ (e + 1) ≠ 1 := by
        have : 1 < p ^ (e + 1) := Nat.one_lt_pow (by omega) hp.one_lt
        omega
      simp [divisorCount, ArithmeticFunction.one_apply_ne hne]
  | succ k ih =>
    change (ArithmeticFunction.zeta ^ (k + 1)) (p ^ e) = _
    rw [pow_succ, ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    simp_rw [show ∀ j, (ArithmeticFunction.zeta ^ k) (p ^ j) = k.multichoose j by
      intro j; exact ih j]
    rw [Nat.sum_range_multichoose, Nat.multichoose_eq]
    have heq : k + 1 + e - 1 = k + e := by omega
    rw [heq]
    simpa [Nat.add_comm] using (Nat.choose_symm_add (a := k) (b := e))

/-- The ratio recurrence for multichoose coefficients, without division. -/
theorem multichoose_step (k e : ℕ) :
    (e + 1) * k.multichoose (e + 1) = (k + e) * k.multichoose e := by
  cases k with
  | zero => cases e <;> simp
  | succ k =>
    simp only [Nat.multichoose_eq]
    have h0 : k + 1 + (e + 1) - 1 = (k + e) + 1 := by omega
    have h1 : k + 1 + e - 1 = k + e := by omega
    rw [h0, h1]
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.add_one_mul_choose_eq (k + e) e).symm

/-- Squaring the divisor coefficient is dominated by replacing k with k squared. -/
theorem multichoose_sq_le (k e : ℕ) : (k.multichoose e) ^ 2 ≤ (k ^ 2).multichoose e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 := multichoose_step k e
    have h2 := multichoose_step (k ^ 2) e
    have hratio : (k + e) ^ 2 ≤ (e + 1) * (k ^ 2 + e) := by
      have hs : (0 : ℤ) ≤ (e : ℤ) * ((k : ℤ) - 1) ^ 2 := by positivity
      exact_mod_cast (show ((k : ℤ) + e) ^ 2 ≤ ((e : ℤ) + 1) * ((k : ℤ) ^ 2 + e) by nlinarith)
    have hmul := Nat.mul_le_mul_left ((k + e) ^ 2) ih
    have hratio' := Nat.mul_le_mul_right ((k ^ 2).multichoose e) hratio
    have hsquare : (e + 1) ^ 2 * (k.multichoose (e + 1)) ^ 2 =
        (k + e) ^ 2 * (k.multichoose e) ^ 2 := by nlinarith [congrArg (fun n : ℕ => n ^ 2) h1]
    have hr : (e + 1) ^ 2 * (k ^ 2).multichoose (e + 1) =
        ((e + 1) * (k ^ 2 + e)) * (k ^ 2).multichoose e := by nlinarith [congrArg (fun n : ℕ => (e + 1) * n) h2]
    have htotal : (e + 1) ^ 2 * (k.multichoose (e + 1)) ^ 2 ≤
        (e + 1) ^ 2 * (k ^ 2).multichoose (e + 1) := by
      rw [hsquare, hr]
      exact hmul.trans hratio'
    exact Nat.le_of_mul_le_mul_left htotal (by positivity)

/-- The square of the k-fold divisor count is bounded by the k squared fold count. -/
theorem divisorCount_sq_le (k n : ℕ) : divisorCount k n ^ 2 ≤ divisorCount (k ^ 2) n := by
  by_cases hn : n = 0
  · simp [hn, divisorCount]
  have hmult (j : ℕ) : (ArithmeticFunction.zeta ^ j).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.pow
  have hfactor (j : ℕ) : divisorCount j n =
      ∏ p ∈ n.primeFactors, divisorCount j (p ^ n.factorization p) := by
    have h := ArithmeticFunction.IsMultiplicative.multiplicative_factorization (ArithmeticFunction.zeta ^ j) (hmult j) hn
    simpa only [Finsupp.prod, Nat.support_factorization, divisorCount] using h
  rw [hfactor k, hfactor (k ^ 2), ← Finset.prod_pow]
  apply Finset.prod_le_prod'
  intro p hp
  rw [divisorCount_prime_pow k p _ (Nat.prime_of_mem_primeFactors hp),
    divisorCount_prime_pow (k ^ 2) p _ (Nat.prime_of_mem_primeFactors hp)]
  exact multichoose_sq_le k _

/-- The complete divisor second moment bound cited after equation 7, with constant one. -/
theorem divisorSecondMoment (k : ℕ) (hk : 1 ≤ k) : Section2.DivisorSecondMoment k := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  let N := ⌊x⌋₊
  have hN : 1 ≤ N := (Nat.le_floor_iff hx0.le).mpr (by norm_num; linarith)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hlog : 0 ≤ 1 + Real.log N := by
    have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    linarith
  have hlogle : 1 + Real.log N ≤ Real.log (Real.exp 1 * x) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hx0.ne', Real.log_exp]
    exact add_le_add le_rfl (Real.log_le_log hN0 hNx)
  have hk2 : k ^ 2 - 1 + 1 = k ^ 2 := by have : 1 ≤ k ^ 2 := one_le_pow₀ hk; omega
  have hfirst := divisor_first_moment (k ^ 2 - 1) N
  rw [hk2] at hfirst
  have hset : Icc 1 N = Ioc 0 N := by ext n; simp; omega
  norm_num only [one_mul]
  change (∑ n ∈ Icc 1 N, (divisorCount k n : ℝ) ^ 2) ≤ _
  rw [hset]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (divisorCount (k ^ 2) n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact_mod_cast divisorCount_sq_le k n
    _ ≤ N * (1 + Real.log N) ^ (k ^ 2 - 1) := hfirst
    _ ≤ _ := by gcongr


end
end LeanLab.Perelli1996.Divisor103
