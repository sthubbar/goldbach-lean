module

public import LeanLab.AlmostPrimes.DDLemma23Full
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Log.Sum

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T0715Z-cloud19, unit U-5260.
P0048 Dudek-Dunn Lemma 2.3 cites Rosser and Schoenfeld 1962 for `Σ_{p < z} log p / p < log z`.
This file PROVES that bound for every real `z ≥ 1000`, with no cited input, by Legendre's formula:
`log n! ≥ Σ_{p ≤ n} (n/p - 1) log p + Σ_{p ≤ 13} (n/p² - 1) log p`, Stirling's
`log n! ≤ n log n - n + log n + 1`, and Chebyshev's `θ(n) ≤ n log 4` from Mathlib. The prime square
terms for `p ≤ 13` give `Σ log p / p² ≥ 0.4327 > log 4 - 1 + 0.046`, which pays for `θ(n)`.
Rosser-Schoenfeld state it for all `z > 1`; the range below 1000 is not needed by Lemma 2.3, which
takes `z ≥ 10^10`. `rankin_sum_lt_of_RS1` is Lemma 2.3 CONDITIONAL ON the `Σ 1/p` bound only.
KNOWN mathematics. Goldbach is open.
-/

@[expose] public section

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.RSLogSum

/-- Legendre: `log n! = Σ_{p ≤ n} v_p(n!) log p`. -/
lemma log_factorial_eq (n : ℕ) :
    Real.log ((n.factorial : ℕ) : ℝ) =
      ∑ p ∈ Nat.primesLE n, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hle : p ≤ n := (Nat.Prime.dvd_factorial hpp).1 (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc]
    exact ⟨⟨Nat.zero_le _, hle⟩, hpp⟩
  · intro p _; simp

/-- `v_p(n!) ≥ ⌊n/p⌋ + ⌊n/p²⌋`. -/
lemma two_terms_le (n p : ℕ) (hp : p.Prime) :
    n / p + n / p ^ 2 ≤ n.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (b := Nat.log p n + 3) (by omega)]
  have hsub : ({1, 2} : Finset ℕ) ⊆ Ico 1 (Nat.log p n + 3) := by
    intro i hi; simp at hi; simp; omega
  calc n / p + n / p ^ 2 = ∑ i ∈ ({1, 2} : Finset ℕ), n / p ^ i := by
        rw [sum_pair (by norm_num)]; simp
    _ ≤ _ := sum_le_sum_of_subset hsub

/-- `n/d - 1 ≤ ⌊n/d⌋`. -/
lemma div_sub_one_le (n d : ℕ) (hd : 0 < d) : (n : ℝ) / d - 1 ≤ ((n / d : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := n) hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [sub_le_iff_le_add, div_le_iff₀ hd']
  have : (n : ℝ) < ((n / d : ℕ) : ℝ) * d + d := by exact_mod_cast h
  nlinarith

/-- The six primes whose square terms are kept. -/
def Q : Finset ℕ := {2, 3, 5, 7, 11, 13}

lemma Q_prime : ∀ p ∈ Q, p.Prime := by
  intro p hp; simp [Q] at hp; rcases hp with h | h | h | h | h | h <;> subst h <;> norm_num

lemma Q_sub (n : ℕ) (hn : 13 ≤ n) : Q ⊆ Nat.primesLE n := by
  intro p hp
  have hle : p ≤ 13 := by simp [Q] at hp; omega
  rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc]
  exact ⟨⟨Nat.zero_le _, by omega⟩, Q_prime p hp⟩

/-- Legendre lower bound: `n S(n) - θ(n) + Σ_{p ∈ Q} (n/p² - 1) log p ≤ log n!`. -/
lemma legendre_lower (n : ℕ) (hn : 13 ≤ n) :
    (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p - ∑ p ∈ Nat.primesLE n, Real.log p
      + ∑ p ∈ Q, ((n : ℝ) / p ^ 2 - 1) * Real.log p ≤ Real.log ((n.factorial : ℕ) : ℝ) := by
  rw [log_factorial_eq]
  have hQ := Q_sub n hn
  have key : ∀ p ∈ Nat.primesLE n,
      ((n : ℝ) / p - 1) * Real.log p + (if p ∈ Q then ((n : ℝ) / p ^ 2 - 1) * Real.log p else 0)
        ≤ ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
    intro p hp
    have hpp : p.Prime := (Nat.prime_of_mem_primesBelow hp)
    have hp0 : 0 < p := hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    have h1 := div_sub_one_le n p hp0
    have h2 := div_sub_one_le n (p ^ 2) (by positivity)
    have h3 : ((n / p : ℕ) : ℝ) + ((n / p ^ 2 : ℕ) : ℝ) ≤ ((n.factorial.factorization p : ℕ) : ℝ) := by
      exact_mod_cast two_terms_le n p hpp
    have h20 : (0 : ℝ) ≤ ((n / p ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast at h2
    split_ifs
    · nlinarith
    · nlinarith
  calc _ = ∑ p ∈ Nat.primesLE n, (((n : ℝ) / p - 1) * Real.log p
          + (if p ∈ Q then ((n : ℝ) / p ^ 2 - 1) * Real.log p else 0)) := by
        rw [sum_add_distrib, ← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hQ, mul_sum,
          ← sum_sub_distrib]
        congr 1
        apply sum_congr rfl; intro p hp
        ring
    _ ≤ _ := sum_le_sum key

lemma log_two_bounds : 0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

lemma log_ge_of_pow (p a b : ℕ) (h : 2 ^ a ≤ p ^ b) (hb : 0 < b) :
    (a : ℝ) / b * Real.log 2 ≤ Real.log p := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have := Real.log_le_log hp (by exact_mod_cast h : (2 : ℝ) ^ a ≤ (p : ℝ) ^ b)
  rw [Real.log_pow, Real.log_pow] at this
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_mul_eq_mul_div, div_le_iff₀ hb']; linarith

lemma log_le_of_pow (p a : ℕ) (hp : 0 < p) (h : p ≤ 2 ^ a) :
    Real.log p ≤ a * Real.log 2 := by
  have := Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast h : ((p : ℕ) : ℝ) ≤ ((2 ^ a : ℕ) : ℝ))
  push_cast at this; rw [Real.log_pow] at this; exact this

/-- `Σ_{p ∈ Q} log p / p² > 0.4327`, so it beats `log 4 - 1 ≈ 0.3863`. -/
lemma TQ_ge : 2 * Real.log 2 - 1 + 0.04 < ∑ p ∈ Q, Real.log p / (p : ℝ) ^ 2 := by
  have l3 := log_ge_of_pow 3 19 12 (by norm_num) (by norm_num)
  have l5 := log_ge_of_pow 5 23 10 (by norm_num) (by norm_num)
  have l7 := log_ge_of_pow 7 14 5 (by norm_num) (by norm_num)
  have l11 := log_ge_of_pow 11 10 3 (by norm_num) (by norm_num)
  have l13 := log_ge_of_pow 13 11 3 (by norm_num) (by norm_num)
  have h2 := log_two_bounds
  simp only [Q]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  push_cast at l3 l5 l7 l11 l13 ⊢
  norm_num at l3 l5 l7 l11 l13 ⊢
  linarith

lemma thetaQ_le : ∑ p ∈ Q, Real.log p ≤ 17 * Real.log 2 := by
  have l3 := log_le_of_pow 3 2 (by norm_num) (by norm_num)
  have l5 := log_le_of_pow 5 3 (by norm_num) (by norm_num)
  have l7 := log_le_of_pow 7 3 (by norm_num) (by norm_num)
  have l11 := log_le_of_pow 11 4 (by norm_num) (by norm_num)
  have l13 := log_le_of_pow 13 4 (by norm_num) (by norm_num)
  simp only [Q]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  push_cast at l3 l5 l7 l11 l13 ⊢
  linarith

/-- **Rosser-Schoenfeld 1962 (3.24) in the form Dudek-Dunn cite**, for integers:
`Σ_{p ≤ n} log p / p < log n` for every `n ≥ 1000`. No cited input. -/
theorem sum_log_div_lt_log (n : ℕ) (hn : 1000 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p < Real.log n := by
  have hn13 : 13 ≤ n := by omega
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL := legendre_lower n hn13
  -- Stirling-type upper bound
  have hfac : Real.log ((n.factorial : ℕ) : ℝ) ≤ n * Real.log n - n + Real.log n + 1 := by
    have h := Real.sum_log_le (x := (n : ℝ)) (by linarith)
    rw [Nat.floor_natCast, Real.sum_log_eq_log_factorial] at h
    exact h
  -- Chebyshev
  have hθ : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]; exact Chebyshev.theta_le_log4_mul_x hn0.le
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  -- the Q sum
  have hQs : ∑ p ∈ Q, ((n : ℝ) / p ^ 2 - 1) * Real.log p
      = n * ∑ p ∈ Q, Real.log p / (p : ℝ) ^ 2 - ∑ p ∈ Q, Real.log p := by
    rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro p _; ring
  have hT := TQ_ge
  have hθQ := thetaQ_le
  have h2 := log_two_bounds
  -- log n ≤ n/100 + 5
  have hlogn : Real.log n ≤ n / 100 + 5 := by
    have h1 := Real.log_le_sub_one_of_pos (x := (n : ℝ) / 100) (by positivity)
    rw [Real.log_div hn0.ne' (by norm_num)] at h1
    have : Real.log 100 ≤ 7 * Real.log 2 := by
      have := log_le_of_pow 100 7 (by norm_num) (by norm_num); push_cast at this; exact this
    linarith
  rw [hQs] at hL
  set T := ∑ p ∈ Q, Real.log p / (p : ℝ) ^ 2
  set S := ∑ p ∈ Nat.primesLE n, Real.log p / p
  rw [hlog4] at hθ
  have hnT := mul_lt_mul_of_pos_left hT hn0
  have e1 : (n : ℝ) * (2 * Real.log 2 - 1 + 4e-2) = 2 * Real.log 2 * n - n + 4e-2 * n := by ring
  rw [e1] at hnT
  -- n S ≤ n log n - n + log n + 1 + θ - n T + θ_Q
  have hmain : n * S < n * Real.log n := by
    linarith [h2.2]
  exact lt_of_mul_lt_mul_left hmain hn0.le

/-- The real form used by Dudek-Dunn Lemma 2.3: for `z ≥ 1000` and any set `P` of primes below
`z`, `Σ_{p ∈ P} log p / p < log z`. -/
theorem sum_log_div_lt_log_real (z : ℝ) (hz : 1000 ≤ z) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) < z) :
    ∑ p ∈ P, Real.log p / p < Real.log z := by
  have hz0 : 0 < z := by linarith
  set n := ⌊z⌋₊
  have hn : 1000 ≤ n := Nat.le_floor (by exact_mod_cast hz)
  have hsub : P ⊆ Nat.primesLE n := by
    intro p hp
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc]
    exact ⟨⟨Nat.zero_le _, Nat.le_floor (hP p hp).2.le⟩, (hP p hp).1⟩
  have hnn : ∀ p ∈ Nat.primesLE n, p ∉ P → 0 ≤ Real.log p / p := fun p _ _ =>
    div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  calc ∑ p ∈ P, Real.log p / p ≤ ∑ p ∈ Nat.primesLE n, Real.log p / p :=
        sum_le_sum_of_subset_of_nonneg hsub hnn
    _ < Real.log n := sum_log_div_lt_log n hn
    _ ≤ Real.log z := Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
        (Nat.floor_le hz0.le)

/-- **Dudek-Dunn Lemma 2.3**, the Rankin divisor sum bound, now CONDITIONAL ON the
Rosser-Schoenfeld `Σ 1/p < log log z + 0.2634` bound only; the `Σ log p / p` input is PROVED. -/
theorem rankin_sum_lt_of_RS1 (z : ℝ) (hz : 10 ^ 10 ≤ z) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) < z)
    (hRS1 : ∑ p ∈ P, (1 : ℝ) / p < log (log z) + 0.2634) :
    ∑ s ∈ P.powerset.filter (fun s : Finset ℕ => (∏ p ∈ s, ((p : ℕ) : ℝ)) < z ^ (18.4 : ℝ)),
        (8 : ℝ) ^ s.card < 0.591 * z ^ (18.4 : ℝ) * log z ^ 8 :=
  DDLemma23.rankin_sum_lt z hz P hP hRS1
    (sum_log_div_lt_log_real z (by linarith) P hP)

end LeanLab.AlmostPrimes.RSLogSum

