module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Log.Sum
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Prime.Factorial

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1515Z-cloud27, unit U-5650.

# Chebyshev's explicit lower bound with the weight 1, -1/2, -1/3, -1/5, +1/30

`psi_ge_chebyshev30`: for every natural `n ≥ 30`,
`ψ(n) ≥ A n - 5 log n + 2 log 30 - 1` with `A = log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30`,
`A = 0.92129...`. `pi_ge_chebyshev30`: `π(n) ≥ (0.9212 n - 5 log n) / log n` for `n ≥ 30`.

Mathlib's `Chebyshev.psi_ge` and `Chebyshev.pi_ge` have the constant `log 2 = 0.6931`.

Proof, Chebyshev 1852. Put `C(n) = log n! - log ⌊n/2⌋! - log ⌊n/3⌋! - log ⌊n/5⌋! + log ⌊n/30⌋!`.
By Legendre, `C(n) = Σ_{p ≤ n} log p Σ_{i ≥ 1} S(⌊n/p^i⌋)` with
`S(k) = k - ⌊k/2⌋ - ⌊k/3⌋ - ⌊k/5⌋ + ⌊k/30⌋ ≤ 1`, so `C(n) ≤ Σ_p ⌊log_p n⌋ log p = ψ(n)`.
Mathlib's two-sided bound `x log x - x - log x + 1 ≤ log ⌊x⌋! ≤ x log x - x + log x + 1` then gives
`C(n) ≥ A n - 5 log n + 2 log 30 - 1`.

KNOWN mathematics, Chebyshev 1852. No cited input. Goldbach is open.
-/

@[expose] public section

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- Chebyshev's weight: `S(k) = k - ⌊k/2⌋ - ⌊k/3⌋ - ⌊k/5⌋ + ⌊k/30⌋ ≤ 1`. -/
lemma weight_le_one (k : ℕ) :
    (k : ℤ) - (k / 2 : ℕ) - (k / 3 : ℕ) - (k / 5 : ℕ) + (k / 30 : ℕ) ≤ 1 := by
  push_cast; omega

/-- Legendre over any prime range containing `m`: `log m! = Σ_{p ≤ n} v_p(m!) log p`. -/
lemma log_factorial_eq_of_le {m n : ℕ} (hmn : m ≤ n) :
    Real.log ((m.factorial : ℕ) : ℝ) =
      ∑ p ∈ Nat.primesLE n, ((m.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hle : p ≤ m := (Nat.Prime.dvd_factorial hpp).1 (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc]
    exact ⟨⟨Nat.zero_le _, hle.trans hmn⟩, hpp⟩
  · intro p _; simp

/-- The per-prime bracket is at most `⌊log_p n⌋`. -/
lemma bracket_le (n p : ℕ) (hp : p.Prime) :
    ((n.factorial.factorization p : ℕ) : ℤ) - ((n / 2).factorial.factorization p : ℕ)
      - ((n / 3).factorial.factorization p : ℕ) - ((n / 5).factorial.factorization p : ℕ)
      + ((n / 30).factorial.factorization p : ℕ) ≤ (Nat.log p n : ℤ) := by
  have hb : ∀ m, m ≤ n → Nat.log p m < Nat.log p n + 1 := fun m hm =>
    Nat.lt_succ_of_le (Nat.log_mono_right hm)
  rw [Nat.factorization_factorial hp (hb n le_rfl),
    Nat.factorization_factorial hp (hb _ (Nat.div_le_self n 2)),
    Nat.factorization_factorial hp (hb _ (Nat.div_le_self n 3)),
    Nat.factorization_factorial hp (hb _ (Nat.div_le_self n 5)),
    Nat.factorization_factorial hp (hb _ (Nat.div_le_self n 30))]
  simp only [Nat.cast_sum]
  rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  calc _ ≤ ∑ _i ∈ Ico 1 (Nat.log p n + 1), (1 : ℤ) := by
        apply sum_le_sum
        intro i _
        have e : ∀ j, n / j / p ^ i = n / p ^ i / j := fun j => by
          rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
        rw [e 2, e 3, e 5, e 30]
        exact weight_le_one (n / p ^ i)
    _ = _ := by simp

/-- `C(n) ≤ ψ(n)`. -/
theorem combo_le_psi (n : ℕ) :
    Real.log (n.factorial : ℝ) - Real.log ((n / 2).factorial : ℝ)
      - Real.log ((n / 3).factorial : ℝ) - Real.log ((n / 5).factorial : ℝ)
      + Real.log ((n / 30).factorial : ℝ) ≤ ψ n := by
  rw [log_factorial_eq_of_le le_rfl, log_factorial_eq_of_le (Nat.div_le_self n 2),
    log_factorial_eq_of_le (Nat.div_le_self n 3), log_factorial_eq_of_le (Nat.div_le_self n 5),
    log_factorial_eq_of_le (Nat.div_le_self n 30), psi_eq_sum_mul_log_prime,
    ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  have hpp : p.Prime := by
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter] at hp; exact hp.2
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  have h := bracket_le n p hpp
  have h' : ((n.factorial.factorization p : ℕ) : ℝ) - ((n / 2).factorial.factorization p : ℕ)
      - ((n / 3).factorial.factorization p : ℕ) - ((n / 5).factorial.factorization p : ℕ)
      + ((n / 30).factorial.factorization p : ℕ) ≤ (Nat.log p n : ℝ) := by
    exact_mod_cast h
  nlinarith

/-- `log ⌊n/j⌋! = log ⌊(n : ℝ)/j⌋₊!` written as Mathlib's partial sum of `log`. -/
lemma log_fact_div (n j : ℕ) :
    Real.log ((n / j).factorial : ℝ) = ∑ k ∈ Ioc 0 ⌊(n : ℝ) / j⌋₊, Real.log k := by
  rw [Nat.floor_div_eq_div, Real.sum_log_eq_log_factorial]

/-- The constant `A = log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30`. -/
def A : ℝ := Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30

/-- **Chebyshev 1852, explicit.** `ψ(n) ≥ A n - 5 log n + 2 log 30 - 1` for `n ≥ 30`. -/
theorem psi_ge_chebyshev30 (n : ℕ) (hn : 30 ≤ n) :
    A * n - 5 * Real.log n + 2 * Real.log 30 - 1 ≤ ψ n := by
  have hn' : (30 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) < n := by linarith
  refine le_trans ?_ (combo_le_psi n)
  have e1 : Real.log (n.factorial : ℝ) = ∑ k ∈ Ioc 0 ⌊(n : ℝ)⌋₊, Real.log k := by
    rw [Nat.floor_natCast, Real.sum_log_eq_log_factorial]
  rw [e1, log_fact_div, log_fact_div, log_fact_div, log_fact_div]
  have l1 := Real.le_sum_log (x := (n : ℝ)) (by linarith)
  have u2 := Real.sum_log_le (x := (n : ℝ) / (2 : ℕ)) (by push_cast; linarith)
  have u3 := Real.sum_log_le (x := (n : ℝ) / (3 : ℕ)) (by push_cast; linarith)
  have u5 := Real.sum_log_le (x := (n : ℝ) / (5 : ℕ)) (by push_cast; linarith)
  have l30 := Real.le_sum_log (x := (n : ℝ) / (30 : ℕ)) (by
    push_cast; rw [le_div_iff₀ (by norm_num)]; linarith)
  push_cast at u2 u3 u5 l30 ⊢
  rw [Real.log_div h0.ne' (by norm_num)] at u2 u3 u5 l30
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  unfold A
  rw [h30] at l30 ⊢
  nlinarith [l1, u2, u3, u5, l30]

/-- `p^b ≥ 2^a` gives `log p ≥ (a/b) log 2`. -/
lemma log_ge_of_pow (p a b : ℕ) (h : 2 ^ a ≤ p ^ b) (hb : 0 < b) :
    (a : ℝ) / b * Real.log 2 ≤ Real.log p := by
  have h' : ((2 : ℝ)) ^ a ≤ (p : ℝ) ^ b := by exact_mod_cast h
  have hp : (0 : ℝ) < (p : ℝ) ^ b := lt_of_lt_of_le (by positivity) h'
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at this
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_mul_eq_mul_div, div_le_iff₀ hb']; linarith

/-- Numerical value: `A > 0.9212`. -/
lemma A_gt : (0.9212 : ℝ) < A := by
  have h2 := Real.log_two_gt_d9
  have h3 := log_ge_of_pow 3 84 53 (by norm_num) (by norm_num)
  have h5 := log_ge_of_pow 5 65 28 (by norm_num) (by norm_num)
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  push_cast at h3 h5
  unfold A; rw [h30]; linarith

/-- `ψ(n) ≥ 0.9212 n - 5 log n` for `n ≥ 30`. -/
theorem psi_ge_09212 (n : ℕ) (hn : 30 ≤ n) : 0.9212 * n - 5 * Real.log n ≤ ψ n := by
  have h := psi_ge_chebyshev30 n hn
  have hA := A_gt
  have h30 : 1 ≤ Real.log 30 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-- **Chebyshev's explicit lower bound for `π`.** `π(n) ≥ (0.9212 n - 5 log n) / log n` for
`n ≥ 30`, against Mathlib's `Chebyshev.pi_ge` with `log 2 = 0.6931`. -/
theorem pi_ge_chebyshev30 (n : ℕ) (hn : 30 ≤ n) :
    (0.9212 * n - 5 * Real.log n) / Real.log n ≤ (Nat.primeCounting n : ℝ) := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rw [div_le_iff₀ hlog]
  exact (psi_ge_09212 n hn).trans (psi_le_primeCounting_mul_log n)

/-- Vacuity test: the hypothesis holds at `n = 30`, and there the bound is a real constraint. -/
example : (0.9212 * (30 : ℕ) - 5 * Real.log (30 : ℕ)) / Real.log (30 : ℕ) ≤
    (Nat.primeCounting 30 : ℝ) := pi_ge_chebyshev30 30 le_rfl

end LeanLab.ChebyshevExplicit

