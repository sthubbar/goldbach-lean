module

public import LeanLab.ChebyshevExplicit.Psi30

/-!
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T1515Z-cloud27, unit U-5652.

# Chebyshev's explicit upper bound with the weight 1, -1/2, -1/3, -1/5, +1/30

`psi_le_chebyshev30`: for every natural `n`, `ψ(n) ≤ (6/5) A n + 2 log² n + 160`, with Chebyshev's
`A = 0.92129...` of `Psi30.lean`, so `(6/5) A < 1.1062`; `psi_le_11062` states it with `1.1062`.
Mathlib's `Chebyshev.theta_le_log4_mul_x` has `log 4 = 1.386`.

Proof, Chebyshev 1852. The weight `S(k) = k - ⌊k/2⌋ - ⌊k/3⌋ - ⌊k/5⌋ + ⌊k/30⌋` is `≥ 0` always and
`= 1` for `1 ≤ k ≤ 5`, so the combination `C(n)` of `Psi30.lean` is at least `ψ(n) - ψ(⌊n/6⌋)`.
Mathlib's two-sided bound for `log ⌊x⌋!` gives `C(n) ≤ A n + 5 log n - 2 log 30 - 1` for `n ≥ 30`.
Strong induction on `n` with `n ↦ ⌊n/6⌋` sums the geometric series `A n (1 + 1/6 + 1/36 + ...)`.

KNOWN mathematics, Chebyshev 1852. No cited input. Goldbach is open.
-/

@[expose] public section

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- The weight is nonnegative. -/
lemma weight_nonneg (k : ℕ) :
    0 ≤ (k : ℤ) - (k / 2 : ℕ) - (k / 3 : ℕ) - (k / 5 : ℕ) + (k / 30 : ℕ) := by
  push_cast; omega

/-- The weight is `1` on `1 ≤ k ≤ 5`. -/
lemma weight_eq_one (k : ℕ) (h1 : 1 ≤ k) (h5 : k ≤ 5) :
    (k : ℤ) - (k / 2 : ℕ) - (k / 3 : ℕ) - (k / 5 : ℕ) + (k / 30 : ℕ) = 1 := by
  interval_cases k <;> norm_num

/-- The per-prime bracket is at least `⌊log_p n⌋ - ⌊log_p ⌊n/6⌋⌋`. -/
lemma bracket_ge (n p : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    (Nat.log p n : ℤ) - (Nat.log p (n / 6) : ℤ) ≤
    ((n.factorial.factorization p : ℕ) : ℤ) - ((n / 2).factorial.factorization p : ℕ)
      - ((n / 3).factorial.factorization p : ℕ) - ((n / 5).factorial.factorization p : ℕ)
      + ((n / 30).factorial.factorization p : ℕ) := by
  have hb : ∀ m, m ≤ n → Nat.log p m < Nat.log p n + 1 := fun m hm =>
    Nat.lt_succ_of_le (Nat.log_mono_right hm)
  rw [Nat.factorization_factorial hp (hb n le_rfl),
    Nat.factorization_factorial hp (hb _ (Nat.div_le_self n 2)),
    Nat.factorization_factorial hp (hb _ (Nat.div_le_self n 3)),
    Nat.factorization_factorial hp (hb _ (Nat.div_le_self n 5)),
    Nat.factorization_factorial hp (hb _ (Nat.div_le_self n 30))]
  simp only [Nat.cast_sum]
  rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  have e : ∀ i j, n / j / p ^ i = n / p ^ i / j := fun i j => by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  simp only [e]
  set a := Nat.log p (n / 6)
  have ha : a ≤ Nat.log p n := Nat.log_mono_right (Nat.div_le_self n 6)
  have hsub : Ioc a (Nat.log p n) ⊆ Ico 1 (Nat.log p n + 1) := by
    intro i hi; rw [mem_Ioc] at hi; rw [mem_Ico]; omega
  calc (Nat.log p n : ℤ) - (a : ℤ) = ∑ _i ∈ Ioc a (Nat.log p n), (1 : ℤ) := by
        simp; omega
    _ = ∑ i ∈ Ioc a (Nat.log p n), (((n / p ^ i : ℕ) : ℤ) - ((n / p ^ i / 2 : ℕ) : ℤ)
          - ((n / p ^ i / 3 : ℕ) : ℤ) - ((n / p ^ i / 5 : ℕ) : ℤ) + ((n / p ^ i / 30 : ℕ) : ℤ)) := by
        apply sum_congr rfl
        intro i hi
        rw [mem_Ioc] at hi
        have hP : p ^ i ≤ n := Nat.pow_le_of_le_log hn hi.2
        have hP6 : n / 6 < p ^ i := Nat.lt_pow_of_log_lt hp.one_lt hi.1
        have hPpos : 0 < p ^ i := pow_pos hp.pos i
        have h1 : 1 ≤ n / p ^ i := (Nat.one_le_div_iff hPpos).mpr hP
        have h5 : n / p ^ i ≤ 5 := by
          have : n / p ^ i < 6 := (Nat.div_lt_iff_lt_mul hPpos).mpr (by omega)
          omega
        exact (weight_eq_one _ h1 h5).symm
    _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro i _ _
        exact weight_nonneg _

/-- `ψ(n) - ψ(⌊n/6⌋) ≤ C(n)`. -/
theorem psi_sub_le_combo (n : ℕ) :
    ψ n - ψ ((n / 6 : ℕ) : ℝ) ≤
      Real.log (n.factorial : ℝ) - Real.log ((n / 2).factorial : ℝ)
      - Real.log ((n / 3).factorial : ℝ) - Real.log ((n / 5).factorial : ℝ)
      + Real.log ((n / 30).factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp
  have hψ6 : ψ ((n / 6 : ℕ) : ℝ) = ∑ p ∈ Nat.primesLE n, (Nat.log p (n / 6) : ℝ) * Real.log p := by
    rw [psi_eq_sum_mul_log_prime]
    apply sum_subset
    · intro p hp
      rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.div_le_self n 6)⟩, hp.2⟩
    · intro p hp1 hp
      have : n / 6 < p := by
        by_contra h
        apply hp
        rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc] at hp1 ⊢
        exact ⟨⟨Nat.zero_le _, by omega⟩, hp1.2⟩
      simp [Nat.log_of_lt this]
  rw [log_factorial_eq_of_le le_rfl, log_factorial_eq_of_le (Nat.div_le_self n 2),
    log_factorial_eq_of_le (Nat.div_le_self n 3), log_factorial_eq_of_le (Nat.div_le_self n 5),
    log_factorial_eq_of_le (Nat.div_le_self n 30), psi_eq_sum_mul_log_prime, hψ6,
    ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib,
    ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  have hpp : p.Prime := by
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter] at hp; exact hp.2
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  have h := bracket_ge n p hpp hn.ne'
  have h' : (Nat.log p n : ℝ) - (Nat.log p (n / 6) : ℝ) ≤
      ((n.factorial.factorization p : ℕ) : ℝ) - ((n / 2).factorial.factorization p : ℕ)
      - ((n / 3).factorial.factorization p : ℕ) - ((n / 5).factorial.factorization p : ℕ)
      + ((n / 30).factorial.factorization p : ℕ) := by
    exact_mod_cast h
  nlinarith

/-- `C(n) ≤ A n + 5 log n - 2 log 30 - 1` for `n ≥ 30`. -/
theorem combo_le (n : ℕ) (hn : 30 ≤ n) :
    Real.log (n.factorial : ℝ) - Real.log ((n / 2).factorial : ℝ)
      - Real.log ((n / 3).factorial : ℝ) - Real.log ((n / 5).factorial : ℝ)
      + Real.log ((n / 30).factorial : ℝ) ≤ A * n + 5 * Real.log n - 2 * Real.log 30 - 1 := by
  have hn' : (30 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) < n := by linarith
  have e1 : Real.log (n.factorial : ℝ) = ∑ k ∈ Ioc 0 ⌊(n : ℝ)⌋₊, Real.log k := by
    rw [Nat.floor_natCast, Real.sum_log_eq_log_factorial]
  rw [e1, log_fact_div, log_fact_div, log_fact_div, log_fact_div]
  have u1 := Real.sum_log_le (x := (n : ℝ)) (by linarith)
  have l2 := Real.le_sum_log (x := (n : ℝ) / (2 : ℕ)) (by push_cast; linarith)
  have l3 := Real.le_sum_log (x := (n : ℝ) / (3 : ℕ)) (by push_cast; linarith)
  have l5 := Real.le_sum_log (x := (n : ℝ) / (5 : ℕ)) (by push_cast; linarith)
  have u30 := Real.sum_log_le (x := (n : ℝ) / (30 : ℕ)) (by
    push_cast; rw [le_div_iff₀ (by norm_num)]; linarith)
  push_cast at l2 l3 l5 u30 ⊢
  rw [Real.log_div h0.ne' (by norm_num)] at l2 l3 l5 u30
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  unfold A
  rw [h30] at u30 ⊢
  nlinarith [u1, l2, l3, l5, u30]

/-- `ψ(n) - ψ(⌊n/6⌋) ≤ A n + 5 log n` for `n ≥ 30`. -/
theorem psi_sub_psi_div6_le (n : ℕ) (hn : 30 ≤ n) :
    ψ n - ψ ((n / 6 : ℕ) : ℝ) ≤ A * n + 5 * Real.log n := by
  have h := (psi_sub_le_combo n).trans (combo_le n hn)
  have h30 : 0 ≤ Real.log 30 := Real.log_nonneg (by norm_num)
  linarith

lemma A_pos : 0 < A := lt_trans (by norm_num) A_gt

/-- **Chebyshev 1852, explicit upper bound.** `ψ(n) ≤ (6/5) A n + 2 log² n + 160` for every `n`. -/
theorem psi_le_chebyshev30 (n : ℕ) :
    ψ n ≤ 6 / 5 * A * n + 2 * Real.log n ^ 2 + 160 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hA := A_pos
  by_cases hn : n < 30
  · have h := psi_le_const_mul_self (x := (n : ℝ)) (by positivity)
    have hn' : (n : ℝ) ≤ 29 := by exact_mod_cast (by omega : n ≤ 29)
    have hl4 : Real.log 4 < 1.3863 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
      linarith [Real.log_two_lt_d9]
    have : 0 ≤ (n : ℝ) := by positivity
    nlinarith [sq_nonneg (Real.log n)]
  push Not at hn
  set m := n / 6 with hm
  have hmn : m < n := by omega
  have ihm := ih m hmn
  have hstep := psi_sub_psi_div6_le n hn
  have hm1 : 1 ≤ m := by omega
  have hmR : (m : ℝ) * 6 ≤ n := by exact_mod_cast (by omega : m * 6 ≤ n)
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hlogm0 : 0 ≤ Real.log m := Real.log_nonneg hm1R
  -- `log m ≤ log n - log 6`, `log 6 ≥ 1.79`, `log n ≥ 3`
  have hl6 : 1.79 ≤ Real.log 6 := by
    have h3 := log_ge_of_pow 3 84 53 (by norm_num) (by norm_num)
    have h2 := Real.log_two_gt_d9
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    push_cast at h3; nlinarith
  have hlogm : Real.log m ≤ Real.log n - Real.log 6 := by
    rw [← Real.log_div (by positivity) (by norm_num)]
    apply Real.log_le_log (by positivity)
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hln : 3 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : (30 : ℝ) ≤ n := by exact_mod_cast hn
    have he : exp 3 ≤ 2.7182818286 ^ 3 := by
      have := Real.exp_nat_mul 1 3
      rw [mul_one] at this
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, this]
      exact pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_d9.le 3
    linarith [show (2.7182818286 : ℝ) ^ 3 ≤ 21 by norm_num]
  have hsq : Real.log m ^ 2 ≤ (Real.log n - 1.79) ^ 2 := by
    apply pow_le_pow_left₀ hlogm0; linarith
  have hAm : 6 / 5 * A * (m : ℝ) ≤ 1 / 5 * A * n := by nlinarith
  nlinarith

/-- `(6/5) A < 1.1062`. -/
lemma A_upper : 6 / 5 * A < 1.1062 := by
  have h2 := Real.log_two_lt_d9
  have h3 : Real.log 3 ≤ 65 / 41 * Real.log 2 := by
    have h : Real.log ((3 : ℝ) ^ 41) ≤ Real.log ((2 : ℝ) ^ 65) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith
  have h5 : Real.log 5 ≤ 100 / 43 * Real.log 2 := by
    have h : Real.log ((5 : ℝ) ^ 43) ≤ Real.log ((2 : ℝ) ^ 100) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  unfold A; rw [h30]; linarith

/-- `ψ(n) ≤ 1.1062 n + 2 log² n + 160` for every `n`. -/
theorem psi_le_11062 (n : ℕ) : ψ n ≤ 1.1062 * n + 2 * Real.log n ^ 2 + 160 := by
  have h := psi_le_chebyshev30 n
  have hA := A_upper
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-- `θ(n) ≤ 1.1062 n + 2 log² n + 160`, since `θ ≤ ψ`. -/
theorem theta_le_11062 (n : ℕ) : θ n ≤ 1.1062 * n + 2 * Real.log n ^ 2 + 160 :=
  (theta_le_psi _).trans (psi_le_11062 n)

end LeanLab.ChebyshevExplicit

