module

public import LeanLab.LanguascoPerelli1996.Character422

/-!
P0071 page 355, the noncoprime coefficient error before display 14.
Embed the contributing prime powers into the divisors of a power of q.
Mathlib's exact divisor sum for Lambda supplies the logarithmic bound.
The primitive character replacement and explicit formula remain separate.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.LanguascoPerelli1996.BadPrimes422
open Real Finset

/-- Derived support bound for the noncoprime error before display 14.
A prime power n at most N sharing a prime with q divides q to the
integer base two logarithm of N. -/
theorem prime_power_dvd_modulus_power {n N q : ℕ} (hn : IsPrimePow n)
    (hN : n ≤ N) (hq : ¬ Nat.Coprime n q) : n ∣ q ^ (Nat.log 2 N) := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  have hpq : p ∣ q := hp.dvd_iff_not_coprime.mpr (by
    intro hc
    exact hq (hc.pow_left k))
  have hkN : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num)
    ((Nat.pow_le_pow_left hp.two_le k).trans hN)
  exact (pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkN)

/-- Derived finite error estimate before page 355 display 14.
The total Lambda weight of coefficients at most N not coprime to q
is at most integer log base two of N times log q. -/
theorem bad_vonMangoldt_sum (s : Finset ℕ) (N q : ℕ) (hq : 0 < q)
    (hs : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s.filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) ≤
      (Nat.log 2 N : ℝ) * Real.log q := by
  classical
  let b := s.filter (fun n => ¬ Nat.Coprime n q)
  have heq := Finset.sum_filter_of_ne (s := b) (p := IsPrimePow)
    (f := fun n => ArithmeticFunction.vonMangoldt n)
    (fun n hn hn0 => ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn0)
  have hsub : b.filter IsPrimePow ⊆ (q ^ (Nat.log 2 N)).divisors := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hb, hp⟩
    rcases Finset.mem_filter.mp hb with ⟨hns, hcop⟩
    exact Nat.mem_divisors.mpr
      ⟨prime_power_dvd_modulus_power hp (hs n hns) hcop, pow_ne_zero _ hq.ne'⟩
  change (∑ n ∈ b, ArithmeticFunction.vonMangoldt n) ≤ _
  rw [← heq]
  calc
    _ ≤ ∑ n ∈ (q ^ (Nat.log 2 N)).divisors, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n hn hnb => ArithmeticFunction.vonMangoldt_nonneg)
    _ = _ := by
      rw [ArithmeticFunction.vonMangoldt_sum, Nat.cast_pow, Real.log_pow]

/-- Page 355 before display 14, the explicit noncoprime exponential error.
The phases have norm one, so the preceding Lambda weight bounds its norm. -/
theorem bad_exponential_sum (s : Finset ℕ) (N : ℕ) {q : ℕ} [NeZero q]
    (a : ℕ) (η : ℝ) (hs : ∀ n ∈ s, n ≤ N) :
    ‖∑ n ∈ s.filter (fun n => ¬ Nat.Coprime n q),
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        e ((n : ℝ) * ((a : ℝ) / q)) * e ((n : ℝ) * η)‖ ≤
      (Nat.log 2 N : ℝ) * Real.log q := by
  have he (t : ℝ) : ‖e t‖ = 1 := by
    unfold e
    rw [Complex.norm_exp]
    simp
  calc
    _ ≤ ∑ n ∈ s.filter (fun n => ¬ Nat.Coprime n q),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          e ((n : ℝ) * ((a : ℝ) / q)) * e ((n : ℝ) * η)‖ := norm_sum_le _ _
    _ = ∑ n ∈ s.filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ _ := bad_vonMangoldt_sum s N q (Nat.pos_of_ne_zero (NeZero.ne q)) hs

/-- Derived real logarithmic form of the error before page 355 display 14.
The coefficient one over log two is a chosen explicit constant.
This is uniform in the additive phases and the finite stopped interval. -/
theorem bad_exponential_sum_log (s : Finset ℕ) (N : ℕ) {q : ℕ} [NeZero q]
    (a : ℕ) (η : ℝ) (hs : ∀ n ∈ s, n ≤ N) :
    ‖∑ n ∈ s.filter (fun n => ¬ Nat.Coprime n q),
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        e ((n : ℝ) * ((a : ℝ) / q)) * e ((n : ℝ) * η)‖ ≤
      Real.log N * Real.log q / Real.log 2 := by
  refine (bad_exponential_sum s N a η hs).trans ?_
  have hh := mul_le_mul_of_nonneg_right (Real.natLog_le_logb N 2)
    (Real.log_natCast_nonneg q)
  simpa only [Real.logb, Nat.cast_ofNat, div_mul_eq_mul_div] using hh

/-- Page 355 before display 14, derived quantitative character reduction
for the actual stopped remainder in page 358 display 21.
The character sums here use the original characters, not their primitive
inducing characters. The noncoprime contribution is bounded explicitly. -/
theorem stopped_character_error {q : ℕ} [NeZero q] (a : ℕ)
    (ha : Nat.Coprime a q) (X Y η : ℝ) :
    ‖Decomp381a.partialR X Y η q a -
      ((∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
          (∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊,
            (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * e ((n : ℝ) * η))) /
          (q.totient : ℂ) -
        (muPhi q : ℂ) * (∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊, e ((n : ℝ) * η)))‖ ≤
      Real.log ⌊Y⌋₊ * Real.log q / Real.log 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hh := Character422.stopped_character_expansion a ha X Y η
  have heq : Decomp381a.partialR X Y η q a -
      ((∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) * tau χ⁻¹ *
          (∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊,
            (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * e ((n : ℝ) * η))) /
          (q.totient : ℂ) -
        (muPhi q : ℂ) * (∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊, e ((n : ℝ) * η))) =
      ∑ n ∈ (Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊).filter (fun n => ¬ Nat.Coprime n q),
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          e ((n : ℝ) * ((a : ℝ) / q)) * e ((n : ℝ) * η) := by
    have hc (z : ℂ) : (q.totient : ℂ) * (z / (q.totient : ℂ)) = z := by
      field_simp [hφ]
    apply mul_left_cancel₀ hφ
    rw [mul_sub, mul_sub, hc]
    linear_combination hh
  rw [heq]
  exact bad_exponential_sum_log _ ⌊Y⌋₊ a η (fun n hn => (Finset.mem_Icc.mp hn).2)

end LeanLab.LanguascoPerelli1996.BadPrimes422

