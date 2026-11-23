module

public import Mathlib

/-!
P0083 Perelli 1996, page 481 between equations 3 and 4.

This file contains small standard facts used for the final reduction step of the elementary
van der Corput 1939 / Landreau 1989 style bound that replaces the cited Nair 1992 mean value:
the weight m * tau(m) / phi(m) is at most tau(m)^2, submultiplicativity of the divisor count,
a polynomial size cutoff on the window, a floor power lower bound, the reduction to the primitive
part, and a window inclusion.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

open Polynomial

namespace LeanLab.Perelli1996.Nair103

theorem two_pow_omega_le_tau (m : ℕ) (hm : m ≠ 0) :
    2 ^ m.primeFactors.card ≤ m.divisors.card := by
  rw [Nat.card_divisors hm, ← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    have h1 : 0 < m.factorization p := hpp.factorization_pos_of_dvd hm hdvd
    show 2 ≤ m.factorization p + 1
    omega

theorem le_totient_mul_two_pow (m : ℕ) :
    m ≤ m.totient * 2 ^ m.primeFactors.card := by
  have h := Nat.totient_mul_prod_primeFactors m
  have hpos : 0 < ∏ p ∈ m.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hle : ∏ p ∈ m.primeFactors, p ≤
      2 ^ m.primeFactors.card * ∏ p ∈ m.primeFactors, (p - 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      show p ≤ 2 * (p - 1)
      omega
  have h2 : m * ∏ p ∈ m.primeFactors, (p - 1) ≤
      (m.totient * 2 ^ m.primeFactors.card) * ∏ p ∈ m.primeFactors, (p - 1) := by
    rw [← h, mul_assoc]
    exact Nat.mul_le_mul_left _ hle
  exact Nat.le_of_mul_le_mul_right h2 hpos

theorem weight_le_tau_sq (m : ℕ) :
    (m : ℝ) * m.divisors.card / m.totient ≤ (m.divisors.card : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  have hφ : (0 : ℝ) < (m.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hm
  have hnat : m ≤ m.totient * m.divisors.card :=
    (le_totient_mul_two_pow m).trans
      (Nat.mul_le_mul_left _ (two_pow_omega_le_tau m hm.ne'))
  have hreal : (m : ℝ) ≤ (m.totient : ℝ) * (m.divisors.card : ℝ) := by
    exact_mod_cast hnat
  have hτ : (0 : ℝ) ≤ (m.divisors.card : ℝ) := Nat.cast_nonneg _
  rw [div_le_iff₀ hφ]
  calc (m : ℝ) * (m.divisors.card : ℝ)
      ≤ ((m.totient : ℝ) * (m.divisors.card : ℝ)) * (m.divisors.card : ℝ) :=
        mul_le_mul_of_nonneg_right hreal hτ
    _ = (m.divisors.card : ℝ) ^ 2 * (m.totient : ℝ) := by ring

open scoped Pointwise in
theorem tau_mul_le (a b : ℕ) : (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

theorem window_cutoff (F : ℤ[X]) (hk : 1 ≤ F.natDegree) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ N H : ℝ, 1 ≤ N → 0 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ n : ℕ, (n : ℝ) ≤ N ^ (1 / (F.natDegree : ℝ)) + H + 1 → ((F.eval (n : ℤ) : ℤ) : ℝ) ≤ c * N := by
  set k := F.natDegree with hkdef
  set S : ℝ := ∑ i ∈ Finset.range (k + 1), |(F.coeff i : ℝ)| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have h3k : (0 : ℝ) ≤ 3 ^ k := by positivity
  refine ⟨1 + 3 ^ k * S, ?_, ?_⟩
  · have : 0 ≤ (3 : ℝ) ^ k * S := mul_nonneg h3k hS0
    linarith
  intro N H hN hH0 hH n hn
  set x : ℝ := N ^ (1 / (k : ℝ)) with hx
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hk0 : k ≠ 0 := by omega
  have hxk : x ^ k = N := by
    rw [hx, one_div]
    exact Real.rpow_inv_natCast_pow hN0 hk0
  have hx1 : 1 ≤ x := by
    rw [hx]
    exact Real.one_le_rpow hN (by positivity)
  have hn3 : (n : ℝ) ≤ 3 * x := by linarith
  have h3x1 : 1 ≤ 3 * x := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hev : ((F.eval (n : ℤ) : ℤ) : ℝ) = ∑ i ∈ Finset.range (k + 1), (F.coeff i : ℝ) * (n : ℝ) ^ i := by
    rw [Polynomial.eval_eq_sum_range, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (F.coeff i : ℝ) * (n : ℝ) ^ i ≤ |(F.coeff i : ℝ)| * (3 * x) ^ k := by
    intro i hi
    have hik : i ≤ k := by
      have := Finset.mem_range.mp hi
      omega
    have hp1 : (n : ℝ) ^ i ≤ (3 * x) ^ i := pow_le_pow_left₀ hn0 hn3 i
    have hp2 : (3 * x) ^ i ≤ (3 * x) ^ k := pow_le_pow_right₀ h3x1 hik
    have hp0 : (0 : ℝ) ≤ (n : ℝ) ^ i := pow_nonneg hn0 i
    calc (F.coeff i : ℝ) * (n : ℝ) ^ i
        ≤ |(F.coeff i : ℝ)| * (n : ℝ) ^ i :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hp0
      _ ≤ |(F.coeff i : ℝ)| * (3 * x) ^ k :=
          mul_le_mul_of_nonneg_left (hp1.trans hp2) (abs_nonneg _)
  have hsum : ((F.eval (n : ℤ) : ℤ) : ℝ) ≤ S * (3 * x) ^ k := by
    rw [hev, hS, Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  have hpow : (3 * x) ^ k = 3 ^ k * N := by
    rw [mul_pow, hxk]
  rw [hpow] at hsum
  nlinarith [hsum, hN0]

theorem floor_pow_ge (k : ℕ) (hk : 1 ≤ k) (c : ℝ) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → N ^ (1 / (3 * (k : ℝ))) ≤ H →
      c * N ≤ ((⌊H⌋₊ : ℝ)) ^ (4 * (k * (k + 1))) := by
  set R : ℕ := 4 * (k * (k + 1)) with hR
  refine ⟨max 3 (c * 2 ^ R), le_max_left _ _, ?_⟩
  intro N H hN hH
  have hN3 : (3 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hNc : c * 2 ^ R ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set y : ℝ := N ^ (1 / (3 * (k : ℝ))) with hy
  have h3k0 : 3 * k ≠ 0 := by omega
  have hy3k : y ^ (3 * k) = N := by
    have hcast : (1 / (3 * (k : ℝ))) = (((3 * k : ℕ) : ℝ))⁻¹ := by
      push_cast
      rw [one_div]
    rw [hy, hcast]
    exact Real.rpow_inv_natCast_pow hN0 h3k0
  have hy1 : 1 ≤ y := by
    rw [hy]
    exact Real.one_le_rpow hN1 (by positivity)
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hH1 : 1 ≤ H := hy1.trans hH
  -- floor lower bound
  have hfl1 : 1 ≤ ⌊H⌋₊ := Nat.le_floor (by exact_mod_cast hH1)
  have hfl1' : (1 : ℝ) ≤ (⌊H⌋₊ : ℝ) := by exact_mod_cast hfl1
  have hlt : H < (⌊H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one H
  have hhalf : y / 2 ≤ (⌊H⌋₊ : ℝ) := by linarith
  have hpowfl : (y / 2) ^ R ≤ ((⌊H⌋₊ : ℝ)) ^ R :=
    pow_le_pow_left₀ (by positivity) hhalf R
  -- y^R ≥ N^2
  have hRsplit : R = (3 * k) * (k + 1) + k * (k + 1) := by
    rw [hR]; ring
  have hyR : N ^ 2 ≤ y ^ R := by
    rw [hRsplit, pow_add, pow_mul, hy3k]
    have h1 : N ^ 2 ≤ N ^ (k + 1) := pow_le_pow_right₀ hN1 (by omega)
    have h2 : (1 : ℝ) ≤ y ^ (k * (k + 1)) := one_le_pow₀ hy1
    have h3 : (0 : ℝ) ≤ N ^ (k + 1) := pow_nonneg hN0 _
    calc N ^ 2 ≤ N ^ (k + 1) := h1
      _ = N ^ (k + 1) * 1 := (mul_one _).symm
      _ ≤ N ^ (k + 1) * y ^ (k * (k + 1)) := mul_le_mul_of_nonneg_left h2 h3
  have h2R : (0 : ℝ) < 2 ^ R := by positivity
  have hcN : c * N ≤ N ^ 2 / 2 ^ R := by
    rw [le_div_iff₀ h2R]
    have : c * 2 ^ R * N ≤ N * N := mul_le_mul_of_nonneg_right hNc hN0
    calc c * N * 2 ^ R = c * 2 ^ R * N := by ring
      _ ≤ N * N := this
      _ = N ^ 2 := by ring
  calc c * N ≤ N ^ 2 / 2 ^ R := hcN
    _ ≤ y ^ R / 2 ^ R := div_le_div_of_nonneg_right hyR h2R.le
    _ = (y / 2) ^ R := (div_pow y 2 R).symm
    _ ≤ ((⌊H⌋₊ : ℝ)) ^ R := hpowfl

theorem primPart_facts (F : ℤ[X]) (hk : 1 ≤ F.natDegree) (ha : 0 < F.leadingCoeff) :
    ∃ (c : ℕ) (G : ℤ[X]), 0 < c ∧ G.IsPrimitive ∧ G.natDegree = F.natDegree ∧ 0 < G.leadingCoeff ∧
      ∀ z : ℤ, F.eval z = (c : ℤ) * G.eval z := by
  have hF0 : F ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hk
    omega
  have hc0 : F.content ≠ 0 := fun h => hF0 (Polynomial.content_eq_zero_iff.mp h)
  have hcnn : 0 ≤ F.content := Int.nonneg_of_normalize_eq_self Polynomial.normalize_content
  have hcpos : 0 < F.content := lt_of_le_of_ne hcnn (Ne.symm hc0)
  have hcast : ((F.content.natAbs : ℕ) : ℤ) = F.content := Int.natAbs_of_nonneg hcnn
  have hlc : F.leadingCoeff = F.content * F.primPart.leadingCoeff := by
    conv_lhs => rw [F.eq_C_content_mul_primPart]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  refine ⟨F.content.natAbs, F.primPart, Int.natAbs_pos.mpr hc0, F.isPrimitive_primPart,
    F.natDegree_primPart, ?_, ?_⟩
  · rw [hlc] at ha
    by_contra hneg
    replace hneg := not_lt.mp hneg
    nlinarith [mul_nonneg hcpos.le (neg_nonneg.mpr hneg)]
  · intro z
    rw [hcast]
    conv_lhs => rw [F.eq_C_content_mul_primPart]
    rw [Polynomial.eval_mul, Polynomial.eval_C]

theorem win_subset (x H : ℝ) (hx : 0 ≤ x) (hH : 0 ≤ H) :
    Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊ ⊆ Finset.Icc ⌈x⌉₊ (⌈x⌉₊ + ⌊H⌋₊) := by
  apply Finset.Icc_subset_Icc le_rfl
  have _ := hx
  have h1 : x + H ≤ H + ((⌈x⌉₊ : ℕ) : ℝ) := by
    have := Nat.le_ceil x
    linarith
  calc ⌊x + H⌋₊ ≤ ⌊H + ((⌈x⌉₊ : ℕ) : ℝ)⌋₊ := Nat.floor_le_floor h1
    _ = ⌊H⌋₊ + ⌈x⌉₊ := Nat.floor_add_natCast hH _
    _ = ⌈x⌉₊ + ⌊H⌋₊ := add_comm _ _

end LeanLab.Perelli1996.Nair103
