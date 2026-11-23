module

public import LeanLab.Perelli1996.NairCount103
public import LeanLab.Perelli1996.NairPrep103
public import LeanLab.Perelli1996.Definitions103

/-!
P0083 Perelli 1996, page 481 between equations 3 and 4.

This file contains the final reduction step of the elementary van der Corput 1939 / Landreau 1989
style argument that replaces the short interval mean value cited from Nair 1992: the mean square
of the divisor weight m * tau(m) / phi(m) plus log N over the polynomial window is at most
C * H * (log N) ^ d for a fixed d. It reduces to the primitive part, bounds the weight by tau ^ 2,
and applies the fourth moment bound `tau_pow_sum` with the cutoff D = floor H.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

open Polynomial

namespace LeanLab.Perelli1996.Nair103

theorem toNat_natCast_mul_eq (c : ℕ) (z : ℤ) : ((c : ℤ) * z).toNat = c * z.toNat := by
  rcases le_total 0 z with h | h
  · lift z to ℕ using h
    rw [← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  · have h2 : (c : ℤ) * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg c) h
    rw [Int.toNat_of_nonpos h2, Int.toNat_of_nonpos h, mul_zero]

theorem term_le (c g : ℕ) (L : ℝ) :
    (((c * g : ℕ) : ℝ) * (c * g).divisors.card / (c * g).totient + L) ^ 2 ≤
      2 * ((c.divisors.card : ℝ) ^ 4 * (g.divisors.card : ℝ) ^ 4) + 2 * L ^ 2 := by
  have hw0 : (0 : ℝ) ≤ ((c * g : ℕ) : ℝ) * (c * g).divisors.card / (c * g).totient :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hw1 := weight_le_tau_sq (c * g)
  have ht : (((c * g).divisors.card : ℕ) : ℝ) ≤ (c.divisors.card : ℝ) * (g.divisors.card : ℝ) := by
    exact_mod_cast tau_mul_le c g
  have ht2 : (((c * g).divisors.card : ℕ) : ℝ) ^ 2 ≤
      ((c.divisors.card : ℝ) * (g.divisors.card : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) ht 2
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = ((c * g : ℕ) : ℝ) * (c * g).divisors.card / (c * g).totient :=
    ⟨_, rfl⟩
  rw [← hwdef] at hw0 hw1 ⊢
  have hw : w ≤ ((c.divisors.card : ℝ) * (g.divisors.card : ℝ)) ^ 2 := hw1.trans ht2
  have h2 : w ^ 2 ≤ (c.divisors.card : ℝ) ^ 4 * (g.divisors.card : ℝ) ^ 4 := by
    calc w ^ 2 ≤ (((c.divisors.card : ℝ) * (g.divisors.card : ℝ)) ^ 2) ^ 2 :=
          pow_le_pow_left₀ hw0 hw 2
      _ = _ := by ring
  nlinarith [sq_nonneg (w - L)]

theorem nair_mean_explicit (F : ℤ[X]) (hk : 1 ≤ F.natDegree) (ha : 0 < F.leadingCoeff) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ ε : ℝ, 0 < ε →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∑ n ∈ Finset.Icc ⌈N ^ (1 / (F.natDegree : ℝ))⌉₊ ⌊N ^ (1 / (F.natDegree : ℝ)) + H⌋₊,
        (((F.eval (n : ℤ)).toNat : ℝ) * (F.eval (n : ℤ)).toNat.divisors.card /
          (F.eval (n : ℤ)).toNat.totient + Real.log N) ^ 2 ≤ C * H * Real.log N ^ d := by
  obtain ⟨c, G, _hc, hprim, hdeg, _hGl, hev⟩ := primPart_facts F hk ha
  have hkG : 1 ≤ G.natDegree := by rw [hdeg]; exact hk
  obtain ⟨M, C₀, hC₀, hsum⟩ := tau_pow_sum G hkG hprim 4 (by norm_num)
  obtain ⟨cc, _hcc1, hcut⟩ := window_cutoff G hkG
  rw [hdeg] at hsum hcut
  obtain ⟨N₀, hN₀, hfl⟩ := floor_pow_ge F.natDegree hk cc
  have hkR : (1 : ℝ) ≤ (F.natDegree : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (F.natDegree : ℝ) := by linarith
  refine ⟨(M : ℝ) + 2, by positivity, ?_⟩
  intro ε hε
  have hA0 : (0 : ℝ) ≤ (c.divisors.card : ℝ) ^ 4 := by positivity
  refine ⟨4 * (c.divisors.card : ℝ) ^ 4 * C₀ * 2 ^ M + 4, N₀, ?_, hN₀, ?_⟩
  · have : (0 : ℝ) ≤ 4 * (c.divisors.card : ℝ) ^ 4 * C₀ * 2 ^ M := by positivity
    linarith
  intro N H hN hHl hHu
  have hN3 : (3 : ℝ) ≤ N := hN₀.trans hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_three
    linarith
  have h3k : (0 : ℝ) ≤ 1 / (3 * (F.natDegree : ℝ)) := by positivity
  have hy1 : (1 : ℝ) ≤ N ^ (1 / (3 * (F.natDegree : ℝ))) := Real.one_le_rpow hN1 h3k
  have hyH : N ^ (1 / (3 * (F.natDegree : ℝ))) ≤ H :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hHl
  have hH1 : (1 : ℝ) ≤ H := hy1.trans hyH
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hx0 : (0 : ℝ) ≤ N ^ (1 / (F.natDegree : ℝ)) := Real.rpow_nonneg hN0.le _
  have hxN : N ^ (1 / (F.natDegree : ℝ)) ≤ N := by
    have h1 : 1 / (F.natDegree : ℝ) ≤ 1 := by
      rw [div_le_one hkpos]
      exact hkR
    have h2 := Real.rpow_le_rpow_of_exponent_le hN1 h1
    rwa [Real.rpow_one] at h2
  have hD1 : 1 ≤ ⌊H⌋₊ := Nat.le_floor (by exact_mod_cast hH1)
  have hD1R : (1 : ℝ) ≤ (⌊H⌋₊ : ℝ) := by exact_mod_cast hD1
  have hDH : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le hH0
  have hDN : (⌊H⌋₊ : ℝ) ≤ N := hDH.trans (hHu.trans hxN)
  have hlogD0 : 0 ≤ Real.log (⌊H⌋₊ : ℝ) := Real.log_nonneg hD1R
  have hlogD : Real.log (⌊H⌋₊ : ℝ) ≤ Real.log N := Real.log_le_log (by linarith) hDN
  have hceil : ((⌈N ^ (1 / (F.natDegree : ℝ))⌉₊ : ℕ) : ℝ) < N ^ (1 / (F.natDegree : ℝ)) + 1 :=
    Nat.ceil_lt_add_one hx0
  -- name the endpoints
  obtain ⟨lo, hlo⟩ : ∃ lo : ℕ, lo = ⌈N ^ (1 / (F.natDegree : ℝ))⌉₊ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = ⌊H⌋₊ := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log N := ⟨_, rfl⟩
  have hsub := win_subset (N ^ (1 / (F.natDegree : ℝ))) H hx0 hH0
  have hflN := hfl N H hN hyH
  rw [← hlo] at hsub hceil ⊢
  rw [← hD] at hsub hD1 hD1R hDH hlogD0 hlogD hflN
  rw [← hLdef] at hL1 hlogD ⊢
  have hL0 : (0 : ℝ) ≤ L := by linarith
  -- cutoff
  have hb : ∀ n ∈ Finset.Icc lo (lo + D),
      G.eval (n : ℤ) ≤ (D : ℤ) ^ (4 * (F.natDegree * (F.natDegree + 1))) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnR : (n : ℝ) ≤ (lo : ℝ) + (D : ℝ) := by exact_mod_cast hn.2
    have hn' : (n : ℝ) ≤ N ^ (1 / (F.natDegree : ℝ)) + H + 1 := by linarith
    have h1 := hcut N H hN1 hH0 hHu n hn'
    have h2 : ((G.eval (n : ℤ) : ℤ) : ℝ) ≤
        ((((D : ℤ) ^ (4 * (F.natDegree * (F.natDegree + 1))) : ℤ)) : ℝ) := by
      push_cast
      exact h1.trans hflN
    exact Int.cast_le.mp h2
  have hS := hsum lo (lo + D) D hD1 hb
  rw [Nat.add_sub_cancel_left] at hS
  obtain ⟨SG, hSG⟩ : ∃ SG : ℝ, SG = ∑ n ∈ Finset.Icc lo (lo + D),
      (((G.eval (n : ℤ)).toNat.divisors.card : ℝ)) ^ 4 := ⟨_, rfl⟩
  rw [← hSG] at hS
  have hpowM : (1 + Real.log (D : ℝ)) ^ M ≤ 2 ^ M * L ^ M := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) M
  have hSG2 : SG ≤ C₀ * (2 * H) * (2 ^ M * L ^ M) := by
    refine hS.trans ?_
    apply mul_le_mul _ hpowM (pow_nonneg (by linarith) M) (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hC₀.le
  -- pointwise bound and summation
  have hterm : ∀ n ∈ Finset.Icc lo (lo + D),
      (((F.eval (n : ℤ)).toNat : ℝ) * (F.eval (n : ℤ)).toNat.divisors.card /
          (F.eval (n : ℤ)).toNat.totient + L) ^ 2 ≤
        2 * ((c.divisors.card : ℝ) ^ 4 * (((G.eval (n : ℤ)).toNat.divisors.card : ℝ)) ^ 4) +
          2 * L ^ 2 := by
    intro n _
    rw [hev (n : ℤ), toNat_natCast_mul_eq]
    exact term_le c _ L
  have hcard : ((Finset.Icc lo (lo + D)).card : ℝ) ≤ 2 * H := by
    rw [Nat.card_Icc]
    have h : lo + D + 1 - lo = D + 1 := by omega
    rw [h]
    push_cast
    linarith
  have hmain : ∑ n ∈ Finset.Icc lo ⌊N ^ (1 / (F.natDegree : ℝ)) + H⌋₊,
      (((F.eval (n : ℤ)).toNat : ℝ) * (F.eval (n : ℤ)).toNat.divisors.card /
          (F.eval (n : ℤ)).toNat.totient + L) ^ 2 ≤
      2 * (c.divisors.card : ℝ) ^ 4 * SG + (2 * H) * (2 * L ^ 2) := by
    calc _ ≤ ∑ n ∈ Finset.Icc lo (lo + D),
          (((F.eval (n : ℤ)).toNat : ℝ) * (F.eval (n : ℤ)).toNat.divisors.card /
            (F.eval (n : ℤ)).toNat.totient + L) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg _)
      _ ≤ ∑ n ∈ Finset.Icc lo (lo + D),
          (2 * ((c.divisors.card : ℝ) ^ 4 *
            (((G.eval (n : ℤ)).toNat.divisors.card : ℝ)) ^ 4) + 2 * L ^ 2) :=
          Finset.sum_le_sum hterm
      _ = 2 * (c.divisors.card : ℝ) ^ 4 * SG +
            ((Finset.Icc lo (lo + D)).card : ℝ) * (2 * L ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hSG,
            Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ 2 * (c.divisors.card : ℝ) ^ 4 * SG + (2 * H) * (2 * L ^ 2) := by
          have : (0 : ℝ) ≤ 2 * L ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_right hcard this
          linarith
  have hrpow : L ^ ((M : ℝ) + 2) = L ^ (M + 2) := by
    have : ((M : ℝ) + 2) = ((M + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
  rw [hrpow]
  have hP1 : L ^ M ≤ L ^ (M + 2) := pow_le_pow_right₀ hL1 (by omega)
  have hP2 : L ^ 2 ≤ L ^ (M + 2) := pow_le_pow_right₀ hL1 (by omega)
  have hc1 : (0 : ℝ) ≤ 4 * (c.divisors.card : ℝ) ^ 4 * C₀ * 2 ^ M * H := by positivity
  have hc2 : (0 : ℝ) ≤ 4 * H := by linarith
  have hq1 := mul_le_mul_of_nonneg_left hP1 hc1
  have hq2 := mul_le_mul_of_nonneg_left hP2 hc2
  have hq0 : 2 * (c.divisors.card : ℝ) ^ 4 * SG ≤
      2 * (c.divisors.card : ℝ) ^ 4 * (C₀ * (2 * H) * (2 ^ M * L ^ M)) :=
    mul_le_mul_of_nonneg_left hSG2 (by positivity)
  calc _ ≤ 2 * (c.divisors.card : ℝ) ^ 4 * SG + (2 * H) * (2 * L ^ 2) := hmain
    _ ≤ 2 * (c.divisors.card : ℝ) ^ 4 * (C₀ * (2 * H) * (2 ^ M * L ^ M)) +
          (2 * H) * (2 * L ^ 2) := by linarith
    _ = 4 * (c.divisors.card : ℝ) ^ 4 * C₀ * 2 ^ M * H * L ^ M + 4 * H * L ^ 2 := by ring
    _ ≤ 4 * (c.divisors.card : ℝ) ^ 4 * C₀ * 2 ^ M * H * L ^ (M + 2) +
          4 * H * L ^ (M + 2) := by linarith
    _ = (4 * (c.divisors.card : ℝ) ^ 4 * C₀ * 2 ^ M + 4) * H * L ^ (M + 2) := by ring

end LeanLab.Perelli1996.Nair103
