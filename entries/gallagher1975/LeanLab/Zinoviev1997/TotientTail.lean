module

public import Mathlib

/-!
AI wrote this Lean code. Codex task69, 2026-10-25.
Elementary support for the reciprocal totient square tail on page 356.
The seventh power inequality below is a supporting estimate.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology
set_option maxRecDepth 4096

/-- Correct the three small prime factors in the totient estimate. -/
def phiWeight (p n : ℕ) : ℕ := if p ∣ n then (p - 1) ^ 8 else p ^ 7

theorem phiWeight_mul {p a b : ℕ} (hp : p.Prime) (hab : Nat.Coprime a b) :
    phiWeight p (a * b) * p ^ 7 = phiWeight p a * phiWeight p b := by
  unfold phiWeight
  by_cases ha : p ∣ a <;> by_cases hb : p ∣ b
  · have : p ∣ Nat.gcd a b := Nat.dvd_gcd ha hb
    rw [hab] at this
    exact False.elim (hp.not_dvd_one this)
  · simp [ha, hb, Dvd.dvd.mul_right ha]
  · simp [ha, hb, Dvd.dvd.mul_left hb, mul_comm]
  · have hh : ¬ p ∣ a * b := fun h => (hp.dvd_mul.mp h).elim ha hb
    simp [ha, hb, hh]

theorem phiWeight_prime_pow {r p : ℕ} (hr : r.Prime) (hp : p.Prime) {k : ℕ}
    (hk : 0 < k) : phiWeight r (p ^ k) = if p = r then (r - 1) ^ 8 else r ^ 7 := by
  have h : r ∣ p ^ k ↔ p = r := by
    constructor
    · intro hd
      exact ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hd)).symm
    · rintro rfl
      exact dvd_pow_self p hk.ne'
  simp only [phiWeight, h]

/-- Weighted multiplicative form of the seventh power bound. -/
def TotientGood (q : ℕ) : Prop :=
  q ^ 7 * (phiWeight 2 q * phiWeight 3 q * phiWeight 5 q) ≤
    (2 ^ 7 * 3 ^ 7 * 5 ^ 7) * Nat.totient q ^ 8

theorem totientGood_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    TotientGood (p ^ k) := by
  unfold TotientGood
  rw [Nat.totient_prime_pow hp hk, phiWeight_prime_pow Nat.prime_two hp hk,
    phiWeight_prime_pow Nat.prime_three hp hk,
    phiWeight_prime_pow (by norm_num : Nat.Prime 5) hp hk]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hpow : p ^ (7 * j) ≤ p ^ (8 * j) := Nat.pow_le_pow_right hp.pos (by omega)
  have he1 : (p ^ (j + 1)) ^ 7 = p ^ 7 * p ^ (7 * j) := by ring
  have he2 : (p ^ j * (p - 1)) ^ 8 = (p - 1) ^ 8 * p ^ (8 * j) := by ring
  rw [he1, he2]
  by_cases h7 : 7 ≤ p
  · have hp7 : p ^ 7 ≤ (p - 1) ^ 8 := by
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 7 := ⟨p - 7, by omega⟩
      rw [show m + 7 - 1 = m + 6 by omega]
      ring_nf
      omega
    simp only [show p ≠ 2 by omega, show p ≠ 3 by omega, show p ≠ 5 by omega,
      ite_false]
    have hh := Nat.mul_le_mul hp7 hpow
    nlinarith
  · interval_cases p <;> norm_num at hp <;> norm_num <;> nlinarith

theorem totientGood_mul {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : TotientGood a) (hb : TotientGood b) : TotientGood (a * b) := by
  unfold TotientGood at *
  rw [Nat.totient_mul hab]
  have h2 := phiWeight_mul Nat.prime_two hab
  have h3 := phiWeight_mul Nat.prime_three hab
  have h5 := phiWeight_mul (by norm_num : Nat.Prime 5) hab
  have hh : (a * b) ^ 7 * (phiWeight 2 (a * b) * phiWeight 3 (a * b) *
      phiWeight 5 (a * b)) * (2 ^ 7 * 3 ^ 7 * 5 ^ 7) ≤
      ((2 ^ 7 * 3 ^ 7 * 5 ^ 7) * (Nat.totient a * Nat.totient b) ^ 8) *
        (2 ^ 7 * 3 ^ 7 * 5 ^ 7) := by
    calc
      _ = (a ^ 7 * (phiWeight 2 a * phiWeight 3 a * phiWeight 5 a)) *
          (b ^ 7 * (phiWeight 2 b * phiWeight 3 b * phiWeight 5 b)) := by
        rw [show (a * b) ^ 7 * (phiWeight 2 (a * b) * phiWeight 3 (a * b) *
            phiWeight 5 (a * b)) * (2 ^ 7 * 3 ^ 7 * 5 ^ 7) =
          (a * b) ^ 7 * ((phiWeight 2 (a * b) * 2 ^ 7) *
            (phiWeight 3 (a * b) * 3 ^ 7) * (phiWeight 5 (a * b) * 5 ^ 7)) by ring,
          h2, h3, h5]
        ring
      _ ≤ ((2 ^ 7 * 3 ^ 7 * 5 ^ 7) * Nat.totient a ^ 8) *
          ((2 ^ 7 * 3 ^ 7 * 5 ^ 7) * Nat.totient b ^ 8) := Nat.mul_le_mul ha hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hh (by norm_num)

theorem totientGood_all : ∀ q : ℕ, 0 < q → TotientGood q := by
  intro q
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn => intro _; exact totientGood_prime_pow p n hp hn
  | zero => intro h; omega
  | one => intro _; norm_num [TotientGood, phiWeight]
  | coprime a b ha hb hab iha ihb =>
    intro _
    exact totientGood_mul hab (iha (by omega)) (ihb (by omega))

/-- A uniform elementary totient bound with exponent seven eighths. -/
theorem seventh_le_totient_eighth (q : ℕ) (hq : 0 < q) :
    q ^ 7 ≤ 2401 * Nat.totient q ^ 8 := by
  have h := totientGood_all q hq
  unfold TotientGood at h
  have hw : 16777216 ≤ phiWeight 2 q * phiWeight 3 q * phiWeight 5 q := by
    unfold phiWeight
    split_ifs <;> norm_num
  have hh := (Nat.mul_le_mul_left (q ^ 7) hw).trans h
  omega

/-- The reciprocal square form of the seventh power inequality. -/
theorem inv_totient_sq_seven (q : ℕ) (hq : 0 < q) :
    1 / (Nat.totient q : ℝ) ^ 2 ≤ 7 * (q : ℝ) ^ (-(7 : ℝ) / 4) := by
  have h := seventh_le_totient_eighth q hq
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hphi : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hc : (q : ℝ) ^ 7 ≤ 2401 * (Nat.totient q : ℝ) ^ 8 := by exact_mod_cast h
  have he : ((q : ℝ) ^ ((7 : ℝ) / 4)) ^ 4 = (q : ℝ) ^ 7 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqr.le]
    norm_num
  have hr : (q : ℝ) ^ ((7 : ℝ) / 4) ≤ 7 * (Nat.totient q : ℝ) ^ 2 := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [he]
    nlinarith [hc]
  rw [show (-(7 : ℝ) / 4) = -((7 : ℝ) / 4) by ring, Real.rpow_neg hqr.le]
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul] using hr

/-- A finite integral comparison for the power tail. -/
theorem powerTail_Ioc (Q M : ℕ) (hQ : 0 < Q) (hQM : Q ≤ M) :
    ∑ q ∈ Finset.Ioc Q M, (q : ℝ) ^ (-(7 : ℝ) / 4) ≤
      (4 / 3 : ℝ) * (Q : ℝ) ^ (-(3 : ℝ) / 4) := by
  have hs : (∑ q ∈ Finset.Ioc Q M, (q : ℝ) ^ (-(7 : ℝ) / 4)) =
      ∑ i ∈ Finset.Ico Q M, ((i + 1 : ℕ) : ℝ) ^ (-(7 : ℝ) / 4) := by
    symm
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      simp only [Finset.mem_Ico, Finset.mem_Ioc] at hi ⊢
      omega
    · intro i _ j _ hij
      omega
    · intro q hq
      simp only [Finset.mem_Ioc] at hq
      refine ⟨q - 1, ?_, by omega⟩
      simp only [Finset.mem_Ico]
      omega
    · intro i hi
      rfl
  rw [hs]
  have hqr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hmr : (0 : ℝ) < M := lt_of_lt_of_le hqr (by exact_mod_cast hQM)
  have ha : AntitoneOn (fun x : ℝ => x ^ (-(7 : ℝ) / 4)) (Set.Icc (Q : ℝ) M) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hqr hx.1) hxy (by norm_num)
  have hh := ha.sum_le_integral_Ico hQM
  have hi : (∫ x in (Q : ℝ)..M, x ^ (-(7 : ℝ) / 4)) =
      (4 / 3 : ℝ) * ((Q : ℝ) ^ (-(3 : ℝ) / 4) - (M : ℝ) ^ (-(3 : ℝ) / 4)) := by
    rw [integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
    · norm_num
      ring
    · rw [Set.uIcc_of_le (by exact_mod_cast hQM)]
      intro h
      have := h.1
      linarith
  rw [hi] at hh
  have hn := Real.rpow_nonneg hmr.le (-(3 : ℝ) / 4)
  linarith

/-- The reciprocal totient square tail needed in display 3.15, for every finite cutoff. -/
theorem totientTail_Ioc_bound (Q M : ℕ) (hQ : 2200 ≤ Q) :
    ∑ q ∈ Finset.Ioc Q M, (1 / (Nat.totient q : ℝ) ^ 2) ≤ 7 / 240 := by
  rcases le_or_gt Q M with hQM | hQM
  · have hq0 : 0 < Q := by omega
    have hh : (∑ q ∈ Finset.Ioc Q M, (1 / (Nat.totient q : ℝ) ^ 2)) ≤
        7 * ((4 / 3 : ℝ) * (Q : ℝ) ^ (-(3 : ℝ) / 4)) := by
      calc
        _ ≤ ∑ q ∈ Finset.Ioc Q M, 7 * (q : ℝ) ^ (-(7 : ℝ) / 4) := by
          apply Finset.sum_le_sum
          intro q hq
          exact inv_totient_sq_seven q (by have := (Finset.mem_Ioc.mp hq).1; omega)
        _ = 7 * ∑ q ∈ Finset.Ioc Q M, (q : ℝ) ^ (-(7 : ℝ) / 4) := by
          rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (powerTail_Ioc Q M hq0 hQM) (by norm_num)
    have hqr : (0 : ℝ) < Q := by exact_mod_cast hq0
    have hpow : (320 : ℝ) ≤ (Q : ℝ) ^ ((3 : ℝ) / 4) := by
      apply (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp
      rw [← Real.rpow_natCast ((Q : ℝ) ^ ((3 : ℝ) / 4)), ← Real.rpow_mul hqr.le]
      norm_num
      have hqr' : (2200 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2200) hqr' 3
      norm_num at hcube ⊢
      linarith
    have hn : (Q : ℝ) ^ (-(3 : ℝ) / 4) ≤ 1 / 320 := by
      rw [show (-(3 : ℝ) / 4) = -((3 : ℝ) / 4) by ring, Real.rpow_neg hqr.le]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 320) hpow
    have he := mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 7 * (4 / 3))
    nlinarith
  · rw [Finset.Ioc_eq_empty (by omega : ¬ Q < M), Finset.sum_empty]
    norm_num

/-- The decimal bound also holds with the smaller cutoff 2200. -/
theorem totientTail_Ioc_2200 (Q M : ℕ) (hQ : 2200 ≤ Q) :
    ∑ q ∈ Finset.Ioc Q M, (1 / (Nat.totient q : ℝ) ^ 2) < 0.03 :=
  lt_of_le_of_lt (totientTail_Ioc_bound Q M hQ) (by norm_num)

/-- The printed tail cutoff is covered by the stronger uniform estimate. -/
theorem totientTail_Ioc (Q M : ℕ) (hQ : 2330 ≤ Q) :
    ∑ q ∈ Finset.Ioc Q M, (1 / (Nat.totient q : ℝ) ^ 2) < 0.03 :=
  totientTail_Ioc_2200 Q M (by omega)

end LeanLab.Zinoviev1997
