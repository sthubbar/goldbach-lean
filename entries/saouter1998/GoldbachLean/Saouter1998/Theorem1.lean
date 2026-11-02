module

public import Mathlib
public import GoldbachLean.Saouter1998.Theorem2

/-!
# Saouter 1998, Theorem 1

Theorem 1 on page 864, with an arbitrary modular base, by the prime factor and discriminant argument
of `Theorem2.lean`, which specialises it to base 5.
AI wrote the Lean code: Claude by Anthropic for most files, Codex for Theorem 1 and the statement of Lemma 1, Gemini and Antigravity agents for parts of the Lemma 1 proof; it is checked only by the Lean kernel. Ternary Goldbach is
Helfgott's theorem, binary Goldbach is open.
-/

@[expose] public section

namespace GoldbachLean.Saouter1998.Thm1

open GoldbachLean.Saouter1998.Thm2

/-- The modular test forces every prime factor to have the required form. -/
theorem factor_form {p R a : ℕ} (hp : p.Prime) (hpN : p ∣ 2 ^ 22 * R + 1)
    (ha : (a : ZMod (2 ^ 22 * R + 1)) ^ (2 ^ 22 * R / 2) = -1) :
    ∃ j, 3 ≤ j ∧ p = 2 ^ 22 * j + 1 := by
  have hp2 : p ≠ 2 := by
    intro h2
    have h2N : 2 ∣ 2 ^ 22 * R + 1 := h2 ▸ hpN
    have h2X : 2 ∣ 2 ^ 22 * R := Dvd.dvd.mul_right (dvd_pow_self 2 (by norm_num)) R
    have h21 := (Nat.dvd_add_right h2X).mp h2N
    norm_num at h21
  rw [half_eq] at ha
  obtain ⟨j, hj⟩ := two_pow_dvd (m := 21) hp hpN hp2 (by exact_mod_cast ha)
  have hp1 := hp.two_le
  have hpj : p = 2 ^ 22 * j + 1 := by norm_num at hj ⊢; omega
  refine ⟨j, ?_, hpj⟩
  by_contra hlt
  interval_cases j
  · norm_num at hpj; omega
  · norm_num at hpj; subst hpj; norm_num at hp
  · norm_num at hpj; subst hpj; norm_num at hp

/-- The sufficient condition under the wider size bound of Lemma 1. -/
theorem theorem1_if (R base : ℕ) (hR : R % 2 = 1) (hlt : 2 ^ 22 * R + 1 < 2 * (2 ^ 22) ^ 3)
    (ha : (base : ZMod (2 ^ 22 * R + 1)) ^ (2 ^ 22 * R / 2) = -1)
    (hc : R / (2 * 2 ^ 22) = 0 ∨
      ¬ IsSquare ((R % (2 * 2 ^ 22) : ℤ) ^ 2 - 8 * (R / (2 * 2 ^ 22) : ℤ))) :
    (2 ^ 22 * R + 1).Prime := by
  by_contra hNp
  obtain ⟨N, hN⟩ : ∃ N, N = 2 ^ 22 * R + 1 := ⟨_, rfl⟩
  rw [← hN] at hNp hlt
  have hR1 : 1 ≤ R := by omega
  have hN2 : 2 ≤ N := by have := Nat.mul_le_mul_left (2 ^ 22) hR1; omega
  have hpp : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hmin : ∀ q, q.Prime → q ∣ N → N.minFac ≤ q :=
    fun q hq hqN => Nat.minFac_le_of_dvd hq.two_le hqN
  have hpd : N.minFac ∣ N := Nat.minFac_dvd N
  generalize N.minFac = p at hpp hmin hpd
  obtain ⟨a, ha3, hpa⟩ := factor_form hpp (hN ▸ hpd) ha
  obtain ⟨M, hM⟩ := hpd
  have hM1 : M ≠ 1 := by
    intro h1; rw [h1, mul_one] at hM; exact hNp (hM ▸ hpp)
  have hM0 : M ≠ 0 := by intro h0; rw [h0, mul_zero] at hM; omega
  have hpbig : 12582913 ≤ p := by rw [hpa]; norm_num; omega
  -- M is prime, else N ≥ p^3 > 2 F^3
  have hMp : M.Prime := by
    by_contra hMnp
    have hqp : M.minFac.Prime := Nat.minFac_prime hM1
    have hqN : M.minFac ∣ N := hM ▸ Dvd.dvd.mul_left (Nat.minFac_dvd M) p
    have hpq : p ≤ M.minFac := hmin _ hqp hqN
    have hq2 : M.minFac ^ 2 ≤ M := by
      simpa [sq] using Nat.minFac_sq_le_self (by omega : 0 < M) hMnp
    have h3 : p * (p * p) ≤ N := by
      rw [hM]
      apply Nat.mul_le_mul_left
      calc p * p ≤ M.minFac * M.minFac := Nat.mul_le_mul hpq hpq
        _ = M.minFac ^ 2 := by ring
        _ ≤ M := hq2
    have : (12582913 : ℕ) * (12582913 * 12582913) ≤ p * (p * p) :=
      Nat.mul_le_mul hpbig (Nat.mul_le_mul hpbig hpbig)
    norm_num at hlt this
    omega
  obtain ⟨b, hb3, hMb⟩ := factor_form hMp (hN ▸ ⟨p, by rw [hM, mul_comm]⟩) ha
  -- R = F a b + a + b
  have hReq : R = 2 ^ 22 * (a * b) + (a + b) := by
    have h : 2 ^ 22 * R + 1 = (2 ^ 22 * a + 1) * (2 ^ 22 * b + 1) := by
      rw [← hpa, ← hMb, ← hN]; exact hM
    have h' : 2 ^ 22 * R = 2 ^ 22 * (2 ^ 22 * (a * b) + (a + b)) := by
      have := h; ring_nf at this ⊢; omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'
  -- a b is even, since R is odd
  have hEven : Even (a * b) := by
    have hodd : Odd (a + b) := by
      have hRo : Odd R := Nat.odd_iff.mpr hR
      rw [hReq] at hRo
      have hE : Even (2 ^ 22 * (a * b)) := ⟨2 ^ 21 * (a * b), by ring⟩
      rcases Nat.even_or_odd (a + b) with h1 | h1
      · exact absurd (hE.add h1) (Nat.not_even_iff_odd.mpr hRo)
      · exact h1
    rcases Nat.even_or_odd a with h1 | h1
    · exact h1.mul_right b
    · have : Even b := by
        rcases Nat.even_or_odd b with h2 | h2
        · exact h2
        · exact absurd (h1.add_odd h2) (Nat.not_even_iff_odd.mpr hodd)
      exact this.mul_left a
  obtain ⟨s, hs⟩ := hEven
  have hab2 : a * b = 2 * s := by omega
  -- size: a b < 2 F, so a + b < 2 F
  have habF : a * b < 2 * 2 ^ 22 := by
    have h1 : 2 ^ 22 * (2 ^ 22 * (a * b)) < 2 * (2 ^ 22) ^ 3 := by
      have : 2 ^ 22 * (2 ^ 22 * (a * b)) ≤ 2 ^ 22 * R := by
        rw [hReq]; apply Nat.mul_le_mul_left; omega
      omega
    by_contra hge
    have hge' : 2 * 2 ^ 22 ≤ a * b := by omega
    have : 2 ^ 22 * (2 ^ 22 * (2 * 2 ^ 22)) ≤ 2 ^ 22 * (2 ^ 22 * (a * b)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hge')
    norm_num at this h1; omega
  have hsum : a + b < 2 * 2 ^ 22 := by
    have := key3 ha3 hb3
    omega
  have hdiv : R / (2 * 2 ^ 22) = s := by
    have hF : (2 : ℕ) ^ 22 = 4194304 := by norm_num
    rw [hReq, hab2]; rw [hF] at hsum ⊢; omega
  have hmod : R % (2 * 2 ^ 22) = a + b := by
    have hF : (2 : ℕ) ^ 22 = 4194304 := by norm_num
    rw [hReq, hab2]; rw [hF] at hsum ⊢; omega
  have hdivZ : (R : ℤ) / (2 * 2 ^ 22) = (s : ℤ) := by
    have := congrArg (Nat.cast : ℕ → ℤ) hdiv; push_cast at this; exact this
  have hmodZ : (R : ℤ) % (2 * 2 ^ 22) = (a : ℤ) + b := by
    have := congrArg (Nat.cast : ℕ → ℤ) hmod; push_cast at this; exact this
  rcases hc with h0 | hns
  · rw [hdiv] at h0
    have : 9 ≤ a * b := Nat.mul_le_mul ha3 hb3
    omega
  · apply hns
    rw [hdivZ, hmodZ]
    have := isSquare_sub hab2
    push_cast at this
    exact this

/-- Theorem 1 on page 864, with an arbitrary modular base. -/
theorem theorem1 (R a : ℕ) (hR : R % 2 = 1) (hlt : 2 ^ 22 * R + 1 < 10 ^ 20)
    (ha : (a : ZMod (2 ^ 22 * R + 1)) ^ (2 ^ 22 * R / 2) = -1) :
    (2 ^ 22 * R + 1).Prime ↔
      (R / (2 * 2 ^ 22) = 0 ∨
        ¬ IsSquare ((R % (2 * 2 ^ 22) : ℤ) ^ 2 - 8 * (R / (2 * 2 ^ 22) : ℤ))) := by
  exact ⟨theorem2_only_if R, theorem1_if R a hR
    (lt_trans hlt GoldbachLean.Saouter1998.Paper.cube_bound) ha⟩

/-- Theorem 1 for an integer base, as in the paper. -/
theorem theorem1_int (R : ℕ) (a : ℤ) (hR : R % 2 = 1)
    (hlt : 2 ^ 22 * R + 1 < 10 ^ 20)
    (ha : (a : ZMod (2 ^ 22 * R + 1)) ^ (2 ^ 22 * R / 2) = -1) :
    (2 ^ 22 * R + 1).Prime ↔
      (R / (2 * 2 ^ 22) = 0 ∨
        ¬ IsSquare ((R % (2 * 2 ^ 22) : ℤ) ^ 2 - 8 * (R / (2 * 2 ^ 22) : ℤ))) := by
  haveI : NeZero (2 ^ 22 * R + 1) := ⟨by omega⟩
  apply theorem1 R (a : ZMod (2 ^ 22 * R + 1)).val hR hlt
  simpa only [ZMod.natCast_zmod_val] using ha

end GoldbachLean.Saouter1998.Thm1
