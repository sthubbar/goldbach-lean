module

public import Mathlib
public import GoldbachLean.Saouter1998.Lemma1

/-!
# Saouter 1998, Lemma 1, the proof

A proof of Lemma 1 of the paper for every even `F`: Pocklington's order argument puts every prime
factor of `N` in the class `1 mod F`, the size bound `N < 2 F^3` leaves two factors `aF + 1` and
`bF + 1`, and the quadratic with roots `a` and `b` gives the discriminant `r^2 - 8 s`.
AI wrote the Lean code: Claude by Anthropic for most files, Codex for Theorem 1 and the statement of Lemma 1, Gemini and Antigravity agents for parts of the Lemma 1 proof; it is checked only by the Lean kernel. Ternary Goldbach is
Helfgott's theorem, binary Goldbach is open.
-/

@[expose] public section

namespace GoldbachLean.Saouter1998.BLS

/-- The case `F = 0` is excluded by `N < 2 F^3`. -/
theorem leaf_F_zero (R : ℕ) (hN_lt : R * 0 + 1 < 2 * 0 ^ 3) :
    ((R * 0 + 1).Prime ↔
      R / (2 * 0) = 0 ∨ ¬ IsSquare (((R % (2 * 0) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * 0) : ℕ) : ℤ))) := by
  exfalso
  simp at hN_lt
/-- The Fermat and gcd conditions imply that every prime factor is `1 mod F`. -/
theorem leaf_pock (F R : ℕ) (a : ℤ) (hOdd : Odd (R * F + 1)) (hF : Even F) (hCoprime : Nat.Coprime R F)
    (hFermat : (a : ZMod (R * F + 1)) ^ (R * F) = 1)
    (hgcd : ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ (R * F / p) - 1) (R * F + 1) = 1) :
    ∀ p : ℕ, p.Prime → p ∣ R * F + 1 → ∃ k : ℕ, p = k * F + 1 := by
  intro p hp hpN
  have : Fact p.Prime := ⟨hp⟩
  set c : ZMod p := (a : ZMod p) ^ R with hc
  have hpow : c ^ F = 1 := by
    have h := congrArg (ZMod.castHom hpN (ZMod p)) hFermat
    simp only [map_pow, map_intCast, map_one] at h
    rw [hc, ← pow_mul]; exact h
  have hd : ∀ q : ℕ, q.Prime → q ∣ F → c ^ (F / q) ≠ 1 := by
    intro q hq hqF hcq
    have hdiv : R * (F / q) = R * F / q := (Nat.mul_div_assoc R hqF).symm
    have h1 : (a : ZMod p) ^ (R * F / q) = 1 := by
      rw [← hdiv, pow_mul, ← hc]; exact hcq
    have h2 : ((a ^ (R * F / q) - 1 : ℤ) : ZMod p) = 0 := by
      push_cast; rw [h1, sub_self]
    have hp_dvd_a : (p : ℤ) ∣ a ^ (R * F / q) - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h2
    have hp_dvd_N : (p : ℤ) ∣ (R * F + 1 : ℕ) := Int.natCast_dvd_natCast.mpr hpN
    have hp_dvd_gcd : (p : ℤ) ∣ (Int.gcd (a ^ (R * F / q) - 1) (R * F + 1) : ℤ) :=
      Int.dvd_coe_gcd hp_dvd_a hp_dvd_N
    have h_gcd_one := hgcd q hq hqF
    rw [h_gcd_one, Nat.cast_one] at hp_dvd_gcd
    have hp_dvd_one : p ∣ 1 := Int.natCast_dvd_natCast.mp hp_dvd_gcd
    exact Nat.Prime.not_dvd_one hp hp_dvd_one
  have hF0 : F ≠ 0 := by
    intro hF0; subst hF0
    have := hd 2 Nat.prime_two (dvd_zero 2)
    simp at this
  have hF_pos : 0 < F := Nat.pos_of_ne_zero hF0
  have hord : orderOf c = F := orderOf_eq_of_pow_and_pow_div_prime hF_pos hpow hd
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow hF0] at hpow
    exact zero_ne_one hpow
  have hF_dvd : F ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hc0
  have hp1 : 1 ≤ p := hp.one_le
  obtain ⟨k, hk⟩ := hF_dvd
  refine ⟨k, ?_⟩
  rw [mul_comm]
  omega

/-- If `N` is prime, the condition of Lemma 1 holds. -/
theorem leaf_prime_cond (F R : ℕ) (hF : 0 < F) (hN : (R * F + 1).Prime) :
    R / (2 * F) = 0 ∨ ¬ IsSquare (((R % (2 * F) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * F) : ℕ) : ℤ)) := by
  by_contra hcon
  rw [not_or, not_not] at hcon
  obtain ⟨hs0, t, ht⟩ := hcon
  obtain ⟨s, hs⟩ : ∃ s, s = R / (2 * F) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = R % (2 * F) := ⟨_, rfl⟩
  rw [← hs, ← hr] at ht
  rw [← hs] at hs0
  have hRsr : R = 2 * F * s + r := by rw [hs, hr]; exact (Nat.div_add_mod R (2 * F)).symm
  obtain ⟨u, hu⟩ : ∃ u, u = t.natAbs := ⟨_, rfl⟩
  have hut : ((u * u : ℕ) : ℤ) = t * t := by
    rw [hu]; push_cast; exact abs_mul_abs_self t
  have hru : r * r = u * u + 8 * s := by
    have : ((r * r : ℕ) : ℤ) = ((u * u + 8 * s : ℕ) : ℤ) := by
      push_cast at hut ⊢; rw [hut, ← ht]; ring
    exact_mod_cast this
  have hulr : u < r := by
    by_contra hge
    have hge' : r ≤ u := by omega
    have : r * r ≤ u * u := Nat.mul_le_mul hge' hge'
    omega
  have hpar : (r + u) % 2 = 0 := by
    have h1 : Even (r * r) ↔ Even (u * u) := by
      rw [hru, Nat.even_add]; simp [show Even (8 * s) from ⟨4 * s, by ring⟩]
    rw [Nat.even_mul, Nat.even_mul, or_self, or_self] at h1
    rcases Nat.even_or_odd r with h2 | h2
    · have := h1.mp h2
      obtain ⟨x, hx⟩ := h2; obtain ⟨y, hy⟩ := this; omega
    · have hu' : ¬ Even u := fun h => (Nat.not_even_iff_odd.mpr h2) (h1.mpr h)
      rw [Nat.not_even_iff_odd] at hu'
      obtain ⟨x, hx⟩ := h2; obtain ⟨y, hy⟩ := hu'; omega
  obtain ⟨a, ha⟩ : ∃ a, 2 * a = r + u := ⟨(r + u) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, 2 * b = r - u := ⟨(r - u) / 2, by omega⟩
  have hab : a * b = 2 * s := by
    have h4 : (2 * a) * (2 * b) = 8 * s := by
      rw [ha, hb]
      zify [hulr.le] at hru ⊢
      linear_combination hru
    have h4' : 4 * (a * b) = 4 * (2 * s) := by
      calc 4 * (a * b) = (2 * a) * (2 * b) := by ring
        _ = 8 * s := h4
        _ = 4 * (2 * s) := by ring
    omega
  have hsum : a + b = r := by omega
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, mul_zero] at hab; omega
    · exact h
  have ha1 : 1 ≤ a := by omega
  have hfac : R * F + 1 = (a * F + 1) * (b * F + 1) := by
    rw [hRsr, ← hsum]
    have : (a * F + 1) * (b * F + 1) =
        F * (F * (a * b)) + F * (a + b) + 1 := by ring
    rw [this, hab]; ring
  rw [hfac] at hN
  have h1 : a * F + 1 ≠ 1 := by have := Nat.mul_le_mul ha1 hF; omega
  have h2 : b * F + 1 ≠ 1 := by have := Nat.mul_le_mul hb1 hF; omega
  exact Nat.not_prime_mul h1 h2 hN


lemma eq_of_mod_factors (F n : ℕ) (hF : 0 < F) (h_mod : n % F = 1) :
    ∃ c, n = c * F + 1 := by
  have h1 : n = F * (n / F) + n % F := (Nat.div_add_mod n F).symm
  rw [h_mod] at h1
  use n / F
  rw [mul_comm, ← h1]

lemma prod_prime_factors_mod (F : ℕ) (hF : 1 < F) (n : ℕ) (hn : 0 < n)
    (h_prime_factors : ∀ p, p.Prime → p ∣ n → p % F = 1) :
    n % F = 1 := by
  induction' n using Nat.strongRecOn with n ih
  by_cases hn1 : n = 1
  · rw [hn1]; exact Nat.mod_eq_of_lt hF
  by_cases hP : n.Prime
  · exact h_prime_factors n hP (dvd_rfl)
  · obtain ⟨a, b, ha_gt1, hb_gt1, hab⟩ : ∃ a b, 1 < a ∧ 1 < b ∧ n = a * b := by
      have hn_gt1 : 1 < n := by omega
      obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hn_gt1.ne'
      use p, n / p
      have hp_gt1 : 1 < p := hp.one_lt
      refine ⟨hp_gt1, ?_, ?_⟩
      · have hp_ne_n : p ≠ n := by
          rintro rfl
          exact hP hp
        have hdvd : p ∣ n := hp_dvd
        have : n / p > 1 := by
          have : n / p ≠ 1 := by
            intro h
            have h' := Nat.div_eq_iff_eq_mul_right hp_gt1.pos hdvd |>.mp h
            rw [h'] at hp_ne_n
            exact hp_ne_n (by omega)
          have : n / p > 0 := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp_gt1.pos
          omega
        exact this
      · exact (Nat.mul_div_cancel' hp_dvd).symm

    have h_a_lt : a < n := by rw [hab]; exact lt_mul_right (by omega) hb_gt1
    have h_b_lt : b < n := by rw [hab]; exact lt_mul_left (by omega) ha_gt1
    have ha_pos : 0 < a := by omega
    have hb_pos : 0 < b := by omega
    have h_a_mod := ih a h_a_lt ha_pos (fun p hp hp_dvd => h_prime_factors p hp (dvd_trans hp_dvd ⟨b, hab⟩))
    have h_b_mod := ih b h_b_lt hb_pos (fun p hp hp_dvd => h_prime_factors p hp (dvd_trans hp_dvd ⟨a, by rw [mul_comm]; exact hab⟩))
    rw [hab, Nat.mul_mod, h_a_mod, h_b_mod, mul_one]
    exact Nat.mod_eq_of_lt hF

lemma eq_comp_factors (F n : ℕ) (hF : 1 < F) (hn_gt1 : 1 < n)
    (h_prime_factors : ∀ p, p.Prime → p ∣ n → p % F = 1)
    (hP : ¬n.Prime) :
    ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ n = (a * F + 1) * (b * F + 1) := by
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hn_gt1.ne'
  have hdvd : p ∣ n := hp_dvd
  have h1 : p * (n / p) = n := Nat.mul_div_cancel' hdvd
  set q := n / p
  have hq_dvd : q ∣ n := by exact ⟨p, by rw [mul_comm, ← h1]⟩
  have hp_gt1 : 1 < p := hp.one_lt
  have hp_ne_n : p ≠ n := by
    rintro rfl
    exact hP hp
  have hq_gt1 : 1 < q := by
    have : q ≠ 1 := by
      intro h
      have h' := Nat.div_eq_iff_eq_mul_right hp_gt1.pos hp_dvd |>.mp h
      rw [h'] at hp_ne_n
      exact hp_ne_n (by omega)
    have : q > 0 := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp_gt1.pos
    omega
  have hp_mod : p % F = 1 := h_prime_factors p hp hp_dvd
  have hq_mod : q % F = 1 := by
    apply prod_prime_factors_mod F hF q (by omega)
    intro p' hp' hp'_dvd
    exact h_prime_factors p' hp' (dvd_trans hp'_dvd hq_dvd)
  obtain ⟨c_p, hc_p⟩ := eq_of_mod_factors F p (by omega) hp_mod
  obtain ⟨c_q, hc_q⟩ := eq_of_mod_factors F q (by omega) hq_mod
  use c_p, c_q
  have hc_p_ge1 : 1 ≤ c_p := by
    by_contra h_not
    have : c_p = 0 := by omega
    subst this
    rw [zero_mul, zero_add] at hc_p
    omega
  have hc_q_ge1 : 1 ≤ c_q := by
    by_contra h_not
    have : c_q = 0 := by omega
    subst this
    rw [zero_mul, zero_add] at hc_q
    omega
  refine ⟨hc_p_ge1, hc_q_ge1, ?_⟩
  rw [← hc_p, ← hc_q]
  exact h1.symm
/-- A composite `N` with all prime factors `1 mod F` is a product of two numbers `1 mod F`. -/
theorem leaf_comp_factors (F R : ℕ) (hF : 0 < F) (hR : 0 < R) (hN_lt : R * F + 1 < 2 * F ^ 3)
    (hpock : ∀ p : ℕ, p.Prime → p ∣ R * F + 1 → ∃ k : ℕ, p = k * F + 1)
    (hN : ¬ (R * F + 1).Prime) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ R * F + 1 = (a * F + 1) * (b * F + 1) := by
  have hN_gt1 : 1 < R * F + 1 := by
    have : 1 ≤ R * F := Nat.mul_pos hR hF
    omega
  have hF1 : 1 < F := by
    -- N < 2F^3 => F > 1. If F = 1, N < 2 => R*1 + 1 < 2 => R = 0, contradiction.
    by_contra h_not
    have hF_eq_1 : F = 1 := by omega
    subst hF_eq_1
    have : R + 1 < 2 := by omega
    omega
  have hpock_mod : ∀ p : ℕ, p.Prime → p ∣ R * F + 1 → p % F = 1 := by
    intro p hp hp_dvd
    obtain ⟨k, hk⟩ := hpock p hp hp_dvd
    rw [hk]
    have : k * F + 1 = F * k + 1 := by rw [mul_comm]
    rw [this, Nat.add_mod]
    simp
    have : 1 % F = 1 := Nat.mod_eq_of_lt hF1
    exact this
  obtain ⟨a_fac, b_fac, ha, hb, h_eq⟩ := eq_comp_factors F (R * F + 1) hF1 hN_gt1 hpock_mod hN
  use a_fac, b_fac

/-- The factorization gives `R` in terms of `a` and `b`. -/
theorem leaf_R_eq (F R a b : ℕ) (hF : 0 < F) (h : R * F + 1 = (a * F + 1) * (b * F + 1)) :
    R = a * b * F + a + b := by
  have h1 : R * F + 1 = (a * b * F + a + b) * F + 1 := by
    calc R * F + 1 = (a * F + 1) * (b * F + 1) := h
      _ = a * b * F * F + a * F + b * F + 1 := by ring
      _ = (a * b * F + a + b) * F + 1 := by ring
  exact Nat.eq_of_mul_eq_mul_right hF (Nat.add_right_cancel h1)

/-- If `N` factors in this way, the condition of Lemma 1 fails. -/
theorem leaf_comp_cond_from_factors (F R a b : ℕ) (hF : 0 < F)
    (hFe : Even F) (hCop : Nat.Coprime R F) (hN_lt : R * F + 1 < 2 * F ^ 3)
    (h_eq : R * F + 1 = (a * F + 1) * (b * F + 1)) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬ (R / (2 * F) = 0 ∨ ¬ IsSquare (((R % (2 * F) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * F) : ℕ) : ℤ))) := by
  have hR_eq := leaf_R_eq F R a b hF h_eq
  have hR_odd : Odd R := by
    by_contra h_even
    rw [Nat.not_odd_iff_even] at h_even
    have h1 : 2 ∣ R := even_iff_two_dvd.mp h_even
    have h2 : 2 ∣ F := even_iff_two_dvd.mp hFe
    have h3 : 2 ∣ Nat.gcd R F := Nat.dvd_gcd h1 h2
    rw [hCop] at h3
    omega
  have hab_even : Even (a * b) := by
    have h1 : Odd (a + b) := by
      have h2 : R % 2 = 1 := Nat.odd_iff.mp hR_odd
      have h3 : F % 2 = 0 := Nat.even_iff.mp hFe
      have h4 : R = a * b * F + (a + b) := by rw [hR_eq]; ring
      have h5 : R % 2 = (a * b * F + (a + b)) % 2 := by rw [h4]
      rw [Nat.add_mod, Nat.mul_mod, h3, mul_zero, Nat.zero_mod, zero_add, Nat.mod_mod] at h5
      exact Nat.odd_iff.mpr (by omega)
    have h2 : (a + b) % 2 = 1 := Nat.odd_iff.mp h1
    have h3 : (a * b) % 2 = 0 := by
      have h4 : (a + b) % 2 = (a % 2 + b % 2) % 2 := Nat.add_mod a b 2
      revert h2 h4
      generalize ha_mod : a % 2 = x
      generalize hb_mod : b % 2 = y
      intro h4 h2
      have hx : x < 2 := by rw [← ha_mod]; exact Nat.mod_lt a (by omega)
      have hy : y < 2 := by rw [← hb_mod]; exact Nat.mod_lt b (by omega)
      have : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by omega
      cases this with
      | inl h =>
        have h5 : a % 2 = 0 := by omega
        have h6 : 2 ∣ a := Nat.dvd_of_mod_eq_zero h5
        have h7 : 2 ∣ a * b := dvd_mul_of_dvd_left h6 b
        exact Nat.mod_eq_zero_of_dvd h7
      | inr h =>
        have h5 : b % 2 = 0 := by omega
        have h6 : 2 ∣ b := Nat.dvd_of_mod_eq_zero h5
        have h7 : 2 ∣ a * b := dvd_mul_of_dvd_right h6 a
        exact Nat.mod_eq_zero_of_dvd h7
    exact Nat.even_iff.mpr h3

  obtain ⟨s, hs⟩ := even_iff_two_dvd.mp hab_even
  have hR2 : R = 2 * F * s + (a + b) := by rw [hR_eq, hs]; ring
  have hab_lt : a * b < 2 * F := by
    have hF2 : 0 < F * F := Nat.mul_pos hF hF
    have : a * b * F * F + a * F + b * F + 1 < 2 * F * F * F := by
      calc a * b * F * F + a * F + b * F + 1 = (a * F + 1) * (b * F + 1) := by ring
        _ = R * F + 1 := h_eq.symm
        _ < 2 * F ^ 3 := hN_lt
        _ = 2 * F * F * F := by ring
    have h2 : a * b * (F * F) < 2 * F * (F * F) := by
      calc a * b * (F * F) = a * b * F * F := by ring
        _ ≤ a * b * F * F + a * F + b * F + 1 := by omega
        _ < 2 * F * F * F := this
        _ = 2 * F * (F * F) := by ring
    exact lt_of_mul_lt_mul_right h2 hF2.le

  have hapb_lt : a + b < 2 * F := by
    have h_ineq : a + b ≤ a * b + 1 := by
      obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      obtain ⟨b', hb'⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [ha', hb']
      have : (a' + 1) * (b' + 1) + 1 = a' * b' + a' + b' + 2 := by ring
      rw [this]
      omega
    have h2 : a * b + 1 ≤ 2 * F := by omega
    have h3 : a + b ≤ 2 * F := by omega
    have h4 : Even (2 * F) := Even.mul_right even_two F
    have h5 : Odd (a + b) := by
      have h2 : R % 2 = 1 := Nat.odd_iff.mp hR_odd
      have h3 : F % 2 = 0 := Nat.even_iff.mp hFe
      have h4 : R = a * b * F + (a + b) := by rw [hR_eq]; ring
      have h5 : R % 2 = (a * b * F + (a + b)) % 2 := by rw [h4]
      rw [Nat.add_mod, Nat.mul_mod, h3, mul_zero, Nat.zero_mod, zero_add, Nat.mod_mod] at h5
      exact Nat.odd_iff.mpr (by omega)
    have h6 : a + b ≠ 2 * F := by
      intro hc
      rw [hc] at h5
      have h7 : ¬ Odd (2 * F) := by intro h_odd; exact Nat.not_odd_iff_even.mpr h4 h_odd
      exact h7 h5
    omega

  have h_div : R / (2 * F) = s := by
    have : R = s * (2 * F) + (a + b) := by rw [hR2]; ring
    have h0 : R / (2 * F) = (s * (2 * F) + (a + b)) / (2 * F) := by rw [this]
    rw [h0]
    have h_div_add : (s * (2 * F) + (a + b)) / (2 * F) = s + (a + b) / (2 * F) := by
      have h2F : 0 < 2 * F := by omega
      have : (s * (2 * F) + (a + b)) / (2 * F) = ((a + b) + s * (2 * F)) / (2 * F) := by rw [add_comm]
      rw [this]
      have : ((a + b) + s * (2 * F)) / (2 * F) = (a + b) / (2 * F) + s := Nat.add_mul_div_right (a + b) s h2F
      rw [this]
      exact add_comm _ _
    rw [h_div_add]
    have h0' : (a + b) / (2 * F) = 0 := Nat.div_eq_of_lt hapb_lt
    omega

  have h_mod : R % (2 * F) = a + b := by
    have : R = s * (2 * F) + (a + b) := by rw [hR2]; ring
    have h0 : R % (2 * F) = (s * (2 * F) + (a + b)) % (2 * F) := by rw [this]
    rw [h0]
    have h_mod_add : (s * (2 * F) + (a + b)) % (2 * F) = (a + b) % (2 * F) := by
      have : s * (2 * F) + (a + b) = (a + b) + s * (2 * F) := by ring
      rw [this, Nat.add_mul_mod_self_right]
    rw [h_mod_add]
    exact Nat.mod_eq_of_lt hapb_lt

  intro h_cond
  cases h_cond with
  | inl h_zero =>
    rw [h_div] at h_zero
    have : a * b = 0 := by omega
    have : a * b ≥ 1 := Nat.mul_pos ha hb
    omega
  | inr h_not_sq =>
    have : (((R % (2 * F) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * F) : ℕ) : ℤ)) = ((a - b : ℤ) ^ 2) := by
      rw [h_div, h_mod]
      have hs2 : 2 * (s : ℤ) = (a * b : ℤ) := by
        have : 2 * s = a * b := hs.symm
        exact_mod_cast this
      push_cast
      calc (a + b : ℤ) ^ 2 - 8 * (s : ℤ) = (a + b : ℤ) ^ 2 - 4 * (2 * s : ℤ) := by ring
        _ = (a + b : ℤ) ^ 2 - 4 * (a * b : ℤ) := by rw [hs2]
        _ = (a - b : ℤ) ^ 2 := by ring
    rw [this] at h_not_sq
    have h_sq : IsSquare ((a - b : ℤ) ^ 2) := ⟨a - b, by ring⟩
    exact h_not_sq h_sq

/-- Lemma 1 of the paper, proved. -/
theorem lemma1 : Lemma1 := by
  intro F R a hOdd hF hCoprime hFermat hgcd hN_lt
  rcases Nat.eq_zero_or_pos F with rfl | hF_pos
  · exact leaf_F_zero R hN_lt
  constructor
  · intro hN
    exact leaf_prime_cond F R hF_pos hN
  · intro hcond
    by_contra hN_comp
    have hpock := leaf_pock F R a hOdd hF hCoprime hFermat hgcd
    have hR : 0 < R := by
      rcases Nat.eq_zero_or_pos R with rfl | h
      · have h1 : F = 1 := Nat.coprime_zero_left F |>.mp hCoprime
        subst h1
        exact absurd hF (by decide)
      · exact h
    obtain ⟨a_fac, b_fac, ha, hb, heq⟩ := leaf_comp_factors F R hF_pos hR hN_lt hpock hN_comp
    have h_fail := leaf_comp_cond_from_factors F R a_fac b_fac hF_pos hF hCoprime hN_lt heq ha hb
    exact h_fail hcond

end GoldbachLean.Saouter1998.BLS
