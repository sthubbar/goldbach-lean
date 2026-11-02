module

public import Mathlib
public import GoldbachLean.Saouter1998.Paper
public import GoldbachLean.Saouter1998.ModPow

/-!
# Saouter 1998, Theorem 2

Theorem 2 of the paper, the Brillhart, Lehmer and Selfridge criterion specialised to `F = 2^22` and
base 5, proved in both directions from first principles.

* If: every prime factor of `N` is `1 mod 2^22` by the order of `5^R`, the least such prime is
  `12582913`, so below `2 F^3` a composite `N` has exactly two prime factors `aF + 1` and `bF + 1`,
  which forces `s ≥ 1` and `r^2 - 8 s = (a - b)^2`.
* Only if: a square `r^2 - 8 s = t^2` with `s ≥ 1` factors `N = (aF + 1) (bF + 1)`, where
  `a, b = (r ± t) / 2`.

The "if" direction is proved under the size condition `N < 2 F^3` of Lemma 1, which covers the
paper's last prime `100000000209366024193` above `10^20`; that prime is then certified by the
paper's own test, one modular power in the kernel.
AI wrote the Lean code: Claude by Anthropic for most files, Codex for Theorem 1 and the statement of Lemma 1, Gemini and Antigravity agents for parts of the Lemma 1 proof; it is checked only by the Lean kernel. Ternary Goldbach is
Helfgott's theorem, binary Goldbach is open.
-/

@[expose] public section

namespace GoldbachLean.Saouter1998.Thm2

open GoldbachLean.Saouter1998.Paper GoldbachLean.Saouter1998.ModPow

/-- A prime factor `p` of `N` with `a^(R 2^m) = -1 mod N` has `2^(m+1) ∣ p - 1`. -/
theorem two_pow_dvd {N p R m a : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hp2 : p ≠ 2)
    (ha : (a : ZMod N) ^ (R * 2 ^ m) = -1) : 2 ^ (m + 1) ∣ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  set c : ZMod p := (a : ZMod p) ^ R with hc
  have hcm : c ^ (2 ^ m) = -1 := by
    have h := congrArg (ZMod.castHom hpN (ZMod p)) ha
    simp only [map_pow, map_natCast, castHom_neg_one] at h
    rw [hc, ← pow_mul]; exact h
  have hnot : ¬ c ^ (2 ^ m) = 1 := by rw [hcm]; exact ZMod.neg_one_ne_one
  have hfin : c ^ (2 ^ (m + 1)) = 1 := by
    rw [pow_succ, pow_mul, hcm]; exact neg_one_sq
  have hord : orderOf c = 2 ^ (m + 1) := orderOf_eq_prime_pow hnot hfin
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at hcm
    exact (neg_ne_zero.mpr (one_ne_zero (α := ZMod p))) hcm.symm
  exact hord ▸ ZMod.orderOf_dvd_card_sub_one hc0

theorem half_eq (R : ℕ) : 2 ^ 22 * R / 2 = R * 2 ^ 21 := by
  rw [show (2 : ℕ) ^ 22 = 2 * 2 ^ 21 by norm_num, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num),
    mul_comm]

/-- Every prime factor of a Theorem 2 candidate is `j 2^22 + 1` with `j ≥ 3`. -/
theorem factor_form {p R : ℕ} (hp : p.Prime) (hpN : p ∣ 2 ^ 22 * R + 1)
    (h5 : (5 : ZMod (2 ^ 22 * R + 1)) ^ (2 ^ 22 * R / 2) = -1) :
    ∃ j, 3 ≤ j ∧ p = 2 ^ 22 * j + 1 := by
  have hp2 : p ≠ 2 := by
    intro h2
    have h2N : 2 ∣ 2 ^ 22 * R + 1 := h2 ▸ hpN
    have h2X : 2 ∣ 2 ^ 22 * R := Dvd.dvd.mul_right (dvd_pow_self 2 (by norm_num)) R
    have h21 := (Nat.dvd_add_right h2X).mp h2N
    norm_num at h21
  rw [half_eq] at h5
  obtain ⟨j, hj⟩ := two_pow_dvd (m := 21) hp hpN hp2 (by exact_mod_cast h5)
  have hp1 := hp.two_le
  have hpj : p = 2 ^ 22 * j + 1 := by norm_num at hj ⊢; omega
  refine ⟨j, ?_, hpj⟩
  by_contra hlt
  interval_cases j
  · norm_num at hpj; omega
  · norm_num at hpj; subst hpj; norm_num at hp
  · norm_num at hpj; subst hpj; norm_num at hp

theorem key3 {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) : 3 * a + 3 * b ≤ a * b + 9 := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb
  ring_nf; omega

theorem isSquare_sub {a b s : ℕ} (hab : a * b = 2 * s) :
    IsSquare (((a + b : ℕ) : ℤ) ^ 2 - 8 * (s : ℤ)) := by
  refine ⟨(a : ℤ) - b, ?_⟩
  have h : ((a : ℤ) * b) = 2 * s := by exact_mod_cast hab
  push_cast
  linear_combination 4 * h

/-- Theorem 2, the "if" direction, under the size condition `N < 2 F^3` of Lemma 1. -/
theorem theorem2_if (R : ℕ) (hR : R % 2 = 1) (hlt : 2 ^ 22 * R + 1 < 2 * (2 ^ 22) ^ 3)
    (h5 : (5 : ZMod (2 ^ 22 * R + 1)) ^ (2 ^ 22 * R / 2) = -1)
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
  obtain ⟨a, ha3, hpa⟩ := factor_form hpp (hN ▸ hpd) h5
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
  obtain ⟨b, hb3, hMb⟩ := factor_form hMp (hN ▸ ⟨p, by rw [hM, mul_comm]⟩) h5
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

/-- Theorem 2, the "only if" direction: a prime `2^22 R + 1` has `s = 0` or `r^2 - 8s` not a
square. No hypothesis on `R` is needed. -/
theorem theorem2_only_if (R : ℕ) (hp : (2 ^ 22 * R + 1).Prime) :
    R / (2 * 2 ^ 22) = 0 ∨
      ¬ IsSquare ((R % (2 * 2 ^ 22) : ℤ) ^ 2 - 8 * (R / (2 * 2 ^ 22) : ℤ)) := by
  by_contra hcon
  rw [not_or, not_not] at hcon
  obtain ⟨hs0, t, ht⟩ := hcon
  obtain ⟨s, hs⟩ : ∃ s, s = R / (2 * 2 ^ 22) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = R % (2 * 2 ^ 22) := ⟨_, rfl⟩
  have hsZ : (R : ℤ) / (2 * 2 ^ 22) = (s : ℤ) := by
    have := congrArg (Nat.cast : ℕ → ℤ) hs; push_cast at this; exact this.symm
  have hrZ : (R : ℤ) % (2 * 2 ^ 22) = (r : ℤ) := by
    have := congrArg (Nat.cast : ℕ → ℤ) hr; push_cast at this; exact this.symm
  rw [hsZ, hrZ] at ht
  rw [← hs] at hs0
  have hRsr : R = 2 * 2 ^ 22 * s + r := by rw [hs, hr]; exact (Nat.div_add_mod R (2 * 2 ^ 22)).symm
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
  have hfac : 2 ^ 22 * R + 1 = (2 ^ 22 * a + 1) * (2 ^ 22 * b + 1) := by
    rw [hRsr, ← hsum]
    have : (2 ^ 22 * a + 1) * (2 ^ 22 * b + 1) =
        2 ^ 22 * (2 ^ 22 * (a * b)) + 2 ^ 22 * (a + b) + 1 := by ring
    rw [this, hab]; ring
  rw [hfac] at hp
  have h1 : 2 ^ 22 * a + 1 ≠ 1 := by have := Nat.mul_le_mul_left (2 ^ 22) ha1; omega
  have h2 : 2 ^ 22 * b + 1 ≠ 1 := by have := Nat.mul_le_mul_left (2 ^ 22) hb1; omega
  exact Nat.not_prime_mul h1 h2 hp

/-- Theorem 2 of the paper, as stated in `Paper.Theorem2`. -/
theorem theorem2 : Theorem2 := by
  intro R hR hlt _ h5
  refine ⟨theorem2_only_if R, theorem2_if R hR (lt_trans hlt (by norm_num)) h5⟩

/-! ### The paper's last prime, certified by the paper's own test -/

/-- Boolean form of the test, with a square-free witness `k` for `r^2 - 8s`. -/
def thm2B (R k : ℕ) : Bool :=
  let N := 2 ^ 22 * R + 1
  let s := R / (2 * 2 ^ 22)
  let r := R % (2 * 2 ^ 22)
  (R % 2 == 1) && decide (N < 2 * (2 ^ 22) ^ 3) &&
    (pm (N.log2 + 1) 5 (R * 2 ^ 21) N == N - 1) &&
    (s == 0 || decide (r * r < 8 * s) ||
      (decide (8 * s + k * k < r * r) && decide (r * r < 8 * s + (k + 1) * (k + 1))))

theorem not_isSquare_of {x : ℤ} {k : ℕ} (h1 : (k * k : ℤ) < x) (h2 : x < ((k + 1) * (k + 1) : ℤ)) :
    ¬ IsSquare x := by
  rintro ⟨y, rfl⟩
  have hy : y * y = (y.natAbs * y.natAbs : ℕ) := by push_cast; exact (abs_mul_abs_self y).symm
  rw [hy] at h1 h2
  have h1' : k * k < y.natAbs * y.natAbs := by exact_mod_cast h1
  have h2' : y.natAbs * y.natAbs < (k + 1) * (k + 1) := by exact_mod_cast h2
  rcases le_or_gt y.natAbs k with h | h
  · have := Nat.mul_le_mul h h; omega
  · have h' : k + 1 ≤ y.natAbs := h
    have := Nat.mul_le_mul h' h'; omega

theorem prime_of_thm2B {R k : ℕ} (h : thm2B R k = true) : (2 ^ 22 * R + 1).Prime := by
  simp only [thm2B, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hR, hlt⟩, hpm⟩, hsq⟩ := h
  apply theorem2_if R hR hlt
  · set N := 2 ^ 22 * R + 1 with hN
    rw [half_eq]
    have he : R * 2 ^ 21 < 2 ^ (N.log2 + 1) := by
      have h1 : R * 2 ^ 21 < N := by rw [hN]; omega
      exact lt_trans h1 Nat.lt_log2_self
    have := pm_cast (N.log2 + 1) 5 (R * 2 ^ 21) N he
    rw [hpm, Nat.cast_ofNat] at this
    rw [← this]
    have hN1 : 1 ≤ N := by omega
    rw [Nat.cast_sub hN1]
    simp
  · have hrZ : (R : ℤ) % (2 * 2 ^ 22) = ((R % (2 * 2 ^ 22) : ℕ) : ℤ) := by push_cast; rfl
    have hsZ : (R : ℤ) / (2 * 2 ^ 22) = ((R / (2 * 2 ^ 22) : ℕ) : ℤ) := by push_cast; rfl
    rw [hrZ, hsZ]
    generalize R % (2 * 2 ^ 22) = r at hsq ⊢
    generalize R / (2 * 2 ^ 22) = s at hsq ⊢
    rcases hsq with (h0 | hneg) | ⟨hk1, hk2⟩
    · exact Or.inl h0
    · right
      rintro ⟨y, hy⟩
      have h1 : ((r * r : ℕ) : ℤ) < ((8 * s : ℕ) : ℤ) := by exact_mod_cast hneg
      push_cast at h1
      nlinarith [mul_self_nonneg y]
    · right
      apply not_isSquare_of (k := k)
      · have h1 : ((8 * s + k * k : ℕ) : ℤ) < ((r * r : ℕ) : ℤ) := by exact_mod_cast hk1
        push_cast at h1; nlinarith
      · have h1 : ((r * r : ℕ) : ℤ) < ((8 * s + (k + 1) * (k + 1) : ℕ) : ℤ) := by
          exact_mod_cast hk2
        push_cast at h1; nlinarith

/-- Page 865: the last prime of Saouter's ladder, `100000000209366024193`, above `10^20`, is prime,
by the test of Theorem 2 under the size condition `N < 2 F^3`, kernel checked. -/
theorem last_prime : (100000000209366024193 : ℕ).Prime := by
  have h := prime_of_thm2B (R := 23841857960073) (k := 7960711) (by decide +kernel)
  have e : 2 ^ 22 * 23841857960073 + 1 = 100000000209366024193 := by norm_num
  rw [e] at h
  exact h

/-- The first rung, `138412033`, by the same test. -/
theorem first_prime : (138412033 : ℕ).Prime := by
  have h := prime_of_thm2B (R := 33) (k := 0) (by decide +kernel)
  have e : 2 ^ 22 * 33 + 1 = 138412033 := by norm_num
  rw [e] at h
  exact h

end GoldbachLean.Saouter1998.Thm2
