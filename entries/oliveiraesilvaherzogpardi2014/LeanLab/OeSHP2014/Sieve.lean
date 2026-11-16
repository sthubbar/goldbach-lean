module

public import Mathlib
public import LeanLab.OeSHP2014.Primes

/-!
# Soundness of the window check

The lemmas that turn one window equality of `Core.lean` into a statement about primes. Only
one direction is needed: every odd multiple of a sieving prime is marked by the sieve, so a
bit that survives the sieve is a prime.
-/

@[expose] public section

namespace LeanLab.OeSHP2014

/-- The doubling of `repL` keeps every multiple of `d` below the current length marked, and
stops only when the length exceeds `L`. -/
theorem repL_mult (d L : ℕ) : ∀ f r len, 0 < len → d ∣ len → L < len * 2 ^ f →
    (∀ m, m < len → d ∣ m → r.testBit m = true) →
    ∀ m, m ≤ L → d ∣ m → (repL d L f r len).testBit m = true := by
  intro f
  induction f with
  | zero =>
    intro r len _ _ hL hr m hm hdm
    simp only [repL]
    exact hr m (by simpa using lt_of_le_of_lt hm hL) hdm
  | succ k ih =>
    intro r len hlen hdl hL hr m hm hdm
    simp only [repL]
    by_cases hc : L < len
    · rw [if_pos hc]; exact hr m (by omega) hdm
    · rw [if_neg hc]
      apply ih (r ||| (r <<< len)) (2 * len) (by omega) (Dvd.dvd.mul_left hdl 2)
        (by rw [pow_succ] at hL; linarith) _ m hm hdm
      intro m' hm' hdm'
      rw [Nat.testBit_or, Bool.or_eq_true]
      by_cases h1 : m' < len
      · exact Or.inl (hr m' h1 hdm')
      · right
        rw [Nat.testBit_shiftLeft]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, hr (m' - len) (by omega) (Nat.dvd_sub hdm' hdl)⟩

/-- From `r = 1` and `len = d`, `repL` marks every multiple of `d` up to `L`. -/
theorem testBit_repL {d L m : ℕ} (hd : 1 ≤ d) (hL : L < 2 ^ 64) (hm : m ≤ L) (hdm : d ∣ m) :
    (repL d L 64 1 d).testBit m = true := by
  apply repL_mult d L 64 1 d (by omega) dvd_rfl _ _ m hm hdm
  · calc L < 2 ^ 64 := hL
      _ ≤ d * 2 ^ 64 := Nat.le_mul_of_pos_left _ (by omega)
  · intro m' hm' hdm'
    obtain ⟨k, rfl⟩ := hdm'
    have : k = 0 := by
      by_contra hk
      have : d ≤ d * k := Nat.le_mul_of_pos_right d (by omega)
      omega
    subst this
    simp

theorem le_firstOddMul (d t : ℕ) (hd : 1 ≤ d) : t ≤ firstOddMul d t := by
  unfold firstOddMul
  have h1 := Nat.div_add_mod (t + d - 1) d
  have h2 := Nat.mod_lt (t + d - 1) (show d > 0 by omega)
  split_ifs
  · rw [mul_add, mul_one]; omega
  · omega

theorem firstOddMul_spec (d t : ℕ) :
    ∃ k, firstOddMul d t = d * k ∧ k % 2 = 1 ∧ k ≤ (t + d - 1) / d + 1 ∧ (t + d - 1) / d ≤ k := by
  unfold firstOddMul
  split_ifs with h
  · exact ⟨_, rfl, by omega, le_rfl, by omega⟩
  · exact ⟨_, rfl, by omega, by omega, le_rfl⟩

/-- The least odd multiple is at most any odd multiple `d * k ≥ t`. -/
theorem firstOddMul_le (d t k : ℕ) (hd : 1 ≤ d) (hk : k % 2 = 1) (h : t ≤ d * k) :
    firstOddMul d t ≤ d * k := by
  obtain ⟨k', hk', hk'2, hk'3, hk'4⟩ := firstOddMul_spec d t
  rw [hk']
  apply Nat.mul_le_mul_left
  have : (t + d - 1) / d ≤ k := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    omega
  omega

/-- The odd sieve marks every odd multiple `m` of a listed odd `d` with `d * d ≤ m` in the
window. -/
theorem osieve_of_dvd (lo Wb m d : ℕ) (hd : 1 ≤ d) (hdo : d % 2 = 1) (hlo : lo % 2 = 1)
    (hmo : m % 2 = 1) (hdm : d * d ≤ m) (hlom : lo ≤ m) (hmW : m < lo + 2 * Wb)
    (hW : Wb < 2 ^ 64) (hdv : d ∣ m) :
    ∀ D : List ℕ, d ∈ D → (osieve lo Wb D).testBit ((m - lo) / 2) = true := by
  intro D
  induction D with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro hmem
    simp only [osieve, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hmem with rfl | h
    · left
      obtain ⟨k, rfl⟩ := hdv
      have hk : k % 2 = 1 := by
        rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · subst hj; rw [show d * (j + j) = 2 * (d * j) by ring] at hmo; omega
        · omega
      have hf1 := le_firstOddMul d (max lo (d * d)) hd
      have hf2 := firstOddMul_le d (max lo (d * d)) k hd hk (by omega)
      obtain ⟨k', hk', hk'2, -, -⟩ := firstOddMul_spec d (max lo (d * d))
      rw [Nat.testBit_shiftLeft]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      have hkk : k' ≤ k := by
        rw [hk'] at hf2
        exact Nat.le_of_mul_le_mul_left hf2 (by omega)
      obtain ⟨e, he⟩ : 2 ∣ k - k' := by omega
      have hdiff : (d * k - lo) / 2 - (firstOddMul d (max lo (d * d)) - lo) / 2 = d * e := by
        rw [hk']
        have : d * k - d * k' = 2 * (d * e) := by
          rw [← Nat.mul_sub, he]; ring
        omega
      refine ⟨by omega, ?_⟩
      rw [hdiff]
      exact testBit_repL hd hW (by omega) (dvd_mul_right d e)
    · right; exact ih h

/-- `SRo L` holds every odd prime `p` with `p * p < L`, for `L ≤ 20000 * 20000`. -/
theorem mem_SRo {L p : ℕ} (hL : L ≤ 20000 * 20000) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpL : p * p < L) : p ∈ SRo L := by
  unfold SRo
  rw [List.mem_filter]
  refine ⟨PL_tail_complete p ?_ hp hp2, by simpa using hpL⟩
  by_contra h
  have h := not_lt.mp h
  have : 20000 * 20000 ≤ p * p := Nat.mul_le_mul h h
  omega

/-- A set bit of the odd window prime bitmap is a prime. -/
theorem prime_of_opm {lo Wb i : ℕ} (h3 : 3 ≤ lo) (hlo : lo % 2 = 1)
    (hW : lo + 2 * Wb ≤ 20000 * 20000) (h : (opm lo Wb).testBit i = true) :
    (lo + 2 * i).Prime := by
  simp only [opm, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one] at h
  by_cases hiW : i < Wb
  · simp only [hiW, decide_true, Bool.and_true] at h
    by_contra hp
    set m := lo + 2 * i with hm
    have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
    have hsq : m.minFac * m.minFac ≤ m := by
      have := Nat.minFac_sq_le_self (show 0 < m by omega) hp
      simpa [sq] using this
    have hmo : m % 2 = 1 := by omega
    have hf2 : m.minFac ≠ 2 := by
      intro h2
      have := Nat.minFac_dvd m
      rw [h2] at this
      omega
    have hfo : m.minFac % 2 = 1 := by
      rcases hmf.eq_two_or_odd with h2 | h2
      · exact absurd h2 hf2
      · exact h2
    have hb := osieve_of_dvd lo Wb m m.minFac hmf.one_lt.le hfo hlo hmo hsq (by omega) (by omega)
      (by omega) (Nat.minFac_dvd m) (SRo (lo + 2 * Wb)) (mem_SRo hW hmf hf2 (by omega))
    rw [show (m - lo) / 2 = i by omega] at hb
    rw [hb] at h
    simp at h
  · simp [hiW] at h

/-- The even mask has bit `(n - lo - 1) / 2` set for each even `n` in `[A, B]`. -/
theorem testBit_oem {lo A B n : ℕ} (hlo : lo < A) (hA : A ≤ n) (hB : n ≤ B) (hn : n % 2 = 0)
    (hAe : A % 2 = 0) (hlo1 : lo % 2 = 1) : (oem lo A B).testBit ((n - lo - 1) / 2) = true := by
  simp only [oem, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

theorem of_gmo (P : ℕ) : ∀ (Q : List ℕ) (j : ℕ), (gmo P Q).testBit j = true →
    ∃ q ∈ Q, q / 2 ≤ j ∧ P.testBit (j - q / 2) = true := by
  intro Q
  induction Q with
  | nil => intro j h; simp [gmo] at h
  | cons a t ih =>
    intro j h
    simp only [gmo, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft, Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨a, by simp, h1, h2⟩
    · obtain ⟨q, hq, h3⟩ := ih j h
      exact ⟨q, List.mem_cons_of_mem _ hq, h3⟩

/-- Soundness of one window check: every even `n` in `[A, B]` is `x + y` with `x` among the
first `K` odd primes and `y` prime. -/
theorem partition_of_owcheck {lo Wb A B K : ℕ} (h3 : 3 ≤ lo) (hlo1 : lo % 2 = 1)
    (hW : lo + 2 * Wb ≤ 20000 * 20000) (hlo : lo < A) (hAe : A % 2 = 0)
    (h : oem lo A B &&& gmo (opm lo Wb) (QKo K) = oem lo A B) :
    ∀ n, A ≤ n → n ≤ B → n % 2 = 0 → ∃ x ∈ QKo K, (n - x).Prime := by
  intro n hA hB hn
  have h1 := testBit_oem hlo hA hB hn hAe hlo1
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at h1
  obtain ⟨x, hx, hxn, hp⟩ := of_gmo _ _ _ h1.2
  have hpr := prime_of_opm h3 hlo1 hW hp
  have hxo := (QKo_prime K x hx).2
  rw [show lo + 2 * ((n - lo - 1) / 2 - x / 2) = n - x by omega] at hpr
  exact ⟨x, hx, hpr⟩

end LeanLab.OeSHP2014
