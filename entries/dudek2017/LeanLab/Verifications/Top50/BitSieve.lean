module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.Verifications.Top50.Base

/-!
A bignum sieve for even Goldbach, unit U-0340, run 20261017T1704Z-8485.
The primes below L are one natural number, built by a sieve of Eratosthenes in which each
step is one GMP operation the kernel runs natively: OR, shift, mod, xor. The even n that are
p + q with q in a short list of small primes are another natural number, and the whole range
is checked by ONE equality of natural numbers. Soundness is proved once, for every L ≤ 10^8.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Verifications.Top50.Bits

open LeanLab.Verifications.Top50

/-- One doubling step: `r` together with a copy of `r` shifted up by `s`. -/
def dup (s r : ℕ) : ℕ := r ||| (r <<< s)

/-- `rep d j` has bit `m` set exactly for the multiples `m` of `d` below `d * 2 ^ j`. -/
def rep (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => dup (d * 2 ^ j) (rep d j)

theorem rep_lt (d : ℕ) (hd : 1 ≤ d) : ∀ j, rep d j < 2 ^ (d * 2 ^ j)
  | 0 => by
    have : 2 ^ 1 ≤ 2 ^ (d * 2 ^ 0) := Nat.pow_le_pow_right (by norm_num) (by simpa using hd)
    simp only [rep]; omega
  | j + 1 => by
    have ih := rep_lt d hd j
    simp only [rep, dup]
    have h2 : d * 2 ^ (j + 1) = d * 2 ^ j + d * 2 ^ j := by ring
    rw [h2]
    apply Nat.or_lt_two_pow
    · exact lt_of_lt_of_le ih (Nat.pow_le_pow_right (by norm_num) (by omega))
    · rw [Nat.shiftLeft_eq, pow_add]
      exact Nat.mul_lt_mul_of_pos_right ih (by positivity)

theorem testBit_one_iff (m : ℕ) : (1 : ℕ).testBit m = true ↔ m = 0 := by
  rcases m with _ | m
  · simp
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, iff_false]
    rw [Nat.testBit_eq_false_of_lt]
    · simp
    · exact Nat.one_lt_two_pow (by omega)

theorem testBit_rep (d : ℕ) (hd : 1 ≤ d) : ∀ j m,
    (rep d j).testBit m = true ↔ m < d * 2 ^ j ∧ d ∣ m
  | 0, m => by
    simp only [rep, pow_zero, mul_one, testBit_one_iff]
    constructor
    · rintro rfl; exact ⟨by omega, dvd_zero d⟩
    · rintro ⟨hm, k, rfl⟩
      have : k < 1 := Nat.lt_of_mul_lt_mul_left (by simpa using hm)
      have : k = 0 := by omega
      simp [this]
  | j + 1, m => by
    have ih := testBit_rep d hd j
    have hlt := rep_lt d hd j
    have h2 : d * 2 ^ (j + 1) = d * 2 ^ j + d * 2 ^ j := by ring
    have hds : d ∣ d * 2 ^ j := ⟨2 ^ j, rfl⟩
    simp only [rep, dup, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq]
    rw [h2]
    by_cases hm : m < d * 2 ^ j
    · rw [ih]
      constructor
      · rintro (⟨h1, h3⟩ | ⟨h1, _⟩)
        · exact ⟨by omega, h3⟩
        · omega
      · rintro ⟨_, h3⟩; exact Or.inl ⟨hm, h3⟩
    · have hb : (rep d j).testBit m = false :=
        Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [hb, ih]
      have hdvd : d ∣ m - d * 2 ^ j ↔ d ∣ m := by
        constructor
        · intro h
          have := Nat.dvd_add h hds
          rwa [Nat.sub_add_cancel (by omega)] at this
        · intro h; exact Nat.dvd_sub h hds
      constructor
      · rintro (h | ⟨_, h1, h3⟩)
        · simp at h
        · exact ⟨by omega, hdvd.mp h3⟩
      · rintro ⟨h1, h3⟩
        exact Or.inr ⟨by omega, by omega, hdvd.mpr h3⟩

/-- Enough doublings for `d` to cover `[0, L)`. -/
def jOf (d L : ℕ) : ℕ := (L / d).log2 + 1

theorem lt_jOf (d L : ℕ) (hd : 1 ≤ d) : L < d * 2 ^ jOf d L := by
  have h1 : L / d < 2 ^ ((L / d).log2 + 1) := Nat.lt_log2_self
  have h2 : L < d * (L / d + 1) := by
    have := Nat.div_add_mod L d
    have := Nat.mod_lt L (show d > 0 by omega)
    rw [mul_add]; omega
  exact lt_of_lt_of_le h2 (Nat.mul_le_mul_left d h1)

/-- The sieve: bit `m` is set when some `d ∈ D` has `d * d ≤ m` and `d ∣ m`, for `m < L`. -/
def sieve (L : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: t => (rep d (jOf d L) <<< (d * d)) ||| sieve L t

theorem sieve_of_dvd (L m d : ℕ) (hd : 1 ≤ d) (hdm : d * d ≤ m) (hmL : m < L) (hdv : d ∣ m) :
    ∀ D : List ℕ, d ∈ D → (sieve L D).testBit m = true := by
  intro D
  induction D with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro hmem
    simp only [sieve, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hmem with rfl | h
    · left
      rw [Nat.testBit_shiftLeft]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hdm, (testBit_rep d hd _ _).mpr ⟨?_, ?_⟩⟩
      · have := lt_jOf d L hd; omega
      · exact Nat.dvd_sub hdv (dvd_mul_right d d)
    · right; exact ih h

/-- The sieving primes for `L`. -/
def D (L : ℕ) : List ℕ := P10k.filter (fun p => p * p < L)

theorem mem_D {L p : ℕ} (hL : L ≤ 10 ^ 8) (hp : p.Prime) (hpL : p * p < L) : p ∈ D L := by
  unfold D
  rw [List.mem_filter]
  refine ⟨P10k_complete p ?_ hp, by simpa using hpL⟩
  by_contra h
  have h := not_lt.mp h
  have : 10000 * 10000 ≤ p * p := Nat.mul_le_mul h h
  omega

/-- The prime bitmap: bit `m` set iff `2 ≤ m < L` and `m` is not sieved out. -/
def pm (L : ℕ) : ℕ := ((sieve L (D L) ||| 3) % 2 ^ L) ^^^ (2 ^ L - 1)

theorem testBit_three_eq (m : ℕ) (hm : 2 ≤ m) : (3 : ℕ).testBit m = false :=
  Nat.testBit_eq_false_of_lt
    (lt_of_lt_of_le (by norm_num : (3 : ℕ) < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hm))

theorem prime_of_pm {L m : ℕ} (hL : L ≤ 10 ^ 8) (h : (pm L).testBit m = true) : m.Prime := by
  simp only [pm, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_or] at h
  by_cases hmL : m < L
  · simp only [hmL, decide_true, Bool.true_and] at h
    have h2 : 2 ≤ m := by
      by_contra h2
      have t0 : (3 : ℕ).testBit 0 = true := by decide
      have t1 : (3 : ℕ).testBit 1 = true := by decide
      interval_cases m <;> simp_all
    rw [testBit_three_eq m h2] at h
    by_contra hp
    have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
    have hsq : m.minFac * m.minFac ≤ m := by
      have := Nat.minFac_sq_le_self (show 0 < m by omega) hp
      simpa [sq] using this
    have hb := sieve_of_dvd L m m.minFac hmf.one_lt.le hsq hmL (Nat.minFac_dvd m) (D L)
      (mem_D hL hmf (by omega))
    rw [hb] at h
    simp at h
  · simp [hmL] at h

/-- The Goldbach mask: bit `n` set when `n - q` is in `P` for some `q ∈ Q`, `q ≤ n`. -/
def gm (P : ℕ) : List ℕ → ℕ
  | [] => 0
  | q :: t => (P <<< q) ||| gm P t

theorem of_gm (P : ℕ) : ∀ (Q : List ℕ) (n : ℕ), (gm P Q).testBit n = true →
    ∃ q ∈ Q, q ≤ n ∧ P.testBit (n - q) = true := by
  intro Q
  induction Q with
  | nil => intro n h; simp [gm] at h
  | cons a t ih =>
    intro n h
    simp only [gm, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft, Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨a, by simp, h1, h2⟩
    · obtain ⟨q, hq, h3⟩ := ih n h
      exact ⟨q, List.mem_cons_of_mem _ hq, h3⟩

/-- The even mask: bit `n` set for `A ≤ n ≤ B` with `n - A` even. -/
def em (A B : ℕ) : ℕ := (rep 2 (jOf 2 B) <<< A) % 2 ^ (B + 1)

theorem testBit_em {A B n : ℕ} (hA : A ≤ n) (hB : n ≤ B) (he : 2 ∣ n - A) :
    (em A B).testBit n = true := by
  simp only [em, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨by omega, hA, (testBit_rep 2 (by norm_num) _ _).mpr ⟨?_, he⟩⟩
  have := lt_jOf 2 B (by norm_num); omega

/-- Soundness of one equality check: every `n` in the even mask is a Goldbach sum. -/
theorem goldbach_of_check {L A B : ℕ} {Q : List ℕ} (hL : L ≤ 10 ^ 8) (hQ : ∀ q ∈ Q, q.Prime)
    (h : em A B &&& gm (pm L) Q = em A B) :
    ∀ n, A ≤ n → n ≤ B → 2 ∣ n - A → IsGoldbachSum n := by
  intro n hA hB he
  have h1 := testBit_em hA hB he
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at h1
  obtain ⟨q, hq, hqn, hp⟩ := of_gm _ Q n h1.2
  exact ⟨q, n - q, hQ q hq, prime_of_pm hL hp, by omega⟩

/-- From one check starting at 4 to `EvenGoldbachUpTo B`. -/
theorem upTo_of_check {L B : ℕ} {Q : List ℕ} (hL : L ≤ 10 ^ 8) (hQ : ∀ q ∈ Q, q.Prime)
    (h : em 4 B &&& gm (pm L) Q = em 4 B) : EvenGoldbachUpTo B := by
  intro n hn h4 hnB
  apply goldbach_of_check hL hQ h n h4 hnB
  obtain ⟨k, rfl⟩ := hn
  exact ⟨k - 2, by omega⟩

theorem take_prime (k : ℕ) : ∀ q ∈ P10k.take k, q.Prime := by
  have h : P10k.all (fun q => primeB q) = true := by decide +kernel
  intro q hq
  exact primeB_sound (List.all_eq_true.mp h q (List.mem_of_mem_take hq))

/-- Small test: every even n from 4 to 10000. -/
theorem check_1e4 : em 4 10000 &&& gm (pm 10001) (P10k.take 40) = em 4 10000 := by
  decide +kernel

theorem upTo_1e4 : EvenGoldbachUpTo 10000 := upTo_of_check (by norm_num) (take_prime 40) check_1e4

/-! ### Windows: the same check on `[lo, lo + W)`, for ranges whose bitmap would not fit at once -/

/-- The least multiple of `d` that is at least `t`. -/
def firstMul (d t : ℕ) : ℕ := d * ((t + d - 1) / d)

theorem le_firstMul (d t : ℕ) (hd : 1 ≤ d) : t ≤ firstMul d t := by
  unfold firstMul
  have h1 := Nat.div_add_mod (t + d - 1) d
  have h2 := Nat.mod_lt (t + d - 1) (show d > 0 by omega)
  omega

theorem firstMul_le (d t k : ℕ) (hd : 1 ≤ d) (h : t ≤ d * k) : firstMul d t ≤ d * k := by
  unfold firstMul
  apply Nat.mul_le_mul_left
  have : (t + d - 1) / d < k + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    rw [add_mul, one_mul, mul_comm k d]; omega
  omega

theorem dvd_firstMul (d t : ℕ) : d ∣ firstMul d t := ⟨_, rfl⟩

/-- Window sieve: bit `i` set when `lo + i < lo + W` has some `d ∈ D`, `d * d ≤ lo + i`, `d ∣ lo + i`. -/
def wsieve (lo W : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: t => (rep d (jOf d W) <<< (firstMul d (max lo (d * d)) - lo)) ||| wsieve lo W t

theorem wsieve_of_dvd (lo W m d : ℕ) (hd : 1 ≤ d) (hdm : d * d ≤ m) (hlo : lo ≤ m)
    (hmW : m < lo + W) (hdv : d ∣ m) :
    ∀ D : List ℕ, d ∈ D → (wsieve lo W D).testBit (m - lo) = true := by
  intro D
  induction D with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro hmem
    simp only [wsieve, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hmem with rfl | h
    · left
      obtain ⟨k, rfl⟩ := hdv
      have hf1 := le_firstMul d (max lo (d * d)) hd
      have hf2 := firstMul_le d (max lo (d * d)) k hd (by omega)
      have hJ := lt_jOf d W hd
      rw [Nat.testBit_shiftLeft]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by omega, (testBit_rep d hd _ _).mpr ⟨by omega, ?_⟩⟩
      have : d * k - lo - (firstMul d (max lo (d * d)) - lo) =
          d * k - firstMul d (max lo (d * d)) := by omega
      rw [this]
      exact Nat.dvd_sub (dvd_mul_right d k) (dvd_firstMul _ _)
    · right; exact ih h

/-- Window prime bitmap: bit `i` set iff `i < W` and `lo + i` is not sieved out. -/
def wpm (lo W : ℕ) : ℕ := (wsieve lo W (D (lo + W)) % 2 ^ W) ^^^ (2 ^ W - 1)

theorem prime_of_wpm {lo W i : ℕ} (h2 : 2 ≤ lo) (hW : lo + W ≤ 10 ^ 8)
    (h : (wpm lo W).testBit i = true) : (lo + i).Prime := by
  simp only [wpm, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one] at h
  by_cases hiW : i < W
  · simp only [hiW, decide_true, Bool.true_and] at h
    by_contra hp
    set m := lo + i with hm
    have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
    have hsq : m.minFac * m.minFac ≤ m := by
      have := Nat.minFac_sq_le_self (show 0 < m by omega) hp
      simpa [sq] using this
    have hb := wsieve_of_dvd lo W m m.minFac hmf.one_lt.le hsq (by omega) (by omega)
      (Nat.minFac_dvd m) (D (lo + W)) (mem_D hW hmf (by omega))
    rw [show m - lo = i by omega] at hb
    rw [hb] at h
    simp at h
  · simp [hiW] at h

/-- Window even mask: bit `n - lo` set for `A ≤ n ≤ B` with `n - A` even. -/
def wem (lo A B : ℕ) : ℕ := (rep 2 (jOf 2 (B - lo)) <<< (A - lo)) % 2 ^ (B - lo + 1)

theorem testBit_wem {lo A B n : ℕ} (hlo : lo ≤ A) (hA : A ≤ n) (hB : n ≤ B) (he : 2 ∣ n - A) :
    (wem lo A B).testBit (n - lo) = true := by
  simp only [wem, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨by omega, by omega, (testBit_rep 2 (by norm_num) _ _).mpr ⟨?_, ?_⟩⟩
  · have := lt_jOf 2 (B - lo) (by norm_num); omega
  · rw [show n - lo - (A - lo) = n - A by omega]; exact he

/-- Soundness of one window check. -/
theorem goldbach_of_wcheck {lo W A B : ℕ} {Q : List ℕ} (h2 : 2 ≤ lo) (hW : lo + W ≤ 10 ^ 8)
    (hlo : lo ≤ A) (hQ : ∀ q ∈ Q, q.Prime)
    (h : wem lo A B &&& gm (wpm lo W) Q = wem lo A B) :
    ∀ n, A ≤ n → n ≤ B → 2 ∣ n - A → IsGoldbachSum n := by
  intro n hA hB he
  have h1 := testBit_wem hlo hA hB he
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at h1
  obtain ⟨q, hq, hqn, hp⟩ := of_gm _ Q _ h1.2
  have := prime_of_wpm h2 hW hp
  exact ⟨q, lo + (n - lo - q), hQ q hq, this, by omega⟩

/-- Extend `EvenGoldbachUpTo a` by one window `[a + 2, B]`. -/
theorem upTo_extend {lo W a B : ℕ} {Q : List ℕ} (ha : EvenGoldbachUpTo a) (hae : 2 ∣ a)
    (h2 : 2 ≤ lo) (hW : lo + W ≤ 10 ^ 8) (hlo : lo ≤ a + 2) (hQ : ∀ q ∈ Q, q.Prime)
    (h : wem lo (a + 2) B &&& gm (wpm lo W) Q = wem lo (a + 2) B) : EvenGoldbachUpTo B := by
  intro n hn h4 hnB
  by_cases hna : n ≤ a
  · exact ha n hn h4 hna
  · have hn2 : a + 2 ≤ n := by
      obtain ⟨k, hk⟩ := hn
      obtain ⟨i, hi⟩ := hae
      omega
    apply goldbach_of_wcheck h2 hW hlo hQ h n hn2 hnB
    exact Nat.dvd_sub (even_iff_two_dvd.mp hn) (Nat.dvd_add hae (dvd_refl 2))

end LeanLab.Verifications.Top50.Bits
