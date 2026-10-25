module

public import Mathlib

/-!
P0067 van der Corput 1939, page 94: "En vertu de ... φ(q) ≥ (1/2) q^{3/4}". PROVED here for
every q ≥ 1, in the integer form q³ ≤ 16 φ(q)⁴. The proof: φ(p^k)⁴/p^{3k} is at
least 1/8 for p = 2, 16/27 for p = 3 and 1 for p ≥ 5, and the product 2/27 exceeds 1/16.
AI-written Lean code, Claude, run 20261016T2204Z-20593. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.VanDerCorput1939

/-- The weight at 2. -/
def w2 (n : ℕ) : ℕ := if 2 ∣ n then 1 else 8
/-- The weight at 3. -/
def w3 (n : ℕ) : ℕ := if 3 ∣ n then 16 else 27

theorem w2_mul {a b : ℕ} (h : Nat.Coprime a b) : w2 (a * b) * 8 = w2 a * w2 b := by
  unfold w2
  by_cases ha : 2 ∣ a <;> by_cases hb : 2 ∣ b
  · have h1 : 2 ∣ Nat.gcd a b := Nat.dvd_gcd ha hb
    rw [h] at h1; omega
  · simp [ha, hb, Dvd.dvd.mul_right ha]
  · simp [ha, hb, Dvd.dvd.mul_left hb]
  · have : ¬ 2 ∣ a * b := fun hab => (Nat.prime_two.dvd_mul.mp hab).elim ha hb
    simp [ha, hb, this]

theorem w3_mul {a b : ℕ} (h : Nat.Coprime a b) : w3 (a * b) * 27 = w3 a * w3 b := by
  unfold w3
  by_cases ha : 3 ∣ a <;> by_cases hb : 3 ∣ b
  · have h1 : 3 ∣ Nat.gcd a b := Nat.dvd_gcd ha hb
    rw [h] at h1; omega
  · simp [ha, hb, Dvd.dvd.mul_right ha]
  · simp [ha, hb, Dvd.dvd.mul_left hb]
  · have : ¬ 3 ∣ a * b := fun hab => (Nat.prime_three.dvd_mul.mp hab).elim ha hb
    simp [ha, hb, this]

/-- The weighted multiplicative form. -/
def Good (q : ℕ) : Prop := q ^ 3 * (w2 q * w3 q) ≤ 216 * (Nat.totient q) ^ 4

theorem good_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) : Good (p ^ k) := by
  unfold Good
  rw [Nat.totient_prime_pow hp hk]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 : 2 ∣ p ^ (j + 1) ↔ p = 2 := by
    constructor
    · intro h; exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow h)).symm
    · rintro rfl; exact dvd_pow_self 2 (by omega)
  have h3 : 3 ∣ p ^ (j + 1) ↔ p = 3 := by
    constructor
    · intro h; exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    · rintro rfl; exact dvd_pow_self 3 (by omega)
  unfold w2 w3
  have hpj : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp.pos
  have hjj : p ^ (3 * j) ≤ p ^ (4 * j) := Nat.pow_le_pow_right hp.pos (by omega)
  have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
  rcases (by have := hp.two_le; omega : p = 2 ∨ p = 3 ∨ 5 ≤ p) with rfl | rfl | h5
  · rw [if_pos (h2.mpr rfl), if_neg (by rw [h3]; omega)]
    have e1 : (2 ^ (j + 1)) ^ 3 = 8 * 2 ^ (3 * j) := by ring
    have e2 : (2 ^ j * (2 - 1)) ^ 4 = 2 ^ (4 * j) := by ring
    rw [e1, e2]; nlinarith
  · rw [if_neg (by rw [h2]; omega), if_pos (h3.mpr rfl)]
    have e1 : (3 ^ (j + 1)) ^ 3 = 27 * 3 ^ (3 * j) := by ring
    have e2 : (3 ^ j * (3 - 1)) ^ 4 = 16 * 3 ^ (4 * j) := by ring
    rw [e1, e2]; nlinarith
  · have hn2 : ¬ p = 2 := by omega
    have hn3 : ¬ p = 3 := by omega
    rw [if_neg (by rw [h2]; omega), if_neg (by rw [h3]; omega)]
    -- p^{3j+3} * 216 ≤ 216 * p^{4j} (p-1)^4, from p^3 ≤ (p-1)^4
    have hp3 : p ^ 3 ≤ (p - 1) ^ 4 := by
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 5 := ⟨p - 5, by omega⟩
      rw [show m + 5 - 1 = m + 4 by omega]
      ring_nf; nlinarith [Nat.zero_le m, sq_nonneg (m : ℕ)]
    have e1 : (p ^ (j + 1)) ^ 3 = p ^ 3 * p ^ (3 * j) := by ring
    have e2 : (p ^ j * (p - 1)) ^ 4 = (p - 1) ^ 4 * p ^ (4 * j) := by ring
    rw [e1, e2]
    calc p ^ 3 * p ^ (3 * j) * (8 * 27) ≤ (p - 1) ^ 4 * p ^ (4 * j) * 216 := by
          have := Nat.mul_le_mul hp3 hjj; nlinarith
      _ = 216 * ((p - 1) ^ 4 * p ^ (4 * j)) := by ring

theorem good_mul {a b : ℕ} (h : Nat.Coprime a b) (ha : Good a) (hb : Good b) : Good (a * b) := by
  unfold Good at *
  rw [Nat.totient_mul h]
  have h2 := w2_mul h
  have h3 := w3_mul h
  have key : (a * b) ^ 3 * (w2 (a * b) * w3 (a * b)) * 216 ≤
      216 * (Nat.totient a * Nat.totient b) ^ 4 * 216 := by
    calc (a * b) ^ 3 * (w2 (a * b) * w3 (a * b)) * 216
        = (a ^ 3 * (w2 a * w3 a)) * (b ^ 3 * (w2 b * w3 b)) := by
          rw [show (a * b) ^ 3 * (w2 (a * b) * w3 (a * b)) * 216 =
            (a * b) ^ 3 * ((w2 (a * b) * 8) * (w3 (a * b) * 27)) by ring, h2, h3]; ring
      _ ≤ (216 * Nat.totient a ^ 4) * (216 * Nat.totient b ^ 4) := Nat.mul_le_mul ha hb
      _ = 216 * (Nat.totient a * Nat.totient b) ^ 4 * 216 := by ring
  exact Nat.le_of_mul_le_mul_right key (by norm_num)

theorem good_all : ∀ q, 0 < q → Good q := by
  intro q
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn => intro _; exact good_prime_pow p n hp hn
  | zero => intro h; omega
  | one => intro _; unfold Good w2 w3; norm_num
  | coprime a b ha hb hab iha ihb =>
    intro _; exact good_mul hab (iha (by omega)) (ihb (by omega))

/-- `q³ ≤ 16 φ(q)⁴` for every `q ≥ 1`. -/
theorem cube_le_totient_pow4 (q : ℕ) (hq : 0 < q) : q ^ 3 ≤ 16 * (Nat.totient q) ^ 4 := by
  have h := good_all q hq
  unfold Good at h
  have hw : 16 ≤ w2 q * w3 q := by
    unfold w2 w3; split_ifs <;> norm_num
  have : q ^ 3 * 16 ≤ 216 * Nat.totient q ^ 4 := le_trans (Nat.mul_le_mul_left _ hw) h
  omega

/-- van der Corput's `φ(q) ≥ (1/2) q^{3/4}`, page 94. -/
theorem totient_ge (q : ℕ) (hq : 0 < q) : (1 / 2 : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 4) ≤ Nat.totient q := by
  have h := cube_le_totient_pow4 q hq
  have e : ((q : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 = (q : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast ((q : ℝ) ^ ((3 : ℝ) / 4)), ← Real.rpow_mul (Nat.cast_nonneg q)]
    norm_num
  have hc : ((q ^ 3 : ℕ) : ℝ) ≤ ((16 * Nat.totient q ^ 4 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hc
  have hr : ((q : ℝ) ^ ((3 : ℝ) / 4)) ^ 4 ≤ (2 * (Nat.totient q : ℝ)) ^ 4 := by
    rw [e]; linarith [show (2 * (Nat.totient q : ℝ)) ^ 4 = 16 * (Nat.totient q : ℝ) ^ 4 by ring]
  have h2 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp hr
  linarith

end LeanLab.VanDerCorput1939
