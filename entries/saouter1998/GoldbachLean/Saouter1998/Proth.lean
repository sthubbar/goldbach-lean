module

public import Mathlib
public import GoldbachLean.Saouter1998.ModPow

/-!
# Proth's theorem

The direction of Proth's theorem that the computation uses: if `N = k 2^n + 1` with `0 < k < 2^n`
and `a^((N-1)/2) = -1` modulo `N`, then `N` is prime. This is Theorem 2.3 of Helfgott and Platt,
Numerical verification of the ternary Goldbach conjecture up to 8.875e30, without the Jacobi symbol
condition of their display, which only guides the choice of `a`. `prothB` is the Boolean form for
the kernel.
AI wrote the Lean code: Claude by Anthropic for most files, Codex for Theorem 1 and the statement of Lemma 1, Gemini and Antigravity agents for parts of the Lemma 1 proof; it is checked only by the Lean kernel. Ternary Goldbach is
Helfgott's theorem, binary Goldbach is open.
-/

@[expose] public section

namespace GoldbachLean.Saouter1998.Proth

open GoldbachLean.Saouter1998.ModPow

/-- Proth's theorem, sufficiency, as in Theorem 2.3 of Helfgott and Platt. -/
theorem proth {k m a N : ℕ} (hk0 : 0 < k) (hk : k < 2 ^ (m + 1)) (hN : N = k * 2 ^ (m + 1) + 1)
    (ha : (a : ZMod N) ^ (k * 2 ^ m) = -1) : N.Prime := by
  have hN3 : 3 ≤ N := by
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [hN, pow_succ]; nlinarith
  by_contra hNp
  set p := N.minFac with hp_def
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ N := Nat.minFac_dvd N
  have hsq : p ^ 2 ≤ N := by
    have := Nat.minFac_sq_le_self (by omega : 0 < N) hNp
    simpa [sq] using this
  have : Fact p.Prime := ⟨hpp⟩
  -- N is odd, so p is odd
  have hp2 : p ≠ 2 := by
    intro h2
    have h2N : 2 ∣ k * 2 ^ (m + 1) + 1 := hN ▸ (h2 ▸ hpd)
    have h2X : 2 ∣ k * 2 ^ (m + 1) := Dvd.dvd.mul_left (dvd_pow_self 2 (Nat.succ_ne_zero m)) k
    have h21 := (Nat.dvd_add_right h2X).mp h2N
    norm_num at h21
  -- move the congruence to ZMod p
  set c : ZMod p := (a : ZMod p) ^ k with hc
  have hcm : c ^ (2 ^ m) = -1 := by
    have h := congrArg (ZMod.castHom hpd (ZMod p)) ha
    simp only [map_pow, map_natCast, castHom_neg_one] at h
    rw [hc, ← pow_mul]; exact h
  have hne : (-1 : ZMod p) ≠ 1 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by
      have : (1 : ZMod p) + 1 = 0 := by
        calc (1 : ZMod p) + 1 = -1 + 1 := by rw [h]
          _ = 0 := neg_add_cancel 1
      simpa [one_add_one_eq_two] using this
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
  have hnot : ¬ c ^ (2 ^ m) = 1 := by rw [hcm]; exact hne
  have hfin : c ^ (2 ^ (m + 1)) = 1 := by
    rw [pow_succ, pow_mul, hcm]; exact neg_one_sq
  have hord : orderOf c = 2 ^ (m + 1) := orderOf_eq_prime_pow hnot hfin
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at hcm
    exact (neg_ne_zero.mpr (one_ne_zero (α := ZMod p))) hcm.symm
  have hdvd : 2 ^ (m + 1) ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hc0
  have hp1 : 2 ^ (m + 1) + 1 ≤ p := by
    have := Nat.le_of_dvd (by have := hpp.two_le; omega) hdvd
    omega
  have : (2 ^ (m + 1) + 1) ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left hp1 2) hsq
  rw [hN] at this
  nlinarith

/-- The Boolean Proth test with the fast modular power `pm`. -/
def prothB (k m a : ℕ) : Bool :=
  let N := k * 2 ^ (m + 1) + 1
  decide (0 < k) && decide (k < 2 ^ (m + 1)) &&
    (pm (N.log2 + 1) a (k * 2 ^ m) N == N - 1)

theorem prime_of_prothB {k m a : ℕ} (h : prothB k m a = true) : (k * 2 ^ (m + 1) + 1).Prime := by
  simp only [prothB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hk0, hk⟩, hpm⟩ := h
  set N := k * 2 ^ (m + 1) + 1 with hN
  apply proth hk0 hk rfl
  have he : k * 2 ^ m < 2 ^ (N.log2 + 1) := by
    have h1 : k * 2 ^ m < N := by rw [hN, pow_succ]; nlinarith [Nat.one_le_two_pow (n := m)]
    exact lt_trans h1 Nat.lt_log2_self
  rw [← pm_cast _ a _ N he, hpm]
  have hN1 : 1 ≤ N := by omega
  rw [Nat.cast_sub hN1]
  simp

end GoldbachLean.Saouter1998.Proth
