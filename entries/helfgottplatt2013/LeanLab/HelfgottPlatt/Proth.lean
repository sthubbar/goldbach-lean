module

public import Mathlib

/-!
Helfgott and Platt 2013, P0006, unit U-0950, run 20261018T1404Z-22216.
Theorem 2.3 of the paper, Proth's theorem, the direction the computation uses: if
N = k 2^n + 1 with 0 < k < 2^n and a^((N-1)/2) = -1 mod N, then N is prime.
The Jacobi symbol condition in the paper's display only guides the choice of a; it is not
needed for primality, so it is left out here, which makes the statement stronger.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.

This file is an extract of the lab file `LeanLab/HelfgottPlatt/Proth.lean`: it keeps `proth`
and the paper's bound `T`, and drops the Boolean test `prothB`, its soundness lemma and the
certificate of a Proth prime just below `T`, which no compared theorem uses; with them went
the lab import `LeanLab.Verifications.Pratt`. Four steps of `proth` were rewritten for Mathlib
v4.35.0-rc3, where `ring`, `norm_num` and `linear_combination` do not close `1 + -1 = 0` in
`ZMod p` under `Fact p.Prime`; the statement is unchanged.
-/

@[expose] public section

namespace LeanLab.HelfgottPlatt.Proth

/-- Proth's theorem, sufficiency, paper Theorem 2.3. -/
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
    rw [map_pow, map_natCast, map_neg, map_one] at h
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
    exact hne (by
      have : (0 : ZMod p) = -1 := hcm
      have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
      exact absurd (neg_eq_zero.mp this.symm) h1)
  have hdvd : 2 ^ (m + 1) ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hc0
  have hp1 : 2 ^ (m + 1) + 1 ≤ p := by
    have := Nat.le_of_dvd (by have := hpp.two_le; omega) hdvd
    omega
  have : (2 ^ (m + 1) + 1) ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left hp1 2) hsq
  rw [hN] at this
  nlinarith

/-- The paper's bound, Theorem 4.1. -/
def T : ℕ := 8875694145621773516800000000000

end LeanLab.HelfgottPlatt.Proth
