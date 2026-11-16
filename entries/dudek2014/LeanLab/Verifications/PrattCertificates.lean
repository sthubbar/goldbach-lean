module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
Lucas certificates for primality: a binary modular power proved equal to `ZMod`
exponentiation, and Lucas' test with a listed factorization of `p - 1`.
AI wrote the Lean code.
-/

@[expose] public section

namespace LeanLab.Verifications.Pratt

/-- Binary modular power with fuel. -/
def pm : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 1
  | fuel + 1, a, e, m =>
    if e = 0 then 1 % m else
      let h := pm fuel a (e / 2) m
      if e % 2 = 1 then h * h % m * a % m else h * h % m

theorem pm_cast : ∀ fuel a e m, e < 2 ^ fuel → ((pm fuel a e m : ℕ) : ZMod m) = (a : ZMod m) ^ e := by
  intro fuel
  induction fuel with
  | zero => intro a e m he; simp at he; subst he; simp [pm]
  | succ k ih =>
    intro a e m he
    simp only [pm]
    by_cases h0 : e = 0
    · subst h0; simp
    · rw [if_neg h0]
      have hlt : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
      have IH := ih a (e / 2) m hlt
      have he2 : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1]
        simp only [Nat.cast_mul, ZMod.natCast_mod, IH]
        conv_rhs => rw [he2, h1, pow_add, pow_mul, pow_one]
        ring
      · rw [if_neg h1]
        have h1' : e % 2 = 0 := by omega
        simp only [Nat.cast_mul, ZMod.natCast_mod, IH]
        conv_rhs => rw [he2, h1', add_zero, pow_mul]
        ring

/-- Lucas' test with a listed factorization of `p - 1`. -/
theorem pratt (p a : ℕ) (L : List (ℕ × ℕ)) (hp : p < 2 ^ 64)
    (hprod : (L.map fun x => x.1 ^ x.2).prod = p - 1) (hprimes : ∀ x ∈ L, x.1.Prime)
    (hpow : pm 64 a (p - 1) p = 1 % p)
    (hnot : ∀ x ∈ L, pm 64 a ((p - 1) / x.1) p % p ≠ 1 % p) : p.Prime := by
  apply lucas_primality p (a : ZMod p)
  · rw [← pm_cast 64 a (p - 1) p (by omega), hpow]
    simp
  · intro q hq hqd heq
    rw [← hprod] at hqd
    obtain ⟨y, hy, hyd⟩ := (Nat.prime_iff.mp hq).dvd_prod_iff.mp hqd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hqx : q = x.1 :=
      (Nat.prime_dvd_prime_iff_eq hq (hprimes x hx)).mp (hq.dvd_of_dvd_pow hyd)
    subst hqx
    apply hnot x hx
    have h2 : (p - 1) / x.1 < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    rw [← pm_cast 64 a _ p h2] at heq
    have := (ZMod.natCast_eq_natCast_iff' _ 1 p).mp (by rw [heq]; simp)
    simpa using this

theorem pB {n : ℕ} (h : primeB n = true) : n.Prime := primeB_sound h

/-- Lucas' test with a listed factorization of `p - 1`, with the two power conditions stated in
`ZMod p`. Each power is then proved by `reduce_mod_char`, whose fast modular exponentiation
emits small explicit squaring steps, so no kernel has to run a large decision procedure. -/
theorem prattZ (p a : ℕ) (L : List (ℕ × ℕ))
    (hprod : (L.map fun x => x.1 ^ x.2).prod = p - 1) (hprimes : ∀ x ∈ L, x.1.Prime)
    (hpow : (a : ZMod p) ^ (p - 1) = 1)
    (hnot : ∀ x ∈ L, (a : ZMod p) ^ ((p - 1) / x.1) ≠ 1) : p.Prime := by
  apply lucas_primality p (a : ZMod p) hpow
  intro q hq hqd
  rw [← hprod] at hqd
  obtain ⟨y, hy, hyd⟩ := (Nat.prime_iff.mp hq).dvd_prod_iff.mp hqd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  have hqx : q = x.1 :=
    (Nat.prime_dvd_prime_iff_eq hq (hprimes x hx)).mp (hq.dvd_of_dvd_pow hyd)
  subst hqx
  exact hnot x hx

/-- A residue computed to be `c` with `c % p ≠ 1` is not `1` in `ZMod p`. -/
theorem zmod_ne_one {p c : ℕ} (hp : 1 < p) (hc : c % p ≠ 1) {x : ZMod p}
    (hx : x = (c : ZMod p)) : x ≠ 1 := by
  subst hx
  intro h
  apply hc
  have h1 : ((c : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h
  rw [ZMod.natCast_eq_natCast_iff'] at h1
  rwa [Nat.mod_eq_of_lt hp] at h1

end LeanLab.Verifications.Pratt
