module

public import Mathlib

/-!
# Erdős 1950: an arithmetic progression of odd numbers none of which is `p + 2^k`

Lab proof, unit U-5604, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics,
P. Erdős, On integers of the form 2^k + p and some related problems, Summa Brasil. Math. 2, 1950,
with his covering `{0 mod 2, 0 mod 3, 1 mod 4, 3 mod 8, 7 mod 12, 23 mod 24}` and the primes
3, 7, 5, 17, 13, 241, all dividing `2^24 - 1`. The extra condition `31 ∣ n` keeps `n - q` off the
powers of 2 for the six covering primes `q`, so `n - 2^k` is never the covering prime itself.
Residues from numerics/erdos_cover.py. The companion of `romanov`: the numbers `p + 2^k` have
positive lower density, and a positive proportion of odd numbers is not of that form.
Binary Goldbach is OPEN; this is the Linnik-Goldbach line.

* `erdos_odd_not_sum`: every `n = 119477317 + 346729110 t` is odd and not `p + 2^k`, PROVED.
* `erdos_infinite`: infinitely many odd numbers are not `p + 2^k`, PROVED.
-/

@[expose] public section


namespace LeanLab.Romanov

/-- The covering prime for `k mod 24`. -/
def qOf (r : ℕ) : ℕ :=
  if r % 2 = 0 then 3 else if r % 3 = 0 then 7 else if r % 4 = 1 then 5 else
    if r % 8 = 3 then 17 else if r % 12 = 7 then 13 else 241

lemma qOf_facts : ∀ r < 24, 119477317 % qOf r = 2 ^ r % qOf r ∧ qOf r ∣ 16777215 ∧
    qOf r ∣ 346729110 ∧ 2 ≤ qOf r := by decide

lemma qOf_mod31 : ∀ r < 24, ∀ j < 5, (qOf r + 2 ^ j) % 31 ≠ 0 := by decide

lemma pow_modEq_24 (k : ℕ) : 2 ^ k ≡ 2 ^ (k % 24) [MOD 16777215] := by
  conv_lhs => rw [← Nat.mod_add_div k 24, pow_add, pow_mul]
  have h : 2 ^ 24 ≡ 1 [MOD 16777215] := by decide
  simpa using (Nat.ModEq.refl (2 ^ (k % 24))).mul (h.pow (k / 24))

lemma pow_modEq_5 (k : ℕ) : 2 ^ k ≡ 2 ^ (k % 5) [MOD 31] := by
  conv_lhs => rw [← Nat.mod_add_div k 5, pow_add, pow_mul]
  have h : 2 ^ 5 ≡ 1 [MOD 31] := by decide
  simpa using (Nat.ModEq.refl (2 ^ (k % 5))).mul (h.pow (k / 5))

/-- **Erdős 1950.** -/
theorem erdos_odd_not_sum (t : ℕ) :
    Odd (119477317 + 346729110 * t) ∧
      ∀ p k : ℕ, p.Prime → 119477317 + 346729110 * t ≠ p + 2 ^ k := by
  refine ⟨?_, fun p k hp h => ?_⟩
  · have : Odd (119477317 : ℕ) := by decide
    exact this.add_even ((by decide : Even (346729110 : ℕ)).mul_right t)
  have hr := Nat.mod_lt k (by norm_num : 24 > 0)
  obtain ⟨hres, hq, hqM, hq2⟩ := qOf_facts (k % 24) hr
  set q := qOf (k % 24)
  -- `p + 2^(k mod 24) ≡ 2^(k mod 24) [MOD q]`
  have hkq : 2 ^ k ≡ 2 ^ (k % 24) [MOD q] := Nat.ModEq.of_dvd hq (pow_modEq_24 k)
  have hn : 119477317 + 346729110 * t ≡ 119477317 [MOD q] := by
    have : 346729110 * t ≡ 0 [MOD q] :=
      Nat.modEq_zero_iff_dvd.2 (Dvd.dvd.mul_right hqM t)
    simpa using (Nat.ModEq.refl 119477317).add this
  have h1 : p + 2 ^ (k % 24) ≡ 0 + 2 ^ (k % 24) [MOD q] := by
    calc p + 2 ^ (k % 24) ≡ p + 2 ^ k [MOD q] := (Nat.ModEq.refl p).add hkq.symm
      _ = 119477317 + 346729110 * t := h.symm
      _ ≡ 119477317 [MOD q] := hn
      _ ≡ 0 + 2 ^ (k % 24) [MOD q] := by rw [zero_add]; exact hres
  have hpq : q ∣ p := Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_right_cancel' _ h1)
  have hqp : q = p := ((Nat.dvd_prime hp).1 hpq).resolve_left (by omega)
  -- then `q + 2^k = n ≡ 0 [MOD 31]`
  have h31 : q + 2 ^ (k % 5) ≡ 0 [MOD 31] := by
    have hn31 : 119477317 + 346729110 * t ≡ 0 [MOD 31] := by
      have : 346729110 * t ≡ 0 [MOD 31] :=
        Nat.modEq_zero_iff_dvd.2 (Dvd.dvd.mul_right (by norm_num) t)
      simpa using (show 119477317 ≡ 0 [MOD 31] by decide).add this
    calc q + 2 ^ (k % 5) ≡ q + 2 ^ k [MOD 31] := (Nat.ModEq.refl q).add (pow_modEq_5 k).symm
      _ = 119477317 + 346729110 * t := by rw [hqp]; exact h.symm
      _ ≡ 0 [MOD 31] := hn31
  exact qOf_mod31 (k % 24) hr (k % 5) (Nat.mod_lt k (by norm_num)) h31

/-- Infinitely many odd numbers are not of the form `p + 2^k`. -/
theorem erdos_infinite :
    {n : ℕ | Odd n ∧ ∀ p k : ℕ, p.Prime → n ≠ p + 2 ^ k}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun t => 119477317 + 346729110 * t)
    (fun a b hab => by simp only at hab; omega) fun t => erdos_odd_not_sum t

end LeanLab.Romanov
