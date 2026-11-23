module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
Lucas certificates for the P0005 Table 4 and Table 8 record primes.
Extracted from Pratt.lean without the table import to break the import cycle.
AI wrote the Lean code. Binary Goldbach is open.
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

/-! ### 3325581707333960528 - 9781 = 3325581707333950747 -/

theorem p9930667 : Nat.Prime 9930667 := pB (by decide +kernel)

theorem p288128372339 : Nat.Prime 288128372339 := by
  refine pratt 288128372339 2 [(2, 1), (89, 1), (163, 1), (9930667, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p9930667

theorem prime_nRec_sub_literal : Nat.Prime 3325581707333950747 := by
  show Nat.Prime 3325581707333950747
  refine pratt 3325581707333950747 2 [(2, 1), (3, 5), (11, 1), (17, 1), (127, 1), (288128372339, 1)]
    (by norm_num) (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p288128372339

/-! ### The gap ends 1425172824437699411 and 1425172824437700887 -/

theorem p655664866807 : Nat.Prime 655664866807 := by
  refine pratt 655664866807 3 [(2, 1), (3, 1), (23, 1), (1801, 1), (2638087, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three
  all_goals exact pB (by decide +kernel)

theorem pGap_prime_lo_literal : Nat.Prime 1425172824437699411 := by
  show Nat.Prime 1425172824437699411
  refine pratt 1425172824437699411 2 [(2, 1), (5, 1), (655664866807, 1), (217363, 1)]
    (by norm_num) (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact pB (by decide +kernel)
  · exact p655664866807
  · exact pB (by decide +kernel)

theorem p712586412218850443 : Nat.Prime 712586412218850443 := by
  refine pratt 712586412218850443 2
    [(2, 1), (7, 1), (13, 1), (251, 1), (6631939, 1), (2352079, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  all_goals exact pB (by decide +kernel)

theorem pGap_prime_hi_literal : Nat.Prime 1425172824437700887 := by
  show Nat.Prime 1425172824437700887
  refine pratt 1425172824437700887 5 [(2, 1), (712586412218850443, 1)]
    (by norm_num) (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact Nat.prime_two
  · exact p712586412218850443

end LeanLab.Verifications.Pratt
