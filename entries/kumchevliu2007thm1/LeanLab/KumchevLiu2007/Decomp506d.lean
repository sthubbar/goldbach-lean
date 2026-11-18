module

public import LeanLab.KumchevLiu2007.Decomp506bBase

/-!
The local density in the sieve application on page 17 is multiplicative.
The proofs transport square roots through the Chinese remainder equivalence.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

-- Port fix for Mathlib v4.35.0-rc3: its instance making a simple nilpotent additive group
-- commutative is found for `ZMod p` under `Fact p.Prime` and blocks `ring` and `simp`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace LeanLab.KumchevLiu2007.Task506d

open Task506b
open scoped BigOperators

/-- Page 17, the full natural residue root count equals the root count in ZMod. -/
theorem root_count_zmod (n d : ℕ) [NeZero d] :
    ((Finset.range d).filter (fun x => x ^ 2 % d = n % d)).card =
      ((Finset.univ : Finset (ZMod d)).filter (fun x => x ^ 2 = (n : ZMod d))).card := by
  classical
  apply Finset.card_bij (fun (a : ℕ) _ => (a : ZMod d))
  · intro a ha
    obtain ⟨_, heq⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hh := (ZMod.natCast_eq_natCast_iff' (a ^ 2) n d).mpr heq
    simpa only [Nat.cast_pow] using hh
  · intro a ha b hb hab
    have hh := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha).1),
      Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)] using hh
  · intro a ha
    refine ⟨a.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt a), ?_⟩,
      ZMod.natCast_zmod_val a⟩
    apply (ZMod.natCast_eq_natCast_iff' (a.val ^ 2) n d).mp
    simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using (Finset.mem_filter.mp ha).2

/-- Page 17, CRT makes the square root count multiplicative at coprime positive moduli. -/
theorem root_count_coprime_mul (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    ((Finset.range (a * b)).filter (fun x => x ^ 2 % (a * b) = n % (a * b))).card =
      ((Finset.range a).filter (fun x => x ^ 2 % a = n % a)).card *
        ((Finset.range b).filter (fun x => x ^ 2 % b = n % b)).card := by
  classical
  haveI : NeZero a := ⟨ha.ne'⟩
  haveI : NeZero b := ⟨hb.ne'⟩
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero ha.ne' hb.ne'⟩
  rw [root_count_zmod, root_count_zmod, root_count_zmod, ← Finset.card_product]
  let e := ZMod.chineseRemainder hab
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    have hx2 := (Finset.mem_filter.mp hx).2
    have heq : (e x) ^ 2 = (n : ZMod a × ZMod b) := by
      simpa only [map_pow, map_natCast] using congrArg e hx2
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  · intro x hx y hy hxy
    exact e.injective hxy
  · intro x hx
    obtain ⟨hxa, hxb⟩ := Finset.mem_product.mp hx
    have hxa2 := (Finset.mem_filter.mp hxa).2
    have hxb2 := (Finset.mem_filter.mp hxb).2
    refine ⟨e.symm x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply x⟩
    apply e.injective
    simp only [map_pow, map_natCast, e.apply_symm_apply]
    exact Prod.ext hxa2 hxb2

/-- Page 17, the density at modulus zero is zero by the totalized quotient convention. -/
theorem density_zero (n : ℕ) : density n 0 = 0 := by
  simp [density]

/-- Page 17, the density at modulus one is one. -/
theorem density_one (n : ℕ) : density n 1 = 1 := by
  simp [density, Nat.mod_one]

/-- Page 17, the stated sieve density is multiplicative at coprime natural moduli. -/
theorem density_coprime_mul (n a b : ℕ) (hab : a.Coprime b) :
    density n (a * b) = density n a * density n b := by
  by_cases ha : a = 0
  · subst a
    simp [density_zero]
  by_cases hb : b = 0
  · subst b
    simp [density_zero]
  by_cases hna : n.Coprime a
  · by_cases hnb : n.Coprime b
    · have hnab : n.Coprime (a * b) := hna.mul_right hnb
      simp only [density, if_pos hna, if_pos hnb, if_pos hnab,
        root_count_coprime_mul n a b (by omega) (by omega) hab,
        Nat.totient_mul hab, Nat.cast_mul, div_mul_div_comm]
    · have hnab : ¬ n.Coprime (a * b) := by
        intro hh
        exact hnb (Nat.coprime_mul_iff_right.mp hh).2
      simp [density, hnb, hnab]
  · have hnab : ¬ n.Coprime (a * b) := by
      intro hh
      exact hna (Nat.coprime_mul_iff_right.mp hh).1
    simp [density, hna, hnab]

/-- Page 17, every sieve density is nonnegative. -/
theorem density_nonneg (n d : ℕ) : 0 ≤ density n d := by
  unfold density
  split_ifs <;> positivity

/-- Page 17, the prime density is bounded by two over p minus one. -/
theorem density_prime_le (n p : ℕ) (hp : p.Prime) :
    density n p ≤ 2 / ((p : ℝ) - 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  by_cases hcop : n.Coprime p
  · haveI : Fact p.Prime := ⟨hp⟩
    have hnot : ¬ p ∣ n := hp.coprime_iff_not_dvd.mp hcop.symm
    have hc : ((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card ≤ 2 := by
      rw [Task129s.root_count_range_eq p n hnot]
      exact Task129a.nonzero_square_roots_le_two p n
    rw [density, if_pos hcop, Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by linarith)
  · simp only [density, if_neg hcop]
    positivity

/-- Page 17, the numerical density packaged as an arithmetic function. -/
noncomputable def densityFunction (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨density n, density_zero n⟩

/-- Page 17, the density has the Mathlib multiplicative arithmetic function property. -/
theorem density_isMultiplicative (n : ℕ) : (densityFunction n).IsMultiplicative := by
  exact ⟨density_one n, fun {a b} hab => density_coprime_mul n a b hab⟩

/-- Page 17, at a prime the coprimality density equals the displayed divisibility formula. -/
theorem density_prime_eq (n p : ℕ) (hp : p.Prime) :
    density n p = if p ∣ n then 0 else
      (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) / Nat.totient p := by
  by_cases hdiv : p ∣ n
  · have hcop : ¬ n.Coprime p := fun hh => (hp.coprime_iff_not_dvd.mp hh.symm) hdiv
    simp [density, hdiv, hcop]
  · have hcop : n.Coprime p := (hp.coprime_iff_not_dvd.mpr hdiv).symm
    simp [density, hdiv, hcop]

/-- Page 17, the sieve density at two is zero for admissible n. -/
theorem density_two_of_InH2 (n : ℕ) (hn : InH2 n) : density n 2 = 0 := by
  rw [density_prime_eq n 2 (by decide), if_pos hn.2]

/-- Page 17, the sieve density at three is zero for admissible n. -/
theorem density_three_of_InH2 (n : ℕ) (hn : InH2 n) : density n 3 = 0 := by
  by_cases hdiv : 3 ∣ n
  · rw [density_prime_eq n 3 (by decide), if_pos hdiv]
  have hnmod : n % 3 = 2 := by
    have hh := Nat.mod_lt n (by norm_num : 0 < 3)
    have hh1 := hn.1
    rw [Nat.dvd_iff_mod_eq_zero] at hdiv
    omega
  have hc : ((Finset.range 3).filter (fun x => x ^ 2 % 3 = n % 3)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx
    have hx3 : x < 3 := Finset.mem_range.mp hx
    interval_cases x <;> norm_num [hnmod]
  rw [density_prime_eq n 3 (by decide), if_neg hdiv, hc]
  simp

/-- Page 13 hypothesis 43 and page 17, every prime density is strictly below one for n in H2. -/
theorem density_prime_lt_one (n p : ℕ) (hn : InH2 n) (hp : p.Prime) : density n p < 1 := by
  by_cases hp2 : p = 2
  · subst p
    rw [density_two_of_InH2 n hn]
    norm_num
  by_cases hp3 : p = 3
  · subst p
    rw [density_three_of_InH2 n hn]
    norm_num
  have hp4 : 4 ≤ p := by have hh := hp.two_le; omega
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp4
  apply (density_prime_le n p hp).trans_lt
  exact (div_lt_one (by linarith)).mpr (by linarith)

/-- Page 17 display 58, the sieve product is strictly positive for admissible n. -/
theorem sieveProduct_pos (X δ : ℝ) (n : ℕ) (hn : InH2 n) : 0 < sieveProduct X δ n := by
  classical
  unfold sieveProduct
  apply Finset.prod_pos
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2
  rw [← density_prime_eq n p hpp]
  exact sub_pos.mpr (density_prime_lt_one n p hn hpp)

end LeanLab.KumchevLiu2007.Task506d
