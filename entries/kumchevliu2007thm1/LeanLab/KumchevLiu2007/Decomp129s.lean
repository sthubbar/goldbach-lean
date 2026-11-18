module

public import LeanLab.KumchevLiu2007.Decomp129a

/-!
Kumchev and Liu, arXiv 0801.0130, paper P0088. Route burst session 8 p3, 2026-11-12.
Upstream helper file for `Decomp129`: page 17 display 59 for j equal to 2,
with the products written out, since `sieveV` and `partialProduct2` live in
`Decomp129`, which imports this file.

The local identity used is exact: for every prime p and every n,
1 - g(p) = (1 + A2(n, p)) (1 - 1/p), with A2 computed from its definition by
`Task129a.A2_prime_root_count`. It does not use the sign printed in display 46
on page 14, see the QUESTION in the burst note. The Mertens step is the
elementary bound, product of 1 - 1/p over p at most Q at most 1/log Q, proved
through the Euler product and the harmonic sum. The two Mertens lemmas are
copies of `AlmostPrimes.Decomp1528b.harmonic_mul_prod_le` and
`mertens_prod_upper`, copied to avoid a long import chain.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

-- Port fix for Mathlib v4.35.0-rc3: its instance making a simple nilpotent additive group
-- commutative is found for `ZMod p` under `Fact p.Prime` and blocks `ring` and `simp`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace LeanLab.KumchevLiu2007.Task129s

open Real Complex LeanLab.KumchevLiu2007
open U1534 Task129a
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Elementary Mertens, Euler product form: the harmonic number H_N times the
product of 1 - 1/p over primes p at most N is at most 1. Copy of
`AlmostPrimes.Decomp1528b.harmonic_mul_prod_le`. -/
theorem harmonic_mul_prod_le (N : ℕ) :
    (harmonic N : ℝ) * ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) ≤ 1 := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ)⁻¹
      map_one' := by simp
      map_mul' := by intro a b; simp [mul_comm] }
  have hsmall : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hseries := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := f) hsmall (Nat.primesLE N)
  have hfilter : (Nat.primesLE N).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp [Nat.mem_primesLE]
  have hmem : ∀ n ∈ Finset.Icc 1 N, n ∈ Nat.factoredNumbers (Nat.primesLE N) := by
    intro n hn
    rw [Nat.mem_factoredNumbers_iff_forall_le]
    refine ⟨by have := (Finset.mem_Icc.mp hn).1; omega, ?_⟩
    intro p hpn hp _
    exact Nat.mem_primesLE.mpr ⟨le_trans hpn (Finset.mem_Icc.mp hn).2, hp⟩
  have hsum := sum_le_hasSum
    ((Finset.Icc 1 N).subtype (fun n => n ∈ Nat.factoredNumbers (Nat.primesLE N)))
    (fun n _ => show 0 ≤ f n by dsimp [f]; positivity) hseries.2
  rw [hfilter] at hsum
  have hH : (harmonic N : ℝ) ≤ ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p)⁻¹ := by
    change (∑ n ∈ (Finset.Icc 1 N).subtype (fun n => n ∈ Nat.factoredNumbers (Nat.primesLE N)),
      ((n : ℕ) : ℝ)⁻¹) ≤ ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)⁻¹ at hsum
    rw [Finset.sum_subtype_of_mem (fun n : ℕ => (n : ℝ)⁻¹) hmem] at hsum
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
      using hsum
  have hP : 0 < ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) := by
    apply Finset.prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    exact sub_pos.mpr ((div_lt_one hp0).2 hp1)
  rw [Finset.prod_inv_distrib] at hH
  calc (harmonic N : ℝ) * ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p)
      ≤ (∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p))⁻¹ *
          ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) :=
        mul_le_mul_of_nonneg_right hH hP.le
    _ = 1 := inv_mul_cancel₀ hP.ne'

/-- Elementary Mertens product upper bound, the product of 1 - 1/p over primes
p at most x is at most 1/log x for real x at least 2. This is the Mertens step
in page 17 display 59. Copy of `AlmostPrimes.Decomp1528b.mertens_prod_upper`. -/
theorem mertens_prod_upper {x : ℝ} (hx : 2 ≤ x) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (1 : ℝ) / p) ≤ 1 / Real.log x := by
  set N := ⌊x⌋₊
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hl1 : Real.log x ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
    push_cast; exact Real.log_le_log (by linarith) hxN.le
  have hH := log_add_one_le_harmonic N
  have hP := harmonic_mul_prod_le N
  have hP0 : 0 ≤ ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  rw [le_div_iff₀ hlx]
  have : Real.log x * ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) ≤
      (harmonic N : ℝ) * ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) :=
    mul_le_mul_of_nonneg_right (le_trans hl1 hH) hP0
  linarith

/-- Page 17, definition of r(p) and g(p): the number of x in 0, ..., p - 1 with
x squared congruent to n mod p equals the number of nonzero residues x with
x squared = n in ZMod p, when p does not divide n. -/
theorem root_count_range_eq (p : ℕ) [Fact p.Prime] (n : ℕ) (hpn : ¬ p ∣ n) :
    ((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card =
      ((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).card := by
  have hp : p.Prime := Fact.out
  apply Finset.card_bij (fun (a : ℕ) _ => (a : ZMod p))
  · intro a ha
    obtain ⟨_, h⟩ := Finset.mem_filter.mp ha
    have hc : ((a ^ 2 : ℕ) : ZMod p) = (n : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff' (a ^ 2) n p).mpr h
    push_cast at hc
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, hc⟩
    intro h0
    apply hpn
    have h2 : ((a : ZMod p)) ^ 2 = 0 := by rw [h0]; ring
    rw [hc] at h2
    exact (ZMod.natCast_eq_zero_iff n p).mp h2
  · intro a ha b hb hab
    have h := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha).1),
      Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)] using h
  · intro b hb
    have hb2 := (Finset.mem_filter.mp hb).2
    refine ⟨b.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt b), ?_⟩,
      ZMod.natCast_zmod_val b⟩
    apply (ZMod.natCast_eq_natCast_iff' (b.val ^ 2) n p).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hb2

/-- When p divides n there is no nonzero x in ZMod p with x squared = n. -/
theorem root_count_dvd_eq_zero (p : ℕ) [Fact p.Prime] (n : ℕ) (hpn : p ∣ n) :
    ((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hx2
  have hn : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
  rw [hn] at hx2
  exact (Finset.mem_erase.mp hx).1 (pow_eq_zero_iff (by norm_num) |>.mp hx2)

/-- Page 17, display 59, first step, at one prime, made exact: comparing the
definition of g with A2. For every prime p and every n, with the density g(p)
of page 17 written out, 1 - g(p) = |1 + A2(n, p)| (1 - 1/p). The factor
1 + A2(n, p) is real and nonnegative, equal to p (p - 1 - rho) / (p - 1)^2 with
rho the nonzero square root count of n mod p, by `Task129a.A2_prime_root_count`. -/
theorem one_sub_density_eq (p : ℕ) (hp : p.Prime) (n : ℕ) :
    1 - (if p ∣ n then (0 : ℝ) else
      (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) / (Nat.totient p : ℝ)) =
      ‖1 + A2 n p‖ * (1 - 1 / (p : ℝ)) := by
  have : Fact p.Prime := ⟨hp⟩
  set ρ := ((Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))).card
    with hρ
  have hdens : (if p ∣ n then (0 : ℝ) else
      (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) / (Nat.totient p : ℝ)) =
      (ρ : ℝ) / ((p : ℝ) - 1) := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
    split_ifs with h
    · rw [hρ, root_count_dvd_eq_zero p n h]; simp
    · rw [root_count_range_eq p n h]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hρle : (ρ : ℝ) ≤ (p : ℝ) - 1 := by
    have h1 : ρ ≤ (Finset.univ.erase (0 : ZMod p)).card := Finset.card_filter_le _ _
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at h1
    have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [← this]; exact_mod_cast h1
  have hA : 1 + A2 n p = (((p : ℝ) * ((p : ℝ) - 1 - ρ) / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ) := by
    rw [A2_prime_root_count]
    have hne : ((p : ℂ) - 1) ≠ 0 := by
      have : ((p : ℂ) - 1) = (((p : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast hp1.ne'
    push_cast
    field_simp
    ring
  rw [hdens, hA, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by apply div_nonneg <;> nlinarith)]
  field_simp

/-- Page 17 display 59 for j = 2, with sieveV and P2(n, z) written out:
the product of 1 - g(p) over primes p at most Q is at most |P2(n, Q)| / log Q
for Q at least 2. The paper's first step, comparing g with A2 through display 46,
is here an equality prime by prime, `one_sub_density_eq`; the second step is
Mertens' product, `mertens_prod_upper`. PROVED with constant 1. -/
theorem sieve_product_explicit (Q : ℝ) (hQ : 2 ≤ Q) (n : ℕ) :
    ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime,
      (1 - (if p ∣ n then (0 : ℝ) else
        (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) /
          (Nat.totient p : ℝ))) ≤
      1 * ‖∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime, (1 + A2 n p)‖ / Real.log Q := by
  set S := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime with hS
  have hfac : ∏ p ∈ S, (1 - (if p ∣ n then (0 : ℝ) else
        (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) /
          (Nat.totient p : ℝ))) =
      (∏ p ∈ S, ‖1 + A2 n p‖) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    exact one_sub_density_eq p (Finset.mem_filter.mp hp).2 n
  have hM : ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ 1 / Real.log Q := mertens_prod_upper hQ
  have hnorm : ‖∏ p ∈ S, (1 + A2 n p)‖ = ∏ p ∈ S, ‖1 + A2 n p‖ := Complex.norm_prod _ _
  rw [hfac, ← hnorm, one_mul, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left hM (norm_nonneg _)

end LeanLab.KumchevLiu2007.Task129s
