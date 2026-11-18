module

public import LeanLab.KumchevLiu2007.Decomp506b

/-!
Truncated window Bombieri Vinogradov remainder bound for Kumchev and Liu, arXiv 0801.0130,
paper P0088, pages 16 and 17, displays 56 to 58.
The semiprime sequence of page 16 is cut from below at a real number a between
sqrt Y / 2 and sqrt Y, and the prime to semiprime transfer of page 17 is rerun on the
truncated sequence. The error terms are the same maximal prime errors as in the
untruncated transfer of Decomp542a, so the final bound has the same shape.
This file adapts Decomp542a, `progressionCount_factor_sum` through
`bv_remainder_from_maximal`, and adds no definition.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Trunc129

open Real LeanLab.KumchevLiu2007 Task506b Task542a
open scoped BigOperators Topology

/-- Page 17 between displays 57 and 58, truncated window version: the truncated semiprime
progression count is the exact sum over its smaller prime of the truncated factor counts. -/
theorem trunc_count_factor_sum (X B ε a : ℝ) (n d : ℕ) :
    ((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter
        (fun q => d ∣ n - q ^ 2)).card : ℝ) =
      ∑ p ∈ primeWindow X B ε,
        ((((factorPrimes X ε p).filter (fun r : ℕ => a ≤ ((p * r : ℕ) : ℝ))).filter
          (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card : ℝ) := by
  classical
  let S := (primeWindow X B ε).sigma (fun p : ℕ =>
    ((factorPrimes X ε p).filter (fun r : ℕ => a ≤ ((p * r : ℕ) : ℝ))).filter
      (fun r : ℕ => d ∣ n - (p * r) ^ 2))
  have hcard : S.card = (((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter
      (fun q => d ∣ n - q ^ 2)).card := by
    apply Finset.card_bij (fun v _ => v.1 * v.2)
    · intro v hv
      obtain ⟨hp, hr⟩ := Finset.mem_sigma.mp hv
      obtain ⟨hrA, hdiv⟩ := Finset.mem_filter.mp hr
      obtain ⟨hrF, hcut⟩ := Finset.mem_filter.mp hrA
      obtain ⟨hrange, hrp, hpr, hlo, hhi⟩ := Finset.mem_filter.mp hrF
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hlo, hhi,
        v.1, hp, v.2, hrp, hpr, rfl⟩, hcut⟩, hdiv⟩
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hhi.le))
    · intro v hv w hw heq
      obtain ⟨hp, hr⟩ := Finset.mem_sigma.mp hv
      obtain ⟨hq, hs⟩ := Finset.mem_sigma.mp hw
      have hrf := (Finset.mem_filter.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1).2
      have hsf := (Finset.mem_filter.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1).2
      have hh := ordered_prime_products_injective v.1 v.2 w.1 w.2
        (Finset.mem_filter.mp hp).2.1 hrf.1 (Finset.mem_filter.mp hq).2.1 hsf.1
        hrf.2.1 hsf.2.1 heq
      exact Sigma.ext hh.1 (heq_of_eq hh.2)
    · intro q hq
      obtain ⟨hqA, hdiv⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqsem, hcut⟩ := Finset.mem_filter.mp hqA
      obtain ⟨hqrange, hlo, hhi, p, hp, r, hr, hpr, heq⟩ := Finset.mem_filter.mp hqsem
      have hp1 := (Finset.mem_filter.mp hp).2.1.one_le
      have hrq : r ≤ q := by rw [heq]; nlinarith
      have hrange : r ∈ Finset.range (⌊Real.sqrt (Y X ε)⌋₊ + 1) :=
        Finset.mem_range.mpr (hrq.trans_lt (Finset.mem_range.mp hqrange))
      refine ⟨⟨p, r⟩, Finset.mem_sigma.mpr ⟨hp, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hrange, hr, hpr, ?_, ?_⟩, ?_⟩, ?_⟩⟩,
        heq.symm⟩
      · simpa only [← heq] using hlo
      · simpa only [← heq] using hhi
      · simpa only [← heq] using hcut
      · simpa only [← heq] using hdiv
  have hh := congrArg (fun k : ℕ => (k : ℝ)) hcard
  rw [Finset.card_sigma] at hh
  simpa only [Nat.cast_sum] using hh.symm

/-- Page 16 before display 56, truncated window version: the truncated factor counts in a
residue class equal the prime count in the half open interval from max (jlo) (a / p) to
sqrt Y / p, written with the clamped upper endpoint. -/
theorem trunc_factor_residue_eq_intervalAP (X B ε a : ℝ) (p d c : ℕ)
    (hp : p ∈ primeWindow X B ε) (hY : 0 < Y X ε) :
    ((((factorPrimes X ε p).filter (fun r : ℕ => a ≤ ((p * r : ℕ) : ℝ))).filter
        (fun r : ℕ => r % d = c % d)).card : ℝ) =
      intervalAP (max (jlo X ε p) (a / p))
        (max (max (jlo X ε p) (a / p)) (jhi X ε p)) d c := by
  classical
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
  have hT := jhi_eq_prime_endpoint X B ε p hp hY
  have hTroot : Real.sqrt (Y X ε) / p ≤ Real.sqrt (Y X ε) := by
    apply (div_le_iff₀ hp0).mpr
    nlinarith [Real.sqrt_nonneg (Y X ε)]
  unfold intervalAP
  congr 1
  apply congrArg Finset.card
  ext r
  constructor
  · intro hr
    obtain ⟨hrA, hmod⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrF, hcut⟩ := Finset.mem_filter.mp hrA
    obtain ⟨hrange, hrp, hpr, hlo, hhi⟩ := Finset.mem_filter.mp hrF
    have hrlo : jlo X ε p ≤ (r : ℝ) := by
      apply max_le (by exact_mod_cast hpr)
      apply (div_le_iff₀ (by positivity : 0 < 2 * (p : ℝ))).mpr
      push_cast at hlo
      nlinarith
    have hrcut : a / p ≤ (r : ℝ) := by
      apply (div_le_iff₀ hp0).mpr
      push_cast at hcut
      linarith
    have hrhi : (r : ℝ) < jhi X ε p := by
      rw [hT]
      apply (lt_div_iff₀ hp0).mpr
      simpa only [Nat.cast_mul, mul_comm] using hhi
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hrp.pos, Nat.le_floor (hrhi.le.trans (le_max_right _ _))⟩,
        hrp, hmod⟩, max_le hrlo hrcut, hrhi.trans_le (le_max_right _ _)⟩
  · intro hr
    obtain ⟨hrI, hrlo, hrhi⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrange, hrp, hmod⟩ := Finset.mem_filter.mp hrI
    have hrj : jlo X ε p ≤ (r : ℝ) := (le_max_left _ _).trans hrlo
    have hrc : a / p ≤ (r : ℝ) := (le_max_right _ _).trans hrlo
    have hrhi' : (r : ℝ) < jhi X ε p := by
      rcases lt_max_iff.mp hrhi with h | h
      · exact absurd h (not_lt.mpr hrlo)
      · exact h
    have hpr : p ≤ r := by exact_mod_cast ((le_max_left _ _).trans hrj : (p : ℝ) ≤ r)
    have hrT : (r : ℝ) < Real.sqrt (Y X ε) / p := by rwa [hT] at hrhi'
    have hbound : r ∈ Finset.range (⌊Real.sqrt (Y X ε)⌋₊ + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor (hrT.le.trans hTroot)))
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hbound, hrp, hpr, ?_, ?_⟩, ?_⟩, hmod⟩
    · have hh : Real.sqrt (Y X ε) / (2 * p) ≤ (r : ℝ) := (le_max_right _ _).trans hrj
      have hh' := (div_le_iff₀ (by positivity : 0 < 2 * (p : ℝ))).mp hh
      push_cast
      nlinarith
    · have hh := (lt_div_iff₀ hp0).mp hrT
      simpa only [Nat.cast_mul, mul_comm] using hh
    · have hh := (div_le_iff₀ hp0).mp hrc
      push_cast
      linarith

/-- Page 17 between displays 57 and 58, truncated window version, stated for an arbitrary
finite set of larger primes: split the fixed smaller prime progression count by its root
residue. -/
theorem finset_progression_residues (F : Finset ℕ) (p n d : ℕ) [NeZero d]
    (hsmall : ∀ r ∈ F, (p * r) ^ 2 ≤ n) :
    (F.filter (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card =
      ∑ c ∈ twistedRoots p n d, (F.filter (fun r : ℕ => (r : ZMod d) = c)).card := by
  classical
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro r hr
  have hiff : d ∣ n - (p * r) ^ 2 ↔
      (((p * r) ^ 2 : ℕ) : ZMod d) = (n : ZMod d) :=
    (Nat.modEq_iff_dvd' (hsmall r hr)).symm.trans
      (ZMod.natCast_eq_natCast_iff' ((p * r) ^ 2) n d).symm
  simpa only [twistedRoots, Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.cast_pow, Nat.cast_mul] using hiff

/-- Page 17 between displays 57 and 58, truncated window version: a residue fiber of the
truncated larger prime count is the corresponding prime count in the truncated interval. -/
theorem trunc_factor_residue_cast_eq (X B ε a : ℝ) (p d : ℕ) [NeZero d]
    (hp : p ∈ primeWindow X B ε) (hY : 0 < Y X ε) (c : ZMod d) :
    ((((factorPrimes X ε p).filter (fun r : ℕ => a ≤ ((p * r : ℕ) : ℝ))).filter
        (fun r : ℕ => (r : ZMod d) = c)).card : ℝ) =
      intervalAP (max (jlo X ε p) (a / p))
        (max (max (jlo X ε p) (a / p)) (jhi X ε p)) d c.val := by
  rw [← trunc_factor_residue_eq_intervalAP X B ε a p d c.val hp hY]
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro r hr
  have hh := ZMod.natCast_eq_natCast_iff' r c.val d
  simpa only [ZMod.natCast_zmod_val] using hh

/-- Page 17 between displays 57 and 58, truncated window version: the finite prime to
semiprime transfer at a coprime squarefree modulus, for the truncated factor set. The error
is the maximal prime error at sqrt Y / p, which covers every sub interval. -/
theorem trunc_factor_progression_error_coprime (X B ε a : ℝ) (p n d : ℕ) [NeZero d]
    (hp : p ∈ primeWindow X B ε) (hY : 0 < Y X ε) (ha : a ≤ Real.sqrt (Y X ε))
    (hpd : Nat.Coprime p d) (hd : Squarefree d) (hnd : Nat.Coprime n d)
    (hsmall : ∀ r ∈ (factorPrimes X ε p).filter (fun r : ℕ => a ≤ ((p * r : ℕ) : ℝ)),
      (p * r) ^ 2 ≤ n)
    (hT : 2 ≤ Real.sqrt (Y X ε) / p)
    (hL : 1 ≤ Real.log (Real.sqrt (Y X ε) / p))
    (hdT : (d : ℝ) ≤ Real.sqrt (Y X ε) / p) :
    |((((factorPrimes X ε p).filter (fun r : ℕ => a ≤ ((p * r : ℕ) : ℝ))).filter
        (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card : ℝ) -
      density n d * (∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
        1 / Real.log u)| ≤
      (d.divisors.card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hjlo : 2 ≤ jlo X ε p :=
    (by exact_mod_cast hpp.two_le : (2 : ℝ) ≤ p).trans (le_max_left _ _)
  have hlo : 2 ≤ max (jlo X ε p) (a / p) := hjlo.trans (le_max_left _ _)
  have hhiT : jhi X ε p = Real.sqrt (Y X ε) / p := jhi_eq_prime_endpoint X B ε p hp hY
  have hjj : jlo X ε p ≤ jhi X ε p := le_max_left _ _
  have hhi : max (max (jlo X ε p) (a / p)) (jhi X ε p) ≤ Real.sqrt (Y X ε) / p :=
    max_le (max_le (hjj.trans hhiT.le) (div_le_div_of_nonneg_right ha hp0.le)) hhiT.le
  have hclass (c : ZMod d) (hc : c ∈ twistedRoots p n d) :
      |intervalAP (max (jlo X ε p) (a / p))
          (max (max (jlo X ε p) (a / p)) (jhi X ε p)) d c.val -
        (∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
          1 / Real.log u) / Nat.totient d| ≤
        2 * primeError (Real.sqrt (Y X ε) / p) d + 2 :=
    intervalAP_error (Real.sqrt (Y X ε) / p) _ _ d c.val hT hL hd0 hdT (ZMod.val_lt c)
      (twistedRoots_coprime p n d hnd c hc) hlo (le_max_left _ _) hhi
  have hpart : ((((factorPrimes X ε p).filter (fun r : ℕ => a ≤ ((p * r : ℕ) : ℝ))).filter
        (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card : ℝ) =
      ∑ c ∈ twistedRoots p n d, intervalAP (max (jlo X ε p) (a / p))
        (max (max (jlo X ε p) (a / p)) (jhi X ε p)) d c.val := by
    rw [finset_progression_residues _ p n d hsmall, Nat.cast_sum]
    exact Finset.sum_congr rfl
      (fun c _ => trunc_factor_residue_cast_eq X B ε a p d hp hY c)
  have hmain : density n d *
      (∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
        1 / Real.log u) =
      ∑ c ∈ twistedRoots p n d,
        (∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
          1 / Real.log u) / Nat.totient d := by
    rw [Finset.sum_const, nsmul_eq_mul, twistedRoots_card p n d hpd]
    simp only [density, ite_eq_left hnd]
    ring
  have hnn : 0 ≤ 2 * primeError (Real.sqrt (Y X ε) / p) d + 2 := by
    have h := primeError_nonneg (Real.sqrt (Y X ε) / p) d hT hL hd0 hdT
    linarith
  rw [hpart, hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c ∈ twistedRoots p n d,
        |intervalAP (max (jlo X ε p) (a / p))
            (max (max (jlo X ε p) (a / p)) (jhi X ε p)) d c.val -
          (∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
            1 / Real.log u) / Nat.totient d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ twistedRoots p n d, (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) :=
      Finset.sum_le_sum hclass
    _ = ((twistedRoots p n d).card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d.divisors.card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) := by
      apply mul_le_mul_of_nonneg_right _ hnn
      exact_mod_cast twistedRoots_card_le_tau p n d hpd hd hnd

/-- Page 17 between displays 57 and 58, truncated window version, stated for an arbitrary
finite set of larger primes: the progression fiber vanishes at a noncoprime modulus in the
rough range. -/
theorem finset_progression_zero (F : Finset ℕ) (p n d : ℕ)
    (hnd : ¬ Nat.Coprime n d)
    (hsmall : ∀ r ∈ F, (p * r) ^ 2 ≤ n)
    (hrough : ∀ r ∈ F, Nat.Coprime (p * r) d) :
    (F.filter (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hrF, hdiv⟩ := Finset.mem_filter.mp hr
  have hmod := (Nat.modEq_iff_dvd' (hsmall r hrF)).mpr hdiv
  have heq := (ZMod.natCast_eq_natCast_iff' ((p * r) ^ 2) n d).mpr hmod
  have hunit : IsUnit (((p * r) ^ 2 : ℕ) : ZMod d) :=
    (ZMod.isUnit_iff_coprime ((p * r) ^ 2) d).mpr ((hrough r hrF).pow_left 2)
  rw [heq] at hunit
  exact hnd ((ZMod.isUnit_iff_coprime n d).mp hunit)

/-- Page 17 between displays 57 and 58, truncated window version: the full finite transfer
for the truncated factor set, including the vanishing noncoprime case. -/
theorem trunc_factor_progression_error (X B ε a : ℝ) (p n d : ℕ) [NeZero d]
    (hp : p ∈ primeWindow X B ε) (hY : 0 < Y X ε) (ha : a ≤ Real.sqrt (Y X ε))
    (hd : Squarefree d) (hdp : d < p)
    (hsmall : ∀ r ∈ (factorPrimes X ε p).filter (fun r : ℕ => a ≤ ((p * r : ℕ) : ℝ)),
      (p * r) ^ 2 ≤ n)
    (hT : 2 ≤ Real.sqrt (Y X ε) / p)
    (hL : 1 ≤ Real.log (Real.sqrt (Y X ε) / p))
    (hdT : (d : ℝ) ≤ Real.sqrt (Y X ε) / p) :
    |((((factorPrimes X ε p).filter (fun r : ℕ => a ≤ ((p * r : ℕ) : ℝ))).filter
        (fun r : ℕ => d ∣ n - (p * r) ^ 2)).card : ℝ) -
      density n d * (∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
        1 / Real.log u)| ≤
      (d.divisors.card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hpp := (Finset.mem_filter.mp hp).2.1
  have hpd : p.Coprime d := hpp.coprime_iff_not_dvd.mpr (fun h =>
    (not_le_of_gt hdp) (Nat.le_of_dvd hd0 h))
  by_cases hnd : Nat.Coprime n d
  · exact trunc_factor_progression_error_coprime X B ε a p n d hp hY ha hpd hd hnd hsmall
      hT hL hdT
  · rw [finset_progression_zero _ p n d hnd hsmall
      (fun r hr => factorPrimes_coprime X ε p d hpp hd0 hdp r (Finset.mem_filter.mp hr).1)]
    simp only [Nat.cast_zero, density, ite_eq_right hnd, zero_mul, sub_self, abs_zero]
    have hE := primeError_nonneg (Real.sqrt (Y X ε) / p) d hT hL hd0 hdT
    positivity

/-- Page 17 between displays 57 and 58, truncated window version: summing the fixed smaller
prime transfer gives the error of the truncated semiprime sequence at one modulus. -/
theorem trunc_progression_error (X B ε a : ℝ) (n d : ℕ) [NeZero d]
    (hY : 0 < Y X ε) (hYX : Y X ε ≤ X) (hXn : X < (n : ℝ))
    (ha : a ≤ Real.sqrt (Y X ε)) (hd : Squarefree d)
    (hparams : ∀ p ∈ primeWindow X B ε, d < p ∧
      2 ≤ Real.sqrt (Y X ε) / p ∧ 1 ≤ Real.log (Real.sqrt (Y X ε) / p) ∧
        (d : ℝ) ≤ Real.sqrt (Y X ε) / p) :
    |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter
          (fun q => d ∣ n - q ^ 2)).card : ℝ) -
        density n d * (∑ p ∈ primeWindow X B ε,
          ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
            1 / Real.log u)| ≤
      ∑ p ∈ primeWindow X B ε,
        (d.divisors.card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) := by
  rw [trunc_count_factor_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hdp, hT, hL, hdT⟩ := hparams p hp
  apply trunc_factor_progression_error X B ε a p n d hp hY ha hd hdp _ hT hL hdT
  intro r hr
  have hhi := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2.2.2
  have hs := Real.sq_sqrt hY.le
  have hnn : (0 : ℝ) ≤ (p * r : ℕ) := by positivity
  have hreal : (((p * r : ℕ) : ℝ)) ^ 2 ≤ (n : ℝ) := by nlinarith [Real.sqrt_nonneg (Y X ε)]
  exact_mod_cast hreal

/-- Page 17 between displays 57 and 58, the bookkeeping step of the transfer in abstract
form, used for the truncated window version: a pointwise bound by divisor weighted errors
with an endpoint term sums to twice the weighted error sum plus the endpoint moment. -/
theorem weighted_transfer_sum (S P : Finset ℕ) (E : ℕ → ℕ → ℝ) (τ : ℕ → ℝ) (M : ℝ)
    (f : ℕ → ℝ)
    (hf : ∀ d ∈ S, f d ≤ ∑ p ∈ P, τ d * (2 * E p d + 2))
    (hmoment : (∑ d ∈ S, τ d) ≤ M) :
    (∑ d ∈ S, f d) ≤
      2 * (∑ p ∈ P, ∑ d ∈ S, τ d * E p d) + 2 * (P.card : ℝ) * M := by
  have hterm (d p : ℕ) : τ d * (2 * E p d + 2) = 2 * (τ d * E p d) + 2 * τ d := by ring
  have hsplit : (∑ d ∈ S, ∑ p ∈ P, τ d * (2 * E p d + 2)) =
      2 * (∑ p ∈ P, ∑ d ∈ S, τ d * E p d) + 2 * (P.card : ℝ) * ∑ d ∈ S, τ d := by
    rw [Finset.sum_comm]
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  have h1 := Finset.sum_le_sum hf
  rw [hsplit] at h1
  have hmom := mul_le_mul_of_nonneg_left hmoment (show (0 : ℝ) ≤ 2 * P.card by positivity)
  linarith

/-- Page 17 between displays 57 and 58, truncated window version: the explicit remainder of
the truncated semiprime sequence transfers to maximal prime errors with an endpoint term. -/
theorem trunc_remainder_prime_transfer (X B ε a : ℝ) (n : ℕ)
    (hY : 0 < Y X ε) (hYX : Y X ε ≤ X) (hXn : X < (n : ℝ))
    (ha : a ≤ Real.sqrt (Y X ε))
    (hparams : ∀ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
      ∀ p ∈ primeWindow X B ε, d < p ∧
        2 ≤ Real.sqrt (Y X ε) / p ∧ 1 ≤ Real.log (Real.sqrt (Y X ε) / p) ∧
          (d : ℝ) ≤ Real.sqrt (Y X ε) / p) :
    (∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
        |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter
            (fun q => d ∣ n - q ^ 2)).card : ℝ) -
          density n d * (∑ p ∈ primeWindow X B ε,
            ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
              1 / Real.log u)|) ≤
      2 * (∑ p ∈ primeWindow X B ε,
        ∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
          (d.divisors.card : ℝ) * primeError (Real.sqrt (Y X ε) / p) d) +
      2 * ((primeWindow X B ε).card : ℝ) * (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ^ 2 := by
  have hrewrite : (∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
      (ArithmeticFunction.moebius d : ℝ) ^ 2 *
        |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter
            (fun q => d ∣ n - q ^ 2)).card : ℝ) -
          density n d * (∑ p ∈ primeWindow X B ε,
            ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
              1 / Real.log u)|) =
      ∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
        |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter
            (fun q => d ∣ n - q ^ 2)).card : ℝ) -
          density n d * (∑ p ∈ primeWindow X B ε,
            ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
              1 / Real.log u)| := by
    refine Eq.trans ?_ (Finset.sum_filter _ _).symm
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hs : Squarefree d
    · have hm : (ArithmeticFunction.moebius d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
      simp only [hs, ite_true, hm, one_mul]
    · simp only [hs, ite_false, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs,
        Int.cast_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
  have hf : ∀ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
      |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter
            (fun q => d ∣ n - q ^ 2)).card : ℝ) -
          density n d * (∑ p ∈ primeWindow X B ε,
            ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
              1 / Real.log u)| ≤
        ∑ p ∈ primeWindow X B ε,
          (d.divisors.card : ℝ) * (2 * primeError (Real.sqrt (Y X ε) / p) d + 2) := by
    intro d hd
    obtain ⟨hdI, hds⟩ := Finset.mem_filter.mp hd
    have hd0 : 0 < d := (Finset.mem_Icc.mp hdI).1
    have : NeZero d := ⟨hd0.ne'⟩
    exact trunc_progression_error X B ε a n d hY hYX hXn ha hds (hparams d hdI)
  have hfull : (∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊, (d.divisors.card : ℝ)) ≤
      (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ^ 2 := by
    exact_mod_cast divisor_sum_trivial ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊
  have hmoment : (∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
      (d.divisors.card : ℝ)) ≤ (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)).trans hfull
  rw [hrewrite]
  exact weighted_transfer_sum ((Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree)
    (primeWindow X B ε) (fun p d => primeError (Real.sqrt (Y X ε) / p) d)
    (fun d => (d.divisors.card : ℝ)) ((⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ^ 2)
    (fun d => |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter
            (fun q => d ∣ n - q ^ 2)).card : ℝ) -
          density n d * (∑ p ∈ primeWindow X B ε,
            ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p),
              1 / Real.log u)|) hf hmoment

/-- Page 17 between displays 57 and 58, truncated window version of the Bombieri Vinogradov
remainder estimate, with the decidability instances of this file, which has no classical
local instance, as in Decomp542a. The cut a only needs a at most sqrt Y. -/
theorem trunc_bv_remainder_std (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) → ∀ a : ℝ,
      Real.sqrt (Y X ε) / 2 ≤ a → a ≤ Real.sqrt (Y X ε) →
      (∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
        |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter (fun q => d ∣ n - q ^ 2)).card : ℝ) -
          density n d * (∑ p ∈ primeWindow X B ε, ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p), 1 / Real.log u)|) ≤
        C * errorScale X ε A := by
  obtain ⟨K, hK, hprime⟩ := prime_window_weighted_bv A B ε hA hB hε hε1
  have hevent : ∀ᶠ X : ℝ in Filter.atTop,
      ∀ n : ℕ, X < (n : ℝ) → ∀ a : ℝ, a ≤ Real.sqrt (Y X ε) →
      (∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
        |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter (fun q => d ∣ n - q ^ 2)).card : ℝ) -
          density n d * (∑ p ∈ primeWindow X B ε, ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p), 1 / Real.log u)|) ≤
        (2 * K + 4) * errorScale X ε A := by
    filter_upwards [hprime, rough_level_parameters B ε hB hε hε1,
      prime_window_bv_parameters 1 2 B ε (by norm_num) hB hε hε1,
      endpoint_correction_bound A B ε hε] with X hp hr hw he
    intro n hXn a ha
    have hparams : ∀ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
        ∀ p ∈ primeWindow X B ε, d < p ∧
          2 ≤ Real.sqrt (Y X ε) / p ∧ 1 ≤ Real.log (Real.sqrt (Y X ε) / p) ∧
            (d : ℝ) ≤ Real.sqrt (Y X ε) / p := by
      intro d hd p hpp
      obtain ⟨hT, hlog, hlo, hhi, hlevel⟩ := hw.2 p hpp
      have hdD : (d : ℝ) ≤ Y X ε ^ (1 / 9 : ℝ) :=
        (by exact_mod_cast (Finset.mem_Icc.mp hd).2 : (d : ℝ) ≤ ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).trans
          (Nat.floor_le (Real.rpow_nonneg hr.1.le _))
      have hpz := (Finset.mem_filter.mp hpp).2.2.1
      have hdp : d < p := by exact_mod_cast (hdD.trans_lt (hr.2.2.trans_le hpz))
      have hlogpow : Real.log (Real.sqrt (Y X ε) / p) ^ (-(1 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)
      have hroot : Real.sqrt (Real.sqrt (Y X ε) / p) ≤ Real.sqrt (Y X ε) / p := by
        have hh := Real.sq_sqrt (show 0 ≤ Real.sqrt (Y X ε) / p by positivity)
        nlinarith [Real.sqrt_nonneg (Real.sqrt (Y X ε) / p)]
      have hdT := hdD.trans (hlevel.trans ((mul_le_of_le_one_right
        (Real.sqrt_nonneg _) hlogpow).trans hroot))
      exact ⟨hdp, hT, hlog, hdT⟩
    have ht := trunc_remainder_prime_transfer X B ε a n hr.1 hr.2.1 hXn ha hparams
    linarith [ht, hp, he]
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨2 * K + 4, X0, by positivity, ?_⟩
  intro X hX n hn hXn a ha1 ha2
  exact hX0 X hX n hXn a ha2

section ClassicalInstances

attribute [local instance] Classical.propDecidable

/-- Page 17 between displays 57 and 58, truncated window version of the Bombieri Vinogradov
remainder estimate for the truncated semiprime sequence of page 16, cut from below at a.
This is the interface statement. It is elaborated with the classical decidability local
instance, as in Decomp506bBase, Decomp506b, Decomp506e, Decomp506f, Decomp506g and Decomp129,
so that it matches the same text in the files that consume it. -/
theorem trunc_bv_remainder (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) → ∀ a : ℝ,
      Real.sqrt (Y X ε) / 2 ≤ a → a ≤ Real.sqrt (Y X ε) →
      (∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
        |((((semiprimes X B ε).filter (fun q : ℕ => a ≤ (q : ℝ))).filter (fun q => d ∣ n - q ^ 2)).card : ℝ) -
          density n d * (∑ p ∈ primeWindow X B ε, ∫ u in max (jlo X ε p) (a / p)..max (max (jlo X ε p) (a / p)) (jhi X ε p), 1 / Real.log u)|) ≤
        C * errorScale X ε A := by
  obtain ⟨C, X0, hC, h⟩ := trunc_bv_remainder_std A B ε hA hB hε hε1
  refine ⟨C, X0, hC, fun X hX n hn hXn a ha1 ha2 => ?_⟩
  convert h X hX n hn hXn a ha1 ha2

end ClassicalInstances


end LeanLab.KumchevLiu2007.Trunc129
