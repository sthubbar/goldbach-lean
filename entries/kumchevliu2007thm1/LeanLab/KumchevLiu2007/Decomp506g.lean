module

public import LeanLab.PNTSieve.BonferroniWeighted
public import LeanLab.KumchevLiu2007.Decomp506f

/-!
The remaining analytic Rosser input is an explicit upper weight construction.
The original sifted count bound follows by the proved finite model and support bridge.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

-- Port fix for Mathlib v4.35.0-rc3: its instance making a simple nilpotent additive group
-- commutative is found for `ZMod p` under `Fact p.Prime` and blocks `ring` and `simp`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace LeanLab.KumchevLiu2007.Task506g

open Real Task506b Task506d Task506e Task506f
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-! ### 1. Subset products and divisors -/

/-- The subset-product map is injective on the subsets of a finset of primes. -/
theorem prod_powerset_injOn (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∀ T ∈ S.powerset, ∀ U ∈ S.powerset, (∏ p ∈ T, p) = (∏ p ∈ U, p) → T = U := by
  have key : ∀ A B : Finset ℕ, A ⊆ S → B ⊆ S → (∏ p ∈ A, p) = (∏ p ∈ B, p) → A ⊆ B := by
    intro A B hA hB hAB
    by_contra hsub
    obtain ⟨p, hpA, hpB⟩ := Finset.not_subset.mp hsub
    have hpp : p.Prime := hS p (hA hpA)
    have hdvd : p ∣ ∏ q ∈ A, q := Finset.dvd_prod_of_mem _ hpA
    rw [hAB] at hdvd
    obtain ⟨q, hqB, hpq⟩ := (hpp.prime.dvd_finsetProd_iff id).mp hdvd
    have hqp : q.Prime := hS q (hB hqB)
    have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqp).mp hpq
    exact hpB (hpeq ▸ hqB)
  intro T hT U hU hTU
  have hTS : T ⊆ S := Finset.mem_powerset.mp hT
  have hUS : U ⊆ S := Finset.mem_powerset.mp hU
  exact Finset.Subset.antisymm (key T U hTS hUS hTU) (key U T hUS hTS hTU.symm)

/-- The divisors of a product of distinct primes are exactly the subset products. -/
theorem divisors_eq_image_powerset (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hmem : ∀ p, p.Prime → p ∣ ∏ p ∈ S, p → p ∈ S) :
    (∏ p ∈ S, p).divisors = S.powerset.image (fun T => ∏ p ∈ T, p) := by
  classical
  have hP0 : (∏ p ∈ S, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hS p hp).ne_zero
  have hsq : Squarefree (∏ p ∈ S, p) :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => by
        change IsRelPrime p q
        rw [← Nat.coprime_iff_isRelPrime]
        exact (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)
      (fun p hp => (hS p hp).squarefree)
  refine Finset.Subset.antisymm ?_ ?_
  · intro d hd
    have hdvd : d ∣ ∏ p ∈ S, p := (Nat.mem_divisors.mp hd).1
    have hsqd : Squarefree d := Squarefree.squarefree_of_dvd hdvd hsq
    refine Finset.mem_image.mpr ⟨d.primeFactors, Finset.mem_powerset.mpr ?_,
      Nat.prod_primeFactors_of_squarefree hsqd⟩
    intro p hp
    exact hmem p (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans hdvd)
  · intro d hd
    obtain ⟨T, hT, hTd⟩ := Finset.mem_image.mp hd
    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
    exact Nat.mem_divisors.mpr ⟨hTd ▸ Finset.prod_dvd_prod_of_subset T S id hTS, hP0⟩

/-- Sums over the divisors of a squarefree product are sums over subset products. -/
theorem sum_divisors_eq_sum_powerset (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hmem : ∀ p, p.Prime → p ∣ ∏ p ∈ S, p → p ∈ S) (f : ℕ → ℝ) :
    ∑ d ∈ (∏ p ∈ S, p).divisors, f d = ∑ T ∈ S.powerset, f (∏ p ∈ T, p) := by
  classical
  rw [divisors_eq_image_powerset S hS hmem]
  rw [Finset.sum_image (fun T hT U hU h => prod_powerset_injOn S hS T hT U hU h)]

/-- On a product of distinct primes the Moebius function is `(-1)^(#factors)`. -/
theorem coe_moebius_prod_primes (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    (ArithmeticFunction.moebius (∏ p ∈ T, p) : ℝ) = (-1 : ℝ) ^ T.card := by
  have h1 : ArithmeticFunction.moebius (∏ p ∈ T, p) = ∏ p ∈ T, ArithmeticFunction.moebius p :=
    ArithmeticFunction.IsMultiplicative.map_prod_of_prime
      ArithmeticFunction.isMultiplicative_moebius T hT
  have h2 : (∏ p ∈ T, ArithmeticFunction.moebius p) = ((-1 : ℤ)) ^ T.card := by
    rw [Finset.prod_congr rfl (fun p hp => ArithmeticFunction.moebius_apply_prime (hT p hp)),
      Finset.prod_const]
  rw [h1, h2]
  push_cast
  ring

/-! ### 2. Maclaurin's bound (`PNTSieve.Esymm` is outside this file's imports) -/

/-- `S^(k+1) + (k+1) y S^k <= (S+y)^(k+1)` for `S, y >= 0`. -/
theorem pow_ge_two_terms (S y : ℝ) (hS : 0 ≤ S) (hy : 0 ≤ y) (k : ℕ) :
    S ^ (k + 1) + (k + 1) * y * S ^ k ≤ (S + y) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : 0 ≤ S + y := by linarith
      calc S ^ (k + 1 + 1) + (↑(k + 1) + 1) * y * S ^ (k + 1)
          ≤ (S + y) * (S ^ (k + 1) + (k + 1) * y * S ^ k) := by
            push_cast
            have hpos : 0 ≤ (k + 1 : ℝ) * y * y * S ^ k := by positivity
            have e : (S + y) * (S ^ (k + 1) + (k + 1) * y * S ^ k) =
                S ^ (k + 1 + 1) + ((k : ℝ) + 1 + 1) * y * S ^ (k + 1) +
                  (k + 1) * y * y * S ^ k := by ring
            rw [e]; linarith
        _ ≤ (S + y) * (S + y) ^ (k + 1) := mul_le_mul_of_nonneg_left ih h1
        _ = (S + y) ^ (k + 1 + 1) := by ring

/-- The elementary symmetric sum of size `k+1` splits at an inserted element. -/
theorem esymm_step (x : ℕ → ℝ) {a : ℕ} {P : Finset ℕ} (ha : a ∉ P) (k : ℕ) :
    (∑ T ∈ (insert a P).powersetCard (k + 1), ∏ p ∈ T, x p) =
      (∑ T ∈ P.powersetCard (k + 1), ∏ p ∈ T, x p)
        + x a * ∑ T ∈ P.powersetCard k, ∏ p ∈ T, x p := by
  classical
  have hdisj : Disjoint (P.powersetCard (k + 1)) ((P.powersetCard k).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro T h1 h2
    obtain ⟨U, -, rfl⟩ := Finset.mem_image.mp h2
    exact ha ((Finset.mem_powersetCard.mp h1).1 (Finset.mem_insert_self a U))
  have hinj : Set.InjOn (insert a) (P.powersetCard k : Set (Finset ℕ)) := by
    intro T1 h1 T2 h2 he
    have n1 : a ∉ T1 := fun h => ha ((Finset.mem_powersetCard.mp h1).1 h)
    have n2 : a ∉ T2 := fun h => ha ((Finset.mem_powersetCard.mp h2).1 h)
    simpa [n1, n2] using congrArg (fun U => U.erase a) he
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union hdisj, Finset.sum_image hinj,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun T hT => ?_
  have haT : a ∉ T := fun h => ha ((Finset.mem_powersetCard.mp hT).1 h)
  rw [Finset.prod_insert haT]

/-- `k! * e_k(x) <= (sum x)^k` for nonnegative weights. -/
theorem factorial_mul_esymm_le (x : ℕ → ℝ) (hx : ∀ p, 0 ≤ x p) :
    ∀ (P : Finset ℕ) (k : ℕ),
      (k.factorial : ℝ) * ∑ T ∈ P.powersetCard k, ∏ p ∈ T, x p ≤ (∑ p ∈ P, x p) ^ k := by
  intro P
  induction P using Finset.induction with
  | empty =>
      intro k
      rcases k with _ | k
      · simp
      · rw [Finset.powersetCard_eq_empty.mpr (by simp)]
        simp
  | insert a P ha ih =>
      intro k
      rcases k with _ | k
      · simp
      · set A : ℝ := ∑ T ∈ P.powersetCard (k + 1), ∏ p ∈ T, x p with hAdef
        set E : ℝ := ∑ T ∈ P.powersetCard k, ∏ p ∈ T, x p with hEdef
        have hxa : (0 : ℝ) ≤ x a := hx a
        have hS0 : (0 : ℝ) ≤ ∑ p ∈ P, x p := Finset.sum_nonneg fun p _ => hx p
        have hA : ((k + 1).factorial : ℝ) * A ≤ (∑ p ∈ P, x p) ^ (k + 1) := by
          have h := ih (k + 1)
          rw [← hAdef] at h
          exact h
        have hE : (k.factorial : ℝ) * E ≤ (∑ p ∈ P, x p) ^ k := by
          have h := ih k
          rw [← hEdef] at h
          exact h
        have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        have hb2 : ((k : ℝ) + 1) * x a * ((k.factorial : ℝ) * E)
            ≤ ((k : ℝ) + 1) * x a * (∑ p ∈ P, x p) ^ k :=
          mul_le_mul_of_nonneg_left hE (by positivity)
        have hkey := pow_ge_two_terms (∑ p ∈ P, x p) (x a) hS0 hxa k
        rw [esymm_step x ha k, ← hAdef, ← hEdef, mul_add, Finset.sum_insert ha]
        have h2 : ((k + 1).factorial : ℝ) * (x a * E)
            = ((k : ℝ) + 1) * x a * ((k.factorial : ℝ) * E) := by
          rw [hfac]
          ring
        rw [h2]
        have hkey' : (∑ p ∈ P, x p) ^ (k + 1) + ((k : ℝ) + 1) * x a * (∑ p ∈ P, x p) ^ k
            ≤ (x a + ∑ p ∈ P, x p) ^ (k + 1) := by
          rw [add_comm (x a) (∑ p ∈ P, x p)]
          exact hkey
        calc ((k + 1).factorial : ℝ) * A + ((k : ℝ) + 1) * x a * ((k.factorial : ℝ) * E)
            ≤ (∑ p ∈ P, x p) ^ (k + 1) + ((k : ℝ) + 1) * x a * (∑ p ∈ P, x p) ^ k :=
              add_le_add hA hb2
          _ ≤ (x a + ∑ p ∈ P, x p) ^ (k + 1) := hkey'

/-- `k! >= (k / e)^k`. -/
theorem factorial_ge_div_exp (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hfac0 : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hlog := LeanLab.PNTSieve.Mertens.log_factorial_ge k
  have hexplog : Real.log ((k : ℝ) / Real.exp 1) = Real.log (k : ℝ) - 1 := by
    rw [Real.log_div hk0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have h1 : (0 : ℝ) < (k : ℝ) / Real.exp 1 := by positivity
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos h1, hexplog]
  have h2 : (Real.log (k : ℝ) - 1) * (k : ℝ) = (k : ℝ) * Real.log (k : ℝ) - k := by ring
  rw [h2]
  calc Real.exp ((k : ℝ) * Real.log (k : ℝ) - k) ≤ Real.exp (Real.log (k.factorial : ℝ)) :=
        Real.exp_le_exp.mpr hlog
    _ = (k.factorial : ℝ) := Real.exp_log hfac0

/-- The `k`-fold elementary symmetric sum of weights with total `S` is at most
`(e S / k)^k`. -/
theorem esymm_le_exp (x : ℕ → ℝ) (hx : ∀ p, 0 ≤ x p) (P : Finset ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∑ T ∈ P.powersetCard k, ∏ p ∈ T, x p ≤ (Real.exp 1 * (∑ p ∈ P, x p) / k) ^ k := by
  set Ssum : ℝ := ∑ p ∈ P, x p with hSsum
  have hS0 : 0 ≤ Ssum := by rw [hSsum]; exact Finset.sum_nonneg fun p _ => hx p
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hfac0 : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hmac : ∑ T ∈ P.powersetCard k, ∏ p ∈ T, x p ≤ Ssum ^ k / (k.factorial : ℝ) := by
    rw [le_div_iff₀ hfac0]
    have h := factorial_mul_esymm_le x hx P k
    rw [← hSsum] at h
    calc (∑ T ∈ P.powersetCard k, ∏ p ∈ T, x p) * (k.factorial : ℝ)
        = (k.factorial : ℝ) * ∑ T ∈ P.powersetCard k, ∏ p ∈ T, x p := by ring
      _ ≤ Ssum ^ k := h
  refine hmac.trans ?_
  have hfac := factorial_ge_div_exp k hk
  have hSexp : (Real.exp 1 * Ssum / k) ^ k * ((k : ℝ) / Real.exp 1) ^ k = Ssum ^ k := by
    rw [← mul_pow]
    have hkne : (k : ℝ) ≠ 0 := hk0.ne'
    have hene : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    congr 1
    field_simp
  rw [div_le_iff₀ hfac0]
  calc Ssum ^ k = (Real.exp 1 * Ssum / k) ^ k * ((k : ℝ) / Real.exp 1) ^ k := hSexp.symm
    _ ≤ (Real.exp 1 * Ssum / k) ^ k * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)

/-- `prod (1 - y) >= exp (- sum y/(1-y))` for `0 <= y < 1`. -/
theorem prod_one_sub_ge_exp (S : Finset ℕ) (y : ℕ → ℝ)
    (hy0 : ∀ p ∈ S, 0 ≤ y p) (hy1 : ∀ p ∈ S, y p < 1) :
    Real.exp (-(∑ p ∈ S, y p / (1 - y p))) ≤ ∏ p ∈ S, (1 - y p) := by
  have hpos : ∀ p ∈ S, 0 < 1 - y p := fun p hp => by linarith [hy1 p hp]
  have hlog : ∀ p ∈ S, -(y p / (1 - y p)) ≤ Real.log (1 - y p) := by
    intro p hp
    have hpos' : (0 : ℝ) < 1 - y p := hpos p hp
    have h1 : (0 : ℝ) < 1 / (1 - y p) := by positivity
    have h2 := Real.log_le_sub_one_of_pos h1
    rw [Real.log_div one_ne_zero (ne_of_gt hpos'), Real.log_one] at h2
    have h3 : 1 / (1 - y p) - 1 = y p / (1 - y p) := by
      rw [div_sub_one (ne_of_gt hpos')]
      ring_nf
    linarith
  calc Real.exp (-(∑ p ∈ S, y p / (1 - y p)))
      = Real.exp (∑ p ∈ S, -(y p / (1 - y p))) := by rw [Finset.sum_neg_distrib]
    _ ≤ Real.exp (∑ p ∈ S, Real.log (1 - y p)) :=
        Real.exp_le_exp.mpr (Finset.sum_le_sum hlog)
    _ = ∏ p ∈ S, (1 - y p) := by
        rw [Real.exp_sum]
        exact Finset.prod_congr rfl fun p hp => Real.exp_log (hpos p hp)


/-! ### 3. Page-17 density on the sieve support -/

/-- Page 17: a positive prime density is exactly `2 / (p - 1)`. -/
theorem density_prime_eq_two_div (n p : ℕ) (hp : p.Prime) (hn : InH2 n)
    (hpos : 0 < density n p) : density n p = 2 / ((p : ℝ) - 1) := by
  have hpne2 : p = 2 → False := by
    intro h
    rw [h, density_two_of_InH2 n hn] at hpos
    exact lt_irrefl _ hpos
  have hnd : ¬ p ∣ n := by
    intro h
    rw [density_prime_eq n p hp, if_pos h] at hpos
    exact lt_irrefl _ hpos
  haveI : Fact p.Prime := ⟨hp⟩
  have hcopn : Nat.Coprime n p := (hp.coprime_iff_not_dvd.mpr hnd).symm
  let Sset : Finset (ZMod p) :=
    (Finset.univ.erase (0 : ZMod p)).filter (fun x => x ^ 2 = (n : ZMod p))
  have hScard : ((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card = Sset.card :=
    Task129s.root_count_range_eq p n hnd
  have hSle : Sset.card ≤ 2 := Task129a.nonzero_square_roots_le_two p n
  have hden : density n p =
      (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) /
        (Nat.totient p : ℝ) := by
    rw [density, if_pos hcopn]
  have hphi : (0 : ℝ) < (Nat.totient p : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hcposR :
      (0 : ℝ) < (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) := by
    by_contra h
    push_neg at h
    rw [hden] at hpos
    have hle : ((((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) /
        (Nat.totient p : ℝ)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hphi.le
    linarith
  have hSpos : 0 < Sset.card := by
    rw [← hScard]
    exact_mod_cast hcposR
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hSpos
  obtain ⟨hx0, hx2⟩ := Finset.mem_filter.mp hx
  have hxne : x ≠ 0 := (Finset.mem_erase.mp hx0).1
  have hneg : -x ∈ Sset := by
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨neg_ne_zero.mpr hxne, Finset.mem_univ _⟩, ?_⟩
    rw [neg_sq, hx2]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    obtain h1 | h2 := (Nat.dvd_prime Nat.prime_two).mp hdvd
    · exact hp.ne_one h1
    · exact hpne2 h2
  have hne : -x ≠ x := by
    intro e
    have hsum : x + x = 0 := by
      have h := add_neg_cancel x
      rwa [e] at h
    have h2x : (2 : ZMod p) * x = 0 := by
      rw [two_mul]
      exact hsum
    rcases mul_eq_zero.mp h2x with h | h
    · exact h2ne h
    · exact hxne h
  have h2le : 2 ≤ Sset.card := by
    have h1 : 1 < Sset.card := Finset.one_lt_card.mpr ⟨-x, hneg, x, hx, hne⟩
    omega
  have hSeq : Sset.card = 2 := by omega
  rw [hden, hScard, hSeq, Nat.totient_prime hp, Nat.cast_ofNat, Nat.cast_sub hp.one_le,
    Nat.cast_one]

/-- Page 17: on a divisor of the sifted prime product the density is the product of the
two-dimensional local densities. -/
theorem density_eq_prod_of_dvd_primeProduct (X δ : ℝ) (n d : ℕ) (hn : InH2 n)
    (hd : d ∣ primeProduct X δ n) :
    density n d = ∏ p ∈ d.primeFactors, (2 / ((p : ℝ) - 1)) := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd (primeProduct_squarefree X δ n)
  have hmul : density n d = ∏ p ∈ d.primeFactors, density n p :=
    ((density_isMultiplicative n).prod_primeFactors (l := d) hsq).symm
  rw [hmul]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hsupp : p ∈ primeSupport X δ n :=
    prime_mem_of_dvd_product X δ n p hpprime
      ((Nat.dvd_of_mem_primeFactors hp).trans hd)
  exact density_prime_eq_two_div n p hpprime hn (Finset.mem_filter.mp hsupp).2.2.2

/-- `primeProduct` is the product of the support. -/
theorem primeProduct_eq_prod (X δ : ℝ) (n : ℕ) :
    primeProduct X δ n = ∏ p ∈ primeSupport X δ n, p := rfl

/-! ### 4. The model main sum of the truncated weights -/

/-- The model main sum of the truncated Moebius weights is the Bonferroni truncation of the
Euler product of the local densities. -/
theorem mainSum_truncated (X B δ ε : ℝ) (n K : ℕ) (hn : InH2 n) :
    (sieveModel X B δ ε n hn).mainSum
        (fun d => if d.primeFactors.card ≤ K then (ArithmeticFunction.moebius d : ℝ) else 0)
      = ∑ T ∈ (primeSupport X δ n).powerset.filter (fun T => T.card ≤ K),
          (-1 : ℝ) ^ T.card * ∏ p ∈ T, density n p := by
  classical
  have hS : ∀ p ∈ primeSupport X δ n, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hmem : ∀ p, p.Prime → p ∣ ∏ p ∈ primeSupport X δ n, p → p ∈ primeSupport X δ n := by
    intro p hp hd
    exact prime_mem_of_dvd_product X δ n p hp (by rwa [primeProduct_eq_prod])
  have hnu : ∀ d, (sieveModel X B δ ε n hn).nu d = density n d := fun d => rfl
  have hPP : (sieveModel X B δ ε n hn).prodPrimes = ∏ p ∈ primeSupport X δ n, p := rfl
  rw [BoundingSieve.mainSum, hPP]
  simp only [hnu]
  have hstep : ∑ d ∈ (∏ p ∈ primeSupport X δ n, p).divisors,
      (if d.primeFactors.card ≤ K then (ArithmeticFunction.moebius d : ℝ) else 0) * density n d
      = ∑ d ∈ (∏ p ∈ primeSupport X δ n, p).divisors.filter
          (fun d => d.primeFactors.card ≤ K), (ArithmeticFunction.moebius d : ℝ) * density n d := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun d _ => by
      by_cases hc : d.primeFactors.card ≤ K <;> simp [hc]
  rw [hstep]
  refine Finset.sum_nbij' (fun d => d.primeFactors) (fun T => ∏ p ∈ T, p) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro d hd
    obtain ⟨hddiv, hdcard⟩ := Finset.mem_filter.mp hd
    have hdvd : d ∣ ∏ p ∈ primeSupport X δ n, p := (Nat.mem_divisors.mp hddiv).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hdcard⟩
    intro p hp
    exact hmem p (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hdvd)
  · -- backward membership
    intro T hT
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_filter.mp hT
    have hTS : T ⊆ primeSupport X δ n := Finset.mem_powerset.mp hTsub
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.prod_dvd_prod_of_subset T _ id hTS
    · exact Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero)
    · have hpf : (∏ p ∈ T, p).primeFactors = T :=
        Nat.primeFactors_prod (fun p hpT => hS p (hTS hpT))
      rw [hpf]
      exact hTcard
  · -- left inverse
    intro d hd
    have hdvd : d ∣ ∏ p ∈ primeSupport X δ n, p :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    exact Nat.prod_primeFactors_of_squarefree
      (Squarefree.squarefree_of_dvd hdvd (primeProduct_squarefree X δ n))
  · -- right inverse
    intro T hT
    have hTS : T ⊆ primeSupport X δ n := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    exact Nat.primeFactors_prod fun p hp => hS p (hTS hp)
  · -- term equality
    intro d hd
    obtain ⟨hddiv, hdcard⟩ := Finset.mem_filter.mp hd
    have hdvd : d ∣ ∏ p ∈ primeSupport X δ n, p := (Nat.mem_divisors.mp hddiv).1
    have hsqd : Squarefree d := Squarefree.squarefree_of_dvd hdvd (primeProduct_squarefree X δ n)
    have hcard : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
    have hmu : (ArithmeticFunction.moebius d : ℝ) = (-1 : ℝ) ^ d.primeFactors.card := by
      have h1 : (ArithmeticFunction.moebius (∏ p ∈ d.primeFactors, p) : ℝ)
          = (-1 : ℝ) ^ d.primeFactors.card := coe_moebius_prod_primes d.primeFactors hcard
      rwa [Nat.prod_primeFactors_of_squarefree hsqd] at h1
    have hnu2 : density n d = ∏ p ∈ d.primeFactors, density n p :=
      ((density_isMultiplicative n).prod_primeFactors (l := d) hsqd).symm
    rw [hmu, hnu2]


/-! ### 5. The truncated Moebius weights: upper Moebius, size, level -/

/-- The Moebius weights truncated at `K` prime factors are upper Moebius for even `K`. -/
theorem isUpperMoebius_truncated (K : ℕ) (hK : Even K) :
    BoundingSieve.IsUpperMoebius
      (fun d => if d.primeFactors.card ≤ K then (ArithmeticFunction.moebius d : ℝ) else 0) := by
  classical
  intro N
  rcases eq_or_ne N 0 with hN0 | hN0
  · subst hN0
    rw [Nat.divisors_zero, Finset.sum_empty]
    simp
  set Pp : ℕ := ∏ p ∈ N.primeFactors, p with hPp
  have hS : ∀ p ∈ N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hPp0 : Pp ≠ 0 := by
    rw [hPp]
    exact Finset.prod_ne_zero_iff.mpr fun p hp => (hS p hp).ne_zero
  have hPpdvd : Pp ∣ N := by rw [hPp]; exact Nat.prod_primeFactors_dvd N
  have hmem : ∀ p, p.Prime → p ∣ Pp → p ∈ N.primeFactors := by
    intro p hp hd
    exact Nat.mem_primeFactors.mpr ⟨hp, hd.trans hPpdvd, hN0⟩
  have hzero : ∀ d ∈ N.divisors, d ∉ Pp.divisors →
      (if d.primeFactors.card ≤ K then (ArithmeticFunction.moebius d : ℝ) else 0) = 0 := by
    intro d hd hnot
    have hdvd : d ∣ N := (Nat.mem_divisors.mp hd).1
    have hnsq : ¬ Squarefree d := by
      intro hsq
      apply hnot
      refine Nat.mem_divisors.mpr ⟨?_, hPp0⟩
      rw [← Nat.prod_primeFactors_of_squarefree hsq]
      refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
      intro p hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
        (Nat.dvd_of_mem_primeFactors hp).trans hdvd, hN0⟩
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
    simp
  have hsub : ∀ d, d ∈ Pp.divisors → d ∈ N.divisors := by
    intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    exact Nat.mem_divisors.mpr ⟨hdvd.trans hPpdvd, hN0⟩
  rw [← Finset.sum_subset hsub hzero, hPp,
    sum_divisors_eq_sum_powerset N.primeFactors hS hmem]
  have hterm : ∀ T ∈ N.primeFactors.powerset,
      (if (∏ p ∈ T, p).primeFactors.card ≤ K then
        (ArithmeticFunction.moebius (∏ p ∈ T, p) : ℝ) else 0)
      = (if T.card ≤ K then (-1 : ℝ) ^ T.card else 0) := by
    intro T hT
    have hTS : T ⊆ N.primeFactors := Finset.mem_powerset.mp hT
    have hpT : ∀ p ∈ T, p.Prime := fun p hp => hS p (hTS hp)
    rw [Nat.primeFactors_prod hpT, coe_moebius_prod_primes T hpT]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have htrunc : ((LeanLab.PNTSieve.Bonferroni.trunc N.primeFactors K : ℤ) : ℝ)
      = ∑ T ∈ (N.primeFactors).powerset.filter (fun T => T.card ≤ K), (-1 : ℝ) ^ T.card := by
    unfold LeanLab.PNTSieve.Bonferroni.trunc
    push_cast
    rfl
  have hbf := LeanLab.PNTSieve.Bonferroni.bonferroni_even N.primeFactors hK
  have hcast : (if N.primeFactors = ∅ then (1 : ℝ) else 0) ≤
      ∑ T ∈ (N.primeFactors).powerset.filter (fun T => T.card ≤ K), (-1 : ℝ) ^ T.card := by
    rw [← htrunc]
    exact_mod_cast hbf
  have hiff : (if N = 1 then (1 : ℝ) else 0) = (if N.primeFactors = ∅ then (1 : ℝ) else 0) := by
    by_cases h1 : N = 1
    · subst h1
      simp
    · have hlt : 1 < N := by omega
      have hne : N.primeFactors ≠ ∅ :=
        Finset.nonempty_iff_ne_empty.mp (Nat.nonempty_primeFactors.mpr hlt)
      simp [h1, hne]
  rw [hiff]
  exact hcast

/-- The truncated Moebius weights have absolute value at most one. -/
theorem abs_truncated_le_one (K d : ℕ) :
    |(if d.primeFactors.card ≤ K then (ArithmeticFunction.moebius d : ℝ) else 0)| ≤ 1 := by
  split_ifs with h
  · have h1 : |ArithmeticFunction.moebius d| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
    rw [← Int.cast_abs]
    exact_mod_cast h1
  · simp

/-- `prod p <= c ^ #s` for nonzero factors bounded by `c >= 0` (avoids `MulLeftMono ℝ`,
which this Mathlib build does not have). -/
theorem prod_nat_le_pow_card (s : Finset ℕ) (c : ℝ) (hpos : 0 ≤ c)
    (h : ∀ p ∈ s, (p : ℝ) ≤ c) : ∏ p ∈ s, (p : ℝ) ≤ c ^ s.card := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
      have h1 : (0 : ℝ) ≤ (a : ℝ) := by positivity
      have h2 : (a : ℝ) ≤ c := h a (Finset.mem_insert_self a s)
      have h3 : (0 : ℝ) ≤ ∏ p ∈ s, (p : ℝ) := Finset.prod_nonneg fun p _ => by positivity
      have h4 : (0 : ℝ) ≤ c ^ s.card := pow_nonneg hpos _
      calc (a : ℝ) * ∏ p ∈ s, (p : ℝ) ≤ c * c ^ s.card :=
            mul_le_mul h2 (ih (fun p hp => h p (Finset.mem_insert_of_mem hp))) h3 hpos
        _ = c ^ s.card * c := by ring
        _ = c ^ (s.card + 1) := by ring

/-- A divisor of the sifted prime product with at most `K` prime factors is at most the level,
provided `K * log z <= log D`. -/
theorem divisor_lt_level (X δ ε : ℝ) (n K : ℕ) (hn : InH2 n) (hX1 : 1 < X) (hδ : 0 < δ)
    (hδ1 : δ < 1)
    (hlev : (K : ℝ) * Real.log (Real.exp (Real.log X ^ (1 - δ / 2)))
      ≤ Real.log (Y X ε ^ (1 / 9 : ℝ)))
    {d : ℕ} (hd : d ∈ (primeProduct X δ n).divisors) (hc : d.primeFactors.card ≤ K) :
    (d : ℝ) ≤ Y X ε ^ (1 / 9 : ℝ) := by
  classical
  set Zf : ℝ := Real.exp (Real.log X ^ (1 - δ / 2)) with hZf
  have hX0 : (0 : ℝ) < X := by linarith
  have hZ1 : 1 < Zf := by
    rw [hZf]
    refine Real.one_lt_exp_iff.mpr ?_
    have hL : 0 < Real.log X := Real.log_pos hX1
    exact Real.rpow_pos_of_pos hL _
  have hZ0 : 0 < Zf := by linarith
  have hdvd : d ∣ primeProduct X δ n := (Nat.mem_divisors.mp hd).1
  have hsqd : Squarefree d := Squarefree.squarefree_of_dvd hdvd (primeProduct_squarefree X δ n)
  have hS : ∀ p ∈ primeSupport X δ n, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hlt : ∀ p ∈ d.primeFactors, (p : ℝ) < Zf := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hps : p ∈ primeSupport X δ n :=
      prime_mem_of_dvd_product X δ n p hpp ((Nat.dvd_of_mem_primeFactors hp).trans hdvd)
    have h2 := (Finset.mem_filter.mp hps).2.2.1
    rwa [hZf]
  have hstep1 : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsqd]
  rw [hstep1]
  have hb : ∏ p ∈ d.primeFactors, (p : ℝ) ≤ Zf ^ d.primeFactors.card :=
    prod_nat_le_pow_card d.primeFactors Zf hZ0.le (fun p hp => le_of_lt (hlt p hp))
  have hpow : Zf ^ d.primeFactors.card ≤ Zf ^ K := pow_le_pow_right₀ hZ1.le hc
  have hYpos : (0 : ℝ) < Y X ε ^ (1 / 9 : ℝ) :=
    Real.rpow_pos_of_pos (by unfold Y; positivity) _
  have hZK : Zf ^ K ≤ Y X ε ^ (1 / 9 : ℝ) := by
    have hexp : Zf ^ K = Real.exp ((K : ℝ) * Real.log Zf) := by
      rw [hZf, ← Real.exp_nat_mul, Real.log_exp]
    rw [hexp]
    refine le_trans (Real.exp_le_exp.mpr ?_) (le_of_eq (Real.exp_log hYpos))
    simpa [hZf] using hlev
  exact le_trans hb (le_trans hpow hZK)


/-! ### 6. Size of the total local density -/

/-- The total local density on the sieve support is `O(log log z)`. -/
theorem sum_density_le (X δ : ℝ) (n : ℕ) (hn : InH2 n)
    (hX1 : 1 < X) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hZ2 : 2 ≤ ⌊Real.exp (Real.log X ^ (1 - δ / 2))⌋₊) :
    ∑ p ∈ primeSupport X δ n, density n p ≤
      4 * (Real.log (Real.log (⌊Real.exp (Real.log X ^ (1 - δ / 2))⌋₊ : ℝ)) + 12) := by
  classical
  have hS : ∀ p ∈ primeSupport X δ n, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hterm : ∀ p ∈ primeSupport X δ n, density n p ≤ 4 * (1 / (p : ℝ)) := by
    intro p hp
    have hpp := hS p hp
    have hpos := (Finset.mem_filter.mp hp).2.2.2
    rw [density_prime_eq_two_div n p hpp hn hpos]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    calc 2 / ((p : ℝ) - 1) ≤ 4 / (p : ℝ) := by
          rw [div_le_div_iff₀ hp1 hp0]
          linarith
      _ = 4 * (1 / (p : ℝ)) := by ring
  have hsub : primeSupport X δ n ⊆
      (Finset.Icc 1 ⌊Real.exp (Real.log X ^ (1 - δ / 2))⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpr, hpp, hplt, -⟩ := Finset.mem_filter.mp hp
    have hpZ : p ≤ ⌊Real.exp (Real.log X ^ (1 - δ / 2))⌋₊ := by
      have h1 : p < ⌊Real.exp (Real.log X ^ (1 - δ / 2))⌋₊ + 1 := Finset.mem_range.mp hpr
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.pos, hpZ⟩, hpp⟩
  calc ∑ p ∈ primeSupport X δ n, density n p
      ≤ ∑ p ∈ primeSupport X δ n, 4 * (1 / (p : ℝ)) := Finset.sum_le_sum hterm
    _ = 4 * ∑ p ∈ primeSupport X δ n, (1 / (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 4 * ∑ p ∈ (Finset.Icc 1 ⌊Real.exp (Real.log X ^ (1 - δ / 2))⌋₊).filter Nat.Prime,
          (1 / (p : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 4 * (Real.log (Real.log (⌊Real.exp (Real.log X ^ (1 - δ / 2))⌋₊ : ℝ)) + 12) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact LeanLab.PNTSieve.Mertens.sum_inv_primes_le _ hZ2

/-- `5 <= p` on the sieve support for admissible `n`. -/
theorem five_le_of_mem_primeSupport (X δ : ℝ) (n : ℕ) (hn : InH2 n) {p : ℕ}
    (hp : p ∈ primeSupport X δ n) : 5 ≤ p := by
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hpos : 0 < density n p := (Finset.mem_filter.mp hp).2.2.2
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [density_two_of_InH2 n hn] at hpos
    exact lt_irrefl _ hpos
  have hp3 : p ≠ 3 := by
    rintro rfl
    rw [density_three_of_InH2 n hn] at hpos
    exact lt_irrefl _ hpos
  have hp4 : p ≠ 4 := by
    rintro rfl
    have hp' : Nat.Prime 4 := hpp
    norm_num at hp'
  have := hpp.two_le
  omega

/-- `sum g/(1-g) <= 2 sum g` on the sieve support. -/
theorem sum_density_div_le (X δ : ℝ) (n : ℕ) (hn : InH2 n) :
    ∑ p ∈ primeSupport X δ n, density n p / (1 - density n p)
      ≤ 2 * ∑ p ∈ primeSupport X δ n, density n p := by
  classical
  have hS : ∀ p ∈ primeSupport X δ n, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp := hS p hp
  have hpos := (Finset.mem_filter.mp hp).2.2.2
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by
    have := five_le_of_mem_primeSupport X δ n hn hp
    exact_mod_cast this
  rw [density_prime_eq_two_div n p hpp hn hpos]
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hnu : 2 / ((p : ℝ) - 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ h1]
    linarith
  have hnu0 : (0 : ℝ) ≤ 2 / ((p : ℝ) - 1) := by positivity
  have hden : (0 : ℝ) < 1 - 2 / ((p : ℝ) - 1) := by linarith
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hle : (1 : ℝ) / 2 ≤ 1 - 2 / ((p : ℝ) - 1) := by linarith
  calc 2 / ((p : ℝ) - 1) / (1 - 2 / ((p : ℝ) - 1))
      ≤ 2 / ((p : ℝ) - 1) / (1 / 2) := by
        rw [div_le_div_iff₀ hden hhalf]
        exact mul_le_mul_of_nonneg_left hle hnu0
    _ = 2 * (2 / ((p : ℝ) - 1)) := by field_simp

/-! ### 7. `sieveProduct` against the support product -/

/-- `sieveProduct` is the product of `1 - density` over the primes below `z`. -/
theorem sieveProduct_eq_prod_density (X δ : ℝ) (n : ℕ) :
    sieveProduct X δ n =
      ∏ p ∈ (Finset.range (⌊Real.exp (Real.log X ^ (1 - δ / 2))⌋₊ + 1)).filter Nat.Prime,
        (1 - density n p) := by
  unfold sieveProduct
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2
  have h1 : (1 : ℝ) - (if p ∣ n then 0 else
      (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) / (Nat.totient p : ℝ))
      = 1 - density n p := by
    by_cases h : p ∣ n
    · have hcop : ¬ Nat.Coprime n p := fun hc => (hpp.coprime_iff_not_dvd.mp hc.symm) h
      rw [if_pos h, density, if_neg hcop]
    · have hcop : Nat.Coprime n p := (hpp.coprime_iff_not_dvd.mpr h).symm
      rw [if_neg h, density, if_pos hcop]
  rw [h1]

/-- The support product is at most twice `sieveProduct`: the two index sets differ only at
primes of zero density and possibly at `p = z` itself. -/
theorem support_prod_le_sieveProduct (X δ : ℝ) (n : ℕ) (hn : InH2 n)
    (hZ5 : 5 ≤ Real.exp (Real.log X ^ (1 - δ / 2))) :
    (∏ p ∈ primeSupport X δ n, (1 - density n p)) ≤ 2 * sieveProduct X δ n := by
  classical
  set Zf : ℝ := Real.exp (Real.log X ^ (1 - δ / 2)) with hZf
  set Sset : Finset ℕ := primeSupport X δ n with hSset
  set Sall : Finset ℕ := (Finset.range (⌊Zf⌋₊ + 1)).filter Nat.Prime with hSall
  set D1 : Finset ℕ := (Sall \ Sset).filter (fun p => 0 < density n p) with hD1
  have hsub : Sset ⊆ Sall := by
    intro p hp
    obtain ⟨hpr, hpp, hplt, -⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpr, hpp⟩
  have hone : ∀ p ∈ Sall \ Sset, p ∉ D1 → (1 - density n p) = 1 := by
    intro p hp hpd
    have hle0 : density n p ≤ 0 := by
      by_contra hc
      push_neg at hc
      exact hpd (Finset.mem_filter.mpr ⟨hp, hc⟩)
    have hge : 0 ≤ density n p := density_nonneg n p
    have hz : density n p = 0 := le_antisymm hle0 hge
    rw [hz]
    norm_num
  have hD1eq : ∏ p ∈ Sall \ Sset, (1 - density n p) = ∏ p ∈ D1, (1 - density n p) := by
    rw [hD1, Finset.prod_filter]
    refine Finset.prod_congr rfl fun p hp => ?_
    by_cases h : 0 < density n p
    · rw [if_pos h]
    · have hnd : p ∉ D1 := by
        intro hmem
        exact h (Finset.mem_filter.mp hmem).2
      rw [if_neg h, hone p hp hnd]
  -- an element of `D1` is a prime below `z` outside the support with positive density, hence `z`
  have hval : ∀ p ∈ D1, p = ⌊Zf⌋₊ := by
    intro p hp
    obtain ⟨hpdiff, hppos⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpall, hpnot⟩ := Finset.mem_sdiff.mp hpdiff
    have hpp : p.Prime := (Finset.mem_filter.mp hpall).2
    have hpZ : p ≤ ⌊Zf⌋₊ := by
      have h := Finset.mem_range.mp (Finset.mem_filter.mp hpall).1
      omega
    have hnotlt : ¬ (p : ℝ) < Zf := by
      intro hlt
      have hmem : p ∈ Finset.range (⌊Zf⌋₊ + 1) := Finset.mem_range.mpr (by omega)
      exact hpnot (Finset.mem_filter.mpr ⟨hmem, hpp, hlt, hppos⟩)
    have h1 : Zf ≤ (p : ℝ) := le_of_not_gt hnotlt
    have h2 : ((⌊Zf⌋₊ : ℕ) : ℝ) ≤ Zf :=
      Nat.floor_le (le_of_lt (Real.exp_pos (Real.log X ^ (1 - δ / 2))))
    have h3 : (p : ℝ) ≤ ((⌊Zf⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpZ
    have : (p : ℝ) = ((⌊Zf⌋₊ : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have hcard : D1.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    rw [hval a ha, hval b hb]
  have hfloor5 : (5 : ℝ) ≤ ((⌊Zf⌋₊ : ℕ) : ℝ) := by
    have := Nat.le_floor hZ5
    exact_mod_cast this
  have hterm : ∀ p ∈ D1, (1 / 2 : ℝ) ≤ 1 - density n p := by
    intro p hp
    have hpos : 0 < density n p := (Finset.mem_filter.mp hp).2
    have hpdiff := (Finset.mem_filter.mp hp).1
    have hpp : p.Prime :=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hpdiff).1).2
    have hp5 : (5 : ℝ) ≤ (p : ℝ) := by
      rw [hval p hp]; exact hfloor5
    rw [density_prime_eq_two_div n p hpp hn hpos]
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have h2 : 2 / ((p : ℝ) - 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ h1]
      linarith
    linarith
  have hD1ge : (1 / 2 : ℝ) ≤ ∏ p ∈ D1, (1 - density n p) := by
    rcases Nat.eq_zero_or_pos D1.card with h | h
    · have hempty : D1 = ∅ := Finset.card_eq_zero.mp h
      rw [hempty, Finset.prod_empty]
      norm_num
    · have hc : D1.card = 1 := by omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
      rw [ha, Finset.prod_singleton]
      exact hterm a (by rw [ha]; exact Finset.mem_singleton_self a)
  have hprod : sieveProduct X δ n = ∏ p ∈ Sall, (1 - density n p) := by
    rw [hSall, hZf]
    exact sieveProduct_eq_prod_density X δ n
  have hspl : ∏ p ∈ Sall, (1 - density n p) =
      (∏ p ∈ Sall \ Sset, (1 - density n p)) * (∏ p ∈ Sset, (1 - density n p)) := by
    rw [Finset.prod_sdiff hsub]
  have hSnonneg : 0 ≤ ∏ p ∈ Sset, (1 - density n p) :=
    Finset.prod_nonneg fun p hp => by
      have h1 : density n p ≤ 1 :=
        (density_prime_lt_one n p hn (Finset.mem_filter.mp hp).2.1).le
      linarith
  rw [hprod, hspl, hD1eq]
  nlinarith [hD1ge, hSnonneg]

/-! ### 8. The truncation deviation -/

/-- Bonferroni truncation deviation, with `x p <= 1` assumed only on `P`. -/
theorem weighted_dev_restricted (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (P : Finset ℕ)
    (hx1 : ∀ p ∈ P, x p ≤ 1) (r : ℕ) :
    |(∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p)
      - ∏ p ∈ P, (1 - x p)|
      ≤ ∑ T ∈ P.powersetCard (r + 1), ∏ p ∈ T, x p := by
  have hwt0 : ∀ S ∈ P.powerset, 0 ≤ LeanLab.PNTSieve.Bonferroni.wt x P S := by
    intro S hS
    unfold LeanLab.PNTSieve.Bonferroni.wt
    refine mul_nonneg (Finset.prod_nonneg fun p _ => hx0 p) ?_
    refine Finset.prod_nonneg fun p hp => ?_
    have hpP : p ∈ P := (Finset.mem_sdiff.mp hp).1
    linarith [hx1 p hpP]
  rw [← LeanLab.PNTSieve.Bonferroni.avg_identity (x := x) P r,
    LeanLab.PNTSieve.Bonferroni.prod_eq_wt_empty x P,
    ← Finset.sum_sub_distrib, ← LeanLab.PNTSieve.Bonferroni.sum_wt_choose x P r]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S hS => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hwt0 S hS)]
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast LeanLab.PNTSieve.Bonferroni.trunc_dev S r) (hwt0 S hS)

/-- `mainSum` of the truncated weights is at most twice the support product. -/
theorem mainSum_le_prod_add (X B δ ε : ℝ) (n K : ℕ) (hn : InH2 n) (hK : 1 ≤ K)
    (hlarge : Real.exp 3 * (∑ p ∈ primeSupport X δ n, density n p) ≤ (K : ℝ) + 1)
    (hY2 : (∑ p ∈ primeSupport X δ n, density n p / (1 - density n p))
      ≤ 2 * ((K : ℝ) + 1)) :
    (sieveModel X B δ ε n hn).mainSum
        (fun d => if d.primeFactors.card ≤ K then (ArithmeticFunction.moebius d : ℝ) else 0)
      ≤ 2 * ∏ p ∈ primeSupport X δ n, (1 - density n p) := by
  classical
  set Sset : Finset ℕ := primeSupport X δ n with hSset
  set Ssum : ℝ := ∑ p ∈ Sset, density n p with hSsum
  set Ysum : ℝ := ∑ p ∈ Sset, density n p / (1 - density n p) with hYsum
  have hS : ∀ p ∈ Sset, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hx0 : ∀ p, 0 ≤ density n p := fun p => density_nonneg n p
  have hx1 : ∀ p ∈ Sset, density n p ≤ 1 := fun p hp =>
    (density_prime_lt_one n p hn (hS p hp)).le
  have hxt1 : ∀ p ∈ Sset, density n p < 1 := fun p hp =>
    density_prime_lt_one n p hn (hS p hp)
  have hS0 : 0 ≤ Ssum := by
    rw [hSsum]
    exact Finset.sum_nonneg fun p _ => hx0 p
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  rw [mainSum_truncated X B δ ε n K hn]
  -- Bonferroni deviation
  have hdev := weighted_dev_restricted (fun p => density n p) hx0 Sset hx1 K
  have hstep1 : (∑ T ∈ Sset.powerset.filter (fun T => T.card ≤ K),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, density n p)
      ≤ (∏ p ∈ Sset, (1 - density n p))
        + ∑ T ∈ Sset.powersetCard (K + 1), ∏ p ∈ T, density n p := by
    have h1 := (abs_le.mp hdev).2
    linarith
  have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
  have hesymm : (∑ T ∈ Sset.powersetCard (K + 1), ∏ p ∈ T, density n p)
      ≤ (Real.exp 1 * Ssum / ((K + 1 : ℕ) : ℝ)) ^ (K + 1) := by
    have h := esymm_le_exp (fun p => density n p) hx0 Sset (k := K + 1) (by omega)
    rw [← hSsum] at h
    exact h
  -- bound the exponential tail
  have hbase0 : (0 : ℝ) ≤ Real.exp 1 * Ssum / ((K + 1 : ℕ) : ℝ) := by positivity
  have hK1' : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by rw [hcast]; exact hK1
  have hbase : Real.exp 1 * Ssum / ((K + 1 : ℕ) : ℝ) ≤ Real.exp (-2) := by
    rcases eq_or_lt_of_le hS0 with h | h
    · rw [← h]
      simp only [mul_zero, zero_div]
      positivity
    · rw [div_le_iff₀ hK1']
      have h1 : Real.exp 1 * Ssum = Real.exp (-2) * (Real.exp 3 * Ssum) := by
        rw [← mul_assoc, ← Real.exp_add]
        norm_num
      rw [h1]
      exact mul_le_mul_of_nonneg_left (by rw [hcast]; exact hlarge) (by positivity)
  have hpow : (Real.exp 1 * Ssum / ((K + 1 : ℕ) : ℝ)) ^ (K + 1)
      ≤ Real.exp (-2 * ((K + 1 : ℕ) : ℝ)) := by
    calc (Real.exp 1 * Ssum / ((K + 1 : ℕ) : ℝ)) ^ (K + 1)
        ≤ (Real.exp (-2)) ^ (K + 1) := pow_le_pow_left₀ hbase0 hbase (K + 1)
      _ = Real.exp (-2 * ((K + 1 : ℕ) : ℝ)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  have hexp2 : Real.exp (-2 * ((K + 1 : ℕ) : ℝ)) ≤ Real.exp (-(Ysum)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [hcast]
    linarith
  have hVge : Real.exp (-(Ysum)) ≤ ∏ p ∈ Sset, (1 - density n p) := by
    have := prod_one_sub_ge_exp Sset (fun p => density n p) (fun p _ => hx0 p) hxt1
    rw [← hYsum] at this
    exact this
  linarith

/-! ### 9. Arithmetic for large `X` -/

/-- `log log X` is eventually below any fixed positive multiple of `(log X)^(δ/2)`. -/
theorem eventually_loglog_le (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∀ᶠ X : ℝ in Filter.atTop, Real.log (Real.log X) ≤ C * (Real.log X) ^ (δ / 2) := by
  have hb : ∀ᶠ u : ℝ in Filter.atTop, Real.log u ≤ C * u ^ (δ / 2) := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < δ / 2 by linarith)).bound hC
    filter_upwards [h, Filter.eventually_gt_atTop (1 : ℝ)] with u hu hu1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.log_pos hu1),
      abs_of_pos (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < u) _)] at hu
    exact hu
  exact Real.tendsto_log_atTop.eventually hb

/-- Numerical side conditions for the truncated weight construction at large `X`. -/
theorem eventually_side_conditions (B δ ε : ℝ) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      Real.exp 1 < X ∧
      5 ≤ Real.exp (Real.log X ^ (1 - δ / 2)) ∧
      2 ≤ ⌊Real.exp (Real.log X ^ (1 - δ / 2))⌋₊ ∧
      400 * Real.exp 3 * (Real.log (Real.log X) + 2)
        ≤ (7 / 108) * (Real.log X) ^ (δ / 2) := by
  have hexp2 : (0 : ℝ) < δ / 2 := by linarith
  have he3 : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
  have hloglog := eventually_loglog_le δ (7 / 108 / (800 * Real.exp 3)) hδ (by positivity)
  have hgrowth : ∀ᶠ X : ℝ in Filter.atTop,
      (216 * 800 * Real.exp 3 / 7) ≤ (Real.log X) ^ (δ / 2) := by
    have ht := (tendsto_rpow_atTop hexp2).comp Real.tendsto_log_atTop
    exact ht.eventually (Filter.eventually_ge_atTop _)
  filter_upwards [hloglog, hgrowth, Filter.eventually_gt_atTop (Real.exp 4)] with X hll hgr hX4
  have hXe : Real.exp 1 < X :=
    lt_trans (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 4)) hX4
  have hL4 : (4 : ℝ) < Real.log X := by
    have h2 := Real.log_lt_log (Real.exp_pos 4) hX4
    rwa [Real.log_exp] at h2
  refine ⟨hXe, ?_, ?_, ?_⟩
  · have hL1 : (1 : ℝ) < Real.log X := by
      have h2 := Real.log_lt_log (Real.exp_pos 1) hXe
      rwa [Real.log_exp] at h2
    have ht2 : (2 : ℝ) ≤ (Real.log X) ^ (1 - δ / 2) := by
      have hbase : (2 : ℝ) ≤ (Real.log X) ^ (1 / 2 : ℝ) := by
        have h2 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
          rw [← Real.sqrt_eq_rpow]
          norm_num
        calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := h2.symm
          _ ≤ (Real.log X) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4) (le_of_lt hL4)
                (by norm_num : (0 : ℝ) ≤ 1 / 2)
      exact le_trans hbase (Real.rpow_le_rpow_of_exponent_le hL1.le (by linarith))
    have he2 : Real.exp 2 ≤ Real.exp ((Real.log X) ^ (1 - δ / 2)) := Real.exp_le_exp.mpr ht2
    have h5 : (5 : ℝ) ≤ Real.exp 2 := by
      have h := Real.exp_one_gt_d9
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [he]
      nlinarith [h]
    linarith
  · have hL1 : (1 : ℝ) < Real.log X := by
      have h2 := Real.log_lt_log (Real.exp_pos 1) hXe
      rwa [Real.log_exp] at h2
    have ht2 : (2 : ℝ) ≤ (Real.log X) ^ (1 - δ / 2) := by
      have hbase : (2 : ℝ) ≤ (Real.log X) ^ (1 / 2 : ℝ) := by
        have h2 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
          rw [← Real.sqrt_eq_rpow]
          norm_num
        calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := h2.symm
          _ ≤ (Real.log X) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4) (le_of_lt hL4)
                (by norm_num : (0 : ℝ) ≤ 1 / 2)
      exact le_trans hbase (Real.rpow_le_rpow_of_exponent_le hL1.le (by linarith))
    have h5 : (2 : ℝ) ≤ Real.exp ((Real.log X) ^ (1 - δ / 2)) :=
      le_trans (by linarith : (2 : ℝ) ≤ (Real.log X) ^ (1 - δ / 2) + 1) (Real.add_one_le_exp _)
    exact Nat.le_floor h5
  · have hepos : Real.exp 3 ≠ 0 := (Real.exp_pos 3).ne'
    have hk : 400 * Real.exp 3 * (7 / 108 / (800 * Real.exp 3)) = (7 / 216 : ℝ) := by
      field_simp
      ring
    have hmul : 400 * Real.exp 3 * Real.log (Real.log X)
        ≤ 400 * Real.exp 3 * ((7 / 108 / (800 * Real.exp 3)) * (Real.log X) ^ (δ / 2)) :=
      mul_le_mul_of_nonneg_left hll (by positivity)
    have heq : 400 * Real.exp 3 * ((7 / 108 / (800 * Real.exp 3)) * (Real.log X) ^ (δ / 2))
        = (7 / 216) * (Real.log X) ^ (δ / 2) := by
      rw [← mul_assoc, hk]
    have hb2 : 800 * Real.exp 3 ≤ (7 / 216) * (Real.log X) ^ (δ / 2) := by
      have hstep := mul_le_mul_of_nonneg_left hgr (by norm_num : (0 : ℝ) ≤ 7 / 216)
      calc 800 * Real.exp 3 = (7 / 216) * (216 * 800 * Real.exp 3 / 7) := by ring
        _ ≤ (7 / 216) * (Real.log X) ^ (δ / 2) := hstep
    have hexp : 400 * Real.exp 3 * (Real.log (Real.log X) + 2)
        = 400 * Real.exp 3 * Real.log (Real.log X) + 800 * Real.exp 3 := by ring
    linarith [hmul, heq, hb2, hexp]

/-! ### 10. The leaf -/

/-- LEAF: Kumchev and Liu page 13 Lemma 3.7 and page 17 before display 58.
Iwaniec, Rosser's sieve, DOI 10.4064/aa-36-2-171-202, page 172 Theorem 1
and page 179 formulas 3.4, 3.6 and 3.7. The upper coefficients have absolute
value at most one and vanish above D. Their main sum is at most a constant
times the sieve product, using the uniform dimension two bound stated on
Kumchev and Liu page 17 and the fact that log D over log z tends to infinity.
Primes with zero density are omitted. Strict cutoff endpoints and the closed
product convention cost a fixed factor at large z. CITED weight construction
and uniform dimension estimate. No sequence count or remainder bound is assumed. -/
theorem upper_weights (B δ ε : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, ∀ hn : InH2 n,
      ∃ μ : ℕ → ℝ, BoundingSieve.IsUpperMoebius μ ∧
        (∀ d ∈ (primeProduct X δ n).divisors, Y X ε ^ (1 / 9 : ℝ) < (d : ℝ) → μ d = 0) ∧
        (∀ d ∈ (primeProduct X δ n).divisors, |μ d| ≤ 1) ∧
        (sieveModel X B δ ε n hn).mainSum μ ≤ C * sieveProduct X δ n := by

  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp (eventually_side_conditions B δ ε hB hδ hδ1 hε)
  refine ⟨4, max X0 1, by norm_num, ?_⟩
  intro X hX n hn
  obtain ⟨hXe, hZ5, hZ2, harith⟩ := hX0 X (le_trans (le_max_left _ _) hX)
  set t : ℝ := (Real.log X) ^ (1 - δ / 2) with ht
  set Zf : ℝ := Real.exp t with hZf
  set Dv : ℝ := Y X ε ^ (1 / 9 : ℝ) with hDv
  set K : ℕ := 2 * ⌊(Real.log Dv / t) / 4⌋₊ with hKdef
  have hX1 : (1 : ℝ) < X :=
    lt_trans (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)) hXe
  have hX0' : (0 : ℝ) < X := by linarith
  have hL1 : (1 : ℝ) < Real.log X := by
    have h2 := Real.log_lt_log (Real.exp_pos 1) hXe
    rwa [Real.log_exp] at h2
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have ht0 : (0 : ℝ) < t := by
    rw [ht]
    exact Real.rpow_pos_of_pos hL0 _
  have hY1 : (1 : ℝ) ≤ Y X ε := by
    unfold Y
    calc (1 : ℝ) = (1 : ℝ) ^ (7 / 12 + ε / 2) := (Real.one_rpow _).symm
      _ ≤ X ^ (7 / 12 + ε / 2) :=
          Real.rpow_le_rpow (by norm_num) hX1.le (by linarith)
  have hDv1 : (1 : ℝ) ≤ Dv := by
    rw [hDv]
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / 9 : ℝ) := (Real.one_rpow _).symm
      _ ≤ (Y X ε) ^ (1 / 9 : ℝ) := Real.rpow_le_rpow (by norm_num) hY1 (by norm_num)
  have hlogD0 : 0 ≤ Real.log Dv := Real.log_nonneg hDv1
  have hlogD : Real.log Dv = ((7 / 12 + ε / 2) * (1 / 9)) * Real.log X := by
    have hYpos : (0 : ℝ) < Y X ε := by unfold Y; positivity
    rw [hDv, Real.log_rpow hYpos, Y, Real.log_rpow hX0']
    ring
  -- the level exponent
  have hKle : (K : ℝ) ≤ (Real.log Dv / t) / 2 := by
    have h1 : (⌊(Real.log Dv / t) / 4⌋₊ : ℝ) ≤ (Real.log Dv / t) / 4 :=
      Nat.floor_le (by apply div_nonneg _ (by norm_num); exact div_nonneg hlogD0 ht0.le)
    have h2 : (K : ℝ) = 2 * (⌊(Real.log Dv / t) / 4⌋₊ : ℝ) := by
      rw [hKdef]; push_cast; ring
    rw [h2]; linarith
  have hKlow : (Real.log Dv / t) / 2 - 2 ≤ (K : ℝ) := by
    have h1 : (Real.log Dv / t) / 4 - 1 < (⌊(Real.log Dv / t) / 4⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one ((Real.log Dv / t) / 4)
      linarith
    have h2 : (K : ℝ) = 2 * (⌊(Real.log Dv / t) / 4⌋₊ : ℝ) := by
      rw [hKdef]; push_cast; ring
    rw [h2]; linarith
  have hlev : (K : ℝ) * Real.log Zf ≤ Real.log Dv := by
    rw [hZf, Real.log_exp]
    calc (K : ℝ) * t ≤ ((Real.log Dv / t) / 2) * t :=
          mul_le_mul_of_nonneg_right hKle ht0.le
      _ = Real.log Dv / 2 := by field_simp
      _ ≤ Real.log Dv := by linarith
  have hKeven : Even K := by
    rw [hKdef]
    exact ⟨_, by ring⟩
  -- the two density sums
  have hSsum : (∑ p ∈ primeSupport X δ n, density n p)
      ≤ 4 * (Real.log (Real.log (⌊Zf⌋₊ : ℝ)) + 12) := by
    rw [hZf, ht]
    exact sum_density_le X δ n hn hX1 hδ hδ1 hZ2
  have hYsum : (∑ p ∈ primeSupport X δ n, density n p / (1 - density n p))
      ≤ 2 * ∑ p ∈ primeSupport X δ n, density n p := sum_density_div_le X δ n hn
  have hllZ : Real.log (Real.log (⌊Zf⌋₊ : ℝ)) ≤ Real.log (Real.log X) := by
    have hfl1 : (1 : ℝ) < (⌊Zf⌋₊ : ℝ) := by
      have h2 : (2 : ℝ) ≤ (⌊Zf⌋₊ : ℝ) := by exact_mod_cast hZ2
      linarith
    have h1 : Real.log (⌊Zf⌋₊ : ℝ) ≤ t := by
      have hfl : (1 : ℕ) ≤ ⌊Real.exp t⌋₊ :=
        Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ Real.exp t by
          push_cast
          exact Real.one_le_exp ht0.le)
      have hpos : (0 : ℝ) < (⌊Real.exp t⌋₊ : ℝ) := by
        have h1 : (0 : ℕ) < ⌊Real.exp t⌋₊ := by omega
        exact_mod_cast h1
      rw [hZf]
      have hstep := Real.log_le_log hpos (Nat.floor_le (le_of_lt (Real.exp_pos t)))
      rwa [Real.log_exp] at hstep
    have h2 : Real.log t ≤ Real.log (Real.log X) := by
      rw [ht]
      refine Real.log_le_log (by positivity) ?_
      calc (Real.log X) ^ (1 - δ / 2) ≤ (Real.log X) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1.le (by linarith)
        _ = Real.log X := Real.rpow_one _
    calc Real.log (Real.log (⌊Zf⌋₊ : ℝ)) ≤ Real.log t :=
          Real.log_le_log (by linarith [Real.log_pos hfl1]) h1
      _ ≤ Real.log (Real.log X) := h2
  have hllX0 : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hL1.le
  have hA0 : (0 : ℝ) ≤ Real.log (Real.log (⌊Zf⌋₊ : ℝ)) := by
    have hfloor5 : (5 : ℝ) ≤ ((⌊Zf⌋₊ : ℕ) : ℝ) := by
      have h := Nat.le_floor hZ5
      exact_mod_cast h
    have h1 : (1 : ℝ) < Real.log ((⌊Zf⌋₊ : ℕ) : ℝ) := by
      have h2 : (1 : ℝ) < Real.log 5 := by
        have h := Real.log_lt_log (Real.exp_pos 1)
          (by linarith [Real.exp_one_lt_d9] : Real.exp 1 < 5)
        rwa [Real.log_exp] at h
      have h3 : Real.log 5 ≤ Real.log ((⌊Zf⌋₊ : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num : (0 : ℝ) < 5) hfloor5
      linarith
    exact (Real.log_pos h1).le
  -- `s/2` dominates the elementary-symmetric bound
  have hsBnd : Real.exp 3 * (4 * (Real.log (Real.log (⌊Zf⌋₊ : ℝ)) + 12) + 1) + 1
      ≤ (Real.log Dv / t) / 2 := by
    have hs_eq : Real.log Dv / t = ((7 / 12 + ε / 2) * (1 / 9)) * (Real.log X) ^ (δ / 2) := by
      rw [hlogD, ht]
      rw [div_eq_iff (Real.rpow_pos_of_pos hL0 _).ne']
      calc ((7 / 12 + ε / 2) * (1 / 9)) * Real.log X
          = ((7 / 12 + ε / 2) * (1 / 9)) *
              ((Real.log X) ^ (δ / 2) * (Real.log X) ^ (1 - δ / 2)) := by
            rw [← Real.rpow_add hL0, show δ / 2 + (1 - δ / 2) = 1 by ring, Real.rpow_one]
        _ = (((7 / 12 + ε / 2) * (1 / 9)) * (Real.log X) ^ (δ / 2)) *
              (Real.log X) ^ (1 - δ / 2) := by ring
    rw [hs_eq]
    have he : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
    have hstep : Real.exp 3 * (4 * (Real.log (Real.log (⌊Zf⌋₊ : ℝ)) + 12) + 1) + 1
        ≤ 50 * (Real.exp 3 * (Real.log (Real.log X) + 2)) := by
      have h4 : (4 * (Real.log (Real.log X) + 12) + 2)
          ≤ 50 * (Real.log (Real.log X) + 2) := by linarith
      have h5 : Real.exp 3 * (4 * (Real.log (Real.log X) + 12) + 2)
          ≤ 50 * (Real.exp 3 * (Real.log (Real.log X) + 2)) := by
        nlinarith [h4, Real.exp_pos 3]
      nlinarith [hllZ, he, h5, Real.exp_pos 3]
    have hfin : 50 * (Real.exp 3 * (Real.log (Real.log X) + 2))
        ≤ (((7 / 12 + ε / 2) * (1 / 9)) * (Real.log X) ^ (δ / 2)) / 2 := by
      have hcge : (7 / 108 : ℝ) ≤ (7 / 12 + ε / 2) * (1 / 9) := by nlinarith [hε]
      have ht2pos : (0 : ℝ) ≤ (Real.log X) ^ (δ / 2) := Real.rpow_nonneg hL0.le _
      linarith [harith, mul_le_mul_of_nonneg_right hcge ht2pos]
    linarith [hstep, hfin]
  have hBnd0 : (0 : ℝ) ≤ 4 * (Real.log (Real.log (⌊Zf⌋₊ : ℝ)) + 12) + 1 := by
    linarith
  have hlarge : Real.exp 3 * (∑ p ∈ primeSupport X δ n, density n p) ≤ (K : ℝ) + 1 := by
    have h1 : Real.exp 3 * (∑ p ∈ primeSupport X δ n, density n p)
        ≤ Real.exp 3 * (4 * (Real.log (Real.log (⌊Zf⌋₊ : ℝ)) + 12)) :=
      mul_le_mul_of_nonneg_left hSsum (Real.exp_pos 3).le
    have hb : Real.exp 3 * (4 * (Real.log (Real.log (⌊Zf⌋₊ : ℝ)) + 12))
        ≤ Real.exp 3 * (4 * (Real.log (Real.log (⌊Zf⌋₊ : ℝ)) + 12) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 3).le
    linarith [h1, hb, hsBnd, hKlow]
  have hK1 : 1 ≤ K := by
    have h1 : (49 : ℝ) ≤ (Real.log Dv / t) / 2 := by
      have he1 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
      have hmul : (1 : ℝ) * (4 * (Real.log (Real.log (⌊Zf⌋₊ : ℝ)) + 12) + 1)
          ≤ Real.exp 3 * (4 * (Real.log (Real.log (⌊Zf⌋₊ : ℝ)) + 12) + 1) :=
        mul_le_mul_of_nonneg_right he1 (by linarith)
      linarith [hsBnd, hmul, hA0]
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by linarith [hKlow, h1]
    exact_mod_cast h2
  have hY2 : (∑ p ∈ primeSupport X δ n, density n p / (1 - density n p))
      ≤ 2 * ((K : ℝ) + 1) := by
    have h1 : (∑ p ∈ primeSupport X δ n, density n p)
        ≤ 4 * (Real.log (Real.log (⌊Zf⌋₊ : ℝ)) + 12) + 1 := by linarith [hSsum]
    have h2 : Real.exp 3 * (4 * (Real.log (Real.log (⌊Zf⌋₊ : ℝ)) + 12) + 1) ≤ (K : ℝ) + 1 := by
      linarith [hsBnd, hKlow]
    have he1 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
    nlinarith [hYsum, h1, h2, hBnd0, he1]
  refine ⟨fun d => if d.primeFactors.card ≤ K then (ArithmeticFunction.moebius d : ℝ) else 0,
    isUpperMoebius_truncated K hKeven, ?_, ?_, ?_⟩
  · intro d hd hDd
    by_cases hc : d.primeFactors.card ≤ K
    · exfalso
      have hlev' : (K : ℝ) * Real.log (Real.exp (Real.log X ^ (1 - δ / 2)))
          ≤ Real.log (Y X ε ^ (1 / 9 : ℝ)) := hlev
      have hlt := divisor_lt_level X δ ε n K hn hX1 hδ hδ1 hlev' hd hc
      have hDd' : Y X ε ^ (1 / 9 : ℝ) < (d : ℝ) := hDd
      linarith [hlt, hDd']
    · simp only [hc, ite_false]
  · intro d hd
    exact abs_truncated_le_one K d
  · have h1 := mainSum_le_prod_add X B δ ε n K hn hK1 hlarge hY2
    have h2 : (∏ p ∈ primeSupport X δ n, (1 - density n p)) ≤ 2 * sieveProduct X δ n :=
      support_prod_le_sieveProduct X δ n hn hZ5
    calc (sieveModel X B δ ε n hn).mainSum
          (fun d => if d.primeFactors.card ≤ K then (ArithmeticFunction.moebius d : ℝ) else 0)
        ≤ 2 * ∏ p ∈ primeSupport X δ n, (1 - density n p) := h1
      _ ≤ 2 * (2 * sieveProduct X δ n) := by
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 4 * sieveProduct X δ n := by ring

/-- Page 17 display 58, the exact Rosser application from explicit upper weights.
CONDITIONAL ON upper_weights. The finite support and remainder steps are proved. -/
theorem rosser_application_from_weights (B δ ε : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      siftedCount X B δ ε n ≤ C *
        (primeMass X B ε * sieveProduct X δ n + remainder X B ε n) := by
  obtain ⟨C, Xw, hC, hw⟩ := upper_weights B δ ε hB hδ hδ1 hε hε1
  obtain ⟨Xp, hp⟩ := Filter.eventually_atTop.mp (rough_support_parameters B ε hB hε)
  refine ⟨C + 1, max Xw Xp, by positivity, ?_⟩
  intro X hX n hn hXn hnle
  obtain ⟨hY, hroot, hz, hcube⟩ := hp X ((le_max_right _ _).trans hX)
  obtain ⟨μ, hupper, hlevel, hbound, hmain⟩ := hw X ((le_max_left _ _).trans hX) n hn
  have hb := sifted_upper_of_weights X B δ ε C n hn hY hroot hz hcube μ hupper hlevel hbound hmain
  have hNV : 0 ≤ primeMass X B ε * sieveProduct X δ n :=
    mul_nonneg (primeMass_nonneg X B ε) (sieveProduct_nonneg X δ n)
  have hR := remainder_nonneg X B ε n
  calc _ ≤ C * (primeMass X B ε * sieveProduct X δ n) + remainder X B ε n := hb
       _ ≤ (C + 1) * (primeMass X B ε * sieveProduct X δ n + remainder X B ε n) := by
         nlinarith [mul_nonneg hC.le hR]

end LeanLab.KumchevLiu2007.Task506g
