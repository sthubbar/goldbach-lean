module

public import LeanLab.KumchevLiu2007.Decomp506c
public import LeanLab.KumchevLiu2007.Decomp506d
public import LeanLab.PNTSieve.MertensUpper
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
Maximal prime distribution and the weighted transfer on page 17.
Source https://arxiv.org/abs/0801.0130 between displays 57 and 58.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

-- Port fix for Mathlib v4.35.0-rc3: its instance making a simple nilpotent additive group
-- commutative is found for `ZMod p` under `Fact p.Prime` and blocks `ring` and `simp`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace LeanLab.KumchevLiu2007.Task542a

open Real Task506b
open scoped BigOperators Topology

/-- Page 17, the squarefree divisor weight factors over its prime divisors. -/
theorem squarefree_divisor_weight (n : ℕ) (hn : Squarefree n) :
    (n.divisors.card : ℝ) ^ 2 / n = ∏ p ∈ n.primeFactors, ((4 : ℝ) / p) := by
  have hc : n.divisors.card = ∏ p ∈ n.primeFactors, (2 : ℕ) := by
    rw [Nat.card_divisors hn.ne_zero]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hn (Nat.mem_primeFactors.mp hp).1
      (Nat.mem_primeFactors.mp hp).2.1]
  have hnR : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    simpa only [Nat.cast_prod] using congrArg (fun k : ℕ => (k : ℝ))
      (Nat.prod_primeFactors_of_squarefree hn).symm
  rw [hc, Nat.cast_prod, hnR, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  norm_num


/-- Page 17 Cauchy step, finite Euler upper bound for the reciprocal moment. -/
theorem squarefree_moment_euler (N : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter Squarefree, (n.divisors.card : ℝ) ^ 2 / n) ≤
      ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 + (4 : ℝ) / p) := by
  classical
  let S := (Finset.Icc 1 N).filter Nat.Prime
  let T := (Finset.Icc 1 N).filter Squarefree
  have hinj : Set.InjOn Nat.primeFactors (↑T : Set ℕ) := by
    intro a ha b hb hab
    have hsa := (Finset.mem_filter.mp ha).2
    have hsb := (Finset.mem_filter.mp hb).2
    rw [← Nat.prod_primeFactors_of_squarefree hsa,
      ← Nat.prod_primeFactors_of_squarefree hsb, hab]
  have hsub : T.image Nat.primeFactors ⊆ S.powerset := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_powerset.mpr
    intro p hp
    obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
    have hnN := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hpp.pos, (Nat.le_of_dvd (by omega : 0 < n) hpn).trans hnN.2⟩, hpp⟩
  calc
    _ = ∑ n ∈ T, ∏ p ∈ n.primeFactors, ((4 : ℝ) / p) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact squarefree_divisor_weight n (Finset.mem_filter.mp hn).2
    _ = ∑ t ∈ T.image Nat.primeFactors, ∏ p ∈ t, ((4 : ℝ) / p) :=
      (Finset.sum_image (f := fun t : Finset ℕ => ∏ p ∈ t, ((4 : ℝ) / p)) hinj).symm
    _ ≤ ∑ t ∈ S.powerset, ∏ p ∈ t, ((4 : ℝ) / p) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ =>
        Finset.prod_nonneg fun _ _ => by positivity)
    _ = _ := (Finset.prod_one_add S).symm


/-- Page 17 Cauchy step, logarithmic bound for the squared divisor reciprocal moment. -/
theorem squarefree_moment_log (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ (Finset.Icc 1 N).filter Squarefree, (n.divisors.card : ℝ) ^ 2 / n) ≤
      Real.exp 48 * Real.log N ^ 4 := by
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  calc
    _ ≤ ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 + (4 : ℝ) / p) :=
      squarefree_moment_euler N
    _ ≤ Real.exp (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (4 : ℝ) / p) :=
      Real.prod_one_add_le_exp_sum _ (fun _ => by positivity)
    _ ≤ Real.exp (4 * (Real.log (Real.log N) + 12)) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left
        (LeanLab.PNTSieve.Mertens.sum_inv_primes_le N hN) (by norm_num : (0 : ℝ) ≤ 4)
      simpa only [Finset.mul_sum, mul_one_div] using h
    _ = Real.exp 48 * Real.log N ^ 4 := by
      rw [mul_add, Real.exp_add]
      rw [show (4 : ℝ) * Real.log (Real.log N) =
        (4 : ℕ) * Real.log (Real.log N) by norm_num,
        Real.exp_nat_mul, Real.exp_log hL]
      norm_num
      ring


/-- Page 17, weighted Cauchy with the squared divisor reciprocal moment.
CONDITIONAL ON the explicit pointwise and distribution estimates. -/
theorem divisor_weighted_cauchy (N : ℕ) (hN : 2 ≤ N) (E : ℕ → ℝ)
    (M V : ℝ) (hM : 0 ≤ M)
    (hE : ∀ d ∈ (Finset.Icc 1 N).filter Squarefree, 0 ≤ E d)
    (hpoint : ∀ d ∈ (Finset.Icc 1 N).filter Squarefree, (d : ℝ) * E d ≤ M)
    (hBV : ∑ d ∈ (Finset.Icc 1 N).filter Squarefree, E d ≤ V) :
    (∑ d ∈ (Finset.Icc 1 N).filter Squarefree, (d.divisors.card : ℝ) * E d) ^ 2 ≤
      (Real.exp 48 * Real.log N ^ 4) * M * V := by
  apply Task506c.cauchy_progression_errors _ _ _ (fun d : ℕ => (d : ℝ)) M
    (Real.exp 48 * Real.log N ^ 4) V _ hE hM (by positivity) hpoint
    (squarefree_moment_log N hN) hBV
  intro d hd
  exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1


/-- Page 17, extracting the logarithmic saving from the squared Cauchy estimate. -/
theorem cauchy_log_absorption (S K T L A : ℝ) (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hL : 0 < L) (hbound : S ^ 2 ≤ K * T ^ 2 * L ^ (-2 * A)) :
    S ≤ Real.sqrt K * T * L ^ (-A) := by
  have hsq : (Real.sqrt K * T * L ^ (-A)) ^ 2 = K * T ^ 2 * L ^ (-2 * A) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hK, ← Real.rpow_mul_natCast hL.le]
    congr 2
    ring
  have hnonneg : 0 ≤ Real.sqrt K * T * L ^ (-A) := by positivity
  nlinarith [sq_nonneg (S - Real.sqrt K * T * L ^ (-A))]


/-- Page 17, a general finite prime Euler product has a fixed logarithmic power. -/
theorem prime_euler_log (k N : ℕ) (hN : 2 ≤ N) :
    (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 + (k : ℝ) / p)) ≤
      Real.exp (12 * (k : ℝ)) * Real.log N ^ k := by
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  calc
    _ ≤ Real.exp (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (k : ℝ) / p) :=
      Real.prod_one_add_le_exp_sum _ (fun _ => by positivity)
    _ ≤ Real.exp ((k : ℝ) * (Real.log (Real.log N) + 12)) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left
        (LeanLab.PNTSieve.Mertens.sum_inv_primes_le N hN) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      simpa only [Finset.mul_sum, mul_one_div] using h
    _ = Real.exp (12 * (k : ℝ)) * Real.log N ^ k := by
      rw [mul_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log hL]
      ring


/-- Page 17, an elementary totient reciprocal bound for the pointwise error. -/
theorem totient_reciprocal_le (N d : ℕ) (hN : 2 ≤ N) (hd : 0 < d) (hdN : d ≤ N) :
    (d : ℝ) / Nat.totient d ≤ Real.exp 24 * Real.log N ^ 2 := by
  classical
  let S := (Finset.Icc 1 N).filter Nat.Prime
  have hsub : d.primeFactors ⊆ S := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hpp.pos, (Nat.le_of_dvd hd hpd).trans hdN⟩, hpp⟩
  have htot : (Nat.totient d : ℝ) = (d : ℝ) *
      ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors d)
    push_cast at h
    exact h
  have hfac (p : ℕ) (hp : p.Prime) : 0 < 1 - (p : ℝ)⁻¹ := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
  have hprod : 0 < ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_pos fun p hp => hfac p (Nat.mem_primeFactors.mp hp).1
  have heq : (d : ℝ) / Nat.totient d =
      ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [Finset.prod_inv_distrib, htot]
    field_simp [hprod.ne', (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)]
  rw [heq]
  calc
    _ ≤ ∏ p ∈ d.primeFactors, (1 + (2 : ℝ) / p) := by
      apply Finset.prod_le_prod₀ (fun p hp => (inv_pos.mpr (hfac p (Nat.mem_primeFactors.mp hp).1)).le)
      intro p hp
      have hpp := (Nat.mem_primeFactors.mp hp).1
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have hp0 : (0 : ℝ) < p := by linarith
      rw [← one_div]
      apply (div_le_iff₀ (hfac p hpp)).mpr
      have hi : (p : ℝ)⁻¹ ≤ 1 / 2 := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
      have hi0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
      simp only [div_eq_mul_inv]
      nlinarith
    _ ≤ ∏ p ∈ S, (1 + (2 : ℝ) / p) :=
      Finset.prod_le_prod_of_subset_of_one_le₀ hsub
        (fun _ _ => by positivity) (fun p _ _ => by
          have h : (0 : ℝ) ≤ 2 / p := by positivity
          linarith)
    _ ≤ Real.exp 24 * Real.log N ^ 2 := by
      convert prime_euler_log 2 N hN using 1 <;> norm_num [S]


/-- Page 17, prime counting in a reduced residue class up to a real endpoint. -/
noncomputable def primeAP (x : ℝ) (d a : ℕ) : ℝ :=
  (((Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ p % d = a % d)).card : ℝ)

/-- Page 17, the elementary progression count retains the reciprocal modulus. -/
theorem primeAP_trivial (x : ℝ) (d a : ℕ) (hx : 0 ≤ x) (hd : 0 < d) :
    (d : ℝ) * primeAP x d a ≤ x + d := by
  classical
  let S := (Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ p % d = a % d)
  have hcard : S.card ≤ ⌊x⌋₊ / d + 1 := by
    have h := Finset.card_le_card_of_injOn (fun p : ℕ => p / d)
      (s := S) (t := Finset.range (⌊x⌋₊ / d + 1)) ?_ ?_
    · simpa only [Finset.card_range] using h
    · intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.div_le_div_right (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2))
    · intro p hp q hq heq
      have hpm := (Finset.mem_filter.mp hp).2.2
      have hqm := (Finset.mem_filter.mp hq).2.2
      change p / d = q / d at heq
      have hpdiv := Nat.mod_add_div p d
      have hqdiv := Nat.mod_add_div q d
      rw [heq] at hpdiv
      omega
  have hmul : d * S.card ≤ ⌊x⌋₊ + d := by
    calc _ ≤ d * (⌊x⌋₊ / d + 1) := Nat.mul_le_mul_left d hcard
      _ ≤ ⌊x⌋₊ + d := by
        rw [Nat.mul_add, Nat.mul_one]
        exact Nat.add_le_add_right (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self ⌊x⌋₊ d) d
  have hmulR : (d : ℝ) * (S.card : ℝ) ≤ (⌊x⌋₊ : ℝ) + d := by exact_mod_cast hmul
  change (d : ℝ) * (S.card : ℝ) ≤ x + d
  linarith [Nat.floor_le hx]


/-- Page 17, a crude bound for the logarithmic integral at every endpoint. -/
theorem log_integral_abs_le (x : ℝ) (hx : 2 ≤ x) :
    |∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤ 2 * x := by
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (2 : ℝ)) (b := x) (C := (2 : ℝ)) (f := fun t => 1 / Real.log t) ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x - 2)] at h
    linarith
  · intro t ht
    rw [Set.uIoc_of_le hx] at ht
    have hlog : (1 : ℝ) / 2 ≤ Real.log t :=
      hlog2.trans (Real.log_le_log (by norm_num) ht.1.le)
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / Real.log t)]
    exact (div_le_iff₀ (by linarith : 0 < Real.log t)).mpr (by linarith)


/-- Page 17, the maximal prime counting discrepancy, including zero. -/
noncomputable def primeError (T : ℝ) (d : ℕ) : ℝ :=
  sSup (insert 0 {v : ℝ | ∃ a : ℕ, ∃ x : ℝ,
    a < d ∧ Nat.Coprime a d ∧ 2 ≤ x ∧ x ≤ T ∧
      v = |primeAP x d a - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d|})

/-- Page 17, the elementary prime discrepancy bound before taking the maximum. -/
theorem prime_discrepancy_pointwise (T x : ℝ) (d a : ℕ)
    (hT : 2 ≤ T) (hL : 1 ≤ Real.log T) (hd : 0 < d) (hdT : (d : ℝ) ≤ T)
    (hx : 2 ≤ x) (hxT : x ≤ T) :
    (d : ℝ) * |primeAP x d a -
      (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d| ≤
      (2 + 2 * Real.exp 24) * T * Real.log T ^ 2 := by
  have hN : 2 ≤ ⌊T⌋₊ := Nat.le_floor hT
  have hphi : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd
  have hlog : Real.log (⌊T⌋₊ : ℝ) ≤ Real.log T :=
    Real.log_le_log (by exact_mod_cast (show 0 < ⌊T⌋₊ by omega)) (Nat.floor_le (by linarith))
  have hlog0 : 0 ≤ Real.log (⌊T⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ ⌊T⌋₊ by omega))
  have hr : (d : ℝ) / Nat.totient d ≤ Real.exp 24 * Real.log T ^ 2 := by
    apply (totient_reciprocal_le ⌊T⌋₊ d hN hd (Nat.le_floor hdT)).trans
    gcongr
  let I := ∫ t in (2 : ℝ)..x, 1 / Real.log t
  have hi : |I| ≤ 2 * T := (log_integral_abs_le x hx).trans (by linarith)
  have hp : (d : ℝ) * primeAP x d a ≤ 2 * T :=
    (primeAP_trivial x d a (by linarith) hd).trans (by linarith)
  have habs := abs_sub (primeAP x d a) (I / Nat.totient d)
  rw [abs_of_nonneg (show 0 ≤ primeAP x d a by unfold primeAP; positivity),
    abs_div, abs_of_pos hphi] at habs
  have hmul := mul_le_mul_of_nonneg_left habs (show (0 : ℝ) ≤ d by positivity)
  have hm := mul_le_mul hr hi (abs_nonneg I) (by positivity : 0 ≤ Real.exp 24 * Real.log T ^ 2)
  have hrewrite : (d : ℝ) * (primeAP x d a + |I| / Nat.totient d) =
      (d : ℝ) * primeAP x d a + ((d : ℝ) / Nat.totient d) * |I| := by ring
  rw [hrewrite] at hmul
  change (d : ℝ) * |primeAP x d a - I / Nat.totient d| ≤ _
  have hsq : 1 ≤ Real.log T ^ 2 := by nlinarith
  nlinarith [mul_nonneg (show 0 ≤ T by linarith) (show 0 ≤ Real.log T ^ 2 - 1 by linarith)]


/-- Page 17, the maximal prime error satisfies the same reciprocal modulus bound. -/
theorem primeError_le (T : ℝ) (d : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ Real.log T)
    (hd : 0 < d) (hdT : (d : ℝ) ≤ T) :
    primeError T d ≤ ((2 + 2 * Real.exp 24) * T * Real.log T ^ 2) / d := by
  unfold primeError
  apply csSup_le (Set.insert_nonempty 0 _)
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · positivity
  · obtain ⟨a, x, ha, hcop, hx, hxT, rfl⟩ := hv
    apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
    simpa only [mul_comm] using prime_discrepancy_pointwise T x d a hT hL hd hdT hx hxT


/-- Page 17, boundedness needed for the real supremum in the maximal error. -/
theorem primeError_bddAbove (T : ℝ) (d : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ Real.log T)
    (hd : 0 < d) (hdT : (d : ℝ) ≤ T) :
    BddAbove (insert 0 {v : ℝ | ∃ a : ℕ, ∃ x : ℝ,
      a < d ∧ Nat.Coprime a d ∧ 2 ≤ x ∧ x ≤ T ∧
        v = |primeAP x d a - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d|}) := by
  refine ⟨((2 + 2 * Real.exp 24) * T * Real.log T ^ 2) / d, ?_⟩
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · positivity
  · obtain ⟨a, x, ha, hcop, hx, hxT, rfl⟩ := hv
    apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
    simpa only [mul_comm] using prime_discrepancy_pointwise T x d a hT hL hd hdT hx hxT


/-- Page 17, the maximal error is nonnegative. -/
theorem primeError_nonneg (T : ℝ) (d : ℕ) (hT : 2 ≤ T) (hL : 1 ≤ Real.log T)
    (hd : 0 < d) (hdT : (d : ℝ) ≤ T) : 0 ≤ primeError T d := by
  exact le_csSup (primeError_bddAbove T d hT hL hd hdT) (Set.mem_insert 0 _)


/-- Page 17, each reduced residue endpoint error is below the maximal error. -/
theorem primeError_majorizes (T x : ℝ) (d a : ℕ)
    (hT : 2 ≤ T) (hL : 1 ≤ Real.log T) (hd : 0 < d) (hdT : (d : ℝ) ≤ T)
    (ha : a < d) (hcop : Nat.Coprime a d) (hx : 2 ≤ x) (hxT : x ≤ T) :
    |primeAP x d a - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d| ≤
      primeError T d := by
  apply le_csSup (primeError_bddAbove T d hT hL hd hdT)
  exact Set.mem_insert_of_mem 0 ⟨a, x, ha, hcop, hx, hxT, rfl⟩


/-- Page 17, a reciprocal moment bound valid also at the empty and unit levels. -/
theorem squarefree_moment_scale (D : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlog : Real.log (max 2 D : ℕ) ≤ L) :
    (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, (d.divisors.card : ℝ) ^ 2 / d) ≤
      Real.exp 48 * L ^ 4 := by
  have hsub : (Finset.Icc 1 D).filter Squarefree ⊆
      (Finset.Icc 1 (max 2 D)).filter Squarefree := by
    intro d hd
    obtain ⟨hdI, hds⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hdI).1, (Finset.mem_Icc.mp hdI).2.trans (le_max_right _ _)⟩, hds⟩
  calc
    _ ≤ ∑ d ∈ (Finset.Icc 1 (max 2 D)).filter Squarefree, (d.divisors.card : ℝ) ^ 2 / d :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ Real.exp 48 * Real.log (max 2 D : ℕ) ^ 4 := squarefree_moment_log _ (le_max_left _ _)
    _ ≤ Real.exp 48 * L ^ 4 := by
      have hlog0 : 0 ≤ Real.log (max 2 D : ℕ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ max 2 D by omega))
      gcongr


/-- Page 17, divisor weighted maximal errors from an unweighted distribution bound.
CONDITIONAL ON the explicit unweighted prime error sum. -/
theorem weighted_prime_errors_of_sum (D : ℕ) (T A C : ℝ)
    (hT : 2 ≤ T) (hL : 1 ≤ Real.log T) (hDT : (D : ℝ) ≤ T) (hC : 0 ≤ C)
    (hsum : (∑ d ∈ Finset.Icc 1 D, primeError T d) ≤
      C * T * Real.log T ^ (-2 * A - 6)) :
    (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
      (d.divisors.card : ℝ) * primeError T d) ≤
      Real.sqrt (Real.exp 48 * (2 + 2 * Real.exp 24) * C) * T * Real.log T ^ (-A) := by
  let L := Real.log T
  let K := 2 + 2 * Real.exp 24
  let S := (Finset.Icc 1 D).filter Squarefree
  have hE (d : ℕ) (hd : d ∈ Finset.Icc 1 D) : 0 ≤ primeError T d := by
    have hdI := Finset.mem_Icc.mp hd
    exact primeError_nonneg T d hT hL hdI.1 ((by exact_mod_cast hdI.2 : (d : ℝ) ≤ D).trans hDT)
  have hpoint (d : ℕ) (hd : d ∈ S) : (d : ℝ) * primeError T d ≤ K * T * L ^ 2 := by
    have hdI := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    have hh := primeError_le T d hT hL hdI.1
      ((by exact_mod_cast hdI.2 : (d : ℝ) ≤ D).trans hDT)
    have hp : (0 : ℝ) < d := by exact_mod_cast hdI.1
    simpa only [mul_comm] using (le_div_iff₀ hp).mp hh
  have hsumS : (∑ d ∈ S, primeError T d) ≤ C * T * L ^ (-2 * A - 6) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun d hd _ => hE d hd)).trans hsum
  have hlog : Real.log (max 2 D : ℕ) ≤ L := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < max 2 D by omega))
    have hh : ((max 2 D : ℕ) : ℝ) = max 2 (D : ℝ) := by norm_cast
    rw [hh]
    exact max_le hT hDT
  have hc := Task506c.cauchy_progression_errors S
    (fun d : ℕ => (d.divisors.card : ℝ)) (primeError T) (fun d : ℕ => (d : ℝ))
    (K * T * L ^ 2) (Real.exp 48 * L ^ 4) (C * T * L ^ (-2 * A - 6))
    (fun d hd => by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1)
    (fun d hd => hE d (Finset.mem_filter.mp hd).1) (by dsimp [K]; positivity)
    (by positivity) hpoint (squarefree_moment_scale D L hL hlog) hsumS
  have hpow : L ^ 4 * L ^ 2 * L ^ (-2 * A - 6) = L ^ (-2 * A) := by
    rw [← Real.rpow_natCast L 4, ← Real.rpow_natCast L 2,
      ← Real.rpow_add (by dsimp [L]; linarith : 0 < L),
      ← Real.rpow_add (by dsimp [L]; linarith : 0 < L)]
    congr 1
    norm_num
  have hid : (Real.exp 48 * L ^ 4) * (K * T * L ^ 2) *
      (C * T * L ^ (-2 * A - 6)) = (Real.exp 48 * K * C) * T ^ 2 * L ^ (-2 * A) := by
    calc
      _ = (Real.exp 48 * K * C) * T ^ 2 * (L ^ 4 * L ^ 2 * L ^ (-2 * A - 6)) := by ring
      _ = _ := by rw [hpow]
  rw [hid] at hc
  exact cauchy_log_absorption _ _ T L A (by positivity)
    (by linarith) (by dsimp [L]; linarith) hc


end LeanLab.KumchevLiu2007.Task542a
