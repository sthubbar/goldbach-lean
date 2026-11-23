module

public import LeanLab.Linnik1951.Decomp520a

/-!
P0093 page 159 display 5.3 and page 160 display 5.5. Fresh split of the mixed
estimate mixed_bound520 of Decomp520a, written in the residue form used there.

QUESTION. The page image of page 160 prints 5.5 as N ln^6 N over the square root
of q tau, which is the display of mixed_bound520; the text file papers/P0093.txt
drops the q. The printed derivation gives only N ln^6 N times q over phi of q
over the square root of q tau in character form, and times the square root of
q over phi of q in residue form. That factor is unbounded over the moduli below
N to the one tenth. The exact display is therefore not reached by the printed
argument. This file proves the REPAIRED display with ln^7 N in place of ln^6 N,
which absorbs the factor and still feeds local_expansion520, whose error carries
ln^13 N. The final theorem is CONDITIONAL ON residue_square_mean520 and on the
leaves below. The older leaves mixed_shifted_bound520 and mixed_diagonal_bound520
are not used.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- LEAF: P0093 page 160 display 5.5, first inequality, in residue form. The
norm of the mixed integral is at most twice the norm of the principal coefficient
times the reduced residue sum of the arc integrals of the product of norms. -/
theorem mixed_norm_le_prep1121 (N q : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    ‖mixedIntegral520 N q n‖ ≤ 2 * ‖principalCoefficient520 q‖ *
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖principalPrime520 N q z‖ * ‖residueError520 N q a z‖ := by
  set r : ℝ := 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hle : -r ≤ r := by linarith
  unfold mixedIntegral520
  rw [← hr]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  refine (intervalIntegral.norm_integral_le_integral_norm hle).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  have hP := continuous_principal520 N q hN
  have hE := continuous_residue520 N q a hN
  apply intervalIntegral.integral_mono_on hle
  · exact ((by fun_prop : Continuous (fun z : ℝ =>
      (2 * principalCoefficient520 q * principalPrime520 N q z * residueError520 N q a z) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))).norm
      |>.intervalIntegrable _ _)
  · exact (continuous_const.mul (hP.norm.mul hE.norm)).intervalIntegrable _ _
  · intro z _
    have hunit : ‖Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) *
        Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, hunit, mul_one, norm_mul, norm_mul, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    ring_nf
    exact le_refl _

/-- LEAF: P0093 page 156 display 3.3 with the coefficient of display 3.4. The
principal coefficient mu of q over phi of q has norm at most one over phi of q. -/
theorem coefficient_le_inv_totient_prep1121 (q : ℕ) (hq : 1 ≤ q) :
    ‖principalCoefficient520 q‖ ≤ 1 / (q.totient : ℝ) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hμ : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hc : principalCoefficient520 q =
      (((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) : ℝ) : ℂ) := rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hφ]
  exact div_le_div_of_nonneg_right hμ hφ.le

/-- LEAF: P0093 page 159 display 5.3, the Cauchy Schwarz step, here over the
reduced residues and the arc together. For continuous real functions on a
symmetric interval, the residue sum of the integrals of f times g a is at most
the square root of the number of residues times the integral of f squared, times
the square root of the residue sum of the integrals of g a squared. -/
theorem arc_cauchy_schwarz_prep1121 (s : Finset ℕ) (r : ℝ) (hr : 0 ≤ r)
    (f : ℝ → ℝ) (g : ℕ → ℝ → ℝ) (hf : Continuous f) (hg : ∀ a, Continuous (g a)) :
    ∑ a ∈ s, ∫ z in -r..r, f z * g a z ≤
      Real.sqrt ((s.card : ℝ) * ∫ z in -r..r, f z ^ 2) *
        Real.sqrt (∑ a ∈ s, ∫ z in -r..r, g a z ^ 2) := by
  have hrr : -r ≤ r := by linarith
  set A : ℝ := ∫ z in -r..r, f z ^ 2 with hA
  set L : ℝ := ∑ a ∈ s, ∫ z in -r..r, f z * g a z with hLd
  set B : ℝ := ∑ a ∈ s, ∫ z in -r..r, g a z ^ 2 with hB
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg hrr (fun z _ => sq_nonneg _)
  have hone : ∀ (t : ℝ) (a : ℕ), ∫ z in -r..r, (t * f z - g a z) ^ 2 =
      t ^ 2 * A - 2 * t * (∫ z in -r..r, f z * g a z) + ∫ z in -r..r, g a z ^ 2 := by
    intro t a
    have e : (fun z => (t * f z - g a z) ^ 2) =
        fun z => (t ^ 2 * f z ^ 2 - 2 * t * (f z * g a z)) + g a z ^ 2 := by
      funext z; ring
    have i1 : IntervalIntegrable (fun z => t ^ 2 * f z ^ 2) volume (-r) r :=
      (continuous_const.mul (hf.pow 2)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun z => 2 * t * (f z * g a z)) volume (-r) r :=
      (continuous_const.mul (hf.mul (hg a))).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun z => g a z ^ 2) volume (-r) r :=
      ((hg a).pow 2).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hquad : ∀ t : ℝ, 0 ≤ ((s.card : ℝ) * A) * (t * t) + (-2 * L) * t + B := by
    intro t
    have hnn : 0 ≤ ∑ a ∈ s, ∫ z in -r..r, (t * f z - g a z) ^ 2 :=
      Finset.sum_nonneg (fun a _ => intervalIntegral.integral_nonneg hrr (fun z _ => sq_nonneg _))
    have hexp : ∑ a ∈ s, ∫ z in -r..r, (t * f z - g a z) ^ 2 =
        ((s.card : ℝ) * A) * (t * t) + (-2 * L) * t + B := by
      rw [Finset.sum_congr rfl (fun a _ => hone t a), Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul, hLd, hB]
      ring
    linarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  have hsq : L ^ 2 ≤ ((s.card : ℝ) * A) * B := by nlinarith
  rw [← Real.sqrt_mul (by positivity)]
  exact (le_abs_self L).trans (Real.abs_le_sqrt hsq)

/-- LEAF: P0093 page 159 before display 5.3, the inclusion step of the trivial
estimate. When the arc radius is at most one half, the arc integral of the
squared norm of the principal series is at most its integral over one full
period, since the series has period one. -/
theorem principal_arc_le_period_prep1121 (N q : ℕ) (hN : 1 ≤ N) (r : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    ∫ z in -r..r, ‖principalPrime520 N q z‖ ^ 2 ≤
      ∫ z in (0 : ℝ)..1, ‖principalPrime520 N q z‖ ^ 2 := by
  have hS : Function.Periodic (primeFourier111_up111 N) 1 := by
    intro α
    unfold primeFourier111_up111
    apply tsum_congr
    intro p
    congr 1
    have he : ((-(2 * Real.pi * (α + 1) * (p : ℕ)) : ℝ) : ℂ) * Complex.I =
        ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) : ℂ) * Complex.I +
          ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) := by push_cast; ring
    rw [he, Complex.exp_add]
    have hp : Complex.exp ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I (-(p : ℕ) : ℤ) using 1 <;> push_cast <;> ring
    rw [hp, mul_one]
  have hP : Function.Periodic (principalPrime520 N q) 1 := by
    intro α
    unfold principalPrime520
    rw [hS α]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    have he : ((-(2 * Real.pi * (α + 1) * p) : ℝ) : ℂ) * Complex.I =
        ((-(2 * Real.pi * α * p) : ℝ) : ℂ) * Complex.I +
          ((-(p : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) := by push_cast; ring
    rw [he, Complex.exp_add]
    have hp : Complex.exp ((-(p : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I (-(p : ℤ)) using 1 <;> push_cast <;> ring
    rw [hp, mul_one]
  have hF : Function.Periodic (fun z => ‖principalPrime520 N q z‖ ^ 2) 1 := by
    intro z
    simp only [hP z]
  have hc : Continuous (fun z => ‖principalPrime520 N q z‖ ^ 2) :=
    (continuous_principal520 N q hN).norm.pow 2
  have h1 : ∫ z in -r..r, ‖principalPrime520 N q z‖ ^ 2 ≤
      ∫ z in (-(1 / 2) : ℝ)..(1 / 2), ‖principalPrime520 N q z‖ ^ 2 :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) hr
      (Filter.Eventually.of_forall (fun z => by positivity)) (hc.intervalIntegrable _ _)
  have h2 := hF.intervalIntegral_add_eq (-(1 / 2)) 0
  have e1 : (-(1 / 2) : ℝ) + 1 = 1 / 2 := by norm_num
  have e2 : (0 : ℝ) + 1 = 1 := by norm_num
  rw [e1, e2] at h2
  rw [← h2]
  exact h1

/-- P0093 page 159 before display 5.3, the Parseval identity for the principal
series over one period, from tsum_sq_fourierCoeffOn as in fourier_parseval111_up111. -/
theorem principal_parseval_identity_prep1121 (N q : ℕ) (hN : 1 ≤ N) :
    ∫ z in (0 : ℝ)..1, ‖principalPrime520 N q z‖ ^ 2 =
      ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (principalPrime520 N q) i‖ ^ 2 := by
  have hf := continuous_principal520 N q hN
  have hs : IntervalIntegrable (fun α => ‖principalPrime520 N q α‖ ^ 2)
      MeasureTheory.volume 0 1 := (hf.norm.pow 2).intervalIntegrable 0 1
  have hL2 : MeasureTheory.MemLp (principalPrime520 N q) 2
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hs.1
  simpa using (tsum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hL2).symm


/-- LEAF: P0093 page 159 before display 5.3, the Chebyshev input of the trivial
estimate. The number of primes up to x is at most a constant times x over ln x;
Mathlib gives theta of x at most ln 4 times x as theta_le_log4_mul_x, and the
primes above the square root of x each contribute at least half of ln x. -/
theorem prime_count_chebyshev_prep1121 :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
      (((Finset.range (x + 1)).filter Nat.Prime).card : ℝ) ≤ C * (x : ℝ) / Real.log x := by
  refine ⟨2 * Real.log 4 + 2, by positivity, ?_⟩
  intro x hx
  have hX : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hX0 : (0 : ℝ) < (x : ℝ) := by linarith
  have h := Chebyshev.pi_le_log4_mul_div hX
  rw [Nat.floor_natCast] at h
  have hcard : (((Finset.range (x + 1)).filter Nat.Prime).card : ℝ) = (Nat.primeCounting x : ℝ) := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    rfl
  rw [hcard]
  have hlog : 0 < Real.log x := Real.log_pos hX
  have hsq : Real.log (Real.sqrt x) = Real.log x / 2 := by
    rw [Real.log_sqrt hX0.le]
  rw [hsq] at h
  have hs0 : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hX0
  have hss : Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) = x := Real.mul_self_sqrt hX0.le
  have hls : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs0
  rw [hsq] at hls
  have hroot : Real.sqrt (x : ℝ) ≤ 2 * (x : ℝ) / Real.log x := by
    rw [le_div_iff₀ hlog]
    nlinarith
  have hmain : Real.log 4 * (x : ℝ) / (Real.log x / 2) = 2 * Real.log 4 * x / Real.log x := by
    field_simp
  rw [hmain] at h
  have hfin : (2 * Real.log 4 + 2) * (x : ℝ) / Real.log x =
      2 * Real.log 4 * x / Real.log x + 2 * (x : ℝ) / Real.log x := by
    field_simp
  rw [hfin]
  linarith


/-- LEAF: P0093 page 160 display 5.5, the factor q over phi of q that the
printed step drops, first half. q over phi of q is the product of p over p minus
one over the prime factors p of q, see Nat.totient_mul_prod_primeFactors. The i th
smallest prime factor is at least i plus one, so the product telescopes to at most
the number of prime factors plus one. -/
theorem q_div_totient_le_omega_prep1121 (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) / (q.totient : ℝ) ≤ (q.primeFactors.card : ℝ) + 1 := by
  -- the product bound over any finite set of integers at least two
  have key : ∀ S : Finset ℕ, (∀ p ∈ S, 2 ≤ p) →
      ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) ≤ (S.card : ℝ) + 1 := by
    intro S
    induction S using Finset.induction_on_max with
    | empty => intro _; simp
    | insert m S' hlt ih =>
      intro h2
      have hm : m ∉ S' := fun hm => lt_irrefl m (hlt m hm)
      have h2' : ∀ p ∈ S', 2 ≤ p := fun p hp => h2 p (Finset.mem_insert_of_mem hp)
      have hm2 : 2 ≤ m := h2 m (Finset.mem_insert_self m S')
      have hsub : S' ⊆ Finset.Ico 2 m := by
        intro p hp
        rw [Finset.mem_Ico]
        exact ⟨h2' p hp, hlt p hp⟩
      have hcard : S'.card + 2 ≤ m := by
        have := Finset.card_le_card hsub
        rw [Nat.card_Ico] at this
        omega
      have hcardR : (S'.card : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hcard
      rw [Finset.prod_insert hm, Finset.card_insert_of_notMem hm]
      have ih' := ih h2'
      have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      have hk0 : (0 : ℝ) ≤ S'.card := by positivity
      have hP0 : 0 ≤ ∏ p ∈ S', ((p : ℝ) / ((p : ℝ) - 1)) := by
        apply Finset.prod_nonneg
        intro p hp
        have : (2 : ℝ) ≤ p := by exact_mod_cast h2' p hp
        apply div_nonneg <;> linarith
      have hfac : (m : ℝ) / ((m : ℝ) - 1) ≤ ((S'.card : ℝ) + 2) / ((S'.card : ℝ) + 1) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
      have hf0 : 0 ≤ (m : ℝ) / ((m : ℝ) - 1) := by apply div_nonneg <;> linarith
      calc (m : ℝ) / ((m : ℝ) - 1) * ∏ p ∈ S', ((p : ℝ) / ((p : ℝ) - 1))
          ≤ ((S'.card : ℝ) + 2) / ((S'.card : ℝ) + 1) * ((S'.card : ℝ) + 1) :=
            mul_le_mul hfac ih' hP0 (by positivity)
        _ = ((S'.card + 1 : ℕ) : ℝ) + 1 := by
            field_simp
            push_cast
            ring
  have hq0 : q ≠ 0 := by omega
  have hid := Nat.totient_mul_prod_primeFactors q
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hprod : (q : ℝ) / (q.totient : ℝ) =
      ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    have hidR : (q.totient : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ) =
        (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) hid
      simp only [Nat.cast_mul, Nat.cast_prod] at this
      rw [this]
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      have : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
      push_cast [this]
      ring
    have hne : ∀ p ∈ q.primeFactors, ((p : ℝ) - 1) ≠ 0 := by
      intro p hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      linarith
    have hpd : ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
    rw [Finset.prod_div_distrib, eq_div_iff hpd, div_mul_eq_mul_div, div_eq_iff hφ.ne']
    linarith [hidR]
  rw [hprod]
  exact key _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)

/-- LEAF: P0093 page 160 display 5.5, the factor q over phi of q, second half.
Two to the number of prime factors of q divides into q, so that number is at
most ln q over ln 2. -/
theorem card_primeFactors_le_log_prep1121 (q : ℕ) (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
  have hdvd : ∏ p ∈ q.primeFactors, p ∣ q := Nat.prod_primeFactors_dvd q
  have hle : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) hdvd
  have h2prod : ∏ p ∈ q.primeFactors, (2 : ℕ) ≤ ∏ p ∈ q.primeFactors, p := by
    refine Finset.prod_le_prod ?_
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hpow : (2 : ℕ) ^ q.primeFactors.card ≤ q := by
    rw [Finset.prod_const] at h2prod
    exact le_trans h2prod hle
  have hcast : ((2 : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) := by
    exact_mod_cast hpow
  have hlog : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (q : ℝ) := by
    have h1 : Real.log ((2 : ℝ) ^ q.primeFactors.card) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by positivity) hcast
    rwa [Real.log_pow] at h1
  have hpos2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos2]
  linarith

/-- P0093 page 160 display 5.5, the factor q over phi of q. For moduli at most
N to the one tenth and N at least two hundred, q over phi of q is at most ln N.
Assembled from the two leaves above. -/
theorem q_div_totient_le_log_prep1121 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
      (q : ℝ) / (q.totient : ℝ) ≤ Real.log N := by
  refine ⟨200, ?_⟩
  intro N hN q hq hqQ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have h1 := q_div_totient_le_omega_prep1121 q hq
  have h2 := card_primeFactors_le_log_prep1121 q hq
  have hlq : Real.log q ≤ (1 / 10) * Real.log N := by
    have := Real.log_le_log hqpos hqQ
    rwa [Real.log_rpow hNpos] at this
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlN : (5 : ℝ) ≤ Real.log N := by
    have hexp : Real.exp 5 ≤ (N : ℝ) := by
      have he := Real.exp_one_lt_d9
      have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hb : Real.exp 1 ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le he.le 5
      have : (200 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      nlinarith
    have := Real.log_le_log (Real.exp_pos 5) hexp
    simpa using this
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have h3 : Real.log q / Real.log 2 ≤ (1 / 10) * Real.log N / 0.6931471803 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have h4 : (1 / 10) * Real.log N / 0.6931471803 + 1 ≤ Real.log N := by
    rw [div_add_one (by norm_num), div_le_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- LEAF: P0093 page 160 display 5.5, the closing inequality chain. Real
numbers only: from the norm step, the coefficient bound, Cauchy Schwarz, the
principal mass bound, the residue mean bound and the totient ratio bound, the
mixed norm is at most twice the square root of the product of the two constants
times N times L to the seventh over the square root of q tau. -/
theorem mixed_chain_prep1121 (m c S M R φ q τ Nr L C1 C2 : ℝ)
    (hφ : 0 < φ) (hq : 0 < q) (hτ : 0 < τ) (hNr : 0 ≤ Nr) (hL : 1 ≤ L)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hc0 : 0 ≤ c) (hM0 : 0 ≤ M) (hR0 : 0 ≤ R)
    (hm : m ≤ 2 * c * S) (hc : c ≤ 1 / φ)
    (hS : S ≤ Real.sqrt (φ * M) * Real.sqrt R)
    (hM : M ≤ C1 * Nr / L) (hR : R ≤ C2 * Nr / τ * L ^ 13)
    (hqφ : q / φ ≤ L) :
    m ≤ 2 * Real.sqrt (C1 * C2) * Nr * L ^ 7 / Real.sqrt (q * τ) := by
  have hL0 : 0 ≤ L := by linarith
  have hqτ : 0 < q * τ := mul_pos hq hτ
  set T : ℝ := Real.sqrt (C1 * C2) * Nr * L ^ 7 / Real.sqrt (q * τ) with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have key : c * S ≤ T := by
    by_cases hS0 : S ≤ 0
    · have : c * S ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0 hS0
      linarith
    rw [not_le] at hS0
    have h1 : c * S ≤ (1 / φ) * (Real.sqrt (φ * M) * Real.sqrt R) :=
      mul_le_mul hc hS hS0.le (by positivity)
    refine h1.trans ?_
    have hA0 : 0 ≤ (1 / φ) * (Real.sqrt (φ * M) * Real.sqrt R) := by positivity
    rw [← pow_le_pow_iff_left₀ hA0 hT0 (two_ne_zero)]
    have hlhs : ((1 / φ) * (Real.sqrt (φ * M) * Real.sqrt R)) ^ 2 = M * R / φ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hR0]
      field_simp
    have hrhs : T ^ 2 = C1 * C2 * Nr ^ 2 * L ^ 14 / (q * τ) := by
      rw [hT, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
        Real.sq_sqrt hqτ.le]
      ring
    rw [hlhs, hrhs]
    have hMR : M * R ≤ (C1 * Nr / L) * (C2 * Nr / τ * L ^ 13) :=
      mul_le_mul hM hR hR0 (by positivity)
    have hinv : 1 / φ ≤ L / q := by
      rw [div_le_div_iff₀ hφ hq]
      rw [div_le_iff₀ hφ] at hqφ
      linarith
    have hL13 : L ^ 13 ≤ L ^ 14 := pow_le_pow_right₀ hL (by norm_num)
    have hLpos : 0 < L := by linarith
    calc M * R / φ = (M * R) * (1 / φ) := by ring
      _ ≤ ((C1 * Nr / L) * (C2 * Nr / τ * L ^ 13)) * (L / q) :=
          mul_le_mul hMR hinv (by positivity) (by positivity)
      _ = C1 * C2 * Nr ^ 2 * L ^ 13 / (q * τ) := by
          field_simp
      _ ≤ C1 * C2 * Nr ^ 2 * L ^ 14 / (q * τ) := by
          apply div_le_div_of_nonneg_right _ hqτ.le
          exact mul_le_mul_of_nonneg_left hL13 (by positivity)
  have : 2 * c * S = 2 * (c * S) := by ring
  rw [this] at hm
  have hfin : 2 * Real.sqrt (C1 * C2) * Nr * L ^ 7 / Real.sqrt (q * τ) = 2 * T := by
    rw [hT]; ring
  rw [hfin]
  linarith

end LeanLab.Linnik1951
