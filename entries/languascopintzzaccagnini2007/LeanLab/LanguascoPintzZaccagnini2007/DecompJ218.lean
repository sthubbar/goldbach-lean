module

public import LeanLab.LanguascoPintzZaccagnini2007.Truncation131
public import LeanLab.LanguascoPintzZaccagnini2007.Lemma62
public import LeanLab.LanguascoPintzZaccagnini2007.Residues131
public import LeanLab.LanguascoPintzZaccagnini2007.PeriodCount131

/-!
P0045 U-1608. Re-cut of the major arc decomposition of display 25, page 8.
The old leaves are kept as text and refuted in Audit1608.lean.
Open leaves here: `cor42_published131` and `cor42_window_extension131`, Corollary 4.2 for the BINARY integral,
and `major_arcs_combine131`, displays 15 to 24, the singular series average.
`major_arcs_j2_131`, displays 12 to 14, is proved here from Lemma 6.2.
`major_asymptotic131_assembly` is proved from these and has no open proof of its own.
Decomp131.lean now imports this file, so `major_asymptotic131` is this assembly.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- Display 4 on page 3: the BINARY major arc integral R_M(n), which is the
integral of S^2 e(-n alpha), that is `majorContribution131` at k = 0. -/
def binaryMajor131 (X n : ℕ) (P : ℝ) : ℝ := majorContribution131 0 X n P

/-- The even integers of [X/2, X], the range of m in Lemma 6.2, page 9.
Display 12 evaluates R_M at n = N - 2^ν1 - ... - 2^νk, which can fall just below 2X/3
when N is near 2X/3, so the J(X) of Corollary 4.2 does not cover it. -/
def evenWindow131 (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun n : ℕ => Even n ∧ (X : ℝ) / 2 ≤ n)

/-- Page 6: q' is the product of the odd primes dividing q, without multiplicity. -/
def oddRad131 (r : ℕ) : ℕ := ∏ p ∈ r.primeFactors.filter (fun p => 2 < p), p

/-- Display 5: the exponent tuples in [1, L']^k, L' = L - sqrt L. -/
abbrev tuples131 (k X : ℕ) : Finset (Fin k → ℕ) :=
  exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊

/-- Display 5: M = 2^ν1 + ... + 2^νk. -/
def tuplePower131 {k : ℕ} (ν : Fin k → ℕ) : ℕ := ∑ i, 2 ^ ν i

/-- Corollary 4.2 and display 10, page 6: at most K₁ moduli, each with r' at least c L^2. -/
def ExceptionalModuli131 (K₁ : ℕ) (c : ℝ) (X : ℕ) (E : Finset ℕ) : Prop :=
  E.card ≤ K₁ ∧ ∀ r ∈ E, c * Lg X ^ 2 ≤ oddRad131 r

/-- Display 9, page 6: n lies in J_1, that is r does not divide C* n for all r in E. -/
def Nonexceptional131 (Cstar : ℕ) (E : Finset ℕ) (n : ℕ) : Prop :=
  ∀ r ∈ E, ¬ r ∣ Cstar * n

/-- Pointwise factors of the singular series are nonnegative. -/
theorem singF_nonneg131 (n : ℕ) (p : {p : ℕ // p.Prime}) : 0 ≤ singF n p := by
  unfold singF
  have h2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
  split_ifs with h
  · exact div_nonneg (by linarith) (by linarith)
  · have h1 : (1 : ℝ) ≤ (p.1 : ℝ) - 1 := by linarith
    have h3 : 1 ≤ ((p.1 : ℝ) - 1) ^ 2 := one_le_pow₀ h1
    have h4 : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact h3
    linarith

/-- The singular series is nonnegative. -/
theorem Sing_nonneg131 (n : ℕ) : 0 ≤ Sing n := by
  have hS : Sing n = ∏' p, singF n p := rfl
  rw [hS]
  by_cases hm : Multipliable (singF n)
  · exact ge_of_tendsto hm.hasProd
      (Eventually.of_forall fun S => prod_nonneg fun p _ => singF_nonneg131 n p)
  · rw [tprod_eq_one_of_not_multipliable hm]
    norm_num

/-- The major arcs lie in a bounded interval. -/
theorem majorArcs_bounded131 (X : ℕ) (P : ℝ) :
    majorArcs131 X P ⊆ Set.Icc (-(1 / arcQ131 X P)) (1 + 1 / arcQ131 X P) := by
  rintro α ⟨q, a, hq, hqP, ha, -, h1, h2⟩
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hP : 0 < P := by linarith
  have hQ : 0 ≤ arcQ131 X P := by unfold arcQ131; positivity
  have hQi : 0 ≤ 1 / arcQ131 X P := by positivity
  have hb : 1 / ((q : ℝ) * arcQ131 X P) ≤ 1 / arcQ131 X P := by
    have he : 1 / ((q : ℝ) * arcQ131 X P) = (1 / (q : ℝ)) * (1 / arcQ131 X P) := by
      rw [div_mul_div_comm, one_mul]
    rw [he]
    exact mul_le_of_le_one_left hQi (by rw [div_le_one (by linarith)]; exact hq0)
  have ham := mem_Icc.mp ha
  have ha1 : (a : ℝ) / q ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact_mod_cast ham.2
  have ha0 : 0 ≤ (a : ℝ) / q := by positivity
  exact ⟨by linarith, by linarith⟩

/-- A tuple power is at most j 2^M. -/
theorem tuplePower_le131 {j M : ℕ} {ν : Fin j → ℕ} (hν : ν ∈ exponentTuples131 j M) :
    tuplePower131 ν ≤ j * 2 ^ M := by
  unfold tuplePower131
  have h : ∀ i ∈ (univ : Finset (Fin j)), 2 ^ ν i ≤ 2 ^ M := fun i _ =>
    Nat.pow_le_pow_right (by norm_num) (mem_Icc.mp (Fintype.mem_piFinset.mp hν i)).2
  calc ∑ i, 2 ^ ν i ≤ ∑ _i : Fin j, 2 ^ M := sum_le_sum h
    _ = j * 2 ^ M := by simp

/-- A tuple power is even, since every exponent is at least 1. -/
theorem tuplePower_even131 {j M : ℕ} {ν : Fin j → ℕ} (hν : ν ∈ exponentTuples131 j M) :
    Even (tuplePower131 ν) := by
  unfold tuplePower131
  rw [even_iff_two_dvd]
  refine dvd_sum fun i _ => ?_
  exact dvd_pow_self 2 (by
    have := (mem_Icc.mp (Fintype.mem_piFinset.mp hν i)).1
    omega)

/-- Page 3: 2^(L') is o(X), so the shifts in display 5 are at most X/6 for large X. -/
theorem tuple_window131 (k : ℕ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      1 ≤ Lg X ∧ 6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ ≤ X := by
  have ht : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Tendsto (fun X : ℕ => Real.exp (Real.log 2 * Real.sqrt (Lg X))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((Real.tendsto_sqrt_atTop.comp ht).const_mul_atTop hlog)
  obtain ⟨X₀, hX₀⟩ := ((ht.eventually_ge_atTop 1).and
    (hs.eventually_ge_atTop (6 * (k : ℝ)))).exists_forall_of_atTop
  refine ⟨max 1 X₀, fun X hX => ?_⟩
  obtain ⟨hL, hE⟩ := hX₀ X (le_trans (le_max_right _ _) hX)
  refine ⟨hL, ?_⟩
  have hX1 : (0 : ℝ) < X := by
    have : 1 ≤ X := le_trans (le_max_left _ _) hX
    exact_mod_cast this
  have hsq : Real.sqrt (Lg X) ≤ Lg X :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have ht0 : 0 ≤ Lg X - Real.sqrt (Lg X) := by linarith
  have hfl := Nat.floor_le ht0
  set M := ⌊Lg X - Real.sqrt (Lg X)⌋₊
  have h2M : (2 : ℝ) ^ M ≤ (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hfl
  have hXe : (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) * (2 : ℝ) ^ (Real.sqrt (Lg X)) = X := by
    rw [← Real.rpow_add (by norm_num), sub_add_cancel]
    exact Real.rpow_logb (by norm_num) (by norm_num) hX1
  have hE' : 6 * (k : ℝ) ≤ (2 : ℝ) ^ (Real.sqrt (Lg X)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    exact hE
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ M := by positivity
  have hq : (0 : ℝ) ≤ (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) := by positivity
  have hmain : 6 * (k : ℝ) * (2 : ℝ) ^ M ≤ X := by
    calc 6 * (k : ℝ) * (2 : ℝ) ^ M
        ≤ (2 : ℝ) ^ (Real.sqrt (Lg X)) * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) :=
          mul_le_mul hE' h2M hp (by positivity)
      _ = X := by rw [mul_comm]; exact hXe
  exact_mod_cast hmain

/-- Natural number form of membership in J(X). -/
theorem evenJ_nat131 {X N : ℕ} (hN : N ∈ evenJ131 X) :
    1 ≤ N ∧ N ≤ X ∧ Even N ∧ 2 * X ≤ 3 * N := by
  obtain ⟨h1, h2, h3⟩ := mem_filter.mp hN
  obtain ⟨h4, h5⟩ := mem_Icc.mp h1
  refine ⟨h4, h5, h2, ?_⟩
  have : 2 * (X : ℝ) ≤ 3 * N := by linarith
  exact_mod_cast this

/-- Shifted arguments stay in the window of Lemma 6.2. -/
theorem window_mem131 {X N M : ℕ} (hN : N ∈ evenJ131 X) (hM : 6 * M ≤ X) (hev : Even M) :
    N - M ∈ evenWindow131 X := by
  obtain ⟨h1, h2, h3, h4⟩ := evenJ_nat131 hN
  have hle : M ≤ N := by omega
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, (Nat.even_sub hle).mpr ?_, ?_⟩
  · exact iff_of_true h3 hev
  · have : X ≤ 2 * (N - M) := by omega
    have h' : (X : ℝ) ≤ 2 * ((N - M : ℕ) : ℝ) := by exact_mod_cast this
    linarith

/-- Display 5 on page 4, proved: the k-fold integral is the sum of the binary integrals
at the shifted arguments N - M. -/
theorem major_expand131 (k X N : ℕ) (P : ℝ)
    (h : ∀ ν ∈ tuples131 k X, tuplePower131 ν ≤ N) :
    majorContribution131 k X N P =
      ∑ ν ∈ tuples131 k X, binaryMajor131 X (N - tuplePower131 ν) P := by
  have hpoint : ∀ α : ℝ,
      primeSum131 X α ^ 2 * powerSum131 X α ^ k * phase131 (-(N : ℝ) * α) =
      ∑ ν ∈ tuples131 k X, primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
        phase131 (-((N - tuplePower131 ν : ℕ) : ℝ) * α) := by
    intro α
    rw [powerSum_pow131, mul_sum, sum_mul]
    refine sum_congr rfl fun ν hν => ?_
    have hc : ((N - tuplePower131 ν : ℕ) : ℝ) = (N : ℝ) - tuplePower131 ν :=
      Nat.cast_sub (h ν hν)
    have he : phase131 (((∑ i, 2 ^ ν i : ℕ) : ℝ) * α) * phase131 (-(N : ℝ) * α) =
        phase131 (-((N : ℝ) - tuplePower131 ν) * α) := by
      rw [phase_add131]
      congr 1
      unfold tuplePower131
      ring
    rw [hc, pow_zero, mul_one, mul_assoc, he]
  have hint : ∀ ν ∈ tuples131 k X, IntegrableOn (fun α : ℝ =>
      primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
        phase131 (-((N - tuplePower131 ν : ℕ) : ℝ) * α)) (majorArcs131 X P) := by
    intro ν _
    have hc : Continuous (fun α : ℝ =>
        primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
          phase131 (-((N - tuplePower131 ν : ℕ) : ℝ) * α)) :=
      (((primeSum_continuous131 X).pow 2).mul ((powerSum_continuous131 X).pow 0)).mul
        (phase_continuous131.comp (continuous_const.mul continuous_id))
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set (majorArcs_bounded131 X P)
  have hi : (∫ α in majorArcs131 X P,
        primeSum131 X α ^ 2 * powerSum131 X α ^ k * phase131 (-(N : ℝ) * α)) =
      ∑ ν ∈ tuples131 k X, ∫ α in majorArcs131 X P,
        primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
          phase131 (-((N - tuplePower131 ν : ℕ) : ℝ) * α) := by
    calc _ = ∫ α in majorArcs131 X P, ∑ ν ∈ tuples131 k X,
          primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
            phase131 (-((N - tuplePower131 ν : ℕ) : ℝ) * α) :=
          integral_congr_ae (Eventually.of_forall hpoint)
      _ = _ := integral_finsetSum _ hint
  unfold binaryMajor131 majorContribution131
  rw [hi, Complex.re_sum]

/-- Elementary split of displays 11 and 12: good terms by a relative bound,
bad terms by a bound on the sum over bad indices. -/
theorem split_bound131 {ι : Type*} (T : Finset ι) (bad : ι → Prop) [DecidablePred bad]
    (a b s : ι → ℝ) (η D : ℝ)
    (hη : 0 ≤ η) (hD : 0 ≤ D) (hb : ∀ ν ∈ T, 0 ≤ b ν) (hs : ∀ ν ∈ T, 0 ≤ s ν)
    (hgood : ∀ ν ∈ T, ¬ bad ν → |a ν - b ν| ≤ η * b ν)
    (hbad : ∀ ν ∈ T, bad ν → |a ν - b ν| ≤ D * s ν) :
    |∑ ν ∈ T, a ν - ∑ ν ∈ T, b ν| ≤ η * ∑ ν ∈ T, b ν + D * ∑ ν ∈ T.filter bad, s ν := by
  rw [sum_filter, mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ν hν => ?_)
  by_cases h : bad ν
  · rw [if_pos h]
    have := hbad ν hν h
    have := mul_nonneg hη (hb ν hν)
    linarith
  · rw [if_neg h]
    simpa using hgood ν hν h

/-- Pages 6 and 7: the part of r' prime to C*. It divides n whenever r divides C* n. -/
def oddFree131 (Cstar r : ℕ) : ℕ :=
  ∏ p ∈ (r.primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ p ∣ Cstar), p

theorem oddFree_odd131 (Cstar r : ℕ) : Odd (oddFree131 Cstar r) := by
  refine Finset.prod_induction (fun p => p) Odd (fun _ _ ha hb => ha.mul hb) odd_one
    (fun p hp => ?_)
  obtain ⟨hp1, -⟩ := mem_filter.mp hp
  obtain ⟨hp2, hp3⟩ := mem_filter.mp hp1
  exact (Nat.prime_of_mem_primeFactors hp2).odd_of_ne_two (by omega)

theorem oddRad_le131 {Cstar : ℕ} (hC : 0 < Cstar) (r : ℕ) :
    oddRad131 r ≤ oddFree131 Cstar r * Cstar := by
  have h := Finset.prod_filter_mul_prod_filter_not (r.primeFactors.filter (fun p => 2 < p))
    (fun p => ¬ p ∣ Cstar) (fun p => p)
  have hU : ∏ p ∈ (r.primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ ¬ p ∣ Cstar), p ∣
      Cstar := by
    refine Finset.prod_primes_dvd Cstar (fun p hp => ?_) (fun p hp => ?_)
    · exact (Nat.prime_of_mem_primeFactors
        (mem_filter.mp (mem_filter.mp hp).1).1).prime
    · exact not_not.mp (mem_filter.mp hp).2
  have hU' := Nat.le_of_dvd hC hU
  unfold oddRad131 oddFree131
  rw [← h]
  exact Nat.mul_le_mul_left _ hU'

theorem oddFree_dvd131 {Cstar r n : ℕ} (h : r ∣ Cstar * n) : oddFree131 Cstar r ∣ n := by
  refine Finset.prod_primes_dvd n (fun p hp => ?_) (fun p hp => ?_)
  · exact (Nat.prime_of_mem_primeFactors (mem_filter.mp (mem_filter.mp hp).1).1).prime
  · obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
    have hp3 := (mem_filter.mp hp1).1
    have hpp := Nat.prime_of_mem_primeFactors hp3
    have hd := (Nat.dvd_of_mem_primeFactors hp3).trans h
    exact ((Nat.Prime.dvd_mul hpp).mp hd).resolve_left hp2

/-- The averaging step of pages 6 and 7: fix all exponents but one and apply a bound
for A(m, s) on the window. -/
theorem tuple_sum_dvd_le131 {j X N s : ℕ} {ε' : ℝ}
    (hA : ∀ m : ℕ, (X : ℝ) / 2 ≤ m → m ≤ X → Amr X m s ≤ ε' * Lg X)
    (hε' : 0 ≤ ε') (hL : 1 ≤ Lg X)
    (hw : 6 * (j + 1) * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ ≤ X) (hN : N ∈ evenJ131 X) :
    ∑ ν ∈ exponentTuples131 (j + 1) ⌊Lg X - Real.sqrt (Lg X)⌋₊,
        (if s ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) ≤
      ε' * Lg X ^ (j + 1) := by
  obtain ⟨hN1, hN2, -, hN4⟩ := evenJ_nat131 hN
  have hsq : Real.sqrt (Lg X) ≤ Lg X :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have ht0 : 0 ≤ Lg X - Real.sqrt (Lg X) := by linarith
  have hfl := Nat.floor_le ht0
  have hML : ((⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) ≤ Lg X := by
    linarith [Real.sqrt_nonneg (Lg X)]
  set M := ⌊Lg X - Real.sqrt (Lg X)⌋₊ with hMdef
  have hpi : exponentTuples131 (j + 1) M =
      ((Icc 1 M) ×ˢ exponentTuples131 j M).map
        (Fin.consEquiv (fun _ : Fin (j + 1) => ℕ)).toEmbedding := by
    have := Finset.filter_piFinset_eq_map_consEquiv (fun _ : Fin (j + 1) => Icc 1 M)
      (fun _ => True)
    simp only [Finset.filter_true] at this
    exact this
  rw [hpi, Finset.sum_map, Finset.sum_product_right]
  have hin : ∀ t ∈ exponentTuples131 j M,
      ∑ a ∈ Icc 1 M,
        (if s ∣ N - tuplePower131 ((Fin.consEquiv (fun _ : Fin (j + 1) => ℕ)).toEmbedding (a, t))
          then Sing (N - tuplePower131
            ((Fin.consEquiv (fun _ : Fin (j + 1) => ℕ)).toEmbedding (a, t))) else 0) ≤
        ε' * Lg X := by
    intro t ht
    have htp := tuplePower_le131 ht
    have h6 : 6 * tuplePower131 t + 6 * 2 ^ M ≤ X := by
      have : 6 * (j + 1) * 2 ^ M = 6 * (j * 2 ^ M) + 6 * 2 ^ M := by ring
      omega
    have hm1 : (X : ℝ) / 2 ≤ ((N - tuplePower131 t : ℕ) : ℝ) := by
      have : X ≤ 2 * (N - tuplePower131 t) := by omega
      have h' : (X : ℝ) ≤ 2 * ((N - tuplePower131 t : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hm2 : N - tuplePower131 t ≤ X := by omega
    refine le_trans (le_of_eq ?_) (hA _ hm1 hm2)
    unfold Amr
    rw [sum_filter]
    refine sum_congr rfl fun a ha => ?_
    have ha2 : 2 ^ a ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (mem_Icc.mp ha).2
    have hlt : 2 ^ a < N - tuplePower131 t := by omega
    have hp : tuplePower131 ((Fin.consEquiv (fun _ : Fin (j + 1) => ℕ)).toEmbedding (a, t)) =
        2 ^ a + tuplePower131 t := by
      simp only [tuplePower131, Equiv.toEmbedding_apply, Fin.consEquiv_apply,
        Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hsub : N - (2 ^ a + tuplePower131 t) = N - tuplePower131 t - 2 ^ a := by omega
    rw [hp, hsub]
    by_cases hd : s ∣ N - tuplePower131 t - 2 ^ a
    · rw [if_pos hd, if_pos ⟨hlt, hd⟩]
    · rw [if_neg hd, if_neg (fun h => hd h.2)]
  calc _ ≤ ∑ _t ∈ exponentTuples131 j M, ε' * Lg X := sum_le_sum hin
    _ = (M : ℝ) ^ j * (ε' * Lg X) := by
      rw [sum_const, exponentTuples_card131, nsmul_eq_mul, Nat.cast_pow]
    _ ≤ Lg X ^ j * (ε' * Lg X) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hML j)
        (mul_nonneg hε' (by linarith))
    _ = ε' * Lg X ^ (j + 1) := by ring

/-- PROVED from Lemma 6.2. Displays 12 to 14 on pages 6 and 7: for moduli as in Corollary 4.2,
the singular series sum over tuples with N - M in J_2 is at most any fixed fraction of L^k.
This is the honest J_2 estimate; the old leaf with this name compared integrals instead. -/
theorem major_arcs_j2_131 (k : ℕ) (hk : 1 ≤ k) (K₁ Cstar : ℕ) (hC : 0 < Cstar) (c : ℝ)
    (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ E : Finset ℕ, ExceptionalModuli131 K₁ c X E →
      ∀ N ∈ evenJ131 X, ∀ B ⊆ tuples131 k X,
        (∀ ν ∈ B, ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν)) →
        ∑ ν ∈ B, Sing (N - tuplePower131 ν) ≤ ε * Lg X ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hK : (0 : ℝ) < (K₁ : ℝ) + 1 := by positivity
  set ε' : ℝ := ε / ((K₁ : ℝ) + 1) with hε'def
  have hε' : 0 < ε' := div_pos hε hK
  have hεK : ((K₁ : ℝ) + 1) * ε' = ε := by
    rw [hε'def]
    field_simp
  obtain ⟨r₀, X₁, h62⟩ := lemma62_proved ε' hε'
  obtain ⟨X₂, hX₂⟩ := tuple_window131 (j + 1)
  have ht : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨X₃, hX₃⟩ := (ht.eventually_ge_atTop
    ((r₀ : ℝ) * Cstar / c)).exists_forall_of_atTop
  refine ⟨max X₁ (max X₂ X₃), fun X hX E hE N hN B hB hbad => ?_⟩
  have hx1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hx2 : X₂ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hx3 : X₃ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  obtain ⟨hL, hw⟩ := hX₂ X hx2
  have hL3 := hX₃ X hx3
  have hCr : (0 : ℝ) < Cstar := by exact_mod_cast hC
  have hLk : 0 ≤ Lg X ^ (j + 1) := by positivity
  have hsmall : ∀ r ∈ E, r₀ ≤ oddFree131 Cstar r := by
    intro r hr
    have h1 := hE.2 r hr
    have h2 : (oddRad131 r : ℝ) ≤ oddFree131 Cstar r * Cstar := by
      exact_mod_cast oddRad_le131 hC r
    have h3 : (r₀ : ℝ) * Cstar ≤ c * Lg X := by
      rw [div_le_iff₀ hc] at hL3
      linarith
    have h4 : c * Lg X ≤ c * Lg X ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hc.le
    have h5 : (r₀ : ℝ) * Cstar ≤ oddFree131 Cstar r * Cstar := by linarith
    exact_mod_cast le_of_mul_le_mul_right h5 hCr
  have hLnn : 0 ≤ Lg X := by linarith
  have hone : ∀ r ∈ E, ∑ ν ∈ tuples131 (j + 1) X,
      (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) ≤
        ε' * Lg X ^ (j + 1) := by
    intro r hr
    have ho := oddFree_odd131 Cstar r
    have hA : ∀ m : ℕ, (X : ℝ) / 2 ≤ m → m ≤ X → Amr X m (oddFree131 Cstar r) ≤ ε' * Lg X :=
      fun m hm1 hm2 => h62 X hx1 m _ hm1 hm2 ho.pos ho (hsmall r hr)
    exact tuple_sum_dvd_le131 hA hε'.le hL hw hN
  have hnn : ∀ (ν : Fin (j + 1) → ℕ), ∀ r ∈ E, 0 ≤
      (if oddFree131 Cstar r ∣ N - tuplePower131 ν then
        Sing (N - tuplePower131 ν) else 0) := by
    intro ν r _
    split_ifs
    · exact Sing_nonneg131 _
    · exact le_rfl
  calc ∑ ν ∈ B, Sing (N - tuplePower131 ν)
      ≤ ∑ ν ∈ B, ∑ r ∈ E,
        (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) := by
        refine sum_le_sum fun ν hν => ?_
        have hex : ∃ r ∈ E, r ∣ Cstar * (N - tuplePower131 ν) := by
          by_contra hcon
          exact hbad ν hν (fun r hr hd => hcon ⟨r, hr, hd⟩)
        obtain ⟨r, hr, hd⟩ := hex
        have hs := single_le_sum (hnn ν) hr
        rwa [if_pos (oddFree_dvd131 hd)] at hs
    _ ≤ ∑ ν ∈ tuples131 (j + 1) X, ∑ r ∈ E,
        (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) :=
        sum_le_sum_of_subset_of_nonneg hB fun ν _ _ => sum_nonneg (hnn ν)
    _ = ∑ r ∈ E, ∑ ν ∈ tuples131 (j + 1) X,
        (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) :=
        sum_comm
    _ ≤ ∑ _r ∈ E, ε' * Lg X ^ (j + 1) := sum_le_sum hone
    _ = (E.card : ℝ) * (ε' * Lg X ^ (j + 1)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((K₁ : ℝ) + 1) * (ε' * Lg X ^ (j + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hε'.le hLk)
        have : (E.card : ℝ) ≤ K₁ := by exact_mod_cast hE.1
        linarith
    _ = ε * Lg X ^ (j + 1) := by
        linear_combination (Lg X ^ (j + 1)) * hεK

/-- The statement of the leaf `major_arcs_j1_131`, Corollary 4.2. -/
def Cor42Statement131 : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ (K₁ Cstar : ℕ) (c A : ℝ), 0 < Cstar ∧ 0 < c ∧ 0 ≤ A ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ ExceptionalModuli131 K₁ c X E ∧
        (∀ n ∈ evenWindow131 X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
        (∀ n ∈ evenWindow131 X, |binaryMajor131 X n P| ≤ A * n * Sing n)

/-- The statement of the leaf `major_arcs_combine131`, displays 15 to 24. -/
def SingularAverageStatement131 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |∑ ν ∈ tuples131 k X,
          ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) -
        coefficient131 k N * N * Lg X ^ k| ≤ ε * N * Lg X ^ k

/-- Corollary 4.2 for the binary integral on a chosen window W of even n. Same constants, same P
and E for the whole window. `Cor42Statement131` is the instance W = evenWindow131. -/
def Cor42OnWindow131 (W : ℕ → Finset ℕ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ (K₁ Cstar : ℕ) (c A : ℝ), 0 < Cstar ∧ 0 < c ∧ 0 ≤ A ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ ExceptionalModuli131 K₁ c X E ∧
        (∀ n ∈ W X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
        (∀ n ∈ W X, |binaryMajor131 X n P| ≤ A * n * Sing n)


/-! ### The window `[X/2, X]` against `J(X) = [2X/3, X]`

`cor42_window_extension131` asks for Corollary 4.2 on `evenWindow131 X` from the same statement on
`evenJ131 X`. The two windows differ in exactly the strip `X/2 ≤ n < 2X/3`, and the data `P`, `E` of
the corollary are chosen inside `∀ X`, so the `J(X)` form controls nothing on that strip at the same
`P`. The lemmas below make that precise: `evenWindow131` is `evenJ131` together with the strip, a
bound on a window splits into its `J`-part and its strip part *at the same data*, and consequently
the extension follows from the strip input. `Cor42OnWindow131` is monotone in the window, so the
pair (`cor42_published131`, `cor42_window_extension131`) is equivalent to the single window
statement. -/

/-- `J(X) ⊆ [X/2, X]`. -/
private lemma evenJ_subset_window131 (X : ℕ) : evenJ131 X ⊆ evenWindow131 X := by
  intro n hn
  obtain ⟨h1, h2, h3⟩ := mem_filter.mp hn
  obtain ⟨h4, h5⟩ := mem_Icc.mp h1
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨h4, h5⟩, h2, ?_⟩
  have h6 : 2 * (X : ℝ) / 3 ≤ (n : ℝ) := h3
  have h7 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  linarith

/-- Outside `J(X)`, a point of the window lies in the strip `n < 2X/3`. -/
private lemma mem_window_not_J131 {X n : ℕ} (h : n ∈ evenWindow131 X) (hJ : n ∉ evenJ131 X) :
    2 * (X : ℝ) / 3 > n := by
  obtain ⟨h1, h2, h3⟩ := mem_filter.mp h
  by_contra hcon
  push_neg at hcon
  exact hJ (mem_filter.mpr ⟨h1, h2, hcon⟩)

/-- Conversely, a point of the window in the strip is outside `J(X)`. -/
private lemma mem_strip_not_J131 {X n : ℕ} (h : evenWindow131 X) (hn : 2 * (X : ℝ) / 3 > n) :
    n ∉ evenJ131 X := by
  intro hJ
  obtain ⟨-, -, h3⟩ := mem_filter.mp hJ
  linarith

/-- The window is `J(X)` together with the strip `X/2 ≤ n < 2X/3`. -/
private lemma window_eq_J_union_strip131 (X : ℕ) :
    evenWindow131 X = evenJ131 X ∪ (evenWindow131 X).filter (fun n => 2 * (X : ℝ) / 3 > n) := by
  ext n
  constructor
  · intro h
    by_cases hJ : n ∈ evenJ131 X
    · exact mem_union.mpr (Or.inl hJ)
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨h, mem_window_not_J131 h hJ⟩))
  · intro h
    rcases mem_union.mp h with hJ | hs
    · exact evenJ_subset_window131 X hJ
    · exact (mem_filter.mp hs).1

/-- The strengthening is not vacuous: at `X = 12` the even integer `6` lies in the window and
outside `J(12) = {8, 10, 12}`. -/
private lemma strip_witness131 : (6 : ℕ) ∈ evenWindow131 12 ∧ (6 : ℕ) ∉ evenJ131 12 := by
  constructor
  · refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by norm_num, by norm_num⟩, ⟨3, rfl⟩, ?_⟩
    norm_num
  · intro h
    obtain ⟨-, -, h3⟩ := mem_filter.mp h
    norm_num at h3

/-- A bound holding on a window splits into its `J(X)` part and its strip part. -/
private lemma forall_mem_window_iff131 (X : ℕ) (φ : ℕ → Prop) :
    (∀ n ∈ evenWindow131 X, φ n) ↔
      ((∀ n ∈ evenJ131 X, φ n) ∧
        (∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → φ n)) := by
  constructor
  · intro h
    exact ⟨fun n hn => h n (evenJ_subset_window131 X hn), fun n hn _ => h n hn⟩
  · rintro ⟨h1, h2⟩ n hn
    by_cases hJ : n ∈ evenJ131 X
    · exact h1 n hJ
    · exact h2 n hn (mem_window_not_J131 hn hJ)

/-- `Cor42OnWindow131` is monotone in the window: a bound on a larger window gives one on a
smaller one. -/
private lemma Cor42OnWindow_mono131 {W₁ W₂ : ℕ → Finset ℕ} (h : ∀ X, W₁ X ⊆ W₂ X)
    (hW : Cor42OnWindow131 W₂) : Cor42OnWindow131 W₁ := by
  intro η hη
  obtain ⟨K₁, Cstar, c, A, h1, h2', h3, X₀, hX₀⟩ := hW η hη
  refine ⟨K₁, Cstar, c, A, h1, h2', h3, X₀, fun X hX => ?_⟩
  obtain ⟨P, E, hP, hE, hrel, hup⟩ := hX₀ X hX
  exact ⟨P, E, hP, hE, fun n hn => hrel n (h X hn), fun n hn => hup n (h X hn)⟩

/-- The window form implies the `J(X)` form of Corollary 4.2 with the same constants. -/
private lemma cor42_J_of_window131 (h : Cor42OnWindow131 evenWindow131) :
    Cor42OnWindow131 evenJ131 :=
  Cor42OnWindow_mono131 (fun X => evenJ_subset_window131 X) h

/-- **The strip input of `cor42_window_extension131`.** Displays 11 and 12 for the integers of
`[X/2, 2X/3)` alone, with the constants, the admissible `P` and the exceptional set `E` exactly as
in `Cor42OnWindow131`. This is the missing input of the leaf: no argument from the `J(X)` form
reaches these `n` at the same `P`, because `binaryMajor131 X n P` depends on `X` through
`primeSum131 X` and `majorArcs131 X P`. The statement is the leaf's conclusion with the window
bounds split into their `J` and strip parts. -/
private theorem cor42_strip_input_iff131 :
    (∀ η : ℝ, 0 < η →
      ∃ (K₁ Cstar : ℕ) (c A : ℝ), 0 < Cstar ∧ 0 < c ∧ 0 ≤ A ∧
        ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
          ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ ExceptionalModuli131 K₁ c X E ∧
            (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
              |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
            (∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → Nonexceptional131 Cstar E n →
              |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
            (∀ n ∈ evenJ131 X, |binaryMajor131 X n P| ≤ A * n * Sing n) ∧
            (∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n →
              |binaryMajor131 X n P| ≤ A * n * Sing n)) ↔
    Cor42OnWindow131 evenWindow131 := by
  constructor
  · intro hs η hη
    obtain ⟨K₁, Cstar, c, A, h1, h2, h3, X₀, hX₀⟩ := hs η hη
    refine ⟨K₁, Cstar, c, A, h1, h2, h3, X₀, fun X hX => ?_⟩
    obtain ⟨P, E, hP, hE, hrelJ, hrelS, hupJ, hupS⟩ := hX₀ X hX
    refine ⟨P, E, hP, hE, ?_, ?_⟩
    · exact (forall_mem_window_iff131 X
        (fun n => Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n)).mpr ⟨hrelJ, hrelS⟩
    · exact (forall_mem_window_iff131 X
        (fun n => |binaryMajor131 X n P| ≤ A * n * Sing n)).mpr ⟨hupJ, hupS⟩
  · intro hb η hη
    obtain ⟨K₁, Cstar, c, A, h1, h2, h3, X₀, hX₀⟩ := hb η hη
    refine ⟨K₁, Cstar, c, A, h1, h2, h3, X₀, fun X hX => ?_⟩
    obtain ⟨P, E, hP, hE, hrel, hup⟩ := hX₀ X hX
    obtain ⟨hrelJ, hrelS⟩ := (forall_mem_window_iff131 X
      (fun n => Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n)).mp hrel
    obtain ⟨hupJ, hupS⟩ := (forall_mem_window_iff131 X
      (fun n => |binaryMajor131 X n P| ≤ A * n * Sing n)).mp hup
    exact ⟨P, E, hP, hE, hrelJ, hrelS, hupJ, hupS⟩

/-- **`cor42_window_extension131` from the strip input.** A reduction, not a proof of the leaf: the
strip input is not in this file's closure, and it is not a consequence of `cor42_published131`
either, since that statement fixes `P` and `E` only on `J(X)`. -/
private theorem cor42_window_extension_of_strip131
    (hs : ∀ η : ℝ, 0 < η →
      ∃ (K₁ Cstar : ℕ) (c A : ℝ), 0 < Cstar ∧ 0 < c ∧ 0 ≤ A ∧
        ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
          ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ ExceptionalModuli131 K₁ c X E ∧
            (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
              |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
            (∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → Nonexceptional131 Cstar E n →
              |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
            (∀ n ∈ evenJ131 X, |binaryMajor131 X n P| ≤ A * n * Sing n) ∧
            (∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n →
              |binaryMajor131 X n P| ≤ A * n * Sing n)) :
    Cor42OnWindow131 evenJ131 → Cor42OnWindow131 evenWindow131 :=
  fun _ => cor42_strip_input_iff131.mp hs



/-! ### The singular series average: displays 15 to 24 (private development of unit J218)

The development below proves `major_arcs_combine131`. `Sing_even_eq218` puts the singular series in
the form `2c₀ H`, `tuple_H_eq_sum` is the tuple exchange of displays 15 to 17, `S0_estimate218` is
the estimate of displays 17 to 24 with the period of the moduli split at `K = ⌊√L⌋`, and
`major_arcs_combine218` is the leaf itself. -/


/-- The product defining the twin prime constant converges over `ℕ` as well. -/
private theorem summable_inv_sq218 :
    Summable (fun m : ℕ => 1 / ((m : ℝ) - 1) ^ 2) :=
  LeanLab.ChenExplicit.summable_inv_sub_one_sq

/-- The `m = 2` factor of the singular series. -/
private theorem singF_two218 {n : ℕ} (hn : Even n) : singF n ⟨2, Nat.prime_two⟩ = 2 := by
  unfold singF
  rw [if_pos (even_iff_two_dvd.mp hn)]
  norm_num

/-- **The singular series in product form**: for even `n ≥ 1`,
`𝔖(n) = 2 c₀ ∏_{p ∣ n, p > 2} (1 + 1/(p - 2)) = 2 c₀ H(n)`. -/
private theorem Sing_even_eq218 {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    Sing n = 2 * LeanLab.ChenExplicit.twinC * H n := by
  classical
  have h2dvd : (2 : ℕ) ∣ n := even_iff_two_dvd.mp hn
  set A : ℕ → ℝ := fun m => if m = 2 then 2 else 1 with hAdef
  set B : ℕ → ℝ := fun m => if m.Prime ∧ 2 < m then 1 - 1 / ((m : ℝ) - 1) ^ 2 else 1 with hBdef
  set C : ℕ → ℝ := fun m =>
    if m.Prime ∧ 2 < m then (if m ∣ n then ((m : ℝ) - 1) / ((m : ℝ) - 2) else 1) else 1
    with hCdef
  -- (1) `Sing` is the product over `ℕ` of the prime-indicator of `singF`.
  have hPhi : Sing n = ∏' m : ℕ, (if h : m.Prime then singF n ⟨m, h⟩ else 1) := by
    have h1 : ∀ x : {m : ℕ // m.Prime},
        (if h : (x : ℕ).Prime then singF n ⟨(x : ℕ), h⟩ else 1) = singF n x := by
      intro x; exact dif_pos x.2
    calc ∏' x : {m : ℕ // m.Prime}, singF n x
        = ∏' x : {m : ℕ // m.Prime},
            (if h : (x : ℕ).Prime then singF n ⟨(x : ℕ), h⟩ else 1) := tprod_congr fun x => (h1 x).symm
      _ = ∏' m : ℕ, Set.mulIndicator {m : ℕ | m.Prime}
            (fun m => if h : m.Prime then singF n ⟨m, h⟩ else 1) m :=
            tprod_subtype (s := {m : ℕ | m.Prime})
              (f := fun m => if h : m.Prime then singF n ⟨m, h⟩ else 1)
      _ = ∏' m : ℕ, (if h : m.Prime then singF n ⟨m, h⟩ else 1) := by
            refine tprod_congr fun m => ?_
            by_cases h : m.Prime
            · rw [Set.mulIndicator_of_mem (by exact h), dif_pos h]
            · rw [Set.mulIndicator_of_notMem (by simpa using h), dif_neg h]
  -- (2) the pointwise factorisation
  have hpt : ∀ m : ℕ, (if h : m.Prime then singF n ⟨m, h⟩ else 1) = A m * B m * C m := by
    intro m
    simp only [hAdef, hBdef, hCdef]
    by_cases hP : m.Prime
    · rw [dif_pos hP]
      by_cases hm2 : m = 2
      · subst hm2
        have hs : singF n ⟨2, Nat.prime_two⟩ = 2 := by
          unfold singF
          rw [if_pos h2dvd]; norm_num
        rw [hs]
        simp [Nat.prime_two]
      · have hlt : 2 < m := lt_of_le_of_ne hP.two_le (Ne.symm hm2)
        rw [if_neg hm2, if_pos ⟨hP, hlt⟩, if_pos ⟨hP, hlt⟩, one_mul]
        have h3 : (3 : ℝ) ≤ (m : ℝ) := by
          have h3n : 3 ≤ m := by
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
            have hk2 : 2 ≤ k := by
              by_contra hc
              have : k ≤ 1 := by omega
              have : m ≤ 2 := by omega
              omega
            omega
          exact_mod_cast h3n
        by_cases hd : m ∣ n
        · rw [if_pos hd]
          unfold singF
          rw [if_pos hd]
          have hm0 : (m : ℝ) ≠ 0 := by positivity
          have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
          have hm2' : (m : ℝ) - 2 ≠ 0 := by linarith
          field_simp
          ring
        · rw [if_neg hd]
          unfold singF
          rw [if_neg hd]
          ring
    · have hm2 : m ≠ 2 := fun e => hP (e ▸ Nat.prime_two)
      rw [dif_neg hP, if_neg hm2]
      simp [hP]
  -- (3) the three factors are multipliable
  have hA : Multipliable A := by
    refine multipliable_of_hasFiniteMulSupport (Set.Finite.subset (Set.finite_singleton 2) ?_)
    intro m hm
    simp only [hAdef, Function.mulSupport, Function.mem_support, ne_eq] at hm
    by_cases h : m = 2
    · simpa using h
    · exact absurd (if_neg h) hm
  have hsumC : Summable (fun m : ℕ =>
      (if m.Prime ∧ 2 < m then (-(1 / ((m : ℝ) - 1) ^ 2)) else 0)) := by
    refine Summable.of_norm_bounded (g := fun m : ℕ => 1 / ((m : ℝ) - 1) ^ 2)
      summable_inv_sq218 ?_
    intro m
    by_cases h : m.Prime ∧ 2 < m
    · have hd : (0:ℝ) < (m:ℝ) - 1 := by
        have h3 : (3:ℝ) ≤ (m:ℝ) := by
          exact_mod_cast (show 3 ≤ m by omega)
        linarith
      rw [if_pos h, norm_neg, Real.norm_eq_abs, abs_div, abs_one, abs_pow, abs_of_pos hd]
    · rw [if_neg h, norm_zero]; positivity
  have hB : Multipliable B := by
    refine (Real.multipliable_one_add_of_summable hsumC).congr fun m => ?_
    simp only [hBdef]
    by_cases h : m.Prime ∧ 2 < m
    · rw [if_pos h, if_pos h]; try ring
    · rw [if_neg h, if_neg h]; try ring
  have hCsupp : ∀ m, C m ≠ 1 → m ∈ n.primeFactors := by
    intro m hm
    simp only [hCdef] at hm
    by_cases h : m.Prime ∧ 2 < m
    · rw [if_pos h] at hm
      by_cases hd : m ∣ n
      · rw [if_pos hd] at hm
        exact Nat.mem_primeFactors.2 ⟨h.1, hd, hn0⟩
      · rw [if_neg hd] at hm
        exact absurd rfl hm
    · rw [if_neg h] at hm
      exact absurd rfl hm
  have hC : Multipliable C :=
    multipliable_of_hasFiniteMulSupport
      (Set.Finite.subset (Finset.finite_toSet _) fun m hm => hCsupp m (by simpa using hm))
  -- (4) distribute the products
  have hmAB : Multipliable (fun m => A m * B m) := (hA.hasProd.mul hB.hasProd).multipliable
  have hsplit1 : ∏' m : ℕ, (A m * B m * C m) = (∏' m : ℕ, (A m * B m)) * ∏' m : ℕ, C m :=
    Multipliable.tprod_mul hmAB hC
  have hsplit2 : ∏' m : ℕ, (A m * B m) = (∏' m : ℕ, A m) * ∏' m : ℕ, B m :=
    Multipliable.tprod_mul hA hB
  -- (5) the three values
  have hAval : ∏' m : ℕ, A m = 2 := by
    rw [hAdef]
    rw [tprod_eq_mulSingle 2 (fun m hm => if_neg hm)]
    simp
  have hBval : ∏' m : ℕ, B m = LeanLab.ChenExplicit.twinC := by
    have e : ∏' m : ℕ, B m =
        ∏' m : ℕ, Set.mulIndicator {m : ℕ | m.Prime ∧ 2 < m}
          (fun m : ℕ => 1 - 1 / ((m : ℝ) - 1) ^ 2) m := by
      refine tprod_congr fun m => ?_
      simp only [hBdef]
      by_cases h : m.Prime ∧ 2 < m
      · rw [if_pos h, Set.mulIndicator_of_mem (by exact h)]
      · rw [if_neg h, Set.mulIndicator_of_notMem (by simpa using h)]
    rw [e, ← tprod_subtype (s := {m : ℕ | m.Prime ∧ 2 < m})
      (f := fun m : ℕ => 1 - 1 / ((m : ℝ) - 1) ^ 2)]
    rfl
  have hCval : ∏' m : ℕ, C m = H n := by
    set s : Finset ℕ := n.primeFactors.filter (fun p => 2 < p) with hsdef
    have hoff : ∀ m ∉ s, C m = 1 := by
      intro m hm
      simp only [hCdef]
      by_cases h : m.Prime ∧ 2 < m
      · rw [if_pos h]
        by_cases hd : m ∣ n
        · rw [if_pos hd]
          have hmem : m ∈ n.primeFactors.filter (fun p => 2 < p) :=
            mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨h.1, hd, hn0⟩, h.2⟩
          exact absurd (by simpa [hsdef] using hmem) hm
        · rw [if_neg hd]
      · rw [if_neg h]
    have hprod : ∏' m : ℕ, C m = ∏ m ∈ s, C m := tprod_eq_prod hoff
    rw [hprod]
    have hval : ∀ m ∈ s, C m = (1 + 1 / ((m : ℝ) - 2)) := by
      intro m hm
      have hm' : m ∈ n.primeFactors.filter (fun p => 2 < p) := by simpa [hsdef] using hm
      obtain ⟨hmem, hm2⟩ := mem_filter.1 hm'
      have hP : m.Prime := Nat.prime_of_mem_primeFactors hmem
      have hdvd : m ∣ n := Nat.dvd_of_mem_primeFactors hmem
      simp only [hCdef]
      rw [if_pos ⟨hP, hm2⟩, if_pos hdvd]
      have h3 : (3:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      have h0 : (m : ℝ) - 2 ≠ 0 := by linarith
      field_simp
      ring
    rw [Finset.prod_congr rfl hval, hsdef]
    try rfl
  calc Sing n = ∏' m : ℕ, (if h : m.Prime then singF n ⟨m, h⟩ else 1) := hPhi
    _ = ∏' m : ℕ, (A m * B m * C m) := tprod_congr hpt
    _ = (∏' m : ℕ, (A m * B m)) * ∏' m : ℕ, C m := hsplit1
    _ = ((∏' m : ℕ, A m) * ∏' m : ℕ, B m) * ∏' m : ℕ, C m := by rw [hsplit2]
    _ = (2 * LeanLab.ChenExplicit.twinC) * H n := by rw [hAval, hBval, hCval]
    _ = 2 * LeanLab.ChenExplicit.twinC * H n := by ring

/-- A prime dividing a product of primes from `t` belongs to `t`. -/
private theorem prime_dvd_prod_mem218 {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) {q : ℕ}
    (hq : q.Prime) (hd : q ∣ ∏ p ∈ t, p) : q ∈ t := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty] at hd
      exact absurd hd (hq.not_dvd_one)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha] at hd
      rcases hq.dvd_mul.mp hd with h | h
      · have ha' : a.Prime := ht a (Finset.mem_insert_self a s)
        rcases ha'.eq_one_or_self_of_dvd q h with h1 | h1
        · exact absurd h1 hq.ne_one
        · rw [h1]; exact Finset.mem_insert_self a s
      · exact Finset.mem_insert_of_mem
          (ih (fun p hp => ht p (Finset.mem_insert_of_mem hp)) h)

/-- A product of primes has exactly those primes as its prime factors. -/
private theorem primeFactors_prod_of_primes218 {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) :
    Nat.primeFactors (∏ p ∈ t, p) = t := by
  have h0 : ∏ p ∈ t, p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (ht p hp).ne_zero
  ext q
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hq, hd, -⟩
    exact prime_dvd_prod_mem218 ht hq hd
  · intro hq
    exact ⟨ht q hq, Finset.dvd_prod_of_mem _ hq, h0⟩

/-- Display 2 in divisor form: `𝔖(n) = 2c₀ Σ'_{d ∣ n} f(d)` for even `n ≥ 1`. -/
private theorem Sing_even_eq_divisor218 {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    Sing n = 2 * LeanLab.ChenExplicit.twinC *
      ∑ d ∈ n.divisors.filter (fun d => Squarefree d ∧ Odd d), fd d := by
  classical
  rw [Sing_even_eq218 hn hn0]
  congr 1
  unfold H
  set G : ℕ → ℝ := fun p => if p = 2 then 0 else 1 / ((p : ℝ) - 2) with hGdef
  have h1 : ∑ d ∈ n.divisors.filter (fun d => Squarefree d ∧ Odd d), fd d
      = ∑ d ∈ n.divisors.filter (fun d => Squarefree d), (if Odd d then fd d else 0) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : Squarefree d <;> by_cases h2 : Odd d <;> simp [h, h2]
  rw [h1, Nat.sum_divisors_filter_squarefree hn0]
  have he : (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
    rw [Nat.factors_eq]; rfl
  rw [he]
  have hpt : ∀ t ∈ n.primeFactors.powerset,
      (if Odd t.val.prod then fd t.val.prod else 0) = ∏ p ∈ t, G p := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    have htp : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
    have hprod : t.val.prod = ∏ p ∈ t, p := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hprod]
    by_cases h2 : 2 ∈ t
    · have hodd : ¬ Odd (∏ p ∈ t, p) :=
        Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr (Finset.dvd_prod_of_mem _ h2))
      rw [if_neg hodd]
      exact (Finset.prod_eq_zero h2 (by simp [hGdef])).symm
    · have hlt : ∀ p ∈ t, 2 < p := by
        intro p hp
        have hp2 : p ≠ 2 := fun h => h2 (h ▸ hp)
        have := (htp p hp).two_le
        omega
      have hodd : Odd (∏ p ∈ t, p) := by
        refine Finset.prod_induction (fun p => p) Odd (fun a b ha hb => ha.mul hb) odd_one
          fun p hp => (htp p hp).odd_of_ne_two (fun h => h2 (h ▸ hp))
      rw [if_pos hodd, fd, primeFactors_prod_of_primes218 htp, Finset.filter_true_of_mem hlt]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [hGdef]
      beta_reduce
      rw [if_neg (by have := hlt p hp; omega : p ≠ 2)]
  rw [Finset.sum_congr rfl hpt]
  rw [← Finset.prod_one_add]
  have h2 : ∏ p ∈ n.primeFactors, (1 + G p) = ∏ p ∈ n.primeFactors.filter (fun p => 2 < p),
      (1 + 1 / ((p : ℝ) - 2)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => 2 < p)
      (fun p => 1 + G p)]
    have hone : ∏ p ∈ n.primeFactors.filter (fun p => ¬ 2 < p), (1 + G p) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      simp only [Finset.mem_filter] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp.1
      have hp2 : p = 2 := by have := hpp.two_le; omega
      simp [hGdef, hp2]
    rw [hone, mul_one]
    refine Finset.prod_congr rfl fun p hp => ?_
    simp only [Finset.mem_filter] at hp
    rw [hGdef]
    beta_reduce
    rw [if_neg (by omega : p ≠ 2)]
  rw [h2]

/-- **The `k`-tuple exchange of displays 15 to 17**, before any estimate: the weighted count over
exponent tuples is a weighted sum over the squarefree divisors that occur, each counted once per
tuple that it divides. This is the `k`-tuple form of `sum_H_le`'s first step. -/
private theorem tuple_H_eq_sum (k M N : ℕ) :
    ∑ ν ∈ exponentTuples131 k M, H (N - tuplePower131 ν) =
      ∑ s ∈ (exponentTuples131 k M).biUnion (fun ν => (opf (N - tuplePower131 ν)).powerset),
        (#{ν ∈ exponentTuples131 k M |
          s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s := by
  classical
  set T := exponentTuples131 k M with hT
  set Pν : (Fin k → ℕ) → Finset (Finset ℕ) := fun ν => (opf (N - tuplePower131 ν)).powerset with hPν
  set U := T.biUnion Pν with hU
  have hPU : ∀ ν ∈ T, Pν ν ⊆ U := fun ν hν => subset_biUnion_of_mem Pν hν
  calc ∑ ν ∈ T, H (N - tuplePower131 ν)
      = ∑ ν ∈ T, ∑ s ∈ U, if s ∈ Pν ν then W s else 0 := by
          refine sum_congr rfl fun ν hν => ?_
          rw [H_eq_sum, sum_ite_mem, inter_eq_right.2 (hPU ν hν)]
    _ = ∑ s ∈ U, ∑ ν ∈ T, if s ∈ Pν ν then W s else 0 := sum_comm
    _ = ∑ s ∈ U, (#{ν ∈ T | s ∈ Pν ν} : ℝ) * W s := by
          refine sum_congr rfl fun s _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]

/-- **P0045 (22), the `Σ₂` of display 21**: the part of the series (26) carried by moduli with
`ξ(d) > K` is as small as we please, uniformly in the truncation point. Used to discard the
`ξ(d) > L^{1/2}` half of the divisor sum in display 21. -/
private theorem exists_xi_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ K' : ℕ, K ≤ K' →
      ∑' d : ℕ, (if K' < xi d then seriesTerm d else 0) ≤ ε := by
  classical
  have hnn : ∀ d, 0 ≤ seriesTerm d := fun d => seriesTerm_nonneg d
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∑' k : ℕ, seriesTerm (k + (D + 1)) ≤ ε := by
    obtain ⟨D, hD⟩ :=
      ((tendsto_order.1 (tendsto_sum_nat_add seriesTerm)).2 ε hε).exists_forall_of_atTop
    exact ⟨D, le_of_lt (hD (D + 1) (by omega))⟩
  refine ⟨(Finset.range (D + 1)).sup xi, fun K' hK' => ?_⟩
  refine Real.tsum_le_of_sum_le (f := fun d => if K' < xi d then seriesTerm d else 0)
    (fun d => ?_) (fun s => ?_)
  · show (0 : ℝ) ≤ (if K' < xi d then seriesTerm d else 0)
    split_ifs with h
    · exact hnn d
    · exact le_rfl
  · have hsub : s.filter (fun d => K' < xi d) ⊆ Finset.Icc (D + 1) (s.sup id) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      have hdmem : d ∈ s := hd.1
      have hK : K' < xi d := hd.2
      have hlt : ¬ d < D + 1 := by
        intro hcon
        have : xi d ≤ (Finset.range (D + 1)).sup xi :=
          Finset.le_sup (s := Finset.range (D + 1)) (f := xi) (Finset.mem_range.2 hcon)
        omega
      exact Finset.mem_Icc.2 ⟨by omega, Finset.le_sup (f := id) hdmem⟩
    have hkey : ∑ d ∈ s, (if K' < xi d then seriesTerm d else 0) =
        ∑ d ∈ s.filter (fun d => K' < xi d), seriesTerm d := by
      rw [Finset.sum_filter]
    rw [hkey]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hnn d)) ?_
    exact le_trans (tail_le D _ (fun d hd => (Finset.mem_Icc.1 hd).1)) hD



/-! ## 2b. The pieces of the singular-series average (P0045 displays 17 to 22) -/

/-- The tuple count over the exponent tuples equals `residueTupleCount131` at the modulus
`d = ∏ s`: the set `s ⊆ opf (N - M_ν)` is exactly `d ∣ N - M_ν`. -/
private lemma count_eq_residue218 {k M N : ℕ}
    (hN : ∀ ν ∈ exponentTuples131 k M, tuplePower131 ν ≤ N)
    (hpos : ∀ ν ∈ exponentTuples131 k M, 0 < N - tuplePower131 ν)
    {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    #{ν ∈ exponentTuples131 k M | s ∈ (opf (N - tuplePower131 ν)).powerset}
      = residueTupleCount131 (∏ p ∈ s, p) k M N := by
  classical
  have hbase : exponentTuples131 k M = Fintype.piFinset (fun _ : Fin k => Icc 1 M) := rfl
  rw [hbase]
  unfold residueTupleCount131
  congr 1
  ext ν
  simp only [mem_filter]
  constructor
  · rintro ⟨hν, hsub⟩
    refine ⟨hν, ?_⟩
    have hle := hN ν hν
    have hd : (∏ p ∈ s, p) ∣ N - tuplePower131 ν :=
      Finset.prod_primes_dvd _ (fun p hp => (hs p hp).1.prime)
        (fun p hp => (opf_spec (mem_powerset.1 hsub hp)).2.2)
    have h1 : ((∏ p ∈ s, p : ℕ) : ℤ) ∣ ((N - tuplePower131 ν : ℕ) : ℤ) := by exact_mod_cast hd
    have hcast : ((tuplePower131 ν : ℕ) : ℤ) = ∑ i, (2 : ℤ) ^ ν i := by
      simp [tuplePower131]
    rw [Nat.cast_sub hle, hcast] at h1
    exact h1
  · rintro ⟨hν, hdvd⟩
    refine ⟨hν, ?_⟩
    have hle := hN ν hν
    have hcast : ((tuplePower131 ν : ℕ) : ℤ) = ∑ i, (2 : ℤ) ^ ν i := by
      simp [tuplePower131]
    have h1 : ((∏ p ∈ s, p : ℕ) : ℤ) ∣ ((N - tuplePower131 ν : ℕ) : ℤ) := by
      rwa [Nat.cast_sub hle, hcast]
    have hd : (∏ p ∈ s, p) ∣ N - tuplePower131 ν := by exact_mod_cast h1
    refine mem_powerset.2 ?_
    intro p hp
    have hpd : p ∣ N - tuplePower131 ν :=
      (Finset.dvd_prod_of_mem _ hp).trans hd
    have hp' := hs p hp
    exact mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp'.1, hpd, (hpos ν hν).ne'⟩, hp'.2⟩

/-- `ξ(d) ≤ K` bounds `d`: `d ∣ 2^ξ(d) - 1`. -/
private lemma d_le_two_pow218 {d K : ℕ} (hd : Odd d) (hd0 : 0 < d) (h : xi d ≤ K) :
    d ≤ 2 ^ K := by
  obtain ⟨h1, h2⟩ := xi_odd hd hd0
  have hpos : 0 < 2 ^ xi d - 1 := by
    have h3 : 2 ≤ 2 ^ xi d := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ xi d := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hdle : d ≤ 2 ^ xi d - 1 := Nat.le_of_dvd hpos h2
  have hmono : 2 ^ xi d ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) h
  omega

/-- A nonzero `jcount` exhibits an exponent tuple in `[1, ξ(d)]^{k}` with `d ∣ N - Σ 2^ν`. -/
private lemma jcount_pos_witness218 {d j N : ℕ} (hpos : 0 < jcount d j N) :
    ∃ ν : Fin (j + 1) → ℕ, (∀ i, 1 ≤ ν i ∧ ν i ≤ xi d) ∧
      (d : ℤ) ∣ (N : ℤ) - ∑ i, (2 : ℤ) ^ ν i := by
  classical
  unfold jcount at hpos
  obtain ⟨ν, hν⟩ := Finset.card_pos.mp hpos
  rw [mem_filter] at hν
  exact ⟨ν, fun i => mem_Icc.1 (Fintype.mem_piFinset.1 hν.1 i), hν.2⟩

/-- If `ξ(d) ≤ M` and `jcount d j N ≠ 0`, then `d` divides some `N - tuplePower131 ν`
with `ν ∈ exponentTuples131 (j+1) M`. This is what makes the divisor sum over `U` exhaustive
for the moduli with `ξ(d) ≤ K`. -/
private lemma jcount_pos_mem218 {d j M N : ℕ} (hj : xi d ≤ M)
    (hle : ∀ ν ∈ exponentTuples131 (j + 1) M, tuplePower131 ν ≤ N)
    (hpos : 0 < jcount d j N) :
    ∃ ν ∈ exponentTuples131 (j + 1) M, d ∣ N - tuplePower131 ν := by
  classical
  obtain ⟨ν, hν, hdvd⟩ := jcount_pos_witness218 hpos
  have hmem : ν ∈ exponentTuples131 (j + 1) M := by
    rw [exponentTuples131, Fintype.mem_piFinset]
    intro i
    exact mem_Icc.2 ⟨(hν i).1, le_trans (hν i).2 hj⟩
  refine ⟨ν, hmem, ?_⟩
  have hcast : ((tuplePower131 ν : ℕ) : ℤ) = ∑ i, (2 : ℤ) ^ ν i := by
    simp [tuplePower131]
  have h1 : (d : ℤ) ∣ ((N - tuplePower131 ν : ℕ) : ℤ) := by
    rwa [Nat.cast_sub (hle ν hmem), hcast]
  exact_mod_cast h1

/-- `H` at the product `P` of the shifted arguments is `O((k+1) log L)`: the argument of
`lemma62_proved`, where now `P` has `M^k` factors so `ω(P) ≤ L^{k+1}`. -/
private lemma H_prod_bound218 {k M X N : ℕ} (hX : 1 ≤ X) (hk : 1 ≤ k)
    (hM : (M : ℝ) ≤ Lg X) (hcard : k ≤ M)
    (hN : N ≤ X) (hpos : ∀ ν ∈ exponentTuples131 k M, 0 < N - tuplePower131 ν) :
    H (∏ ν ∈ exponentTuples131 k M, (N - tuplePower131 ν)) ≤
      3 * Real.exp 27 * ((k : ℝ) + 1) * Real.log (Lg X + 2) := by
  classical
  set T := exponentTuples131 k M with hT
  set P : ℕ := ∏ ν ∈ T, (N - tuplePower131 ν) with hP
  have hL1 : (1 : ℝ) ≤ Lg X := by
    have h1 : 1 ≤ M := le_trans hk hcard
    have h2 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1
    linarith
  have hL0 : 0 ≤ Lg X := by linarith
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 fun ν hν => (hpos ν hν).ne'
  have hcardM : T.card = M ^ k := exponentTuples_card131 k M
  have hω : (P.primeFactors.card : ℝ) ≤ (Lg X) ^ (k + 1) := by
    have h1 : 2 ^ P.primeFactors.card ≤ P := Romanov.two_pow_card_le P hP0
    have h2 : P ≤ X ^ T.card := by
      calc P ≤ ∏ _ν ∈ T, X :=
            Finset.prod_le_prod fun ν _ => le_trans (Nat.sub_le N _) hN
        _ = X ^ T.card := by rw [prod_const]
    have h3 : ((2 : ℝ) ^ P.primeFactors.card) ≤ (X : ℝ) ^ T.card := by
      exact_mod_cast le_trans h1 h2
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_pow, Real.log_pow] at h4
    have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hLX : Real.log X = Lg X * Real.log 2 := by
      rw [Lg, Real.logb, div_mul_cancel₀ _ hl2.ne']
    rw [hLX] at h4
    have h5 : (P.primeFactors.card : ℝ) ≤ T.card * Lg X := by
      have h6 : (P.primeFactors.card : ℝ) * Real.log 2 ≤ (T.card * Lg X) * Real.log 2 := by
        calc (P.primeFactors.card : ℝ) * Real.log 2 ≤ (T.card : ℝ) * (Lg X * Real.log 2) := h4
          _ = (T.card * Lg X) * Real.log 2 := by push_cast; ring
      exact le_of_mul_le_mul_right h6 hl2
    have h7 : (T.card : ℝ) = (M : ℝ) ^ k := by rw [hcardM]; push_cast; ring
    have h8 : (M : ℝ) ^ k ≤ (Lg X) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg M) hM k
    have h9 : (T.card * Lg X : ℝ) ≤ (Lg X) ^ (k + 1) := by
      rw [h7, pow_succ]
      exact mul_le_mul_of_nonneg_right h8 hL0
    linarith
  set y : ℕ := ⌈(Lg X) ^ (k + 1)⌉₊ + 4 with hy
  have hy4 : 4 ≤ y := by omega
  have hωy : P.primeFactors.card ≤ y := by
    have h2 : ((P.primeFactors.card : ℕ) : ℝ) ≤ (Lg X) ^ (k + 1) := hω
    have h3 : (Lg X) ^ (k + 1) ≤ ((⌈(Lg X) ^ (k + 1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h4 : ((P.primeFactors.card : ℕ) : ℝ) < ((⌈(Lg X) ^ (k + 1)⌉₊ : ℕ) : ℝ) + 1 := by
      linarith
    have h5 : P.primeFactors.card < ⌈(Lg X) ^ (k + 1)⌉₊ + 1 := by exact_mod_cast h4
    omega
  have hsum := sum_W_opf_le P y hy4 hωy
  rw [H_eq_sum P]
  refine le_trans hsum ?_
  have hy0 : (0 : ℝ) < (y : ℝ) := by
    have h1 : 0 < y := by omega
    exact_mod_cast h1
  have hyb : (y : ℝ) ≤ 6 * (Lg X) ^ (k + 1) := by
    have h1 : ((⌈(Lg X) ^ (k + 1)⌉₊ : ℕ) : ℝ) < (Lg X) ^ (k + 1) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ (Lg X) ^ (k + 1) := one_le_pow₀ hL1
    have hyc : (y : ℝ) = ((⌈(Lg X) ^ (k + 1)⌉₊ : ℕ) : ℝ) + 4 := by
      rw [hy, Nat.cast_add, Nat.cast_ofNat]
    rw [hyc]
    linarith
  have hlog : Real.log (y : ℝ) ≤ 3 * ((k : ℝ) + 1) * Real.log (Lg X + 2) := by
    have ha : (0 : ℝ) < 6 * (Lg X) ^ (k + 1) := by positivity
    have hb : (1 : ℝ) ≤ Real.log (Lg X + 2) := by
      have h3 : (3 : ℝ) ≤ Lg X + 2 := by linarith
      have h4 : Real.exp 1 < Lg X + 2 := lt_of_lt_of_le Real.exp_one_lt_d9 (by linarith)
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (Lg X + 2) := Real.log_le_log (Real.exp_pos 1) h4.le
    have h1 : Real.log (y : ℝ) ≤ Real.log (6 * (Lg X) ^ (k + 1)) := Real.log_le_log hy0 hyb
    have h2 : Real.log (6 * (Lg X) ^ (k + 1)) =
        Real.log 6 + ((k : ℝ) + 1) * Real.log (Lg X) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    have h6 : Real.log 6 ≤ 2 := by
      have h7 : (6 : ℝ) ≤ Real.exp 2 := by
        have h8 := Real.exp_one_gt_d9
        have h9 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      calc Real.log 6 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h7
        _ = 2 := Real.log_exp 2
    have h3 : Real.log (Lg X) ≤ Real.log (Lg X + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have h4 : ((k : ℝ) + 1) * Real.log (Lg X) ≤ ((k : ℝ) + 1) * Real.log (Lg X + 2) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : (2 : ℝ) ≤ 2 * ((k : ℝ) + 1) * Real.log (Lg X + 2) := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith [hb, hk1]
    have h6' : (0 : ℝ) ≤ ((k : ℝ) + 1) * Real.log (Lg X + 2) := by positivity
    linarith [h1, h2, h4, h5, h6, h6']
  calc Real.exp 27 * Real.log (y : ℝ)
      ≤ Real.exp 27 * (3 * ((k : ℝ) + 1) * Real.log (Lg X + 2)) :=
        mul_le_mul_of_nonneg_left hlog (Real.exp_pos 27).le
    _ = 3 * Real.exp 27 * ((k : ℝ) + 1) * Real.log (Lg X + 2) := by ring


/-! ## 2c. The divisor sum over the occurring moduli is the finite part of (23) -/

/-- **Displays 20 to 23, the identification step.** The coefficient sum over the moduli that
occur in `U` with `ξ(d) ≤ M` is the finite part of the series (23): a modulus with `ξ(d) ≤ M`
that occurs in the series at all divides some `N - tuplePower131 ν` with `ν` in the truncated
box, hence is one of the moduli counted in `U`. The bound `d ≤ 2^ξ(d) ≤ 2^M` makes the sum
finite. -/
private lemma coeff_image_eq218 {j M N : ℕ}
    (hle : ∀ ν ∈ exponentTuples131 (j + 1) M, tuplePower131 ν ≤ N)
    (hpos : ∀ ν ∈ exponentTuples131 (j + 1) M, 0 < N - tuplePower131 ν) :
    ∑ s ∈ ((exponentTuples131 (j + 1) M).biUnion
        (fun ν => (opf (N - tuplePower131 ν)).powerset)).filter
        (fun s => xi (∏ p ∈ s, p) ≤ M),
        Ckterm (j + 1) N (∏ p ∈ s, p)
      = ∑ d ∈ (Finset.range (2 ^ M + 1)).filter (fun d => xi d ≤ M), Ckterm (j + 1) N d := by
  classical
  set T := exponentTuples131 (j + 1) M with hT
  set U := T.biUnion (fun ν => (opf (N - tuplePower131 ν)).powerset) with hU
  set U' := U.filter (fun s => xi (∏ p ∈ s, p) ≤ M) with hU'
  have hUs : ∀ s ∈ U, ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro s hs p hp
    rw [hU, Finset.mem_biUnion] at hs
    obtain ⟨ν, -, hsν⟩ := hs
    exact ⟨(opf_spec (mem_powerset.1 hsν hp)).1, (opf_spec (mem_powerset.1 hsν hp)).2.1⟩
  have hinj : ∀ a ∈ U', ∀ b ∈ U', ∏ p ∈ a, p = ∏ p ∈ b, p → a = b := by
    intro a ha b hb hab
    have h1 : Nat.primeFactors (∏ p ∈ a, p) = a :=
      primeFactors_prod_of_primes218 fun p hp => (hUs a (mem_filter.1 ha).1 p hp).1
    have h2 : Nat.primeFactors (∏ p ∈ b, p) = b :=
      primeFactors_prod_of_primes218 fun p hp => (hUs b (mem_filter.1 hb).1 p hp).1
    rw [← h1, ← h2, hab]
  rw [← Finset.sum_image hinj]
  refine Finset.sum_subset ?_ ?_
  · -- the occurring moduli lie below `2^M + 1`
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨s, hs, rfl⟩ := hd
    obtain ⟨hsU, hsxi⟩ := mem_filter.1 hs
    obtain ⟨hos, -, -⟩ := set_facts (fun p hp => hUs s hsU p hp)
    rw [mem_filter, mem_range]
    refine ⟨?_, hsxi⟩
    have h := d_le_two_pow218 hos.2.1 hos.1 hsxi
    omega
  · -- a modulus that occurs in the series but not in `U` contributes nothing
    intro d hd hnot
    rw [mem_filter, mem_range] at hd
    obtain ⟨-, hdxi⟩ := hd
    unfold Ckterm
    split_ifs with hOS
    · have hz : jcount d j N = 0 := by
        by_contra hne
        obtain ⟨ν, hνT, hνdvd⟩ :=
          jcount_pos_mem218 (d := d) (j := j) (M := M) (N := N) hdxi hle (Nat.pos_of_ne_zero hne)
        have hn0 : N - tuplePower131 ν ≠ 0 := (hpos ν hνT).ne'
        have hsU : d.primeFactors ∈ U := by
          rw [hU, Finset.mem_biUnion]
          refine ⟨ν, hνT, mem_powerset.2 ?_⟩
          intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hpd : p ∣ N - tuplePower131 ν :=
            (Nat.dvd_of_mem_primeFactors hp).trans hνdvd
          refine mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hpp, hpd, hn0⟩, ?_⟩
          have hne2 : p ≠ 2 := by
            rintro rfl
            exact (Nat.not_even_iff_odd.mpr hOS.2.1)
              (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
          have := hpp.two_le
          omega
        have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hOS.2.2
        have hmemS : xi (∏ p ∈ d.primeFactors, p) ≤ M := by rw [hprod]; exact hdxi
        exact hnot (mem_image.2 ⟨d.primeFactors, mem_filter.2 ⟨hsU, hmemS⟩, hprod⟩)
      have hji : j + 1 - 1 = j := by omega
      rw [hji, hz]
      simp
    · rfl


/-! ## 3. The large-period region `ξ(d) > M` of the divisor sum

A modulus of period larger than the exponent cutoff `M` is hit at most once per `k` coordinates:
two exponents `a, a' ∈ [1, M]` that both solve `d ∣ N - M_ν - 2^{a}` would force
`ξ(d) ∣ |a - a'| < ξ(d)`. This is step 3 of the split of the divisor sum in display 21, the one
piece that does not need the per-modulus `jcount` comparison. -/

/-- A tuple of exponents of length `k + 1` is its initial segment together with its last entry. -/
private lemma tuplePower_split218 (k : ℕ) (ν : Fin (k + 1) → ℕ) :
    tuplePower131 ν = (∑ i : Fin k, 2 ^ ν (Fin.castSucc i)) + 2 ^ ν (Fin.last k) := by
  unfold tuplePower131
  exact Fin.sum_univ_castSucc _

/-- Transport a ℤ-divisibility of `2^n - 2^m` to `ℕ`. -/
private lemma int_dvd_two_pow_sub218 {d m n : ℕ} (h : 2 ^ m ≤ 2 ^ n)
    (hd : (d : ℤ) ∣ ((2 : ℤ) ^ n - (2 : ℤ) ^ m)) : d ∣ 2 ^ n - 2 ^ m := by
  have hcast : ((2 ^ n - 2 ^ m : ℕ) : ℤ) = ((2 : ℤ) ^ n - (2 : ℤ) ^ m) := by
    rw [Nat.cast_sub h]
    push_cast
    ring
  have : ((d : ℕ) : ℤ) ∣ ((2 ^ n - 2 ^ m : ℕ) : ℤ) := by
    rw [hcast]
    exact hd
  exact_mod_cast this

/-- The initial segment of an exponent tuple of length `k + 1` is an exponent tuple of length `k`. -/
private lemma init_mem_exponentTuples218 {k M : ℕ} {ν : Fin (k + 1) → ℕ}
    (hν : ν ∈ exponentTuples131 (k + 1) M) : Fin.init ν ∈ exponentTuples131 k M := by
  rw [exponentTuples131, Fintype.mem_piFinset] at hν ⊢
  intro i
  exact hν i.castSucc

/-- **Region `ξ(d) > M`**: at most `M^k` exponent tuples make the odd modulus `d = ∏ s`
divide the shifted argument, where `M < ξ(d)` and `M ≥ 1`. -/
private lemma tuple_count_xi_large218 {k M N : ℕ} (hM : 1 ≤ M) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (hxi : M < xi (∏ p ∈ s, p))
    (hle : ∀ ν ∈ exponentTuples131 (k + 1) M, tuplePower131 ν ≤ N)
    (hlt : ∀ ν ∈ exponentTuples131 (k + 1) M, tuplePower131 ν < N) :
    #{ν ∈ exponentTuples131 (k + 1) M |
        s ∈ (opf (N - tuplePower131 ν)).powerset} ≤ M ^ k := by
  classical
  set d : ℕ := ∏ p ∈ s, p with hd
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hs p hp).1.ne_zero
  have hdodd : Odd d := by
    rw [hd]
    refine Finset.prod_induction (fun p => p) Odd (fun x y hx hy => hx.mul hy) odd_one
      fun p hp => ?_
    exact (hs p hp).1.odd_of_ne_two (by have := (hs p hp).2; omega)
  set T := exponentTuples131 (k + 1) M with hT
  set V := T.filter (fun ν => s ∈ (opf (N - tuplePower131 ν)).powerset) with hV
  have hVT : ∀ ν ∈ V, ν ∈ T := fun ν hν => (mem_filter.1 hν).1
  have hbnd : ∀ ν ∈ V, 1 ≤ ν (Fin.last k) ∧ ν (Fin.last k) ≤ M := by
    intro ν hν
    have hνT := hVT ν hν
    rw [hT, exponentTuples131, Fintype.mem_piFinset] at hνT
    exact mem_Icc.1 (hνT (Fin.last k))
  -- every member of `V` satisfies the divisibility, split at the last coordinate
  have hdvd : ∀ ν ∈ V, (d : ℤ) ∣ ((N : ℤ) - ((∑ i : Fin k, (2 : ℤ) ^ ν (Fin.castSucc i)) +
      (2 : ℤ) ^ ν (Fin.last k))) := by
    intro ν hν
    rw [hV, mem_filter] at hν
    obtain ⟨hνT, hνs⟩ := hν
    have hn0 : N - tuplePower131 ν ≠ 0 := by have := hlt ν hνT; omega
    have hdd : d ∣ N - tuplePower131 ν := prod_dvd_of_subset hn0 (mem_powerset.1 hνs)
    have h1 : ((d : ℕ) : ℤ) ∣ ((N - tuplePower131 ν : ℕ) : ℤ) := by exact_mod_cast hdd
    have h2 : ((tuplePower131 ν : ℕ) : ℤ) =
        (∑ i : Fin k, (2 : ℤ) ^ ν (Fin.castSucc i)) + (2 : ℤ) ^ ν (Fin.last k) := by
      rw [tuplePower_split218]; push_cast; rfl
    rw [Nat.cast_sub (hle ν hνT), h2] at h1
    exact h1
  have hinj : ∀ a ∈ V, ∀ b ∈ V, Fin.init a = Fin.init b → a = b := by
    intro a ha b hb hab
    have hIa := hdvd a ha
    have hIb := hdvd b hb
    -- the initial segments have the same sum of powers
    have hsum : (∑ i : Fin k, (2 : ℤ) ^ a (Fin.castSucc i)) =
        (∑ i : Fin k, (2 : ℤ) ^ b (Fin.castSucc i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have : Fin.init a i = Fin.init b i := by rw [hab]
      exact congrArg (fun m => (2 : ℤ) ^ m) this
    rw [hsum] at hIa
    have hdiff : (d : ℤ) ∣ ((2 : ℤ) ^ b (Fin.last k) - (2 : ℤ) ^ a (Fin.last k)) := by
      have := dvd_sub hIa hIb
      convert this using 1
      ring
    -- bounds on the last coordinates
    obtain ⟨ha1, haM⟩ := hbnd a ha
    obtain ⟨hb1, hbM⟩ := hbnd b hb
    have hlast : a (Fin.last k) = b (Fin.last k) := by
      rcases le_total (a (Fin.last k)) (b (Fin.last k)) with h | h
      · rcases Nat.eq_or_lt_of_le h with heq | hlt'
        · exact heq
        · exfalso
          -- `d ∣ 2^{a} * (2^{b-a} - 1)` with `d` odd gives `ξ(d) ∣ b - a`
          have hnat : d ∣ 2 ^ b (Fin.last k) - 2 ^ a (Fin.last k) :=
            int_dvd_two_pow_sub218 (Nat.pow_le_pow_right (by norm_num) h) hdiff
          have hfac : 2 ^ b (Fin.last k) - 2 ^ a (Fin.last k) =
              2 ^ a (Fin.last k) * (2 ^ (b (Fin.last k) - a (Fin.last k)) - 1) := by
            have e : 2 ^ b (Fin.last k) =
                2 ^ a (Fin.last k) * 2 ^ (b (Fin.last k) - a (Fin.last k)) := by
              rw [← pow_add]; congr 1; omega
            rw [e, Nat.mul_sub_one]
          rw [hfac] at hnat
          have hcop : Nat.Coprime d (2 ^ a (Fin.last k)) :=
            Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hdodd)
          have hdl : d ∣ 2 ^ (b (Fin.last k) - a (Fin.last k)) - 1 :=
            hcop.dvd_of_dvd_mul_left hnat
          have hxid : xi d ∣ b (Fin.last k) - a (Fin.last k) :=
            xi_dvd hdodd (Nat.pos_of_ne_zero hd0) hdl
          have hlt2 : b (Fin.last k) - a (Fin.last k) < xi d := by omega
          exact absurd hxid (Nat.not_dvd_of_pos_of_lt (by omega) hlt2)
      · rcases Nat.eq_or_lt_of_le h with heq | hlt'
        · exact heq.symm
        · exfalso
          have hdiff' : (d : ℤ) ∣ ((2 : ℤ) ^ a (Fin.last k) - (2 : ℤ) ^ b (Fin.last k)) := by
            have := dvd_sub hIb hIa
            convert this using 1
            ring
          have hnat : d ∣ 2 ^ a (Fin.last k) - 2 ^ b (Fin.last k) :=
            int_dvd_two_pow_sub218 (Nat.pow_le_pow_right (by norm_num) h) hdiff'
          have hfac : 2 ^ a (Fin.last k) - 2 ^ b (Fin.last k) =
              2 ^ b (Fin.last k) * (2 ^ (a (Fin.last k) - b (Fin.last k)) - 1) := by
            have e : 2 ^ a (Fin.last k) =
                2 ^ b (Fin.last k) * 2 ^ (a (Fin.last k) - b (Fin.last k)) := by
              rw [← pow_add]; congr 1; omega
            rw [e, Nat.mul_sub_one]
          rw [hfac] at hnat
          have hcop : Nat.Coprime d (2 ^ b (Fin.last k)) :=
            Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hdodd)
          have hdl : d ∣ 2 ^ (a (Fin.last k) - b (Fin.last k)) - 1 :=
            hcop.dvd_of_dvd_mul_left hnat
          have hxid : xi d ∣ a (Fin.last k) - b (Fin.last k) :=
            xi_dvd hdodd (Nat.pos_of_ne_zero hd0) hdl
          have hlt2 : a (Fin.last k) - b (Fin.last k) < xi d := by omega
          exact absurd hxid (Nat.not_dvd_of_pos_of_lt (by omega) hlt2)
    calc a = Fin.snoc (Fin.init a) (a (Fin.last k)) := (Fin.snoc_init_self a).symm
      _ = Fin.snoc (Fin.init b) (b (Fin.last k)) := by rw [hab, hlast]
      _ = b := Fin.snoc_init_self b
  calc V.card = (V.image Fin.init).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (exponentTuples131 k M).card := by
        refine Finset.card_le_card fun x hx => ?_
        obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
        exact init_mem_exponentTuples218 (hVT ν hν)
    _ = M ^ k := exponentTuples_card131 k M

/-! ## 4. Auxiliary asymptotics for the final estimate

`M = ⌊L - √L⌋₊` is the exponent cutoff, so `M ~ L`, `1 ≤ M`, and any fixed power of `log` is
`o(M)`. These are all the facts the epsilon bookkeeping of the singular series average needs. -/

/-- `Lg X → ∞`. -/
private lemma eventually_Lg_ge218 (c : ℝ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → c ≤ Lg X := by
  have ht : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  exact (ht.eventually_ge_atTop c).exists_forall_of_atTop

/-- `M = ⌊L - √L⌋₊` satisfies `1 ≤ M`, `M ≤ L` and `L/2 ≤ M` once `L ≥ 9`. -/
private lemma M_bounds218 {X : ℕ} (hL : 16 ≤ Lg X) :
    1 ≤ ⌊Lg X - Real.sqrt (Lg X)⌋₊ ∧ (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ≤ Lg X ∧
      Lg X / 2 ≤ (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) := by
  set L := Lg X with hLdef
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hsq : Real.sqrt L ≤ L := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have ht0 : 0 ≤ L - Real.sqrt L := by linarith
  set M := ⌊L - Real.sqrt L⌋₊ with hM
  have hfl : (M : ℝ) ≤ L - Real.sqrt L := Nat.floor_le ht0
  have hlt : L - Real.sqrt L - 1 < (M : ℝ) := by
    have := Nat.lt_floor_add_one (L - Real.sqrt L)
    linarith
  have hsl : Real.sqrt L ≤ L / 4 := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hsnn : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg L
  refine ⟨?_, by linarith, by linarith⟩
  have h1 : (1 : ℝ) ≤ (M : ℝ) := by linarith
  exact_mod_cast h1

/-- `log(L + 2) ≤ c M` for every `c > 0` and all large `X`. -/
private lemma log_le_M218 (c : ℝ) (hc : 0 < c) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      Real.log (Lg X + 2) ≤ c * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) := by
  obtain ⟨X₁, hX₁⟩ := eventually_Lg_ge218 (max 16 (max ((8 / c) ^ 2) 4))
  refine ⟨X₁, fun X hX => ?_⟩
  have hX' := hX₁ X hX
  have hL : 16 ≤ Lg X := le_trans (le_max_left _ _) hX'
  have hLc : (8 / c) ^ 2 ≤ Lg X :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX')
  have hL4 : (4 : ℝ) ≤ Lg X :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX')
  obtain ⟨-, hML, hLM⟩ := M_bounds218 hL
  have hL1 : (1 : ℝ) ≤ Lg X := by linarith
  -- `log (L + 2) ≤ 2 log L` since `L + 2 ≤ L ^ 2`
  have hsq : Real.log (Lg X + 2) ≤ 2 * Real.log (Lg X) := by
    have h1 : Real.log (Lg X + 2) ≤ Real.log (Lg X ^ 2) := by
      refine Real.log_le_log (by linarith) ?_
      nlinarith
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  -- `log L ≤ 2 √L`
  have hroot : Real.log (Lg X) ≤ 2 * Real.sqrt (Lg X) := by
    have h := Real.log_le_rpow_div (x := Lg X) (by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    have h2 : Real.sqrt (Lg X) / (1 / 2) = 2 * Real.sqrt (Lg X) := by ring
    linarith [h, h2]
  have hc8 : 8 / c ≤ Real.sqrt (Lg X) := by
    calc 8 / c = Real.sqrt ((8 / c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Lg X) := Real.sqrt_le_sqrt hLc
  have h8 : 8 ≤ c * Real.sqrt (Lg X) := by
    have h := mul_le_mul_of_nonneg_right hc8 hc.le
    rw [div_mul_cancel₀ _ hc.ne'] at h
    simpa [mul_comm] using h
  have hs1 : 8 * Real.sqrt (Lg X) ≤ c * Lg X := by
    have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ Lg X by linarith)
    nlinarith [h8, Real.sqrt_nonneg (Lg X), hsq2]
  have hfin : 2 * Real.log (Lg X) ≤ c * Lg X / 2 := by linarith
  calc Real.log (Lg X + 2) ≤ 2 * Real.log (Lg X) := hsq
    _ ≤ c * Lg X / 2 := hfin
    _ ≤ c * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith) hc.le

/-- `k 2^M ≤ η X` for every `η > 0` and all large `X`. -/
private lemma tuple_window_eps218 (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (k : ℝ) * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ ≤ η * X := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set c : ℝ := ((k : ℝ) + 1) / η with hcdef
  have hc : 0 < c := div_pos hk hη
  have ht : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Tendsto (fun X : ℕ => Real.exp (Real.log 2 * Real.sqrt (Lg X))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((Real.tendsto_sqrt_atTop.comp ht).const_mul_atTop hlog)
  obtain ⟨X₀, hX₀⟩ := ((ht.eventually_ge_atTop 1).and
    (hs.eventually_ge_atTop c)).exists_forall_of_atTop
  refine ⟨max 1 X₀, fun X hX => ?_⟩
  obtain ⟨hL, hE⟩ := hX₀ X (le_trans (le_max_right _ _) hX)
  have hX1 : (0 : ℝ) < X := by
    have : 1 ≤ X := le_trans (le_max_left _ _) hX
    exact_mod_cast this
  have hsq : Real.sqrt (Lg X) ≤ Lg X :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have ht0 : 0 ≤ Lg X - Real.sqrt (Lg X) := by linarith
  have hfl := Nat.floor_le ht0
  set M := ⌊Lg X - Real.sqrt (Lg X)⌋₊
  have h2M : (2 : ℝ) ^ M ≤ (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hfl
  have hXe : (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) * (2 : ℝ) ^ (Real.sqrt (Lg X)) = X := by
    rw [← Real.rpow_add (by norm_num), sub_add_cancel]
    exact Real.rpow_logb (by norm_num) (by norm_num) hX1
  have hE' : c ≤ (2 : ℝ) ^ (Real.sqrt (Lg X)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    exact hE
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ M := by positivity
  have hq : (0 : ℝ) ≤ (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) := by positivity
  have h1 : (k : ℝ) * (2 : ℝ) ^ M ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ M := by nlinarith
  have h2 : ((k : ℝ) + 1) * (2 : ℝ) ^ M ≤
      ((k : ℝ) + 1) * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) :=
    mul_le_mul_of_nonneg_left h2M hk.le
  have h3 : ((k : ℝ) + 1) * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) =
      c * η * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) := by
    rw [hcdef]
    field_simp
  have h4 : c * η * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) ≤
      (2 : ℝ) ^ (Real.sqrt (Lg X)) * η * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) := by
    refine mul_le_mul_of_nonneg_right ?_ hq
    exact mul_le_mul_of_nonneg_right hE' hη.le
  have hXX : (2 : ℝ) ^ (Real.sqrt (Lg X)) * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) = X := by
    rw [mul_comm]; exact hXe
  have h5 : (2 : ℝ) ^ (Real.sqrt (Lg X)) * η * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) = η * X := by
    rw [show (2 : ℝ) ^ (Real.sqrt (Lg X)) * η * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X))
      = η * ((2 : ℝ) ^ (Real.sqrt (Lg X)) * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X))) by ring, hXX]
  calc (k : ℝ) * (2 : ℝ) ^ M ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ M := h1
    _ ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) := h2
    _ = c * η * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) := h3
    _ ≤ (2 : ℝ) ^ (Real.sqrt (Lg X)) * η * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) := h4
    _ = η * X := h5

/-- The divisor sets occurring in `U` are subsets of the odd primes of `P = ∏ (N - M_ν)`, so
their `W`-weight is bounded by `H P`. This is the `+1` term of `sum_H_le`, summed at once. -/
private lemma sum_W_le_HP218 {k M N : ℕ} (hpos : ∀ ν ∈ exponentTuples131 k M,
    0 < N - tuplePower131 ν) :
    ∑ s ∈ (exponentTuples131 k M).biUnion
        (fun ν => (opf (N - tuplePower131 ν)).powerset), W s ≤
      H (∏ ν ∈ exponentTuples131 k M, (N - tuplePower131 ν)) := by
  classical
  set T := exponentTuples131 k M with hT
  set P : ℕ := ∏ ν ∈ T, (N - tuplePower131 ν) with hP
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 fun ν hν => (hpos ν hν).ne'
  have hsub : T.biUnion (fun ν => (opf (N - tuplePower131 ν)).powerset) ⊆ (opf P).powerset := by
    intro s hs
    rw [Finset.mem_biUnion] at hs
    obtain ⟨ν, hν, hsν⟩ := hs
    rw [mem_powerset] at hsν ⊢
    refine Subset.trans hsν ?_
    exact opf_mono (Finset.dvd_prod_of_mem _ hν) hP0
  rw [H_eq_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun s hs _ => W_nonneg fun p hp => ?_
  exact (opf_spec (mem_powerset.1 hs hp)).2.1

/-- **The head region `ξ(d_s) ≤ K ≤ M` is the finite part of (23).** Pointwise form: the count
`c_s` is `M^k ξ^{-k} j(d_s,k-1,N)` up to `k (2M)^{k-1}`, with the weight `W s = f(d_s)` already
absorbed into `Ckterm`. -/
private lemma head_pointwise218 {k M K N : ℕ} (hk : 1 ≤ k) (hKM : K ≤ M)
    (hle : ∀ ν ∈ exponentTuples131 k M, tuplePower131 ν ≤ N)
    (hpos : ∀ ν ∈ exponentTuples131 k M, 0 < N - tuplePower131 ν)
    {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (hxi : xi (∏ p ∈ s, p) ≤ K) :
    |(#{ν ∈ exponentTuples131 k M |
        s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s
      - (M : ℝ) ^ k * Ckterm k N (∏ p ∈ s, p)| ≤
      W s * ((k : ℝ) * (2 * (M : ℝ)) ^ (k - 1)) := by
  classical
  obtain ⟨hos, -, hfd⟩ := set_facts hs
  have hdodd : Odd (∏ p ∈ s, p) := hos.2.1
  have hξ1 : 1 ≤ xi (∏ p ∈ s, p) := (xi_spec hdodd).1
  have hξpos : (0 : ℝ) < (xi (∏ p ∈ s, p) : ℝ) := by exact_mod_cast hξ1
  have hξM : xi (∏ p ∈ s, p) ≤ M := le_trans hxi hKM
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have h1 : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_trans hξ1 hξM)
    exact_mod_cast h1
  -- (1) the count is the modular tuple count
  have hcnt : (#{ν ∈ exponentTuples131 k M |
      s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) =
      (residueTupleCount131 (∏ p ∈ s, p) k M N : ℝ) := by
    rw [count_eq_residue218 hle hpos hs]
  -- (2) the per-modulus error of display 20
  have hbje := block_jcount_error131 (d := ∏ p ∈ s, p) hdodd (k - 1) M N
  have hk1 : k - 1 + 1 = k := by omega
  have hkk : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    rw [← hk1]; push_cast; ring
  rw [hk1] at hbje
  simp only [hkk] at hbje
  -- (3) multiply by the nonnegative weight
  have hWs : 0 ≤ W s := by
    rw [← hfd]
    exact fd_nonneg hos
  have hprod : ((residueTupleCount131 (∏ p ∈ s, p) k M N : ℝ) -
      (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) *
        ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ)) ^ k) * W s =
      (residueTupleCount131 (∏ p ∈ s, p) k M N : ℝ) * W s -
        (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) *
          ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ)) ^ k * W s := by ring
  have hmul : |(residueTupleCount131 (∏ p ∈ s, p) k M N : ℝ) * W s -
      (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) *
        ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ)) ^ k * W s| ≤
      W s * ((jcount (∏ p ∈ s, p) (k - 1) N : ℝ) * (k : ℝ) *
        ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ^ (k - 1)) := by
    calc |(residueTupleCount131 (∏ p ∈ s, p) k M N : ℝ) * W s -
        (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) *
          ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ)) ^ k * W s|
        = |((residueTupleCount131 (∏ p ∈ s, p) k M N : ℝ) -
          (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) *
            ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ)) ^ k) * W s| := by rw [hprod]
      _ = |(residueTupleCount131 (∏ p ∈ s, p) k M N : ℝ) -
          (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) *
            ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ)) ^ k| * W s := by
          rw [abs_mul, abs_of_nonneg hWs]
      _ ≤ (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) * (k : ℝ) *
            ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ^ (k - 1) * W s :=
          mul_le_mul_of_nonneg_right hbje hWs
      _ = W s * ((jcount (∏ p ∈ s, p) (k - 1) N : ℝ) * (k : ℝ) *
            ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ^ (k - 1)) := by ring
  -- (4) the weight-free bound `j · k · (⌊M/ξ⌋+1)^{k-1} ≤ k (2M)^{k-1}`
  have herr : (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) * (k : ℝ) *
      ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ^ (k - 1) ≤
      (k : ℝ) * (2 * (M : ℝ)) ^ (k - 1) := by
    have hj : (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) ≤ ((xi (∏ p ∈ s, p) : ℝ)) ^ (k - 1) := by
      have := jcount_le hdodd (k - 1) N
      exact_mod_cast this
    -- `⌊M/ξ⌋ + 1 ≤ 2 M / ξ`
    have hq1 : ((M / xi (∏ p ∈ s, p) : ℕ) : ℝ) ≤ (M : ℝ) / (xi (∏ p ∈ s, p) : ℝ) :=
      Nat.cast_div_le
    have hq2 : (1 : ℝ) ≤ (M : ℝ) / (xi (∏ p ∈ s, p) : ℝ) := by
      rw [le_div_iff₀ hξpos]
      simpa using (Nat.cast_le.mpr hξM : (xi (∏ p ∈ s, p) : ℝ) ≤ (M : ℝ))
    have hq : ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ≤ 2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ)) := by
      push_cast
      linarith
    have hq0 : (0 : ℝ) ≤ ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) := by positivity
    have h2M0 : (0 : ℝ) ≤ 2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ)) := by linarith
    have hpw : ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ^ (k - 1) ≤
        (2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ))) ^ (k - 1) :=
      pow_le_pow_left₀ hq0 hq (k - 1)
    have hj0 : (0 : ℝ) ≤ (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) := Nat.cast_nonneg _
    have hjw : (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) *
        ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ^ (k - 1) ≤
        ((xi (∏ p ∈ s, p) : ℝ)) ^ (k - 1) *
          (2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ))) ^ (k - 1) :=
      mul_le_mul hj hpw (by positivity) (by positivity)
    have heq : ((xi (∏ p ∈ s, p) : ℝ)) ^ (k - 1) *
        (2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ))) ^ (k - 1) = (2 * (M : ℝ)) ^ (k - 1) := by
      have h2 : (2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ))) =
          2 * (M : ℝ) / (xi (∏ p ∈ s, p) : ℝ) := by ring
      rw [h2, div_pow]
      field_simp
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    calc (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) * (k : ℝ) *
          ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ^ (k - 1)
        = (k : ℝ) * ((jcount (∏ p ∈ s, p) (k - 1) N : ℝ) *
            ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ^ (k - 1)) := by ring
      _ ≤ (k : ℝ) * (((xi (∏ p ∈ s, p) : ℝ)) ^ (k - 1) *
            (2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ))) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left hjw hk0
      _ = (k : ℝ) * (2 * (M : ℝ)) ^ (k - 1) := by rw [heq]
  -- (5) the main term: `j · (M/ξ)^k · W s = M^k Ckterm`
  have hterm : (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) *
      ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ)) ^ k * W s =
      (M : ℝ) ^ k * Ckterm k N (∏ p ∈ s, p) := by
    unfold Ckterm
    rw [if_pos hos, ← hfd, div_pow]
    have hx0 : (xi (∏ p ∈ s, p) : ℝ) ≠ 0 := hξpos.ne'
    field_simp
  rw [hcnt]
  rw [hterm] at hmul
  exact hmul.trans (mul_le_mul_of_nonneg_left herr hWs)

/-- Every member of `U` is a set of odd primes. -/
private lemma mem_U_spec218 {k M N : ℕ} {s : Finset ℕ}
    (hs : s ∈ (exponentTuples131 k M).biUnion
      (fun ν => (opf (N - tuplePower131 ν)).powerset)) :
    ∀ p ∈ s, p.Prime ∧ 2 < p := by
  classical
  rw [Finset.mem_biUnion] at hs
  obtain ⟨ν, -, hsν⟩ := hs
  exact fun p hp => ⟨(opf_spec (mem_powerset.1 hsν hp)).1,
    (opf_spec (mem_powerset.1 hsν hp)).2.1⟩

/-- **The head region `ξ(d_s) ≤ K`**, summed: the weighted count is `M^k` times the finite part
of (23) over those moduli, up to `k (2M)^{k-1}` times the total weight. -/
private lemma sum_head218 {k M K N : ℕ} (hk : 1 ≤ k) (hKM : K ≤ M)
    (hle : ∀ ν ∈ exponentTuples131 k M, tuplePower131 ν ≤ N)
    (hpos : ∀ ν ∈ exponentTuples131 k M, 0 < N - tuplePower131 ν) :
    |∑ s ∈ ((exponentTuples131 k M).biUnion
          (fun ν => (opf (N - tuplePower131 ν)).powerset)).filter
          (fun s => xi (∏ p ∈ s, p) ≤ K),
        (#{ν ∈ exponentTuples131 k M |
          s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s
      - (M : ℝ) ^ k * ∑ s ∈ ((exponentTuples131 k M).biUnion
          (fun ν => (opf (N - tuplePower131 ν)).powerset)).filter
          (fun s => xi (∏ p ∈ s, p) ≤ K), Ckterm k N (∏ p ∈ s, p)| ≤
      (k : ℝ) * (2 * (M : ℝ)) ^ (k - 1) *
        ∑ s ∈ ((exponentTuples131 k M).biUnion
          (fun ν => (opf (N - tuplePower131 ν)).powerset)).filter
          (fun s => xi (∏ p ∈ s, p) ≤ K), W s := by
  classical
  set U := (exponentTuples131 k M).biUnion
    (fun ν => (opf (N - tuplePower131 ν)).powerset) with hU
  set Uf := U.filter (fun s => xi (∏ p ∈ s, p) ≤ K) with hUf
  have hodd : ∀ s ∈ U, ∀ p ∈ s, p.Prime ∧ 2 < p := fun s hs => mem_U_spec218 hs
  have hfac : (M : ℝ) ^ k * ∑ s ∈ Uf, Ckterm k N (∏ p ∈ s, p) =
      ∑ s ∈ Uf, (M : ℝ) ^ k * Ckterm k N (∏ p ∈ s, p) := Finset.mul_sum ..
  have hsplit : ∑ s ∈ Uf, (#{ν ∈ exponentTuples131 k M |
        s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s -
      (M : ℝ) ^ k * ∑ s ∈ Uf, Ckterm k N (∏ p ∈ s, p) =
      ∑ s ∈ Uf, ((#{ν ∈ exponentTuples131 k M |
          s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s -
        (M : ℝ) ^ k * Ckterm k N (∏ p ∈ s, p)) := by
    rw [hfac, ← Finset.sum_sub_distrib]
  rw [hsplit]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hpw : ∀ s ∈ Uf, |(#{ν ∈ exponentTuples131 k M |
        s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s -
        (M : ℝ) ^ k * Ckterm k N (∏ p ∈ s, p)| ≤
      W s * ((k : ℝ) * (2 * (M : ℝ)) ^ (k - 1)) :=
    fun s hs => head_pointwise218 hk hKM hle hpos (hodd s (mem_filter.1 hs).1)
      (mem_filter.1 hs).2
  calc ∑ s ∈ Uf, |(#{ν ∈ exponentTuples131 k M |
        s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s -
        (M : ℝ) ^ k * Ckterm k N (∏ p ∈ s, p)|
      ≤ ∑ s ∈ Uf, W s * ((k : ℝ) * (2 * (M : ℝ)) ^ (k - 1)) :=
        Finset.sum_le_sum hpw
    _ = (k : ℝ) * (2 * (M : ℝ)) ^ (k - 1) * ∑ s ∈ Uf, W s := by
        rw [← Finset.sum_mul, mul_comm]

/-- Beyond `2^K + 1`, a modulus with `ξ(d) ≤ K` contributes nothing to (23). -/
private lemma Ckterm_eq_zero218 {k K N d : ℕ} (hd : 2 ^ K + 1 ≤ d) (hxi : xi d ≤ K) :
    Ckterm k N d = 0 := by
  by_cases hos : OddSqf d
  · exfalso
    have h := d_le_two_pow218 hos.2.1 hos.1 hxi
    omega
  · unfold Ckterm
    rw [if_neg hos]

/-- **Displays 20 to 23, the truncation step.** `Ck k N` minus its finite part over the moduli
with `ξ(d) ≤ K` is at most the tail of the series (26) with `ξ(d) > K`. -/
private lemma Ck_sub_finite218 (k K N : ℕ) (hk : 1 ≤ k) :
    |Ck k N - ∑ d ∈ (Finset.range (2 ^ K + 1)).filter (fun d => xi d ≤ K),
        Ckterm k N d| ≤
      ∑' d : ℕ, (if K < xi d then seriesTerm d else 0) := by
  classical
  set D := 2 ^ K + 1 with hD
  have hDval : D = 2 ^ K + 1 := hD
  have hgsum : Summable (fun d => Ckterm k N d) := Ck_summable hk N
  have hgnn : ∀ d, 0 ≤ Ckterm k N d := fun d => Ckterm_nonneg k N d
  have hle' : ∀ d : ℕ, (if K < xi d then seriesTerm d else 0) ≤ seriesTerm d := by
    intro d
    by_cases h : K < xi d
    · rw [if_pos h]
    · rw [if_neg h]; exact seriesTerm_nonneg d
  have htnn : ∀ d, 0 ≤ (if K < xi d then seriesTerm d else 0) := by
    intro d
    by_cases h : K < xi d
    · rw [if_pos h]; exact seriesTerm_nonneg d
    · rw [if_neg h]
  have htsum : Summable (fun d => if K < xi d then seriesTerm d else 0) :=
    Summable.of_nonneg_of_le htnn hle' lemma61_proved
  -- (1) split `Ck` at `D`
  have hCk : Ck k N = ∑ d ∈ Finset.range D, Ckterm k N d +
      ∑' j : ℕ, Ckterm k N (j + D) :=
    (hgsum.sum_add_tsum_nat_add D).symm
  -- (2) the finite part as a sum of indicators
  have hF : ∑ d ∈ (Finset.range D).filter (fun d => xi d ≤ K), Ckterm k N d =
      ∑ d ∈ Finset.range D, (if xi d ≤ K then Ckterm k N d else 0) := Finset.sum_filter ..
  -- (3) the difference
  have hdiff_fin : ∑ d ∈ Finset.range D, Ckterm k N d -
      ∑ d ∈ Finset.range D, (if xi d ≤ K then Ckterm k N d else 0) =
      ∑ d ∈ Finset.range D, (if K < xi d then Ckterm k N d else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : xi d ≤ K
    · rw [if_pos h, if_neg (by omega : ¬ K < xi d)]; ring
    · rw [if_neg h, if_pos (by omega : K < xi d)]; ring
  have hdiff : Ck k N - ∑ d ∈ (Finset.range D).filter (fun d => xi d ≤ K), Ckterm k N d =
      ∑ d ∈ Finset.range D, (if K < xi d then Ckterm k N d else 0) +
        ∑' j : ℕ, Ckterm k N (j + D) := by
    rw [hCk, hF]
    calc (∑ d ∈ Finset.range D, Ckterm k N d) + (∑' j : ℕ, Ckterm k N (j + D)) -
          (∑ d ∈ Finset.range D, (if xi d ≤ K then Ckterm k N d else 0))
        = ((∑ d ∈ Finset.range D, Ckterm k N d) -
            (∑ d ∈ Finset.range D, (if xi d ≤ K then Ckterm k N d else 0))) +
          (∑' j : ℕ, Ckterm k N (j + D)) := by ring
      _ = _ := by rw [hdiff_fin]
  have hfin0 : (0 : ℝ) ≤ ∑ d ∈ Finset.range D, (if K < xi d then Ckterm k N d else 0) :=
    Finset.sum_nonneg fun d _ => by
      by_cases h : K < xi d
      · rw [if_pos h]; exact hgnn d
      · rw [if_neg h]
  have hfar0 : (0 : ℝ) ≤ ∑' j : ℕ, Ckterm k N (j + D) := tsum_nonneg fun j => hgnn _
  rw [hdiff, abs_of_nonneg (by linarith)]
  -- (4) bound the finite part by a finite sub-sum of the tail
  have hfin : ∑ d ∈ Finset.range D, (if K < xi d then Ckterm k N d else 0) ≤
      ∑ d ∈ Finset.range D, (if K < xi d then seriesTerm d else 0) := by
    refine Finset.sum_le_sum fun d _ => ?_
    by_cases h : K < xi d
    · rw [if_pos h, if_pos h]; exact Ckterm_le hk N d
    · rw [if_neg h, if_neg h]
  have hfin2 : ∑ d ∈ Finset.range D, (if K < xi d then seriesTerm d else 0) ≤
      ∑' d : ℕ, (if K < xi d then seriesTerm d else 0) :=
    htsum.sum_le_tsum _ fun d _ => htnn d
  -- (5) the far tail, using that `ξ(d) ≤ K` forces `Ckterm = 0` there
  have hfar : ∑' j : ℕ, Ckterm k N (j + D) ≤
      ∑' j : ℕ, (if K < xi (j + D) then seriesTerm (j + D) else 0) := by
    have hpw : ∀ j : ℕ, Ckterm k N (j + D) ≤
        (if K < xi (j + D) then seriesTerm (j + D) else 0) := by
      intro j
      by_cases h : K < xi (j + D)
      · rw [if_pos h]; exact Ckterm_le hk N (j + D)
      · rw [if_neg h]
        exact le_of_eq (Ckterm_eq_zero218 (show 2 ^ K + 1 ≤ j + D by rw [hD]; omega)
          (by omega))
    exact Summable.tsum_le_tsum hpw
      (hgsum.comp_injective (add_left_injective D))
      (htsum.comp_injective (add_left_injective D))
  have hFF : (∑ d ∈ Finset.range D, (if K < xi d then seriesTerm d else 0)) +
      (∑' j : ℕ, (if K < xi (j + D) then seriesTerm (j + D) else 0)) =
      ∑' d : ℕ, (if K < xi d then seriesTerm d else 0) :=
    htsum.sum_add_tsum_nat_add D
  linarith

/-- `k - 1 + 1 = k` for `k ≥ 1`. -/
private lemma kk_pred_succ218 {k : ℕ} (hk : 1 ≤ k) : k - 1 + 1 = k := by omega

/-- On `U` the map `s ↦ ∏_{p ∈ s} p` is injective. -/
private lemma prod_inj_on_U218 {k M N : ℕ} {a b : Finset ℕ}
    (ha : a ∈ (exponentTuples131 k M).biUnion
      (fun ν => (opf (N - tuplePower131 ν)).powerset))
    (hb : b ∈ (exponentTuples131 k M).biUnion
      (fun ν => (opf (N - tuplePower131 ν)).powerset))
    (hab : ∏ p ∈ a, p = ∏ p ∈ b, p) : a = b := by
  classical
  have h1 : Nat.primeFactors (∏ p ∈ a, p) = a :=
    primeFactors_prod_of_primes218 fun p hp => (mem_U_spec218 ha p hp).1
  have h2 : Nat.primeFactors (∏ p ∈ b, p) = b :=
    primeFactors_prod_of_primes218 fun p hp => (mem_U_spec218 hb p hp).1
  rw [← h1, ← h2, hab]

/-- **The middle region `K < ξ(d_s) ≤ M`**: a modulus whose period exceeds `K` carries at most
`(2M)^k` times its own series term. -/
private lemma middle_pointwise218 {k M K N : ℕ} (hk : 1 ≤ k)
    (hle : ∀ ν ∈ exponentTuples131 k M, tuplePower131 ν ≤ N)
    (hpos : ∀ ν ∈ exponentTuples131 k M, 0 < N - tuplePower131 ν)
    {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (hK : K < xi (∏ p ∈ s, p)) (hM : xi (∏ p ∈ s, p) ≤ M) :
    (#{ν ∈ exponentTuples131 k M |
        s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s ≤
      (2 * (M : ℝ)) ^ k * seriesTerm (∏ p ∈ s, p) := by
  classical
  obtain ⟨hos, -, hfd⟩ := set_facts hs
  have hdodd : Odd (∏ p ∈ s, p) := hos.2.1
  have hξ1 : 1 ≤ xi (∏ p ∈ s, p) := (xi_spec hdodd).1
  have hξpos : (0 : ℝ) < (xi (∏ p ∈ s, p) : ℝ) := by exact_mod_cast hξ1
  have hξMpos : (0 : ℝ) < (M : ℝ) := by
    have h1 : 0 < M := lt_of_lt_of_le (by omega) hM
    exact_mod_cast h1
  have hcnt : (#{ν ∈ exponentTuples131 k M |
      s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) =
      (residueTupleCount131 (∏ p ∈ s, p) k M N : ℝ) := by
    rw [count_eq_residue218 hle hpos hs]
  have hbnd := (block_jcount_bounds131 (d := ∏ p ∈ s, p) hdodd (k - 1) M N).2
  rw [kk_pred_succ218 hk] at hbnd
  have hbndR : (residueTupleCount131 (∏ p ∈ s, p) k M N : ℝ) ≤
      ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ^ k *
        (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) := by
    have h1 : ((residueTupleCount131 (∏ p ∈ s, p) k M N : ℕ) : ℝ) ≤
        (((M / xi (∏ p ∈ s, p) + 1) ^ k * jcount (∏ p ∈ s, p) (k - 1) N : ℕ) : ℝ) := by
      exact_mod_cast hbnd
    push_cast at h1
    exact h1
  have hj : (jcount (∏ p ∈ s, p) (k - 1) N : ℝ) ≤ ((xi (∏ p ∈ s, p) : ℝ)) ^ (k - 1) := by
    have := jcount_le hdodd (k - 1) N
    exact_mod_cast this
  have hq1 : ((M / xi (∏ p ∈ s, p) : ℕ) : ℝ) ≤ (M : ℝ) / (xi (∏ p ∈ s, p) : ℝ) :=
    Nat.cast_div_le
  have hq2 : (1 : ℝ) ≤ (M : ℝ) / (xi (∏ p ∈ s, p) : ℝ) := by
    rw [le_div_iff₀ hξpos]
    simpa using (Nat.cast_le.mpr hM : (xi (∏ p ∈ s, p) : ℝ) ≤ (M : ℝ))
  have hq : ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ≤
      2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ)) := by
    push_cast
    linarith
  have hq0 : (0 : ℝ) ≤ ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) := by positivity
  have h2M0 : (0 : ℝ) ≤ 2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ)) := by linarith
  have hpw : ((M / xi (∏ p ∈ s, p) : ℕ) + 1 : ℝ) ^ k ≤
      (2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ))) ^ k := pow_le_pow_left₀ hq0 hq k
  -- combine: `c_s ≤ (2M/ξ)^k ξ^{k-1} = 2^k M^k / ξ`
  have hstep1 : (residueTupleCount131 (∏ p ∈ s, p) k M N : ℝ) ≤
      (2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ))) ^ k * ((xi (∏ p ∈ s, p) : ℝ)) ^ (k - 1) := by
    refine hbndR.trans ?_
    exact mul_le_mul hpw hj (Nat.cast_nonneg _) (by positivity)
  have hstep2 : (2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ))) ^ k *
      ((xi (∏ p ∈ s, p) : ℝ)) ^ (k - 1) = (2 * (M : ℝ)) ^ k / (xi (∏ p ∈ s, p) : ℝ) := by
    have h2 : (2 * ((M : ℝ) / (xi (∏ p ∈ s, p) : ℝ))) =
        2 * (M : ℝ) / (xi (∏ p ∈ s, p) : ℝ) := by ring
    rw [h2, div_pow]
    have hk1 : ((xi (∏ p ∈ s, p) : ℝ)) ^ k =
        ((xi (∏ p ∈ s, p) : ℝ)) ^ (k - 1) * (xi (∏ p ∈ s, p) : ℝ) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hk1]
    field_simp
  have hW : W s = fd (∏ p ∈ s, p) := hfd.symm
  have hser : seriesTerm (∏ p ∈ s, p) = fd (∏ p ∈ s, p) / (xi (∏ p ∈ s, p) : ℝ) := by
    unfold seriesTerm
    rw [if_pos hos]
  have hWs : 0 ≤ W s := by
    rw [hW]; exact fd_nonneg hos
  have hfin : (#{ν ∈ exponentTuples131 k M |
      s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s ≤
      (2 * (M : ℝ)) ^ k * seriesTerm (∏ p ∈ s, p) := by
    rw [hcnt]
    calc (residueTupleCount131 (∏ p ∈ s, p) k M N : ℝ) * W s
        ≤ ((2 * (M : ℝ)) ^ k / (xi (∏ p ∈ s, p) : ℝ)) * W s :=
          mul_le_mul_of_nonneg_right (hstep1.trans (le_of_eq hstep2)) hWs
      _ = (2 * (M : ℝ)) ^ k * seriesTerm (∏ p ∈ s, p) := by
          rw [hW, hser]
          field_simp
  exact hfin

/-- **The middle region, summed**: at most `(2M)^k` times the `ξ > K` tail of (26). -/
private lemma sum_middle218 {k M K N : ℕ} (hk : 1 ≤ k)
    (hle : ∀ ν ∈ exponentTuples131 k M, tuplePower131 ν ≤ N)
    (hpos : ∀ ν ∈ exponentTuples131 k M, 0 < N - tuplePower131 ν) :
    ∑ s ∈ ((exponentTuples131 k M).biUnion
          (fun ν => (opf (N - tuplePower131 ν)).powerset)).filter
          (fun s => K < xi (∏ p ∈ s, p) ∧ xi (∏ p ∈ s, p) ≤ M),
        (#{ν ∈ exponentTuples131 k M |
          s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s ≤
      (2 * (M : ℝ)) ^ k * ∑' d : ℕ, (if K < xi d then seriesTerm d else 0) := by
  classical
  set U := (exponentTuples131 k M).biUnion
    (fun ν => (opf (N - tuplePower131 ν)).powerset) with hU
  set Um := U.filter (fun s => K < xi (∏ p ∈ s, p) ∧ xi (∏ p ∈ s, p) ≤ M) with hUm
  have hnn : ∀ d : ℕ, 0 ≤ (if K < xi d then seriesTerm d else 0) := by
    intro d
    by_cases h : K < xi d
    · rw [if_pos h]; exact seriesTerm_nonneg d
    · rw [if_neg h]
  have hle' : ∀ d : ℕ, (if K < xi d then seriesTerm d else 0) ≤ seriesTerm d := by
    intro d
    by_cases h : K < xi d
    · rw [if_pos h]
    · rw [if_neg h]; exact seriesTerm_nonneg d
  have htsum : Summable (fun d => if K < xi d then seriesTerm d else 0) :=
    Summable.of_nonneg_of_le hnn hle' lemma61_proved
  have hpw : ∀ s ∈ Um, (#{ν ∈ exponentTuples131 k M |
        s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s ≤
      (2 * (M : ℝ)) ^ k * (if K < xi (∏ p ∈ s, p) then
        seriesTerm (∏ p ∈ s, p) else 0) := by
    intro s hs
    obtain ⟨hsU, hK, hM⟩ := mem_filter.1 hs
    have hp := middle_pointwise218 hk hle hpos (mem_U_spec218 hsU) hK hM
    have h1 : (if K < xi (∏ p ∈ s, p) then seriesTerm (∏ p ∈ s, p) else 0) =
        seriesTerm (∏ p ∈ s, p) := if_pos hK
    rw [h1]
    exact hp
  calc ∑ s ∈ Um, (#{ν ∈ exponentTuples131 k M |
        s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s
      ≤ ∑ s ∈ Um, (2 * (M : ℝ)) ^ k * (if K < xi (∏ p ∈ s, p) then
          seriesTerm (∏ p ∈ s, p) else 0) := Finset.sum_le_sum hpw
    _ = (2 * (M : ℝ)) ^ k * ∑ s ∈ Um, (if K < xi (∏ p ∈ s, p) then
          seriesTerm (∏ p ∈ s, p) else 0) := (Finset.mul_sum ..).symm
    _ ≤ (2 * (M : ℝ)) ^ k * ∑' d : ℕ, (if K < xi d then seriesTerm d else 0) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hinj : ∀ a ∈ Um, ∀ b ∈ Um, ∏ p ∈ a, p = ∏ p ∈ b, p → a = b :=
          fun a ha b hb => prod_inj_on_U218 (mem_filter.1 ha).1 (mem_filter.1 hb).1
        have himg : ∑ d ∈ Um.image (fun s => ∏ p ∈ s, p),
              (if K < xi d then seriesTerm d else 0) =
            ∑ s ∈ Um, (if K < xi (∏ p ∈ s, p) then
              seriesTerm (∏ p ∈ s, p) else 0) := by
          refine Finset.sum_image ?_
          intro a ha b hb hab
          exact hinj a ha b hb hab
        rw [← himg]
        exact htsum.sum_le_tsum _ fun d _ => hnn d

/-- **The large-period region `ξ(d_s) > M`, summed**: the total weight of those divisors, times
`M^{k-1}`. -/
private lemma sum_large218 {k M K N : ℕ} (hk : 1 ≤ k) (hM1 : 1 ≤ M)
    (hle : ∀ ν ∈ exponentTuples131 k M, tuplePower131 ν ≤ N)
    (hpos : ∀ ν ∈ exponentTuples131 k M, 0 < N - tuplePower131 ν)
    (hlt : ∀ ν ∈ exponentTuples131 k M, tuplePower131 ν < N) :
    ∑ s ∈ ((exponentTuples131 k M).biUnion
          (fun ν => (opf (N - tuplePower131 ν)).powerset)).filter
          (fun s => M < xi (∏ p ∈ s, p)),
        (#{ν ∈ exponentTuples131 k M |
          s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s ≤
      (M : ℝ) ^ (k - 1) *
        H (∏ ν ∈ exponentTuples131 k M, (N - tuplePower131 ν)) := by
  classical
  set U := (exponentTuples131 k M).biUnion
    (fun ν => (opf (N - tuplePower131 ν)).powerset) with hU
  set Ul := U.filter (fun s => M < xi (∏ p ∈ s, p)) with hUl
  have hkk : k - 1 + 1 = k := by omega
  have hpw : ∀ s ∈ Ul, (#{ν ∈ exponentTuples131 k M |
        s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s ≤
      (M : ℝ) ^ (k - 1) * W s := by
    intro s hs
    obtain ⟨hsU, hxl⟩ := mem_filter.1 hs
    have hle' : ∀ ν ∈ exponentTuples131 (k - 1 + 1) M, tuplePower131 ν ≤ N := by
      rw [hkk]; exact hle
    have hlt' : ∀ ν ∈ exponentTuples131 (k - 1 + 1) M, tuplePower131 ν < N := by
      rw [hkk]; exact hlt
    have hc := tuple_count_xi_large218 (k := k - 1) (M := M) (N := N) hM1
      (mem_U_spec218 hsU) hxl hle' hlt'
    rw [hkk] at hc
    have hcr : (#{ν ∈ exponentTuples131 k M |
        s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) ≤ (M : ℝ) ^ (k - 1) := by
      exact_mod_cast hc
    have hW : 0 ≤ W s := W_nonneg fun p hp => (mem_U_spec218 hsU p hp).2
    exact mul_le_mul_of_nonneg_right hcr hW
  calc ∑ s ∈ Ul, (#{ν ∈ exponentTuples131 k M |
        s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s
      ≤ ∑ s ∈ Ul, (M : ℝ) ^ (k - 1) * W s := Finset.sum_le_sum hpw
    _ = (M : ℝ) ^ (k - 1) * ∑ s ∈ Ul, W s := (Finset.mul_sum ..).symm
    _ ≤ (M : ℝ) ^ (k - 1) * ∑ s ∈ U, W s := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun s hs _ => W_nonneg fun p hp => (mem_U_spec218 hs p hp).2
    _ ≤ (M : ℝ) ^ (k - 1) *
        H (∏ ν ∈ exponentTuples131 k M, (N - tuplePower131 ν)) := by
        refine mul_le_mul_of_nonneg_left (sum_W_le_HP218 hpos) (by positivity)
/-- **Displays 20 to 23 at the head truncation `K`.** The coefficient sum over the moduli of `U`
with `ξ(d) ≤ K` is the finite part of the series (23) at `2^K`: a modulus with `ξ(d) ≤ K` that
occurs in the series at all is already hit inside the box `[1, ξ(d)]^{j+1} ⊆ [1,M]^{j+1}`, hence
is counted in `U`, and `d ≤ 2^ξ(d) - 1 < 2^K + 1` makes the sum finite. -/
private lemma coeff_image_K218 {j K M N : ℕ} (hKM : K ≤ M)
    (hle : ∀ ν ∈ exponentTuples131 (j + 1) M, tuplePower131 ν ≤ N)
    (hpos : ∀ ν ∈ exponentTuples131 (j + 1) M, 0 < N - tuplePower131 ν) :
    ∑ s ∈ ((exponentTuples131 (j + 1) M).biUnion
        (fun ν => (opf (N - tuplePower131 ν)).powerset)).filter
        (fun s => xi (∏ p ∈ s, p) ≤ K),
        Ckterm (j + 1) N (∏ p ∈ s, p)
      = ∑ d ∈ (Finset.range (2 ^ K + 1)).filter (fun d => xi d ≤ K), Ckterm (j + 1) N d := by
  classical
  set T := exponentTuples131 (j + 1) M with hT
  set U := T.biUnion (fun ν => (opf (N - tuplePower131 ν)).powerset) with hU
  set U' := U.filter (fun s => xi (∏ p ∈ s, p) ≤ K) with hU'
  have hUs : ∀ s ∈ U, ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro s hs p hp
    rw [hU, Finset.mem_biUnion] at hs
    obtain ⟨ν, -, hsν⟩ := hs
    exact ⟨(opf_spec (mem_powerset.1 hsν hp)).1, (opf_spec (mem_powerset.1 hsν hp)).2.1⟩
  have hinj : ∀ a ∈ U', ∀ b ∈ U', ∏ p ∈ a, p = ∏ p ∈ b, p → a = b := by
    intro a ha b hb hab
    have h1 : Nat.primeFactors (∏ p ∈ a, p) = a :=
      primeFactors_prod_of_primes218 fun p hp => (hUs a (mem_filter.1 ha).1 p hp).1
    have h2 : Nat.primeFactors (∏ p ∈ b, p) = b :=
      primeFactors_prod_of_primes218 fun p hp => (hUs b (mem_filter.1 hb).1 p hp).1
    rw [← h1, ← h2, hab]
  rw [← Finset.sum_image hinj]
  refine Finset.sum_subset ?_ ?_
  · -- the occurring moduli lie below `2^M + 1`
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨s, hs, rfl⟩ := hd
    obtain ⟨hsU, hsxi⟩ := mem_filter.1 hs
    obtain ⟨hos, -, -⟩ := set_facts (fun p hp => hUs s hsU p hp)
    rw [mem_filter, mem_range]
    refine ⟨?_, hsxi⟩
    have h := d_le_two_pow218 hos.2.1 hos.1 hsxi
    omega
  · -- a modulus that occurs in the series but not in `U` contributes nothing
    intro d hd hnot
    rw [mem_filter, mem_range] at hd
    obtain ⟨-, hdxi⟩ := hd
    unfold Ckterm
    split_ifs with hOS
    · have hz : jcount d j N = 0 := by
        by_contra hne
        obtain ⟨ν, hνT, hνdvd⟩ :=
          jcount_pos_mem218 (d := d) (j := j) (M := M) (N := N) (le_trans hdxi hKM) hle
            (Nat.pos_of_ne_zero hne)
        have hn0 : N - tuplePower131 ν ≠ 0 := (hpos ν hνT).ne'
        have hsU : d.primeFactors ∈ U := by
          rw [hU, Finset.mem_biUnion]
          refine ⟨ν, hνT, mem_powerset.2 ?_⟩
          intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hpd : p ∣ N - tuplePower131 ν :=
            (Nat.dvd_of_mem_primeFactors hp).trans hνdvd
          refine mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hpp, hpd, hn0⟩, ?_⟩
          have hne2 : p ≠ 2 := by
            rintro rfl
            exact (Nat.not_even_iff_odd.mpr hOS.2.1)
              (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
          have := hpp.two_le
          omega
        have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hOS.2.2
        have hmemS : xi (∏ p ∈ d.primeFactors, p) ≤ K := by rw [hprod]; exact hdxi
        exact hnot (mem_image.2 ⟨d.primeFactors, mem_filter.2 ⟨hsU, hmemS⟩, hprod⟩)
      have hji : j + 1 - 1 = j := by omega
      rw [hji, hz]
      simp
    · rfl

/-- `k (2M)^{k-1} · δM/(4k 2^{k-1}) = (δ/4) M^k`. -/
private lemma head_scale218 {k : ℕ} (hk : 1 ≤ k) {M δ : ℝ} :
    (k : ℝ) * (2 * M) ^ (k - 1) * (δ * M / (4 * (k : ℝ) * (2 : ℝ) ^ (k - 1))) =
      δ / 4 * M ^ k := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have h : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact h.ne'
  have hA : (2 : ℝ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hBM : M ^ (k - 1) * M = M ^ k := by
    rw [← pow_succ, kk_pred_succ218 hk]
  have hstep : (k : ℝ) * ((2 : ℝ) ^ (k - 1) * M ^ (k - 1)) *
      (δ * M / (4 * (k : ℝ) * (2 : ℝ) ^ (k - 1))) = δ / 4 * (M ^ (k - 1) * M) := by
    field_simp
  rw [mul_pow]
  exact hstep.trans (by rw [hBM])

/-- `(2M)^k · δ/(8·2^k) = (δ/8) M^k`. -/
private lemma middle_scale218 (k : ℕ) {M δ : ℝ} :
    (2 * M) ^ k * (δ / (8 * (2 : ℝ) ^ k)) = δ / 8 * M ^ k := by
  have hA : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [mul_pow]
  field_simp

/-- `M^{k-1} · δM/4 = (δ/4) M^k`. -/
private lemma large_scale218 {k : ℕ} (hk : 1 ≤ k) {M δ : ℝ} :
    M ^ (k - 1) * (δ * M / 4) = δ / 4 * M ^ k := by
  have hBM : M ^ (k - 1) * M = M ^ k := by
    rw [← pow_succ, kk_pred_succ218 hk]
  calc M ^ (k - 1) * (δ * M / 4) = δ / 4 * (M ^ (k - 1) * M) := by ring
    _ = δ / 4 * M ^ k := by rw [hBM]

set_option maxHeartbeats 4000000

/-- **The core estimate of the singular series average** (displays 15 to 24): for every `δ > 0`
and all large `X`, the weighted tuple sum of `H` is `Ck k N M^k` up to `δ M^k`, uniformly on the
even `N` of `J(X)`. This is the arithmetic input of `major_arcs_combine131`; it uses no analysis. -/
private lemma S0_estimate218 (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |∑ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊, H (N - tuplePower131 ν) -
        Ck k N * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k| ≤
      δ * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k := by
  classical
  set τ : ℝ := δ / (8 * (2 : ℝ) ^ k) with hτdef
  have hτ : 0 < τ := by
    rw [hτdef]; positivity
  obtain ⟨Kt, hKt⟩ := exists_xi_tail τ hτ
  set clog : ℝ := δ / (12 * Real.exp 27 * ((k : ℝ) + 1) * (k : ℝ) * (2 : ℝ) ^ (k - 1))
    with hclogdef
  have hclog : 0 < clog := by
    rw [hclogdef]; positivity
  obtain ⟨Xlog, hXlog⟩ := log_le_M218 clog hclog
  obtain ⟨Xwin, hXwin⟩ := tuple_window131 k
  obtain ⟨Xlg, hXlg⟩ := eventually_Lg_ge218 (max 16 (max (2 * (k : ℝ)) ((Kt : ℝ) ^ 2 + 1)))
  refine ⟨max Xwin (max Xlg Xlog), fun X hX N hN => ?_⟩
  have hx1 : Xwin ≤ X := le_trans (le_max_left _ _) hX
  have hx2 : Xlg ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hx3 : Xlog ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  obtain ⟨hL1, hw6⟩ := hXwin X hx1
  have hbig := hXlg X hx2
  have h16 : 16 ≤ Lg X := le_trans (le_max_left _ _) hbig
  have h2k : 2 * (k : ℝ) ≤ Lg X :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hbig)
  have hKtsq : ((Kt : ℝ) ^ 2 + 1) ≤ Lg X :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hbig)
  have hlogM : Real.log (Lg X + 2) ≤ clog * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) := hXlog X hx3
  obtain ⟨hM1, hML, hML2⟩ := M_bounds218 h16
  have hL0 : (0 : ℝ) ≤ Lg X := by linarith
  have hsq2 : Real.sqrt (Lg X) ≤ Lg X / 2 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hkM : k ≤ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by
    have h1 : (k : ℝ) ≤ (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) := by linarith
    exact_mod_cast h1
  -- `K = ⌊√L⌋` sits between `Kt` and `M`
  have hKle : ((⌊Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) ≤ Lg X - Real.sqrt (Lg X) := by
    have h2 : ((⌊Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (Lg X) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    linarith
  have hKM : ⌊Real.sqrt (Lg X)⌋₊ ≤ ⌊Lg X - Real.sqrt (Lg X)⌋₊ :=
    (Nat.le_floor_iff (by linarith)).2 hKle
  have hKtK : Kt ≤ ⌊Real.sqrt (Lg X)⌋₊ := by
    have hsq : (Kt : ℝ) ^ 2 ≤ Lg X := by linarith
    have h1 : (Kt : ℝ) ≤ Real.sqrt (Lg X) := by
      calc (Kt : ℝ) = Real.sqrt ((Kt : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (Lg X) := Real.sqrt_le_sqrt hsq
    exact (Nat.le_floor_iff (Real.sqrt_nonneg _)).2 h1
  have htailK : (∑' d : ℕ, (if ⌊Real.sqrt (Lg X)⌋₊ < xi d then seriesTerm d else 0)) ≤ τ :=
    hKt ⌊Real.sqrt (Lg X)⌋₊ hKtK
  -- the shifted arguments are positive and at most `N`
  obtain ⟨hN1, hN2, -, hN4⟩ := evenJ_nat131 hN
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by
    have : 1 ≤ X := by omega
    exact_mod_cast this
  have hk2M : (k : ℝ) * (2 : ℝ) ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ ≤ (X : ℝ) / 6 := by
    have hc : ((6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast hw6
    have he : ((6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) =
        6 * ((k : ℝ) * (2 : ℝ) ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) := by push_cast; ring
    rw [he] at hc
    linarith
  have hNR : (2 : ℝ) / 3 * (X : ℝ) ≤ (N : ℝ) := by
    have h : (2 : ℝ) * (X : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast hN4
    linarith
  have hle : ∀ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊,
      tuplePower131 ν ≤ N := by
    intro ν hν
    have h1 := tuplePower_le131 hν
    have h2 : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      have he : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) =
          (k : ℝ) * (2 : ℝ) ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by push_cast; ring
      rw [he]; nlinarith
    have h3 : k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ ≤ N := by exact_mod_cast h2
    omega
  have hpos : ∀ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊,
      0 < N - tuplePower131 ν := by
    intro ν hν
    have := hle ν hν
    have h2 : tuplePower131 ν ≤ k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := tuplePower_le131 hν
    have h3 : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) < (N : ℝ) := by
      have he : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) =
          (k : ℝ) * (2 : ℝ) ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by push_cast; ring
      rw [he]; nlinarith
    have h4 : k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ < N := by exact_mod_cast h3
    omega
  have hlt : ∀ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊,
      tuplePower131 ν < N := by
    intro ν hν
    have h2 : tuplePower131 ν ≤ k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := tuplePower_le131 hν
    have h3 : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) < (N : ℝ) := by
      have he : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) =
          (k : ℝ) * (2 : ℝ) ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by push_cast; ring
      rw [he]; nlinarith
    have h4 : k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ < N := by exact_mod_cast h3
    omega
  -- the product bound for `H`
  have hHPb := H_prod_bound218 (k := k) (M := ⌊Lg X - Real.sqrt (Lg X)⌋₊) (X := X) (N := N)
    (by omega : 1 ≤ X) hk hML hkM hN2 hpos
  have hHP1 : H (∏ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊,
      (N - tuplePower131 ν)) ≤
      δ * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) /
        (4 * (k : ℝ) * (2 : ℝ) ^ (k - 1)) := by
    refine hHPb.trans ?_
    have hk0 : (k : ℝ) ≠ 0 := by
      have h : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      exact h.ne'
    have hA0 : (2 : ℝ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hk10 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have he0 : Real.exp 27 ≠ 0 := (Real.exp_pos 27).ne'
    calc 3 * Real.exp 27 * ((k : ℝ) + 1) * Real.log (Lg X + 2)
        ≤ 3 * Real.exp 27 * ((k : ℝ) + 1) * (clog * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ)) := by
          refine mul_le_mul_of_nonneg_left hlogM (by positivity)
      _ = δ * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) / (4 * (k : ℝ) * (2 : ℝ) ^ (k - 1)) := by
          rw [hclogdef]
          field_simp
          ring
  -- the weighted tuple sum, its three regions, and the coefficient
  set U := (exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊).biUnion
    (fun ν => (opf (N - tuplePower131 ν)).powerset) with hU
  set cf : Finset ℕ → ℝ := fun s =>
    (#{ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ |
      s ∈ (opf (N - tuplePower131 ν)).powerset} : ℝ) * W s with hcf
  set U1 := U.filter (fun s => xi (∏ p ∈ s, p) ≤ ⌊Real.sqrt (Lg X)⌋₊) with hU1
  set U2 := U.filter (fun s => ⌊Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p) ∧
    xi (∏ p ∈ s, p) ≤ ⌊Lg X - Real.sqrt (Lg X)⌋₊) with hU2
  set U3 := U.filter (fun s => ⌊Lg X - Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p)) with hU3
  have hpart : ∀ s ∈ U, cf s =
      (if xi (∏ p ∈ s, p) ≤ ⌊Real.sqrt (Lg X)⌋₊ then cf s else 0) +
      (if ⌊Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p) ∧
          xi (∏ p ∈ s, p) ≤ ⌊Lg X - Real.sqrt (Lg X)⌋₊ then cf s else 0) +
      (if ⌊Lg X - Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p) then cf s else 0) := by
    intro s _
    by_cases h1 : xi (∏ p ∈ s, p) ≤ ⌊Real.sqrt (Lg X)⌋₊
    · have h2 : ¬ (⌊Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p) ∧
          xi (∏ p ∈ s, p) ≤ ⌊Lg X - Real.sqrt (Lg X)⌋₊) := by
        rintro ⟨h2', -⟩; omega
      rw [if_pos h1, if_neg h2,
        if_neg (by omega : ¬ ⌊Lg X - Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p))]
      ring
    · have h2 : ⌊Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p) := by omega
      by_cases h3 : xi (∏ p ∈ s, p) ≤ ⌊Lg X - Real.sqrt (Lg X)⌋₊
      · rw [if_neg h1, if_pos ⟨h2, h3⟩,
          if_neg (by omega : ¬ ⌊Lg X - Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p))]
        ring
      · have h4 : ¬ (⌊Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p) ∧
            xi (∏ p ∈ s, p) ≤ ⌊Lg X - Real.sqrt (Lg X)⌋₊) := by
          rintro ⟨-, h4'⟩; omega
        rw [if_neg h1, if_neg h4,
          if_pos (by omega : ⌊Lg X - Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p))]
        ring
  have hsplit : ∑ s ∈ U, cf s = ∑ s ∈ U1, cf s + ∑ s ∈ U2, cf s + ∑ s ∈ U3, cf s := by
    rw [hU1, hU2, hU3]
    calc ∑ s ∈ U, cf s
        = ∑ s ∈ U, ((if xi (∏ p ∈ s, p) ≤ ⌊Real.sqrt (Lg X)⌋₊ then cf s else 0) +
            (if ⌊Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p) ∧
                xi (∏ p ∈ s, p) ≤ ⌊Lg X - Real.sqrt (Lg X)⌋₊ then cf s else 0) +
            (if ⌊Lg X - Real.sqrt (Lg X)⌋₊ < xi (∏ p ∈ s, p) then cf s else 0)) :=
          Finset.sum_congr rfl hpart
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
  set A1 : ℝ := ∑ s ∈ U1, cf s with hA1def
  set A2 : ℝ := ∑ s ∈ U2, cf s with hA2def
  set A3 : ℝ := ∑ s ∈ U3, cf s with hA3def
  set B1 : ℝ := (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k *
    ∑ s ∈ U1, Ckterm k N (∏ p ∈ s, p) with hB1def
  set W1 : ℝ := ∑ s ∈ U1, W s with hW1def
  -- the three region bounds
  have hA1b : |A1 - B1| ≤ (k : ℝ) * (2 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ)) ^ (k - 1) * W1 := by
    rw [hA1def, hB1def, hW1def, hcf]
    exact sum_head218 (k := k) (M := ⌊Lg X - Real.sqrt (Lg X)⌋₊)
      (K := ⌊Real.sqrt (Lg X)⌋₊) (N := N) hk hKM hle hpos
  have hle' : ∀ ν ∈ exponentTuples131 (k - 1 + 1) ⌊Lg X - Real.sqrt (Lg X)⌋₊,
      tuplePower131 ν ≤ N := by
    rw [kk_pred_succ218 hk]; exact hle
  have hpos' : ∀ ν ∈ exponentTuples131 (k - 1 + 1) ⌊Lg X - Real.sqrt (Lg X)⌋₊,
      0 < N - tuplePower131 ν := by
    rw [kk_pred_succ218 hk]; exact hpos
  have hcoefEq := coeff_image_K218 (j := k - 1) (K := ⌊Real.sqrt (Lg X)⌋₊)
    (M := ⌊Lg X - Real.sqrt (Lg X)⌋₊) (N := N) hKM hle' hpos'
  rw [kk_pred_succ218 hk] at hcoefEq
  have hA2b : |∑ s ∈ U1, Ckterm k N (∏ p ∈ s, p) - Ck k N| ≤
      ∑' d : ℕ, (if ⌊Real.sqrt (Lg X)⌋₊ < xi d then seriesTerm d else 0) := by
    have hcf2 := Ck_sub_finite218 k ⌊Real.sqrt (Lg X)⌋₊ N hk
    rw [← hcoefEq] at hcf2
    rw [abs_sub_comm]
    exact hcf2
  have hA2nn : (0 : ℝ) ≤ A2 := by
    rw [hA2def]
    refine Finset.sum_nonneg fun s hs => ?_
    exact mul_nonneg (Nat.cast_nonneg _)
      (W_nonneg fun p hp => (mem_U_spec218 (mem_filter.1 hs).1 p hp).2)
  have hA3nn : (0 : ℝ) ≤ A3 := by
    rw [hA3def]
    refine Finset.sum_nonneg fun s hs => ?_
    exact mul_nonneg (Nat.cast_nonneg _)
      (W_nonneg fun p hp => (mem_U_spec218 (mem_filter.1 hs).1 p hp).2)
  have hB1b : |B1 - Ck k N * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k| ≤
      (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k *
        ∑' d : ℕ, (if ⌊Real.sqrt (Lg X)⌋₊ < xi d then seriesTerm d else 0) := by
    have h1 : B1 - Ck k N * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k =
        (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k *
          (∑ s ∈ U1, Ckterm k N (∏ p ∈ s, p) - Ck k N) := by
      rw [hB1def]; ring
    rw [h1, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hA2b (by positivity)
  have hA2b2 : A2 ≤ (2 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ)) ^ k *
      ∑' d : ℕ, (if ⌊Real.sqrt (Lg X)⌋₊ < xi d then seriesTerm d else 0) := by
    rw [hA2def, hcf]
    exact sum_middle218 (k := k) (M := ⌊Lg X - Real.sqrt (Lg X)⌋₊)
      (K := ⌊Real.sqrt (Lg X)⌋₊) (N := N) hk hle hpos
  have hA3b : A3 ≤ (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ (k - 1) *
      H (∏ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊, (N - tuplePower131 ν)) := by
    rw [hA3def, hcf]
    exact sum_large218 (k := k) (M := ⌊Lg X - Real.sqrt (Lg X)⌋₊)
      (K := ⌊Real.sqrt (Lg X)⌋₊) (N := N) hk hM1 hle hpos hlt
  -- the triangle inequality
  have htri : |A1 + A2 + A3 - Ck k N * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k| ≤
      |A1 - B1| + |B1 - Ck k N * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k| + |A2| + |A3| := by
    have hdecomp : A1 + A2 + A3 - Ck k N * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k =
        ((A1 - B1) + (B1 - Ck k N * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k)) + A2 + A3 := by
      ring
    rw [hdecomp]
    have h1 := abs_add_le (A1 - B1)
      (B1 - Ck k N * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k)
    have h2 := abs_add_le ((A1 - B1) +
      (B1 - Ck k N * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k)) A2
    have h3 := abs_add_le (((A1 - B1) +
      (B1 - Ck k N * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k)) + A2) A3
    have h4 : |A2| = A2 := abs_of_nonneg hA2nn
    have h5 : |A3| = A3 := abs_of_nonneg hA3nn
    linarith
  -- the four terms are each at most `δ/4` or `δ/8` of `M^k`
  have hW1b : W1 ≤ H (∏ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊,
      (N - tuplePower131 ν)) := by
    rw [hW1def, hU1]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_)
      (sum_W_le_HP218 hpos)
    intro s hs _
    exact W_nonneg fun p hp => (mem_U_spec218 hs p hp).2
  have hfin1 : (k : ℝ) * (2 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ)) ^ (k - 1) * W1 ≤
      δ / 4 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k := by
    have h1 := mul_le_mul_of_nonneg_left hW1b
      (show (0 : ℝ) ≤ (k : ℝ) * (2 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ)) ^ (k - 1) by positivity)
    refine h1.trans ?_
    have h2 := mul_le_mul_of_nonneg_left hHP1
      (show (0 : ℝ) ≤ (k : ℝ) * (2 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ)) ^ (k - 1) by positivity)
    exact h2.trans (le_of_eq (head_scale218 hk))
  have hfin2 : (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k *
      (∑' d : ℕ, (if ⌊Real.sqrt (Lg X)⌋₊ < xi d then seriesTerm d else 0)) ≤
      δ / 8 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k := by
    have h1 := mul_le_mul_of_nonneg_left htailK
      (show (0 : ℝ) ≤ (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k by positivity)
    have h2 : (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k * τ ≤
        δ / 8 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k := by
      have h3 : τ ≤ δ / 8 := by
        rw [hτdef]
        have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        refine div_le_div_of_nonneg_left hδ.le (by norm_num) ?_
        nlinarith
      have h6 := mul_le_mul_of_nonneg_left h3
        (show (0 : ℝ) ≤ (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k by positivity)
      linarith
    linarith
  have hfin3 : (2 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ)) ^ k *
      (∑' d : ℕ, (if ⌊Real.sqrt (Lg X)⌋₊ < xi d then seriesTerm d else 0)) ≤
      δ / 8 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k := by
    have h1 := mul_le_mul_of_nonneg_left htailK
      (show (0 : ℝ) ≤ (2 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ)) ^ k by positivity)
    refine h1.trans ?_
    exact le_of_eq (middle_scale218 k)
  have hHP2 : H (∏ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊,
      (N - tuplePower131 ν)) ≤ δ * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) / 4 := by
    refine hHP1.trans ?_
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hA1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := one_le_pow₀ (by norm_num)
    have hden : (4 : ℝ) ≤ 4 * (k : ℝ) * (2 : ℝ) ^ (k - 1) := by
      have h := mul_le_mul (mul_le_mul_of_nonneg_left hk1 (by norm_num : (0:ℝ) ≤ 4))
        hA1 (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ 4 * (k:ℝ))
      calc (4 : ℝ) = 4 * 1 * 1 := by norm_num
        _ ≤ 4 * (k : ℝ) * (2 : ℝ) ^ (k - 1) := h
    have h1 := div_le_div_of_nonneg_left
      (show (0 : ℝ) ≤ δ * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) by positivity)
      (by norm_num : (0 : ℝ) < 4) hden
    linarith
  have hfin4 : (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ (k - 1) *
      H (∏ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊, (N - tuplePower131 ν)) ≤
      δ / 4 * (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k := by
    have h1 := mul_le_mul_of_nonneg_left hHP2
      (show (0 : ℝ) ≤ (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ (k - 1) by positivity)
    exact h1.trans (le_of_eq (large_scale218 hk))
  have hS0 : ∑ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊, H (N - tuplePower131 ν) =
      ∑ s ∈ U, cf s := by
    rw [hcf, hU]
    exact tuple_H_eq_sum k ⌊Lg X - Real.sqrt (Lg X)⌋₊ N
  rw [hS0, hsplit, ← hA1def, ← hA2def, ← hA3def, ← hB1def] at *
  linarith [htri, hA1b, hB1b, hA2b2, hA3b, hfin1, hfin2, hfin3, hfin4, hA2nn, hA3nn,
    abs_of_nonneg hA2nn, abs_of_nonneg hA3nn]

/-- The relative shift `k(√L + 1)/L` is arbitrarily small. -/
private lemma eventually_sqrt_ratio218 (k : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (k : ℝ) * ((Real.sqrt (Lg X) + 1) / Lg X) ≤ c := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · refine ⟨1, fun X _ => ?_⟩
    subst hk0
    simp only [Nat.cast_zero, zero_mul]
    exact hc.le
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  obtain ⟨X₀, hX₀⟩ := eventually_Lg_ge218
    (max 1 (max ((2 * (k : ℝ) / c) ^ 2) (2 * (k : ℝ) / c)))
  refine ⟨X₀, fun X hX => ?_⟩
  have h := hX₀ X hX
  have hL1 : (1 : ℝ) ≤ Lg X := le_trans (le_max_left _ _) h
  have hLa : (2 * (k : ℝ) / c) ^ 2 ≤ Lg X :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h)
  have hLb : 2 * (k : ℝ) / c ≤ Lg X :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h)
  have hL0 : 0 < Lg X := by linarith
  have hsq : Real.sqrt (Lg X) * Real.sqrt (Lg X) = Lg X := Real.mul_self_sqrt hL0.le
  have hs0 : 0 < Real.sqrt (Lg X) := Real.sqrt_pos.mpr hL0
  have hs : 2 * (k : ℝ) / c ≤ Real.sqrt (Lg X) := by
    calc 2 * (k : ℝ) / c = Real.sqrt ((2 * (k : ℝ) / c) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Lg X) := Real.sqrt_le_sqrt hLa
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  have he : 2 * (k : ℝ) / c * (c / 2) = (k : ℝ) := by
    field_simp
  have h1 : (k : ℝ) / Real.sqrt (Lg X) ≤ c / 2 := by
    rw [div_le_iff₀ hs0]
    have h' := mul_le_mul_of_nonneg_right hs hc2.le
    rw [he] at h'
    linarith
  have h2 : (k : ℝ) / Lg X ≤ c / 2 := by
    rw [div_le_iff₀ hL0]
    have h' := mul_le_mul_of_nonneg_right hLb hc2.le
    rw [he] at h'
    linarith
  have heq : (k : ℝ) * ((Real.sqrt (Lg X) + 1) / Lg X) =
      (k : ℝ) / Real.sqrt (Lg X) + (k : ℝ) / Lg X := by
    have h3 : (k : ℝ) * Real.sqrt (Lg X) / Lg X = (k : ℝ) / Real.sqrt (Lg X) := by
      rw [div_eq_div_iff hL0.ne' hs0.ne']
      nlinarith [hsq]
    rw [← h3, ← add_div]
    have h4 : (k : ℝ) * (Real.sqrt (Lg X) + 1) = (k : ℝ) * Real.sqrt (Lg X) + k := by ring
    rw [← mul_div_assoc, h4]
  rw [heq]
  linarith

/-- Bernoulli for the exponent cutoff: `L^k - M^k ≤ L^k k (1 - M/L)` for `0 ≤ M ≤ L`. -/
private lemma pow_sub_pow_le218 {k : ℕ} {M L : ℝ} (hM0 : 0 ≤ M) (hML : M ≤ L) (hL0 : 0 < L) :
    L ^ k - M ^ k ≤ L ^ k * ((k : ℝ) * (1 - M / L)) := by
  set r := M / L with hr
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one hL0]; exact hML
  have hr0 : -1 ≤ r := by
    rw [hr]
    have h : (0 : ℝ) ≤ M / L := div_nonneg hM0 hL0.le
    linarith
  have hbern : 1 + (k : ℝ) * (r - 1) ≤ r ^ k := one_add_mul_sub_le_pow hr0 k
  have hM : M = r * L := by
    rw [hr]; field_simp
  have hpow : M ^ k = r ^ k * L ^ k := by rw [hM, mul_pow]
  have hLk : (0 : ℝ) ≤ L ^ k := by positivity
  calc L ^ k - M ^ k = L ^ k * (1 - r ^ k) := by rw [hpow]; ring
    _ ≤ L ^ k * (1 - (1 + (k : ℝ) * (r - 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ hLk
        linarith
    _ = L ^ k * ((k : ℝ) * (1 - r)) := by ring
    _ = L ^ k * ((k : ℝ) * (1 - M / L)) := by rw [hr]
set_option maxHeartbeats 4000000

/-- **Display 25, the singular series average** — the content of the leaf `major_arcs_combine131`.
Two primes and `k` powers of two: the weighted singular series sum over the exponent tuples is
`2c₀ C(k,N) N L^k` up to `o(N L^k)`, uniformly on the even `N` of `J(X)`. -/
private lemma major_arcs_combine218 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |∑ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊,
          ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) -
        coefficient131 k N * N * Lg X ^ k| ≤ ε * N * Lg X ^ k := by
  classical
  have htc : 0 < LeanLab.ChenExplicit.twinC := LeanLab.ChenExplicit.twinC_pos
  set Sc : ℝ := ∑' d, seriesTerm d with hScdef
  have hSc : 0 ≤ Sc := tsum_nonneg fun d => seriesTerm_nonneg d
  set δ : ℝ := min (ε / (8 * (LeanLab.ChenExplicit.twinC + 1))) 1 with hδdef
  have hδ : 0 < δ := lt_min (div_pos hε (by positivity)) one_pos
  have hδ1 : δ ≤ ε / (8 * (LeanLab.ChenExplicit.twinC + 1)) := min_le_left _ _
  have hδ2 : δ ≤ 1 := min_le_right _ _
  set η : ℝ := ε / (12 * (LeanLab.ChenExplicit.twinC + 1) * (Sc + 1)) with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  set cr : ℝ := ε / (8 * LeanLab.ChenExplicit.twinC * (Sc + 1)) with hcrdef
  have hcr : 0 < cr := by rw [hcrdef]; positivity
  obtain ⟨X1, hX1⟩ := S0_estimate218 k hk δ hδ
  obtain ⟨X2, hX2⟩ := tuple_window131 k
  obtain ⟨X3, hX3⟩ := tuple_window_eps218 k η hη
  obtain ⟨X4, hX4⟩ := eventually_sqrt_ratio218 k cr hcr
  obtain ⟨X5, hX5⟩ := eventually_Lg_ge218 (max 16 (max 2 (k : ℝ)))
  refine ⟨max X1 (max X2 (max X3 (max X4 X5))), fun X hX N hN => ?_⟩
  have hx1 : X1 ≤ X := by omega
  have hx2 : X2 ≤ X := by omega
  have hx3 : X3 ≤ X := by omega
  have hx4 : X4 ≤ X := by omega
  have hx5 : X5 ≤ X := by omega
  obtain ⟨hL1, hw6⟩ := hX2 X hx2
  have hbig := hX5 X hx5
  have h16 : 16 ≤ Lg X := le_trans (le_max_left _ _) hbig
  have hL2 : (2 : ℝ) ≤ Lg X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hbig)
  have hLpos : (0 : ℝ) < Lg X := by linarith
  have hL0 : (0 : ℝ) ≤ Lg X := hLpos.le
  obtain ⟨hM1, hML, hML2⟩ := M_bounds218 h16
  have hMpos : (0 : ℝ) < (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) := by exact_mod_cast hM1
  have hM0 : (0 : ℝ) ≤ (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) := hMpos.le
  have hMlow : Lg X - Real.sqrt (Lg X) - 1 < (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) := by
    have ht := Nat.lt_floor_add_one (Lg X - Real.sqrt (Lg X))
    linarith
  have hS0b := hX1 X hx1 N hN
  obtain ⟨hN1, hN2, hNeven, hN4⟩ := evenJ_nat131 hN
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    have : 1 ≤ X := by omega
    exact_mod_cast this
  have hk2M : (k : ℝ) * (2 : ℝ) ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ ≤ (X : ℝ) / 6 := by
    have hc : ((6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast hw6
    have he : ((6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) =
        6 * ((k : ℝ) * (2 : ℝ) ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) := by push_cast; ring
    rw [he] at hc
    linarith
  have hk2Mle : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
    have hNR2 : (2 : ℝ) / 3 * (X : ℝ) ≤ (N : ℝ) := by
      have h : (2 : ℝ) * (X : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast hN4
      linarith
    have he : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) =
        (k : ℝ) * (2 : ℝ) ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by push_cast; ring
    rw [he]; nlinarith
  have hk2Mlt : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) < (N : ℝ) := by
    have hNR2 : (2 : ℝ) / 3 * (X : ℝ) ≤ (N : ℝ) := by
      have h : (2 : ℝ) * (X : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast hN4
      linarith
    have he : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) =
        (k : ℝ) * (2 : ℝ) ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by push_cast; ring
    rw [he]; nlinarith
  have hle : ∀ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊, tuplePower131 ν ≤ N := by
    intro ν hν
    have h1 := tuplePower_le131 hν
    have h2 : k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ ≤ N := by exact_mod_cast hk2Mle
    omega
  have hposn : ∀ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊,
      0 < N - tuplePower131 ν := by
    intro ν hν
    have h1 := tuplePower_le131 hν
    have h2 : k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ < N := by exact_mod_cast hk2Mlt
    omega
  set T := exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ with hT
  set Mk : ℝ := (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) ^ k with hMkdef
  set Lk : ℝ := Lg X ^ k with hLkdef
  set E : ℝ := (N : ℝ) * Lg X ^ k with hEdef
  set S0 : ℝ := ∑ ν ∈ T, H (N - tuplePower131 ν) with hS0def
  set th : ℝ := ∑ ν ∈ T, ((tuplePower131 ν : ℕ) : ℝ) * H (N - tuplePower131 ν) with hthdef
  set A : ℝ := ∑ ν ∈ T, ((N - tuplePower131 ν : ℕ) : ℝ) * H (N - tuplePower131 ν) with hAdef
  have hMk0 : (0 : ℝ) ≤ Mk := by rw [hMkdef]; positivity
  have hMkL : Mk ≤ Lk := by
    rw [hMkdef, hLkdef]
    exact pow_le_pow_left₀ hM0 hML k
  have hCk0 : (0 : ℝ) ≤ Ck k N := tsum_nonneg fun d => Ckterm_nonneg k N d
  have hCkSc : Ck k N ≤ Sc := by rw [hScdef]; exact Ck_le_series131 hk N
  have hSing : ∀ ν ∈ T, ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) =
      2 * LeanLab.ChenExplicit.twinC *
        (((N - tuplePower131 ν : ℕ) : ℝ) * H (N - tuplePower131 ν)) := by
    intro ν hν
    have hle' := hle ν hν
    have hev : Even (N - tuplePower131 ν) :=
      (Nat.even_sub hle').mpr (iff_of_true hNeven (tuplePower_even131 hν))
    have hn0 : N - tuplePower131 ν ≠ 0 := (hposn ν hν).ne'
    rw [Sing_even_eq218 hev hn0]
    ring
  have hLHS : ∑ ν ∈ T, ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) =
      2 * LeanLab.ChenExplicit.twinC * A := by
    rw [hAdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν hν => ?_
    exact hSing ν hν
  have hAsplit : A = (N : ℝ) * S0 - th := by
    rw [hAdef, hS0def, hthdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ν hν => ?_
    have h1 : ((N - tuplePower131 ν : ℕ) : ℝ) = (N : ℝ) - ((tuplePower131 ν : ℕ) : ℝ) :=
      Nat.cast_sub (hle ν hν)
    rw [h1]; ring
  have hS0up : S0 ≤ (Sc + 1) * Mk := by
    have h1 := (abs_le.mp hS0b).2
    have h2 : Ck k N * Mk ≤ Sc * Mk := mul_le_mul_of_nonneg_right hCkSc hMk0
    have h3 : δ * Mk ≤ 1 * Mk := mul_le_mul_of_nonneg_right hδ2 hMk0
    nlinarith [h1, h2, h3]
  have hH0 : ∀ ν : Fin k → ℕ, (0 : ℝ) ≤ H (N - tuplePower131 ν) :=
    fun ν => le_trans zero_le_one (one_le_H (N - tuplePower131 ν))
  have hthb : th ≤ ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) * S0 := by
    rw [hthdef, hS0def]
    calc ∑ ν ∈ T, ((tuplePower131 ν : ℕ) : ℝ) * H (N - tuplePower131 ν)
        ≤ ∑ ν ∈ T, ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) * H (N - tuplePower131 ν) := by
          refine Finset.sum_le_sum fun ν hν => ?_
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast tuplePower_le131 hν) (hH0 ν)
      _ = ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) * ∑ ν ∈ T, H (N - tuplePower131 ν) :=
          (Finset.mul_sum ..).symm
  have hthnn : (0 : ℝ) ≤ th := by
    rw [hthdef]
    exact Finset.sum_nonneg fun ν _ => mul_nonneg (Nat.cast_nonneg _) (hH0 ν)
  have hratio : (k : ℝ) * (1 - (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) / Lg X) ≤ cr := by
    have h1 : 1 - (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) / Lg X ≤
        (Real.sqrt (Lg X) + 1) / Lg X := by
      have hmul : (1 - (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) / Lg X) * Lg X =
          Lg X - (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) := by
        field_simp
      rw [le_div_iff₀ hLpos, hmul]
      linarith [hMlow]
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    have h4 := hX4 X hx4
    linarith
  have hdiff : Lk - Mk ≤ Lk * cr := by
    have h1 := pow_sub_pow_le218 (k := k) hM0 hML hLpos
    have h2 : Lg X ^ k * ((k : ℝ) *
        (1 - (⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℝ) / Lg X)) ≤ Lg X ^ k * cr :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    rw [hLkdef, hMkdef]
    linarith
  -- (1) the `Ck M^k` error, scaled by `N`
  have hP1 : (N : ℝ) * |S0 - Ck k N * Mk| ≤ ε / (8 * LeanLab.ChenExplicit.twinC) * E := by
    have h1 : |S0 - Ck k N * Mk| ≤ δ * Mk := hS0b
    have h2 : (N : ℝ) * |S0 - Ck k N * Mk| ≤ (N : ℝ) * (δ * Mk) :=
      mul_le_mul_of_nonneg_left h1 hNR
    have h3 : (N : ℝ) * (δ * Mk) ≤ (N : ℝ) * (δ * Lk) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMkL hδ.le) hNR
    have h5 : δ ≤ ε / (8 * LeanLab.ChenExplicit.twinC) := by
      refine hδ1.trans ?_
      have h7 : (0 : ℝ) < 8 * LeanLab.ChenExplicit.twinC := by positivity
      have h9 : (8 * LeanLab.ChenExplicit.twinC) ≤ 8 * (LeanLab.ChenExplicit.twinC + 1) := by
        linarith
      exact div_le_div_of_nonneg_left hε.le h7 h9
    have h4 : (N : ℝ) * (δ * Lk) ≤ ε / (8 * LeanLab.ChenExplicit.twinC) * E := by
      have h9 : (N : ℝ) * (δ * Lk) ≤
          (N : ℝ) * ((ε / (8 * LeanLab.ChenExplicit.twinC)) * Lk) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h5 (by positivity)) hNR
      calc (N : ℝ) * (δ * Lk) ≤ (N : ℝ) * ((ε / (8 * LeanLab.ChenExplicit.twinC)) * Lk) := h9
        _ = ε / (8 * LeanLab.ChenExplicit.twinC) * E := by rw [hEdef, hLkdef]; ring
    linarith
  -- (2) the `M^k` versus `L^k` difference
  have hP2 : Ck k N * ((N : ℝ) * (Lk - Mk)) ≤ ε / (8 * LeanLab.ChenExplicit.twinC) * E := by
    have h2 : (N : ℝ) * (Lk - Mk) ≤ (N : ℝ) * (Lk * cr) :=
      mul_le_mul_of_nonneg_left hdiff hNR
    have h3 : Ck k N * ((N : ℝ) * (Lk - Mk)) ≤ Sc * ((N : ℝ) * (Lk * cr)) :=
      mul_le_mul hCkSc h2 (by positivity) hSc
    have h4 : Sc * cr ≤ ε / (8 * LeanLab.ChenExplicit.twinC) := by
      have e : Sc * cr = ε * (Sc / (Sc + 1)) / (8 * LeanLab.ChenExplicit.twinC) := by
        rw [hcrdef]; field_simp; try ring
      rw [e]
      have h1 : Sc / (Sc + 1) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      calc ε * (Sc / (Sc + 1)) / (8 * LeanLab.ChenExplicit.twinC) ≤
          ε * 1 / (8 * LeanLab.ChenExplicit.twinC) := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left h1 hε.le
        _ = ε / (8 * LeanLab.ChenExplicit.twinC) := by ring
    calc Ck k N * ((N : ℝ) * (Lk - Mk)) ≤ Sc * ((N : ℝ) * (Lk * cr)) := h3
      _ = (Sc * cr) * ((N : ℝ) * Lk) := by ring
      _ ≤ (ε / (8 * LeanLab.ChenExplicit.twinC)) * ((N : ℝ) * Lk) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = ε / (8 * LeanLab.ChenExplicit.twinC) * E := by rw [hEdef, hLkdef]
  -- (3) the shift sum
  have hP3 : th ≤ ε / (8 * LeanLab.ChenExplicit.twinC) * E := by
    have he3 : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) =
        (k : ℝ) * (2 : ℝ) ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by push_cast; ring
    have h3 : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) ≤ η * (X : ℝ) := by
      rw [he3]; exact hX3 X hx3
    have h5 : (X : ℝ) ≤ 3 / 2 * (N : ℝ) := by
      have h : (2 : ℝ) * (X : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast hN4
      linarith
    have hcoef : η * ((3 / 2 : ℝ) * (Sc + 1)) ≤ ε / (8 * LeanLab.ChenExplicit.twinC) := by
      have e : η * ((3 / 2 : ℝ) * (Sc + 1)) =
          ε / (8 * (LeanLab.ChenExplicit.twinC + 1)) := by
        rw [hηdef]; field_simp; try ring
      rw [e]
      have h7 : (0 : ℝ) < 8 * LeanLab.ChenExplicit.twinC := by positivity
      have h9 : (8 * LeanLab.ChenExplicit.twinC) ≤ 8 * (LeanLab.ChenExplicit.twinC + 1) := by
        linarith
      exact div_le_div_of_nonneg_left hε.le h7 h9
    have hstep1 : th ≤ ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) * ((Sc + 1) * Mk) :=
      hthb.trans (mul_le_mul_of_nonneg_left hS0up (Nat.cast_nonneg _))
    have hstep2 : ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) * ((Sc + 1) * Mk) ≤
        η * (X : ℝ) * ((Sc + 1) * Mk) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have hstep3 : η * (X : ℝ) * ((Sc + 1) * Mk) ≤
        (η * ((3 / 2 : ℝ) * (Sc + 1))) * ((N : ℝ) * Lk) := by
      have h8 : (0 : ℝ) ≤ η * (Sc + 1) * Mk := by
        have h9 : (0 : ℝ) ≤ Sc + 1 := by linarith
        nlinarith [hη.le, h9, hMk0]
      have h6 : η * (X : ℝ) * ((Sc + 1) * Mk) ≤
          η * (3 / 2 * (N : ℝ)) * ((Sc + 1) * Mk) := by nlinarith [h5, h8, hη.le]
      have h7 : (0 : ℝ) ≤ η * ((3 / 2 : ℝ) * (Sc + 1)) * (N : ℝ) := by positivity
      have h10 : η * ((3 / 2 : ℝ) * (Sc + 1)) * (N : ℝ) * Mk ≤
          η * ((3 / 2 : ℝ) * (Sc + 1)) * (N : ℝ) * Lk := by
        have h11 : (0 : ℝ) ≤ η * ((3 / 2 : ℝ) * (Sc + 1)) * (N : ℝ) := h7
        exact mul_le_mul_of_nonneg_left hMkL h11
      nlinarith [h6, h10]
    calc th ≤ ((k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) * ((Sc + 1) * Mk) := hstep1
      _ ≤ η * (X : ℝ) * ((Sc + 1) * Mk) := hstep2
      _ ≤ (η * ((3 / 2 : ℝ) * (Sc + 1))) * ((N : ℝ) * Lk) := hstep3
      _ ≤ (ε / (8 * LeanLab.ChenExplicit.twinC)) * ((N : ℝ) * Lk) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = ε / (8 * LeanLab.ChenExplicit.twinC) * E := by rw [hEdef, hLkdef]
  -- assemble
  have hkey : A - Ck k N * (N : ℝ) * Lg X ^ k =
      (N : ℝ) * (S0 - Ck k N * Mk) + Ck k N * ((N : ℝ) * (Mk - Lk)) - th := by
    rw [hAsplit, hLkdef]; ring
  have htri : |A - Ck k N * (N : ℝ) * Lg X ^ k| ≤
      (N : ℝ) * |S0 - Ck k N * Mk| + Ck k N * ((N : ℝ) * (Lk - Mk)) + th := by
    rw [hkey]
    have h1 : |(N : ℝ) * (S0 - Ck k N * Mk) + Ck k N * ((N : ℝ) * (Mk - Lk)) - th| ≤
        |(N : ℝ) * (S0 - Ck k N * Mk) + Ck k N * ((N : ℝ) * (Mk - Lk))| + |th| := by
      rw [sub_eq_add_neg]
      have hh := abs_add_le ((N : ℝ) * (S0 - Ck k N * Mk) +
        Ck k N * ((N : ℝ) * (Mk - Lk))) (-th)
      rw [abs_neg] at hh
      exact hh
    have h2 : |(N : ℝ) * (S0 - Ck k N * Mk) + Ck k N * ((N : ℝ) * (Mk - Lk))| ≤
        |(N : ℝ) * (S0 - Ck k N * Mk)| + |Ck k N * ((N : ℝ) * (Mk - Lk))| :=
      abs_add_le _ _
    have e1 : |(N : ℝ) * (S0 - Ck k N * Mk)| = (N : ℝ) * |S0 - Ck k N * Mk| := by
      rw [abs_mul, abs_of_nonneg hNR]
    have e2 : |Ck k N * ((N : ℝ) * (Mk - Lk))| = Ck k N * ((N : ℝ) * (Lk - Mk)) := by
      rw [abs_mul, abs_of_nonneg hCk0, abs_mul, abs_of_nonneg hNR, abs_sub_comm,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ Lk - Mk)]
    have e3 : |th| = th := abs_of_nonneg hthnn
    linarith
  have hsplit3 : |A - Ck k N * (N : ℝ) * Lg X ^ k| ≤
      ε / (2 * LeanLab.ChenExplicit.twinC) * E := by
    have hsum : ε / (8 * LeanLab.ChenExplicit.twinC) * E +
        ε / (8 * LeanLab.ChenExplicit.twinC) * E +
        ε / (8 * LeanLab.ChenExplicit.twinC) * E ≤
        ε / (2 * LeanLab.ChenExplicit.twinC) * E := by
      have htc0 : LeanLab.ChenExplicit.twinC ≠ 0 := htc.ne'
      have he : ε / (2 * LeanLab.ChenExplicit.twinC) * E =
          4 * (ε / (8 * LeanLab.ChenExplicit.twinC) * E) := by
        field_simp
        ring
      rw [he]
      have h1 : (0 : ℝ) ≤ ε / (8 * LeanLab.ChenExplicit.twinC) * E := by positivity
      linarith
    linarith [htri, hP1, hP2, hP3, hsum]
  rw [hLHS]
  have hfinal : 2 * LeanLab.ChenExplicit.twinC * |A - Ck k N * (N : ℝ) * Lg X ^ k| ≤
      ε * E := by
    have h1 := mul_le_mul_of_nonneg_left hsplit3
      (show (0 : ℝ) ≤ 2 * LeanLab.ChenExplicit.twinC by positivity)
    have h2 : 2 * LeanLab.ChenExplicit.twinC *
        (ε / (2 * LeanLab.ChenExplicit.twinC) * E) = ε * E := by
      field_simp
    linarith
  have habs' : |2 * LeanLab.ChenExplicit.twinC * A - coefficient131 k N * N * Lg X ^ k| =
      2 * LeanLab.ChenExplicit.twinC * |A - Ck k N * (N : ℝ) * Lg X ^ k| := by
    have h2 : 2 * LeanLab.ChenExplicit.twinC * A - coefficient131 k N * (N : ℝ) * Lg X ^ k =
        2 * LeanLab.ChenExplicit.twinC * (A - Ck k N * (N : ℝ) * Lg X ^ k) := by
      unfold coefficient131; ring
    rw [h2, abs_mul, abs_of_nonneg (by positivity)]
  rw [habs']
  have hEeq : ε * (N : ℝ) * Lg X ^ k = ε * E := by
    rw [hEdef]; ring
  rw [hEeq]
  exact hfinal

/-- LEAF. Displays 15 to 24 on pages 7 and 8, with the factor 2c0 restored from display 2.
The weighted singular series sum over tuples in [1, L']^k is 2c0 C(k,N) N L^k up to
o(N L^k), uniformly on even N in J(X). This is arithmetic: Lemma 6.1, the expansion of S(n)
in display 2, display 19, display 20 with A'(N) of display 28, and the bound 30.
No analytic input. The parts already in the lab are `block_jcount_bounds131`,
`coefficient_tail_small131` and `sing_le_two_H`. -/
theorem major_arcs_combine131 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |∑ ν ∈ tuples131 k X,
          ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) -
        coefficient131 k N * N * Lg X ^ k| ≤ ε * N * Lg X ^ k := by
  exact major_arcs_combine218 k hk ε hε

/-- LEAF. Page 3, an admissible P always exists for large X. -/
theorem admissible_P_exists131 :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∃ P : ℝ, AdmissibleP131 X P := by
  refine ⟨1, fun X hX => ⟨(X : ℝ) ^ ((2:ℝ) / 5), ?_⟩⟩
  dsimp [AdmissibleP131]
  exact ⟨le_rfl, Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hX) (by norm_num)⟩

/-- The uniform bound for the corrected coefficient, displays 19, 23 and 26. -/
theorem coefficient_le131 {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    coefficient131 k N ≤ 2 * LeanLab.ChenExplicit.twinC * ∑' d, seriesTerm d := by
  unfold coefficient131
  exact mul_le_mul_of_nonneg_left (Ck_le_series131 hk N)
    (mul_nonneg (by norm_num) LeanLab.ChenExplicit.twinC_pos.le)

/-- CONDITIONAL on the two leaf statements, with no open proof of its own. Display 25 follows
from Corollary 4.2, the proved J_2 estimate and the singular series average. -/
theorem major_asymptotic_of_leaves131 (hj1 : Cor42Statement131)
    (hcomb : SingularAverageStatement131) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∃ P : ℝ, AdmissibleP131 X P ∧
      ∀ N ∈ evenJ131 X,
        |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤
          ε * N * Lg X ^ k := by
  classical
  set B : ℝ := 2 * LeanLab.ChenExplicit.twinC * ∑' d, seriesTerm d with hB
  have hB0 : 0 ≤ B := by
    refine le_trans ?_ (coefficient_le131 hk 0)
    exact mul_nonneg (mul_nonneg (by norm_num) LeanLab.ChenExplicit.twinC_pos.le)
      (by linarith [Ck_ge_one131 hk 0])
  have hB1 : 0 < B + 1 := by linarith
  set η : ℝ := ε / (3 * (B + 1)) with hηdef
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hB1)
  obtain ⟨K₁, Cstar, c, A, hC, hc, hA, X₁, hX₁⟩ := hj1 η hη
  have hA1 : 0 < A + 1 := by linarith
  have hε₂ : 0 < ε / (3 * (A + 1)) := div_pos hε (mul_pos (by norm_num) hA1)
  obtain ⟨X₂, hX₂⟩ := major_arcs_j2_131 k hk K₁ Cstar hC c hc _ hε₂
  obtain ⟨X₃, hX₃⟩ := hcomb k hk (ε / 3) (by positivity)
  obtain ⟨X₄, hX₄⟩ := hcomb k hk 1 one_pos
  obtain ⟨X₅, hX₅⟩ := tuple_window131 k
  refine ⟨max X₁ (max X₂ (max X₃ (max X₄ X₅))), fun X hX => ?_⟩
  have hx1 : X₁ ≤ X := by omega
  have hx2 : X₂ ≤ X := by omega
  have hx3 : X₃ ≤ X := by omega
  have hx4 : X₄ ≤ X := by omega
  have hx5 : X₅ ≤ X := by omega
  obtain ⟨P, E, hP, hE, hgood, hup⟩ := hX₁ X hx1
  refine ⟨P, hP, fun N hN => ?_⟩
  obtain ⟨hL, hw⟩ := hX₅ X hx5
  have hL0 : 0 ≤ Lg X := by linarith
  have hLk : 0 ≤ Lg X ^ k := by positivity
  obtain ⟨hN1, hN2, -, hN4⟩ := evenJ_nat131 hN
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsm : ∀ ν ∈ tuples131 k X, 6 * tuplePower131 ν ≤ X := by
    intro ν hν
    have := tuplePower_le131 hν
    have h6 : 6 * (k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) =
        6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by ring
    omega
  have hle : ∀ ν ∈ tuples131 k X, tuplePower131 ν ≤ N := by
    intro ν hν
    have := hsm ν hν
    omega
  have hwin : ∀ ν ∈ tuples131 k X, N - tuplePower131 ν ∈ evenWindow131 X := fun ν hν =>
    window_mem131 hN (hsm ν hν) (tuplePower_even131 hν)
  set Bad := (tuples131 k X).filter
    (fun ν => ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν)) with hBad
  have hsplit : |∑ ν ∈ tuples131 k X, binaryMajor131 X (N - tuplePower131 ν) P -
      ∑ ν ∈ tuples131 k X, ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)| ≤
      η * ∑ ν ∈ tuples131 k X, ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) +
        (A + 1) * N * ∑ ν ∈ Bad, Sing (N - tuplePower131 ν) := by
    refine split_bound131 (tuples131 k X)
      (fun ν => ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν))
      (fun ν => binaryMajor131 X (N - tuplePower131 ν) P)
      (fun ν => ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν))
      (fun ν => Sing (N - tuplePower131 ν)) η ((A + 1) * N) hη.le
      (mul_nonneg hA1.le hNr)
      (fun ν _ => mul_nonneg (Nat.cast_nonneg _) (Sing_nonneg131 _))
      (fun ν _ => Sing_nonneg131 _) ?_ ?_
    · intro ν hν hb
      have h := hgood _ (hwin ν hν) (not_not.mp hb)
      have e : η * ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) =
          η * (((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)) := by ring
      rw [e] at h
      exact h
    · intro ν hν _
      show |binaryMajor131 X (N - tuplePower131 ν) P -
          ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)| ≤
        (A + 1) * N * Sing (N - tuplePower131 ν)
      have hu := abs_le.mp (hup _ (hwin ν hν))
      have hS := Sing_nonneg131 (N - tuplePower131 ν)
      have hn : ((N - tuplePower131 ν : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le _ _
      have hn0 : (0 : ℝ) ≤ ((N - tuplePower131 ν : ℕ) : ℝ) := Nat.cast_nonneg _
      have h0 := mul_nonneg hn0 hS
      have h1 : A * ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) ≤
          A * N * Sing (N - tuplePower131 ν) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hA) hS
      have h2 : ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) ≤
          N * Sing (N - tuplePower131 ν) := mul_le_mul_of_nonneg_right hn hS
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
  have hjj := hX₂ X hx2 E hE N hN Bad (filter_subset _ _) (fun ν hν => (mem_filter.mp hν).2)
  have hc3 := hX₃ X hx3 N hN
  have hc1 := hX₄ X hx4 N hN
  rw [← major_expand131 k X N P hle] at hsplit
  set W := ∑ ν ∈ tuples131 k X,
    ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) with hW
  set M := majorContribution131 k X N P with hM
  have hNL : 0 ≤ (N : ℝ) * Lg X ^ k := mul_nonneg hNr hLk
  have hcoef : coefficient131 k N * N * Lg X ^ k ≤ B * ((N : ℝ) * Lg X ^ k) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (coefficient_le131 hk N) hNL
  have hWup : W ≤ (B + 1) * ((N : ℝ) * Lg X ^ k) := by
    have := (abs_le.mp hc1).2
    nlinarith
  have hterm1 : η * W ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    have h := mul_le_mul_of_nonneg_left hWup hη.le
    have he : η * ((B + 1) * ((N : ℝ) * Lg X ^ k)) = ε / 3 * ((N : ℝ) * Lg X ^ k) := by
      rw [hηdef]
      field_simp
    rw [he] at h
    exact h
  have hterm2 : (A + 1) * N * ∑ ν ∈ Bad, Sing (N - tuplePower131 ν) ≤
      ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    have h := mul_le_mul_of_nonneg_left hjj (mul_nonneg hA1.le hNr)
    have he : (A + 1) * N * (ε / (3 * (A + 1)) * Lg X ^ k) =
        ε / 3 * ((N : ℝ) * Lg X ^ k) := by
      field_simp
    rw [he] at h
    exact h
  have hfin := abs_sub_le M W (coefficient131 k N * N * Lg X ^ k)
  have hc3' : |W - coefficient131 k N * N * Lg X ^ k| ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    calc _ ≤ _ := hc3
      _ = _ := by ring
  calc _ ≤ _ := hfin
    _ ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) + ε / 3 * ((N : ℝ) * Lg X ^ k) +
        ε / 3 * ((N : ℝ) * Lg X ^ k) := by linarith
    _ = ε * N * Lg X ^ k := by ring

end

end LeanLab.LPZ2007
