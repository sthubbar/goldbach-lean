module

public import LeanLab.LanguascoPintzZaccagnini2007.Decomp131
public import LeanLab.LanguascoPintzZaccagnini2007.Residues131

/-!
P0045 pages 1 and 2. From the weighted count to prime representations.
The main result here is conditional on the repaired major arc input.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real Filter

noncomputable section

/-- The unweighted prime representation count from pages 1 and 2.
The exponent cutoff is determined by X. A negative residual contributes zero,
since the lab prime pair count at zero is zero. -/
def primeRepresentationCount131 (k X N : ℕ) : ℕ :=
  ∑ ν ∈ exponentTuples131 k (Lp X), LeanLab.SchnirelmannGoldbach.r (N - ∑ i, 2 ^ ν i)

/-- The repaired weighted coefficient is at least 1.3 for every positive k. -/
theorem coefficient_lower131 {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    1.3 ≤ coefficient131 k N := by
  have hC := Ck_ge_one131 hk N
  have hT := LeanLab.ChenExplicit.twinC_ge_065
  unfold coefficient131
  nlinarith

/-- If the unweighted count vanishes, every exponent tuple has no prime pair. -/
theorem prime_count_zero_term131 {k X N : ℕ} (h : primeRepresentationCount131 k X N = 0)
    (ν : Fin k → ℕ) (hν : ν ∈ exponentTuples131 k (Lp X)) :
    LeanLab.SchnirelmannGoldbach.r (N - ∑ i, 2 ^ ν i) = 0 := by
  have ht := single_le_sum (f := fun ν : Fin k → ℕ =>
    LeanLab.SchnirelmannGoldbach.r (N - ∑ i, 2 ^ ν i)) (fun _ _ => Nat.zero_le _) hν
  change LeanLab.SchnirelmannGoldbach.r (N - ∑ i, 2 ^ ν i) ≤ primeRepresentationCount131 k X N at ht
  omega

/-- If there is no prime pair, higher prime powers contribute at most 4 sqrt(X) log(X)^2. -/
theorem convolution_no_prime131 {n X : ℕ} (hn : n ≤ X)
    (hr : LeanLab.SchnirelmannGoldbach.r n = 0) :
    weightedConvolution131 n ≤ 4 * Real.sqrt X * Real.log X ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    simp only [weightedConvolution131, range_zero, sum_empty]
    positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hX1 : (1 : ℝ) ≤ X := hn1.trans (by exact_mod_cast hn)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hlogle : Real.log n ≤ Real.log X := Real.log_le_log (by linarith) (by exact_mod_cast hn)
  have htheta : 0 ≤ Chebyshev.psi n - Chebyshev.theta n := sub_nonneg.mpr (Chebyshev.theta_le_psi (n : ℝ))
  have hpp := Chebyshev.psi_sub_theta_le (x := (n : ℝ)) hn1
  have hs := convolution_prime_power_split131 n
  rw [hr] at hs
  simp only [Nat.cast_zero, mul_zero, zero_add] at hs
  calc weightedConvolution131 n ≤ 2 * Real.log n * (Chebyshev.psi n - Chebyshev.theta n) := hs
    _ ≤ 2 * Real.log X * (2 * Real.sqrt X * Real.log X) := by
      gcongr
      calc _ ≤ 2 * Real.sqrt n * Real.log n := hpp
        _ ≤ _ := by gcongr
    _ = _ := by ring

/-- A tuple with no prime representation has only the higher prime power error. -/
theorem tuplePair_no_prime131 {k X N : ℕ} (hN : N ≤ X)
    (ν : Fin k → ℕ) (hr : LeanLab.SchnirelmannGoldbach.r (N - ∑ i, 2 ^ ν i) = 0) :
    tuplePair131 X N ν ≤ 4 * Real.sqrt X * Real.log X ^ 2 := by
  by_cases hp : ∑ i, 2 ^ ν i ≤ N
  · have he : tuplePair131 X N ν = weightedPair131 X (N - ∑ i, 2 ^ ν i) := by
      apply sum_congr rfl
      intro m₁ _
      apply sum_congr rfl
      intro m₂ _
      have he : (m₁ + m₂ + ∑ i, 2 ^ ν i = N) ↔ (m₁ + m₂ = N - ∑ i, 2 ^ ν i) := by omega
      simp only [he]
    rw [he]
    exact (weightedPair_le_convolution131 X _).trans
      (convolution_no_prime131 ((Nat.sub_le _ _).trans hN) hr)
  · have hz : tuplePair131 X N ν = 0 := by
      apply sum_eq_zero
      intro m₁ _
      apply sum_eq_zero
      intro m₂ _
      rw [ite_eq_right (by omega)]
    rw [hz]
    positivity

/-- The full weighted count without prime representations is only a prime power error. -/
theorem Rpp_no_prime131 {k X N : ℕ} (hN : N ≤ X) (hL : 0 ≤ Lg X)
    (hr : primeRepresentationCount131 k X N = 0) :
    Rpp k X N ≤ 4 * Real.sqrt X * Real.log X ^ 2 * Lg X ^ k := by
  rw [Rpp_tuple_sum131]
  have hs := sum_le_card_nsmul (exponentTuples131 k (Lp X)) (tuplePair131 X N)
    (4 * Real.sqrt X * Real.log X ^ 2)
    (fun ν hν => tuplePair_no_prime131 hN ν (prime_count_zero_term131 hr ν hν))
  rw [nsmul_eq_mul, exponentTuples_card131] at hs
  have hfloor : (Lp X : ℝ) ≤ Lg X := Nat.floor_le hL
  have hpow : ((Lp X : ℝ) ^ k) ≤ Lg X ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor k
  push_cast at hs
  nlinarith [mul_le_mul_of_nonneg_right hpow (show (0 : ℝ) ≤ 4 * Real.sqrt X * Real.log X ^ 2 by positivity)]

/-- The higher prime power contribution is eventually at most X/3. -/
theorem prime_power_error_small131 :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → 4 * Real.sqrt X * Real.log X ^ 2 ≤ (X : ℝ) / 3 := by
  have ht : Tendsto (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  obtain ⟨X₀, hX₀⟩ := (ht.eventually_ge_atTop 768).exists_forall_of_atTop
  refine ⟨max X₀ 2, fun X hX => ?_⟩
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hlog : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hl : Real.log X ≤ 8 * (X : ℝ) ^ ((1 : ℝ) / 8) := by
    have := Real.log_le_rpow_div hX0.le (by norm_num : (0 : ℝ) < 1 / 8)
    linarith
  have hq : ((X : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 = (X : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    norm_num
  have hl2 : Real.log X ^ 2 ≤ 64 * (X : ℝ) ^ ((1 : ℝ) / 4) := by
    calc Real.log X ^ 2 ≤ (8 * (X : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 := pow_le_pow_left₀ hlog hl 2
      _ = _ := by rw [mul_pow, hq]; norm_num
  have hp : Real.sqrt X * (X : ℝ) ^ ((1 : ℝ) / 4) * (X : ℝ) ^ ((1 : ℝ) / 4) = X := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    norm_num
  have hg := mul_le_mul_of_nonneg_left (hX₀ X (by omega))
    (show (0 : ℝ) ≤ Real.sqrt X * (X : ℝ) ^ ((1 : ℝ) / 4) by positivity)
  have hlogbound := mul_le_mul_of_nonneg_left hl2 (show (0 : ℝ) ≤ 4 * Real.sqrt X by positivity)
  nlinarith

/-- CONDITIONAL on the repaired weighted main theorem. Almost every even N in J
has a representation by two primes and k powers of two, as on pages 1 and 2. -/
theorem almost_all_primes_of_repaired131 (hm : RepairedMainJ131) (k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((evenJ131 X).filter (fun N => primeRepresentationCount131 k X N = 0)).card : ℝ) ≤
        K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
  classical
  obtain ⟨K, hK, hη⟩ := hm k hk
  obtain ⟨X₁, hX₁⟩ := hη (1 / 2) (by norm_num)
  obtain ⟨X₂, hX₂⟩ := prime_power_error_small131
  refine ⟨K, hK, max 2 (max X₁ X₂), fun X hX => ?_⟩
  have hX2 : 2 ≤ X := by omega
  have hL : 0 < Lg X := Real.logb_pos (by norm_num) (by exact_mod_cast hX2)
  refine le_trans ?_ (hX₁ X (by omega))
  apply Nat.cast_le.mpr
  apply card_le_card
  intro N hN
  obtain ⟨hNJ, hzero⟩ := mem_filter.mp hN
  refine mem_filter.mpr ⟨hNJ, ?_⟩
  obtain ⟨hNX, _, hlower⟩ := mem_filter.mp hNJ
  have hN1 : 1 ≤ N := (mem_Icc.mp hNX).1
  have hNle : N ≤ X := (mem_Icc.mp hNX).2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hscale : 0 < (N : ℝ) * Lg X ^ k := mul_pos hNpos (pow_pos hL k)
  have hR := Rpp_no_prime131 hNle hL.le hzero
  have he := hX₂ X (by omega)
  have hR' : Rpp k X N ≤ 1 / 2 * N * Lg X ^ k := by
    have hmul := mul_le_mul_of_nonneg_right he (pow_nonneg hL.le k)
    have hNXr : (X : ℝ) / 3 ≤ N / 2 := by linarith
    have hm := mul_le_mul_of_nonneg_right hNXr (pow_nonneg hL.le k)
    nlinarith
  have hc := mul_le_mul_of_nonneg_right (coefficient_lower131 hk N) hscale.le
  have ha : coefficient131 k N * N * Lg X ^ k - Rpp k X N ≤
      |Rpp k X N - coefficient131 k N * N * Lg X ^ k| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  nlinarith

/-- A concrete zero count instance: 2 cannot be two primes plus a positive number of powers of two. -/
theorem prime_count_two131 (k : ℕ) (hk : 1 ≤ k) : primeRepresentationCount131 k 2 2 = 0 := by
  unfold primeRepresentationCount131
  apply sum_eq_zero
  intro ν hν
  let i : Fin k := ⟨0, by omega⟩
  have hν1 : 1 ≤ ν i := (mem_Icc.mp ((Fintype.mem_piFinset.mp hν) i)).1
  have hp : 2 ≤ 2 ^ ν i := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ν i := Nat.pow_le_pow_right (by norm_num) hν1
  have hs : 2 ^ ν i ≤ ∑ j, 2 ^ ν j := single_le_sum (f := fun j : Fin k => 2 ^ ν j) (fun _ _ => Nat.zero_le _) (mem_univ i)
  rw [show 2 - ∑ j, 2 ^ ν j = 0 by omega]
  simp [LeanLab.SchnirelmannGoldbach.r]

/-- A nonempty family of prime representations: two primes 2 and k copies of 2. -/
theorem prime_count_positive_family131 (k : ℕ) :
    0 < primeRepresentationCount131 k (2 * k + 4) (2 * k + 4) := by
  let X := 2 * k + 4
  let ν : Fin k → ℕ := fun _ => 1
  have hLg : 1 ≤ Lg X := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ X by exact_mod_cast (by dsimp [X]; omega))
    simpa [Lg] using h
  have hLp : 1 ≤ Lp X := by
    apply Nat.le_floor
    simpa using hLg
  have hν : ν ∈ exponentTuples131 k (Lp X) := by
    rw [exponentTuples131, Fintype.mem_piFinset]
    intro i
    exact mem_Icc.mpr ⟨le_rfl, hLp⟩
  have ht := single_le_sum (f := fun ν : Fin k → ℕ =>
    LeanLab.SchnirelmannGoldbach.r (X - ∑ i, 2 ^ ν i)) (fun _ _ => Nat.zero_le _) hν
  have hsum : ∑ i : Fin k, 2 ^ ν i = 2 * k := by simp [ν, mul_comm]
  change LeanLab.SchnirelmannGoldbach.r (X - ∑ i, 2 ^ ν i) ≤ primeRepresentationCount131 k X X at ht
  rw [hsum, show X - 2 * k = 4 by dsimp [X]; omega] at ht
  have hr : 1 ≤ LeanLab.SchnirelmannGoldbach.r 4 := by
    apply card_pos.mpr
    refine ⟨2, ?_⟩
    norm_num
  change 0 < primeRepresentationCount131 k X X
  omega

/-- The natural count is positive exactly when the paper prime representation exists. -/
theorem prime_count_pos_iff131 (k X N : ℕ) :
    0 < primeRepresentationCount131 k X N ↔
      ∃ (p q : ℕ) (ν : Fin k → ℕ), p.Prime ∧ q.Prime ∧
        ν ∈ exponentTuples131 k (Lp X) ∧ p + q + ∑ i, 2 ^ ν i = N := by
  classical
  constructor
  · intro h
    have hex : ∃ ν ∈ exponentTuples131 k (Lp X),
        0 < LeanLab.SchnirelmannGoldbach.r (N - ∑ i, 2 ^ ν i) := by
      by_contra hn
      push Not at hn
      have hz : primeRepresentationCount131 k X N = 0 :=
        sum_eq_zero (fun ν hν => Nat.eq_zero_of_le_zero (hn ν hν))
      omega
    obtain ⟨ν, hν, hr⟩ := hex
    obtain ⟨p, hp⟩ := card_pos.mp hr
    obtain ⟨hpn, hp, hq⟩ := mem_filter.mp hp
    have hpN := mem_range.mp hpn
    refine ⟨p, (N - ∑ i, 2 ^ ν i) - p, ν, hp, hq, hν, ?_⟩
    have hp2 := hp.two_le
    omega
  · rintro ⟨p, q, ν, hp, hq, hν, he⟩
    have hres : N - ∑ i, 2 ^ ν i = p + q := by omega
    have hr : 0 < LeanLab.SchnirelmannGoldbach.r (N - ∑ i, 2 ^ ν i) := by
      apply card_pos.mpr
      refine ⟨p, mem_filter.mpr ⟨mem_range.mpr ?_, hp, ?_⟩⟩
      · have := hq.two_le
        omega
      · have heq : (N - ∑ i, 2 ^ ν i) - p = q := by omega
        rwa [heq]
    have ht := single_le_sum (f := fun ν : Fin k → ℕ =>
      LeanLab.SchnirelmannGoldbach.r (N - ∑ i, 2 ^ ν i)) (fun _ _ => Nat.zero_le _) hν
    change LeanLab.SchnirelmannGoldbach.r (N - ∑ i, 2 ^ ν i) ≤ primeRepresentationCount131 k X N at ht
    omega

/-- Enlarging the exponent cutoff parameter cannot remove a prime representation. -/
theorem prime_count_mono131 {X Y : ℕ} (hXY : X ≤ Y) (k N : ℕ) :
    primeRepresentationCount131 k X N ≤ primeRepresentationCount131 k Y N := by
  have hLp : Lp X ≤ Lp Y := by
    by_cases hX : X = 0
    · simp [hX, Lp, Lg]
    · apply Nat.floor_mono
      exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast (by omega : 0 < X))
        (by exact_mod_cast hXY)
  apply sum_le_sum_of_subset_of_nonneg
  · intro ν hν
    simp only [exponentTuples131, Fintype.mem_piFinset, mem_Icc] at hν ⊢
    intro i
    exact ⟨(hν i).1, (hν i).2.trans hLp⟩
  · intro _ _ _
    exact Nat.zero_le _

end

end LeanLab.LPZ2007
