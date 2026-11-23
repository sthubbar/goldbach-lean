module

public import LeanLab.LanguascoPintzZaccagnini2007.PrimeRepresentations131

/-!
P0045 page 3, dyadic covering for the unweighted representation conclusion.
The weighted asymptotic is kept on J. Existence of representations is monotone in X.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- All exceptional even integers at most X for the unweighted count. -/
def allPrimeExceptions131 (k X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun N => Even N ∧ primeRepresentationCount131 k X N = 0)

/-- The exceptional set on J from the local theorem. -/
def localPrimeExceptions131 (k X : ℕ) : Finset ℕ :=
  (evenJ131 X).filter (fun N => primeRepresentationCount131 k X N = 0)

/-- The remaining initial interval after removing J(X). -/
def smallerCutoff131 (X : ℕ) : ℕ := (2 * X - 1) / 3

/-- The remaining interval is strictly shorter when X is positive. -/
theorem smallerCutoff_lt131 {X : ℕ} (hX : 0 < X) : smallerCutoff131 X < X := by
  unfold smallerCutoff131
  omega

/-- Its length is at most two thirds of X. -/
theorem smallerCutoff_le131 (X : ℕ) : (smallerCutoff131 X : ℝ) ≤ 2 / 3 * X := by
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX
    norm_num [smallerCutoff131]
  have hdiv := Nat.cast_div_le (m := 2 * X - 1) (n := 3) (α := ℝ)
  have hsub : 1 ≤ 2 * X := by omega
  push_cast [Nat.cast_sub hsub] at hdiv
  unfold smallerCutoff131
  linarith

/-- Page 3: every exception is in J(X) or in the remaining shorter interval. -/
theorem allPrimeExceptions_subset131 (k X : ℕ) :
    allPrimeExceptions131 k X ⊆
      localPrimeExceptions131 k X ∪ allPrimeExceptions131 k (smallerCutoff131 X) := by
  classical
  intro N hN
  obtain ⟨hNX, hEven, hzero⟩ := mem_filter.mp hN
  obtain ⟨hN1, hNle⟩ := mem_Icc.mp hNX
  by_cases hJ : 2 * (X : ℝ) / 3 ≤ N
  · apply mem_union.mpr
    left
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hNX, hEven, hJ⟩, hzero⟩
  · have h3 : 3 * N < 2 * X := by
      have ht : (3 : ℝ) * N < 2 * X := by linarith
      exact_mod_cast ht
    have hNs : N ≤ smallerCutoff131 X := by unfold smallerCutoff131; omega
    have hsX : smallerCutoff131 X ≤ X := by unfold smallerCutoff131; omega
    have hmono := prime_count_mono131 hsX k N
    apply mem_union.mpr
    right
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hN1, hNs⟩, hEven, by omega⟩

/-- Page 3: the exception counts obey the covering recurrence. -/
theorem allPrimeExceptions_recurrence131 (k X : ℕ) :
    (allPrimeExceptions131 k X).card ≤ (localPrimeExceptions131 k X).card +
      (allPrimeExceptions131 k (smallerCutoff131 X)).card :=
  (card_le_card (allPrimeExceptions_subset131 k X)).trans (card_union_le _ _)

/-- The initial exceptional set has at most X elements. -/
theorem allPrimeExceptions_card_le131 (k X : ℕ) : (allPrimeExceptions131 k X).card ≤ X := by
  exact (card_filter_le _ _).trans (by simp)

/-- Page 3: local exception bounds sum geometrically on the shrinking intervals.
CONDITIONAL on the supplied local exception bound hlocal. -/
theorem allPrimeExceptions_bound131 (k X₀ : ℕ) (hX₀ : 2 ≤ X₀) (K : ℝ) (hK : 0 ≤ K)
    (hlocal : ∀ X : ℕ, X₀ ≤ X → (localPrimeExceptions131 k X).card ≤
      K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10) (X : ℕ) :
    (allPrimeExceptions131 k X).card ≤ X₀ +
      K / (1 - (2 / 3 : ℝ) ^ ((3 : ℝ) / 5)) *
        (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log (max (X : ℝ) 2) ^ 10 := by
  let q := (2 / 3 : ℝ) ^ ((3 : ℝ) / 5)
  let A := K / (1 - q)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  have hA0 : 0 ≤ A := div_nonneg hK (by linarith)
  have heq : K + A * q = A := by
    have h1q : (1 : ℝ) - q ≠ 0 := by linarith
    dsimp [A]
    field_simp
    ring
  change (allPrimeExceptions131 k X).card ≤ X₀ + A * (X : ℝ) ^ ((3 : ℝ) / 5) *
    Real.log (max (X : ℝ) 2) ^ 10
  induction X using Nat.strong_induction_on with
  | h X ih =>
    by_cases hX : X < X₀
    · have hc : ((allPrimeExceptions131 k X).card : ℝ) ≤ X₀ := by
        exact_mod_cast (allPrimeExceptions_card_le131 k X).trans hX.le
      have hp : 0 ≤ A * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log (max (X : ℝ) 2) ^ 10 := by positivity
      linarith
    have hXge : X₀ ≤ X := by omega
    have hX2 : (2 : ℝ) ≤ X := by exact_mod_cast (hX₀.trans hXge)
    have hX0 : 0 < X := by omega
    have hXr : (0 : ℝ) < X := by linarith
    let Y := smallerCutoff131 X
    have hYlt : Y < X := smallerCutoff_lt131 hX0
    have hYbound := smallerCutoff_le131 X
    have hlog : Real.log (max (Y : ℝ) 2) ≤ Real.log X := by
      apply Real.log_le_log (by positivity)
      exact max_le (by exact_mod_cast hYlt.le) hX2
    have hlog0 : 0 ≤ Real.log (max (Y : ℝ) 2) := Real.log_nonneg (by linarith [le_max_right (Y : ℝ) 2])
    have hpow : (Y : ℝ) ^ ((3 : ℝ) / 5) ≤ q * (X : ℝ) ^ ((3 : ℝ) / 5) := by
      calc (Y : ℝ) ^ ((3 : ℝ) / 5) ≤ (2 / 3 * (X : ℝ)) ^ ((3 : ℝ) / 5) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hYbound (by norm_num)
        _ = _ := Real.mul_rpow (by norm_num) hXr.le
    have htail : A * (Y : ℝ) ^ ((3 : ℝ) / 5) * Real.log (max (Y : ℝ) 2) ^ 10 ≤
        A * q * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
      calc _ ≤ A * (q * (X : ℝ) ^ ((3 : ℝ) / 5)) * Real.log X ^ 10 := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hA0)
              (pow_le_pow_left₀ hlog0 hlog 10) (by positivity) (by positivity)
        _ = _ := by ring
    have hi := ih Y hYlt
    have hr : ((allPrimeExceptions131 k X).card : ℝ) ≤
        (localPrimeExceptions131 k X).card + (allPrimeExceptions131 k Y).card := by
      exact_mod_cast allPrimeExceptions_recurrence131 k X
    have hl := hlocal X hXge
    rw [max_eq_left hX2]
    calc (allPrimeExceptions131 k X).card
        ≤ K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 +
          (X₀ + A * q * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10) := by linarith
      _ = X₀ + (K + A * q) * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by ring
      _ = _ := by rw [heq]

/-- Page 3 dyadic argument for prime existence on the whole interval [1,X].
CONDITIONAL on the repaired weighted theorem on J. -/
theorem almost_all_primes_global_of_repaired131 (hm : RepairedMainJ131) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (allPrimeExceptions131 k X).card ≤ C * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
  obtain ⟨K, hK, X₁, hX₁⟩ := almost_all_primes_of_repaired131 hm k hk
  let B := max X₁ 4
  let A := K / (1 - (2 / 3 : ℝ) ^ ((3 : ℝ) / 5))
  have hq1 : (2 / 3 : ℝ) ^ ((3 : ℝ) / 5) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  have hA0 : 0 ≤ A := div_nonneg hK (by linarith)
  refine ⟨A + B, by positivity, B, fun X hX => ?_⟩
  have hX4 : 4 ≤ X := by dsimp [B] at hX; omega
  have hXr : (4 : ℝ) ≤ X := by exact_mod_cast hX4
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < X)).mpr
      (Real.exp_one_lt_three.le.trans (by linarith))
  have hpow1 : 1 ≤ (X : ℝ) ^ ((3 : ℝ) / 5) := Real.one_le_rpow (by linarith) (by norm_num)
  have hscale : 1 ≤ (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
    have hh : 1 ≤ Real.log X ^ 10 := one_le_pow₀ hlog1
    nlinarith
  have hb := allPrimeExceptions_bound131 k B (by dsimp [B]; omega) K hK
    (fun Y hY => hX₁ Y (by dsimp [B] at hY; omega)) X
  rw [max_eq_left (by linarith : (2 : ℝ) ≤ X)] at hb
  change (allPrimeExceptions131 k X).card ≤ (A + B) * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10
  change (allPrimeExceptions131 k X).card ≤ (B : ℝ) + A * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 at hb
  nlinarith [mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg B : (0 : ℝ) ≤ B)]

end

end LeanLab.LPZ2007
