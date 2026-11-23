module

public import LeanLab.LanguascoPintzZaccagnini2007.WeightedPairs131

/-!
P0045 display 3 on page 3. Counting the exponent tuples discarded by truncation.
The counting argument follows the paper and the earlier LPZ2007.Eq3Reduce proof.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- Exponent tuples in [1,M]^k from display 3. -/
def exponentTuples131 (k M : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ => Icc 1 M)

/-- The inner weighted count for a fixed exponent tuple in display 3. -/
def tuplePair131 {k : ℕ} (X N : ℕ) (ν : Fin k → ℕ) : ℝ :=
  ∑ m₁ ∈ Icc 1 X, ∑ m₂ ∈ Icc 1 X,
    if m₁ + m₂ + ∑ i, 2 ^ ν i = N then Λ m₁ * Λ m₂ else 0

/-- Removing the zero term from the natural sum does not change the weighted count. -/
theorem range_sum_positive131 {β : Type*} [AddCommMonoid β] (f : ℕ → β) (h0 : f 0 = 0) (n : ℕ) :
    ∑ m ∈ range (n + 1), f m = ∑ m ∈ Icc 1 n, f m := by
  rw [Finset.range_eq_Ico, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_eq_sum_Ico_succ_bot (by omega), h0, zero_add]

/-- The full count is the sum of the inner counts over all exponent tuples. -/
theorem Rpp_tuple_sum131 (k X N : ℕ) :
    Rpp k X N = ∑ ν ∈ exponentTuples131 k (Lp X), tuplePair131 X N ν := by
  unfold Rpp
  rw [range_sum_positive131 _ (by simp) X]
  have he : ∀ m₁ : ℕ,
      (∑ m₂ ∈ range (X + 1),
        ∑ ν ∈ exponentTuples131 k (Lp X),
          if m₁ + m₂ + ∑ i, 2 ^ ν i = N then Λ m₁ * Λ m₂ else (0 : ℝ)) =
      ∑ m₂ ∈ Icc 1 X, ∑ ν ∈ exponentTuples131 k (Lp X),
        if m₁ + m₂ + ∑ i, 2 ^ ν i = N then Λ m₁ * Λ m₂ else (0 : ℝ) := by
    intro m₁
    apply range_sum_positive131
    simp
  change (∑ m₁ ∈ Icc 1 X, ∑ m₂ ∈ range (X + 1),
    ∑ ν ∈ exponentTuples131 k (Lp X),
      if m₁ + m₂ + ∑ i, 2 ^ ν i = N then Λ m₁ * Λ m₂ else (0 : ℝ)) = _
  simp_rw [he]
  unfold tuplePair131
  exact (sum_congr rfl (fun _ _ => sum_comm)).trans sum_comm

/-- The truncated exponent tuples are a subset of the full ones. -/
theorem exponentTuples_subset131 (k X : ℕ) :
    exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊ ⊆ exponentTuples131 k (Lp X) := by
  intro ν hν
  have hf : ⌊Lg X - Real.sqrt (Lg X)⌋₊ ≤ Lp X :=
    Nat.floor_mono (by linarith [Real.sqrt_nonneg (Lg X)])
  simp only [exponentTuples131, Fintype.mem_piFinset, mem_Icc] at hν ⊢
  intro i
  exact ⟨(hν i).1, (hν i).2.trans hf⟩

/-- The truncation difference is exactly the sum over discarded tuples. -/
theorem discarded_tuple_identity131 (k X N : ℕ) :
    Rpp k X N - truncatedCount131 k X N =
      ∑ ν ∈ exponentTuples131 k (Lp X) \
        exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊, tuplePair131 X N ν := by
  rw [Rpp_tuple_sum131]
  have he : truncatedCount131 k X N =
      ∑ ν ∈ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊, tuplePair131 X N ν :=
    (sum_congr rfl (fun _ _ => sum_comm)).trans sum_comm
  rw [he, ← sum_sdiff (exponentTuples_subset131 k X)]
  ring

/-- Each discarded tuple has nonnegative weight bounded by the uniform weighted pair envelope. -/
theorem tuplePair_bound131 {k X N : ℕ} (hN : 3 ≤ N) (ν : Fin k → ℕ) :
    0 ≤ tuplePair131 X N ν ∧
      tuplePair131 X N ν ≤ pairConstant131 * N * (Real.log (Real.log N) + 2) := by
  have hn0 : 0 ≤ tuplePair131 X N ν := by
    apply sum_nonneg
    intro m₁ _
    apply sum_nonneg
    intro m₂ _
    split_ifs
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
    · exact le_rfl
  refine ⟨hn0, ?_⟩
  by_cases hp : ∑ i, 2 ^ ν i ≤ N
  · have he : tuplePair131 X N ν = weightedPair131 X (N - ∑ i, 2 ^ ν i) := by
      apply sum_congr rfl
      intro m₁ _
      apply sum_congr rfl
      intro m₂ _
      have he : (m₁ + m₂ + ∑ i, 2 ^ ν i = N) ↔ (m₁ + m₂ = N - ∑ i, 2 ^ ν i) := by omega
      simp only [he]
    rw [he]
    exact weightedPair_upper131 X (Nat.sub_le _ _) hN
  · have hz : tuplePair131 X N ν = 0 := by
      apply sum_eq_zero
      intro m₁ _
      apply sum_eq_zero
      intro m₂ _
      rw [ite_eq_right (by omega)]
    rw [hz]
    have hC : 0 ≤ pairConstant131 := by unfold pairConstant131; norm_num [LeanLab.SchnirelmannExplicit.C1]; positivity
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlog1 : 1 ≤ Real.log N :=
      (Real.le_log_iff_exp_le hN0).mpr (Real.exp_one_lt_three.le.trans (by exact_mod_cast hN))
    have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hlog1
    positivity

/-- The number of exponent tuples is M^k. -/
theorem exponentTuples_card131 (k M : ℕ) : (exponentTuples131 k M).card = M ^ k := by
  simp [exponentTuples131, Fintype.card_piFinset]

/-- Display 3: at most 2k L^(k-1/2) tuples are discarded once L >= 1. -/
theorem discarded_tuple_card131 {k X : ℕ} (hk : 1 ≤ k) (hL : 1 ≤ Lg X) :
    (((exponentTuples131 k (Lp X) \
      exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊).card) : ℝ) ≤
        2 * k * Lg X ^ ((k : ℝ) - 1 / 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let M := Lp X
  let m := ⌊Lg X - Real.sqrt (Lg X)⌋₊
  have hmM : m ≤ M := Nat.floor_mono (by linarith [Real.sqrt_nonneg (Lg X)])
  have hML : (M : ℝ) ≤ Lg X := Nat.floor_le (by linarith)
  have hmL : Lg X - Real.sqrt (Lg X) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMm : (0 : ℝ) ≤ M - m := sub_nonneg.mpr (by exact_mod_cast hmM)
  have hdiff : (M : ℝ) - m ≤ Real.sqrt (Lg X) + 1 := by linarith
  have hsqrt : 1 ≤ Real.sqrt (Lg X) := Real.one_le_sqrt.mpr hL
  have hp := abs_pow_sub_pow_le (a := (M : ℝ)) (b := (m : ℝ)) (n := j + 1)
  have hpow : (m : ℝ) ^ (j + 1) ≤ (M : ℝ) ^ (j + 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hmM) _
  simp only [abs_of_nonneg (sub_nonneg.mpr hpow), abs_of_nonneg hMm,
    abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M), abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
    max_eq_left (by exact_mod_cast hmM : (m : ℝ) ≤ M), Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hp
  rw [card_sdiff_of_subset (exponentTuples_subset131 (j + 1) X), exponentTuples_card131,
    exponentTuples_card131, Nat.cast_sub (Nat.pow_le_pow_left hmM _)]
  push_cast
  change (M : ℝ) ^ (j + 1) - (m : ℝ) ^ (j + 1) ≤ _
  have hL0 : 0 < Lg X := by linarith
  have he : Lg X ^ (((j : ℝ) + 1) - 1 / 2) = Real.sqrt (Lg X) * Lg X ^ j := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hL0]
    congr 1
    ring
  rw [he]
  calc (M : ℝ) ^ (j + 1) - (m : ℝ) ^ (j + 1)
      ≤ ((M : ℝ) - m) * (j + 1) * (M : ℝ) ^ j := hp
    _ ≤ (Real.sqrt (Lg X) + 1) * (j + 1) * Lg X ^ j := by gcongr
    _ ≤ (2 * Real.sqrt (Lg X)) * (j + 1) * Lg X ^ j := by gcongr; linarith
    _ = _ := by ring

/-- Display 3: the discarded weighted tuples satisfy an explicit log-log error bound. -/
theorem discarded_weight_bound131 {k X N : ℕ} (hk : 1 ≤ k) (hL : 1 ≤ Lg X) (hN : 3 ≤ N) :
    |Rpp k X N - truncatedCount131 k X N| ≤
      2 * k * pairConstant131 * N * Lg X ^ ((k : ℝ) - 1 / 2) * (Real.log (Real.log N) + 2) := by
  rw [discarded_tuple_identity131]
  have h0 : 0 ≤ ∑ ν ∈ exponentTuples131 k (Lp X) \
      exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊, tuplePair131 X N ν :=
    sum_nonneg (fun ν _ => (tuplePair_bound131 hN ν).1)
  rw [abs_of_nonneg h0]
  have hs := sum_le_card_nsmul
    (exponentTuples131 k (Lp X) \ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊)
    (tuplePair131 X N) (pairConstant131 * N * (Real.log (Real.log N) + 2))
    (fun ν _ => (tuplePair_bound131 hN ν).2)
  rw [nsmul_eq_mul] at hs
  have hC : 0 ≤ pairConstant131 := by unfold pairConstant131; norm_num [LeanLab.SchnirelmannExplicit.C1]; positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog1 : 1 ≤ Real.log N :=
    (Real.le_log_iff_exp_le hN0).mpr (Real.exp_one_lt_three.le.trans (by exact_mod_cast hN))
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hlog1
  calc _ ≤ (((exponentTuples131 k (Lp X) \ exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊).card) : ℝ) *
        (pairConstant131 * N * (Real.log (Real.log N) + 2)) := hs
    _ ≤ (2 * k * Lg X ^ ((k : ℝ) - 1 / 2)) *
        (pairConstant131 * N * (Real.log (Real.log N) + 2)) :=
      mul_le_mul_of_nonneg_right (discarded_tuple_card131 hk hL) (by positivity)
    _ = _ := by ring

/-- Display 3: the discarded count is o(N L^k), from the proved lab sieve bound. -/
theorem truncation_tail_proved131 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |Rpp k X N - truncatedCount131 k X N| ≤ ε * N * Lg X ^ k := by
  have ht : Tendsto (fun X : ℕ => (Lg X) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop)
  obtain ⟨X₀, hX₀⟩ := (ht.eventually_ge_atTop (12 * k * pairConstant131 / ε)).exists_forall_of_atTop
  refine ⟨max X₀ 6, fun X hX N hN => ?_⟩
  have hX6 : 6 ≤ X := by omega
  obtain ⟨hNX, _, hNJ⟩ := mem_filter.mp hN
  have hNle : N ≤ X := (mem_Icc.mp hNX).2
  have hN3 : 3 ≤ N := by
    have hXr : (6 : ℝ) ≤ X := by exact_mod_cast hX6
    have hNr : (3 : ℝ) ≤ N := by linarith
    exact_mod_cast hNr
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hL1 : 1 ≤ Lg X := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ X by exact_mod_cast (by omega : 2 ≤ X))
    simpa [Lg] using h
  have hL0 : 0 < Lg X := by linarith
  have hlogN0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogX : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hlogXL : Real.log X ≤ Lg X := by
    unfold Lg
    rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith [mul_nonneg hlogX (sub_nonneg.mpr (show Real.log 2 ≤ 1 by linarith [Real.log_two_lt_d9]))]
  have hlogNL : Real.log N ≤ Lg X :=
    (Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast hNle)).trans hlogXL
  have hLL : Real.log (Real.log N) ≤ Real.log (Lg X) := Real.log_le_log hlogN0 hlogNL
  have hlogL : Real.log (Lg X) ≤ 4 * Lg X ^ ((1 : ℝ) / 4) := by
    have := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have hroot1 : 1 ≤ Lg X ^ ((1 : ℝ) / 4) := Real.one_le_rpow hL1 (by norm_num)
  have hLLroot : Real.log (Real.log N) + 2 ≤ 6 * Lg X ^ ((1 : ℝ) / 4) := by linarith
  have hcoeff : 12 * k * pairConstant131 ≤ ε * Lg X ^ ((1 : ℝ) / 4) := by
    have h := (div_le_iff₀ hε).mp (hX₀ X (by omega))
    linarith
  have hC : 0 ≤ pairConstant131 := by unfold pairConstant131; norm_num [LeanLab.SchnirelmannExplicit.C1]; positivity
  have hpow : Lg X ^ ((k : ℝ) - 1 / 2) * Lg X ^ ((1 : ℝ) / 4) =
      Lg X ^ ((k : ℝ) - 1 / 4) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have hpow' : Lg X ^ ((1 : ℝ) / 4) * Lg X ^ ((k : ℝ) - 1 / 4) = Lg X ^ k := by
    rw [← Real.rpow_add hL0, show (1 : ℝ) / 4 + ((k : ℝ) - 1 / 4) = k by ring, Real.rpow_natCast]
  calc |Rpp k X N - truncatedCount131 k X N|
      ≤ 2 * k * pairConstant131 * N * Lg X ^ ((k : ℝ) - 1 / 2) *
          (Real.log (Real.log N) + 2) := discarded_weight_bound131 hk hL1 hN3
    _ ≤ 2 * k * pairConstant131 * N * Lg X ^ ((k : ℝ) - 1 / 2) *
          (6 * Lg X ^ ((1 : ℝ) / 4)) := mul_le_mul_of_nonneg_left hLLroot (by positivity)
    _ = (12 * k * pairConstant131) * N * Lg X ^ ((k : ℝ) - 1 / 4) := by rw [← hpow]; ring
    _ ≤ (ε * Lg X ^ ((1 : ℝ) / 4)) * N * Lg X ^ ((k : ℝ) - 1 / 4) := by gcongr
    _ = ε * N * Lg X ^ k := by rw [show ε * Lg X ^ ((1 : ℝ) / 4) * N * Lg X ^ ((k : ℝ) - 1 / 4) =
          ε * N * (Lg X ^ ((1 : ℝ) / 4) * Lg X ^ ((k : ℝ) - 1 / 4)) by ring, hpow']

end

end LeanLab.LPZ2007
