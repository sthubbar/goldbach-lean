module

public import LeanLab.Linnik1951.Data357
public import LeanLab.Linnik1951.Decomp357i
public import LeanLab.Linnik1951.Asymptotics357
public import LeanLab.Linnik1951.Decomp376a

/-!
P0093 page 168 equations 10.5 and 10.6. Arithmetic tail and logarithmic tuple count.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 168 after equation 10.7. Positive exponent tuples with
positive even residual, exactly as in the existing main term. -/
noncomputable def residualTuples357 (k N : ℕ) : Finset (Fin k → Fin (N + 1)) := by
  classical
  exact Finset.univ.filter fun ν => (∀ i, 1 ≤ (ν i).val) ∧
    2 ≤ N - ∑ i, 2 ^ (ν i).val ∧ Even (N - ∑ i, 2 ^ (ν i).val)

/-- P0093 page 166 before equation 8.2. Every exponent of a contributing
tuple is at most the integer base two logarithm of N. -/
theorem residual_exponent_le357 (k N : ℕ) (ν : Fin k → Fin (N + 1))
    (hν : ν ∈ residualTuples357 k N) (i : Fin k) : (ν i).val ≤ Nat.log 2 N := by
  classical
  have hm := (Finset.mem_filter.mp hν).2
  have hs : ∑ j, 2 ^ (ν j).val ≤ N := by omega
  have hi : 2 ^ (ν i).val ≤ ∑ j, 2 ^ (ν j).val :=
    Finset.single_le_sum (f := fun j : Fin k => 2 ^ (ν j).val) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  exact Nat.le_log_of_pow_le (by norm_num) (hi.trans hs)

/-- P0093 page 166 before equation 8.2. The bounded exponent tuples
inject into the full logarithmic box. -/
theorem residual_card_bound357 (k N : ℕ) :
    (residualTuples357 k N).card ≤ (Nat.log 2 N + 1) ^ k := by
  classical
  let f : {ν // ν ∈ residualTuples357 k N} → (Fin k → Fin (Nat.log 2 N + 1)) :=
    fun ν i => ⟨(ν.val i).val, Nat.lt_succ_of_le (residual_exponent_le357 k N ν.val ν.property i)⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun g => (g i).val) h
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hc

/-- P0093 page 168 equation 10.6. A residual weight is bounded by the
common upper weight N over log squared 2. -/
theorem residual_weight_upper357 (n N : ℕ) (hn : 2 ≤ n) (hnN : n ≤ N) :
    (n : ℝ) / Real.log n ^ 2 ≤ (N : ℝ) / Real.log 2 ^ 2 := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ n by exact_mod_cast hn)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : Real.log 2 ^ 2 ≤ Real.log n ^ 2 := by nlinarith
  calc
    _ ≤ (n : ℝ) / Real.log 2 ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hnN) (by positivity)

/-- LEAF. P0093 page 168 equations 10.5 and 10.6. The finite Ramanujan
series differs from the Euler product by a uniform negative power of N for
positive even residuals at most N. Saving one hundredth weakens the printed
two hundredths. This leaf has no tuple or circle method integral. -/
theorem singular_tail357 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |truncatedSingular357 N n - singularSeries111 n| ≤
          C * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
  exact singular_tail_decomposed376

/-- P0093 page 168 equations 10.5 and 10.6. A pointwise coefficient tail
bounds the total error by its constant bound times the logarithmic box size. -/
theorem truncated_error_card357 (k N : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hTail : ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
      |truncatedSingular357 N n - singularSeries111 n| ≤ D) :
    |truncatedMain357 k N - mainTerm111 k N| ≤
      ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ k * D * ((N : ℝ) / Real.log 2 ^ 2) := by
  classical
  let S := residualTuples357 k N
  let w : (Fin k → Fin (N + 1)) → ℝ :=
    fun ν => (N - ∑ i, 2 ^ (ν i).val : ℕ) / Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2
  have heq : truncatedMain357 k N - mainTerm111 k N =
      ∑ ν ∈ S, (truncatedSingular357 N (N - ∑ i, 2 ^ (ν i).val) -
        singularSeries111 (N - ∑ i, 2 ^ (ν i).val)) * w ν := by
    unfold truncatedMain357 mainTerm111
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ν hν
    dsimp [w]
    ring
  rw [heq]
  calc
    _ ≤ ∑ ν ∈ S, |(truncatedSingular357 N (N - ∑ i, 2 ^ (ν i).val) -
        singularSeries111 (N - ∑ i, 2 ^ (ν i).val)) * w ν| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ν ∈ S, D * ((N : ℝ) / Real.log 2 ^ 2) := by
      apply Finset.sum_le_sum
      intro ν hν
      have hm := (Finset.mem_filter.mp hν).2
      rw [abs_mul, abs_of_nonneg (show 0 ≤ w ν by dsimp [w]; positivity)]
      exact mul_le_mul (hTail _ hm.2.1 (Nat.sub_le _ _) hm.2.2)
        (residual_weight_upper357 _ N hm.2.1 (Nat.sub_le _ _))
        (by dsimp [w]; positivity) hD
    _ = (S.card : ℝ) * (D * ((N : ℝ) / Real.log 2 ^ 2)) := by simp
    _ ≤ _ := by
      have hc : (S.card : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ k := by
        exact_mod_cast residual_card_bound357 k N
      calc
        _ ≤ (((Nat.log 2 N + 1 : ℕ) : ℝ) ^ k) * (D * ((N : ℝ) / Real.log 2 ^ 2)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by ring

/-- P0093 page 168 equation 10.6. Exact truncated_to_main357 statement,
CONDITIONAL only on the pointwise arithmetic singular tail leaf. -/
theorem truncated_to_main_from_tail357 (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |truncatedMain357 k N - mainTerm111 k N| ≤ ε * scale111 k N := by
  obtain ⟨C, hC, Nt, ht⟩ := singular_tail357
  let A := 1 / Real.log 2 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨Ne, he⟩ := power_saving_negligible357 (A ^ k * C / Real.log 2 ^ 2)
    (1 / 100) (by positivity) (by norm_num) k ε hε
  obtain ⟨Nl, hl⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨max 2 (max Nt (max Ne Nl)), ?_⟩
  intro N hev hN
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have htN : Nt < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have heN : Ne < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hlN : Nl < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hlR : (Nl : ℝ) < (N : ℝ) := by exact_mod_cast hlN
  have hlog : 1 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos _) (hl.trans hlR).le
    simpa only [Real.log_exp] using h
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
    have hp : (2 : ℝ) ^ Nat.log 2 N ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    have hh := Real.log_le_log (pow_pos (by norm_num) _) hp
    rw [Real.log_pow] at hh
    exact (le_div_iff₀ hl2).mpr hh
  have hbox : ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ k ≤ (A * Real.log N) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    dsimp [A]
    rw [add_mul, one_div_mul_eq_div]
    linarith
  have hscale : (N : ℝ) ≤ scale111 k N := by
    have hr : 1 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hl2).mpr
      (by simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ N by exact_mod_cast h2.le))
    exact le_mul_of_one_le_right hpos.le (one_le_pow₀ hr)
  have hb := truncated_error_card357 k N (C * (N : ℝ) ^ (-(1 / 100 : ℝ))) (by positivity) (ht N htN)
  have hp : (N : ℝ) ^ (-(1 / 100 : ℝ)) * N = (N : ℝ) ^ (1 - (1 / 100 : ℝ)) := by
    calc
      _ = (N : ℝ) ^ (-(1 / 100 : ℝ)) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ (-(1 / 100 : ℝ) + 1) := (Real.rpow_add hpos _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ (A * Real.log N) ^ k * (C * (N : ℝ) ^ (-(1 / 100 : ℝ))) *
        ((N : ℝ) / Real.log 2 ^ 2) := hb.trans (by gcongr)
    _ = (A ^ k * C / Real.log 2 ^ 2) * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) * Real.log N ^ k := by
      rw [mul_pow, ← hp]
      ring
    _ ≤ ε * N := he N heN
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale hε.le

end LeanLab.Linnik1951
