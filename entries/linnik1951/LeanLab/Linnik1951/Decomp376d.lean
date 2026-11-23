module

public import LeanLab.Linnik1951.Decomp357b
public import LeanLab.Linnik1951.Weights442

/-!
P0093 pages 165 to 168. Separate the local expansion from its relative correction.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 168 left side of equation 10.7 without its implicit
constant. This is the nonnegative logarithmic relative correction,
retaining the finite singular coefficient at each residual. -/
noncomputable def majorRelative376 (k N : ℕ) : ℝ :=
  ∑ ν ∈ residualTuples357 k N,
    ((N - ∑ i, 2 ^ (ν i).val : ℕ) : ℝ) /
      Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ) ^ 2 *
      (1 / Real.sqrt (Real.log (N - ∑ i, 2 ^ (ν i).val : ℕ))) *
      |truncatedSingular357 N (N - ∑ i, 2 ^ (ν i).val)|


/-- LEAF. P0093 page 168 equation 10.7. The logarithmic relative
correction is negligible compared with scale for fixed k. This arithmetic
summation has no GRH or Mellin hypothesis and contains no arc integral. -/
theorem major_relative_negligible376 (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      majorRelative376 k N ≤ ε * scale111 k N := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A : ℝ := 1 / Real.log 2 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  let D : ℝ := A ^ k * Real.log 2 ^ (k - 2)
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨Nw, hw⟩ := truncated_relative_weight442 (ε / D) (by positivity)
  refine ⟨max 3 Nw, ?_⟩
  intro N _ hN
  have hNw : Nw < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN3 : (3 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNp : (0 : ℝ) < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3).le
  have hl : 0 < Real.log N := by linarith
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
  have hcard : ((residualTuples357 k N).card : ℝ) ≤ (A * Real.log N) ^ k := by
    have hh : ((residualTuples357 k N).card : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ k := by
      exact_mod_cast residual_card_bound357 k N
    exact hh.trans hbox
  have hpow : Real.log N ^ k = Real.log N ^ (k - 2) * Real.log N ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ k)]
  unfold majorRelative376
  calc
    _ ≤ ∑ _ν ∈ residualTuples357 k N, (ε / D) * (N : ℝ) / Real.log N ^ 2 := by
      apply Finset.sum_le_sum
      intro ν hν
      have hm := (Finset.mem_filter.mp hν).2
      exact hw N hNw _ hm.2.1 (Nat.sub_le _ _) hm.2.2
    _ = ((residualTuples357 k N).card : ℝ) * ((ε / D) * (N : ℝ) / Real.log N ^ 2) := by simp
    _ ≤ (A * Real.log N) ^ k * ((ε / D) * (N : ℝ) / Real.log N ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ε * scale111 k N := by
      dsimp [D, scale111]
      rw [mul_pow, div_pow, hpow]
      field_simp [hA.ne', hl2.ne', hl.ne']
      <;> ring

end LeanLab.Linnik1951
