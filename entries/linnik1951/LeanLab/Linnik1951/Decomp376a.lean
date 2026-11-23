module

public import LeanLab.Linnik1951.TailBridge376

/-!
P0093 page 168 equations 10.5 and 10.6. Separate the divisor loss from the tail saving.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- LEAF. P0093 page 168 first inequality in equation 10.5, followed by
identification of the complete series in equation 10.6. The cutoff is
Q equal to N to the one tenth. This retains the divisor count loss and
does not assert any uniform decay as the residual varies. -/
theorem divisor_dependent_tail376 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |truncatedSingular357 N n - singularSeries111 n| ≤
          C * (n.divisors.card : ℝ) * (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
  exact divisor_dependent_tail_proved376

/-- P0093 page 168 equations 10.5 and 10.6. Exact singular_tail357
statement. Both arithmetic inputs now have clean proofs. The proof
retains the residual bound n at most N and the positive even hypotheses. -/
theorem singular_tail_decomposed376 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℕ, 2 ≤ n → n ≤ N → Even n →
        |truncatedSingular357 N n - singularSeries111 n| ≤
          C * (N : ℝ) ^ (-(1 / 100 : ℝ)) := by
  obtain ⟨C, hC, N0, ht⟩ := divisor_dependent_tail376
  obtain ⟨D, hD, hd⟩ := small_power_divisors376
  refine ⟨C * D, mul_pos hC hD, max 1 N0, ?_⟩
  intro N hN n hn hnN hev
  have htN : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hnn : (n : ℝ) ^ (3 / 100 : ℝ) ≤ (N : ℝ) ^ (3 / 100 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hnN) (by norm_num)
  calc
    _ ≤ C * (n.divisors.card : ℝ) * (N : ℝ) ^ (-(1 / 20 : ℝ)) := ht N htN n hn hnN hev
    _ ≤ C * (D * (N : ℝ) ^ (3 / 100 : ℝ)) * (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
      gcongr
      exact (hd n hn).trans (mul_le_mul_of_nonneg_left hnn hD.le)
    _ = (C * D) * ((N : ℝ) ^ (3 / 100 : ℝ) * (N : ℝ) ^ (-(1 / 20 : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (combine_tail_powers376 N hNR) (mul_pos hC hD).le

end LeanLab.Linnik1951
