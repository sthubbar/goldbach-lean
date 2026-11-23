module

public import LeanLab.LanguascoPintzZaccagnini2007.Decomp131b

/-!
P0045 page 3 and display 23. A finite odd modulus for the coefficient.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The product of the odd squarefree d < D needed in the page 3 remark.
A product suffices. No least common multiple is claimed. -/
def residueModulus131 (D : ℕ) : ℕ := ∏ d ∈ (range D).filter OddSqf, d

/-- The finite modulus from the page 3 remark is odd and positive. -/
theorem residueModulus_odd131 (D : ℕ) : Odd (residueModulus131 D) := by
  classical
  apply Finset.prod_induction
  · intro a b ha hb
    exact ha.mul hb
  · exact odd_one
  · intro d hd
    exact (mem_filter.mp hd).2.2.1

/-- Each residue required on page 3 is determined by the single finite modulus. -/
theorem small_dvd_residueModulus131 {D d : ℕ} (hd : d < D) (hs : OddSqf d) :
    d ∣ residueModulus131 D := by
  classical
  exact dvd_prod_of_mem _ (mem_filter.mpr ⟨mem_range.mpr hd, hs⟩)

/-- A single congruence makes the finite sums of display 23 agree. -/
theorem partialC_periodic131 (D k N M : ℕ)
    (h : (residueModulus131 D : ℤ) ∣ (N : ℤ) - M) :
    partialC131 D k N = partialC131 D k M := by
  apply partialC_congr131
  intro d hd hs
  exact (Int.natCast_dvd_natCast.mpr (small_dvd_residueModulus131 hd hs)).trans h

/-- Page 3: one odd modulus controls the variation of C(k,N) to within epsilon.
The same modulus works for every positive k. -/
theorem coefficient_modulus131 (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℕ, Odd q ∧ ∀ k : ℕ, 1 ≤ k → ∀ N M : ℕ,
      (q : ℤ) ∣ (N : ℤ) - M → |Ck k N - Ck k M| < ε := by
  obtain ⟨D, hD⟩ := coefficient_tail_small131 ε hε
  refine ⟨residueModulus131 D, residueModulus_odd131 D, fun k hk N M h => ?_⟩
  obtain ⟨hN0, hN⟩ := hD k hk N
  obtain ⟨hM0, hM⟩ := hD k hk M
  rw [← partialC_periodic131 D k N M h] at hM0 hM
  exact equal_partial_error131 hN0 hN hM0 hM

/-- The d = 1 term of display 23 is exactly one. -/
theorem Ckterm_one131 (k N : ℕ) : Ckterm k N 1 = 1 := by
  simp [Ckterm, oddSqf_1, fd_one, xi_1, jcount]

/-- The lower bound on the coefficient in the theorem, from display 23. -/
theorem Ck_ge_one131 {k : ℕ} (hk : 1 ≤ k) (N : ℕ) : 1 ≤ Ck k N := by
  have h := (Ck_summable hk N).sum_le_tsum ({1} : Finset ℕ)
    (fun d _ => Ckterm_nonneg k N d)
  simpa only [sum_singleton, Ckterm_one131, Ck] using h

/-- Displays 19, 23 and 26: C(k,N) is bounded by the Romanov series. -/
theorem Ck_le_series131 {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    Ck k N ≤ ∑' d, seriesTerm d := by
  exact Summable.tsum_le_tsum (Ckterm_le hk N) (Ck_summable hk N) lemma61_proved

/-- CONDITIONAL on the cited Khalfallah and Pintz numerical bound.
The uncorrected coefficient C(k,N) lies in [1,1.9378], as used on pages 2 and 9. -/
theorem Ck_bounds_of_bound131 (hb : Lemma61Bound) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    1 ≤ Ck k N ∧ Ck k N ≤ 1.9378 := by
  exact ⟨Ck_ge_one131 hk N, (Ck_le_series131 hk N).trans hb⟩

/-- Page 9: the elementary convergence bound already in the lab is too weak
to supply the cited numerical bound 1.9378. This is a negative bound comparison. -/
theorem coarse_bound_insufficient131 : (1.9378 : ℝ) < 8 * log 2 * exp 27 := by
  have hl : (1 : ℝ) / 2 ≤ log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have he := Real.add_one_le_exp (27 : ℝ)
  have hh : (0 : ℝ) ≤ 8 * log 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left he hh]

end

end LeanLab.LPZ2007
