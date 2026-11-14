module

public import LeanLab.Romanov.GallagherBridge

/-!
# The remaining HBP Sigma1 target

AI wrote the Lean code. Known mathematics. HBP arXiv math/0201299v2,
pages 2, 13 and 16, displays 21 and 27. The main bound is stated as a Prop.
The elementary remainder bounds prevent a zero denominator convention from hiding a gap.
Binary Goldbach is OPEN.
-/

@[expose] public section


noncomputable section
namespace LeanLab.Romanov

open Finset Real
open LeanLab.Linnik.U1434Lemma21 (sv sv_le)

/-- Sigma1 counts exponent tuples with multiplicity, as in HBP display 21. -/
def sigmaOne (K N L : ℕ) : ℝ :=
  ∑ ν : Fin K → Fin L, ((N - sv ν : ℕ) : ℝ) / (Nat.totient (N - sv ν) : ℝ)

/-- HBP display 27 in its K at least nine application. Cited, not proved here. -/
def HBPSigmaOneBound : Prop :=
  ∀ K : ℕ, 9 ≤ K → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 * K ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → Even N →
      sigmaOne K N (Nat.log 2 (N / (2 * K))) ≤ C * Real.log N ^ K

/-- Under the paper's truncation, every remainder is positive and at least N divided by two. -/
theorem sigmaOne_remainder_bounds (K N L : ℕ) (hN0 : 0 < N)
    (hN : 2 * (K * 2 ^ L) ≤ N) (ν : Fin K → Fin L) :
    0 < N - sv ν ∧ N ≤ 2 * (N - sv ν) ∧ N - sv ν ≤ N := by
  have hs := sv_le ν
  omega

/-- The elementary pointwise bound loses a factor N compared with display 27. -/
theorem sigmaOne_basic_upper (K N L : ℕ) : sigmaOne K N L ≤ N * (L : ℝ) ^ K := by
  unfold sigmaOne
  calc ∑ ν : Fin K → Fin L, ((N - sv ν : ℕ) : ℝ) / (Nat.totient (N - sv ν) : ℝ)
      ≤ ∑ _ν : Fin K → Fin L, (N : ℝ) := by
        apply sum_le_sum
        intro ν _
        by_cases hn : N - sv ν = 0
        · simp [hn]
        have hp : 0 < Nat.totient (N - sv ν) := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
        have hp1 : (1 : ℝ) ≤ Nat.totient (N - sv ν) := by exact_mod_cast hp
        calc ((N - sv ν : ℕ) : ℝ) / Nat.totient (N - sv ν)
            ≤ ((N - sv ν : ℕ) : ℝ) / 1 :=
              div_le_div_of_nonneg_left (by positivity) (by norm_num) hp1
          _ ≤ N := by simpa only [div_one] using (Nat.cast_le.mpr (Nat.sub_le N (sv ν)) :
            ((N - sv ν : ℕ) : ℝ) ≤ N)
    _ = N * (L : ℝ) ^ K := by simp [mul_comm]

/-- The natural logarithm cutoff in the cited target enforces the paper's truncation. -/
theorem sigmaOne_paper_cutoff (K N : ℕ) (hK : 0 < K) (hN : 2 * K ≤ N) :
    2 * (K * 2 ^ Nat.log 2 (N / (2 * K))) ≤ N := by
  have hd : 0 < N / (2 * K) := Nat.div_pos hN (by omega)
  have hp := Nat.pow_log_le_self 2 hd.ne'
  have hm := Nat.mul_le_mul_left (2 * K) hp
  have hdiv := Nat.div_mul_le_self N (2 * K)
  nlinarith

end LeanLab.Romanov
