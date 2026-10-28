module

public import LeanLab.BS2022GRH.Theorem3LiPV
public import LeanLab.BS2022GRH.U7153Lemma10

/-!
BS2022GRH, P0021, unit U-7153: Theorem 3 and Corollary 1 with Lemma 10 discharged.
`U7153.lemma10` proves Chen's weighted inequality for every natural N ≥ 2^24, so the
hypothesis `h10` of `theorem3_of_nat` is removed: Theorem 3 for N = n natural is now
CONDITIONAL ON Theorems 5, 6, 7 at the Section 5.4 parameters only, stated for the concrete
sifting functions S(A,P,z), Σ_{z ≤ q < y} S(A_q,P,z), S(B,P,y) and π₂(N) of `U7153Lemma10`.

AI-written Lean code, Claude, session MANUAL-N1, unit U-7153. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH
open Real

lemma two_pow_24_le {X₂ N : ℝ} (hX : exp (exp 15.85) ≤ X₂) (hN : X₂ ≤ N) : (2 : ℝ) ^ 24 ≤ N := by
  obtain ⟨hL, hN0⟩ := logN_ge hX hN
  have e1 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have e2 : (2 : ℝ) ^ 24 ≤ exp 1 ^ 24 := pow_le_pow_left₀ (by norm_num) e1 24
  rw [← exp_nat_mul] at e2
  have e3 : exp ((24 : ℕ) * 1) ≤ exp (log N) := exp_le_exp.2 (by push_cast; linarith)
  rw [exp_log hN0] at e3
  linarith

/-- **Theorem 3 for a natural number `N = n`, CONDITIONAL** ON Theorems 5, 6, 7 at the
Section 5.4 parameters only; Lemma 10, the li input and `U_N ≥ 1` are PROVED. Here
`S0 = S(A,P,z)`, `S6 = Σ_{z ≤ q < y} S(A_q,P,z)`, `SB = S(B,P,y)` and `π₂(N)` are the
concrete counts of `U7153Lemma10`, with `z = N^{1/8}`, `y = N^{1/3}`. -/
theorem theorem3_of_nat_L10 {X₂ : ℝ} {n : ℕ} (hX : exp (exp 15.85) ≤ X₂)
    (hN : X₂ ≤ (n : ℝ))
    (h5 : 8 * (UN n * (n : ℝ) / log (n : ℝ) ^ 2) * thm5Bracket α0 (exp eulerMascheroniConstant)
          (1 / 8137) 114 LeanLab.ChenExplicit.twinC (cG X₂) X₂ (n : ℝ) < (U7153.SA n : ℝ))
    (h6 : ∑ q ∈ U7153.Qset n, (U7153.SAq n q : ℝ) ≤ 8 * (UN n * (n : ℝ) / log (n : ℝ) ^ 2) *
          thm6Bracket α0 (exp eulerMascheroniConstant) (1 / 8137)
          112 LeanLab.ChenExplicit.twinC (cG X₂) X₂ (n : ℝ))
    (h7 : (U7153.SB n : ℝ) ≤ UN n * (n : ℝ) / log (n : ℝ) ^ 2 * thm7Bracket α0
          (exp eulerMascheroniConstant) (1 / 8137) 112
          LeanLab.ChenExplicit.twinC LeanLab.ChenExplicit.BJS.cbar 1e-20
          (mL9 (qG ((1 + 1e-20) * (n : ℝ) ^ (1 / 8 : ℝ))) ((n : ℝ) ^ (2 / 3 : ℝ))
            ((1 + 1e-20) * (n : ℝ) ^ (1 / 8 : ℝ)) (sqrt (n : ℝ) / log (n : ℝ) ^ 5))
          (liPV ((n : ℝ) ^ (1 / 3 : ℝ))) (n : ℝ)) :
    4e-4 * (UN n * (n : ℝ) / log (n : ℝ) ^ 2) < (U7153.pi2 n : ℝ) :=
  theorem3_of_nat hX hN (U7153.lemma10 n (two_pow_24_le hX hN)) h5 h6 h7


end LeanLab.BS2022GRH
