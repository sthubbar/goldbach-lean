module

public import LeanLab.Linnik.LiLiu2026

/-!
AI-written Lean code, Claude, 2026-10-19, run 20261019T1703Z-20733, unit U-1086, T2 FRONTIER, I-0073.
Li, Liu, arXiv 2610.15784 v1, read in Claude in Chrome. Chain from the cited inputs to the two
sufficient conditions (58) and (65), building on LiLiu2026.lean.
- `diag22`: (16) and (22) from the values the paper cites: B₁₁ = 1 + A₁₁ = C₀R₀ with Platt and
  Trudgian's C₀R₀ < 1.2784421041, and Johnston-Trudgian Section 3.1's A(2) ≤ 0.05549,
  A(3) ≤ 0.013598, the Khalfalah-Pintz diagonal averages, give A₁₁ < 0.279, A₂₂ < 0.0555,
  A₃₃ < 0.0136. The identification of JT's A(k) with the diagonal A_kk is the paper's citation.
- `tail23`: inequality (23), vᵀTv ≤ (Σ |v_i| √T_ii)², for any real T with |T_ij| ≤ √(T_ii T_jj).
- `vAv_lt`, `wAw_4vAv_lt`: (60) and (66) for A = A_* + T from the tail bounds.
- `k6_of_cited`, `k5_of_cited`: (58) and (65) hold, CONDITIONAL ON C₀R₀ < 1.2784421041,
  JT's A(2), A(3), C₁ = 6.7814 and the positive semidefinite tail; the region maxima and
  I(λ) are proved in LiLiu2026.lean.
Goldbach is open.
-/

@[expose] public section

open Real

namespace LeanLab.Linnik.LiLiu

/-- (16) and (22) from the cited constants. -/
theorem diag22 {CR A22 A33 : ℝ} (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549)
    (hJT3 : A33 ≤ 0.013598) : CR < 1.279 ∧ CR - 1 < 0.279 ∧ A22 < 0.0555 ∧ A33 < 0.0136 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num at * <;> linarith

/-- (23): the tail quadratic form is at most (Σ |v_i| √T_ii)². -/
theorem tail23 (T : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j)) :
    ∑ i, ∑ j, x i * T i j * x j ≤ (∑ i, |x i| * √(T i i)) ^ 2 := by
  have key : ∀ i j, x i * T i j * x j ≤ (|x i| * √(T i i)) * (|x j| * √(T j j)) := by
    intro i j
    calc x i * T i j * x j ≤ |x i * T i j * x j| := le_abs_self _
      _ = |x i| * |T i j| * |x j| := by rw [abs_mul, abs_mul]
      _ ≤ |x i| * (√(T i i) * √(T j j)) * |x j| := by
          gcongr; exact hT i j
      _ = _ := by ring
  calc ∑ i, ∑ j, x i * T i j * x j ≤ ∑ i, ∑ j, (|x i| * √(T i i)) * (|x j| * √(T j j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, |x i| * √(T i i)) ^ 2 := by rw [sq, Finset.sum_mul_sum]

/-- The real quadratic form of A_* at a rational vector, cast. -/
lemma qf_cast (x : Fin 3 → ℚ) :
    (∑ i, ∑ j, (x i : ℝ) * (Astar i j : ℝ) * (x j : ℝ)) = ((qf Astar x : ℚ) : ℝ) := by
  simp [qf]

lemma sqrt_lt_of {t c : ℝ} (hc : 0 ≤ c) (h : t < c ^ 2) : √t ≤ c := by
  rcases le_or_gt t 0 with h0 | h0
  · rw [Real.sqrt_eq_zero'.2 h0]; exact hc
  · rw [Real.sqrt_le_left hc]; exact h.le

/-- (60): vᵀAv < 13/500 for A = A_* + T, from the tail bounds of Section 3. -/
theorem vAv_lt (T : Fin 3 → Fin 3 → ℝ) (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (h1 : T 0 0 < 0.254 ^ 2) (h2 : T 1 1 < 0.077 ^ 2) (h3 : T 2 2 < 0.04 ^ 2) :
    ∑ i, ∑ j, ((v i : ℝ)) * ((Astar i j : ℝ) + T i j) * (v j : ℝ) < 13 / 500 := by
  have hs : ∑ i, ∑ j, ((v i : ℝ)) * ((Astar i j : ℝ) + T i j) * (v j : ℝ) =
      ((qf Astar v : ℚ) : ℝ) + ∑ i, ∑ j, (v i : ℝ) * T i j * (v j : ℝ) := by
    rw [← qf_cast, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs, vAv_star]
  have ht := tail23 T (fun i => (v i : ℝ)) hT
  have s1 := sqrt_lt_of (by norm_num) h1
  have s2 := sqrt_lt_of (by norm_num) h2
  have s3 := sqrt_lt_of (by norm_num) h3
  have hb : (∑ i, |(v i : ℝ)| * √(T i i)) ≤ 0.254 / 16 + 0.077 / 4 + 0.04 := by
    simp [Fin.sum_univ_three, v]
    norm_num
    linarith
  have h0 : 0 ≤ ∑ i, |(v i : ℝ)| * √(T i i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have : (∑ i, |(v i : ℝ)| * √(T i i)) ^ 2 ≤ (0.254 / 16 + 0.077 / 4 + 0.04) ^ 2 :=
    pow_le_pow_left₀ h0 hb 2
  push_cast; norm_num at this ⊢; linarith

/-- **(58) from the cited inputs.** With Platt-Trudgian's C₀R₀, JT's A(2) and A(3), C₁ = 6.7814
and a tail T with |T_ij| ≤ √(T_ii T_jj), the sufficient condition (58) for six powers holds,
for every H ≥ 0 below 2/15, which `region61` supplies for the maximum over D_{5/6}. -/
theorem k6_of_cited {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (Astar 2 2 : ℝ) + T 2 2 = A33) {H : ℝ} (hH0 : 0 ≤ H) (hH : H < 2 / 15) :
    (∑ i, ∑ j, ((v i : ℝ)) * ((Astar i j : ℝ) + T i j) * (v j : ℝ)) +
      11 * (1 / 16) ^ 2 * Real.log 2 / 50 + H * ((6.7814 - 2) / 2 * CR + 7 * Real.log 2 / 25)
      < (1 - 1 / 4 - 1 / 16) ^ 2 := by
  obtain ⟨hCR, h11, h22, h33⟩ := diag22 hPT hJT2 hJT3
  have e1 : (Astar 0 0 : ℝ) = 1/8 + 1/64 + 1/27 + 1/32 + 13/2250 := by
    simp [Astar, A3, A5, A7, A15, A31]
  have e2 : (Astar 1 1 : ℝ) = 1/32 + 1/1024 + 2/243 + 1/128 + 77/56250 := by
    simp [Astar, A3, A5, A7, A15, A31]
  have e3 : (Astar 2 2 : ℝ) = 1/128 + 1/16384 + 4/2187 + 1/512 + 499/1406250 := by
    simp [Astar, A3, A5, A7, A15, A31]
  rw [e1] at hA11; rw [e2] at hA22; rw [e3] at hA33
  have hv := vAv_lt T hT (by norm_num at *; linarith) (by norm_num at *; linarith) (by norm_num at *; linarith)
  have := k6_criterion hCR0 hCR hH0 hH hv
  norm_num at this ⊢; linarith

/-- **(65) from the cited inputs**, five powers on GRH, with τ = 2, c = 1/8, for every H ≥ 0
below 41/60, which `region67` supplies; the wᵀAw + 4vᵀAv input is (66). -/
theorem k5_of_cited {CR WA : ℝ} (hCR0 : 0 ≤ CR) (hPT : CR < 1.2784421041) (hWA : WA < 37 / 200)
    {H : ℝ} (hH0 : 0 ≤ H) (hH : H < 41 / 60) :
    WA + 1 / 32 * Real.log 2 / 4 + H * ((6.7814 - 2) / 2 * CR + Real.log 2 / 4)
      < 2 * 2 * (1 - 1 / 8) * (1 - 1 / 4 - 1 / 16) := by
  have := k5_criterion hCR0 (by linarith) hH0 hH hWA
  norm_num at this ⊢; linarith

/-- Vacuity of `k6_of_cited`: T = 0 with CR = 1 + (A_*)₁₁ meets every hypothesis. -/
theorem k6_of_cited_vacuity : ∃ CR A22 A33 : ℝ, 0 ≤ CR ∧ CR < 1.2784421041 ∧ A22 ≤ 0.05549 ∧
    A33 ≤ 0.013598 ∧ (Astar 0 0 : ℝ) + 0 = CR - 1 ∧ (Astar 1 1 : ℝ) + 0 = A22 ∧
    (Astar 2 2 : ℝ) + 0 = A33 ∧ (∀ i j : Fin 3, |(0:ℝ)| ≤ √(0:ℝ) * √(0:ℝ)) := by
  refine ⟨1 + (Astar 0 0 : ℝ), Astar 1 1, Astar 2 2, ?_, ?_, ?_, ?_, by ring, by ring, by ring,
    fun _ _ => by simp⟩ <;> simp [Astar, A3, A5, A7, A15, A31] <;> norm_num

end LeanLab.Linnik.LiLiu
