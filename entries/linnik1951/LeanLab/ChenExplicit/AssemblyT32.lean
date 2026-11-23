module

public import LeanLab.ChenExplicit.AssemblyT

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6713, track T2.
`BJS3At_of_sieveBounds32`: AssemblyT323.lean of cloud46 U-6602 with the threshold hypothesis
`32.3 ≤ t` relaxed to `32 ≤ t`; the proof is copied unchanged, since it uses the threshold only
through `e^{32} ≥ 6·10¹³` and `3·10¹⁵ L² ≤ e^{L/8}` for `L ≥ e^{32}`.
Chen's theorem is not in doubt; Goldbach is open.
-/

@[expose] public section

open Finset Real
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

noncomputable section
namespace LeanLab.ChenExplicit

lemma exp_32_gt : (6 * 10 ^ 13 : ℝ) ≤ exp 32 := by
  have := exp_one_gt_d9
  have e : exp 32 = exp 1 ^ 32 := by rw [exp_one_pow]; norm_num
  have h1 : exp 32 ≤ exp 32 := le_rfl
  have h2 : (2.7182818283 : ℝ) ^ 32 ≤ exp 1 ^ 32 := pow_le_pow_left₀ (by norm_num) this.le 32
  have h3 : (6 * 10 ^ 13 : ℝ) ≤ (2.7182818283 : ℝ) ^ 32 := by norm_num
  linarith

lemma big_exp32 (L : ℝ) (hL : exp 32 ≤ L) : 3 * 10 ^ 15 * L ^ 2 ≤ exp (L / 8) := by
  have hL6 := exp_32_gt
  have hL0 : 0 ≤ L / 8 := by linarith
  have h := Real.pow_div_factorial_le_exp (L / 8) hL0 4
  have hf : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at h
  have hL2 : (36 * 10 ^ 26 : ℝ) ≤ L ^ 2 := by nlinarith
  have : 3 * 10 ^ 15 * L ^ 2 ≤ (L / 8) ^ 4 / 24 := by
    have : (L / 8) ^ 4 / 24 = L ^ 2 * L ^ 2 / 98304 := by ring
    rw [this, le_div_iff₀ (by norm_num)]
    nlinarith [sq_nonneg L]
  linarith

theorem BJS3At_of_sieveBounds32 (t : ℝ) (ht : 32 ≤ t) (cA cQ cB : ℕ → ℝ)
    (hA : Thm44At t cA) (hQ : Thm50At t cQ) (hB : Thm51At t cB) (hm : MarginAt t cA cQ cB) :
    BJS3At t := by
  intro N hEven hNt
  have hN : exp (exp 32) < (N : ℝ) :=
    lt_of_le_of_lt (exp_le_exp.mpr (exp_le_exp.mpr ht)) hNt
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  set L := Real.log N with hLdef
  have hL : exp 32 < L := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have hL6 := exp_32_gt
  have hL0 : 0 < L := by linarith
  have hNe : (N : ℝ) = exp L := (exp_log hpos).symm
  have hz : zN N = exp (L / 8) := by
    simp only [zN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hy : yN N = exp (L / 3) := by
    simp only [yN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hz2 : 2 ≤ zN N := by
    rw [hz]; have := add_one_le_exp (L / 8); linarith
  have hy0 : 0 < yN N := by rw [hy]; exact exp_pos _
  have hy3 : (N : ℝ) ≤ yN N ^ 3 := by
    rw [hy, ← exp_nat_mul, hNe]; apply exp_le_exp.mpr; push_cast; linarith
  have hchen := chen_inequality N (zN N) (yN N) hz2 hy0 hy3
  have h1 := hA N hEven hNt
  have h2 := hQ N hEven hNt
  have h3 := hB N hEven hNt
  have hmN := hm N hEven hNt
  have hU := U_ge N
  have hL2 : 0 < L ^ 2 := by positivity
  have hM0 : 0 < mainTerm N := by
    have := U_pos N
    simp only [mainTerm]; positivity
  -- the error terms of Lemma 37
  have hE : 2 * (N : ℝ) / zN N + yN N ≤ 1 / 10 ^ 12 * mainTerm N := by
    have hbig := big_exp32 L hL.le
    have e1 : 2 * (N : ℝ) / zN N = 2 * exp (7 * L / 8) := by
      rw [hz, hNe, mul_div_assoc, ← exp_sub]; ring_nf
    have e2 : yN N ≤ exp (7 * L / 8) := by rw [hy]; exact exp_le_exp.mpr (by linarith)
    have e3 : exp L = exp (7 * L / 8) * exp (L / 8) := by rw [← exp_add]; ring_nf
    have hM : 1 / 1000 * exp L / L ^ 2 ≤ mainTerm N := by
      simp only [mainTerm]; rw [← hLdef, ← hNe]
      apply div_le_div_of_nonneg_right _ hL2.le
      rw [hNe]; exact mul_le_mul_of_nonneg_right hU (exp_pos _).le
    have h7 := exp_pos (7 * L / 8)
    have : 3 * exp (7 * L / 8) ≤ 1 / 10 ^ 12 * (1 / 1000 * exp L / L ^ 2) := by
      rw [e3, show 1 / 10 ^ 12 * (1 / 1000 * (exp (7 * L / 8) * exp (L / 8)) / L ^ 2) =
        exp (7 * L / 8) * exp (L / 8) / (10 ^ 15 * L ^ 2) by ring, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hbig h7.le]
    linarith
  have hfin := mul_le_mul_of_nonneg_right hmN hM0.le
  have hgoal : (2 / 10000 : ℝ) * U N * N / Real.log N ^ 2 = 2 / 10000 * mainTerm N := by
    simp only [mainTerm]; ring
  rw [hgoal]
  nlinarith



end LeanLab.ChenExplicit
