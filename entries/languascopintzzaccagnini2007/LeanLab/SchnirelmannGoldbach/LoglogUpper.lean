module

public import LeanLab.Romanov.SingProd
public import LeanLab.SchnirelmannExplicit.Constants

/-!
A uniform log-log upper bound supporting Brun 1919, page 127, display 12.
This uses the existing proved Mertens input through Romanov.SingProd.
It is a lab derivation with explicit constants. AI wrote the Lean code.
Goldbach is open.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LeanLab.SchnirelmannGoldbach

/-- A numerical log-log envelope for the singular product, valid from n = 3. -/
theorem singProd_le_loglog (n : ℕ) (hn : 3 ≤ n) :
    singProd n ≤ Real.exp 13 * (Real.log (Real.log n) + 2) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 1 ≤ Real.log (n : ℝ) :=
    (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < n)).mpr
      (Real.exp_one_lt_three.le.trans hnR)
  have hpow : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by
    exact_mod_cast LeanLab.Romanov.two_pow_card_le n (by omega)
  have hω := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hω
  have hω0 : (0 : ℝ) ≤ n.primeFactors.card := Nat.cast_nonneg _
  have hω2 : (n.primeFactors.card : ℝ) ≤ 2 * Real.log n := by
    nlinarith [Real.log_two_gt_d9]
  let y : ℕ := ⌈2 * Real.log (n : ℝ)⌉₊
  have hylo : 2 * Real.log (n : ℝ) ≤ y := Nat.le_ceil _
  have hy2 : 2 ≤ y := by
    have : (2 : ℝ) ≤ y := by linarith
    exact_mod_cast this
  have hωy : n.primeFactors.card ≤ y := by exact_mod_cast hω2.trans hylo
  have hyhi : (y : ℝ) ≤ 3 * Real.log n := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log (n : ℝ) by linarith)
    change (y : ℝ) < 2 * Real.log (n : ℝ) + 1 at h
    linarith
  have hlogy : Real.log (y : ℝ) ≤ Real.log (Real.log n) + 2 := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < y by omega)) hyhi
    rw [Real.log_mul (by norm_num) (by linarith : Real.log (n : ℝ) ≠ 0)] at h
    have h3 : Real.log (3 : ℝ) ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    linarith
  exact (LeanLab.Romanov.singProd_le_log n y hy2 hωy).trans
    (mul_le_mul_of_nonneg_left hlogy (Real.exp_pos 13).le)

/-- A log-log upper bound with the existing explicit S1 constant. -/
theorem r_le_loglog (n : ℕ) (hn : 3 ≤ n) :
    (r n : ℝ) ≤ LeanLab.SchnirelmannExplicit.C1 * Real.exp 13 * n /
      (Real.log n) ^ 2 * (Real.log (Real.log n) + 2) := by
  have h := LeanLab.SchnirelmannExplicit.S1u_explicit n hn n
    (mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hC : 0 < LeanLab.SchnirelmannExplicit.C1 := by
    norm_num [LeanLab.SchnirelmannExplicit.C1]
  calc (r n : ℝ) ≤ LeanLab.SchnirelmannExplicit.C1 * n / Real.log n ^ 2 * singProd n := h
    _ ≤ LeanLab.SchnirelmannExplicit.C1 * n / Real.log n ^ 2 *
        (Real.exp 13 * (Real.log (Real.log n) + 2)) :=
      mul_le_mul_of_nonneg_left (singProd_le_loglog n hn) (by positivity)
    _ = _ := by ring

/-- Numeric control of the doubling and cubic log-log losses from x = 4. -/
theorem loglog_double_envelope (x : ℝ) (hx : 4 ≤ x) :
    1 / 4 ≤ Real.log (Real.log x) ∧
      Real.log (Real.log (2 * x)) + 2 ≤ 256 * (Real.log (Real.log x)) ^ 3 := by
  have hx0 : 0 < x := by linarith
  have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at h4
  have hL : 4 / 3 ≤ Real.log x := by linarith [Real.log_two_gt_d9]
  have hL0 : 0 < Real.log x := by linarith
  have hinv : (Real.log x)⁻¹ ≤ (3 / 4 : ℝ) := by
    calc (Real.log x)⁻¹ ≤ (4 / 3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hL
      _ = 3 / 4 := by norm_num
  have hT : 1 / 4 ≤ Real.log (Real.log x) := by
    have h := Real.one_sub_inv_le_log_of_pos hL0
    linarith
  have hlog2x : Real.log (2 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show 2 ≤ x by linarith)
    linarith
  have h2x0 : 0 < Real.log (2 * x) := Real.log_pos (by linarith)
  have hT2 : Real.log (Real.log (2 * x)) ≤ Real.log (Real.log x) + 1 := by
    have h := Real.log_le_log h2x0 hlog2x
    rw [Real.log_mul (by norm_num) hL0.ne'] at h
    linarith [Real.log_two_lt_d9]
  have hpoly : Real.log (Real.log x) + 3 ≤ 256 * (Real.log (Real.log x)) ^ 3 := by
    set t := Real.log (Real.log x)
    have ht : 0 ≤ t := by dsimp [t]; linarith
    have hmul : 0 ≤ (t - 1 / 4) * (256 * t ^ 2 + 64 * t + 15) :=
      mul_nonneg (by dsimp [t]; linarith) (by positivity)
    nlinarith
  exact ⟨hT, by linarith⟩

/-- Brun display 12 with a fully numerical coefficient in the ordered convention. -/
theorem brun12_explicit (x : ℕ) (hx : 4 ≤ x) :
    (r (2 * x) : ℝ) ≤ 28471323072636126720 * x / (Real.log x) ^ 2 *
      (Real.log (Real.log x)) ^ 3 := by
  have hxR : (4 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : 1 ≤ Real.log (x : ℝ) :=
    (Real.le_log_iff_exp_le hx0).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have hL0 : 0 < Real.log (x : ℝ) := by linarith
  have hcmp : Real.log (x : ℝ) ≤ Real.log (2 * (x : ℝ)) :=
    Real.log_le_log hx0 (by linarith)
  have hT2 : 0 ≤ Real.log (Real.log (2 * (x : ℝ))) + 2 := by
    have h := Real.log_nonneg (hL.trans hcmp)
    linarith
  have henv := loglog_double_envelope (x : ℝ) hxR
  have hT : 0 ≤ Real.log (Real.log (x : ℝ)) := by linarith [henv.1]
  have hC : 0 < LeanLab.SchnirelmannExplicit.C1 := by
    norm_num [LeanLab.SchnirelmannExplicit.C1]
  have he : Real.exp (13 : ℝ) ≤ (3 : ℝ) ^ 13 := by
    calc Real.exp (13 : ℝ) = Real.exp ((13 : ℕ) * 1) := by norm_num
      _ = (Real.exp 1) ^ 13 := Real.exp_nat_mul 1 13
      _ ≤ (3 : ℝ) ^ 13 := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 13
  have hcoef : 512 * LeanLab.SchnirelmannExplicit.C1 * Real.exp 13 ≤
      (28471323072636126720 : ℝ) := by
    calc 512 * LeanLab.SchnirelmannExplicit.C1 * Real.exp 13
        ≤ 512 * LeanLab.SchnirelmannExplicit.C1 * (3 : ℝ) ^ 13 :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by norm_num [LeanLab.SchnirelmannExplicit.C1]
  have h := r_le_loglog (2 * x) (by omega)
  push_cast at h
  calc (r (2 * x) : ℝ)
      ≤ LeanLab.SchnirelmannExplicit.C1 * Real.exp 13 * (2 * x) /
          (Real.log (2 * x)) ^ 2 * (Real.log (Real.log (2 * x)) + 2) := h
    _ ≤ LeanLab.SchnirelmannExplicit.C1 * Real.exp 13 * (2 * x) /
          (Real.log x) ^ 2 * (Real.log (Real.log (2 * x)) + 2) := by
        gcongr
    _ ≤ LeanLab.SchnirelmannExplicit.C1 * Real.exp 13 * (2 * x) /
          (Real.log x) ^ 2 * (256 * (Real.log (Real.log x)) ^ 3) :=
        mul_le_mul_of_nonneg_left henv.2 (by positivity)
    _ = (512 * LeanLab.SchnirelmannExplicit.C1 * Real.exp 13) * x /
          (Real.log x) ^ 2 * (Real.log (Real.log x)) ^ 3 := by ring
    _ ≤ 28471323072636126720 * x / (Real.log x) ^ 2 *
          (Real.log (Real.log x)) ^ 3 := by gcongr

end LeanLab.SchnirelmannGoldbach




