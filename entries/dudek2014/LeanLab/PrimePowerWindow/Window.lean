module

public import Mathlib
public import LeanLab.Dudek2014.Display
public import LeanLab.PrimePowerWindow.Count

/-!
I-5230, unit U-6601, CLOUD 20261020T1618Z-cloud46: the Schoenfeld step of Dudek 2014 without
Schoenfeld.

Dudek's page 6 display uses Schoenfeld 1976, `0.98 √y < ψ(y) - θ(y) < 1.11 √y + 3 y^{1/3}`,
only through the DIFFERENCE of `ψ - θ` across the window `(x - h, x + h]`, `h = (2/π) √x log x`.
That difference is the mass of the prime powers `p^k`, `k ≥ 2`, inside the window, and
`window_holds` bounds it elementarily for every `x ≥ 65000`:
`(ψ - θ)(x + h) - (ψ - θ)(x - h) < 1.11 √(x + h) + 3 (x + h)^{1/3} - 0.98 √(x - h)`.
Proof: at most `√(x+h) - √(x-h) + 1` squares, at most one `k`-th power for each `3 ≤ k ≤ log₂ x`,
each with weight `log p ≤ log(x + h)/k`; then a polynomial inequality in `u = x^{1/6}`.
`schoenfeld_window_of` records that Schoenfeld's two bounds imply the window form, so the
window form is a faithful weakening of the cited input. No cited input is used.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.PrimePowerWindow
open Real Finset
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.Dudek2014.Section22

/-- The window form of Schoenfeld's step, all that `display_of` uses. -/
def SchoenfeldWindow : Prop :=
  ∀ x : ℝ, 65000 ≤ x →
    (psiF (x + hD x) - thetaF (x + hD x)) - (psiF (x - hD x) - thetaF (x - hD x)) <
      1.11 * √(x + hD x) + 3 * (x + hD x) ^ (1 / 3 : ℝ) - 0.98 * √(x - hD x)

/-- Faithfulness: the cited `Schoenfeld` implies the window form. -/
theorem schoenfeld_window_of (h : Schoenfeld) : SchoenfeldWindow := by
  intro x hx
  obtain ⟨hh0, hhx⟩ := hD_small hx
  obtain ⟨hA1, -⟩ := h (x - hD x) (by linarith)
  obtain ⟨-, hB2⟩ := h (x + hD x) (by linarith)
  linarith

/-- `(ψ - θ)(b) - (ψ - θ)(a)` is the von Mangoldt mass of the non-primes in `(⌊a⌋, ⌊b⌋]`. -/
theorem diff_eq {a b : ℝ} (hab : ⌊a⌋₊ ≤ ⌊b⌋₊) :
    (psiF b - thetaF b) - (psiF a - thetaF a) =
      ∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun n => ¬ n.Prime), Λ n := by
  have hpsi : psiF b - psiF a = ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n := sum_Iic_sub hab
  have htheta : thetaF b - thetaF a =
      ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p := by
    unfold thetaF
    rw [sum_filter, sum_filter, sum_filter]
    exact sum_Iic_sub hab
  have hsplit := sum_filter_add_sum_filter_not (Ioc ⌊a⌋₊ ⌊b⌋₊) Nat.Prime (fun n => Λ n)
  have hpr : ∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Λ n =
      ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p :=
    sum_congr rfl fun n hn => ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.1 hn).2
  linarith

/-- The window mass is at most `(log b / 2)(√b - √a + 1) + (log b / log 2)(log b / 3)`
when every `k`-th power step, `k ≥ 3`, is below one. -/
theorem mass_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hstep : b ^ (1 / (3 : ℝ)) < a ^ (1 / (3 : ℝ)) + 1) :
    ∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun n => ¬ n.Prime), Λ n ≤
      Real.log b / 2 * (√b - √a + 1) + Real.log b / Real.log 2 * (Real.log b / 3) := by
  classical
  have ha0 : 0 ≤ a := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hB1 : 1 ≤ ⌊b⌋₊ := Nat.le_floor (by exact_mod_cast hb1)
  have hBpos : (0 : ℝ) < ⌊b⌋₊ := by exact_mod_cast hB1
  have hlogB : Real.log ⌊b⌋₊ ≤ Real.log b := Real.log_le_log hBpos (Nat.floor_le (by linarith))
  have hlogB0 : 0 ≤ Real.log ⌊b⌋₊ := Real.log_nonneg (by exact_mod_cast hB1)
  set K := Nat.log 2 ⌊b⌋₊ with hK
  set c : ℕ → ℝ := fun k =>
    (((Iic ⌊b⌋₊).filter (fun m => ⌊a⌋₊ < m ^ k ∧ m ^ k ≤ ⌊b⌋₊)).card : ℝ) with hc
  have hmain := sum_nonprime_le ⌊a⌋₊ ⌊b⌋₊
  have hterm0 : ∀ k ∈ insert 2 (Icc 3 K), 0 ≤ Real.log ⌊b⌋₊ / k * c k := fun k _ =>
    mul_nonneg (div_nonneg hlogB0 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hsub : Icc 2 K ⊆ insert 2 (Icc 3 K) := by
    intro k hk
    rw [mem_Icc] at hk
    rw [mem_insert, mem_Icc]
    omega
  have h1 : ∑ k ∈ Icc 2 K, Real.log ⌊b⌋₊ / k * c k ≤
      ∑ k ∈ insert 2 (Icc 3 K), Real.log ⌊b⌋₊ / k * c k :=
    sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => hterm0 k hk
  rw [sum_insert (by simp)] at h1
  -- the squares
  have hc2 : c 2 ≤ √b - √a + 1 := by
    have := count_le ha0 hab (k := 2) (by norm_num)
    rw [show (1 / ((2 : ℕ) : ℝ)) = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow] at this
    exact this
  have hsq : √a ≤ √b := Real.sqrt_le_sqrt hab
  have hk2 : Real.log ⌊b⌋₊ / ((2 : ℕ) : ℝ) * c 2 ≤ Real.log b / 2 * (√b - √a + 1) := by
    have hc0 : 0 ≤ c 2 := Nat.cast_nonneg _
    push_cast
    apply mul_le_mul (by linarith) hc2 hc0 (by have := Real.log_nonneg hb1; linarith)
  -- the higher powers, at most one each
  have hk3 : ∀ k ∈ Icc 3 K, Real.log ⌊b⌋₊ / k * c k ≤ Real.log b / 3 := by
    intro k hk
    rw [mem_Icc] at hk
    have hk1 : 1 ≤ k := by omega
    have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hstepk : b ^ (1 / (k : ℝ)) < a ^ (1 / (k : ℝ)) + 1 := by
      have := rpow_sub_mono ha hab (r := 1 / (k : ℝ)) (s := 1 / 3) (by positivity)
        (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
      linarith
    have hc1 : c k ≤ 1 := by
      have := count_le_one ha0 hab hk1 hstepk
      simp only [hc]; exact_mod_cast this
    have hc0 : 0 ≤ c k := Nat.cast_nonneg _
    calc Real.log ⌊b⌋₊ / k * c k ≤ Real.log ⌊b⌋₊ / k * 1 :=
          mul_le_mul_of_nonneg_left hc1 (div_nonneg hlogB0 (by linarith))
      _ = Real.log ⌊b⌋₊ / k := mul_one _
      _ ≤ Real.log ⌊b⌋₊ / 3 := div_le_div_of_nonneg_left hlogB0 (by norm_num) hkr
      _ ≤ Real.log b / 3 := by linarith
  have hsum3 : ∑ k ∈ Icc 3 K, Real.log ⌊b⌋₊ / k * c k ≤ (K : ℝ) * (Real.log b / 3) := by
    refine (sum_le_sum hk3).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have : (Icc 3 K).card ≤ K := by rw [Nat.card_Icc]; omega
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast this)
    have := Real.log_nonneg hb1; linarith
  have hKle : (K : ℝ) ≤ Real.log b / Real.log 2 := by
    have hpow : 2 ^ K ≤ ⌊b⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    rw [le_div_iff₀ hl2]
    have : Real.log ((2 : ℝ) ^ K) ≤ Real.log ⌊b⌋₊ :=
      Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    rw [Real.log_pow] at this
    linarith
  have hKb : (K : ℝ) * (Real.log b / 3) ≤ Real.log b / Real.log 2 * (Real.log b / 3) :=
    mul_le_mul_of_nonneg_right hKle (by have := Real.log_nonneg hb1; linarith)
  calc _ ≤ _ := hmain
    _ ≤ _ := h1
    _ ≤ _ := by linarith

end LeanLab.PrimePowerWindow

