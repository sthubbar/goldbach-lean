module

public import Mathlib
public import LeanLab.Dudek2014.Lemma5
public import LeanLab.PrimePowerWindow.Holds

/-!
I-5230, unit U-6601, CLOUD 20261020T1618Z-cloud46: Dudek 2014's page 6 display and Theorem 2
WITHOUT Schoenfeld's ψ - θ bounds. `display_of_window` is the lab's `display_of`, Dudek2014/
Display.lean, with the Schoenfeld step replaced by `window_holds`, PROVED with no cited input;
the proof is otherwise copied unchanged. `theorem2_of_lemma4_window`: Dudek's Theorem 2 for every
`x ≥ 2` CONDITIONAL ON Lemma 4 and the page 5 zero sum bound only.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.Section22
open Real Finset
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.PrimePowerWindow

noncomputable section

/-- **`Display22` from Lemma 5 and the Σ bounds alone**, Schoenfeld replaced by `window_holds`. -/
theorem display_of_window {S : ℝ → ℝ → ℝ} (h5 : Lemma5 S) (hS : SigmaBd S) :
    Display22 := by
  intro x hx
  obtain ⟨hh0, hhx⟩ := hD_small hx
  set h := hD x with hhdef
  have hx0 : 0 < x := by linarith
  have hlo : (121 : ℝ) ≤ x - h := by linarith
  have hab : ⌊x - h⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  -- Lemma 5 and the Σ bound
  have hW : h - (2 / π * (x / √(x - h) + (x + h) ^ (3 / 2 : ℝ) / x) * log (2 * x / h))
      - 48 / (5 * h) < WS x h := by
    have h1 := h5 x h hh0 (by linarith)
    have h2 := hS x hx
    rw [← hhdef] at h2
    have hpi := pi_pos
    have hsq : 0 < √(x - h) := sqrt_pos.2 (by linarith)
    have e : (2 * x * h / (π * √(x - h)) + 4 * h * (x + h) ^ (3 / 2 : ℝ) / (π * 2 * x)) *
        log (2 * x / h) / h =
        2 / π * (x / √(x - h) + (x + h) ^ (3 / 2 : ℝ) / x) * log (2 * x / h) := by
      field_simp; ring
    have h3 : S x h / h ≤ |S x h| / h := div_le_div_of_nonneg_right (le_abs_self _) hh0.le
    have h4 : |S x h| / h ≤ 2 / π * (x / √(x - h) + (x + h) ^ (3 / 2 : ℝ) / x) *
        log (2 * x / h) := by
      rw [← e]; exact div_le_div_of_nonneg_right h2 hh0.le
    have := (abs_lt.1 h1).1
    linarith
  -- WS ≤ Σ_{x-h<n≤x+h} Λ(n)
  have hWle : WS x h ≤ ∑ n ∈ Ioc ⌊x - h⌋₊ ⌊x + h⌋₊, Λ n := by
    unfold WS
    rw [← Iic_union_Ioc_eq_Iic hab, sum_union (Iic_disjoint_Ioc le_rfl)]
    have hz : ∑ n ∈ Iic ⌊x - h⌋₊, Λ n * w x h n = 0 := by
      apply sum_eq_zero
      intro n hn
      rw [mem_Iic] at hn
      have hnr : (n : ℝ) ≤ x - h := by
        have := Nat.floor_le (show 0 ≤ x - h by linarith)
        have : (n : ℝ) ≤ ⌊x - h⌋₊ := by exact_mod_cast hn
        linarith
      have hw : w x h n = 0 := by
        unfold w
        apply max_eq_left
        rw [sub_nonpos, le_div_iff₀ hh0, one_mul, abs_of_nonpos (by linarith)]
        linarith
      rw [hw, mul_zero]
    rw [hz, zero_add]
    apply sum_le_sum
    intro n _
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have hw1 : w x h n ≤ 1 := by
      unfold w
      apply max_le (by norm_num)
      have : 0 ≤ |(n : ℝ) - x| / h := div_nonneg (abs_nonneg _) hh0.le
      linarith
    nlinarith [show 0 ≤ w x h n from le_max_left _ _]
  -- ψ and θ differences
  have hpsi : psiF (x + h) - psiF (x - h) = ∑ n ∈ Ioc ⌊x - h⌋₊ ⌊x + h⌋₊, Λ n :=
    sum_Iic_sub hab
  have htheta : thetaF (x + h) - thetaF (x - h) =
      ∑ p ∈ (Ioc ⌊x - h⌋₊ ⌊x + h⌋₊).filter Nat.Prime, log p := by
    unfold thetaF
    rw [sum_filter, sum_filter, sum_filter]
    exact sum_Iic_sub hab
  have hWin := window_holds x hx
  rw [← hhdef] at hWin
  rw [← htheta]
  unfold rhs
  rw [← hhdef]
  linarith

/-- **Dudek 2014 Theorem 2 for every `x ≥ 2`, CONDITIONAL ON Lemma 4 and the page 5 Σ bounds
only**; Schoenfeld's ψ - θ bounds are no longer an input. -/
theorem theorem2_of_lemma4_window {Z : ℝ → ℝ} (h4 : Lemma4 Z)
    (hS : SigmaBd (fun x h => Z (x + h) - 2 * Z x + Z (x - h))) :
    ∀ x : ℝ, 2 ≤ x → PrimeInDudekInterval x :=
  theorem2_of_display (display_of_window (lemma5_of h4) hS)

end

end LeanLab.Dudek2014.Section22

