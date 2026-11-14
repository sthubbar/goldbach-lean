module

public import LeanLab.PNTPort.LargeSieve.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Vinogradov's minor arc bound, basic sums

Lab proof, unit U-5250. AI wrote this file. Known mathematics, no cited input.

* `G Y θ`, the quantity `min (Y, 1/(2‖θ‖))`, read as `Y` when `‖θ‖ = 0`.
* `norm_sum_Ioc_e_le`: `‖∑_{M < n ≤ M + K} e(nθ)‖ ≤ G K θ`.
* `dist0_ge`: the distance to the nearest integer of `x + t + y`, `0 ≤ x ≤ 1`, `t ∈ ℤ`, is at
  least `min (x, 1 - x) - |y|`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real
open LeanLab.PNTPort.LargeSieve

/-- `G Y θ = min (Y, 1/(2‖θ‖))`, and `Y` when `θ` is an integer. -/
noncomputable def G (Y θ : ℝ) : ℝ := if dist0 θ = 0 then Y else min Y (1 / (2 * dist0 θ))

lemma G_le (Y θ : ℝ) : G Y θ ≤ Y := by
  unfold G; split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma G_le_inv {Y θ : ℝ} (h : 0 < dist0 θ) : G Y θ ≤ 1 / (2 * dist0 θ) := by
  unfold G; rw [if_neg h.ne']; exact min_le_right _ _

lemma G_nonneg {Y : ℝ} (hY : 0 ≤ Y) (θ : ℝ) : 0 ≤ G Y θ := by
  unfold G; split_ifs with h
  · exact hY
  · have : 0 < dist0 θ := lt_of_le_of_ne (dist0_nonneg θ) (Ne.symm h)
    exact le_min hY (by positivity)

lemma G_mono {Y Y' : ℝ} (h : Y ≤ Y') (θ : ℝ) : G Y θ ≤ G Y' θ := by
  unfold G; split_ifs
  · exact h
  · exact min_le_min_right _ h

/-- `G` is at most anything that bounds both `Y` and, when `‖θ‖ > 0`, `1/(2‖θ‖)`. -/
lemma G_le_of {Y θ B : ℝ} (hY : Y ≤ B) : G Y θ ≤ B := (G_le Y θ).trans hY

lemma sum_Ioc_e_eq (M K : ℕ) (θ : ℝ) :
    ∑ n ∈ Ioc M (M + K), e (n * θ) = e ((M + 1 : ℕ) * θ) * ∑ k ∈ range K, e (k * θ) := by
  rw [mul_sum]
  have : Ioc M (M + K) = (range K).map (addLeftEmbedding (M + 1)) := by
    ext n; simp only [mem_Ioc, mem_map, mem_range, addLeftEmbedding_apply]
    constructor
    · intro h; exact ⟨n - (M + 1), by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; omega
  rw [this, sum_map]
  refine sum_congr rfl fun k _ => ?_
  rw [addLeftEmbedding_apply, ← e_add]
  congr 1; push_cast; ring

/-- `‖∑_{M < n ≤ M + K} e(nθ)‖ ≤ G K θ`. -/
theorem norm_sum_Ioc_e_le (M K : ℕ) (θ : ℝ) :
    ‖∑ n ∈ Ioc M (M + K), e (n * θ)‖ ≤ G K θ := by
  have hK : ‖∑ n ∈ Ioc M (M + K), e (n * θ)‖ ≤ K := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_e, sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    push_cast; rw [show M + K - M = K by omega]
  unfold G; split_ifs with h
  · exact hK
  · have hpos : 0 < dist0 θ := lt_of_le_of_ne (dist0_nonneg θ) (Ne.symm h)
    refine le_min hK ?_
    rw [sum_Ioc_e_eq, norm_mul, norm_e, one_mul]
    exact norm_geom_le K hpos

/-- `min (x, 1 - x) - |y| ≤ ‖x + t + y‖` for `0 ≤ x ≤ 1` and an integer `t`. -/
lemma dist0_ge {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (t : ℤ) :
    min x (1 - x) - |y| ≤ dist0 (x + t + y) := by
  unfold dist0
  set z : ℤ := round (x + t + y)
  have key : min x (1 - x) ≤ |x - ((z - t : ℤ) : ℝ)| := by
    rcases le_or_gt (z - t) 0 with h | h
    · have : ((z - t : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      exact (min_le_left _ _).trans (by linarith)
    · have h1 : (1 : ℤ) ≤ z - t := h
      have : (1 : ℝ) ≤ ((z - t : ℤ) : ℝ) := by exact_mod_cast h1
      rw [abs_of_nonpos (by linarith)]
      exact (min_le_right _ _).trans (by linarith)
  have e1 : x + t + y - z = (x - ((z - t : ℤ) : ℝ)) + y := by push_cast; ring
  rw [e1]
  have := abs_sub_abs_le_abs_sub (x - ((z - t : ℤ) : ℝ) + y) y
  have h2 : |x - ((z - t : ℤ) : ℝ)| ≤ |x - ((z - t : ℤ) : ℝ) + y| + |y| := by
    have := abs_add_le (x - ((z - t : ℤ) : ℝ) + y) (-y)
    rw [abs_neg, show x - ((z - t : ℤ) : ℝ) + y + -y = x - ((z - t : ℤ) : ℝ) by ring] at this
    exact this
  linarith

end LeanLab.PNTPort.Vinogradov

