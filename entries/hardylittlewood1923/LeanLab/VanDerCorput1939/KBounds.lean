module

public import Mathlib
public import LeanLab.VanDerCorput1939.Global

/-!
P0067 van der Corput 1939, the constant K = ∏_p (1 + 1/(p − 1)³) of the ternary singular series.
Numeric bounds 2.29 < K < 2.33, from the factors at p = 2, 3, 5, 7 and the tail
Σ_{n ≥ 11} 1/(n − 1)³ ≤ 1/90. A float computation over the primes below 10^6 gives
K ≈ 2.30096, inside the proved range.

AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.VanDerCorput1939
open Real Finset

attribute [local instance] Classical.propDecidable

/-- The Euler factor. -/
noncomputable def fK (n : ℕ) : ℝ := 1 + 1 / ((n : ℝ) - 1) ^ 3

/-- Its log on primes, `0` elsewhere. -/
noncomputable def aK (n : ℕ) : ℝ := if n.Prime then Real.log (fK n) else 0

theorem cube_pos_of_prime {p : ℕ} (hp : p.Prime) : 0 < ((p : ℝ) - 1) ^ 3 := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  positivity

theorem fK_pos_of_prime {p : ℕ} (hp : p.Prime) : 0 < fK p := by
  unfold fK; have := cube_pos_of_prime hp; positivity

theorem aK_nonneg (n : ℕ) : 0 ≤ aK n := by
  unfold aK
  split_ifs with hp
  · apply Real.log_nonneg
    unfold fK; have := cube_pos_of_prime hp
    have : 0 ≤ 1 / ((n : ℝ) - 1) ^ 3 := by positivity
    linarith
  · exact le_rfl

/-- `aK n ≤ 1/(n−1)³` on primes, and `aK = 0` elsewhere. -/
theorem aK_le (n : ℕ) : aK n ≤ if n.Prime then 1 / ((n : ℝ) - 1) ^ 3 else 0 := by
  unfold aK
  split_ifs with hp
  · have h := Real.log_le_sub_one_of_pos (fK_pos_of_prime hp)
    unfold fK at h ⊢; linarith
  · exact le_rfl

theorem summable_aK : Summable aK := by
  have hb : Summable (fun n : ℕ => if n.Prime then 1 / ((n : ℝ) - 1) ^ 3 else 0) := by
    have := summable_inv_sub_one_cube.indicator {n : ℕ | n.Prime}
    refine this.congr fun n => ?_
    by_cases hp : n.Prime <;> simp [Set.indicator, hp]
  exact Summable.of_nonneg_of_le aK_nonneg aK_le hb

/-- `K = exp (Σ' n, aK n)`. -/
theorem K_eq_exp : K = Real.exp (∑' n, aK n) := by
  have hpos : ∀ p : {p : ℕ // p.Prime}, 0 < 1 + 1 / ((p : ℝ) - 1) ^ 3 :=
    fun p => fK_pos_of_prime p.2
  have hsub : (∑' p : {p : ℕ // p.Prime}, Real.log (1 + 1 / ((p : ℝ) - 1) ^ 3)) =
      ∑' n, aK n := by
    have h := _root_.tsum_subtype ({n : ℕ | n.Prime} : Set ℕ) (fun n : ℕ => Real.log (fK n))
    refine h.trans ?_
    congr 1; funext n
    by_cases hp : n.Prime <;> simp [Set.indicator, aK, hp]
  have hsumm : Summable (fun p : {p : ℕ // p.Prime} => Real.log (1 + 1 / ((p : ℝ) - 1) ^ 3)) := by
    have := summable_aK.subtype (fun n : ℕ => n.Prime)
    refine this.congr fun p => ?_
    simp [aK, fK, p.2]
  unfold K
  rw [← Real.rexp_tsum_eq_tprod hpos hsumm, hsub]

theorem aK_vals : aK 0 = 0 ∧ aK 1 = 0 ∧ aK 2 = Real.log 2 ∧ aK 3 = Real.log (9 / 8) ∧
    aK 4 = 0 ∧ aK 5 = Real.log (65 / 64) ∧ aK 6 = 0 ∧ aK 7 = Real.log (217 / 216) ∧
    aK 8 = 0 ∧ aK 9 = 0 ∧ aK 10 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [aK, fK] <;> norm_num

/-- The head: primes below 11. -/
theorem head_eq : ∑ n ∈ range 11, aK n =
    Real.log 2 + Real.log (9 / 8) + Real.log (65 / 64) + Real.log (217 / 216) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := aK_vals
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7, h8,
    h9, h10]
  ring

/-- The tail by telescoping: `Σ_{n < N} 1/(n+10)² ≤ 1/9 − 1/(N+9)`. -/
theorem tail_sq_le (N : ℕ) : ∑ n ∈ range N, 1 / ((n : ℝ) + 10) ^ 2 ≤ 1 / 9 - 1 / ((N : ℝ) + 9) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have key : 1 / ((N : ℝ) + 10) ^ 2 ≤ 1 / ((N : ℝ) + 9) - 1 / ((N : ℝ) + 1 + 9) := by
      rw [show (N : ℝ) + 1 + 9 = N + 10 by ring]
      rw [div_sub_div _ _ (by positivity) (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem tail_le : ∑' n, aK (n + 11) ≤ 1 / 90 := by
  have hterm : ∀ n : ℕ, aK (n + 11) ≤ 1 / 10 * (1 / ((n : ℝ) + 10) ^ 2) := by
    intro n
    have h := aK_le (n + 11)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    split_ifs at h with hp
    · refine h.trans ?_
      push_cast
      rw [show (n : ℝ) + 11 - 1 = n + 10 by ring]
      rw [div_le_iff₀ (by positivity)]
      rw [show 1 / 10 * (1 / ((n : ℝ) + 10) ^ 2) * ((n : ℝ) + 10) ^ 3 = ((n : ℝ) + 10) / 10 by
        field_simp]
      linarith
    · exact h.trans (by positivity)
  apply Real.tsum_le_of_sum_range_le (fun n => aK_nonneg _)
  intro N
  calc ∑ n ∈ range N, aK (n + 11) ≤ ∑ n ∈ range N, 1 / 10 * (1 / ((n : ℝ) + 10) ^ 2) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = 1 / 10 * ∑ n ∈ range N, 1 / ((n : ℝ) + 10) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 1 / 10 * (1 / 9) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have := tail_sq_le N
        have : 0 ≤ 1 / ((N : ℝ) + 9) := by positivity
        linarith
    _ = 1 / 90 := by norm_num

theorem log_head_eq : Real.log 2 + Real.log (9 / 8) + Real.log (65 / 64) + Real.log (217 / 216) =
    Real.log (2 * (9 / 8) * (65 / 64) * (217 / 216)) := by
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

/-- **Lower bound**: `2.29 < K`. -/
theorem K_gt : (2.29 : ℝ) < K := by
  rw [K_eq_exp]
  have hle : ∑ n ∈ range 11, aK n ≤ ∑' n, aK n :=
    summable_aK.sum_le_tsum _ (fun n _ => aK_nonneg n)
  rw [head_eq, log_head_eq] at hle
  have := Real.exp_le_exp.mpr hle
  rw [Real.exp_log (by norm_num)] at this
  have : (2.29 : ℝ) < 2 * (9 / 8) * (65 / 64) * (217 / 216) := by norm_num
  linarith

/-- **Upper bound**: `K < 2.33`. -/
theorem K_lt : K < (2.33 : ℝ) := by
  rw [K_eq_exp, ← summable_aK.sum_add_tsum_nat_add 11, head_eq, log_head_eq, Real.exp_add,
    Real.exp_log (by norm_num)]
  have ht := Real.exp_le_exp.mpr tail_le
  have hb : Real.exp (1 / 90) ≤ 1 + 1 / 90 + (1 / 90) ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := 1 / 90) (by norm_num [abs_of_pos])
    have := (abs_le.mp this).2
    linarith
  have hpos : (0 : ℝ) < 2 * (9 / 8) * (65 / 64) * (217 / 216) := by norm_num
  calc 2 * (9 / 8) * (65 / 64) * (217 / 216) * Real.exp (∑' n, aK (n + 11))
      ≤ 2 * (9 / 8) * (65 / 64) * (217 / 216) * (1 + 1 / 90 + (1 / 90) ^ 2) :=
        mul_le_mul_of_nonneg_left (ht.trans hb) hpos.le
    _ < 2.33 := by norm_num

theorem K_bounds : (2.29 : ℝ) < K ∧ K < 2.33 := ⟨K_gt, K_lt⟩

end LeanLab.VanDerCorput1939
