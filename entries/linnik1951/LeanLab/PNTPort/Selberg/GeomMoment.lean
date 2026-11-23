module

public import Mathlib

/-!
# Moments of the truncated geometric distribution

Lab proof, unit U-6004, CLOUD 20261020T0415Z-cloud34, T2 toward IDEAS I-5100 and P0058 Lemma 1.
AI wrote this file. Elementary, no cited input.

* `geom_moment`: for `0 ≤ q < 1`, every `p` and `M`,
  `Σ_{n<M} (1 - q) q^n (n + 1)^p + q^M M^p ≤ p! / (1 - q)^p`.
  These are the weights `c_n = w_n - w_{n+1}` and `w_M` of `abel_cs` for `w_n = q^n`;
* `one_sub_exp_neg_inv`: `1/(1 - e^{-1/N}) ≤ 2N` for `N ≥ 1`, so with `q = e^{-1/N}` the
  `p`-th moment is at most `p! (2N)^p`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Finset

lemma pow_le_factorial_mul_choose (n p : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ p ≤ (p.factorial : ℝ) * ((n + p).choose p : ℕ) := by
  have h1 := Nat.pow_succ_le_ascFactorial (n + 1) p
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at h1
  exact_mod_cast h1

/-- **Moments of the truncated geometric distribution.** -/
theorem geom_moment (p M : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑ n ∈ range M, (1 - q) * q ^ n * ((n : ℝ) + 1) ^ p) + q ^ M * (M : ℝ) ^ p ≤
      (p.factorial : ℝ) / (1 - q) ^ p := by
  have hq : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have h1q : 0 < 1 - q := by linarith
  set h : ℕ → ℝ := fun n => (1 - q) * (p.factorial : ℝ) * (((n + p).choose p : ℕ) * q ^ n) with hh
  have hH : HasSum h ((1 - q) * (p.factorial : ℝ) * (1 / (1 - q) ^ (p + 1))) :=
    (hasSum_choose_mul_geometric_of_norm_lt_one p hq).mul_left _
  have hval : (1 - q) * (p.factorial : ℝ) * (1 / (1 - q) ^ (p + 1)) =
      (p.factorial : ℝ) / (1 - q) ^ p := by
    field_simp; ring
  rw [hval] at hH
  have hs : Summable h := hH.summable
  have hg_le : ∀ n : ℕ, (1 - q) * q ^ n * ((n : ℝ) + 1) ^ p ≤ h n := by
    intro n
    have := pow_le_factorial_mul_choose n p
    push_cast at this
    simp only [hh]
    have hqn : 0 ≤ (1 - q) * q ^ n := by positivity
    calc (1 - q) * q ^ n * ((n : ℝ) + 1) ^ p
        ≤ (1 - q) * q ^ n * ((p.factorial : ℝ) * ((n + p).choose p : ℕ)) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast this) hqn
      _ = _ := by ring
  -- the tail
  have htail : q ^ M * (M : ℝ) ^ p ≤ ∑' i, h (i + M) := by
    have hgeo : HasSum (fun i : ℕ => (1 - q) * q ^ (i + M) * (M : ℝ) ^ p) (q ^ M * (M : ℝ) ^ p) := by
      have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((1 - q) * q ^ M * (M : ℝ) ^ p)
      convert this using 1
      · ext i; rw [pow_add]; ring
      · field_simp
    rw [← hgeo.tsum_eq]
    refine hgeo.summable.tsum_le_tsum (fun i => ?_) ((summable_nat_add_iff M).mpr hs)
    refine le_trans ?_ (hg_le (i + M))
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg M) (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]) p
  have hhead : ∑ n ∈ range M, (1 - q) * q ^ n * ((n : ℝ) + 1) ^ p ≤ ∑ n ∈ range M, h n :=
    sum_le_sum fun n _ => hg_le n
  rw [← hH.tsum_eq, ← hs.sum_add_tsum_nat_add M]
  linarith

/-- `1/(1 - e^{-1/N}) ≤ 2N` for `N ≥ 1`. -/
lemma one_sub_exp_neg_inv {N : ℝ} (hN : 1 ≤ N) : 1 / (1 - Real.exp (-(1 / N))) ≤ 2 * N := by
  have hN0 : 0 < N := by linarith
  set x := 1 / N with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hN0]; exact hN
  have he : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.add_one_le_exp x])
  have hlow : x / 2 ≤ 1 - Real.exp (-x) := by
    have : x / 2 ≤ 1 - 1 / (1 + x) := by
      rw [show 1 - 1 / (1 + x) = x / (1 + x) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    linarith
  have hpos : 0 < 1 - Real.exp (-x) := by linarith
  rw [div_le_iff₀ hpos]
  have : 2 * N * (x / 2) = 1 := by rw [hx]; field_simp
  nlinarith

end LeanLab.PNTPort.Selberg

