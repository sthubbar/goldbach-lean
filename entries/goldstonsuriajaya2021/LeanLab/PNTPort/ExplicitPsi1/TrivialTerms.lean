module

public import LeanLab.PNTPort.ExplicitPsi1.TrivialLimit

/-!
# The trivial zero terms of the explicit formula for `ψ₁`, as real numbers

Lab proof, AI wrote this file, Claude by Anthropic. Known mathematics, no cited input. These
declarations are taken unchanged from the lab file `PNTPort/ExplicitPsi1/DudekLemma4.lean`; the
rest of that file, on Dudek 2014, is not needed by this entry and is left out, so the entry does
not import the Dudek 2014 files.

* `tb y n = y^{-2(n+1)}/((2n + 2)(2n + 1))`, and `tterm_eq`: the complex trivial zero term
  `tterm y n` of `TrivialLimit.lean` is the real number `tb y n` for `y > 0`;
* `y_tsum_tb_bounds`: `0 ≤ y Σₙ tb(y, n) ≤ π²/6` for `y ≥ 1`.
-/

@[expose] public section

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Complex Set Filter Topology
open scoped Real
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.ZetaZeros

local notation "ζ" => riemannZeta

/-- The real trivial zero term `y^{-2(n+1)}/((2n + 2)(2n + 1))`. -/
noncomputable def tb (y : ℝ) (n : ℕ) : ℝ := y ^ (-2 * ((n : ℝ) + 1)) / ((2 * n + 2) * (2 * n + 1))

lemma tterm_eq {y : ℝ} (hy : 0 < y) (n : ℕ) : tterm y n = ((tb y n : ℝ) : ℂ) := by
  unfold tterm tb
  have e : (-2 * ((n : ℂ) + 1)) = ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [e, ← Complex.ofReal_cpow hy.le]
  push_cast
  ring

lemma tb_nonneg {y : ℝ} (hy : 0 < y) (n : ℕ) : 0 ≤ tb y n := by
  unfold tb; have := Real.rpow_nonneg hy.le (-2 * ((n : ℝ) + 1)); positivity

lemma y_tb_le {y : ℝ} (hy : 1 ≤ y) (n : ℕ) : y * tb y n ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  unfold tb
  have hy0 : 0 < y := by linarith
  have hp : y * y ^ (-2 * ((n : ℝ) + 1)) ≤ 1 := by
    rw [← Real.rpow_one_add' hy0.le (by nlinarith [Nat.cast_nonneg (α := ℝ) n])]
    exact Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : ((n : ℝ) + 1) ^ 2 ≤ (2 * n + 2) * (2 * n + 1) := by nlinarith
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Real.rpow_nonneg hy0.le (-2 * ((n : ℝ) + 1))]

lemma summable_tb {y : ℝ} (hy : 1 ≤ y) : Summable (tb y) := by
  have hy0 : 0 < y := by linarith
  have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  have h2 : Summable (fun n => y * tb y n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg hy0.le (tb_nonneg hy0 n)) (y_tb_le hy) h1
  have := h2.mul_left (1 / y)
  refine this.congr (fun n => ?_)
  field_simp

/-- `0 ≤ y Σₙ tb(y, n) ≤ π²/6`. -/
lemma y_tsum_tb_bounds {y : ℝ} (hy : 1 ≤ y) : 0 ≤ y * ∑' n, tb y n ∧ y * ∑' n, tb y n ≤ π ^ 2 / 6 := by
  have hy0 : 0 < y := by linarith
  refine ⟨mul_nonneg hy0.le (tsum_nonneg (tb_nonneg hy0)), ?_⟩
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  rw [← tsum_mul_left]
  have h2 : Summable (fun n => y * tb y n) := (summable_tb hy).mul_left y
  calc ∑' n, y * tb y n ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := h2.tsum_le_tsum (y_tb_le hy) hz.summable
    _ = π ^ 2 / 6 := hz.tsum_eq

end LeanLab.PNTPort.ExplicitPsi1.Trivial
