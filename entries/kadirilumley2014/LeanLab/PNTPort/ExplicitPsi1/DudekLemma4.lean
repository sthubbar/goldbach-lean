module

public import LeanLab.PNTPort.ExplicitPsi1.TrivialLimit
public import LeanLab.PNTPort.ExplicitPsi1.ZetaTwo
public import LeanLab.PNTPort.ExplicitPsi1.Log2Pi
public import LeanLab.Dudek2014.Lemma5
public import LeanLab.Dudek2014.Section22

/-!
# Dudek 2014 Lemma 4, proved: the ψ₁ explicit formula with error at most 2.393

Lab proof, CLOUD 20261020T1518Z-cloud45, unit U-6551. AI wrote this file. Known mathematics,
Davenport chapter 17, no cited input beyond Mathlib and the lab's proved files.

From `explicit_formula_psi1_trivial`, for `y > 1`,
`ψ₁(y) = y²/2 - y log 2π - Z(y) + E(y)`, `Z(y) = Re y Σ_ρ m(ρ) y^ρ/(ρ(ρ + 1))` over the nontrivial
zeros, `E(y) = Re (ζ'/ζ)(-1) - y Σₙ y^{-2(n+1)}/((2n + 2)(2n + 1))`, and
`(ζ'/ζ)(-1) = log 2π - 1 + γ - ζ'/ζ(2)` with `‖ζ'/ζ(2)‖ ≤ 0.97` give `-1.59 ≤ E(y) ≤ 2.386`.

* `lemma4_Zpatch`: the lab's cited Prop `Dudek2014.Section22.Lemma4` holds for `Zpatch`, which is
  `Z` for `y > 1` and is set so the error is 0 for `y ≤ 1`, where `ψ₁ = 0` and Dudek uses nothing;
* `theorem2_of_sigmaBd`: Dudek's Theorem 2, a prime in `(x - (4/π)√x log x, x]` for every
  `x ≥ 2`, CONDITIONAL ON the page 5 zero sum bound `SigmaBd` for `Z` and Schoenfeld's `ψ - θ`
  bounds only; Lemma 4 is no longer an input.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Complex Set Filter Topology
open scoped Real
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.ZetaZeros

local notation "ζ" => riemannZeta

/-- `Σ Λ(n) w₁(n/y) = ψ₁(y)/y`, `ψ₁(y) = Σ_{n ≤ y} (y - n) Λ(n)` as in `Dudek2014.Section22.psi1`. -/
theorem tsum_w1_eq {y : ℝ} (hy : 0 < y) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (ZetaZeros.w1 (n / y) : ℂ) =
      ((LeanLab.Dudek2014.Section22.psi1 y / y : ℝ) : ℂ) := by
  rw [tsum_eq_sum (s := Finset.Iic ⌊y⌋₊) ?_]
  · unfold LeanLab.Dudek2014.Section22.psi1
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff hy.le).mp (Finset.mem_Iic.mp hn)
    have hw : ZetaZeros.w1 (n / y) = (y - n) / y := by
      unfold ZetaZeros.w1
      rw [max_eq_right]
      · field_simp
      · rw [sub_nonneg, div_le_one hy]; exact hny
    rw [hw]
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast
    field_simp
  · intro n hn
    have hlt : ⌊y⌋₊ < n := by
      have := Finset.mem_Iic.not.mp hn; omega
    have hyn : y < n := Nat.lt_of_floor_lt hlt
    have hw : ZetaZeros.w1 (n / y) = 0 := by
      unfold ZetaZeros.w1
      apply max_eq_left
      rw [sub_nonpos, le_div_iff₀ hy]; linarith
    rw [hw]; simp

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

/-- The real zero sum `Z(y) = Re y Σ_ρ m(ρ) y^ρ/(ρ(ρ + 1))`. -/
noncomputable def Zreal (y : ℝ) : ℝ := ((y : ℂ) * ∑' ρ : Zall, zterm y ρ).re

/-- **The explicit formula for `ψ₁` itself**, `y > 1`:
`ψ₁(y) = y²/2 - y log 2π - Z(y) + Re (ζ'/ζ)(-1) - y Σₙ tb(y, n)`. -/
theorem psi1_formula {y : ℝ} (hy : 1 < y) :
    LeanLab.Dudek2014.Section22.psi1 y =
      y ^ 2 / 2 - y * Real.log (2 * π) - Zreal y + (deriv ζ (-1) / ζ (-1)).re -
        y * ∑' n, tb y n := by
  have hy0 : 0 < y := by linarith
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  have h := explicit_formula_psi1_trivial hy
  rw [tsum_w1_eq hy0, logDeriv_zeta_zero, Complex.cpow_neg_one] at h
  have hts : ∑' n : ℕ, tterm y n = ((∑' n, tb y n : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; exact tsum_congr (tterm_eq hy0)
  rw [hts] at h
  have e : ((LeanLab.Dudek2014.Section22.psi1 y : ℝ) : ℂ) =
      (y : ℂ) * ((LeanLab.Dudek2014.Section22.psi1 y / y : ℝ) : ℂ) := by
    push_cast; field_simp
  have hc : ((LeanLab.Dudek2014.Section22.psi1 y : ℝ) : ℂ) =
      (((y ^ 2 / 2 - y * Real.log (2 * π)) : ℝ) : ℂ) - (y : ℂ) * ∑' ρ : Zall, zterm y ρ +
        deriv ζ (-1) / ζ (-1) - ((y * ∑' n, tb y n : ℝ) : ℂ) := by
    rw [e, h]; push_cast; field_simp
  have := congr_arg Complex.re hc
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.add_re] at this
  rw [this, Zreal]

/-- `Re (ζ'/ζ)(-1) = log 2π - 1 + γ - Re ζ'/ζ(2)`. -/
lemma re_logDeriv_neg_one :
    (deriv ζ (-1) / ζ (-1)).re =
      Real.log (2 * π) - 1 + Real.eulerMascheroniConstant - (deriv ζ 2 / ζ 2).re := by
  rw [logDeriv_zeta_neg_one]
  have e : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log (by positivity)]
  rw [e]
  simp

/-- **The error of Lemma 4**: `|E(y)| ≤ 2.393` for `y > 1`. -/
theorem error_bound {y : ℝ} (hy : 1 < y) :
    |(deriv ζ (-1) / ζ (-1)).re - y * ∑' n, tb y n| ≤ 2.393 := by
  rw [re_logDeriv_neg_one]
  have hz := norm_logDeriv_zeta_two_le
  have hre := Complex.abs_re_le_norm (deriv ζ 2 / ζ 2)
  have hre' := abs_le.mp (hre.trans hz)
  obtain ⟨h0, h1⟩ := y_tsum_tb_bounds hy.le
  have hl2 : Real.log (2 * π) = Real.log 2 + Real.log π := Real.log_mul (by norm_num) Real.pi_pos.ne'
  have a1 := Real.log_two_lt_d9
  have a2 := Real.log_two_gt_d9
  have a3 := LeanLab.Dudek2014.Section22.log_pi_lt
  have a4 := LeanLab.Dudek2014.Section22.log_pi_gt
  have g1 := LeanLab.Helfgott2013.GammaFine.gamma_lt_fine
  have g2 := Real.one_half_lt_eulerMascheroniConstant
  have hpi := Real.pi_lt_d2
  have hpi2 : π ^ 2 / 6 ≤ 1.66 := by nlinarith [Real.pi_pos]
  rw [abs_le]; constructor <;> linarith

/-- The patched zero sum: `Z` for `y > 1`, and for `y ≤ 1` the value that makes Lemma 4 exact. -/
noncomputable def Zpatch (y : ℝ) : ℝ :=
  if 1 < y then Zreal y else y ^ 2 / 2 - y * Real.log (2 * π) - LeanLab.Dudek2014.Section22.psi1 y

/-- **Dudek 2014 Lemma 4, PROVED**: the lab's cited Prop holds for `Zpatch`, with no cited input. -/
theorem lemma4_Zpatch : LeanLab.Dudek2014.Section22.Lemma4 Zpatch := by
  intro y hy
  unfold Zpatch
  split_ifs with h
  · rw [psi1_formula h]
    have := error_bound h
    calc _ = |(deriv ζ (-1) / ζ (-1)).re - y * ∑' n, tb y n| := by congr 1; ring
      _ ≤ 2.393 := this
  · have e : LeanLab.Dudek2014.Section22.psi1 y -
        (y ^ 2 / 2 - (y ^ 2 / 2 - y * Real.log (2 * π) - LeanLab.Dudek2014.Section22.psi1 y) -
          y * Real.log (2 * π)) = 0 := by ring
    rw [e, abs_zero]; norm_num

/-- `Zpatch = Zreal` at the three points Dudek's page 5 bound uses, `x ≥ 65000`. -/
lemma sigma_patch {x : ℝ} (hx : 65000 ≤ x) :
    Zpatch (x + LeanLab.Dudek2014.Section22.hD x) - 2 * Zpatch x +
        Zpatch (x - LeanLab.Dudek2014.Section22.hD x) =
      Zreal (x + LeanLab.Dudek2014.Section22.hD x) - 2 * Zreal x +
        Zreal (x - LeanLab.Dudek2014.Section22.hD x) := by
  obtain ⟨h0, h1⟩ := LeanLab.Dudek2014.Section22.hD_small hx
  unfold Zpatch
  rw [ite_eq_left (by linarith), ite_eq_left (by linarith), ite_eq_left (by linarith)]

/-- **Dudek's Theorem 2 without Lemma 4 as an input**: a prime in `(x - (4/π)√x log x, x]` for
every `x ≥ 2`, CONDITIONAL ON `SigmaBd` for the zero sum `Z` and Schoenfeld's `ψ - θ` bounds. -/
theorem theorem2_of_sigmaBd
    (hS : LeanLab.Dudek2014.Section22.SigmaBd (fun x h => Zreal (x + h) - 2 * Zreal x + Zreal (x - h)))
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld) :
    ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x := by
  refine LeanLab.Dudek2014.Section22.theorem2_of_lemma4 lemma4_Zpatch ?_ hSch
  intro x hx
  have := hS x hx
  simp only at this ⊢
  rw [sigma_patch hx]
  exact this

end LeanLab.PNTPort.ExplicitPsi1.Trivial
