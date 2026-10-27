module

public import LeanLab.PNTPort.ExplicitPsi1.PsiOneRHSimple
public import LeanLab.Dudek2014.Display

/-!
# From `ψ₁` to `ψ`: unsmoothing, and an explicit `ψ(x) = x + O(x^{3/4})` under RH

I-5190, unit U-6603, CLOUD 20261020T1618Z-cloud46. AI wrote this file. Known mathematics.

* `psi1_diff_bounds`: for `0 ≤ x` and `0 < h`, `h ψ(x) ≤ ψ₁(x + h) - ψ₁(x) ≤ h ψ(x + h)`, since
  `ψ₁(y) = Σ_{n ≤ y} (y - n) Λ(n)` and each weight grows by at most `h`, exactly `h` for `n ≤ x`;
* `psi_RH_34`: under RH and Trudgian 2014's `N(T)` bound, from cloud45's `psi1_RH_simple`,
  `|ψ₁(y) - y²/2| ≤ 133 y^{3/2}`, with `h = 32 x^{3/4}`:
  `|ψ(x) - x| ≤ 32 x^{3/4}` for every `x ≥ 64⁴`.
The exponent is the trivial one from one unsmoothing; Schoenfeld's `√x log² x / 8π` needs the
truncated explicit formula for `ψ` itself. Binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Real Finset
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.Dudek2014.Section22

/-- **Unsmoothing.** `h ψ(x) ≤ ψ₁(x + h) - ψ₁(x) ≤ h ψ(x + h)`. -/
theorem psi1_diff_bounds {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) :
    h * psiF x ≤ psi1 (x + h) - psi1 x ∧ psi1 (x + h) - psi1 x ≤ h * psiF (x + h) := by
  set M := ⌊x + h⌋₊ with hM
  have hxM : ⌊x⌋₊ ≤ M := Nat.floor_le_floor (by linarith)
  have e1 := psi1_ext (show 0 ≤ x + h by linarith) (le_refl M)
  have e0 := psi1_ext hx hxM
  have hdiff : psi1 (x + h) - psi1 x =
      ∑ n ∈ Iic M, (max (x + h - n) 0 - max (x - n) 0) * Λ n := by
    rw [← e1, ← e0, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => by ring
  have hΛ : ∀ n : ℕ, 0 ≤ Λ n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  constructor
  · -- lower: the terms with n ≤ ⌊x⌋ have weight exactly h
    rw [hdiff]
    have hsub : Iic ⌊x⌋₊ ⊆ Iic M := Iic_subset_Iic.2 hxM
    have hpsi : h * psiF x = ∑ n ∈ Iic ⌊x⌋₊, (max (x + h - n) 0 - max (x - n) 0) * Λ n := by
      unfold psiF
      rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      rw [mem_Iic] at hn
      have hn' : (n : ℝ) ≤ x := by
        have : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
        exact this.trans (Nat.floor_le hx)
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
    rw [hpsi]
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro n _ _
    apply mul_nonneg _ (hΛ n)
    have : max (x - n) 0 ≤ max (x + h - n) 0 := max_le_max (by linarith) le_rfl
    linarith
  · -- upper: every weight grows by at most h
    rw [hdiff]
    unfold psiF
    rw [← hM, mul_sum]
    refine sum_le_sum fun n _ => ?_
    apply mul_le_mul_of_nonneg_right _ (hΛ n)
    rcases le_total (x - n) 0 with h1 | h1
    · rw [max_eq_right h1]
      rcases le_total (x + h - n) 0 with h2 | h2
      · rw [max_eq_right h2]; linarith
      · rw [max_eq_left h2]; linarith
    · rw [max_eq_left h1, max_eq_left (by linarith)]; linarith

/-- `y^{3/2}` in terms of `v = x^{1/4}`. -/
lemma rpow32_of {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = (x ^ (1 / 4 : ℝ)) ^ 6 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma rpow34_of {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 4 : ℝ) = (x ^ (1 / 4 : ℝ)) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma rpow1_of {x : ℝ} (hx : 0 ≤ x) : x = (x ^ (1 / 4 : ℝ)) ^ 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- `(2x)^{3/2} ≤ 2.8285 x^{3/2}`. -/
lemma two_rpow32 {x : ℝ} (hx : 0 ≤ x) : (2 * x) ^ (3 / 2 : ℝ) ≤ 2.8285 * x ^ (3 / 2 : ℝ) := by
  rw [Real.mul_rpow (by norm_num) hx]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx _)
  have : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * √2 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [this]
  have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ 1.41425 ^ 2 by norm_num)
  rw [Real.sqrt_sq (by norm_num)] at h
  linarith

/-- **`|ψ(x) - x| ≤ 32 x^{3/4}` for `x ≥ 64⁴`, CONDITIONAL ON RH and Trudgian's `N(T)`.** -/
theorem psi_RH_34 (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 gZ) {x : ℝ} (hx : 64 ^ 4 ≤ x) :
    |psiF x - x| ≤ 32 * x ^ (3 / 4 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  set v := x ^ (1 / 4 : ℝ) with hv
  have hv0 : 0 ≤ v := Real.rpow_nonneg hx0 _
  have hxv : x = v ^ 4 := rpow1_of hx0
  have hv64 : 64 ≤ v := by
    by_contra hlt
    push Not at hlt
    have : v ^ 4 < 64 ^ 4 := pow_lt_pow_left₀ hlt hv0 (by norm_num)
    linarith
  set h := 32 * v ^ 3 with hhdef
  have hh0 : 0 < h := by positivity
  have hhx : h ≤ x / 2 := by
    rw [hxv, hhdef]
    have : 0 ≤ v ^ 3 := by positivity
    nlinarith
  have h34 : x ^ (3 / 4 : ℝ) = v ^ 3 := rpow34_of hx0
  have h32 : x ^ (3 / 2 : ℝ) = v ^ 6 := rpow32_of hx0
  have bound := fun y (hy : 1 < y) => psi1_RH_simple hRH hN hy
  -- the three ψ₁ values
  have hxh : 1 < x + h := by linarith
  have hxm : 1 < x - h := by linarith
  have b1 := abs_le.1 (bound (x + h) hxh)
  have b0 := abs_le.1 (bound x (by linarith))
  have bm := abs_le.1 (bound (x - h) hxm)
  -- 3/2 powers
  have p1 : (x + h) ^ (3 / 2 : ℝ) ≤ 2.8285 * v ^ 6 := by
    have := Real.rpow_le_rpow (by linarith) (show x + h ≤ 2 * x by linarith)
      (show (0 : ℝ) ≤ 3 / 2 by norm_num)
    have := (this.trans (two_rpow32 hx0)); rwa [h32] at this
  have pm : (x - h) ^ (3 / 2 : ℝ) ≤ v ^ 6 := by
    have := Real.rpow_le_rpow (by linarith) (show x - h ≤ x by linarith)
      (show (0 : ℝ) ≤ 3 / 2 by norm_num)
    rwa [h32] at this
  have p1' : 0 ≤ (x + h) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have pm' : 0 ≤ (x - h) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  rw [h32] at b0
  -- unsmoothing at x and at x - h
  obtain ⟨u1, -⟩ := psi1_diff_bounds hx0 hh0
  obtain ⟨-, u2⟩ := psi1_diff_bounds (show 0 ≤ x - h by linarith) hh0
  rw [sub_add_cancel] at u2
  rw [h34, abs_le]
  have hv3 : 0 < v ^ 3 := by positivity
  have hv6 : v ^ 6 = v ^ 3 * v ^ 3 := by ring
  constructor
  · -- lower: h ψ(x) ≥ ψ₁(x) - ψ₁(x - h)
    have : h * psiF x ≥ x * h - h ^ 2 / 2 - 133 * v ^ 6 - 133 * v ^ 6 := by nlinarith
    -- divide by h = 32 v³: ψ(x) ≥ x - 16 v³ - 266 v³ / 32
    have e : x * h - h ^ 2 / 2 - 133 * v ^ 6 - 133 * v ^ 6 =
        h * (x - 16 * v ^ 3 - 266 / 32 * v ^ 3) := by rw [hhdef, hv6]; ring
    rw [e] at this
    have := le_of_mul_le_mul_left this hh0
    linarith
  · -- upper: h ψ(x) ≤ ψ₁(x + h) - ψ₁(x)
    have : h * psiF x ≤ x * h + h ^ 2 / 2 + 133 * (2.8285 * v ^ 6) + 133 * v ^ 6 := by nlinarith
    have e : x * h + h ^ 2 / 2 + 133 * (2.8285 * v ^ 6) + 133 * v ^ 6 =
        h * (x + 16 * v ^ 3 + 133 * 3.8285 / 32 * v ^ 3) := by rw [hhdef, hv6]; ring
    rw [e] at this
    have := le_of_mul_le_mul_left this hh0
    linarith

end LeanLab.PNTPort.ExplicitPsi1.Trivial
