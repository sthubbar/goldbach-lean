module

public import Mathlib

/-!
# Helfgott's book, Part IV of 2020-04-01, Lemma 16.14: the numerical constants of its proof

Unit U-6716, CLOUD 20261020T1914Z-cloud49, P0014. AI wrote this file.

Source: book pages 437 to 439, copy papers/P0014-book-PartIV.pdf, page images checked. With
`υ(r) = √((1 + √(r² + 1))/2)` as in (15.3), so `υ(4) = √((1 + √17)/2)`:

* `half_arccos_ge`: `(1/2) arccos (1/υ(4)) ≥ 0.44795`, PROVED from `arctan z ≥ z - z³/3`;
* `R_ge`: `R ≥ (1/2)arccos(1/υ(4)) - 1/((T+c) log) - 1/(2T) ≥ 0.42295` for `T ≥ 40`, `log ≥ 2`;
* `bound_5_92654`, `bound_5_59578`: `√(2π) min(1, ·)/R ≤ 5.92654`, `/R₁ ≤ 5.59578`;
* `quarter_ge`, `inv_le_r_div_32`, `R_ge_r`: `0.11198 r`, `1/((T+c)log) ≤ r/32`, `0.08072 r`;
* `bound_15_52669`, `bound_11_19231`: the `r < 4` constants `15.52669/√r` and `11.19231/√r`;
* `rounded`: `5.92654 ≤ 5.927`, `15.52669 ≤ 15.527`, `5.59578 ≤ 5.6`, `11.19231 ≤ 11.2`, the
  constants of (16.35) and (16.36);
* `decreasing_step`: `g'(t) t ≥ 0.11198 t²/(π²δ²) > 1/2` for `t ≥ 4π|δ|`.

All MATCH, see gen/book_c1614_1618_U6716.out. The analytic steps, Lemma 16.12, the convexity
of `E(r) r` from Lemma 15.23 and the concavity of `(1/2) arccos (1/υ(r))`, are the book's; the
last two were also checked on a grid in the script. Ternary Goldbach is a theorem; binary
Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-20.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.BookL1614
open Real

/-- `υ(4) = √((1 + √17)/2)`, (15.3) at `r = 4`. -/
noncomputable def ups4 : ℝ := √((1 + √17) / 2)

/-- `arctan z ≥ z - z³/3` for `z ≥ 0`: the derivative of `arctan z - z + z³/3` is
`z⁴/(1 + z²) ≥ 0`. -/
theorem arctan_ge_sub_cube {z : ℝ} (hz : 0 ≤ z) : z - z ^ 3 / 3 ≤ arctan z := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => arctan x - x + x ^ 3 / 3)
      (1 / (1 + x ^ 2) - 1 + 3 * x ^ 2 / 3) x := by
    intro x
    have h := ((hasDerivAt_arctan x).sub (hasDerivAt_id x)).add ((hasDerivAt_pow 3 x).div_const 3)
    convert h using 1
    · funext y; simp
  have hmono : Monotone (fun x => arctan x - x + x ^ 3 / 3) := by
    apply monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have : 1 / (1 + x ^ 2) - 1 + 3 * x ^ 2 / 3 = x ^ 4 / (1 + x ^ 2) := by
      field_simp; ring
    rw [this]; positivity
  have := hmono hz
  simp at this
  linarith

lemma sqrt17_gt : (4.1231056 : ℝ) < √17 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

/-- **`(1/2) arccos (1/υ(4)) ≥ 0.44795`**, book p. 438; value 0.4479537406. -/
theorem half_arccos_ge : (0.44795 : ℝ) ≤ arccos (1 / ups4) / 2 := by
  have h17 := sqrt17_gt
  have hu2 : ups4 ^ 2 = (1 + √17) / 2 := by
    unfold ups4; rw [Real.sq_sqrt (by positivity)]
  have hu0 : 0 < ups4 := by unfold ups4; positivity
  have hy : 0 < 1 / ups4 := by positivity
  rw [arccos_eq_arctan hy]
  set X0 : ℝ := 1.249621
  -- X0 ≤ √(1 - y²)/y
  have hX : X0 ≤ √(1 - (1 / ups4) ^ 2) / (1 / ups4) := by
    rw [le_div_iff₀ hy]
    apply Real.le_sqrt_of_sq_le
    have e : (1 / ups4) ^ 2 = 1 / ups4 ^ 2 := by ring
    rw [mul_pow, e, hu2]
    rw [show X0 ^ 2 * (1 / ((1 + √17) / 2)) = 2 * X0 ^ 2 / (1 + √17) by field_simp]
    rw [show 1 - 1 / ((1 + √17) / 2) = (√17 - 1) / (1 + √17) by field_simp; ring]
    rw [div_le_div_iff_of_pos_right (by positivity)]
    simp only [X0]; linarith
  have hmono : arctan X0 ≤ arctan (√(1 - (1 / ups4) ^ 2) / (1 / ups4)) :=
    arctan_le_arctan_iff.mpr hX
  set z0 : ℝ := (X0 - 1) / (X0 + 1)
  have hz0 : 0 ≤ z0 := by simp only [z0, X0]; norm_num
  have hadd : arctan 1 + arctan z0 = arctan X0 := by
    rw [arctan_add (by simp only [z0, X0]; norm_num)]
    congr 1; simp only [z0, X0]; norm_num
  rw [arctan_one] at hadd
  have hat := arctan_ge_sub_cube hz0
  have hpi := pi_gt_d20
  have hz : (0.1105028 : ℝ) ≤ z0 - z0 ^ 3 / 3 := by simp only [z0, X0]; norm_num
  linarith

/-- **`R ≥ 0.42295`**, book p. 438: `R ≥ A - 1/((T+c) log(q(T+c)/2π)) - 1/(2T)` with
`A ≥ 0.44795`, `T ≥ 40`, `c ≥ 0` and `log(q(T+c)/2π) ≥ 2`. -/
theorem R_ge {A T c ℓ : ℝ} (hA : 0.44795 ≤ A) (hT : 40 ≤ T) (hc : 0 ≤ c) (hℓ : 2 ≤ ℓ) :
    0.42295 ≤ A - 1 / ((T + c) * ℓ) - 1 / (2 * T) := by
  have h1 : 1 / ((T + c) * ℓ) ≤ 1 / 80 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h2 : 1 / (2 * T) ≤ 1 / 80 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

lemma sqrt_two_pi_lt : √(2 * π) < 2.5066283 := by
  rw [Real.sqrt_lt' (by norm_num)]; have := pi_lt_d20; nlinarith

lemma sqrt_two_pi_pos : 0 < √(2 * π) := by positivity

/-- **`√(2π) min(1, √t/2π|δ|)/R ≤ √(2π)/R ≤ 5.92654`** for `R ≥ 0.42295`, book p. 438. -/
theorem bound_5_92654 {R m : ℝ} (hR : 0.42295 ≤ R) (hm0 : 0 ≤ m) (hm : m ≤ 1) :
    1 / R * √(2 * π) * m ≤ 5.92654 := by
  have hs := sqrt_two_pi_lt; have hs0 := sqrt_two_pi_pos
  have hR0 : 0 < R := by linarith
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ hR0]
  nlinarith

/-- **`√(2π)/R₁ ≤ 5.59578`** for `R₁ ≥ 0.44795`, book p. 439. -/
theorem bound_5_59578 {R m : ℝ} (hR : 0.44795 ≤ R) (hm0 : 0 ≤ m) (hm : m ≤ 1) :
    1 / R * √(2 * π) * m ≤ 5.59578 := by
  have hs := sqrt_two_pi_lt; have hs0 := sqrt_two_pi_pos
  have hR0 : 0 < R := by linarith
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ hR0]
  nlinarith

/-- **(16.37), last step: `A/4 ≥ 0.11198`.** -/
theorem quarter_ge {A : ℝ} (hA : 0.44795 ≤ A) : 0.11198 ≤ A / 4 := by linarith

/-- **`1/((T+c) log) ≤ 1/(2T) ≤ r/32`** with `r = T/(π²δ²)` and `T ≥ 4π|δ|`, book p. 438. -/
theorem inv_le_r_div_32 {T d c ℓ : ℝ} (hd : 0 < d) (hT : 4 * π * d ≤ T) (hc : 0 ≤ c)
    (hℓ : 2 ≤ ℓ) : 1 / ((T + c) * ℓ) ≤ (T / (π ^ 2 * d ^ 2)) / 32 := by
  have hpi := pi_pos
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have h1 : 1 / ((T + c) * ℓ) ≤ 1 / (2 * T) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : 1 / (2 * T) ≤ (T / (π ^ 2 * d ^ 2)) / 32 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (4 * π * d) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by positivity) hT 2
    nlinarith
  linarith

/-- **`R ≥ (0.11198 - 1/32) r ≥ 0.08072 r`**, book p. 438. -/
theorem R_ge_r {R A e r : ℝ} (hr : 0 ≤ r) (hA : 0.11198 * r ≤ A) (he : e ≤ r / 32)
    (hR : A - e ≤ R) : 0.08072 * r ≤ R := by linarith

/-- `√T/(2π|δ|) = √r/2` with `r = T/(π²δ²)`: the `min` of (16.34) at `T`. -/
theorem sqrt_ratio {T d : ℝ} (hT : 0 ≤ T) (hd : 0 < d) :
    √T / (2 * π * d) = √(T / (π ^ 2 * d ^ 2)) / 2 := by
  have hpi := pi_pos
  rw [Real.sqrt_div hT, Real.sqrt_mul (by positivity), Real.sqrt_sq hpi.le,
    Real.sqrt_sq hd.le]
  field_simp

/-- **`√(2π) m/R ≤ 15.52669/√r`** for `m ≤ √r/2` and `R ≥ 0.08072 r`, book p. 438. -/
theorem bound_15_52669 {R m r : ℝ} (hr : 0 < r) (hR : 0.08072 * r ≤ R) (hm0 : 0 ≤ m)
    (hm : m ≤ √r / 2) : 1 / R * √(2 * π) * m ≤ 15.52669 / √r := by
  have hs := sqrt_two_pi_lt; have hs0 := sqrt_two_pi_pos
  have hq0 : 0 < √r := Real.sqrt_pos.mpr hr
  have hq2 : √r ^ 2 = r := Real.sq_sqrt hr.le
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_div_iff₀ hR0 hq0]
  have h1 : √(2 * π) * m * √r ≤ 2.5066283 * (r / 2) := by
    have : m * √r ≤ r / 2 := by nlinarith
    nlinarith
  nlinarith

/-- **`√(2π) m/R₁ ≤ 11.19231/√r`** for `m ≤ √r/2` and `R₁ ≥ 0.11198 r`, book p. 439. -/
theorem bound_11_19231 {R m r : ℝ} (hr : 0 < r) (hR : 0.11198 * r ≤ R) (hm0 : 0 ≤ m)
    (hm : m ≤ √r / 2) : 1 / R * √(2 * π) * m ≤ 11.19231 / √r := by
  have hs := sqrt_two_pi_lt; have hs0 := sqrt_two_pi_pos
  have hq0 : 0 < √r := Real.sqrt_pos.mpr hr
  have hq2 : √r ^ 2 = r := Real.sq_sqrt hr.le
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_div_iff₀ hR0 hq0]
  have h1 : √(2 * π) * m * √r ≤ 2.5066283 * (r / 2) := by
    have : m * √r ≤ r / 2 := by nlinarith
    nlinarith
  nlinarith

/-- **The constants of (16.35) and (16.36)** are the proof's, rounded up. -/
theorem rounded : (5.92654 : ℝ) ≤ 5.927 ∧ (15.52669 : ℝ) ≤ 15.527 ∧ (5.59578 : ℝ) ≤ 5.6 ∧
    (11.19231 : ℝ) ≤ 11.2 := by norm_num

/-- **`φ` decreasing on `[T, (2πδ)²)`**, book p. 439: `0.11198 t²/(π²δ²) > 1/2` for
`t ≥ 4π|δ|`. -/
theorem decreasing_step {t d : ℝ} (hd : 0 < d) (ht : 4 * π * d ≤ t) :
    1 / 2 < 0.11198 * (t ^ 2 / (π ^ 2 * d ^ 2)) := by
  have hpi := pi_pos
  have : (4 * π * d) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) ht 2
  have h16 : 16 ≤ t ^ 2 / (π ^ 2 * d ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

end LeanLab.HelfgottMajor.BookL1614
