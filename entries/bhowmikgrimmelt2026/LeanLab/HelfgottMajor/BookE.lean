module

public import Mathlib
public import LeanLab.HelfgottMajor.BookL1614
public import LeanLab.HelfgottMajor.BookT141
public import LeanLab.HelfgottMajor.BookT143

/-!
# Helfgott's book, Part IV of 2020-04-01: the values of `E(r)` used in Theorems 14.1 to 14.3

Unit U-1411, PC run 20261021T1303Z-13145, P0014. AI wrote this file.

`E(r) = (1/2)(arccos(1/υ(r)) - 2(υ(r) - 1)/r)` with `υ(r) = √((1 + √(1 + r²))/2)`, the
function of (15.2) of the book; the same formula is (3.2) of arXiv 1305.2897, read on ar5iv
in this unit. Recomputed in gen/u1411_check.py, scratch, with mpmath: the five values below
reproduce the book's printed 68.16791, 41.62864, 21.21593, 23.38383, 49.47 to every digit.

Method: `arccos(1/υ) = arctan √(υ² - 1)` and `υ² - 1 = (√(1 + r²) - 1)/2`; then
`arctan X = π/4 - arctan((1 - X)/(1 + X))` and the alternating series bound
`arctan w ≤ w - w³/3 + ... + w¹⁷/17` for `w ≥ 0`, proved by the derivative
`w¹⁸/(1 + w²) ≥ 0`; the case `r = 0.001` uses `arctan z ≥ z - z³/3` of BookL1614.
The radii `r₀` involve `π`, handled by `pi_gt_d20`, `pi_lt_d20` and monotonicity.

PROVED:
* `arctan_le_poly17`, `arctan_ge_of_lt_one`, `arccos_inv`, `E_lower`: the tools;
* `E_c3`: `E(125/(6π²))·1000/3 ≥ 68.16791`, the `c = 3` input of Theorem 14.1, p. 447;
* `E_c4`: `E(125/(8π²))·250 ≥ 41.62864`, the `c = 4` input of Thm. 14.1 and of Thm. 14.3 p. 2;
* `E_p1`: `E(1375/(128π²))·1375/8 ≥ 21.21593`, Theorem 14.3 part 1, p. 449;
* `E_small`: `E(0.001)/(0.001π²)·(1375/32)² ≥ 23.38383` and `·(125/2)² ≥ 49.47`;
* `lead_c3_E`, `lead_c4_E`, `lead_p1_E`, `lead_p2_E`: BookT141's `lead_c3`, `lead_c4` and
  BookT143's `lead_p1`, `lead_p2` with the `E` value discharged.

CONDITIONAL ON Lemma 15.23 of the book, `E(r)/r` non-increasing, which carries the bound
from `r = 0.001` to all `r ≤ 0.001`: `small_p1_E`, `small_p2_E`.

Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN. AI-written Lean code,
Claude, 2026-10-21.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.BookE
open Real

/-- `υ(r) = √((1 + √(1 + r²))/2)`, (15.3) of the book. -/
noncomputable def ups (r : ℝ) : ℝ := √((1 + √(1 + r ^ 2)) / 2)

/-- `E(r) = (1/2) arccos(1/υ(r)) - (υ(r) - 1)/r`, (15.2) of the book, (3.2) of 1305.2897. -/
noncomputable def E (r : ℝ) : ℝ := arccos (1 / ups r) / 2 - (ups r - 1) / r

/-- The alternating Taylor polynomial of `arctan` of degree 17. -/
noncomputable def P17 (w : ℝ) : ℝ :=
  w - w ^ 3 / 3 + w ^ 5 / 5 - w ^ 7 / 7 + w ^ 9 / 9 - w ^ 11 / 11 + w ^ 13 / 13 - w ^ 15 / 15 +
    w ^ 17 / 17

/-- **`arctan w ≤ P17 w` for `w ≥ 0`**: the derivative of `P17 - arctan` is `w¹⁸/(1 + w²)`. -/
theorem arctan_le_poly17 {w : ℝ} (hw : 0 ≤ w) : arctan w ≤ P17 w := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => P17 x - arctan x)
      (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14 + x ^ 16 - 1 / (1 + x ^ 2))
      x := by
    intro x
    have h := ((((((((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 3)).add
      ((hasDerivAt_pow 5 x).div_const 5)).sub ((hasDerivAt_pow 7 x).div_const 7)).add
      ((hasDerivAt_pow 9 x).div_const 9)).sub ((hasDerivAt_pow 11 x).div_const 11)).add
      ((hasDerivAt_pow 13 x).div_const 13)).sub ((hasDerivAt_pow 15 x).div_const 15)).add
      ((hasDerivAt_pow 17 x).div_const 17)).sub (hasDerivAt_arctan x))
    convert h using 1
    · funext y; simp [P17]
    · push_cast; ring
  have hmono : Monotone (fun x => P17 x - arctan x) := by
    apply monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have : 1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14 + x ^ 16 - 1 / (1 + x ^ 2)
        = x ^ 18 / (1 + x ^ 2) := by
      field_simp; ring
    rw [this]; positivity
  have := hmono hw
  simp [P17] at this
  simp only [P17]; linarith

/-- **`arctan X ≥ π/4 - P17((1 - X)/(1 + X))` for `0 ≤ X < 1`**, from
`arctan X + arctan((1 - X)/(1 + X)) = arctan 1`. -/
theorem arctan_ge_of_lt_one {X : ℝ} (h0 : 0 ≤ X) (h1 : X < 1) :
    π / 4 - P17 ((1 - X) / (1 + X)) ≤ arctan X := by
  have hX1 : 0 < 1 + X := by linarith
  have hw : 0 ≤ (1 - X) / (1 + X) := div_nonneg (by linarith) hX1.le
  have hprod : X * ((1 - X) / (1 + X)) < 1 := by
    rw [mul_div_assoc', div_lt_one hX1]; nlinarith
  have hadd := arctan_add hprod
  have hone : (X + (1 - X) / (1 + X)) / (1 - X * ((1 - X) / (1 + X))) = 1 := by
    rw [div_eq_one_iff_eq (by
      have : X * ((1 - X) / (1 + X)) < 1 := hprod
      linarith)]
    field_simp; ring
  rw [hone, arctan_one] at hadd
  have := arctan_le_poly17 hw
  linarith

/-- **`arccos(1/u) = arctan √(u² - 1)`** for `u ≥ 1`. -/
theorem arccos_inv {u : ℝ} (hu : 1 ≤ u) : arccos (1 / u) = arctan √(u ^ 2 - 1) := by
  have hu0 : 0 < u := by linarith
  rw [arccos_eq_arctan (by positivity)]
  congr 1
  have hy : 1 / u ≤ 1 := by rw [div_le_one hu0]; exact hu
  have hn : 0 ≤ 1 - (1 / u) ^ 2 := by
    have : 0 ≤ 1 / u := by positivity
    nlinarith
  calc √(1 - (1 / u) ^ 2) / (1 / u) = √(1 - (1 / u) ^ 2) * √(u ^ 2) := by
        rw [sqrt_sq hu0.le]; field_simp
    _ = √((1 - (1 / u) ^ 2) * u ^ 2) := (sqrt_mul hn _).symm
    _ = √(u ^ 2 - 1) := by congr 1; field_simp

/-- **A rational lower bound for `E(r)`**: from `rL ≤ r ≤ rU`, `sL ≤ √(1 + r²) ≤ sU`,
`XL ≤ √(υ² - 1)` and `υ ≤ uU`, witnessed by squares. -/
theorem E_lower {r rL rU sL sU XL uU : ℝ} (hrL : 0 < rL) (h1 : rL ≤ r) (h2 : r ≤ rU)
    (hsL : sL ^ 2 ≤ 1 + rL ^ 2) (hsU0 : 0 ≤ sU) (hsU : 1 + rU ^ 2 ≤ sU ^ 2)
    (hXL : XL ^ 2 ≤ (sL - 1) / 2) (huU0 : 0 ≤ uU) (huU : (1 + sU) / 2 ≤ uU ^ 2) :
    arctan XL / 2 - (uU - 1) / rL ≤ E r := by
  have hr0 : 0 < r := by linarith
  set s := √(1 + r ^ 2) with hs
  have hsL' : sL ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsU' : s ≤ sU := (sqrt_le_sqrt (by nlinarith)).trans_eq (sqrt_sq hsU0)
  have hs1 : 1 ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hud : ups r = √((1 + s) / 2) := rfl
  have hu2 : ups r ^ 2 = (1 + s) / 2 := by rw [hud, sq_sqrt (by linarith)]
  have hu1 : 1 ≤ ups r := by rw [hud]; exact Real.le_sqrt_of_sq_le (by linarith)
  have huU' : ups r ≤ uU := by
    rw [hud]; exact (sqrt_le_sqrt (by linarith)).trans_eq (sqrt_sq huU0)
  have hX : XL ≤ √(ups r ^ 2 - 1) := Real.le_sqrt_of_sq_le (by rw [hu2]; linarith)
  have hat : arctan XL ≤ arctan √(ups r ^ 2 - 1) := arctan_strictMono.monotone hX
  have hfrac : (ups r - 1) / r ≤ (uU - 1) / rL := by
    calc (ups r - 1) / r ≤ (uU - 1) / r := by gcongr
      _ ≤ (uU - 1) / rL := by
        apply div_le_div_of_nonneg_left (by linarith) hrL h1
  unfold E
  rw [arccos_inv hu1]
  linarith

lemma pi_lo : (3.14159265358979323846 : ℝ) < π := pi_gt_d20
lemma pi_hi : π < (3.14159265358979323847 : ℝ) := pi_lt_d20

lemma pi_sq_hi : π ^ 2 < (3.14159265358979323847 : ℝ) ^ 2 := by
  have := pi_hi; have := pi_pos; nlinarith

lemma pi_sq_lo : (3.14159265358979323846 : ℝ) ^ 2 < π ^ 2 := by
  have := pi_lo; nlinarith

/-- `rL ≤ a/(bπ²) ≤ rU` from the π bounds, when `rL b pU² ≤ a ≤ rU b pL²`. -/
lemma r_bounds {a b rL rU : ℝ} (hb : 0 < b)
    (hL : rL * (b * (3.14159265358979323847 : ℝ) ^ 2) ≤ a)
    (hU : a ≤ rU * (b * (3.14159265358979323846 : ℝ) ^ 2)) (hrU : 0 ≤ rU) (hrL : 0 ≤ rL) :
    rL ≤ a / (b * π ^ 2) ∧ a / (b * π ^ 2) ≤ rU := by
  have h1 := pi_sq_hi; have h2 := pi_sq_lo
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1.le (mul_nonneg hrL hb.le)]
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2.le (mul_nonneg hrU hb.le)]

/-- **`c = 3`, Theorem 14.1, book p. 447: `E(r₀)·1000/3 ≥ 68.16791`** at `r₀ = 125/(6π²)`;
value 68.1679125. -/
theorem E_c3 : 68.16791 ≤ E (125 / (6 * π ^ 2)) * 1000 / 3 := by
  obtain ⟨h1, h2⟩ := r_bounds (a := 125) (b := 6) (rL := 2.1108579925487035)
    (rU := 2.1108579925487036) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hE := E_lower (sL := 2.3357485876495232) (sU := 2.3357485876495233)
    (XL := 0.8172357639168525) (uU := 1.2914620760304043) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ha := arctan_ge_of_lt_one (X := 0.8172357639168525) (by norm_num) (by norm_num)
  have hp := pi_lo
  simp only [P17] at ha
  norm_num at ha hE ⊢
  linarith

/-- **`c = 4` of Theorem 14.1 and part 2 of Theorem 14.3: `250 E(r₀) ≥ 41.62864`** at
`r₀ = 125/(8π²)`; value 41.6286432. -/
theorem E_c4 : 41.62864 ≤ E (125 / (8 * π ^ 2)) * 250 := by
  obtain ⟨h1, h2⟩ := r_bounds (a := 125) (b := 8) (rL := 1.5831434944115276)
    (rU := 1.5831434944115277) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hE := E_lower (sL := 1.8725232505626045) (sU := 1.8725232505626046)
    (XL := 0.6605010410902485) (uU := 1.1984413315975473) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ha := arctan_ge_of_lt_one (X := 0.6605010410902485) (by norm_num) (by norm_num)
  have hp := pi_lo
  simp only [P17] at ha
  norm_num at ha hE ⊢
  linarith

/-- **Part 1 of Theorem 14.3, p. 449: `E(r₀)·1375/8 ≥ 21.21593`** at `r₀ = 1375/(128π²)`;
value 21.2159307. -/
theorem E_p1 : 21.21593 ≤ E (1375 / (128 * π ^ 2)) * 1375 / 8 := by
  obtain ⟨h1, h2⟩ := r_bounds (a := 1375) (b := 128) (rL := 1.0884111524079252)
    (rU := 1.0884111524079253) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hE := E_lower (sL := 1.4780523795474732) (sU := 1.4780523795474733)
    (XL := 0.4889030474171096) (uU := 1.1131155329855642) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ha := arctan_ge_of_lt_one (X := 0.4889030474171096) (by norm_num) (by norm_num)
  have hp := pi_lo
  simp only [P17] at ha
  norm_num at ha hE ⊢
  linarith

/-- `E(0.001) ≥ 1.2499998697916·10⁻⁴`; value 1.24999986979·10⁻⁴, the witnesses give 1.2499998691·10⁻⁴. -/
theorem E_001 : 1.2499998691e-4 ≤ E 0.001 := by
  have hE := E_lower (rL := 0.001) (rU := 0.001) (sL := 1.0000004999998750)
    (sU := 1.0000004999998751) (XL := 0.0004999999374999) (uU := 1.0000001249999610)
    (by norm_num) le_rfl le_rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ha := BookL1614.arctan_ge_sub_cube (z := 0.0004999999374999) (by norm_num)
  norm_num at ha hE ⊢
  linarith

/-- **(16.61), (16.62) at `r = 0.001`**: `E(0.001)/(0.001π²)·(1375/32)² ≥ 23.38383` and
`E(0.001)/(0.001π²)·(125/2)² ≥ 49.47`; values 23.3838309, 49.4732290. -/
theorem E_small :
    23.38383 ≤ E 0.001 / (0.001 * π ^ 2) * (1375 / 32) ^ 2 ∧
    49.47 ≤ E 0.001 / (0.001 * π ^ 2) * (125 / 2) ^ 2 := by
  have h := E_001
  have hp := pi_sq_hi
  have hp0 : 0 < π ^ 2 := by positivity
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith

/-! ## The lead terms with `E` discharged -/

/-- **Theorem 14.1, `c = 3`**: `1.14 π√(6/125) e^{-E(r₀)·1000/3} ≤ 1.94863·10⁻³⁰`. -/
theorem lead_c3_E :
    1.14 * (π * √(6 / 125)) * exp (-(E (125 / (6 * π ^ 2)) * 1000 / 3)) ≤ 1.94863e-30 :=
  (BookT141.lead_c3 E_c3).2

/-- **Theorem 14.1, `c = 4`**: `1.14 π√(8/125) e^{-250 E(r₀)} ≤ 7.5519·10⁻¹⁹`. -/
theorem lead_c4_E :
    1.14 * (π * √(8 / 125)) * exp (-(E (125 / (8 * π ^ 2)) * 250)) ≤ 7.5519e-19 :=
  (BookT141.lead_c4 E_c4).2

/-- **Theorem 14.3 part 1, `r ≥ r₀`**: `2.72 π√(128/1375) e^{-E(r₀)·1375/8} ≤ 1.59299·10⁻⁹`. -/
theorem lead_p1_E :
    2.72 * (π * √(128 / 1375)) * exp (-(E (1375 / (128 * π ^ 2)) * 1375 / 8)) ≤ 1.59299e-9 :=
  (BookT143.lead_p1 E_p1).2

/-- **Theorem 14.3 part 2, `r ≥ r₀`**: `2.72 π√(8/125) e^{-250 E(r₀)} ≤ 1.80186·10⁻¹⁸`. -/
theorem lead_p2_E :
    2.72 * (π * √(8 / 125)) * exp (-(E (125 / (8 * π ^ 2)) * 250)) ≤ 1.80186e-18 :=
  (BookT143.lead_p2 E_c4).2

/-- **(16.61) at `r = 0.001`**: CONDITIONAL ON Lemma 15.23 where applied to `r < 0.001`. -/
theorem small_p1_E :
    2.72 * 606.225 * exp (-(E 0.001 / (0.001 * π ^ 2) * (1375 / 32) ^ 2)) ≤ 1.15275e-7 :=
  BookT143.small_p1 E_small.1

/-- **(16.62) at `r = 0.001`**: CONDITIONAL ON Lemma 15.23 where applied to `r < 0.001`. -/
theorem small_p2_E :
    2.72 * 584.033 * exp (-(E 0.001 / (0.001 * π ^ 2) * (125 / 2) ^ 2)) ≤ 5.46217e-19 :=
  BookT143.small_p2 E_small.2

end LeanLab.HelfgottMajor.BookE
