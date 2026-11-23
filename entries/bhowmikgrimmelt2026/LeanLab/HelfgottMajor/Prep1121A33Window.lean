module

public import LeanLab.HelfgottMajor.Prep1121A33Cells

/-!
P0014 page 67, display A.33, first line, near the maximum.

On the window `u ∈ [1/2, 4/5]`, about `ρ` in `[1.9, 7.7]`, the true maximum `0.07638957128`
at `u ≈ 0.649725`, `ρ ≈ 3.601486` leaves a margin of only `2.9e-8` to the printed
`0.0763896`, so first order cells would need about twenty thousand pieces. Here each of the
four square roots `√((1+u)(4-2u²))`, `√(1-u²)`, `√(4-2u²)`, `√(1-u)` is replaced by a
second order rational bound, tangent at `u = 0.65`, in the direction its sign needs. The result
is one explicit polynomial of degree six, whose Taylor expansion at `t0 = 406/625`
is dominated by its quadratic part on the window: minimum about `1.5e-7`, checked in python.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Prep1121A33Window

open Real LeanLab.HelfgottMajor.Prep1121A33Cells

/-- P0014 page 67, display A.33, first line, cleared of denominators:
`Φ(u) = 4B·aR - 4B·u·ab - u·R + u(2-u) - 2u(1-u)·b` with `B = 0.0763896`. -/
noncomputable def a33Phi (u : ℝ) : ℝ :=
  4 * 0.0763896 * √((1 + u) * (4 - 2 * u ^ 2)) - 4 * 0.0763896 * u * √(1 - u ^ 2) -
    u * √(4 - 2 * u ^ 2) + u * (2 - u) - 2 * u * (1 - u) * √(1 - u)

/-- The degree six lower polynomial for `a33Phi` on the window, P0014 page 67, display A.33,
built from the tangent bounds at `u = 0.65`. -/
noncomputable def a33Poly (u : ℝ) : ℝ :=
  4 * 0.0763896 * (((1 + u) * (4 - 2 * u ^ 2) + (2281611 / 1000000 : ℝ) ^ 2) / (2 * (2281611 / 1000000 : ℝ)) -
      ((1 + u) * (4 - 2 * u ^ 2) - (2281611 / 1000000 : ℝ) ^ 2) ^ 2 / (2 * (2281611 / 1000000 : ℝ) * ((2281611 / 1000000 : ℝ) + (11 / 5 : ℝ)) ^ 2)) -
    4 * 0.0763896 * u * ((1 - u ^ 2 + (379967 / 500000 : ℝ) ^ 2) / (2 * (379967 / 500000 : ℝ))) -
    u * ((4 - 2 * u ^ 2 + (222029 / 125000 : ℝ) ^ 2) / (2 * (222029 / 125000 : ℝ))) + u * (2 - u) -
    2 * u * (1 - u) * ((1 - u + (73951 / 125000 : ℝ) ^ 2) / (2 * (73951 / 125000 : ℝ)))

/-- P0014 page 67, display A.33, first line, window step; Mathlib lookup.
Tangent upper bound for a square root: `√x ≤ (x + c²)/(2c)`. -/
theorem sqrt_le_tangent (x c : ℝ) (hc : 0 < c) (hx : 0 ≤ x) :
    √x ≤ (x + c ^ 2) / (2 * c) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (√x - c), sq_sqrt hx]

/-- P0014 page 67, display A.33, first line, window step; inequality chain.
Second order lower bound for a square root: with `0 ≤ s ≤ √x`,
`(x + c²)/(2c) - (x - c²)²/(2c(c+s)²) ≤ √x`. -/
theorem sqrt_ge_tangent_sub (x c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s) (hx : 0 ≤ x)
    (hsx : s ≤ √x) :
    (x + c ^ 2) / (2 * c) - (x - c ^ 2) ^ 2 / (2 * c * (c + s) ^ 2) ≤ √x := by
  have hr := sq_sqrt hx
  have hy : 0 ≤ √x := sqrt_nonneg x
  -- (x+c²)/(2c) - √x = (√x - c)²/(2c) and (x-c²)² = (√x-c)²(√x+c)² ≥ (√x-c)²(c+s)²
  have h1 : (x + c ^ 2) / (2 * c) - √x = (√x - c) ^ 2 / (2 * c) := by
    field_simp
    nlinarith [hr]
  have h2 : (√x - c) ^ 2 / (2 * c) ≤ (x - c ^ 2) ^ 2 / (2 * c * (c + s) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : (x - c ^ 2) ^ 2 = (√x - c) ^ 2 * (√x + c) ^ 2 := by
      linear_combination (-(x + √x ^ 2 - 2 * c ^ 2)) * hr
    rw [e]
    have hcs : (c + s) ^ 2 ≤ (√x + c) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hcs (sq_nonneg (√x - c))
    nlinarith [sq_nonneg (√x - c), mul_nonneg (sq_nonneg (√x - c)) (sq_nonneg (c + s))]
  linarith

/-- P0014 page 67, display A.33, first line, window step; one clear idea.
A sextic in `t` whose cubic and higher part is at most `m w t²` on `|t| ≤ w` is nonnegative
when the remaining quadratic has nonpositive discriminant. -/
theorem quad_dominant (t w p0 p1 p2 p3 p4 p5 p6 a3 a4 a5 a6 m : ℝ)
    (ht : |t| ≤ w) (h3 : |p3| ≤ a3) (h4 : |p4| ≤ a4) (h5 : |p5| ≤ a5) (h6 : |p6| ≤ a6)
    (hM : a3 + a4 * w + a5 * w ^ 2 + a6 * w ^ 3 ≤ m) (hk : 0 < p2 - m * w)
    (hd : p1 ^ 2 ≤ 4 * p0 * (p2 - m * w)) :
    0 ≤ p0 + p1 * t + p2 * t ^ 2 + p3 * t ^ 3 + p4 * t ^ 4 + p5 * t ^ 5 + p6 * t ^ 6 := by
  have hw : 0 ≤ w := (abs_nonneg t).trans ht
  have tb : ∀ (p a : ℝ) (n : ℕ), |p| ≤ a → -(a * w ^ n * t ^ 2) ≤ p * t ^ (n + 2) := by
    intro p a n hp
    have hb : |p * t ^ (n + 2)| ≤ a * w ^ n * t ^ 2 := by
      rw [abs_mul, abs_pow, pow_add, sq_abs]
      have hn : |t| ^ n ≤ w ^ n := pow_le_pow_left₀ (abs_nonneg t) ht n
      calc |p| * (|t| ^ n * t ^ 2) ≤ a * (w ^ n * t ^ 2) :=
            mul_le_mul hp (mul_le_mul_of_nonneg_right hn (sq_nonneg t)) (by positivity)
              ((abs_nonneg p).trans hp)
        _ = a * w ^ n * t ^ 2 := by ring
    exact (abs_le.mp hb).1
  have k3 := tb p3 a3 1 h3
  have k4 := tb p4 a4 2 h4
  have k5 := tb p5 a5 3 h5
  have k6 := tb p6 a6 4 h6
  have hs : w * t ^ 2 * (a3 + a4 * w + a5 * w ^ 2 + a6 * w ^ 3) ≤ w * t ^ 2 * m :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have hq : 0 ≤ p0 + p1 * t + (p2 - m * w) * t ^ 2 := by
    nlinarith [sq_nonneg (2 * (p2 - m * w) * t + p1)]
  norm_num at k3 k4 k5 k6
  nlinarith

/-- P0014 page 67, display A.33, first line, window step; finite check with the
Taylor certificate at `t0 = 406/625`: the polynomial is nonnegative on `[1/2, 4/5]`. -/
theorem a33Poly_nonneg (u : ℝ) (h1 : 1 / 2 ≤ u) (h2 : u ≤ 4 / 5) : 0 ≤ a33Poly u := by
  have ht : |u - (406 / 625 : ℝ)| ≤ (94 / 625 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have key := quad_dominant (u - (406 / 625 : ℝ)) (94 / 625 : ℝ) (198960086372135924276642958879782244604999 / 1329505993317454399442424763417433886718750000000 : ℝ) (281984991475046004658343157725778255658133 / 4254419178615854078215759242935788437500000000 : ℝ) (1306866815617500312756870747097792415853 / 1701767671446341631286303697174315375000 : ℝ) (-75193607225011617774202485085653396 / 68070706857853665251452147886972615 : ℝ) (-2001550602813440000 / 15275261795596367377 : ℝ) (-1201374146560000000 / 15275261795596367377 : ℝ) (-203705600000000000 / 15275261795596367377 : ℝ) (3452 / 3125 : ℝ) (131033 / 1000000 : ℝ) (78649 / 1000000 : ℝ) (1667 / 125000 : ℝ) (5631 / 5000 : ℝ) ht
    (abs_le.mpr ⟨by norm_num, by norm_num⟩) (abs_le.mpr ⟨by norm_num, by norm_num⟩)
    (abs_le.mpr ⟨by norm_num, by norm_num⟩) (abs_le.mpr ⟨by norm_num, by norm_num⟩)
    (by norm_num) (by norm_num) (by norm_num)
  have e : a33Poly u = (198960086372135924276642958879782244604999 / 1329505993317454399442424763417433886718750000000 : ℝ) + (281984991475046004658343157725778255658133 / 4254419178615854078215759242935788437500000000 : ℝ) * (u - (406 / 625 : ℝ)) + (1306866815617500312756870747097792415853 / 1701767671446341631286303697174315375000 : ℝ) * (u - (406 / 625 : ℝ)) ^ 2 + (-75193607225011617774202485085653396 / 68070706857853665251452147886972615 : ℝ) * (u - (406 / 625 : ℝ)) ^ 3 +
      (-2001550602813440000 / 15275261795596367377 : ℝ) * (u - (406 / 625 : ℝ)) ^ 4 + (-1201374146560000000 / 15275261795596367377 : ℝ) * (u - (406 / 625 : ℝ)) ^ 5 + (-203705600000000000 / 15275261795596367377 : ℝ) * (u - (406 / 625 : ℝ)) ^ 6 := by
    unfold a33Poly
    ring
  rw [e]
  exact key

/-- P0014 page 67, display A.33, first line, window step; inequality chain.
The four tangent bounds, each in the direction of its coefficient's sign, give
`a33Poly u ≤ a33Phi u` on the window. -/
theorem a33Poly_le_Phi (u : ℝ) (h1 : 1 / 2 ≤ u) (h2 : u ≤ 4 / 5) : a33Poly u ≤ a33Phi u := by
  have hX1 : 0 ≤ (1 + u) * (4 - 2 * u ^ 2) := by nlinarith
  have hs0 : (11 / 5 : ℝ) ≤ √((1 + u) * (4 - 2 * u ^ 2)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have b1 := sqrt_ge_tangent_sub ((1 + u) * (4 - 2 * u ^ 2)) (2281611 / 1000000 : ℝ) (11 / 5 : ℝ) (by norm_num) (by norm_num)
    hX1 hs0
  have b2 := sqrt_le_tangent (1 - u ^ 2) (379967 / 500000 : ℝ) (by norm_num) (by nlinarith)
  have b3 := sqrt_le_tangent (4 - 2 * u ^ 2) (222029 / 125000 : ℝ) (by norm_num) (by nlinarith)
  have b4 := sqrt_le_tangent (1 - u) (73951 / 125000 : ℝ) (by norm_num) (by linarith)
  have hu : 0 ≤ u := by linarith
  have hu1 : 0 ≤ 1 - u := by linarith
  unfold a33Poly a33Phi
  have e2 := mul_le_mul_of_nonneg_left b2 (show (0:ℝ) ≤ 4 * 0.0763896 * u by positivity)
  have e3 := mul_le_mul_of_nonneg_left b3 hu
  have e4 := mul_le_mul_of_nonneg_left b4 (show (0:ℝ) ≤ 2 * u * (1 - u) by positivity)
  have e1 := mul_le_mul_of_nonneg_left b1 (show (0:ℝ) ≤ 4 * 0.0763896 by norm_num)
  linarith

/-- P0014 page 67, display A.33, first line, window step; inequality chain.
Clearing the positive denominators `4a` and `R - b u`: `a33Phi u ≥ 0` gives the bound. -/
theorem a33G_le_of_Phi (u : ℝ) (h1 : 1 / 2 ≤ u) (h2 : u ≤ 4 / 5) (h : 0 ≤ a33Phi u) :
    a33G u ≤ (a33B : ℝ) := by
  have hB : ((a33B : ℚ) : ℝ) = 0.0763896 := by norm_num [a33B]
  rw [hB]
  have hu : 0 ≤ u := by linarith
  set a := √(1 + u) with ha
  set b := √(1 - u) with hb
  set R := √(4 - 2 * u ^ 2) with hR
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hb1 : b ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hR1 : 1 < R := by
    rw [hR, show (1:ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by nlinarith)
  have hQ : 0 < R - b * u := by nlinarith
  have e1 : √((1 + u) * (4 - 2 * u ^ 2)) = a * R := Real.sqrt_mul (by linarith) _
  have e2 : √(1 - u ^ 2) = a * b := by
    rw [ha, hb, ← Real.sqrt_mul (by linarith)]
    congr 1
    ring
  unfold a33Phi at h
  rw [e1, e2] at h
  unfold a33G
  rw [← ha, ← hb, ← hR, div_mul_div_comm, div_le_iff₀ (by positivity)]
  nlinarith

/-- P0014 page 67, display A.33, first line, on the window `[1/2, 4/5]` around the maximum. -/
theorem a33G_le_window (u : ℝ) (h1 : 1 / 2 ≤ u) (h2 : u ≤ 4 / 5) : a33G u ≤ (a33B : ℝ) :=
  a33G_le_of_Phi u h1 h2 ((a33Poly_nonneg u h1 h2).trans (a33Poly_le_Phi u h1 h2))

end LeanLab.HelfgottMajor.Prep1121A33Window
