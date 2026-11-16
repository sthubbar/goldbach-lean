module

public import Mathlib
public import LeanLab.Pintz2018.Section9

/-!
# Pintz 2018, Section 9 printed numbers

Each theorem is one printed numerical claim of Section 9 of arXiv 1804.09084v2, proved with the
Taylor bounds of `ExpBounds`.  AI wrote the Lean code.
-/

@[expose] public section


namespace LeanLab.Pintz2018

/-- (9.13), Case 1: `2e^{-(25/7)0.68} + 6e^{-(25/7)0.702} + e^{-(25/7)0.99} - 9e^{-(25/7)1.311} < 0.612`. -/
theorem eq913 : 2 * E 0.68 + 6 * E 0.702 + E 0.99 - 9 * E 1.311 < 0.612 := by
  have h1 := E_upper 0.68 (by norm_num) (by norm_num)
  have h2 := E_upper 0.702 (by norm_num) (by norm_num)
  have h3 := E_upper 0.99 (by norm_num) (by norm_num)
  have h4 := E_lower 1.311 (by norm_num) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  linarith

/-- (9.17), Case 4 with complex `χ₁`. -/
theorem eq917 : 2 * (E 0.44 - E 1.311) < 0.39698 := by
  have h1 := E_upper 0.44 (by norm_num) (by norm_num)
  have h4 := E_lower 1.311 (by norm_num) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h4
  norm_num at h1 h4
  linarith

/-- (9.18), Case 6, the printed value `0.59727...`. -/
theorem eq918 : 0.59727 < E 0.14 - E 1.311 ∧ E 0.14 - E 1.311 < 0.59728 := by
  have h1 := E_upper 0.14 (by norm_num) (by norm_num)
  have h2 := E_lower 0.14 (by norm_num) (by norm_num)
  have h3 := E_upper 1.311 (by norm_num) (by norm_num)
  have h4 := E_lower 1.311 (by norm_num) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  constructor <;> linarith

/-- (9.6): `22.281 e^{-19 Λ₀/21} < 6.805` with `Λ₀ = 1.311`. -/
theorem eq96 : 22.281 * Real.exp (-(19 * 1.311 / 21)) < 6.805 := by
  have h1 := expneg_upper (19 * 1.311 / 21) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith

/-- (9.27): `15.6 e^{-19 Λ₁/21} < 1.74516` with `Λ₁ = 2.421`. -/
theorem eq927 : 15.6 * Real.exp (-(19 * 2.421 / 21)) < 1.74516 := by
  have h1 := expneg_upper (19 * 2.421 / 21) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  linarith

/-- (9.29): `e^{-(25/7)0.04} - e^{-(25/7)Λ₁} < 0.86671`. -/
theorem eq929 : E 0.04 - E 2.421 < 0.86671 := by
  have h1 := E_upper 0.04 (by norm_num) (by norm_num)
  have h2 := E_lower (2.421 / 2) (by norm_num) (by norm_num)
  have h3 : E 2.421 = E (2.421 / 2) ^ 2 := by rw [← E_two]; norm_num
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2
  norm_num at h1 h2
  have h2' : 0 ≤ E (2.421 / 2) := (E_pos _).le
  rw [h3]
  nlinarith

/-- (9.22): the value without exceptional classes. -/
theorem eq922 : (0.622 : ℝ) ^ 2 + 0.0722 * (2 * 0.622 + 6.805) = 0.9680218 := by norm_num

/-- (9.23), (9.24), (9.25), (9.26). -/
theorem surplus :
    (0.0826 : ℝ) - 0.0722 = 0.0104 ∧ (2 * 0.622 + 2 * 0.0826 : ℝ) = 1.4092 ∧
    (0.0104 : ℝ) * 1.4092 = 0.01465568 ∧ (0.0751 : ℝ) - 0.0722 = 0.0029 ∧
    (0.0029 : ℝ) * 0.1502 = 4.3558e-4 := by norm_num

/-- (9.21), Cases 1 to 6: `S < 0.9832`, hence `S < 0.9903`. -/
theorem eq921 : (0.622 : ℝ) ^ 2 + 0.0722 * (2 * 0.622 + 6.805) + 0.01465568 + 4.3558e-4
    < 0.9832 := by norm_num

/-- (9.30), Case 7: `S ≤ 0.86671² + 0.0715 (2 · 0.86671 + 1.74516) < 0.99991`. -/
theorem eq930 : (0.86671 : ℝ) ^ 2 + 0.0715 * (2 * 0.86671 + 1.74516) < 0.99991 := by norm_num

/-- (9.37): `(1 - e^{-0.28}) / 0.04 > 6.1`. -/
theorem eq937 : (6.1 : ℝ) < (1 - Real.exp (-0.28)) / 0.04 := by
  have h1 := expneg_upper 0.28 (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  rw [lt_div_iff₀ (by norm_num)]
  linarith

/-- (9.36) and (9.37), Case 8: for `0 < λ₁ ≤ 0.04`, `e^{-7 λ₁} + 5 λ₁ < 1`. -/
theorem case8_tail (l : ℝ) (h0 : 0 < l) (h1 : l ≤ 0.04) : Real.exp (-7 * l) + 5 * l < 1 := by
  have hy : 0 ≤ 7 * l := by positivity
  have hs := Real.sum_le_exp_of_nonneg hy 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hs
  norm_num at hs
  have hp : 0 < 1 + 7 * l + (7 * l) ^ 2 / 2 := by positivity
  rw [show -7 * l = -(7 * l) by ring, Real.exp_neg]
  have : (Real.exp (7 * l))⁻¹ ≤ (1 + 7 * l + (7 * l) ^ 2 / 2)⁻¹ := inv_anti₀ hp (by linarith)
  have h2 : (1 + 7 * l + (7 * l) ^ 2 / 2)⁻¹ < 1 - 5 * l := by
    rw [inv_eq_one_div, div_lt_iff₀ hp]
    nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) h0]
  linarith

theorem rpow_lt_of_pow_lt (a b : ℝ) (p q : ℕ) (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (h : a ^ p < b ^ q) : a ^ ((p : ℝ) / q) < b := by
  by_contra hcon
  push_neg at hcon
  have hx : (a ^ ((p : ℝ) / q)) ^ q = a ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    rw [show (p : ℝ) / q * q = p by field_simp]
    exact Real.rpow_natCast a p
  have : b ^ q ≤ (a ^ ((p : ℝ) / q)) ^ q := pow_le_pow_left₀ hb.le hcon q
  linarith

/-- (9.33): `10.4 λ₁^{76/77} < 0.435` for `0 < λ₁ ≤ 0.04`. -/
theorem eq933 (l : ℝ) (h0 : 0 < l) (h1 : l ≤ 0.04) : 10.4 * l ^ ((76 : ℝ) / 77) < 0.435 := by
  have h2 : l ^ ((76 : ℝ) / 77) ≤ (0.04 : ℝ) ^ ((76 : ℝ) / 77) :=
    Real.rpow_le_rpow h0.le h1 (by norm_num)
  have h3 : (0.04 : ℝ) ^ ((76 : ℝ) / 77) < 87 / 2080 := by
    have := rpow_lt_of_pow_lt 0.04 (87 / 2080) 76 77 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    simpa using this
  linarith

/-- (9.36): the term `2.87 · 10.4 · λ₁^{11/7}` is at most `5 λ₁` for `0 < λ₁ ≤ 0.04`. -/
theorem eq936_term (l : ℝ) (h0 : 0 < l) (h1 : l ≤ 0.04) :
    2.87 * 10.4 * l ^ ((11 : ℝ) / 7) ≤ 5 * l := by
  have h2 : l ^ ((4 : ℝ) / 7) ≤ (0.04 : ℝ) ^ ((4 : ℝ) / 7) :=
    Real.rpow_le_rpow h0.le h1 (by norm_num)
  have h3 : (0.04 : ℝ) ^ ((4 : ℝ) / 7) < 0.1675 := by
    have := rpow_lt_of_pow_lt 0.04 0.1675 4 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    simpa using this
  have h4 : l ^ ((11 : ℝ) / 7) = l * l ^ ((4 : ℝ) / 7) := by
    rw [show (11 : ℝ) / 7 = 1 + 4 / 7 by norm_num, Real.rpow_add h0, Real.rpow_one]
  rw [h4]
  nlinarith

/-- Case 8 of Section 9 assembled: with `0 < λ₁ ≤ 0.04`,
`e^{-7λ₁} + 2.87 · 10.4 · λ₁^{11/7} < 1`. -/
theorem case8 (l : ℝ) (h0 : 0 < l) (h1 : l ≤ 0.04) :
    Real.exp (-7 * l) + 2.87 * 10.4 * l ^ ((11 : ℝ) / 7) < 1 := by
  have := case8_tail l h0 h1
  have := eq936_term l h0 h1
  linarith

/-- Every case of Section 9 closes below 1: the margin `c₀` of (9.1). -/
theorem all_cases_lt_one :
    (0.9832 : ℝ) < 1 ∧ (0.99991 : ℝ) < 1 := by norm_num

end LeanLab.Pintz2018

