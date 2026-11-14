module

public import Mathlib

/-!
P0032 Riesel-Vaughan 1983, the numerical steps of Lemma 8 (page 60) and Section 9
(pages 69-70), checked in exact rational arithmetic.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.RieselVaughan1983

/-- The left side of (6.8), page 59, with `l = log x`. -/
noncomputable def lhs68 (s t A D C l : ℝ) : ℝ :=
  s * (A / l + 1) * (D / l + 1) * (18 * s * (D / l + 1) - l) - 16 * C * t

/-- Page 60: "for given `A ≥ 0`, `D ≥ 0` the left hand side of (6.8) is a decreasing
function of `l`"; in the form used, positivity at the right end `l₁` gives positivity on
`(0, l₁]`. -/
theorem lhs68_pos_of_le {s t A D C l l₁ : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hC : 0 ≤ C) (ht : 0 ≤ t) (hl : 0 < l) (hll : l ≤ l₁) (h : 0 < lhs68 s t A D C l₁) : 0 < lhs68 s t A D C l := by
  unfold lhs68 at *
  have hl₁ : 0 < l₁ := hl.trans_le hll
  have e1 : A / l₁ ≤ A / l := div_le_div_of_nonneg_left hA hl hll
  have e2 : D / l₁ ≤ D / l := div_le_div_of_nonneg_left hD hl hll
  have p1 : 0 ≤ A / l₁ := div_nonneg hA hl₁.le
  have p2 : 0 ≤ D / l₁ := div_nonneg hD hl₁.le
  -- the last factor is positive at `l₁`, otherwise the left side there would be `≤ 0`
  have hlast : 0 < 18 * s * (D / l₁ + 1) - l₁ := by
    by_contra hc
    push Not at hc
    have : s * (A / l₁ + 1) * (D / l₁ + 1) * (18 * s * (D / l₁ + 1) - l₁) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    have : 0 ≤ 16 * C * t := by positivity
    linarith
  have f3 : 18 * s * (D / l₁ + 1) - l₁ ≤ 18 * s * (D / l + 1) - l := by
    have : 18 * s * (D / l₁ + 1) ≤ 18 * s * (D / l + 1) := by gcongr
    linarith
  have key : s * (A / l₁ + 1) * (D / l₁ + 1) * (18 * s * (D / l₁ + 1) - l₁) ≤
      s * (A / l + 1) * (D / l + 1) * (18 * s * (D / l + 1) - l) := by
    gcongr
  linarith

/-- (2.4): the upper bound for the twin prime constant `C` used on page 60. -/
noncomputable def Cup : ℝ := 1320324 / 1000000

/-- (6.8) at `l = 42`, with `A = 0`, `D = 0`, `u = 79`, `s = 21`, `t = 328.5614`. -/
theorem lhs68_42 : 0 < lhs68 21 (3285614 / 10000) 0 0 Cup 42 := by
  unfold lhs68 Cup; norm_num

/-- (6.8) at `l = 300`, with `A = 8`, `D = 0.99`, `u = 99989`, `s = 9590`, `t = 80096031`. -/
theorem lhs68_300 : 0 < lhs68 9590 80096031 8 (99 / 100) Cup 300 := by
  unfold lhs68 Cup; norm_num

/-- (6.8) at `l = 400`, with `A = 8.43`. -/
theorem lhs68_400 : 0 < lhs68 9590 80096031 (843 / 100) (99 / 100) Cup 400 := by
  unfold lhs68 Cup; norm_num

/-- (6.8) at `l = 424`, with `A = 8.44`. -/
theorem lhs68_424 : 0 < lhs68 9590 80096031 (844 / 100) (99 / 100) Cup 424 := by
  unfold lhs68 Cup; norm_num

/-- The left side of (6.8) is increasing in `-C` and `-t`: a smaller `C` or `t` only helps. -/
theorem lhs68_mono_Ct {s t t' A D C C' l : ℝ} (hC : C ≤ C') (ht : t ≤ t') (hC0 : 0 ≤ C)
    (ht0 : 0 ≤ t) (h : 0 < lhs68 s t' A D C' l) : 0 < lhs68 s t A D C l := by
  unfold lhs68 at *
  have : C * t ≤ C' * t' := mul_le_mul hC ht ht0 (hC0.trans hC)
  nlinarith

/-- The four ranges of page 60 in one statement: for each range the left side of (6.8) is
positive at every `l` of the range, for every `C ≤ 1.320324` and `t` below the table value. -/
theorem lhs68_ranges (C l : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ Cup) :
    (∀ t, 0 ≤ t → t ≤ 3285614 / 10000 → 24 ≤ l → l ≤ 42 → 0 < lhs68 21 t 0 0 C l) ∧
    (∀ t, 0 ≤ t → t ≤ 80096031 → 42 < l → l ≤ 300 →
      0 < lhs68 9590 t 8 (99 / 100) C l) ∧
    (∀ t, 0 ≤ t → t ≤ 80096031 → 300 < l → l ≤ 400 →
      0 < lhs68 9590 t (843 / 100) (99 / 100) C l) ∧
    (∀ t, 0 ≤ t → t ≤ 80096031 → 400 < l → l ≤ 424 →
      0 < lhs68 9590 t (844 / 100) (99 / 100) C l) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht0 ht h1 h2
    exact lhs68_mono_Ct hC ht hC0 ht0
      (lhs68_pos_of_le (by norm_num) le_rfl le_rfl (by unfold Cup; norm_num) (by norm_num) (by linarith) h2 lhs68_42)
  · intro t ht0 ht h1 h2
    exact lhs68_mono_Ct hC ht hC0 ht0
      (lhs68_pos_of_le (by norm_num) (by norm_num) (by norm_num) (by unfold Cup; norm_num) (by norm_num) (by linarith) h2 lhs68_300)
  · intro t ht0 ht h1 h2
    exact lhs68_mono_Ct hC ht hC0 ht0
      (lhs68_pos_of_le (by norm_num) (by norm_num) (by norm_num) (by unfold Cup; norm_num) (by norm_num) (by linarith) h2 lhs68_400)
  · intro t ht0 ht h1 h2
    exact lhs68_mono_Ct hC ht hC0 ht0
      (lhs68_pos_of_le (by norm_num) (by norm_num) (by norm_num) (by unfold Cup; norm_num) (by norm_num) (by linarith) h2 lhs68_424)

/-! ### Section 9, pages 69-70, with `L = log y ≥ 350` -/

/-- Page 69, second display to (9.2): `(7 - 30.5989/L)(1 - 3.6581/L) ≥ 7 - 56.2056/L`. -/
theorem sec9_step2 (L : ℝ) (hL : 350 ≤ L) :
    7 - 562056 / 10000 / L ≤ (7 - 305989 / 10000 / L) * (1 - 36581 / 10000 / L) := by
  have hL0 : 0 < L := by linarith
  rw [show (7 - 305989 / 10000 / L) * (1 - 36581 / 10000 / L) =
      7 - (305989 / 10000 + 7 * (36581 / 10000)) / L + 305989 / 10000 * (36581 / 10000) / L ^ 2
      by field_simp; ring]
  have : 0 ≤ 305989 / 10000 * (36581 / 10000) / L ^ 2 := by positivity
  have h2 : (305989 / 10000 + 7 * (36581 / 10000) : ℝ) ≤ 562056 / 10000 := by norm_num
  have : (305989 / 10000 + 7 * (36581 / 10000)) / L ≤ 562056 / 10000 / L :=
    div_le_div_of_nonneg_right h2 hL0.le
  linarith

/-- Page 70: `(7 - 56.2056/L)(1 + 6.8986/L) > 7 - 9.0233/L ≥ 6.974` for `L ≥ 350`. -/
theorem sec9_step3 (L : ℝ) (hL : 350 ≤ L) :
    7 - 90233 / 10000 / L < (7 - 562056 / 10000 / L) * (1 + 68986 / 10000 / L) ∧
      (6974 / 1000 : ℝ) ≤ 7 - 90233 / 10000 / L := by
  have hL0 : 0 < L := by linarith
  constructor
  · rw [show (7 - 562056 / 10000 / L) * (1 + 68986 / 10000 / L) =
        7 - (562056 / 10000 - 7 * (68986 / 10000)) / L -
          562056 / 10000 * (68986 / 10000) / L ^ 2 by field_simp; ring]
    -- `562056·68986/10^8 / L² ≤ (387.74.../350) / L < 1.1079 / L`
    have hq : 562056 / 10000 * (68986 / 10000) / L ^ 2 ≤
        562056 / 10000 * (68986 / 10000) / 350 / L := by
      rw [div_div, pow_two]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    have : (562056 / 10000 - 7 * (68986 / 10000)) / L + 562056 / 10000 * (68986 / 10000) / 350 / L
        < 90233 / 10000 / L := by
      rw [← add_div]
      exact div_lt_div_of_pos_right (by norm_num) hL0
    linarith
  · have : 90233 / 10000 / L ≤ 90233 / 10000 / 350 := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) hL
    have h2 : (6974 / 1000 : ℝ) ≤ 7 - 90233 / 10000 / 350 := by norm_num
    linarith

/-- Page 70, last display: `(6.974) K y / 120 > (0.0578)(x - y)` with `K = 200`,
`x = (K + 2) y`, and `0.0578 > 1/18`, which is (9.1). -/
theorem sec9_final (y : ℝ) (hy : 0 < y) :
    (578 / 10000) * (202 * y - y) < 6974 / 1000 * 200 * y / 120 ∧
      (1 / 18 : ℝ) < 578 / 10000 := by
  constructor <;> nlinarith

/-- Page 70, the display for `log y ≥ 350`:
`(log(y/2))(8.3 + log(y/2))/(log y)² > 1 + 6.8986/log y`, in the variable `L = log y`. -/
theorem sec9_logy2 (L : ℝ) (hL : 350 ≤ L) :
    1 + 68986 / 10000 / L < (L - Real.log 2) * (83 / 10 + (L - Real.log 2)) / L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  rw [lt_div_iff₀ (by positivity)]
  have e : (1 + 68986 / 10000 / L) * L ^ 2 = L ^ 2 + 68986 / 10000 * L := by
    field_simp
  rw [e]
  nlinarith

end LeanLab.RieselVaughan1983
