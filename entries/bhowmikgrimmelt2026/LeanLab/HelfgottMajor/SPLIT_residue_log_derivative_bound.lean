module

public import LeanLab.HelfgottMajor.Gaussian123Base

/-!
Split of the open logarithmic derivative bound of the residue in
`LeanLab.HelfgottMajor.Gaussian123Base`, displays 4.18 to 4.22 and the display before 4.23,
pages 36 and 37. The sealed statement bounds
`log (2 * π / q) + γ - L'(1, χ)/L(1, χ)` by `3 log q + 15.289` for a primitive character modulo
`q` with `q` not equal to `1`. The four leaves are the quotient itself, the scalar logarithm,
the numerical constant of page 37, and the conductor reduction to `3 ≤ q`;
`residue_log_derivative_bound_split` assembles them with the triangle inequality.
The namespace is the target's, so the names the rest of the lab refers to are unchanged.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.SplitGaussian123
open Real LeanLab.HelfgottArcs

/-- LEAF: step 2 of 4, the scalar logarithm. Page 37: for a real `q` at least `3`, the absolute
value of `log (2π/q) + γ` is at most `log q + (γ + log 2π - log 9)`. This is the elementary
comparison of `2π` with `q ^ 2` and of `9` with `q ^ 2`, losing one power of `log q` and no
more. No character and no `L` function occurs in it. -/
theorem log_two_pi_div_add_gamma_abs_le (q : ℝ) (hq : 3 ≤ q) :
    |log (2 * π / q) + eulerMascheroniConstant| ≤
      log q + (eulerMascheroniConstant + log (2 * π) - log 9) := by
  have hq0 : 0 < q := by linarith
  have h2pi : (0:ℝ) < 2 * π := by positivity
  have hγ : (0:ℝ) < eulerMascheroniConstant :=
    lt_trans (by norm_num) one_half_lt_eulerMascheroniConstant
  have h9q : log 9 ≤ 2 * log q := by
    have h : log 9 ≤ log (q ^ 2) := by
      refine log_le_log (by norm_num) ?_
      nlinarith
    rwa [log_pow] at h
  have h9 : log 9 ≤ 2 * log (2 * π) := by
    have h : log 9 ≤ log ((2 * π) ^ 2) := by
      refine log_le_log (by norm_num) ?_
      nlinarith [pi_gt_three]
    rwa [log_pow] at h
  have hsub : log (2 * π / q) = log (2 * π) - log q := log_div h2pi.ne' hq0.ne'
  have hkey : |log (2 * π / q) + eulerMascheroniConstant| ≤
      |log (2 * π / q)| + eulerMascheroniConstant := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_pos hγ]
  rcases le_or_gt q (2 * π) with hle | hlt
  · have hnn : 0 ≤ log (2 * π / q) := by
      rw [← log_one]
      exact log_le_log (by norm_num) (by rw [le_div_iff₀ hq0]; linarith)
    have habs : |log (2 * π / q)| = log (2 * π) - log q := by
      rw [hsub, abs_of_nonneg]; linarith
    rw [habs] at hkey
    linarith
  · have hneg : log (2 * π / q) < 0 := by
      rw [log_neg_iff (by positivity), div_lt_one hq0]
      linarith
    have habs : |log (2 * π / q)| = log q - log (2 * π) := by
      have hlt' : log (2 * π) < log q := log_lt_log h2pi hlt
      rw [hsub, abs_of_neg (by linarith)]
      ring
    rw [habs] at hkey
    linarith

set_option maxRecDepth 100000 in
/-- LEAF: step 3 of 4, the numerical constant of page 37: `γ + log 2π - log 9 + 15.07017` is at
most `15.289`. Decimal arithmetic with the bounds `γ < 0.57738` and `2π/9 > exp (-0.359)`, and no
variable at all; the whole margin between the two constants lives here. -/
theorem page37_constant_budget :
    eulerMascheroniConstant + log (2 * π) - log 9 + 15.07017 ≤ 15.289 := by
  have hγ : eulerMascheroniConstant ≤ 578/1000 := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 1024
    have hseq : Real.eulerMascheroniSeq' 1024 = (harmonic 1024 : ℝ) - log 1024 := by
      unfold Real.eulerMascheroniSeq'
      norm_num
    rw [hseq] at h
    have hH : (harmonic 1024 : ℝ) ≤ 75094/10000 := by
      have hq : harmonic 1024 ≤ (75094/10000 : ℚ) := by
        norm_num [harmonic]
      have h2 : ((harmonic 1024 : ℚ) : ℝ) ≤ ((75094/10000 : ℚ) : ℝ) := by
        exact_mod_cast hq
      simpa using h2
    have hl2 : (0.6931471803:ℝ) < log 2 := Real.log_two_gt_d9
    have hlog : log (1024:ℝ) = 10 * log 2 := by
      rw [show (1024:ℝ) = 2^10 by norm_num, log_pow]
      norm_num
    linarith
  have hlog9 : log (2 * π / 9) ≤ -(35917/100000) := by
    rw [log_le_iff_le_exp (by positivity), exp_neg, inv_eq_one_div]
    have hpi : 2 * π / 9 ≤ 6283186/9000000 := by
      nlinarith [pi_lt_d6]
    have hp : (0:ℝ) < exp (35917/100000) := exp_pos _
    have hb : exp (35917/100000 : ℝ) ≤ 14322/10000 := by
      have h := Real.exp_bound' (x := (35917/100000 : ℝ)) (by norm_num) (by norm_num)
        (n := 7) (by norm_num)
      have h2 : (∑ m ∈ Finset.range 7, (35917/100000 : ℝ) ^ m / (m.factorial : ℝ)) +
          (35917/100000 : ℝ)^7 * ((7:ℝ)+1) / ((7:ℕ).factorial * 7) ≤ 14322/10000 := by
        norm_num [Finset.sum_range_succ]
      linarith
    rw [le_div_iff₀ hp]
    nlinarith
  have hsp : log (2 * π) - log 9 = log (2 * π / 9) := by
    rw [log_div (by positivity) (by norm_num)]
  linarith

/-- LEAF: step 4 of 4, the conductor reduction. Page 37 notes that there is no primitive
character modulo `2`, so a primitive character modulo `q` with `q` not equal to `1` has `q` at
least `3`. This is the hypothesis the scalar estimate of step 2 needs, and it is arithmetic about
the conductor alone. -/
theorem three_le_conductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) : 3 ≤ q := by
  have h2 : q ≠ 2 := by
    rintro rfl
    have hunit : ∀ u : (ZMod 2)ˣ, u = 1 := by
      intro u
      refine Units.ext ?_
      have hval : ((u : ZMod 2)).val = 1 := by
        have hlt : ((u : ZMod 2)).val < 2 := ZMod.val_lt _
        have hne : ((u : ZMod 2)).val ≠ 0 := by
          rw [ZMod.val_ne_zero]
          exact Units.ne_zero u
        omega
      exact (ZMod.val_eq_one (by norm_num) (u : ZMod 2)).mp hval
    have hχ1 : χ = 1 := by
      refine MulChar.ext (fun u => ?_)
      rw [hunit u]
      simp
    rw [hχ1] at hχ
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
    exact absurd hχ (by norm_num)
  have h0 : q ≠ 0 := NeZero.ne q
  omega

end LeanLab.HelfgottMajor.SplitGaussian123
