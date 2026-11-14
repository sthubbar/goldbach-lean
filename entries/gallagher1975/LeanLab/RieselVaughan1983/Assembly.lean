module

public import LeanLab.RieselVaughan1983.Lemma8
public import LeanLab.RieselVaughan1983.Reduction

/-!
P0032 Riesel-Vaughan 1983, page 69: "In view of Lemmas 7 and 8 it suffices now to show
(9.1)". The induction that turns Lemma 7, Lemma 8 and (9.1) into (1.1), and the chain to the
Theorem.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Real

namespace LeanLab.RieselVaughan1983

/-- Page 69: Lemmas 7 and 8 and (9.1) give (1.1). The step from `y = x/202` to `x` is
`N(x) = N(y) + (N(x) - N(y)) > y/18 + (x - y)/18`. -/
theorem density11_of (h7 : Lemma7) (h8 : Lemma8) (h91 : Display91) : Density11 := by
  have hl202 : 0 < Real.log 202 := Real.log_pos (by norm_num)
  have base : ∀ x : ℝ, 2 ≤ x → Real.log x ≤ 424 → x / 18 < NCount x := by
    intro x hx hl
    have hx0 : 0 < x := by linarith
    by_cases h24 : Real.log x < 24
    · apply h7 x hx
      rw [← Real.exp_log hx0]; exact Real.exp_le_exp.mpr (by linarith)
    · push Not at h24
      exact h8 x hx0 h24 hl
  have step : ∀ k : ℕ, ∀ x : ℝ, 2 ≤ x → Real.log x ≤ 424 + k * Real.log 202 →
      x / 18 < NCount x := by
    intro k
    induction k with
    | zero => intro x hx hl; exact base x hx (by simpa using hl)
    | succ k ih =>
      intro x hx hl
      have hx0 : 0 < x := by linarith
      by_cases hk : Real.log x ≤ 424 + k * Real.log 202
      · exact ih x hx hk
      push Not at hk
      have hbig : 375 ≤ Real.log x := by
        have : (0 : ℝ) ≤ k * Real.log 202 := by positivity
        linarith
      have hy : Real.log (x / 202) = Real.log x - Real.log 202 :=
        Real.log_div hx0.ne' (by norm_num)
      have hy2 : 2 ≤ x / 202 := by
        have h1 : Real.log 202 ≤ 202 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        have hpos : (0 : ℝ) < x / 202 := by positivity
        have : Real.log 2 < Real.log (x / 202) := by
          rw [hy]
          have := Real.log_two_lt_d9
          have : (0 : ℝ) ≤ k * Real.log 202 := by positivity
          linarith
        exact ((Real.log_lt_log_iff (by norm_num) hpos).mp this).le
      have ihy := ih (x / 202) hy2 (by
        rw [hy]; push_cast at hl ⊢; linarith)
      have := h91 x hbig
      linarith
  intro x hx
  obtain ⟨k, hk⟩ := exists_nat_ge ((Real.log x - 424) / Real.log 202)
  apply step k x hx
  have := (div_le_iff₀ hl202).mp hk
  linarith

/-- **The Theorem**, every even number is a sum of at most eighteen primes, CONDITIONAL ON
Lemma 5 at the four table rows of Lemma 8, Lemma 6 (i), (2.30) and (2.31), Rosser-Schoenfeld
(3.3), and (9.1), which carries Sections 7 to 9 of the paper. -/
theorem theorem_of (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h6 : Lemma6i) (hTab : Table230) (hRS : RS33) (h91 : Display91) : Theorem :=
  theorem_of_density11
    (density11_of (lemma7_of_RS hRS) (lemma8_of h24 h42 h278 h396 h6 hTab) h91)

/-- The same with nineteen primes for every `n > 1`, the form Kaniecki and Helfgott quote. -/
theorem corollary19_of (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h6 : Lemma6i) (hTab : Table230) (hRS : RS33) (h91 : Display91) : Corollary19 :=
  corollary19_of_density11
    (density11_of (lemma7_of_RS hRS) (lemma8_of h24 h42 h278 h396 h6 hTab) h91)

end LeanLab.RieselVaughan1983
