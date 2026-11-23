module

public import LeanLab.HelfgottMajor.Assembly
public import LeanLab.HelfgottMajor.Lemma41Terms
public import LeanLab.HelfgottArcs.Statements
public import LeanLab.HelfgottMajor.SplitGaussian123
public import LeanLab.HelfgottMajor.Lemma41Corrected123

/-!
P0014 Theorem 1.1, page 3, proof on pages 56 and 57.
AI wrote this Lean code. Binary Goldbach is open.
The lab uses the Fourier transform of the weight extended by zero to negative arguments.
The analytic leaf uses the recorded repair of Proposition 4.6 on pages 43 and 44.
The final assembly is CONDITIONAL ON HelfgottInput and the analytic leaf.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.Decomp123
open Real
open LeanLab.HelfgottArcs

/-- The error expression of P0014 display 4.43, with the recorded factor 6 repair. -/
noncomputable def gaussianError (q δ x T : ℝ) : ℝ :=
  log (q * T / (2 * π)) *
      (4.329 * exp (-0.1598 * T) + 0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
    (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) / sqrt x +
    (3 * log q + 14 * |δ| + 17) / x + (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)

/-- CITED. P0014 Theorem 1.1 on page 3, in the lab formulation with its named GRH input. -/
def Theorem11 : Prop :=
  ∀ (hG : HelfgottInput) (x : ℝ), 10 ^ 8 ≤ x → ∀ (q : ℕ) [NeZero q],
    q ≤ 300000 → ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ (δ : ℝ),
      |δ| ≤ 4 * 300000 / q →
      MajorShape etaHeart χ δ x (5.281e-22 + 1 / sqrt x * (650400 / sqrt q + 112))

/-- LEAF. P0014 page 56, display 4.86. The selected height exceeds both required thresholds. -/
theorem height_conditions {q δ : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hδ : |δ| ≤ 1200000 / q) :
    1000 / 3 ≤ 1e8 / q ∧ max (4 * π ^ 2 * |δ|) 100 ≤ 1e8 / q := by
  have hq0 : 0 < q := by linarith
  have ht : 1000 / 3 ≤ 1e8 / q := by
    rw [le_div_iff₀ hq0]
    linarith
  refine ⟨ht, max_le ?_ (by linarith)⟩
  rw [le_div_iff₀ hq0]
  have hdq : |δ| * q ≤ 1200000 := (le_div_iff₀ hq0).mp hδ
  have hpi : π ^ 2 ≤ 16 := by nlinarith [pi_pos, pi_lt_four]
  calc 4 * π ^ 2 * |δ| * q = 4 * π ^ 2 * (|δ| * q) := by ring
    _ ≤ 4 * 16 * 1200000 := by gcongr
    _ ≤ 1e8 := by norm_num

/-- LEAF. P0014 page 56, display 4.86. The nonzero shift gives the tail ratio bound. -/
theorem ratio_condition {q δ : ℝ} (hq1 : 1 ≤ q) (hδ : |δ| ≤ 1200000 / q)
    (hδ0 : δ ≠ 0) : 1000 / (12 * π) ≤ (1e8 / q) / (π * |δ|) := by
  have hq0 : 0 < q := by linarith
  have ha : 0 < |δ| := abs_pos.mpr hδ0
  rw [le_div_iff₀ (mul_pos pi_pos ha), le_div_iff₀ hq0]
  have hdq : |δ| * q ≤ 1200000 := (le_div_iff₀ hq0).mp hδ
  have hc : 1000 / (12 * π) * (π * |δ|) * q = (1000 / 12) * (|δ| * q) := by
    field_simp
    <;> ring
  nlinarith

/-- LEAF. P0014 page 56, the first error line. This includes the zero shift. -/
theorem tail_bound {q δ : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hδ : |δ| ≤ 1200000 / q) :
    log (q * (1e8 / q) / (2 * π)) *
      (4.329 * exp (-0.1598 * (1e8 / q)) +
        0.802 * |δ| * exp (-0.1065 * ((1e8 / q) / (π * |δ|)) ^ 2)) ≤ 5.281e-22 := by
  have hq0 : 0 < q := by linarith
  have hT := (height_conditions hq1 hq hδ).1
  have h1 := A1 hT
  have h2 : 0.802 * |δ| * exp (-0.1065 * ((1e8 / q) / (π * |δ|)) ^ 2) ≤
      1200000 * 4.3166e-33 := by
    by_cases hd0 : δ = 0
    · norm_num [hd0]
    · have hh := A2 (ratio_condition hq1 hδ hd0)
      have hd : |δ| ≤ 1200000 := hδ.trans (by
        rw [div_le_iff₀ hq0]
        linarith)
      have hm := mul_le_mul hh hd (abs_nonneg δ) (by norm_num : (0 : ℝ) ≤ 4.3166e-33)
      nlinarith
  have he : q * (1e8 / q) = 1e8 := by field_simp
  rw [he]
  have hL0 : 0 ≤ log (1e8 / (2 * π)) := log_nonneg (by
    rw [le_div_iff₀ (by positivity)]
    linarith [pi_lt_four])
  have hsum := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hL0
  obtain ⟨ha, hb, hc⟩ := A3
  nlinarith

/-- LEAF. P0014 pages 56 and 57, the three algebraic coefficients, with the recorded repair. -/
theorem coefficient_bounds {q δ : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hδ : |δ| ≤ 1200000 / q) :
    (2.337 * sqrt (1e8 / q) * log (q * (1e8 / q)) + 21.817 * sqrt (1e8 / q) +
      2.85 * log q + 74.38 ≤ 648662 / sqrt q + 111) ∧
    (3 * log q + 14 * |δ| + 17 ≤ 55 + 1.7e7 / q) ∧
    (log q + 6) * (1 + 6 * |δ|) ≤ 19 + 1.35e8 / q := by
  have hq' : q ≤ 3e5 := by norm_num at hq ⊢; exact hq
  have hδ' : |δ| ≤ 1.2e6 / q := by norm_num at hδ ⊢; exact hδ
  exact ⟨A4 hq1 hq', (A56 hq1 hq' (abs_nonneg δ) hδ').1,
    Lemma41Terms.sec46_repaired hq1 hq' (abs_nonneg δ) hδ'⟩

/-- LEAF. P0014 page 57, last step for Theorem 1.1, using the corrected remainder. -/
theorem absorb_remainders {q x : ℝ} (hq1 : 1 ≤ q) (hx : 1e8 ≤ x) :
    (648662 / sqrt q + 111) / sqrt x + (55 + 1.7e7 / q) / x +
      (19 + 1.35e8 / q) / (x * sqrt x) ≤
      1 / sqrt x * (650400 / sqrt q + 112) := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < sqrt x := sqrt_pos.mpr hx0
  have hs : 1e4 ≤ sqrt x := by
    rw [le_sqrt (by norm_num) hx0.le]
    norm_num at hx ⊢
    exact hx
  have hs2 := sq_sqrt hx0.le
  have hq0 : 0 < q := by linarith
  have hB0 : 0 ≤ 55 + 1.7e7 / q := by positivity
  have hC0 : 0 ≤ 19 + 1.35e8 / q := by positivity
  have hB : (55 + 1.7e7 / q) / sqrt x ≤ (55 + 1.7e7 / q) / 1e4 :=
    div_le_div_of_nonneg_left hB0 (by norm_num) hs
  have hC : (19 + 1.35e8 / q) / x ≤ (19 + 1.35e8 / q) / 1e8 :=
    div_le_div_of_nonneg_left hC0 (by norm_num) hx
  have hsmall : 648662 / sqrt q + 111 + (55 + 1.7e7 / q) / sqrt x +
      (19 + 1.35e8 / q) / x ≤ 650400 / sqrt q + 112 := by
    have h := Lemma41Terms.thm11_survives hq1
    have eb : (55 + 1.7e7 / q) / 1e4 = 55e-4 + 1700 / q := by ring
    have ec : (19 + 1.35e8 / q) / 1e8 = 19e-8 + 1.35 / q := by ring
    rw [eb] at hB
    rw [ec] at hC
    linarith
  have h := div_le_div_of_nonneg_right hsmall hs0.le
  have eqn : (648662 / sqrt q + 111 + (55 + 1.7e7 / q) / sqrt x +
      (19 + 1.35e8 / q) / x) / sqrt x =
      (648662 / sqrt q + 111) / sqrt x + (55 + 1.7e7 / q) / x +
        (19 + 1.35e8 / q) / (x * sqrt x) := by
    rw [add_div, add_div, div_div, div_div, mul_self_sqrt hx0.le]
  rw [eqn] at h
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

/-- LEAF. P0014 page 56. HelfgottInput contains the zeros up to the selected height. -/
theorem verified_zeros (hG : HelfgottInput) (q : ℕ) [NeZero q] (hq : q ≤ 300000)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 1e8 / (q : ℝ) → s.re = 1 / 2 := by
  intro s hs hs0 hs1 him
  apply hG q χ hχ s hs hs0 hs1
  by_cases hEven : Even q
  · refine Or.inr ⟨hEven, hq.trans (by norm_num), ?_⟩
    norm_num at him ⊢
    exact Or.inl him
  · exact Or.inl ⟨hEven, hq, by norm_num at him ⊢; exact him⟩

/-- The numerical substitution in P0014 pages 56 and 57, independent of cited analysis. -/
theorem error_bound {q δ x : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ 300000)
    (hδ : |δ| ≤ 1200000 / q) (hx : 1e8 ≤ x) :
    gaussianError q δ x (1e8 / q) ≤
      5.281e-22 + 1 / sqrt x * (650400 / sqrt q + 112) := by
  have ht := tail_bound hq1 hq hδ
  obtain ⟨h1, h2, h3⟩ := coefficient_bounds hq1 hq hδ
  have h1' := div_le_div_of_nonneg_right h1 (sqrt_nonneg x)
  have h2' := div_le_div_of_nonneg_right h2 (by linarith : 0 ≤ x)
  have h3' := div_le_div_of_nonneg_right h3 (by positivity : 0 ≤ x * sqrt x)
  have ha := absorb_remainders hq1 hx
  unfold gaussianError
  linarith

end LeanLab.HelfgottMajor.Decomp123
