module

public import LeanLab.KadiriLumley2014.TableArithmetic

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 2 equation 2.1 and page 13 Table 2.
Journal INTEGERS 14 A61 pages 3 and 17.
The paper says the printed values of a are rounded down.
These bounds check that one last-digit interval encloses each printed denominator.
AI wrote this Lean code, Codex by OpenAI, 2026-10-25.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task64
open Real Set

/-- Exact rational delta from the printed column. -/
def PrintedRow.deltaQ (r : PrintedRow) : ℚ := r.deltaUnits / 10 ^ 12

/-- Exact rational lower endpoint of the printed a interval. -/
def PrintedRow.aQ (r : PrintedRow) : ℚ := r.aUnits / 10000

/-- Exact rational u from delta = m u. -/
def PrintedRow.uQ (r : PrintedRow) : ℚ := r.deltaQ / r.m

/-- Every row satisfies the rational inequalities needed to enclose its
printed denominator between the last-digit endpoints of a. -/
theorem tableTwo_rounding_arithmetic : ∀ r ∈ tableTwo,
    let δ := r.deltaQ
    let u := r.uQ
    let a := r.aQ
    let b := a + 1 / 10000
    (0 < δ ∧ 0 ≤ u ∧ u < 1 ∧ 0 ≤ a ∧ b ≤ 1 / 2 ∧ 0 < (r.gapDenom : ℚ)) ∧
    (r.gapDenom : ℚ) * ((1 + δ * (1 - a)) * (1 + u) - (1 + δ * a)) >
      (1 + δ * (1 - a)) * (1 + u) ∧
    (r.gapDenom : ℚ) * ((1 + δ * (1 - b)) - (1 + δ * b) * (1 - u)) <
      1 + δ * (1 - b) := by
  decide +kernel

/-- The interval fraction in equation 2.1, before taking its reciprocal. -/
noncomputable def intervalFraction (δ u a : ℝ) : ℝ :=
  1 - (1 + δ * a) / (1 + δ * (1 - a)) * Real.exp (-u)

/-- Rational enclosures of the exponential give opposite signs at the two
rounding endpoints. This lemma does not assume a cited prime interval result. -/
theorem rounding_bracket {δ u a b D : ℝ}
    (hδ : 0 < δ) (hu : 0 ≤ u) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2)
    (hD : 0 < D)
    (hlo : D * ((1 + δ * (1 - a)) * (1 + u) - (1 + δ * a)) >
      (1 + δ * (1 - a)) * (1 + u))
    (hhi : D * ((1 + δ * (1 - b)) - (1 + δ * b) * (1 - u)) <
      1 + δ * (1 - b)) :
    1 < D * intervalFraction δ u a ∧ D * intervalFraction δ u b < 1 := by
  have hb0 : 0 ≤ b := ha.trans hab
  have ha1 : a ≤ 1 := by linarith
  have hb1 : b ≤ 1 := by linarith
  have hBa : 0 < 1 + δ * (1 - a) := by positivity
  have hBb : 0 < 1 + δ * (1 - b) := by positivity
  have hAa : 0 ≤ (1 + δ * a) / (1 + δ * (1 - a)) := by positivity
  have hAb : 0 ≤ (1 + δ * b) / (1 + δ * (1 - b)) := by positivity
  have hU : 0 < 1 + u := by linarith
  have hexp : Real.exp (-u) ≤ 1 / (1 + u) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hU (by linarith [Real.add_one_le_exp u])
  have hexp' : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
  constructor
  · have hm := mul_le_mul_of_nonneg_left hexp hAa
    have hgap : 1 - (1 + δ * a) / (1 + δ * (1 - a)) * (1 / (1 + u)) ≤
        intervalFraction δ u a := by unfold intervalFraction; linarith
    have heq : D * (1 - (1 + δ * a) / (1 + δ * (1 - a)) * (1 / (1 + u))) =
        D * ((1 + δ * (1 - a)) * (1 + u) - (1 + δ * a)) /
          ((1 + δ * (1 - a)) * (1 + u)) := by field_simp
    have hnum : 1 < D * (1 - (1 + δ * a) / (1 + δ * (1 - a)) * (1 / (1 + u))) := by
      rw [heq]
      exact (lt_div_iff₀ (mul_pos hBa hU)).mpr (by simpa using hlo)
    exact hnum.trans_le (mul_le_mul_of_nonneg_left hgap hD.le)
  · have hm := mul_le_mul_of_nonneg_left hexp' hAb
    have hgap : intervalFraction δ u b ≤
        1 - (1 + δ * b) / (1 + δ * (1 - b)) * (1 - u) := by unfold intervalFraction; linarith
    have heq : D * (1 - (1 + δ * b) / (1 + δ * (1 - b)) * (1 - u)) =
        D * ((1 + δ * (1 - b)) - (1 + δ * b) * (1 - u)) /
          (1 + δ * (1 - b)) := by field_simp
    have hnum : D * (1 - (1 + δ * b) / (1 + δ * (1 - b)) * (1 - u)) < 1 := by
      rw [heq]
      exact (div_lt_iff₀ hBb).mpr (by simpa using hhi)
    exact (mul_le_mul_of_nonneg_left hgap hD.le).trans_lt hnum

/-- Every printed row brackets the target denominator using its own rounded a. -/
theorem tableTwo_rounding_bracket {r : PrintedRow} (hr : r ∈ tableTwo) :
    1 < (r.gapDenom : ℝ) * intervalFraction r.deltaQ r.uQ r.aQ ∧
    (r.gapDenom : ℝ) * intervalFraction r.deltaQ r.uQ (r.aQ + 1 / 10000) < 1 := by
  obtain ⟨hpar, hlo, hhi⟩ := tableTwo_rounding_arithmetic r hr
  apply rounding_bracket
  · exact_mod_cast hpar.1
  · exact_mod_cast hpar.2.1
  · exact_mod_cast hpar.2.2.2.1
  · norm_num
  · have hb := (Rat.cast_le (K := ℝ)).mpr hpar.2.2.2.2.1
    norm_num at hb
    exact hb
  · exact_mod_cast hpar.2.2.2.2.2
  · exact_mod_cast hlo
  · have hh := (Rat.cast_lt (K := ℝ)).mpr hhi
    push_cast at hh
    norm_num at hh
    exact hh

/-- There is a value of a inside its printed last-digit interval giving
exactly the displayed denominator in equation 2.1. -/
theorem tableTwo_rounding_consistent {r : PrintedRow} (hr : r ∈ tableTwo) :
    ∃ a ∈ Icc (r.aQ : ℝ) ((r.aQ : ℝ) + 1 / 10000),
      (r.gapDenom : ℝ) = 1 / intervalFraction r.deltaQ r.uQ a := by
  have hpar := (tableTwo_rounding_arithmetic r hr).1
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hpar.1
  have ha : (0 : ℝ) ≤ r.aQ := by exact_mod_cast hpar.2.2.2.1
  have hb : (r.aQ : ℝ) + 1 / 10000 ≤ 1 / 2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hpar.2.2.2.2.1
    push_cast at hh
    norm_num at hh
    exact hh
  have hD : (0 : ℝ) < r.gapDenom := by exact_mod_cast hpar.2.2.2.2.2
  have hc : ContinuousOn (fun a : ℝ => (r.gapDenom : ℝ) * intervalFraction r.deltaQ r.uQ a)
      (Icc (r.aQ : ℝ) ((r.aQ : ℝ) + 1 / 10000)) := by
    unfold intervalFraction
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro a ha'
    have : 0 ≤ 1 - a := by linarith [ha'.2]
    positivity
  have hbr := tableTwo_rounding_bracket hr
  obtain ⟨a, ha', heq⟩ := intermediate_value_Icc' (by linarith :
      (r.aQ : ℝ) ≤ (r.aQ : ℝ) + 1 / 10000) hc ⟨hbr.2.le, hbr.1.le⟩
  change (r.gapDenom : ℝ) * intervalFraction r.deltaQ r.uQ a = 1 at heq
  refine ⟨a, ha', ?_⟩
  apply (eq_div_iff ?_).2
  · linarith
  · intro hz
    rw [hz, mul_zero] at heq
    norm_num at heq

end LeanLab.KadiriLumley2014.Task64
