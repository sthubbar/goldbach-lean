module

public import Mathlib

/-!
P0032 Riesel-Vaughan 1983, (7.8) in the proof of Lemma 9, page 61: for
`e^60 ≤ u ≤ y/2`,
`u/((log u)(8.3 + log u)) + (y-u)/((log(y-u))(8.3 + log(y-u))) ≤ y/((log(y/2))(8.3 + log(y/2)))`.
The paper shows `f'(u) > 0`; here the same fact is the concavity of
`g(v) = v/((log v)(8.3 + log v))` on `[e^60, ∞)`, from `g'(v) = φ(log v)` with `φ` decreasing.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Real Set

namespace LeanLab.RieselVaughan1983

/-- `g(v) = v/((log v)(8.3 + log v))`. -/
noncomputable def g83 (v : ℝ) : ℝ := v / (Real.log v * (83 / 10 + Real.log v))

/-- `φ(l) = (h - h')/h²` with `h = l(8.3 + l)`, the derivative of `g` in the variable `log v`. -/
noncomputable def phi83 (l : ℝ) : ℝ :=
  (l * (83 / 10 + l) - (83 / 10 + 2 * l)) / (l * (83 / 10 + l)) ^ 2

lemma hasDerivAt_g83 {v : ℝ} (hv : 1 < v) : HasDerivAt g83 (phi83 (Real.log v)) v := by
  have hv0 : 0 < v := by linarith
  have hl : 0 < Real.log v := Real.log_pos hv
  have hlog := Real.hasDerivAt_log hv0.ne'
  have hden : HasDerivAt (fun v => Real.log v * (83 / 10 + Real.log v))
      (v⁻¹ * (83 / 10 + Real.log v) + Real.log v * v⁻¹) v :=
    hlog.mul (hlog.const_add (83 / 10))
  have hne : Real.log v * (83 / 10 + Real.log v) ≠ 0 := by positivity
  have := (hasDerivAt_id' v).div hden hne
  show HasDerivAt (fun v => v / (Real.log v * (83 / 10 + Real.log v))) _ v
  convert this using 1
  unfold phi83
  field_simp
  ring

lemma phi83_antitone : AntitoneOn phi83 (Ici 60) := by
  have hD : Convex ℝ (Ici (60 : ℝ)) := convex_Ici 60
  have hint : interior (Ici (60 : ℝ)) = Ioi 60 := interior_Ici
  -- `φ' = (num'·den - num·den')/den² = h·N(l)/h⁴` with `N(l) < 0`
  have hder : ∀ l : ℝ, 0 < l → HasDerivAt phi83
      (((83 / 10 + l + l - 2) * (l * (83 / 10 + l)) ^ 2 -
        (l * (83 / 10 + l) - (83 / 10 + 2 * l)) *
          (2 * (l * (83 / 10 + l)) * (83 / 10 + l + l))) / ((l * (83 / 10 + l)) ^ 2) ^ 2) l := by
    intro l hl
    have h1 : HasDerivAt (fun l : ℝ => l * (83 / 10 + l)) (1 * (83 / 10 + l) + l * 1) l :=
      (hasDerivAt_id' l).mul ((hasDerivAt_id' l).const_add (83 / 10))
    have h2 : HasDerivAt (fun l : ℝ => 83 / 10 + 2 * l) (2 * 1) l :=
      ((hasDerivAt_id' l).const_mul 2).const_add (83 / 10)
    have hnum := h1.sub h2
    have hden := h1.pow 2
    have hne : (l * (83 / 10 + l)) ^ 2 ≠ 0 := by positivity
    have hq := hnum.div hden hne
    show HasDerivAt (fun l => (l * (83 / 10 + l) - (83 / 10 + 2 * l)) / (l * (83 / 10 + l)) ^ 2) _ l
    convert hq using 1
    simp only [Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat]
    field_simp
    ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos hD
  · intro l hl
    exact (hder l (by simp at hl; linarith)).continuousAt.continuousWithinAt
  · intro l hl
    rw [hint] at hl ⊢
    exact (hder l (by simp at hl; linarith)).hasDerivWithinAt
  · intro l hl
    rw [hint] at hl
    simp only [mem_Ioi] at hl
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have hh : 0 < l * (83 / 10 + l) := by positivity
    have e : (83 / 10 + l + l - 2) * (l * (83 / 10 + l)) ^ 2 -
        (l * (83 / 10 + l) - (83 / 10 + 2 * l)) * (2 * (l * (83 / 10 + l)) * (83 / 10 + l + l)) =
        (l * (83 / 10 + l)) * (-2 * l ^ 3 + (6 - 3 * (83 / 10)) * l ^ 2 +
          (6 * (83 / 10) - (83 / 10) ^ 2) * l + 2 * (83 / 10) ^ 2) := by ring
    rw [e]
    apply mul_nonpos_of_nonneg_of_nonpos hh.le
    have hl0 : (0 : ℝ) < l := by linarith
    nlinarith [sq_nonneg l, mul_pos hl0 hl0]

/-- `g` is concave on `[e^60, ∞)`. -/
lemma g83_concave : ConcaveOn ℝ (Ici (Real.exp 60)) g83 := by
  have hD : Convex ℝ (Ici (Real.exp 60)) := convex_Ici _
  have hint : interior (Ici (Real.exp 60)) = Ioi (Real.exp 60) := interior_Ici
  have h1 : 1 < Real.exp 60 := by have := Real.add_one_le_exp 60; linarith
  apply AntitoneOn.concaveOn_of_deriv hD
  · intro v hv
    simp only [mem_Ici] at hv
    exact (hasDerivAt_g83 (by linarith)).continuousAt.continuousWithinAt
  · rw [hint]
    intro v hv
    simp only [mem_Ioi] at hv
    exact (hasDerivAt_g83 (by linarith)).differentiableAt.differentiableWithinAt
  · rw [hint]
    intro a ha b hb hab
    simp only [mem_Ioi] at ha hb
    rw [(hasDerivAt_g83 (by linarith)).deriv, (hasDerivAt_g83 (by linarith)).deriv]
    have hla : 60 ≤ Real.log a := by
      rw [Real.le_log_iff_exp_le (by linarith)]; exact ha.le
    have hlb : 60 ≤ Real.log b := by
      rw [Real.le_log_iff_exp_le (by linarith)]; exact hb.le
    exact phi83_antitone hla hlb (Real.log_le_log (by linarith) hab)

/-- **(7.8)**, page 61. -/
theorem eq78 (u y : ℝ) (hu : Real.exp 60 ≤ u) (huy : u ≤ y / 2) :
    u / (Real.log u * (83 / 10 + Real.log u)) +
      (y - u) / (Real.log (y - u) * (83 / 10 + Real.log (y - u))) ≤
      y / (Real.log (y / 2) * (83 / 10 + Real.log (y / 2))) := by
  have hc := g83_concave.2 (show u ∈ Ici (Real.exp 60) from hu)
    (show y - u ∈ Ici (Real.exp 60) by simp only [mem_Ici]; linarith)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hc
  rw [show 1 / 2 * u + 1 / 2 * (y - u) = y / 2 by ring] at hc
  unfold g83 at hc
  have e : y / (Real.log (y / 2) * (83 / 10 + Real.log (y / 2))) =
      2 * (y / 2 / (Real.log (y / 2) * (83 / 10 + Real.log (y / 2)))) := by ring
  rw [e]
  linarith

end LeanLab.RieselVaughan1983
