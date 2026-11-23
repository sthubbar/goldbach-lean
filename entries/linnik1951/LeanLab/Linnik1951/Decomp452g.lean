module

public import LeanLab.Linnik1951.Decomp452f

/-!
Original page 158 radial substitution preceding equation 4.6.
This change of variables preserves the complex integrand.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open MeasureTheory

/-- The radial change of variables keeps its inverse Jacobian inside the signed integral. -/
theorem radial_substitution452 (c a b : ℝ) (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b)
    (h : ℝ → ℂ) (_hh : ContinuousOn h (Set.Ioi 0)) :
    (∫ x : ℝ in a..b, h (Real.sqrt (c ^ 2 + x ^ 2))) =
      ∫ u : ℝ in (Real.sqrt (c ^ 2 + a ^ 2))..(Real.sqrt (c ^ 2 + b ^ 2)),
        (u / Real.sqrt (u ^ 2 - c ^ 2)) • h u := by
  let F : ℝ → ℝ := fun x => Real.sqrt (c ^ 2 + x ^ 2)
  let D : ℝ → ℝ := fun x => x / F x
  let G : ℝ → ℂ := fun u => (u / Real.sqrt (u ^ 2 - c ^ 2)) • h u
  have hF (x : ℝ) : 0 < F x := by dsimp [F]; positivity
  have hder (x : ℝ) : HasDerivAt F (D x) x := by
    have hbase : c ^ 2 + x ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < c ^ 2 + x ^ 2)
    have hs := (((hasDerivAt_id x).pow 2).const_add (c ^ 2)).sqrt hbase
    convert hs using 1 <;> dsimp [F, D] <;> ring
  have hcont : ContinuousOn F (Set.uIcc a b) := by
    dsimp [F]
    fun_prop
  have hswap := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := G) hcont
    (fun x _ => hder x)
    (fun x hx => by
      rw [min_eq_left hab, max_eq_right hab] at hx
      exact div_nonneg (ha.trans hx.1).le (hF x).le)
  change (∫ x : ℝ in a..b, h (F x)) = ∫ u : ℝ in F a..F b, G u
  calc
    _ = ∫ x : ℝ in a..b, D x • (G ∘ F) x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have hxp : 0 < x := ha.trans_le hx.1
      have hsq : F x ^ 2 = c ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
      have hroot : Real.sqrt (F x ^ 2 - c ^ 2) = x := by
        rw [hsq, add_sub_cancel_left, Real.sqrt_sq hxp.le]
      change h (F x) = (x / F x) • ((F x / Real.sqrt (F x ^ 2 - c ^ 2)) • h (F x))
      rw [hroot, smul_smul]
      have he : x / F x * (F x / x) = 1 := by
        field_simp [ne_of_gt hxp, ne_of_gt (hF x)]
      rw [he, one_smul]
    _ = _ := hswap

/-- The inverse derivative equals the Jacobian used in the paper. -/
theorem radial_inverse_jacobian452 (N u : ℝ) (hN : 0 < N) (hu : 1 / N < u) :
    u / Real.sqrt (u ^ 2 - (1 / N) ^ 2) = radialJacobian452 N u := by
  have hcp : 0 < 1 / N := one_div_pos.mpr hN
  have hup : 0 < u := hcp.trans hu
  have hdiff : 0 < u ^ 2 - (1 / N) ^ 2 := by nlinarith
  have heq : 1 - 1 / (N ^ 2 * u ^ 2) = (u ^ 2 - (1 / N) ^ 2) / u ^ 2 := by
    field_simp
  dsimp [radialJacobian452]
  rw [heq, Real.sqrt_div hdiff.le, Real.sqrt_sq hup.le]
  field_simp

/-- The radial substitution after setting the real part of the base to one over N. -/
theorem mellin_radial_substitution452 (N a b : ℝ) (hN : 0 < N) (ha : 0 < a)
    (hab : a ≤ b) (h : ℝ → ℂ) (hh : ContinuousOn h (Set.Ioi 0)) :
    (∫ x : ℝ in a..b, h (Real.sqrt ((1 / N) ^ 2 + x ^ 2))) =
      ∫ u : ℝ in (Real.sqrt ((1 / N) ^ 2 + a ^ 2))..(Real.sqrt ((1 / N) ^ 2 + b ^ 2)),
        radialJacobian452 N u • h u := by
  have hcp : 0 < 1 / N := one_div_pos.mpr hN
  rw [radial_substitution452 (1 / N) a b hcp ha hab h hh]
  have hlow : 1 / N < Real.sqrt ((1 / N) ^ 2 + a ^ 2) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  have horder : Real.sqrt ((1 / N) ^ 2 + a ^ 2) ≤
      Real.sqrt ((1 / N) ^ 2 + b ^ 2) := by
    apply Real.sqrt_le_sqrt
    have hpow := pow_le_pow_left₀ ha.le hab 2
    linarith
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le horder] at hu
  dsimp only
  rw [radial_inverse_jacobian452 N u hN (hlow.trans_le hu.1)]

end LeanLab.Linnik1951
