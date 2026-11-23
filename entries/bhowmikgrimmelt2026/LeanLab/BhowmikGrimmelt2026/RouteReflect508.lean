module

public import LeanLab.BhowmikGrimmelt2026.Decomp541a
public import LeanLab.BhowmikGrimmelt2026.Decomp508a

/-!
Reflection of strip zeros with multiplicity under the functional equation.
P0029, Bhowmik and Grimmelt survey, page 11 display 3.7 counts the zeros of L(s, χ) in
unit windows. The count cited there is Davenport, Multiplicative Number Theory, chapter 16,
zero count by Jensen, and it is transferred from the right half of the critical strip to the
left half by the functional equation of Davenport chapter 9. This file proves that transfer:
the map ρ ↦ 1 - ρ sends strip zeros of L(s, χ) to strip zeros of L(s, χ⁻¹) and keeps the
analytic multiplicity, for every Dirichlet character, primitive or not.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- Davenport chapter 9, the Gamma factor of the functional equation is analytic in the right
half plane. Used for P0029 page 11 display 3.7. -/
theorem gamma_factor_analyticAt508 {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ χ.gammaFactor s := by
  classical
  have hinv : AnalyticAt ℂ (fun z => (χ.gammaFactor z)⁻¹) s := by
    apply Differentiable.analyticAt
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Complex.differentiable_Gammaℝ_inv
    · exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)
  have h := hinv.inv (inv_ne_zero (gamma_factor_ne_zero541 χ hs))
  have he : (fun z => (χ.gammaFactor z)⁻¹)⁻¹ = χ.gammaFactor := by
    funext z
    simp only [Pi.inv_apply, inv_inv]
  rwa [he] at h

/-- Davenport chapter 9, the functional equation of a primitive character, read as one
inequality of analytic orders: the order of L(s, χ) at a strip point ρ is at most the order
of L(s, χ⁻¹) at 1 - ρ. Used for P0029 page 11 display 3.7. -/
theorem primitive_order_reflection_le508 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≤
      analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) := by
  have hi : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  let H : ℂ → ℂ := fun s => (q : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ⁻¹ *
    χ.gammaFactor s * (χ⁻¹.gammaFactor (1 - s))⁻¹
  have hρ1 : ρ ≠ 1 := by intro h; simp [h] at h1
  -- analyticity of the multiplier
  have hH : AnalyticAt ℂ H ρ := by
    have hpow : AnalyticAt ℂ (fun s : ℂ => (q : ℂ) ^ (s - 1 / 2)) ρ := by
      apply Differentiable.analyticAt
      intro s
      exact (differentiableAt_id.sub_const _).const_cpow (Or.inl hq)
    have hg2 : AnalyticAt ℂ (fun s : ℂ => (χ⁻¹.gammaFactor (1 - s))⁻¹) ρ := by
      classical
      apply Differentiable.analyticAt
      unfold DirichletCharacter.gammaFactor
      split_ifs
      · exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.const_sub 1)
      · exact Complex.differentiable_Gammaℝ_inv.comp
          ((differentiable_id.const_sub 1).add_const 1)
    exact ((hpow.mul analyticAt_const).mul (gamma_factor_analyticAt508 χ h0)).mul hg2
  -- analyticity of the L function
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ := by
    have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {(1 : ℂ)}ᶜ := fun s hs =>
      (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hρ1)
  -- the functional equation near ρ
  have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev : (DirichletCharacter.LFunction χ⁻¹ ∘ fun s : ℂ => 1 - s) =ᶠ[𝓝 ρ]
      H * DirichletCharacter.LFunction χ := by
    filter_upwards [hopen.mem_nhds (show ρ ∈ {s : ℂ | 0 < s.re ∧ s.re < 1} from ⟨h0, h1⟩)]
      with s hs
    have hs0 : s ≠ 0 := by
      intro h
      have := hs.1
      simp [h] at this
    have hr : 1 - s ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
      linarith [hs.2]
    have hg := gamma_factor_ne_zero541 χ hs.1
    have hc : DirichletCharacter.completedLFunction χ s =
        DirichletCharacter.LFunction χ s * χ.gammaFactor s := by
      rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl hs0), div_mul_cancel₀ _ hg]
    have he := hi.completedLFunction_one_sub s
    rw [inv_inv] at he
    simp only [Function.comp_apply, Pi.mul_apply, H]
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (Or.inl hr), he, hc,
      div_eq_mul_inv]
    ring
  have hcomp : analyticOrderAt (DirichletCharacter.LFunction χ⁻¹ ∘ fun s : ℂ => 1 - s) ρ =
      analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) := by
    have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ :=
      (differentiable_id.const_sub (1 : ℂ)).analyticAt ρ
    have hd : deriv (fun s : ℂ => 1 - s) ρ ≠ 0 := by
      rw [deriv_const_sub, deriv_id'']
      norm_num
    exact analyticOrderAt_comp_of_deriv_ne_zero hg hd
  rw [← hcomp, analyticOrderAt_congr hev, analyticOrderAt_mul hH hL]
  exact le_add_self

/-- Davenport chapter 9, the functional equation of a primitive character keeps the
multiplicity of a zero in the open critical strip: the multiplicity of L(s, χ⁻¹) at 1 - ρ
equals the multiplicity of L(s, χ) at ρ. This covers the trivial character of level 1, the
Riemann zeta function. Used for P0029 page 11 display 3.7. -/
theorem primitive_mult_reflection508 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    mult χ⁻¹ (1 - ρ) = mult χ ρ := by
  have hi : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  have ha := primitive_order_reflection_le508 χ hχ h0 h1
  have hb := primitive_order_reflection_le508 χ⁻¹ hi
    (ρ := 1 - ρ) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  rw [inv_inv, sub_sub_cancel] at hb
  unfold mult analyticOrderNatAt
  rw [le_antisymm hb ha]

/-- Davenport chapter 9 with the Euler factors of chapter 5: a character induced from a
primitive one keeps strip multiplicities under ρ ↦ 1 - ρ. Used for P0029 page 11
display 3.7. -/
theorem induced_mult_reflection508 {r q : ℕ} [NeZero r] [NeZero q] (hd : r ∣ q)
    (ψ : DirichletCharacter ℂ r) (hψ : ψ.IsPrimitive)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    mult (DirichletCharacter.changeLevel hd ψ)⁻¹ (1 - ρ) =
      mult (DirichletCharacter.changeLevel hd ψ) ρ := by
  have h0' : 0 < (1 - ρ).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have h1' : (1 - ρ).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  rw [← map_inv, character_mult_changeLevel508 hd ψ⁻¹ h0' h1',
    character_mult_changeLevel508 hd ψ h0 h1]
  exact primitive_mult_reflection508 ψ hψ h0 h1

/-- Davenport chapter 9, the functional equation keeps the multiplicity of a zero in the
open critical strip for every Dirichlet character, by passing to the primitive character
that induces it. Used for P0029 page 11 display 3.7. -/
theorem character_mult_reflection508 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    mult χ⁻¹ (1 - ρ) = mult χ ρ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hd := χ.conductor_dvd_level
  have h := induced_mult_reflection508 hd χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive h0 h1
  simpa only [χ.changeLevel_primitiveCharacter] using h

/-- Davenport chapter 9, a zero of L(s, χ) in the open critical strip reflects to a zero of
L(s, χ⁻¹) at 1 - ρ, for every Dirichlet character. Used for P0029 page 11 display 3.7. -/
theorem character_zero_reflection508 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hd := χ.conductor_dvd_level
  have h0' : 0 < (1 - ρ).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have h1' : (1 - ρ).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hz : DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
    have h : DirichletCharacter.LFunction χ ρ = 0 ↔
        DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
      simpa only [χ.changeLevel_primitiveCharacter] using
        character_zero_changeLevel508 hd χ.primitiveCharacter h0 h1
    exact h.mp hρ
  have hr := primitive_zero_reflection541 χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive hz h0 h1
  have h := (character_zero_changeLevel508 hd χ.primitiveCharacter⁻¹ h0' h1').mpr hr
  rw [map_inv] at h
  simpa only [χ.changeLevel_primitiveCharacter] using h

end LeanLab.BhowmikGrimmelt2026
