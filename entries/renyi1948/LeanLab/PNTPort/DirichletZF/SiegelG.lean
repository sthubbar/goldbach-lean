module

public import LeanLab.PNTPort.DirichletZF.SiegelTaylor
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# `F(s) - λ/(s - 1)` is entire

Lab proof, unit U-5111. AI wrote this file. Known mathematics, no cited input, a step of the
Estermann-Goldfeld proof of Siegel's theorem, Davenport chapter 21.

For non-principal `χ₁, χ₂` mod `N` with `χ₁χ₂ ≠ χ₀`, `P = L(χ₁) L(χ₂) L(χ₁χ₂)` is entire,
`λ = P(1)`, and
* `zetaOne_differentiable`: `(s - 1) ζ(s)`, with value `1` at `1`, is entire;
* `Gq_differentiable`: `G = dslope ((s - 1) ζ P) 1` is entire;
* `Gq_eq`: `G(s) = F(s) - λ/(s - 1)` for `s ≠ 1`, `F = ζ L(χ₁) L(χ₂) L(χ₁χ₂)`;
* `iteratedDeriv_inv_sub_one`: the `m`-th derivative of `1/(s - 1)` at `s ≠ 1` is
  `(-1)^m m! (s - 1)^{-(m+1)}`;
* `iteratedDeriv_Gq_two`: `G^{(m)}(2) = F^{(m)}(2) - λ (-1)^m m!`.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter Topology Nat

variable {N : ℕ} [NeZero N]

/-- `(s - 1) ζ(s)`, extended by `1` at `s = 1`. -/
noncomputable def zetaOne : ℂ → ℂ :=
  Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1

lemma zetaOne_differentiable : Differentiable ℂ zetaOne := by
  rw [← differentiableOn_univ]
  refine (differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) univ_mem).mp ⟨?_, ?_⟩
  · intro z hz
    have hz1 : z ≠ 1 := hz.2
    refine (DifferentiableAt.differentiableWithinAt ?_)
    have hev : (fun s ↦ (s - 1) * riemannZeta s) =ᶠ[𝓝 z] zetaOne := by
      filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
      simp [zetaOne, Function.update_of_ne hw]
    exact (((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz1))).congr_of_eventuallyEq
      hev.symm
  · unfold zetaOne
    rw [continuousAt_update_same]
    exact riemannZeta_residue_one

lemma zetaOne_of_ne {s : ℂ} (hs : s ≠ 1) : zetaOne s = (s - 1) * riemannZeta s := by
  simp [zetaOne, Function.update_of_ne hs]

/-- `P = L(χ₁) L(χ₂) L(χ₁χ₂)`. -/
noncomputable def Pq (χ₁ χ₂ : DirichletCharacter ℂ N) : ℂ → ℂ := fun s ↦
  DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
    DirichletCharacter.LFunction (χ₁ * χ₂) s

lemma Pq_differentiable {χ₁ χ₂ : DirichletCharacter ℂ N} (h1 : χ₁ ≠ 1) (h2 : χ₂ ≠ 1)
    (h12 : χ₁ * χ₂ ≠ 1) : Differentiable ℂ (Pq χ₁ χ₂) := fun z ↦
  (((DirichletCharacter.differentiable_LFunction h1 z).mul
    (DirichletCharacter.differentiable_LFunction h2 z)).mul
    (DirichletCharacter.differentiable_LFunction h12 z))

/-- `G = dslope ((s - 1) ζ P) 1`. -/
noncomputable def Gq (χ₁ χ₂ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  dslope (fun s ↦ zetaOne s * Pq χ₁ χ₂ s) 1

lemma Gq_differentiable {χ₁ χ₂ : DirichletCharacter ℂ N} (h1 : χ₁ ≠ 1) (h2 : χ₂ ≠ 1)
    (h12 : χ₁ * χ₂ ≠ 1) : Differentiable ℂ (Gq χ₁ χ₂) := by
  rw [← differentiableOn_univ]
  unfold Gq
  rw [differentiableOn_dslope univ_mem]
  exact (zetaOne_differentiable.mul (Pq_differentiable h1 h2 h12)).differentiableOn

lemma Gq_eq (χ₁ χ₂ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    Gq χ₁ χ₂ s = Fq χ₁ χ₂ s - Pq χ₁ χ₂ 1 / (s - 1) := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold Gq
  rw [dslope_of_ne _ hs, slope_def_field, zetaOne_of_ne hs]
  have h1 : zetaOne 1 = 1 := by simp [zetaOne]
  rw [h1]
  simp only [Fq, Pq]
  field_simp

lemma iteratedDeriv_inv_sub_one (m : ℕ) {s : ℂ} (hs : s ≠ 1) :
    iteratedDeriv m (fun z : ℂ ↦ (z - 1)⁻¹) s = (-1) ^ m * (m ! : ℂ) * (s - 1) ^ (-(m + 1 : ℤ)) := by
  induction m generalizing s with
  | zero => simp [zpow_neg_one]
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m (fun z : ℂ ↦ (z - 1)⁻¹) =ᶠ[𝓝 s]
        fun z ↦ (-1) ^ m * (m ! : ℂ) * (z - 1) ^ (-(m + 1 : ℤ)) := by
      filter_upwards [isOpen_ne.mem_nhds hs] with w hw
      exact ih hw
    rw [hev.deriv_eq]
    have hd : HasDerivAt (fun z : ℂ ↦ (z - 1) ^ (-(m + 1 : ℤ)))
        ((-(m + 1 : ℤ) : ℂ) * (s - 1) ^ (-(m + 1 : ℤ) - 1)) s := by
      have := (hasDerivAt_zpow (-(m + 1 : ℤ)) (s - 1) (Or.inl (sub_ne_zero.mpr hs))).comp s
        ((hasDerivAt_id s).sub_const 1)
      convert this using 1
      · funext x; simp
      · push_cast; ring
    rw [(hd.const_mul ((-1) ^ m * (m ! : ℂ))).deriv]
    rw [show -((m + 1 : ℕ) + 1 : ℤ) = -(m + 1 : ℤ) - 1 by push_cast; ring]
    push_cast
    rw [Nat.factorial_succ]
    push_cast
    ring

/-- `G^{(m)}(2) = F^{(m)}(2) - λ (-1)^m m!`. -/
lemma iteratedDeriv_Gq_two {χ₁ χ₂ : DirichletCharacter ℂ N} (h1 : χ₁ ≠ 1) (h2 : χ₂ ≠ 1)
    (h12 : χ₁ * χ₂ ≠ 1) (m : ℕ) :
    iteratedDeriv m (Gq χ₁ χ₂) 2 =
      iteratedDeriv m (Fq χ₁ χ₂) 2 - Pq χ₁ χ₂ 1 * ((-1) ^ m * (m ! : ℂ)) := by
  have hne : ∀ᶠ z in 𝓝 (2 : ℂ), z ≠ 1 := isOpen_ne.mem_nhds (by norm_num)
  have hev : Gq χ₁ χ₂ =ᶠ[𝓝 (2 : ℂ)]
      fun z ↦ Fq χ₁ χ₂ z - Pq χ₁ χ₂ 1 * (z - 1)⁻¹ := by
    filter_upwards [hne] with z hz
    rw [Gq_eq χ₁ χ₂ hz, div_eq_mul_inv]
  rw [(hev.iteratedDeriv m).eq_of_nhds]
  -- analyticity near 2
  set U : Set ℂ := {z | 1 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h2U : (2 : ℂ) ∈ U := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  have hneU : ∀ z ∈ U, z ≠ 1 := by intro z hz h; simp [U, h] at hz
  have hdF : DifferentiableOn ℂ (Fq χ₁ χ₂) U := fun z hz ↦
    ((((differentiableAt_riemannZeta (hneU z hz)).mul
      (DirichletCharacter.differentiable_LFunction h1 z)).mul
      (DirichletCharacter.differentiable_LFunction h2 z)).mul
      (DirichletCharacter.differentiable_LFunction h12 z)).differentiableWithinAt
  have hFc : ContDiffAt ℂ m (Fq χ₁ χ₂) 2 :=
    (hdF.analyticAt (hUo.mem_nhds h2U)).contDiffAt
  have hdI : DifferentiableOn ℂ (fun z : ℂ ↦ (z - 1)⁻¹) U := fun z hz ↦
    (DifferentiableAt.inv (h := fun z : ℂ ↦ z - 1) (by fun_prop)
      (sub_ne_zero.mpr (hneU z hz))).differentiableWithinAt
  have hIc : ContDiffAt ℂ m (fun z : ℂ ↦ Pq χ₁ χ₂ 1 * (z - 1)⁻¹) 2 :=
    contDiffAt_const.mul (hdI.analyticAt (hUo.mem_nhds h2U)).contDiffAt
  rw [iteratedDeriv_fun_sub hFc hIc, iteratedDeriv_const_mul_field,
    iteratedDeriv_inv_sub_one m (by norm_num)]
  norm_num

end LeanLab.PNTPort.DirichletZF

