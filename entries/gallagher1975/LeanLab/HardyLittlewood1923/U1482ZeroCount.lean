module

public import LeanLab.HardyLittlewood1923.U1479Split
public import LeanLab.PNTPort.DirichletZF.U1482Jensen

/-!
AI-written Lean code, Claude, 2026-10-22, PC run 20261022T1302Z-31860, unit U-1482, paper P0004.

# Hardy-Littlewood 1923, U-1479's cited input `ZeroCountUnit`, PROVED

`ZeroCountUnit`, Davenport ch. 16, the zero count per unit height: for primitive `χ` mod `q` and
`t ≥ 0`, the nontrivial zeros with `t ≤ |γ| ≤ t + 1` are finite and number, with multiplicity,
at most `A log (q (t + 2))`. Hardy and Littlewood's Lemma 6, eq 2.611 p. 14, is a weaker form.

Route, all PROVED here or in PNTPort/DirichletZF/U1482Jensen.lean:
* zeros with `1/2 ≤ β < 1` lie within `6/5` of `3/2 ± i (t + 1/2)`, and Mathlib's Jensen
  inequality on the disc of radius `7/5`, with the growth bound of DirichletZF Growth.lean for
  `χ ≠ 1`, the bound for `(s - 1) ζ(s)` for `q = 1`, and `‖L(3/2 + iτ, χ)‖ ≥ 1/Z` from the
  Dirichlet series identity `L(s, χ) L(s, χμ) = 1`, counts them: `rw_count_all`;
* zeros with `0 < β < 1/2` reflect to zeros `1 - ρ` of `L(s, χ⁻¹)` with `β > 1/2`, U-1479's
  `reflect_zero`, and `mult_le_reflect` here shows the multiplicity does not drop, from Mathlib's
  functional equation, whose factor `q^{s - 1/2} ε Γ-factor(s) / Γ-factor(1 - s)` is analytic in
  the strip;
* `zeroCountUnit`: the four pieces sum to `4 log (24 Z q (t + 9/2)²) / log (7/6)`, which is at
  most `A log (q (t + 2))`.

Headline `printedA_form_all_U1482`: eq 3.113 p. 21, CONDITIONAL ON `TruncExplicitPrim` only.
No placeholder proof, no axiom. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1482

open Finset Complex Filter Topology
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1438 (NoZerosRight)
open LeanLab.HardyLittlewood1923.U1444 (singR)
open LeanLab.HardyLittlewood1923.U1479 (IsNTZero mult mult_nonneg ZeroCountUnit TruncExplicitPrim
  reflect_zero)
open LeanLab.PNTPort.DirichletZF.U1482 (RW rw_count_L rw_count_zeta gZ gZ_analyticAt ord_gZ_enat
  gZ_cen_ne cen)
open LeanLab.PNTPort.DirichletZF (Z Z_pos one_le_Z LFunction_c_ne_zero)

/-! ### Gamma factors -/

lemma gammaR_diff {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ Gammaℝ w := by
  have h : DifferentiableAt ℂ (fun s => ((Gammaℝ s)⁻¹)⁻¹) w :=
    (differentiable_Gammaℝ_inv w).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hw))
  simpa only [inv_inv] using h

lemma gf_diff {q : ℕ} (ψ : DirichletCharacter ℂ q) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor ψ) w := by
  rcases ψ.even_or_odd with he | ho
  · have : DirichletCharacter.gammaFactor ψ = Gammaℝ := funext he.gammaFactor_def
    rw [this]; exact gammaR_diff hw
  · have : DirichletCharacter.gammaFactor ψ = fun s => Gammaℝ (s + 1) :=
      funext ho.gammaFactor_def
    rw [this]
    exact DifferentiableAt.comp (f := fun s : ℂ => s + 1) w
      (gammaR_diff (by simp; linarith)) (differentiableAt_id.add_const 1)

lemma gf_inv_diff {q : ℕ} (ψ : DirichletCharacter ℂ q) (w : ℂ) :
    DifferentiableAt ℂ (fun s => (DirichletCharacter.gammaFactor ψ (1 - s))⁻¹) w := by
  rcases ψ.even_or_odd with he | ho
  · simp only [he.gammaFactor_def]
    exact DifferentiableAt.comp (f := fun s : ℂ => 1 - s) (g := fun s => (Gammaℝ s)⁻¹) w
      (differentiable_Gammaℝ_inv _) ((differentiableAt_const _).sub differentiableAt_id)
  · simp only [ho.gammaFactor_def]
    exact DifferentiableAt.comp (f := fun s : ℂ => 1 - s + 1) (g := fun s => (Gammaℝ s)⁻¹) w
      (differentiable_Gammaℝ_inv _)
      (((differentiableAt_const _).sub differentiableAt_id).add_const 1)

lemma gf_ne {q : ℕ} (ψ : DirichletCharacter ℂ q) {w : ℂ} (hw : 0 < w.re) :
    DirichletCharacter.gammaFactor ψ w ≠ 0 := by
  rcases ψ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hw
  · rw [ho.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-! ### The functional equation as a factorization in the strip -/

/-- The factor `q^{s - 1/2} ε(χ⁻¹) γ(χ, s) / γ(χ⁻¹, 1 - s)`. -/
noncomputable def G {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ⁻¹ *
    DirichletCharacter.gammaFactor χ s * (DirichletCharacter.gammaFactor χ⁻¹ (1 - s))⁻¹

lemma fe_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    DirichletCharacter.LFunction χ⁻¹ (1 - s) = G χ s * DirichletCharacter.LFunction χ s := by
  have hs0 : s ≠ 0 := by intro e; rw [e] at h0; simp at h0
  have h1s : 1 - s ≠ 0 := by
    intro e
    have : (1 - s).re = 0 := by rw [e]; simp
    simp at this; linarith
  have hinv : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have hfe := DirichletCharacter.IsPrimitive.completedLFunction_one_sub hinv s
  rw [inv_inv] at hfe
  have hgf := gf_ne χ h0
  have hc : DirichletCharacter.completedLFunction χ s =
      DirichletCharacter.gammaFactor χ s * DirichletCharacter.LFunction χ s := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)]
    field_simp
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inl h1s), hfe, hc,
    G, div_eq_mul_inv]
  ring

/-- The strip `0 < Re s < 1` is open. -/
lemma strip_open : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma G_analyticAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : AnalyticAt ℂ (G χ) ρ := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  refine DifferentiableOn.analyticAt (s := {s : ℂ | 0 < s.re ∧ s.re < 1}) ?_
    (strip_open.mem_nhds ⟨h0, h1⟩)
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold G
  exact ((((differentiableAt_id.sub_const (1 / 2 : ℂ)).const_cpow (Or.inl hq0)).mul_const _).mul
    (gf_diff χ hs.1)).mul (gf_inv_diff χ⁻¹ s)

/-- **Multiplicity does not drop under reflection**: for primitive `χ` and `0 < Re ρ < 1`,
`m(χ, ρ) ≤ m(χ⁻¹, 1 - ρ)`, given analyticity at `ρ` and finite order at `1 - ρ`. -/
theorem mult_le_reflect {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ)
    (hT : analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) ≠ ⊤) :
    mult χ ρ ≤ mult χ⁻¹ (1 - ρ) := by
  have hAff : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := analyticAt_const.sub analyticAt_id
  have hcomp : analyticOrderAt (DirichletCharacter.LFunction χ⁻¹ ∘ fun s : ℂ => 1 - s) ρ =
      analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) := by
    apply analyticOrderAt_comp_of_deriv_ne_zero hAff
    have : deriv (fun s : ℂ => 1 - s) ρ = -1 := by
      have hd : HasDerivAt (fun s : ℂ => 1 - s) (-1) ρ := by
        simpa using (hasDerivAt_id ρ).const_sub (1 : ℂ)
      exact hd.deriv
    rw [this]; norm_num
  have hev : (DirichletCharacter.LFunction χ⁻¹ ∘ fun s : ℂ => 1 - s) =ᶠ[𝓝 ρ]
      (G χ * DirichletCharacter.LFunction χ) := by
    filter_upwards [strip_open.mem_nhds ⟨h0, h1⟩] with s hs
    simp only [Function.comp_apply, Pi.mul_apply]
    exact fe_strip hχ hs.1 hs.2
  have key : analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) =
      analyticOrderAt (G χ) ρ + analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
    rw [← hcomp, analyticOrderAt_congr hev, analyticOrderAt_mul (G_analyticAt χ h0 h1) hA]
  rw [key] at hT
  obtain ⟨hGT, hLT⟩ := WithTop.add_ne_top.mp hT
  simp only [mult, analyticOrderNatAt, key, ENat.toNat_add hGT hLT, Nat.cast_add]
  linarith [Nat.cast_nonneg (α := ℝ) (analyticOrderAt (G χ) ρ).toNat]

/-! ### Analyticity and finite order of `L(s, ψ)` -/

lemma L_analyticAt {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {w : ℂ} (hw : w ≠ 1) :
    AnalyticAt ℂ (DirichletCharacter.LFunction ψ) w :=
  DifferentiableOn.analyticAt (s := {z : ℂ | z ≠ 1})
    (fun z hz => (DirichletCharacter.differentiableAt_LFunction ψ z
      (Or.inl hz)).differentiableWithinAt) (isOpen_compl_singleton.mem_nhds hw)

lemma L_ord_ne_top {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : q = 1 ∨ ψ ≠ 1)
    {w : ℂ} (hw : w ≠ 1) : analyticOrderAt (DirichletCharacter.LFunction ψ) w ≠ ⊤ := by
  rcases hψ with rfl | hψ
  · rw [DirichletCharacter.LFunction_modOne_eq, ← ord_gZ_enat hw]
    have hent : AnalyticOnNhd ℂ gZ Set.univ := fun z _ => gZ_analyticAt z
    refine hent.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ (cen 0)) (Set.mem_univ w) ?_
    simp [(gZ_analyticAt (cen 0)).analyticOrderAt_eq_zero.mpr (gZ_cen_ne 0)]
  · have hent : AnalyticOnNhd ℂ (DirichletCharacter.LFunction ψ) Set.univ := fun z _ =>
      (DirichletCharacter.differentiable_LFunction hψ).analyticAt z
    refine hent.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ (cen 0)) (Set.mem_univ w) ?_
    simp [(hent (cen 0) (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr
      (LFunction_c_ne_zero ψ 0)]

/-! ### Right windows for every character with `q = 1` or `ψ ≠ 1` -/

theorem rw_count_all {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : q = 1 ∨ ψ ≠ 1)
    (τ : ℝ) :
    (RW (DirichletCharacter.LFunction ψ) τ).Finite ∧
      ∀ s : Finset ℂ, (∀ ρ ∈ s, ρ ∈ RW (DirichletCharacter.LFunction ψ) τ) →
        ∑ ρ ∈ s, (analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ : ℝ) ≤
          Real.log (24 * Z * q * (|τ| + 4) ^ 2) / Real.log (7 / 6) := by
  rcases hψ with rfl | hψ
  · rw [DirichletCharacter.LFunction_modOne_eq]
    have := rw_count_zeta τ
    simp only [Nat.cast_one, mul_one]
    exact this
  · exact rw_count_L hψ τ

/-- Summing a weight `m` over a finset sent injectively into a right window. -/
lemma sum_le_RW {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : q = 1 ∨ ψ ≠ 1) (τ : ℝ)
    (s : Finset ℂ) (g : ℂ → ℂ) (hg : Set.InjOn g (s : Set ℂ))
    (hmem : ∀ ρ ∈ s, g ρ ∈ RW (DirichletCharacter.LFunction ψ) τ) (m : ℂ → ℝ)
    (hm : ∀ ρ ∈ s, m ρ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction ψ) (g ρ) : ℝ)) :
    ∑ ρ ∈ s, m ρ ≤ Real.log (24 * Z * q * (|τ| + 4) ^ 2) / Real.log (7 / 6) := by
  classical
  refine (sum_le_sum hm).trans ?_
  rw [← Finset.sum_image (f := fun z => (analyticOrderNatAt (DirichletCharacter.LFunction ψ) z : ℝ))
    hg]
  refine (rw_count_all ψ hψ τ).2 _ fun x hx => ?_
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hx
  exact hmem ρ hρ

lemma im_window_pos {t y : ℝ} (h1 : t ≤ |y|) (h2 : |y| ≤ t + 1) (hy : 0 ≤ y) :
    |y - (t + 1 / 2)| ≤ 1 / 2 := by
  rw [abs_of_nonneg hy] at h1 h2
  rw [abs_le]; constructor <;> linarith

lemma im_window_neg {t y : ℝ} (h1 : t ≤ |y|) (h2 : |y| ≤ t + 1) (hy : y < 0) :
    |y - -(t + 1 / 2)| ≤ 1 / 2 := by
  rw [abs_of_neg hy] at h1 h2
  rw [abs_le]; constructor <;> linarith

/-! ### `ZeroCountUnit`, PROVED -/

/-- The final numerical step: `log (24 Z q (t + 9/2)²) ≤ (log (122 Z) / log 2 + 2) log (q (t + 2))`. -/
lemma log_bound {q : ℕ} (hq : 1 ≤ q) {t : ℝ} (ht : 0 ≤ t) :
    Real.log (24 * Z * q * (|t + 1 / 2| + 4) ^ 2) ≤
      (Real.log (122 * Z) / Real.log 2 + 2) * Real.log (q * (t + 2)) := by
  have hZ := one_le_Z
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t + 1 / 2)]
  set x : ℝ := q * (t + 2) with hx
  have hx2 : 2 ≤ x := by rw [hx]; nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
  have hK : 0 ≤ Real.log (122 * Z) := Real.log_nonneg (by linarith)
  have h1 : 24 * Z * q * (t + 1 / 2 + 4) ^ 2 ≤ 122 * Z * x ^ 2 := by
    have ha : (t + 1 / 2 + 4) ^ 2 ≤ (81 / 16) * (t + 2) ^ 2 := by nlinarith
    have hb : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have hc : 24 * Z * q * (t + 1 / 2 + 4) ^ 2 ≤ 24 * Z * q * ((81 / 16) * (t + 2) ^ 2) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    have hd : 24 * Z * (q : ℝ) * ((81 / 16) * (t + 2) ^ 2) ≤
        24 * Z * (q : ℝ) ^ 2 * ((81 / 16) * (t + 2) ^ 2) := by
      have : 0 ≤ 24 * Z * ((81 / 16) * (t + 2) ^ 2) := by positivity
      nlinarith
    have he : 24 * Z * (q : ℝ) ^ 2 * ((81 / 16) * (t + 2) ^ 2) ≤ 122 * Z * x ^ 2 := by
      rw [hx]
      have : 0 ≤ Z * ((q : ℝ) * (t + 2)) ^ 2 := by positivity
      nlinarith
    linarith
  have hpos : 0 < 24 * Z * q * (t + 1 / 2 + 4) ^ 2 := by positivity
  calc Real.log (24 * Z * q * (t + 1 / 2 + 4) ^ 2) ≤ Real.log (122 * Z * x ^ 2) :=
        Real.log_le_log hpos h1
    _ = Real.log (122 * Z) + 2 * Real.log x := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
    _ ≤ Real.log (122 * Z) / Real.log 2 * Real.log x + 2 * Real.log x := by
        have : Real.log (122 * Z) ≤ Real.log (122 * Z) / Real.log 2 * Real.log x := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
          exact mul_le_mul_of_nonneg_left hlx hK
        linarith
    _ = (Real.log (122 * Z) / Real.log 2 + 2) * Real.log x := by ring

/-- **`ZeroCountUnit`, PROVED.** -/
theorem zeroCountUnit : ZeroCountUnit := by
  classical
  have hl76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hK : 0 ≤ Real.log (122 * Z) := Real.log_nonneg (by linarith [one_le_Z])
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * (Real.log (122 * Z) / Real.log 2 + 2) / Real.log (7 / 6), by positivity,
    fun q _ χ hχ t ht => ?_⟩
  have hq : q = 1 ∨ χ ≠ 1 := by
    by_cases h : q = 1
    · exact Or.inl h
    · right; intro h1; apply h
      have := hχ
      rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at this
      exact this.symm
  have hq' : q = 1 ∨ χ⁻¹ ≠ 1 := hq.imp_right fun h => inv_ne_one.mpr h
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set τ : ℝ := t + 1 / 2 with hτ
  have habs1 : |τ| = |t + 1 / 2| := by rw [hτ]
  have habs2 : |-τ| = |t + 1 / 2| := by rw [abs_neg, hτ]
  set B := Real.log (24 * Z * q * (|t + 1 / 2| + 4) ^ 2) / Real.log (7 / 6) with hB
  -- window membership
  let W : ℂ → Prop := fun ρ => IsNTZero χ ρ ∧ t ≤ |ρ.im| ∧ |ρ.im| ≤ t + 1
  have mem_hp : ∀ ρ, W ρ → 1 / 2 ≤ ρ.re → 0 ≤ ρ.im →
      ρ ∈ RW (DirichletCharacter.LFunction χ) τ := fun ρ h hr hi =>
    ⟨h.1.1, hr, h.1.2.2, im_window_pos h.2.1 h.2.2 hi⟩
  have mem_hn : ∀ ρ, W ρ → 1 / 2 ≤ ρ.re → ρ.im < 0 →
      ρ ∈ RW (DirichletCharacter.LFunction χ) (-τ) := fun ρ h hr hi =>
    ⟨h.1.1, hr, h.1.2.2, im_window_neg h.2.1 h.2.2 hi⟩
  have mem_lp : ∀ ρ, W ρ → ρ.re < 1 / 2 → 0 ≤ ρ.im →
      1 - ρ ∈ RW (DirichletCharacter.LFunction χ⁻¹) (-τ) := by
    intro ρ h hr hi
    have hz := reflect_zero hχ h.1
    refine ⟨hz.1, by simp; linarith, hz.2.2, ?_⟩
    have e : (1 - ρ).im - -τ = -(ρ.im - τ) := by simp; ring
    rw [e, abs_neg]; exact im_window_pos h.2.1 h.2.2 hi
  have mem_ln : ∀ ρ, W ρ → ρ.re < 1 / 2 → ρ.im < 0 →
      1 - ρ ∈ RW (DirichletCharacter.LFunction χ⁻¹) τ := by
    intro ρ h hr hi
    have hz := reflect_zero hχ h.1
    refine ⟨hz.1, by simp; linarith, hz.2.2, ?_⟩
    have e : (1 - ρ).im - τ = -(ρ.im - -τ) := by simp; ring
    rw [e, abs_neg]; exact im_window_neg h.2.1 h.2.2 hi
  -- reflected multiplicity
  have hmr : ∀ ρ, W ρ → mult χ ρ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹)
      (1 - ρ) : ℝ) := by
    intro ρ h
    have hρ1 : ρ ≠ 1 := by intro e; have := h.1.2.2; rw [e] at this; simp at this
    have h1ρ : 1 - ρ ≠ 1 := by
      intro e
      have : (1 - ρ).re = 1 := by rw [e]; simp
      simp at this; linarith [h.1.2.1]
    exact mult_le_reflect hχ h.1.2.1 h.1.2.2 (L_analyticAt χ hρ1) (L_ord_ne_top χ⁻¹ hq' h1ρ)
  have inj1 : ∀ S : Finset ℂ, Set.InjOn (fun z : ℂ => 1 - z) (S : Set ℂ) := by
    intro S a _ b _ hab; simpa using hab
  have inj0 : ∀ S : Finset ℂ, Set.InjOn (fun z : ℂ => z) (S : Set ℂ) := by
    intro S a _ b _ hab; simpa using hab
  refine ⟨?_, fun s hs => ?_⟩
  · -- finiteness
    have f1 := (rw_count_all χ hq τ).1
    have f2 := (rw_count_all χ hq (-τ)).1
    have f3 := (rw_count_all χ⁻¹ hq' τ).1
    have f4 := (rw_count_all χ⁻¹ hq' (-τ)).1
    refine ((f1.union f2).union ((f3.union f4).image fun z => 1 - z)).subset ?_
    intro ρ hρ
    have h : W ρ := hρ
    rcases le_or_gt (1 / 2) ρ.re with hr | hr <;> rcases le_or_gt 0 ρ.im with hi | hi
    · exact Or.inl (Or.inl (mem_hp ρ h hr hi))
    · exact Or.inl (Or.inr (mem_hn ρ h hr hi))
    · exact Or.inr ⟨1 - ρ, Or.inr (mem_lp ρ h hr hi), by ring⟩
    · exact Or.inr ⟨1 - ρ, Or.inl (mem_ln ρ h hr hi), by ring⟩
  · -- the sum, in four pieces
    have hW : ∀ ρ ∈ s, W ρ := hs
    rw [← sum_filter_add_sum_filter_not s (fun ρ => 1 / 2 ≤ ρ.re),
      ← sum_filter_add_sum_filter_not (s.filter fun ρ => 1 / 2 ≤ ρ.re) (fun ρ => 0 ≤ ρ.im),
      ← sum_filter_add_sum_filter_not (s.filter fun ρ => ¬ 1 / 2 ≤ ρ.re) (fun ρ => 0 ≤ ρ.im)]
    have p1 : ∑ ρ ∈ (s.filter fun ρ => 1 / 2 ≤ ρ.re).filter (fun ρ => 0 ≤ ρ.im), mult χ ρ ≤ B := by
      have := sum_le_RW χ hq τ ((s.filter fun ρ => 1 / 2 ≤ ρ.re).filter (fun ρ => 0 ≤ ρ.im)) (fun z => z) (inj0 _) (fun ρ hρ => by
        simp only [mem_filter] at hρ
        exact mem_hp ρ (hW ρ hρ.1.1) hρ.1.2 hρ.2) (mult χ) (fun ρ _ => le_rfl)
      rwa [habs1] at this
    have p2 : ∑ ρ ∈ (s.filter fun ρ => 1 / 2 ≤ ρ.re).filter (fun ρ => ¬ 0 ≤ ρ.im), mult χ ρ ≤ B := by
      have := sum_le_RW χ hq (-τ) ((s.filter fun ρ => 1 / 2 ≤ ρ.re).filter (fun ρ => ¬ 0 ≤ ρ.im)) (fun z => z) (inj0 _) (fun ρ hρ => by
        simp only [mem_filter] at hρ
        exact mem_hn ρ (hW ρ hρ.1.1) hρ.1.2 (lt_of_not_ge hρ.2)) (mult χ) (fun ρ _ => le_rfl)
      rwa [habs2] at this
    have p3 : ∑ ρ ∈ (s.filter fun ρ => ¬ 1 / 2 ≤ ρ.re).filter (fun ρ => 0 ≤ ρ.im), mult χ ρ ≤ B := by
      have := sum_le_RW χ⁻¹ hq' (-τ) ((s.filter fun ρ => ¬ 1 / 2 ≤ ρ.re).filter (fun ρ => 0 ≤ ρ.im))
        (fun z => 1 - z) (inj1 _) (fun ρ hρ => by
        simp only [mem_filter] at hρ
        exact mem_lp ρ (hW ρ hρ.1.1) (lt_of_not_ge hρ.1.2) hρ.2) (mult χ)
        (fun ρ hρ => by
          simp only [mem_filter] at hρ
          exact hmr ρ (hW ρ hρ.1.1))
      rwa [habs2] at this
    have p4 : ∑ ρ ∈ (s.filter fun ρ => ¬ 1 / 2 ≤ ρ.re).filter (fun ρ => ¬ 0 ≤ ρ.im), mult χ ρ ≤
        B := by
      have := sum_le_RW χ⁻¹ hq' τ ((s.filter fun ρ => ¬ 1 / 2 ≤ ρ.re).filter (fun ρ => ¬ 0 ≤ ρ.im))
        (fun z => 1 - z) (inj1 _) (fun ρ hρ => by
        simp only [mem_filter] at hρ
        exact mem_ln ρ (hW ρ hρ.1.1) (lt_of_not_ge hρ.1.2) (lt_of_not_ge hρ.2)) (mult χ)
        (fun ρ hρ => by
          simp only [mem_filter] at hρ
          exact hmr ρ (hW ρ hρ.1.1))
      rwa [habs1] at this
    have hfin := log_bound hq1 ht
    have h4B : 4 * B ≤ 4 * (Real.log (122 * Z) / Real.log 2 + 2) / Real.log (7 / 6) *
        Real.log (q * (t + 2)) := by
      rw [hB]
      have h2 := div_le_div_of_nonneg_right hfin hl76.le
      calc 4 * (Real.log (24 * Z * q * (|t + 1 / 2| + 4) ^ 2) / Real.log (7 / 6))
          ≤ 4 * ((Real.log (122 * Z) / Real.log 2 + 2) * Real.log (q * (t + 2)) /
              Real.log (7 / 6)) := by linarith
        _ = _ := by ring
    linarith

/-! ### Composition with U-1479 -/

/-! ### Vacuity -/

/-- The hypotheses of `mult_le_reflect` are met at a real point of the strip for the character
mod 1: analyticity of `ζ` at `1/2` and finite order of `ζ` at `1/2`. -/
theorem mult_le_reflect_nonvacuous :
    AnalyticAt ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) (1 / 2) ∧
      analyticOrderAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)⁻¹)
        (1 - 1 / 2) ≠ ⊤ ∧ (0 : ℝ) < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1 := by
  have h12 : (1 / 2 : ℂ) ≠ 1 := by norm_num
  refine ⟨L_analyticAt _ h12, L_ord_ne_top _ (Or.inl rfl) (by norm_num), by norm_num, by norm_num⟩

end LeanLab.HardyLittlewood1923.U1482

