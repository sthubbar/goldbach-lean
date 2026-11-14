module

public import Mathlib

/-!
Li-Liu, arXiv 2610.15784, Section 5, Proposition 5.2, display (53), the large deviation bound for
the dyadic sum, read by WebFetch on arxiv.org/html/2610.15784, 2026-10-21.

Paper: z_L(α) = (1/L) ∑_{ν=1}^{L} e(2^ν α); (50) r_λ = λ²/2, β_λ = (r_λ + √(r_λ² + 4r_λ))/2;
(51) D_λ = {x + iy : x ≤ β_λ, x² + y² ≤ r_λ/(1 + r_λ - x)}; (45) w_{ξ,η}(t) = ξ Re e(t) + η Im e(t),
V_{ξ,η}(x,y) = ((1+x)ξ² + 2yξη + (1-x)η²)/2, Φ_{ξ,η}(z) = ξx + ηy - log cosh √V_{ξ,η}(x,y);
(46) ∫_0^1 exp(L Φ_{ξ,η}(z_L(α))) dα ≤ exp((ξ² + η²)/2);
Proposition 5.2: for 0 < λ < 1 and 0 < ρ < I(λ), E_λ(L) = {α ∈ [0,1] : z_L(α) ∉ D_λ} has
(53) ∫_{E_λ(L)} dα ≪_{λ,ρ} e^{-ρL}.
The proof: (47) to (49) give, at each z of the unit disc outside D_λ, a pair (ξ, η) with
Φ_{ξ,η}(z) ≥ I(λ) > ρ; compactness gives finitely many pairs (ξ_j, η_j) covering; then
∫_E ≤ e^{-ρL} ∑_j ∫_0^1 exp(L Φ_j(z_L)) ≪ e^{-ρL} by (46).

Here the two analytic inputs are named Props, cited:
* `Moment46`: display (46), the paper's consequence of Lemma 5.1, (43) and (44);
* `CoverInput λ ρ`: the finite cover, from (47) to (49), (52) and compactness.
PROVED unconditional: `norm_zL_le`, `continuous_Phi`, `continuous_zL`; `moment46_zero`, (46) at
ξ = η = 0; `cover_neg`, `CoverInput λ ρ` for ρ < 0, a vacuity instance outside the paper's
range ρ > 0.
CONDITIONAL ON `Moment46` and `CoverInput λ ρ`: `prop52`, display (53) with the explicit
constant C = ∑_j exp((ξ_j² + η_j²)/2), by the Chernoff step of the paper.

Unit U-1412, PC run 20261021T1303Z-13145. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1412Display53

open MeasureTheory Set Real Finset

/-- `e(t) = exp(2πit)`. -/
noncomputable def eC (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * t)

lemma norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  rw [show 2 * π * Complex.I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_eC : Continuous eC := by unfold eC; fun_prop

/-- `z_L(α) = (1/L) ∑_{ν=1}^{L} e(2^ν α)`. -/
noncomputable def zL (L : ℕ) (α : ℝ) : ℂ := (1 / (L : ℂ)) * ∑ ν ∈ Icc 1 L, eC (2 ^ ν * α)

lemma continuous_zL (L : ℕ) : Continuous (zL L) := by
  unfold zL
  refine continuous_const.mul (continuous_finsetSum _ fun ν _ => ?_)
  exact continuous_eC.comp (continuous_const.mul continuous_id)

/-- `|z_L(α)| ≤ 1` for `L ≥ 1`. -/
theorem norm_zL_le {L : ℕ} (hL : 1 ≤ L) (α : ℝ) : ‖zL L α‖ ≤ 1 := by
  unfold zL
  rw [norm_mul]
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have h1 : ‖(1 / (L : ℂ))‖ = 1 / L := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  have h2 : ‖∑ ν ∈ Icc 1 L, eC (2 ^ ν * α)‖ ≤ L := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_eC, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    simp
  rw [h1]
  calc 1 / (L : ℝ) * ‖∑ ν ∈ Icc 1 L, eC (2 ^ ν * α)‖ ≤ 1 / L * L :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 := by field_simp

/-- (50): `r_λ = λ²/2`. -/
noncomputable def rl (l : ℝ) : ℝ := l ^ 2 / 2

/-- (50): `β_λ = (r_λ + √(r_λ² + 4 r_λ))/2`. -/
noncomputable def bl (l : ℝ) : ℝ := (rl l + Real.sqrt (rl l ^ 2 + 4 * rl l)) / 2

/-- (51): the region `D_λ`. -/
def Dl (l : ℝ) : Set ℂ :=
  {z | z.re ≤ bl l ∧ z.re ^ 2 + z.im ^ 2 ≤ rl l / (1 + rl l - z.re)}

/-- (45): `V_{ξ,η}(x, y)`. -/
noncomputable def V (ξ η x y : ℝ) : ℝ := ((1 + x) * ξ ^ 2 + 2 * y * ξ * η + (1 - x) * η ^ 2) / 2

/-- (45): `Φ_{ξ,η}(z) = ξx + ηy - log cosh √V`. -/
noncomputable def Phi (ξ η : ℝ) (z : ℂ) : ℝ :=
  ξ * z.re + η * z.im - Real.log (Real.cosh (Real.sqrt (V ξ η z.re z.im)))

lemma continuous_Phi (ξ η : ℝ) : Continuous (Phi ξ η) := by
  unfold Phi V
  refine (by fun_prop : Continuous fun z : ℂ => ξ * z.re + η * z.im).sub ?_
  refine Continuous.log ?_ (fun z => (Real.cosh_pos _).ne')
  exact Real.continuous_cosh.comp (Real.continuous_sqrt.comp (by fun_prop))

/-- **Display (46), cited.** For real `ξ, η` and `L ≥ 1`,
`∫_0^1 exp(L Φ_{ξ,η}(z_L(α))) dα ≤ exp((ξ² + η²)/2)`. -/
def Moment46 : Prop :=
  ∀ ξ η : ℝ, ∀ L : ℕ, 1 ≤ L →
    ∫ α in Icc (0 : ℝ) 1, Real.exp (L * Phi ξ η (zL L α)) ≤ Real.exp ((ξ ^ 2 + η ^ 2) / 2)

/-- **The finite cover of the proof of Proposition 5.2, cited.** Finitely many pairs
`(ξ_j, η_j)` such that every `z` of the closed unit disc outside `D_λ` has `Φ_{ξ_j,η_j}(z) > ρ`
for some `j`. -/
def CoverInput (l ρ : ℝ) : Prop :=
  ∃ S : Finset (ℝ × ℝ), ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ Dl l → ∃ p ∈ S, ρ < Phi p.1 p.2 z

/-- **Proposition 5.2, display (53), CONDITIONAL ON `Moment46` and `CoverInput λ ρ`.**
There is `C ≥ 0` with `meas {α ∈ [0,1] : z_L(α) ∉ D_λ} ≤ C e^{-ρL}` for every `L ≥ 1`. -/
theorem prop52 {l ρ : ℝ} (hM : Moment46) (hC : CoverInput l ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
      (volume.restrict (Icc (0 : ℝ) 1) {α | zL L α ∉ Dl l}).toReal ≤ C * Real.exp (-ρ * L) := by
  obtain ⟨S, hS⟩ := hC
  set μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hμ
  have hfin : ∀ s, μ s ≠ ⊤ := by
    intro s
    refine ne_top_of_le_ne_top ?_ (measure_mono (subset_univ s))
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  refine ⟨∑ p ∈ S, Real.exp ((p.1 ^ 2 + p.2 ^ 2) / 2),
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le, fun L hL => ?_⟩
  set f : ℝ × ℝ → ℝ → ℝ := fun p α => Real.exp (L * Phi p.1 p.2 (zL L α)) with hf
  have hfc : ∀ p, Continuous (f p) := fun p =>
    Real.continuous_exp.comp (continuous_const.mul ((continuous_Phi _ _).comp (continuous_zL L)))
  set A : ℝ × ℝ → Set ℝ := fun p => {α | Real.exp (ρ * L) ≤ f p α} with hA
  have hsub : {α | zL L α ∉ Dl l} ⊆ ⋃ p ∈ S, A p := by
    intro α hα
    obtain ⟨p, hp, hρ⟩ := hS (zL L α) (norm_zL_le hL α) hα
    refine mem_iUnion₂.2 ⟨p, hp, ?_⟩
    show Real.exp (ρ * L) ≤ Real.exp (L * Phi p.1 p.2 (zL L α))
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
    exact Real.exp_le_exp.2 (by nlinarith)
  have hmeas : μ {α | zL L α ∉ Dl l} ≤ ∑ p ∈ S, μ (A p) :=
    (measure_mono hsub).trans (measure_biUnion_finset_le S A)
  have hone : ∀ p ∈ S, (μ (A p)).toReal ≤ Real.exp ((p.1 ^ 2 + p.2 ^ 2) / 2) * Real.exp (-ρ * L) := by
    intro p _
    have hint : Integrable (f p) μ := (hfc p).integrableOn_Icc
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ)
      (ae_of_all _ fun α => (Real.exp_pos _).le) hint (Real.exp (ρ * L))
    have hmom := hM p.1 p.2 L hL
    have h1 : Real.exp (ρ * L) * (μ (A p)).toReal ≤ Real.exp ((p.1 ^ 2 + p.2 ^ 2) / 2) :=
      hmk.trans hmom
    have he : Real.exp (-ρ * L) * Real.exp (ρ * L) = 1 := by
      rw [← Real.exp_add]; simp
    calc (μ (A p)).toReal = Real.exp (-ρ * L) * (Real.exp (ρ * L) * (μ (A p)).toReal) := by
          rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (-ρ * L) * Real.exp ((p.1 ^ 2 + p.2 ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = _ := by ring
  calc (μ {α | zL L α ∉ Dl l}).toReal ≤ (∑ p ∈ S, μ (A p)).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun p _ => hfin _) hmeas
    _ = ∑ p ∈ S, (μ (A p)).toReal := ENNReal.toReal_sum fun p _ => hfin _
    _ ≤ ∑ p ∈ S, Real.exp ((p.1 ^ 2 + p.2 ^ 2) / 2) * Real.exp (-ρ * L) :=
        Finset.sum_le_sum hone
    _ = _ := by rw [Finset.sum_mul]

/-- Vacuity of `Moment46` at `ξ = η = 0`: `Φ_{0,0} = 0` and both sides are 1. -/
theorem moment46_zero (L : ℕ) :
    ∫ α in Icc (0 : ℝ) 1, Real.exp (L * Phi 0 0 (zL L α)) ≤ Real.exp ((0 ^ 2 + 0 ^ 2) / 2) := by
  have h : ∀ z : ℂ, Phi 0 0 z = 0 := by
    intro z; simp [Phi, V]
  simp only [h, mul_zero, Real.exp_zero]
  simp

/-- Vacuity of `CoverInput`: for `ρ < 0` the single pair `(0, 0)` covers. Outside the paper's
range `ρ > 0`; it shows only that the Prop is satisfiable. -/
theorem cover_neg (l : ℝ) {ρ : ℝ} (hρ : ρ < 0) : CoverInput l ρ := by
  refine ⟨{(0, 0)}, fun z _ _ => ⟨(0, 0), Finset.mem_singleton_self _, ?_⟩⟩
  simp [Phi, V, hρ]

end LeanLab.Linnik.U1412Display53
