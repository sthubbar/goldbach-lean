module

public import LeanLab.Linnik.U1412Display53
public import LeanLab.Linnik.U1420Cover
public import LeanLab.Linnik.U1420LogCosh
public import LeanLab.Linnik.U1420Lemma51

/-!
Li-Liu, arXiv 2610.15784, Section 5, displays (44) and (46), read by WebFetch on
arxiv.org/html/2610.15784, 2026-10-21.

Paper: w_{ξ,η}(t) = ξ Re e(t) + η Im e(t), z_L(α) = x + iy;
(44) (1/L) ∑_{ν=1}^{L} w_{ξ,η}(2^ν α)² - V_{ξ,η}(x,y) = (1/(2L)) Re((ξ - iη)² (e(2^{L+1}α) - e(2α)));
concavity of u ↦ log cosh √u with derivative in [0, 1/2] gives
  L Φ_{ξ,η}(z_L(α)) ≤ ∑_{ν=1}^{L} [w(2^ν α) - log cosh w(2^ν α)] + (ξ² + η²)/2,
and Lemma 5.1 gives (46) ∫_0^1 exp(L Φ_{ξ,η}(z_L(α))) dα ≤ exp((ξ² + η²)/2).

Here: `display44`, the identity (44) exactly; `sum_sq_le`, its consequence
∑ w² ≤ L V + ξ² + η²; `V_nonneg` on the closed unit disc; `pointwise46`, the displayed
inequality before (46), by Jensen for the concave g of `U1420LogCosh` and g(m) ≤ g(V) + δ/2;
`moment46`, display (46), that is `U1412Display53.Moment46`, PROVED unconditional;
`prop52_unconditional`, Proposition 5.2, display (53), PROVED unconditional.

Unit U-1420, PC run 20261021T1303Z-13145. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1420Moment46

open Set Real Finset MeasureTheory
open LeanLab.Linnik.U1412Display53 LeanLab.Linnik.U1420LogCosh

lemma eC_add (s t : ℝ) : eC (s + t) = eC s * eC t := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma eC_one : eC 1 = 1 := by
  unfold eC; push_cast; rw [mul_one]; exact Complex.exp_two_pi_mul_I

lemma eC_half : eC (1 / 2) = -1 := by
  unfold eC
  rw [show 2 * (π : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ) = π * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

lemma re_sq_add_im_sq (t : ℝ) : (eC t).re ^ 2 + (eC t).im ^ 2 = 1 := by
  have := norm_eC t
  rw [← U1420Cover.sq_norm_eq, this, one_pow]

/-- `w_{ξ,η}(t) = ξ Re e(t) + η Im e(t)`. -/
noncomputable def wf (ξ η t : ℝ) : ℝ := ξ * (eC t).re + η * (eC t).im

lemma continuous_wf (ξ η : ℝ) : Continuous (wf ξ η) := by
  unfold wf
  have h1 := Complex.continuous_re.comp continuous_eC
  have h2 := Complex.continuous_im.comp continuous_eC
  exact (continuous_const.mul h1).add (continuous_const.mul h2)

lemma wf_periodic (ξ η : ℝ) : Function.Periodic (wf ξ η) 1 := by
  intro t; unfold wf; rw [eC_add, eC_one, mul_one]

lemma wf_anti (ξ η t : ℝ) : wf ξ η (t + 1 / 2) = -wf ξ η t := by
  unfold wf; rw [eC_add, eC_half]; simp; ring

/-- `w(t)² = (ξ² + η²)/2 + ((ξ² - η²)/2) Re e(2t) + ξη Im e(2t)`. -/
lemma wf_sq (ξ η t : ℝ) :
    wf ξ η t ^ 2 = (ξ ^ 2 + η ^ 2) / 2 + (ξ ^ 2 - η ^ 2) / 2 * (eC (2 * t)).re +
      ξ * η * (eC (2 * t)).im := by
  have h2 : eC (2 * t) = eC t * eC t := by rw [← eC_add]; ring_nf
  rw [h2, Complex.mul_re, Complex.mul_im]
  unfold wf
  linear_combination ((ξ ^ 2 + η ^ 2) / 2) * re_sq_add_im_sq t

lemma sum_shift (f : ℕ → ℂ) (L : ℕ) :
    ∑ ν ∈ Icc 1 L, f (ν + 1) = ∑ ν ∈ Icc 1 L, f ν - f 1 + f (L + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    ring

/-- The remainder `R = e(2^{L+1}α) - e(2α)` of (44). -/
noncomputable def R44 (L : ℕ) (α : ℝ) : ℂ := eC (2 ^ (L + 1) * α) - eC (2 * α)

lemma norm_R44_le (L : ℕ) (α : ℝ) : (R44 L α).re ^ 2 + (R44 L α).im ^ 2 ≤ 4 := by
  rw [← U1420Cover.sq_norm_eq]
  have : ‖R44 L α‖ ≤ 2 := by
    unfold R44
    refine (norm_sub_le _ _).trans ?_
    rw [norm_eC, norm_eC]; norm_num
  nlinarith [norm_nonneg (R44 L α)]

/-- (44), multiplied out: `∑ w(2^ν α)² = L V(x,y) + ((ξ²-η²)/2) Re R + ξη Im R`. -/
theorem sum_wf_sq (ξ η : ℝ) {L : ℕ} (hL : 1 ≤ L) (α : ℝ) :
    ∑ ν ∈ Icc 1 L, wf ξ η (2 ^ ν * α) ^ 2 =
      L * V ξ η (zL L α).re (zL L α).im + ((ξ ^ 2 - η ^ 2) / 2 * (R44 L α).re +
        ξ * η * (R44 L α).im) := by
  set f : ℕ → ℂ := fun ν => eC (2 ^ ν * α) with hf
  have hf2 : ∀ ν, eC (2 * (2 ^ ν * α)) = f (ν + 1) := by
    intro ν; simp only [hf]; congr 1; ring
  have hE : ∑ ν ∈ Icc 1 L, f ν = (L : ℂ) * zL L α := by
    have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
    unfold zL; rw [← mul_assoc, mul_one_div_cancel hL0, one_mul]
  have hS : ∑ ν ∈ Icc 1 L, f (ν + 1) = (L : ℂ) * zL L α + R44 L α := by
    rw [sum_shift, hE]; simp only [hf, R44, pow_one]; ring
  simp only [wf_sq, hf2]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Complex.re_sum, ← Complex.im_sum, hS]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Complex.add_re, Complex.add_im]
  have hre : ((L : ℂ) * zL L α).re = L * (zL L α).re := by simp
  have him : ((L : ℂ) * zL L α).im = L * (zL L α).im := by simp
  rw [hre, him]
  unfold V
  push_cast [Nat.add_sub_cancel]
  ring

/-- **Display (44), PROVED**, exactly as in the paper. -/
theorem display44 (ξ η : ℝ) {L : ℕ} (hL : 1 ≤ L) (α : ℝ) :
    (1 / (L : ℝ)) * ∑ ν ∈ Icc 1 L, wf ξ η (2 ^ ν * α) ^ 2 - V ξ η (zL L α).re (zL L α).im =
      1 / (2 * L) * (((ξ : ℂ) - η * Complex.I) ^ 2 *
        (eC (2 ^ (L + 1) * α) - eC (2 * α))).re := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  rw [sum_wf_sq ξ η hL α]
  have : (((ξ : ℂ) - η * Complex.I) ^ 2 * (eC (2 ^ (L + 1) * α) - eC (2 * α))).re =
      (ξ ^ 2 - η ^ 2) * (R44 L α).re + 2 * ξ * η * (R44 L α).im := by
    unfold R44
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [this]
  field_simp
  ring

/-- From (44): `∑ w(2^ν α)² ≤ L V(x,y) + ξ² + η²`. -/
theorem sum_sq_le (ξ η : ℝ) {L : ℕ} (hL : 1 ≤ L) (α : ℝ) :
    ∑ ν ∈ Icc 1 L, wf ξ η (2 ^ ν * α) ^ 2 ≤
      L * V ξ η (zL L α).re (zL L α).im + (ξ ^ 2 + η ^ 2) := by
  rw [sum_wf_sq ξ η hL α]
  set p := (R44 L α).re
  set q := (R44 L α).im
  set A := (ξ ^ 2 - η ^ 2) / 2
  set B := ξ * η
  have hR := norm_R44_le L α
  have hAB : A ^ 2 + B ^ 2 = ((ξ ^ 2 + η ^ 2) / 2) ^ 2 := by simp only [A, B]; ring
  have hcs : (A * p + B * q) ^ 2 ≤ (ξ ^ 2 + η ^ 2) ^ 2 := by
    have h1 : (A * p + B * q) ^ 2 ≤ (A ^ 2 + B ^ 2) * (p ^ 2 + q ^ 2) := by
      nlinarith [sq_nonneg (A * q - B * p)]
    have h2 : (A ^ 2 + B ^ 2) * (p ^ 2 + q ^ 2) ≤ (A ^ 2 + B ^ 2) * 4 :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    rw [hAB] at h2
    nlinarith
  have := (abs_le_of_sq_le_sq' hcs (by positivity)).2
  linarith

/-- `V_{ξ,η}(x,y) ≥ 0` on the closed unit disc. -/
theorem V_nonneg (ξ η : ℝ) {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : 0 ≤ V ξ η x y := by
  unfold V
  have hx : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
  rcases eq_or_lt_of_le hx with hx | hx
  · have hy : y = 0 := by subst hx; nlinarith [sq_nonneg y]
    subst hy; rw [← hx]; nlinarith [sq_nonneg η]
  · have hpos : 0 < 1 + x := by linarith
    have key : (1 + x) * ((1 + x) * ξ ^ 2 + 2 * y * ξ * η + (1 - x) * η ^ 2) =
        ((1 + x) * ξ + y * η) ^ 2 + (1 - x ^ 2 - y ^ 2) * η ^ 2 := by ring
    have : 0 ≤ (1 + x) * ((1 + x) * ξ ^ 2 + 2 * y * ξ * η + (1 - x) * η ^ 2) := by
      rw [key]; nlinarith [sq_nonneg ((1 + x) * ξ + y * η), sq_nonneg η]
    have := (mul_nonneg_iff_of_pos_left hpos).1 this
    linarith

/-- `∑ w(2^ν α) = L (ξx + ηy)`. -/
lemma sum_wf (ξ η : ℝ) {L : ℕ} (hL : 1 ≤ L) (α : ℝ) :
    ∑ ν ∈ Icc 1 L, wf ξ η (2 ^ ν * α) = L * (ξ * (zL L α).re + η * (zL L α).im) := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have hE : ∑ ν ∈ Icc 1 L, eC (2 ^ ν * α) = (L : ℂ) * zL L α := by
    unfold zL; rw [← mul_assoc, mul_one_div_cancel hL0, one_mul]
  unfold wf
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum,
    ← Complex.im_sum, hE]
  simp
  ring

/-- **The inequality before (46), PROVED**:
`L Φ_{ξ,η}(z_L(α)) ≤ ∑_{ν=1}^{L} [w(2^ν α) - log cosh w(2^ν α)] + (ξ² + η²)/2`. -/
theorem pointwise46 (ξ η : ℝ) {L : ℕ} (hL : 1 ≤ L) (α : ℝ) :
    L * Phi ξ η (zL L α) ≤
      ∑ ν ∈ Icc 1 L, (wf ξ η (2 ^ ν * α) - Real.log (Real.cosh (wf ξ η (2 ^ ν * α)))) +
        (ξ ^ 2 + η ^ 2) / 2 := by
  set x := (zL L α).re
  set y := (zL L α).im
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hxy : x ^ 2 + y ^ 2 ≤ 1 := by
    rw [← U1420Cover.sq_norm_eq]
    have := norm_zL_le hL α
    nlinarith [norm_nonneg (zL L α)]
  have hV0 := V_nonneg ξ η hxy
  set p : ℕ → ℝ := fun ν => wf ξ η (2 ^ ν * α) ^ 2 with hp
  set m : ℝ := ∑ ν ∈ Icc 1 L, (1 / (L : ℝ)) • p ν with hm
  have hw1 : ∑ ν ∈ Icc 1 L, (1 / (L : ℝ)) = 1 := by
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    field_simp
  have hJ := concaveOn_g.le_map_sum (t := Icc 1 L) (w := fun _ => 1 / (L : ℝ)) (p := p)
    (fun _ _ => by positivity) hw1 (fun ν _ => mem_Ici.2 (sq_nonneg _))
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum] at hJ
  have hm0 : 0 ≤ m := by
    simp only [hm, smul_eq_mul]
    exact Finset.sum_nonneg fun ν _ => mul_nonneg (by positivity) (sq_nonneg _)
  have hmV : m - V ξ η x y ≤ (ξ ^ 2 + η ^ 2) / L := by
    have h := sum_sq_le ξ η hL α
    have : m = (1 / (L : ℝ)) * ∑ ν ∈ Icc 1 L, p ν := by
      simp only [hm, smul_eq_mul, Finset.mul_sum]
    rw [this]
    rw [show (1 / (L : ℝ)) * ∑ ν ∈ Icc 1 L, p ν - V ξ η x y =
      (∑ ν ∈ Icc 1 L, p ν - L * V ξ η x y) / L by field_simp]
    exact div_le_div_of_nonneg_right (by simp only [hp]; linarith) hLpos.le
  have hg := g_le_of_le hm0 hV0 (by positivity) hmV
  have hJ' : ∑ ν ∈ Icc 1 L, g (p ν) ≤ L * g m := by
    have : (1 / (L : ℝ)) * ∑ ν ∈ Icc 1 L, g (p ν) ≤ g m := by
      simpa [hm, smul_eq_mul] using hJ
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hLpos] at this
    linarith
  have hlc : ∑ ν ∈ Icc 1 L, Real.log (Real.cosh (wf ξ η (2 ^ ν * α))) =
      ∑ ν ∈ Icc 1 L, g (p ν) := by
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [log_cosh_eq_g]
  have hPhi : Phi ξ η (zL L α) = ξ * x + η * y - g (V ξ η x y) := rfl
  rw [Finset.sum_sub_distrib, sum_wf ξ η hL α, hlc, hPhi]
  have : (L : ℝ) * g m ≤ L * g (V ξ η x y) + (ξ ^ 2 + η ^ 2) / 2 := by
    have := mul_le_mul_of_nonneg_left hg hLpos.le
    rw [show (L : ℝ) * (g (V ξ η x y) + 1 / 2 * ((ξ ^ 2 + η ^ 2) / L)) =
      L * g (V ξ η x y) + (ξ ^ 2 + η ^ 2) / 2 by field_simp] at this
    exact this
  nlinarith

lemma continuous_sum46 (ξ η : ℝ) (L : ℕ) : Continuous fun α : ℝ =>
    Real.exp (∑ ν ∈ Icc 1 L, (wf ξ η (2 ^ ν * α) - Real.log (Real.cosh (wf ξ η (2 ^ ν * α))))) := by
  refine Real.continuous_exp.comp (continuous_finsetSum _ fun ν _ => ?_)
  have hw : Continuous fun α : ℝ => wf ξ η (2 ^ ν * α) :=
    (continuous_wf ξ η).comp (continuous_const.mul continuous_id)
  exact hw.sub ((Real.continuous_cosh.comp hw).log fun _ => (Real.cosh_pos _).ne')

/-- **Display (46), PROVED unconditional**: `U1412Display53.Moment46` holds. -/
theorem moment46 : Moment46 := by
  intro ξ η L hL
  set c := (ξ ^ 2 + η ^ 2) / 2 with hc
  set G : ℝ → ℝ := fun α => Real.exp (∑ ν ∈ Icc 1 L,
    (wf ξ η (2 ^ ν * α) - Real.log (Real.cosh (wf ξ η (2 ^ ν * α))))) with hG
  have hGc : Continuous G := continuous_sum46 ξ η L
  have hFc : Continuous fun α => Real.exp (L * Phi ξ η (zL L α)) :=
    Real.continuous_exp.comp (continuous_const.mul ((continuous_Phi _ _).comp (continuous_zL L)))
  have hpt : ∀ α, Real.exp (L * Phi ξ η (zL L α)) ≤ Real.exp c * G α := by
    intro α
    rw [hG, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [pointwise46 ξ η hL α, hc])
  have hG1 : ∫ α in Icc (0 : ℝ) 1, G α = 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    exact U1420Lemma51.lemma51 (continuous_wf ξ η) (wf_periodic ξ η) (wf_anti ξ η) L
  calc ∫ α in Icc (0 : ℝ) 1, Real.exp (L * Phi ξ η (zL L α))
      ≤ ∫ α in Icc (0 : ℝ) 1, Real.exp c * G α :=
        integral_mono hFc.integrableOn_Icc (hGc.integrableOn_Icc.const_mul _) hpt
    _ = Real.exp c := by rw [integral_const_mul, hG1, mul_one]

/-- **Proposition 5.2, display (53), PROVED unconditional.** For `0 < λ < 1` and
`ρ < I(λ)` there is `C ≥ 0` with `meas {α ∈ [0,1] : z_L(α) ∉ D_λ} ≤ C e^{-ρL}` for all `L ≥ 1`. -/
theorem prop52_unconditional {l ρ : ℝ} (h0 : 0 < l) (h1 : l < 1) (hρ : ρ < U1420Cover.Il l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
      (volume.restrict (Icc (0 : ℝ) 1) {α | zL L α ∉ Dl l}).toReal ≤ C * Real.exp (-ρ * L) :=
  U1420Cover.prop52_of_moment46 moment46 h0 h1 hρ

/-- Vacuity instance: `λ = 1/2`, `ρ = I(1/2)/2 > 0`. -/
theorem prop52_instance :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
      (volume.restrict (Icc (0 : ℝ) 1) {α | zL L α ∉ Dl (1 / 2)}).toReal ≤
        C * Real.exp (-(U1420Cover.Il (1 / 2) / 2) * L) :=
  prop52_unconditional (by norm_num) (by norm_num) (by linarith [U1420Cover.Il_half_pos])

end LeanLab.Linnik.U1420Moment46
