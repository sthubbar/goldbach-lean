module

public import LeanLab.PNTPort.ExplicitPsi1.Merom
public import LeanLab.PNTPort.StrongPNT.ResidueCalcOnRectangles

/-!
# The residue sum of `-ζ'/ζ(s) xˢ/(s(s + 1))` over a rectangle

Lab proof, unit U-5320, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
Davenport chapter 17, no cited input. It applies the ported residue theorem
`RectangleIntegral'_eq_sumResiduesIn`, Apache-2.0, PrimeNumberTheoremAnd contributors.

`rect_explicit`: for `x > 0`, `c > 1`, `T > 0`, if ζ has no zero on the border of the rectangle
`[-1/2, c] × [-T, T]`, then
`(1/2πi) ∮ F = x/2 - ζ'(0)/ζ(0) - Σ_ρ m(ρ) x^ρ/(ρ(ρ + 1))`,
the sum over the finitely many zeros ρ of ζ inside, `m(ρ)` the order,
`F(s) = -ζ'/ζ(s) xˢ/(s(s + 1))`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1

open Complex Filter Topology Set

local notation "ζ" => riemannZeta

/-- The integrand of the explicit formula for `ψ₁(x)/x`. -/
noncomputable def F (x : ℝ) (s : ℂ) : ℂ :=
  -(deriv ζ s / ζ s) * ((x : ℂ) ^ s / (s * (s + 1)))

/-- `xˢ/(s(s + 1))` without the factor `1/s`. -/
noncomputable def G1 (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s / (s + 1)

lemma analyticAt_xpow {x : ℝ} (hx : 0 < x) (z : ℂ) : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) z :=
  analyticAt_const.cpow analyticAt_id (ofReal_mem_slitPlane.mpr hx)

lemma analyticAt_kernel {x : ℝ} (hx : 0 < x) {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ -1) :
    AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / (s * (s + 1))) z := by
  apply (analyticAt_xpow hx z).div (analyticAt_id.mul (analyticAt_id.add analyticAt_const))
  exact mul_ne_zero h0 (by
    intro h; apply h1; simp only [Pi.add_apply, id] at h; linear_combination h)

lemma analyticAt_logDeriv {z : ℂ} (h1 : z ≠ 1) (hz : ζ z ≠ 0) :
    AnalyticAt ℂ (fun s => deriv ζ s / ζ s) z :=
  (analyticAt_zeta h1).deriv.div (analyticAt_zeta h1) hz

lemma meromorphicAt_F {x : ℝ} (hx : 0 < x) (z : ℂ) : MeromorphicAt (F x) z := by
  have hz := meromorphicAt_zeta z
  have hk : MeromorphicAt (fun s : ℂ => (x : ℂ) ^ s / (s * (s + 1))) z :=
    (analyticAt_xpow hx z).meromorphicAt.div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)).meromorphicAt
  exact (hz.deriv.div hz).neg.mul hk

lemma analyticAt_F {x : ℝ} (hx : 0 < x) {z : ℂ} (h0 : z ≠ 0) (hm1 : z ≠ -1) (h1 : z ≠ 1)
    (hz : ζ z ≠ 0) : AnalyticAt ℂ (F x) z :=
  (analyticAt_logDeriv h1 hz).neg.mul (analyticAt_kernel hx h0 hm1)

/-- `F` has at most simple poles away from `-1`. -/
lemma order_F_ge {x : ℝ} (hx : 0 < x) {z : ℂ} (hm1 : z ≠ -1) :
    -1 ≤ meromorphicOrderAt (F x) z := by
  have hz := meromorphicAt_zeta z
  rcases eq_or_ne z 0 with rfl | h0
  · -- `F = H · s⁻¹` with `H` analytic at 0
    have hζ0 : ζ 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
    have hH : AnalyticAt ℂ (fun s => -(deriv ζ s / ζ s) * G1 x s) 0 := by
      apply (analyticAt_logDeriv (by norm_num) hζ0).neg.mul
      apply (analyticAt_xpow hx 0).div (analyticAt_id.add analyticAt_const)
      simp
    have hF : F x = (fun s => -(deriv ζ s / ζ s) * G1 x s) * (fun s : ℂ => s)⁻¹ := by
      funext s; simp only [F, G1, Pi.mul_apply, Pi.inv_apply]; field_simp
    have hinv : meromorphicOrderAt (fun s : ℂ => s)⁻¹ 0 = -1 := by
      rw [meromorphicOrderAt_inv]
      show -meromorphicOrderAt id (0 : ℂ) = -1
      rw [meromorphicOrderAt_id]
    rw [hF, meromorphicOrderAt_mul hH.meromorphicAt
      (show MeromorphicAt (fun s : ℂ => s)⁻¹ 0 from analyticAt_id.meromorphicAt.inv), hinv]
    have := hH.meromorphicOrderAt_nonneg
    calc (-1 : WithTop ℤ) = 0 + -1 := by simp
      _ ≤ _ := add_le_add_left this _
  · have hF : F x = (fun s => -logDeriv ζ s) * (fun s : ℂ => (x : ℂ) ^ s / (s * (s + 1))) := by
      funext s; simp [F, logDeriv_apply]
    have hk := analyticAt_kernel hx h0 hm1
    have hL : MeromorphicAt (fun s => -logDeriv ζ s) z := (hz.deriv.div hz).neg
    rw [hF, meromorphicOrderAt_mul hL hk.meromorphicAt]
    have h1 : meromorphicOrderAt (fun s => -logDeriv ζ s) z =
        meromorphicOrderAt (logDeriv ζ) z := (meromorphicOrderAt_neg (f := logDeriv ζ)).symm
    rw [h1]
    calc (-1 : WithTop ℤ) = -1 + 0 := by simp
      _ ≤ _ := add_le_add (order_logDeriv_zeta_ge z) hk.meromorphicOrderAt_nonneg

/-- The residue of `F` at a point `ρ ∉ {0, 1, -1}` is `-m(ρ) x^ρ/(ρ(ρ + 1))`, zero unless
`ζ(ρ) = 0`. -/
lemma residue_F_zero {x : ℝ} (hx : 0 < x) {ρ : ℂ} (h0 : ρ ≠ 0) (hm1 : ρ ≠ -1) (h1 : ρ ≠ 1) :
    residue (F x) ρ = -(analyticOrderNatAt ζ ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ * (ρ + 1))) := by
  apply residue_eq_of_tendsto
  have hk := ((analyticAt_kernel hx h0 hm1).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := {ρ}ᶜ))
  have := ((tendsto_logDeriv_zeta_of_ne_one h1).mul hk).neg
  rw [show -(analyticOrderNatAt ζ ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ * (ρ + 1))) =
    -((analyticOrderNatAt ζ ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ * (ρ + 1)))) by ring]
  refine this.congr (fun s => ?_)
  simp only [F]; ring

/-- The residue of `F` at 1 is `x/2`. -/
lemma residue_F_one {x : ℝ} (hx : 0 < x) : residue (F x) 1 = x / 2 := by
  apply residue_eq_of_tendsto
  have hk := ((analyticAt_kernel hx one_ne_zero (by norm_num)).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
  have := (tendsto_logDeriv_zeta_one.mul hk).neg
  rw [show ((x : ℂ) / 2) = -(-1 * ((x : ℂ) ^ (1 : ℂ) / (1 * (1 + 1)))) by
    rw [cpow_one]; ring]
  refine this.congr (fun s => ?_)
  simp only [F]; ring

/-- The residue of `F` at 0 is `-ζ'(0)/ζ(0)`. -/
lemma residue_F_zero_pt {x : ℝ} (hx : 0 < x) : residue (F x) 0 = -(deriv ζ 0 / ζ 0) := by
  apply residue_eq_of_tendsto
  have hζ0 : ζ 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hH : AnalyticAt ℂ (fun s => -(deriv ζ s / ζ s) * G1 x s) 0 := by
    apply (analyticAt_logDeriv (by norm_num) hζ0).neg.mul
    apply (analyticAt_xpow hx 0).div (analyticAt_id.add analyticAt_const)
    simp
  have ht := (hH.continuousAt.tendsto).mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  have hv : -(deriv ζ 0 / ζ 0) * G1 x 0 = -(deriv ζ 0 / ζ 0) := by
    simp [G1]
  rw [hv] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  simp only [F, G1, sub_zero]
  field_simp

lemma border_cases {c T : ℝ} {z : ℂ}
    (hz : z ∈ RectangleBorder ⟨-1 / 2, -T⟩ ⟨c, T⟩) :
    z.im = -T ∨ z.re = -1 / 2 ∨ z.im = T ∨ z.re = c := by
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hz
  rcases hz with ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩) | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

lemma mem_rect {c T : ℝ} (hc : -1 / 2 ≤ c) (hT : 0 ≤ T) {z : ℂ} :
    z ∈ Rectangle ⟨-1 / 2, -T⟩ ⟨c, T⟩ ↔ (-1 / 2 ≤ z.re ∧ z.re ≤ c) ∧ (-T ≤ z.im ∧ z.im ≤ T) := by
  simp only [Rectangle, mem_reProdIm]
  rw [uIcc_of_le hc, uIcc_of_le (by linarith)]
  simp

/-- The zeros of ζ in the rectangle are finitely many. -/
lemma zeros_rect_finite (c T : ℝ) :
    (Rectangle ⟨-1 / 2, -T⟩ ⟨c, T⟩ ∩ riemannZetaZeros).Finite :=
  IsCompact.inter_riemannZetaZeros_finite (isCompact_uIcc.reProdIm isCompact_uIcc)

/-- **The residue sum over a rectangle.** If ζ has no zero on the border of
`[-1/2, c] × [-T, T]`, `c > 1`, `T > 0`, then `(1/2πi) ∮ F = x/2 - ζ'(0)/ζ(0) - Σ m(ρ) x^ρ/(ρ(ρ+1))`
over the zeros inside. -/
theorem rect_explicit {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T)
    (hbd : ∀ z ∈ RectangleBorder ⟨-1 / 2, -T⟩ ⟨c, T⟩, ζ z ≠ 0) :
    RectangleIntegral' (F x) ⟨-1 / 2, -T⟩ ⟨c, T⟩ =
      x / 2 - deriv ζ 0 / ζ 0 - ∑ ρ ∈ (zeros_rect_finite c T).toFinset,
        (analyticOrderNatAt ζ ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ * (ρ + 1))) := by
  set R := Rectangle (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩ with hRdef
  set Zf := (zeros_rect_finite c T).toFinset with hZf
  have hmem := fun z => mem_rect (c := c) (T := T) (by linarith) hT.le (z := z)
  have hRm1 : ∀ z ∈ R, z ≠ -1 := by
    intro z hz h; rw [hmem] at hz; rw [h] at hz; norm_num at hz
  have h0R : (0 : ℂ) ∈ R := by
    rw [hmem]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
  have h1R : (1 : ℂ) ∈ R := by
    rw [hmem]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
  have hζ0 : ζ 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hZfR : ∀ ρ ∈ Zf, ρ ∈ R ∧ ζ ρ = 0 := by
    intro ρ hρ; rw [hZf, Set.Finite.mem_toFinset] at hρ; exact ⟨hρ.1, hρ.2⟩
  -- analytic away from `0`, `1` and the zeros
  have hgood : ∀ z ∈ R, z ≠ 0 → z ≠ 1 → ζ z ≠ 0 → 0 ≤ meromorphicOrderAt (F x) z :=
    fun z hz h0 h1 hζ => (analyticAt_F hx h0 (hRm1 z hz) h1 hζ).meromorphicOrderAt_nonneg
  have hbR : RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩ ⊆ R := rectangleBorder_subset_rectangle _ _
  have hP : ∀ z ∈ R, meromorphicOrderAt (F x) z < 0 → z ∈ (insert 0 (insert 1 Zf) : Finset ℂ) := by
    intro z hz hneg
    by_contra hns
    simp only [Finset.mem_insert, not_or] at hns
    obtain ⟨h0, h1, hZ⟩ := hns
    have hζ : ζ z ≠ 0 := by
      intro h; apply hZ; rw [hZf, Set.Finite.mem_toFinset]; exact ⟨hz, h⟩
    exact absurd (hgood z hz h0 h1 hζ) (not_le.mpr hneg)
  have hres := RectangleIntegral'_eq_sumResiduesIn (f := F x)
    (z := ⟨-1 / 2, -T⟩) (w := ⟨c, T⟩) (by simp; linarith) (by simp; linarith)
    (fun z _ => meromorphicAt_F hx z)
    (by
      rw [Set.disjoint_left]
      intro z hz hneg
      simp only [mem_ofPred_eq] at hneg
      have hzR := hbR hz
      rcases border_cases hz with h | h | h | h
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; linarith)
          (by intro e; rw [e] at h; simp at h; linarith) (hbd z hz)) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; norm_num at h)
          (by intro e; rw [e] at h; simp at h; linarith) (hbd z hz)) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; linarith)
          (by intro e; rw [e] at h; simp at h; linarith) (hbd z hz)) (not_le.mpr hneg)
      · exact absurd (hgood z hzR (by intro e; rw [e] at h; simp at h; linarith)
          (by intro e; rw [e] at h; simp at h; linarith) (hbd z hz)) (not_le.mpr hneg))
    (by
      apply (insert 0 (insert 1 Zf) : Finset ℂ).finite_toSet.subset
      intro z ⟨hz, hneg⟩
      exact hP z hz hneg)
    (fun z hz => order_F_ge hx (hRm1 z hz))
  rw [hres]
  have hS : R ∩ {z | meromorphicOrderAt (F x) z < 0} =
      ((insert 0 (insert 1 Zf) : Finset ℂ) : Set ℂ) ∩ {z | meromorphicOrderAt (F x) z < 0} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hz, hneg⟩; exact ⟨hP z hz hneg, hneg⟩
    · rintro ⟨hz, hneg⟩
      refine ⟨?_, hneg⟩
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact h0R
      · exact h1R
      · exact (hZfR z hz).1
  rw [sumResiduesIn_inter_eq_of_set_eq hS (fun z _ hz =>
    residue_eq_zero_of_not_pole_of_meromorphicAt (meromorphicAt_F hx z) (not_lt.mp hz))]
  rw [sumResiduesIn, Finset.tsum_subtype' (insert 0 (insert 1 Zf)) (fun z => residue (F x) z)]
  have h1Z : (1 : ℂ) ∉ Zf := fun h => riemannZeta_one_ne_zero (hZfR 1 h).2
  have h0Z : (0 : ℂ) ∉ insert 1 Zf := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨zero_ne_one, fun h => hζ0 (hZfR 0 h).2⟩
  rw [Finset.sum_insert h0Z, Finset.sum_insert h1Z, residue_F_zero_pt hx, residue_F_one hx]
  have hsum : ∑ ρ ∈ Zf, residue (F x) ρ =
      ∑ ρ ∈ Zf, -((analyticOrderNatAt ζ ρ : ℂ) * ((x : ℂ) ^ ρ / (ρ * (ρ + 1)))) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    obtain ⟨hρR, hρ0⟩ := hZfR ρ hρ
    have hρne0 : ρ ≠ 0 := by rintro rfl; exact hζ0 hρ0
    have hρne1 : ρ ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hρ0
    rw [residue_F_zero hx hρne0 (hRm1 ρ hρR) hρne1]
    ring
  rw [hsum, Finset.sum_neg_distrib]
  ring

end LeanLab.PNTPort.ExplicitPsi1

