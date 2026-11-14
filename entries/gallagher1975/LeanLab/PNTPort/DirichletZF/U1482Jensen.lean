module

public import LeanLab.PNTPort.DirichletZF.LogDeriv
public import Mathlib.Analysis.Complex.JensenFormula

/-!
AI-written Lean code, Claude, 2026-10-22, PC run 20261022T1302Z-31860, unit U-1482.

# Zeros of `L(s, χ)` and of `ζ` near `3/2 + iτ` right of the critical line, by Jensen

Known mathematics, Davenport ch. 15 and 16, no cited input.

* `jensen_count`: Mathlib's Jensen inequality `AnalyticOnNhd.sum_divisor_le`, restated for finsets
  and `analyticOrderNatAt`: for `f` analytic on the closed disc of radius `R` about `c`,
  `f c ≠ 0`, `‖f‖ ≤ M` on the circle, `1 ≤ M`, `0 < r < R`, the zeros in the disc of radius `r`
  are finite and, with multiplicity, at most `log (M / ‖f c‖) / log (R / r)`.
* `mem_ball_of_window`: a point with `1/2 ≤ Re ρ < 1` and `|Im ρ - τ| ≤ 1/2` lies within `6/5`
  of `3/2 + iτ`.
* `sphere_re_norm`: the circle of radius `7/5` about `3/2 + iτ` lies in `Re z ≥ 1/10`,
  `‖z‖ ≤ |τ| + 3`.
* `rw_count_L`: `χ ≠ 1`, the zeros with `1/2 ≤ β < 1`, `|γ - τ| ≤ 1/2` are finite and number at
  most `log (24 Z N (|τ| + 4)²) / log (7/6)`, by Jensen with the growth bound of Growth.lean and
  the lower bound `‖L(3/2 + iτ)‖ ≥ 1/Z` of LogDeriv.lean.
* `rw_count_zeta`: the same for `ζ` through `(s - 1) ζ(s)`, bound `log (24 Z (|τ| + 4)²)/log (7/6)`.
-/

@[expose] public section

namespace LeanLab.PNTPort.DirichletZF.U1482

open Complex Set Filter Metric Topology MeasureTheory
open LeanLab.PNTPort.DirichletZF (Z Z_pos norm_LFunction_ge norm_LFunction_le)

/-! ### Jensen's inequality for finsets -/

/-- **Jensen count.** -/
theorem jensen_count {f : ℂ → ℂ} {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    {u | u ∈ closedBall c r ∧ f u = 0}.Finite ∧
      ∀ s : Finset ℂ, (∀ u ∈ s, u ∈ closedBall c r) →
        ∑ u ∈ s, (analyticOrderNatAt f u : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log (R / r) := by
  classical
  have hR : 0 < R := hr.trans hrR
  have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (M := M) (f := f)
    (by rw [abs_of_pos hr]; exact hr) (by rw [abs_of_pos hr, abs_of_pos hR]; exact hrR) hM
    (by rw [abs_of_pos hR]; exact hf) hc (by rw [abs_of_pos hR]; exact hb)
  rw [abs_of_pos hr] at hJ
  set D := MeromorphicOn.divisor f (closedBall c r) with hDdef
  have hfr : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR.le)
  have hcmem : c ∈ closedBall c R := mem_closedBall_self hR.le
  have hne : ∀ u ∈ closedBall c r, analyticOrderAt f u ≠ ⊤ := by
    intro u hu
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hf (convex_closedBall c R).isPreconnected
      hcmem (closedBall_subset_closedBall hrR.le hu) ?_
    simp [(hf c hcmem).analyticOrderAt_eq_zero.mpr hc]
  have hDu : ∀ u ∈ closedBall c r, D u = (analyticOrderNatAt f u : ℤ) := by
    intro u hu
    rw [hDdef, MeromorphicOn.AnalyticOnNhd.divisor_apply hfr hu, ← Nat.cast_analyticOrderNatAt (hne u hu)]
    simp
  have hfin : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall c r)
  have hsuppball : Function.support D ⊆ closedBall c r := D.supportWithinDomain
  have hsub : {u | u ∈ closedBall c r ∧ f u = 0} ⊆ Function.support D := by
    rintro u ⟨hu, hz⟩
    rw [Function.mem_support, hDu u hu]
    intro h0
    have h0' : analyticOrderNatAt f u = 0 := by exact_mod_cast h0
    have h' : analyticOrderAt f u = 0 := by
      rw [← Nat.cast_analyticOrderNatAt (hne u hu), h0']; simp
    exact ((hfr u hu).analyticOrderAt_eq_zero.mp h') hz
  refine ⟨hfin.subset hsub, fun s hs => ?_⟩
  set T := s ∪ hfin.toFinset with hT
  have hTball : ∀ u ∈ T, u ∈ closedBall c r := by
    intro u hu
    rw [hT, Finset.mem_union] at hu
    rcases hu with hu | hu
    · exact hs u hu
    · exact hsuppball ((Set.Finite.mem_toFinset hfin).mp hu)
  have hsupp : Function.support (fun u => (D u : ℝ)) ⊆ (T : Set ℂ) := by
    intro u hu
    have hu' : D u ≠ 0 := by
      intro h; apply hu; simp [h]
    rw [hT, Finset.coe_union]
    right
    simpa using hu'
  have hfs : ∑ᶠ u, (D u : ℝ) = ∑ u ∈ T, (D u : ℝ) := finsum_eq_sum_of_support_subset _ hsupp
  have hmap : ((∑ᶠ u, D u : ℤ) : ℝ) = ∑ᶠ u, (D u : ℝ) := by
    have := map_finsum (Int.castRingHom ℝ) hfin
    simpa using this
  have hs1 : ∑ u ∈ s, (analyticOrderNatAt f u : ℝ) = ∑ u ∈ s, (D u : ℝ) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [hDu u (hs u hu)]; simp
  have hs2 : ∑ u ∈ s, (D u : ℝ) ≤ ∑ u ∈ T, (D u : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun u hu _ => ?_
    rw [hDu u (hTball u hu)]; simp
  rw [hs1]
  refine hs2.trans ?_
  rw [← hfs, ← hmap]
  exact hJ

/-! ### Geometry of the disc about `3/2 + iτ` -/

/-- The centre `3/2 + iτ`. -/
noncomputable def cen (τ : ℝ) : ℂ := (3 : ℂ) / 2 + I * τ

/-- The right window: zeros of `f` with `1/2 ≤ Re ρ < 1` and `|Im ρ - τ| ≤ 1/2`. -/
def RW (f : ℂ → ℂ) (τ : ℝ) : Set ℂ :=
  {ρ | f ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im - τ| ≤ 1 / 2}

lemma mem_ball_of_window {τ : ℝ} {ρ : ℂ} (h : 1 / 2 ≤ ρ.re) (h' : ρ.re < 1)
    (hi : |ρ.im - τ| ≤ 1 / 2) : ρ ∈ closedBall (cen τ) (6 / 5) := by
  rw [mem_closedBall, dist_eq_norm]
  have hre : (ρ - cen τ).re = ρ.re - 3 / 2 := by simp [cen]
  have him : (ρ - cen τ).im = ρ.im - τ := by simp [cen]
  have hsq : ‖ρ - cen τ‖ ^ 2 = (ρ - cen τ).re ^ 2 + (ρ - cen τ).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hre, him] at hsq
  have h1 : (ρ.im - τ) ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hi; nlinarith
  have h2 : (ρ.re - 3 / 2) ^ 2 ≤ 1 := by nlinarith
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg (ρ - cen τ)]

lemma norm_cen_le (τ : ℝ) : ‖cen τ‖ ≤ 3 / 2 + |τ| := by
  unfold cen
  have h1 : ‖(3 : ℂ) / 2‖ = 3 / 2 := by rw [norm_div]; simp
  have h2 : ‖I * (τ : ℂ)‖ = |τ| := by simp
  calc ‖(3 : ℂ) / 2 + I * τ‖ ≤ ‖(3 : ℂ) / 2‖ + ‖I * (τ : ℂ)‖ := norm_add_le _ _
    _ = 3 / 2 + |τ| := by rw [h1, h2]

lemma sphere_re_norm {τ : ℝ} {z : ℂ} (hz : z ∈ sphere (cen τ) (7 / 5)) :
    1 / 10 ≤ z.re ∧ ‖z‖ ≤ |τ| + 3 := by
  rw [mem_sphere, dist_eq_norm] at hz
  have h1 := Complex.abs_re_le_norm (z - cen τ)
  rw [hz] at h1
  have hre : (z - cen τ).re = z.re - 3 / 2 := by simp [cen]
  rw [hre] at h1
  refine ⟨by linarith [(abs_le.mp h1).1], ?_⟩
  have hc := norm_cen_le τ
  calc ‖z‖ = ‖(z - cen τ) + cen τ‖ := by ring_nf
    _ ≤ ‖z - cen τ‖ + ‖cen τ‖ := norm_add_le _ _
    _ ≤ |τ| + 3 := by rw [hz]; linarith

/-! ### Non-principal characters -/

/-- **Right window count for `L(s, χ)`, `χ ≠ 1`.** -/
theorem rw_count_L {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (τ : ℝ) :
    (RW (DirichletCharacter.LFunction χ) τ).Finite ∧
      ∀ s : Finset ℂ, (∀ ρ ∈ s, ρ ∈ RW (DirichletCharacter.LFunction χ) τ) →
        ∑ ρ ∈ s, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
          Real.log (24 * Z * N * (|τ| + 4) ^ 2) / Real.log (7 / 6) := by
  set f := DirichletCharacter.LFunction χ with hfdef
  have hf : AnalyticOnNhd ℂ f (closedBall (cen τ) (7 / 5)) := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hlow : 1 / Z ≤ ‖f (cen τ)‖ := norm_LFunction_ge χ τ
  have hZ := Z_pos
  have hc : f (cen τ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow
    have : 0 < 1 / Z := by positivity
    linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hτ := abs_nonneg τ
  set M : ℝ := 10 * N * (|τ| + 3) with hMdef
  have hM : 1 ≤ M := by rw [hMdef]; nlinarith
  have hb : ∀ z ∈ sphere (cen τ) (7 / 5), ‖f z‖ ≤ M := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := sphere_re_norm hz
    calc ‖f z‖ ≤ N * ‖z‖ / z.re := norm_LFunction_le hχ (by linarith)
      _ ≤ N * (|τ| + 3) / (1 / 10) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hz2 (Nat.cast_nonneg _))
            (by norm_num) hz1
      _ = M := by rw [hMdef]; ring
  obtain ⟨hfin, hsum⟩ := jensen_count (r := 6 / 5) (R := 7 / 5) (by norm_num) (by norm_num) hM hf
    hc hb
  refine ⟨hfin.subset fun ρ hρ => ⟨mem_ball_of_window hρ.2.1 hρ.2.2.1 hρ.2.2.2, hρ.1⟩,
    fun s hs => ?_⟩
  refine (hsum s fun ρ hρ => mem_ball_of_window (hs ρ hρ).2.1 (hs ρ hρ).2.2.1
    (hs ρ hρ).2.2.2).trans ?_
  have e : (7 / 5 : ℝ) / (6 / 5) = 7 / 6 := by norm_num
  rw [e]
  have hl : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  refine div_le_div_of_nonneg_right ?_ hl.le
  have hfc : 0 < ‖f (cen τ)‖ := norm_pos_iff.mpr hc
  refine Real.log_le_log (by positivity) ?_
  have h1 : M / ‖f (cen τ)‖ ≤ M * Z := by
    rw [div_le_iff₀ hfc]
    have : 1 ≤ Z * ‖f (cen τ)‖ := by
      rw [div_le_iff₀ hZ] at hlow; linarith
    nlinarith
  refine h1.trans ?_
  rw [hMdef]
  nlinarith [mul_nonneg (mul_nonneg hZ.le (by linarith : (0 : ℝ) ≤ N)) hτ]

/-! ### `ζ` through `(s - 1) ζ(s)` -/

local notation "ζ" => riemannZeta

/-- `(s - 1) ζ(s)`, with the value `1` at `s = 1`; the lab's ZetaZeros `gζ`, re-proved here. -/
noncomputable def gZ : ℂ → ℂ := Function.update (fun s => (s - 1) * ζ s) 1 1

lemma gZ_of_ne {s : ℂ} (h : s ≠ 1) : gZ s = (s - 1) * ζ s := by
  simp [gZ, Function.update_of_ne h]

lemma gZ_one : gZ 1 = 1 := by simp [gZ]

lemma gZ_eventuallyEq {s : ℂ} (h : s ≠ 1) : gZ =ᶠ[𝓝 s] fun w => (w - 1) * ζ w := by
  filter_upwards [isOpen_compl_singleton.mem_nhds h] with w hw
  exact gZ_of_ne hw

lemma gZ_analyticAt (s : ℂ) : AnalyticAt ℂ gZ s := by
  rcases eq_or_ne s 1 with rfl | h
  · apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w ≠ 1 := hw
      have hd : DifferentiableAt ℂ (fun w => (w - 1) * ζ w) w :=
        (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hw')
      exact hd.congr_of_eventuallyEq (gZ_eventuallyEq hw')
    · unfold gZ
      rw [continuousAt_update_same]
      exact riemannZeta_residue_one
  · have hA : AnalyticAt ℂ (fun w => (w - 1) * ζ w) s :=
      (analyticAt_id.sub analyticAt_const).mul (analyticAt_riemannZeta h)
    exact hA.congr (gZ_eventuallyEq h).symm

/-- Orders of `gZ` and `ζ` agree off `1`, as elements of `ℕ∞`. -/
lemma ord_gZ_enat {s : ℂ} (h : s ≠ 1) : analyticOrderAt gZ s = analyticOrderAt ζ s := by
  have hev := gZ_eventuallyEq h
  have hz : AnalyticAt ℂ ζ s := analyticAt_riemannZeta h
  have hl : AnalyticAt ℂ (fun w : ℂ => w - 1) s := analyticAt_id.sub analyticAt_const
  rw [analyticOrderAt_congr hev]
  rw [show (fun w : ℂ => (w - 1) * ζ w) = (fun w : ℂ => w - 1) * ζ from rfl,
    analyticOrderAt_mul hl hz]
  rw [show analyticOrderAt (fun w : ℂ => w - 1) s = 0 from
    analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr h)), zero_add]

lemma ord_gZ {s : ℂ} (h : s ≠ 1) : analyticOrderNatAt gZ s = analyticOrderNatAt ζ s := by
  simp only [analyticOrderNatAt, ord_gZ_enat h]

lemma norm_zetaInt_le' {s : ℂ} (hs : 0 < s.re) :
    ‖∫ (u : ℝ) in Ioi 1, (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ 1 / s.re := by
  have domBound {x : ℝ} (hu : x ∈ Ioi 1) : |Int.fract x| * ‖(x : ℂ) ^ (-s - 1)‖
      ≤ x ^ (-s.re - 1) := by
    rw [mem_Ioi] at hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp only [sub_re, neg_re, one_re, Int.abs_fract]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) (Int.fract_lt_one x).le
  have domIntegral : Integrable (fun x : ℝ => x ^ (-s.re - 1)) (volume.restrict (Set.Ioi 1)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hI := integral_Ioi_rpow_of_lt (a := -s.re - 1) (by linarith) one_pos
  simp only [sub_add_cancel, Real.one_rpow, neg_div_neg_eq] at hI
  simp only [Complex.norm_mul, norm_real, Real.norm_eq_abs, ← hI]
  refine integral_mono_ae (domIntegral.mono' (((measurable_fract.abs).mul
    ((Complex.measurable_ofReal.pow_const _).norm)).aestronglyMeasurable) ?_) domIntegral
    (by filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx using domBound hx)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, Real.norm_eq_abs, abs_abs, norm_norm]
  exact domBound hx

lemma norm_gZ_le {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    ‖gZ s‖ ≤ ‖s - 1‖ + 1 + ‖s‖ * ‖s - 1‖ / s.re := by
  rw [gZ_of_ne h1, ZetaAltFormula hs h1, riemannZeta1]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have e : (s - 1) * (1 + 1 / (s - 1) - s * ∫ (u : ℝ) in Ioi 1,
      (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1)) =
      (s - 1) + 1 - s * (s - 1) * ∫ (u : ℝ) in Ioi 1,
      (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    field_simp
  rw [e]
  have hI := norm_zetaInt_le' hs
  calc ‖(s - 1) + 1 - s * (s - 1) * ∫ (u : ℝ) in Ioi 1, (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1)‖
      ≤ ‖(s - 1) + 1‖ + ‖s * (s - 1) * ∫ (u : ℝ) in Ioi 1,
          (↑(Int.fract u) : ℂ) * (u : ℂ) ^ (-s - 1)‖ := norm_sub_le _ _
    _ ≤ (‖s - 1‖ + 1) + ‖s‖ * ‖s - 1‖ * (1 / s.re) := by
        gcongr
        · exact (norm_add_le _ _).trans (by rw [norm_one])
        · rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by ring

lemma cen_ne_one (τ : ℝ) : cen τ ≠ 1 := by
  intro h
  have := congr_arg Complex.re h
  simp [cen] at this
  norm_num at this

/-- `‖ζ(3/2 + iτ)‖ ≥ 1/Z`, from the case `N = 1` of LogDeriv's `norm_LFunction_ge`. -/
lemma norm_zeta_cen_ge (τ : ℝ) : 1 / Z ≤ ‖ζ (cen τ)‖ := by
  have := norm_LFunction_ge (1 : DirichletCharacter ℂ 1) τ
  rw [DirichletCharacter.LFunction_modOne_eq] at this
  exact this

lemma gZ_cen_ne (τ : ℝ) : gZ (cen τ) ≠ 0 := by
  rw [gZ_of_ne (cen_ne_one τ)]
  refine mul_ne_zero (sub_ne_zero.mpr (cen_ne_one τ)) ?_
  intro h
  have hl := norm_zeta_cen_ge τ
  rw [h, norm_zero] at hl
  have := Z_pos
  have : 0 < 1 / Z := by positivity
  linarith

/-- **Right window count for `ζ`.** -/
theorem rw_count_zeta (τ : ℝ) :
    (RW ζ τ).Finite ∧
      ∀ s : Finset ℂ, (∀ ρ ∈ s, ρ ∈ RW ζ τ) →
        ∑ ρ ∈ s, (analyticOrderNatAt ζ ρ : ℝ) ≤
          Real.log (24 * Z * (|τ| + 4) ^ 2) / Real.log (7 / 6) := by
  have hf : AnalyticOnNhd ℂ gZ (closedBall (cen τ) (7 / 5)) := fun z _ => gZ_analyticAt z
  have hZ := Z_pos
  have hc := gZ_cen_ne τ
  have hlow : 1 / (2 * Z) ≤ ‖gZ (cen τ)‖ := by
    rw [gZ_of_ne (cen_ne_one τ), norm_mul]
    have h1 : 1 / 2 ≤ ‖cen τ - 1‖ := by
      have := Complex.abs_re_le_norm (cen τ - 1)
      have e : (cen τ - 1).re = 1 / 2 := by simp [cen]; norm_num
      rw [e] at this
      linarith [le_abs_self (1 / 2 : ℝ)]
    have h2 := norm_zeta_cen_ge τ
    calc 1 / (2 * Z) = (1 / 2) * (1 / Z) := by field_simp
      _ ≤ ‖cen τ - 1‖ * ‖ζ (cen τ)‖ :=
          mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
  have hτ := abs_nonneg τ
  set M : ℝ := 12 * (|τ| + 4) ^ 2 with hMdef
  have hM : 1 ≤ M := by rw [hMdef]; nlinarith
  have hb : ∀ z ∈ sphere (cen τ) (7 / 5), ‖gZ z‖ ≤ M := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := sphere_re_norm hz
    rcases eq_or_ne z 1 with rfl | h1
    · rw [gZ_one, norm_one]; exact hM
    · refine (norm_gZ_le (by linarith) h1).trans ?_
      have hz3 : ‖z - 1‖ ≤ |τ| + 4 := by
        calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ |τ| + 4 := by rw [norm_one]; linarith
      have hq : ‖z‖ * ‖z - 1‖ / z.re ≤ 10 * (|τ| + 4) ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        have h4 : ‖z‖ * ‖z - 1‖ ≤ (|τ| + 4) * (|τ| + 4) :=
          mul_le_mul (by linarith) hz3 (norm_nonneg _) (by linarith)
        nlinarith
      rw [hMdef]; nlinarith
  obtain ⟨hfin, hsum⟩ := jensen_count (r := 6 / 5) (R := 7 / 5) (by norm_num) (by norm_num) hM hf
    hc hb
  have hne1 : ∀ ρ ∈ RW ζ τ, ρ ≠ 1 := by
    intro ρ hρ h; rw [h] at hρ; have := hρ.2.2.1; simp at this
  have hz0 : ∀ ρ ∈ RW ζ τ, gZ ρ = 0 := by
    intro ρ hρ; rw [gZ_of_ne (hne1 ρ hρ), hρ.1, mul_zero]
  refine ⟨hfin.subset fun ρ hρ => ⟨mem_ball_of_window hρ.2.1 hρ.2.2.1 hρ.2.2.2, hz0 ρ hρ⟩,
    fun s hs => ?_⟩
  have hs' : ∑ ρ ∈ s, (analyticOrderNatAt ζ ρ : ℝ) = ∑ ρ ∈ s, (analyticOrderNatAt gZ ρ : ℝ) := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [ord_gZ (hne1 ρ (hs ρ hρ))]
  rw [hs']
  refine (hsum s fun ρ hρ => mem_ball_of_window (hs ρ hρ).2.1 (hs ρ hρ).2.2.1
    (hs ρ hρ).2.2.2).trans ?_
  have e : (7 / 5 : ℝ) / (6 / 5) = 7 / 6 := by norm_num
  rw [e]
  have hl : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  refine div_le_div_of_nonneg_right ?_ hl.le
  have hfc : 0 < ‖gZ (cen τ)‖ := norm_pos_iff.mpr hc
  refine Real.log_le_log (by positivity) ?_
  have h1 : M / ‖gZ (cen τ)‖ ≤ M * (2 * Z) := by
    rw [div_le_iff₀ hfc]
    have : 1 ≤ (2 * Z) * ‖gZ (cen τ)‖ := by
      rw [div_le_iff₀ (by positivity)] at hlow; linarith
    nlinarith
  refine h1.trans (le_of_eq ?_)
  rw [hMdef]; ring

end LeanLab.PNTPort.DirichletZF.U1482

