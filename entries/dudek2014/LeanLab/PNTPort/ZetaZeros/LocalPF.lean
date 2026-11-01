module

public import LeanLab.PNTPort.ZetaZeros.Count

/-!
# The local partial fraction of `ζ'/ζ` near height `t`

Lab proof, unit U-5263, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics,
Davenport ch. 15 (2), no cited input; from the ported Borel-Carathéodory bound `FinalBound`,
Apache-2.0, PrimeNumberTheoremAnd, applied to `fz` of Count.lean.

`logDeriv_local`: an absolute `C` such that for `|t| ≥ 3` and every `s` with
`‖s - (3/2 + it)‖ ≤ 1` and `ζ s ≠ 0`,
`‖ζ'(s)/ζ(s) - Σ_{ρ} m(ρ)/(s - ρ)‖ ≤ C log |t|`, the sum over the zeros `ρ` of `ζ` with
`‖ρ - (3/2 + it)‖ ≤ 27/25`, with multiplicity `m(ρ)`. On the line `Im s = t` this covers
`1/2 ≤ Re s ≤ 5/2`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric Topology

local notation "ζ" => riemannZeta

/-- The zeros of `ζ` within `27/25` of `3/2 + it`. -/
def Zloc (t : ℝ) : Set ℂ := {ρ : ℂ | ζ ρ = 0 ∧ ‖ρ - cen t‖ ≤ 27 / 25}

lemma one_lt_Bz (t : ℝ) : 1 < Bz t := by
  have hm := m0_pos
  have hm1 : m0 < 1 := by
    unfold m0
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))]
    have := norm_zeta_strict_mono_ofReal (a := 3) (b := 3 / 2) (by norm_num) (by norm_num)
    simpa using this
  unfold Bz
  rw [one_lt_div hm]
  have := abs_nonneg t
  linarith

lemma affInv_aff (t : ℝ) (z : ℂ) : affInv t (aff t z) = z := by
  unfold aff affInv; ring

lemma norm_affInv (t : ℝ) (ρ : ℂ) : ‖affInv t ρ‖ = 2 / 3 * ‖ρ - cen t‖ := by
  unfold affInv; rw [norm_mul]; norm_num; ring

lemma mem_zeros_iff {t : ℝ} (z : ℂ) :
    z ∈ SetOfZeros (18 / 25) (fz t) ↔ aff t z ∈ Zloc t := by
  have hc := zeta_cen_ne t
  have hn : ‖aff t z - cen t‖ = 3 / 2 * ‖z‖ := by
    unfold aff; rw [add_sub_cancel_left, norm_mul]; norm_num
  simp only [SetOfZeros, Zloc, Set.mem_setOf_eq, fz, div_eq_zero_iff, hc, or_false, hn]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h2, h1⟩; exact ⟨by linarith, h2⟩

lemma deriv_fz {t : ℝ} (ht : 3 ≤ |t|) {z : ℂ} (hz : ‖z‖ < 4 / 3) :
    deriv (fz t) z = 3 / 2 * deriv ζ (aff t z) / ζ (cen t) := by
  have hζ : DifferentiableAt ℂ ζ (aff t z) := differentiableAt_riemannZeta (aff_ne_one ht hz)
  have haff : HasDerivAt (aff t) (3 / 2) z := by
    unfold aff
    simpa using ((hasDerivAt_id z).const_mul (3 / 2 : ℂ)).const_add (cen t)
  have h := (hζ.hasDerivAt.comp z haff).div_const (ζ (cen t))
  unfold fz
  rw [show (fun w => ζ (aff t w) / ζ (cen t)) = fun w => (ζ ∘ aff t) w / ζ (cen t) from rfl,
    h.deriv]
  ring

/-- **`ζ'/ζ(s) = Σ_{‖ρ - c‖ ≤ 27/25} m(ρ)/(s - ρ) + O(log |t|)`** for `‖s - c‖ ≤ 1`. -/
theorem logDeriv_local : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
    ∃ hfin : (Zloc t).Finite, ∀ s : ℂ, ‖s - cen t‖ ≤ 1 → ζ s ≠ 0 →
      ‖deriv ζ s / ζ s - ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖ ≤
        C * Real.log |t| := by
  set K : ℝ := 16 * (18 / 25) ^ 2 / (18 / 25 - 2 / 3) ^ 3 +
    1 / ((29 / 30) ^ 2 / (17 / 20) - 17 / 20) / Real.log ((29 / 30) / (17 / 20)) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have : 0 < Real.log ((29 / 30 : ℝ) / (17 / 20)) := Real.log_pos (by norm_num)
    positivity
  set D := |Real.log (41 / m0)|
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨2 / 3 * K * (1 + D / Real.log 3), by positivity, fun t ht => ?_⟩
  have hfZ := finiteSetOfZeros_mono (by norm_num : (18 / 25 : ℝ) < 1) (fz_finite_zeros ht)
  have hfin : (Zloc t).Finite := by
    apply (hfZ.image (aff t)).subset
    intro ρ hρ
    refine ⟨affInv t ρ, ?_, aff_affInv t ρ⟩
    rw [mem_zeros_iff, aff_affInv]; exact hρ
  refine ⟨hfin, fun s hs hζs => ?_⟩
  set z := affInv t s with hzdef
  have hzn : ‖z‖ ≤ 2 / 3 := by rw [hzdef, norm_affInv]; linarith
  have hsz : aff t z = s := aff_affInv t s
  have gA : AnalyticOnNhd ℂ (fz t) (closedBall (0 : ℂ) 1) := by
    intro w hw
    simp only [Metric.mem_closedBall, dist_zero_right] at hw
    exact fz_analyticAt ht (by linarith)
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) (2 / 3) \ SetOfZeros (17 / 20) (fz t) := by
    refine ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hzn, ?_⟩
    rintro ⟨_, h0⟩
    unfold fz at h0
    rw [hsz, div_eq_zero_iff] at h0
    exact h0.elim hζs (zeta_cen_ne t)
  have key := FinalBound (one_lt_Bz t) (by norm_num : (0 : ℝ) < 2 / 3)
    (by norm_num : (2 / 3 : ℝ) < 18 / 25) (by norm_num : (18 / 25 : ℝ) < 1)
    (by norm_num : (18 / 25 : ℝ) < 17 / 20) (by norm_num : (17 / 20 : ℝ) < 29 / 30)
    (by norm_num : (29 / 30 : ℝ) < 1) gA (fz_zero t) (fz_finite_zeros ht)
    (fun w hw => fz_bound ht hw) hzmem
  -- rewrite the left side of `key` in terms of `ζ`
  have hz43 : ‖z‖ < 4 / 3 := by linarith
  have hfzz : fz t z = ζ s / ζ (cen t) := by unfold fz; rw [hsz]
  have hc := zeta_cen_ne t
  have hlhs : deriv (fz t) z / fz t z = 3 / 2 * (deriv ζ s / ζ s) := by
    rw [deriv_fz ht hz43, hsz, hfzz]
    field_simp
  have hinj : Set.InjOn (aff t) (hfZ.toFinset : Set ℂ) := by
    intro a _ b _ hab
    have := congr_arg (affInv t) hab
    rwa [affInv_aff, affInv_aff] at this
  have himg : hfZ.toFinset.image (aff t) = hfin.toFinset := by
    ext ρ
    rw [Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Set.Finite.mem_toFinset, mem_zeros_iff] at hw; exact hw
    · intro hρ
      refine ⟨affInv t ρ, ?_, aff_affInv t ρ⟩
      rw [Set.Finite.mem_toFinset, mem_zeros_iff, aff_affInv]; exact hρ
  have hsum : (∑ ρ ∈ hfZ.toFinset, (analyticOrderNatAt (fz t) ρ : ℂ) / (z - ρ)) =
      3 / 2 * ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ) := by
    rw [← himg, Finset.sum_image hinj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    have hw1 : ‖w‖ ≤ 18 / 25 := hw.1
    rw [ord_fz ht (by linarith)]
    have hdiff : z - w = 2 / 3 * (s - aff t w) := by
      rw [← hsz]; unfold aff; ring
    rw [hdiff]
    by_cases hsw : s - aff t w = 0
    · rw [hsw]; simp
    · field_simp
  rw [hlhs, hsum, ← mul_sub, norm_mul] at key
  have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
  rw [h32] at key
  -- `log B(t) ≤ (1 + D / log 3) log |t|`
  have ht0 : 0 < |t| := by linarith
  have hlt : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
  have hm := m0_pos
  have hB : Real.log (Bz t) ≤ (1 + D / Real.log 3) * Real.log |t| := by
    have h1 : Bz t ≤ |t| * (41 / m0) := by
      unfold Bz
      rw [div_le_iff₀ hm]
      field_simp
      linarith
    have hBpos : 0 < Bz t := lt_trans one_pos (one_lt_Bz t)
    have hD : D ≤ D / Real.log 3 * Real.log |t| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl3]
      exact mul_le_mul_of_nonneg_left hlt (abs_nonneg _)
    calc Real.log (Bz t) ≤ Real.log (|t| * (41 / m0)) := Real.log_le_log hBpos h1
      _ = Real.log |t| + Real.log (41 / m0) := Real.log_mul ht0.ne' (by positivity)
      _ ≤ Real.log |t| + D := by gcongr; exact le_abs_self _
      _ ≤ (1 + D / Real.log 3) * Real.log |t| := by nlinarith
  have hK' : 16 * (18 / 25 : ℝ) ^ 2 / (18 / 25 - 2 / 3) ^ 3 +
      1 / (((29 / 30) ^ 2 / (17 / 20) - 17 / 20) * Real.log ((29 / 30) / (17 / 20))) = K := by
    rw [hK]; ring
  rw [hK'] at key
  have hlogB0 : 0 ≤ Real.log (Bz t) := (Real.log_pos (one_lt_Bz t)).le
  have : 3 / 2 * ‖deriv ζ s / ζ s - ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ)‖
      ≤ K * ((1 + D / Real.log 3) * Real.log |t|) :=
    key.trans (mul_le_mul_of_nonneg_left hB hKpos.le)
  nlinarith [norm_nonneg (deriv ζ s / ζ s - ∑ ρ ∈ hfin.toFinset,
    (analyticOrderNatAt ζ ρ : ℂ) / (s - ρ))]

end LeanLab.PNTPort.ZetaZeros

