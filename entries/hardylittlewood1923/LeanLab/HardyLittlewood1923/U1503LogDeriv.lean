module

public import LeanLab.PNTPort.DirichletZF.U1482Jensen

/-!
AI-written Lean code, Claude, 2026-10-23, CLOUD run 20261023T1343Z-19109, unit U-1503, paper P0004.

# `L'/L` away from its zeros on a wide disc about `3/2 + it`

Known mathematics, Davenport ch. 16, no cited input. It applies the Borel-Caratheodory bound
`FinalBound` and the Jensen count `ZerosBound` of the ported StrongPNT file, Apache-2.0, the
PrimeNumberTheoremAnd contributors, to `g(z) = f(c + (29/20) z) / f(c)`. The rescaling by `29/20`
makes the inner disc reach `Re s = 1/2 - 0.015`, where DirichletZF's LogDeriv.lean only reaches
`Re s = 5/6`.

* `bc_wide`: for `f` entire, `‖f c‖ ≥ a > 0`, `‖f‖ ≤ M` on the disc of radius `1.4355` about `c`,
  `a < M`, and `s` within `1.015` of `c`, not a zero, at distance `≥ η > 0` from every zero
  within `1.16` of `c`: `‖f'/f(s)‖ ≤ (K + 1/(l η)) log (M/a)`, with absolute `K`, `l`.
* `logDeriv_L_wide`: the case `f = L(·, χ)`, `χ ≠ 1` mod `N`, `c = 3/2 + it`,
  `log (M/a) = log (20 N (|t| + 3) Z)`.
* `logDeriv_gZ_wide`: the case `f = (s - 1) ζ(s)`, `log (M/a) = log (60 (|t| + 4)² Z)`.
* `logDeriv_zeta_eq`: `ζ'/ζ = gZ'/gZ - 1/(s - 1)` off `1` and the zeros.
-/

@[expose] public section

open Complex Set Filter Metric Topology

namespace LeanLab.HardyLittlewood1923.U1503

open LeanLab.PNTPort.DirichletZF (Z Z_pos one_le_Z norm_LFunction_ge norm_LFunction_le)
open LeanLab.PNTPort.DirichletZF.U1482 (gZ gZ_of_ne gZ_one gZ_analyticAt gZ_eventuallyEq
  norm_gZ_le cen cen_ne_one norm_zeta_cen_ge norm_cen_le)

/-- The `FinalBound` constant at `r' = 7/10`, `r = 4/5`, `R' = 9/10`, `R = 99/100`. -/
noncomputable def KW : ℝ := 16 * (4 / 5 : ℝ) ^ 2 / (4 / 5 - 7 / 10) ^ 3 +
    1 / (((99 / 100 : ℝ) ^ 2 / (9 / 10) - 9 / 10) * Real.log ((99 / 100) / (9 / 10)))

lemma KW_pos : 0 < KW := by
  unfold KW
  have : 0 < Real.log ((99 / 100 : ℝ) / (9 / 10)) := Real.log_pos (by norm_num)
  have : (0 : ℝ) < (99 / 100 : ℝ) ^ 2 / (9 / 10) - 9 / 10 := by norm_num
  positivity

/-- The Jensen constant `log ((99/100) / (4/5))`. -/
noncomputable def lZ : ℝ := Real.log ((99 / 100 : ℝ) / (4 / 5))

lemma lZ_pos : 0 < lZ := Real.log_pos (by norm_num)

/-- The zeros of an entire function with `g 0 ≠ 0` in the closed unit disc are finite. -/
lemma finite_zeros_of_entire {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h0 : g 0 ≠ 0) :
    (SetOfZeros 1 g).Finite := by
  by_contra hinf; rw [Set.not_finite] at hinf
  have zerosSubset : SetOfZeros 1 g ⊆ closedBall (0 : ℂ) 1 := fun _ hx ↦ by
    simpa only [mem_closedBall, dist_zero_right] using hx.1
  obtain ⟨x, hxK, hacc⟩ :=
    hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall 0 1) zerosSubset
  have hfAnalytic : AnalyticOnNhd ℂ g (ball (0 : ℂ) 2) := fun z _ ↦ hg.analyticAt z
  have hfeq : Set.EqOn g 0 (ball (0 : ℂ) 2) := by
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hfAnalytic
      isPreconnected_ball (z₀ := x) ?_ ?_
    · simp only [mem_ball, mem_closedBall, dist_zero_right] at hxK ⊢
      linarith
    · simp only [mem_closure_iff_clusterPt, ← accPt_principal_iff_clusterPt]
      exact hacc.mono (principal_mono.mpr fun _ h ↦ h.2)
  exact h0 (hfeq (mem_ball_self (by norm_num)))

lemma norm_lam : ‖(29 / 20 : ℂ)‖ = 29 / 20 := by
  rw [norm_div, Complex.norm_ofNat, Complex.norm_ofNat]

/-- **Borel-Caratheodory on the wide disc.** -/
theorem bc_wide {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {a M : ℝ} (ha : 0 < a)
    (hfc : a ≤ ‖f c‖) (hM : ∀ z : ℂ, ‖z - c‖ ≤ 29 / 20 * (99 / 100) → ‖f z‖ ≤ M) (haM : a < M)
    {s : ℂ} (hs : ‖s - c‖ ≤ 29 / 20 * (7 / 10)) (hfs : f s ≠ 0) {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ : ℂ, f ρ = 0 → ‖ρ - c‖ ≤ 29 / 20 * (4 / 5) → η ≤ ‖s - ρ‖) :
    ‖deriv f s / f s‖ ≤ (KW + 1 / (lZ * η)) * Real.log (M / a) := by
  have hfc0 : f c ≠ 0 := by
    intro h; rw [h, norm_zero] at hfc; linarith
  set g : ℂ → ℂ := fun z ↦ f (c + (29 / 20 : ℂ) * z) / f c with hgdef
  have hlin : Differentiable ℂ (fun z : ℂ ↦ c + (29 / 20 : ℂ) * z) :=
    (differentiable_const c).add (differentiable_id.const_mul _)
  have hgd : Differentiable ℂ g := (hf.comp hlin).div_const _
  have hgA : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) 1) := fun z _ ↦ hgd.analyticAt z
  have hg0 : g 0 = 1 := by simp [hgdef, hfc0]
  have hfin := finite_zeros_of_entire hgd (by rw [hg0]; exact one_ne_zero)
  set B := M / a with hBdef
  have hB : 1 < B := (one_lt_div ha).2 haM
  have hgB : ∀ z : ℂ, ‖z‖ ≤ 99 / 100 → ‖g z‖ ≤ B := by
    intro z hz
    simp only [hgdef, norm_div]
    have h1 : ‖(c + (29 / 20 : ℂ) * z) - c‖ ≤ 29 / 20 * (99 / 100) := by
      rw [add_sub_cancel_left, norm_mul, norm_lam]
      exact mul_le_mul_of_nonneg_left hz (by norm_num)
    exact div_le_div₀ (by linarith) (hM _ h1) ha hfc
  set z₀ : ℂ := (s - c) / (29 / 20 : ℂ) with hz₀def
  have hcz : c + (29 / 20 : ℂ) * z₀ = s := by
    rw [hz₀def]; field_simp; try ring
  have hz₀ : ‖z₀‖ ≤ 7 / 10 := by
    rw [hz₀def, norm_div, norm_lam, div_le_iff₀ (by norm_num)]; linarith
  have hgz : g z₀ ≠ 0 := by
    simp only [hgdef, hcz]; exact div_ne_zero hfs hfc0
  have hmem : z₀ ∈ closedBall (0 : ℂ) (7 / 10) \ SetOfZeros (9 / 10) g :=
    ⟨mem_closedBall_zero_iff.2 hz₀, fun h ↦ hgz h.2⟩
  have hFB := FinalBound hB (by norm_num : (0 : ℝ) < 7 / 10) (by norm_num : (7 / 10 : ℝ) < 4 / 5)
    (by norm_num : (4 / 5 : ℝ) < 1) (by norm_num : (4 / 5 : ℝ) < 9 / 10)
    (by norm_num : (9 / 10 : ℝ) < 99 / 100) (by norm_num : (99 / 100 : ℝ) < 1) hgA hg0 hfin hgB hmem
  have hZB := ZerosBound (by norm_num : (0 : ℝ) < 4 / 5) (by norm_num : (4 / 5 : ℝ) < 1)
    (by norm_num : (4 / 5 : ℝ) < 99 / 100) (by norm_num : (99 / 100 : ℝ) < 1) hgA hg0 hfin hgB
  push_cast at hZB
  set S := (finiteSetOfZeros_mono (by norm_num : (4 / 5 : ℝ) < 1) hfin).toFinset with hSdef
  -- the derivative
  have hderiv : deriv g z₀ = (29 / 20 : ℂ) * deriv f s / f c := by
    have h1 : HasDerivAt (fun z : ℂ ↦ c + (29 / 20 : ℂ) * z) (29 / 20) z₀ := by
      simpa using ((hasDerivAt_id z₀).const_mul (29 / 20 : ℂ)).const_add c
    have h2 : HasDerivAt f (deriv f s) (c + (29 / 20 : ℂ) * z₀) := by
      rw [hcz]; exact (hf s).hasDerivAt
    have h3 := (h2.comp z₀ h1).div_const (f c)
    exact h3.deriv.trans (by ring)
  have hratio : deriv g z₀ / g z₀ = (29 / 20 : ℂ) * (deriv f s / f s) := by
    rw [hderiv]
    simp only [hgdef, hcz]
    field_simp
  -- the zero sum
  set L := Real.log B with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hB.le
  have hsum : ‖∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℂ) / (z₀ - ρ)‖ ≤
      (29 / 20) / η * ∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ hρ ↦ ?_
    have hρ' : ρ ∈ SetOfZeros (4 / 5) g := (Set.Finite.mem_toFinset _).1 hρ
    obtain ⟨hρn, hgρ⟩ := hρ'
    have hfρ : f (c + (29 / 20 : ℂ) * ρ) = 0 := by
      simp only [hgdef, div_eq_zero_iff] at hgρ
      rcases hgρ with h | h
      · exact h
      · exact absurd h hfc0
    have hρc : ‖(c + (29 / 20 : ℂ) * ρ) - c‖ ≤ 29 / 20 * (4 / 5) := by
      rw [add_sub_cancel_left, norm_mul, norm_lam]
      exact mul_le_mul_of_nonneg_left hρn (by norm_num)
    have hdist := hd _ hfρ hρc
    have he : s - (c + (29 / 20 : ℂ) * ρ) = (29 / 20 : ℂ) * (z₀ - ρ) := by rw [← hcz]; ring
    rw [he, norm_mul, norm_lam] at hdist
    have hpos : 0 < ‖z₀ - ρ‖ := by
      have : 0 < 29 / 20 * ‖z₀ - ρ‖ := lt_of_lt_of_le hη hdist
      linarith
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hpos]
    have hm : (0 : ℝ) ≤ (analyticOrderNatAt g ρ : ℝ) := Nat.cast_nonneg _
    calc (analyticOrderNatAt g ρ : ℝ) = (analyticOrderNatAt g ρ : ℝ) * 1 := by ring
      _ ≤ (analyticOrderNatAt g ρ : ℝ) * ((29 / 20) / η * ‖z₀ - ρ‖) := by
          apply mul_le_mul_of_nonneg_left _ hm
          rw [div_mul_eq_mul_div, le_div_iff₀ hη]; linarith
      _ = 29 / 20 / η * (analyticOrderNatAt g ρ : ℝ) * ‖z₀ - ρ‖ := by ring
  have hsum2 : ‖∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℂ) / (z₀ - ρ)‖ ≤ (29 / 20) / η * (1 / lZ * L) :=
    hsum.trans (mul_le_mul_of_nonneg_left hZB (by positivity))
  have htot : 29 / 20 * ‖deriv f s / f s‖ ≤ KW * L + (29 / 20) / η * (1 / lZ * L) := by
    have e1 : 29 / 20 * ‖deriv f s / f s‖ = ‖deriv g z₀ / g z₀‖ := by
      rw [hratio, norm_mul, norm_lam]
    rw [e1]
    have hFB' : ‖deriv g z₀ / g z₀ - ∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℂ) / (z₀ - ρ)‖ ≤
        KW * L := hFB
    calc ‖deriv g z₀ / g z₀‖
        = ‖(deriv g z₀ / g z₀ - ∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℂ) / (z₀ - ρ)) +
            ∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℂ) / (z₀ - ρ)‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hFB' hsum2)
  have hK := KW_pos
  have hl := lZ_pos
  have hn0 : 0 ≤ ‖deriv f s / f s‖ := norm_nonneg _
  have e2 : (29 / 20) / η * (1 / lZ * L) = 29 / 20 * (1 / (lZ * η) * L) := by
    ring
  rw [e2] at htot
  have hKL : 0 ≤ KW * L := mul_nonneg hK.le hL0
  have : ‖deriv f s / f s‖ ≤ KW * L + 1 / (lZ * η) * L := by nlinarith
  calc ‖deriv f s / f s‖ ≤ KW * L + 1 / (lZ * η) * L := this
    _ = (KW + 1 / (lZ * η)) * L := by ring

/-- Points within `29/20 · 99/100` of `cen t` have `Re z ≥ 1/20` and `‖z‖ ≤ |t| + 3`. -/
lemma wide_disc_bounds {t : ℝ} {z : ℂ} (hz : ‖z - cen t‖ ≤ 29 / 20 * (99 / 100)) :
    1 / 20 ≤ z.re ∧ ‖z‖ ≤ |t| + 3 := by
  constructor
  · have h1 : |(z - cen t).re| ≤ ‖z - cen t‖ := Complex.abs_re_le_norm _
    have h2 : (z - cen t).re = z.re - 3 / 2 := by simp [cen]
    rw [h2] at h1
    have := (abs_le.mp (h1.trans hz)).1
    linarith
  · have h3 : ‖z‖ ≤ ‖z - cen t‖ + ‖cen t‖ := by
      calc ‖z‖ = ‖(z - cen t) + cen t‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have := norm_cen_le t
    linarith

/-- **`L'/L` on the wide disc, `χ ≠ 1`.** -/
theorem logDeriv_L_wide {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ)
    {s : ℂ} (hs : ‖s - cen t‖ ≤ 29 / 20 * (7 / 10))
    (hLs : DirichletCharacter.LFunction χ s ≠ 0) {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖ρ - cen t‖ ≤ 29 / 20 * (4 / 5) →
      η ≤ ‖s - ρ‖) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      (KW + 1 / (lZ * η)) * Real.log (20 * N * (|t| + 3) * Z) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hZ := one_le_Z
  have hZ0 := Z_pos
  have hfc : 1 / Z ≤ ‖DirichletCharacter.LFunction χ (cen t)‖ := norm_LFunction_ge χ t
  have hM : ∀ z : ℂ, ‖z - cen t‖ ≤ 29 / 20 * (99 / 100) →
      ‖DirichletCharacter.LFunction χ z‖ ≤ 20 * N * (|t| + 3) := by
    intro z hz
    obtain ⟨hre, hnorm⟩ := wide_disc_bounds hz
    have hre0 : 0 < z.re := by linarith
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ N * ‖z‖ / z.re := norm_LFunction_le hχ hre0
      _ ≤ N * (|t| + 3) / (1 / 20) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnorm (by linarith))
            (by norm_num) hre
      _ = 20 * N * (|t| + 3) := by ring
  have haM : 1 / Z < 20 * N * (|t| + 3) := by
    have h1 : 1 / Z ≤ 1 := by rw [div_le_one hZ0]; exact hZ
    have h2 : (60 : ℝ) ≤ 20 * N * (|t| + 3) := by nlinarith [abs_nonneg t]
    linarith
  have hb := bc_wide (DirichletCharacter.differentiable_LFunction hχ) (by positivity) hfc hM haM
    hs hLs hη hd
  have e : 20 * N * (|t| + 3) / (1 / Z) = 20 * N * (|t| + 3) * Z := by
    field_simp
  rwa [e] at hb

/-- **`(s - 1) ζ(s)` on the wide disc.** -/
theorem logDeriv_gZ_wide (t : ℝ) {s : ℂ} (hs : ‖s - cen t‖ ≤ 29 / 20 * (7 / 10))
    (hgs : gZ s ≠ 0) {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ : ℂ, gZ ρ = 0 → ‖ρ - cen t‖ ≤ 29 / 20 * (4 / 5) → η ≤ ‖s - ρ‖) :
    ‖deriv gZ s / gZ s‖ ≤ (KW + 1 / (lZ * η)) * Real.log (60 * (|t| + 4) ^ 2 * Z) := by
  have hZ := one_le_Z
  have hZ0 := Z_pos
  have hgd : Differentiable ℂ gZ := fun z ↦ (gZ_analyticAt z).differentiableAt
  have hfc : 1 / (2 * Z) ≤ ‖gZ (cen t)‖ := by
    rw [gZ_of_ne (cen_ne_one t), norm_mul]
    have h1 : 1 / 2 ≤ ‖cen t - 1‖ := by
      have := Complex.abs_re_le_norm (cen t - 1)
      have e : (cen t - 1).re = 1 / 2 := by norm_num [cen]
      rw [e] at this; rwa [abs_of_pos (by norm_num)] at this
    have h2 := norm_zeta_cen_ge t
    calc 1 / (2 * Z) = (1 / 2) * (1 / Z) := by ring
      _ ≤ ‖cen t - 1‖ * ‖riemannZeta (cen t)‖ :=
          mul_le_mul h1 h2 (by positivity) (by linarith)
  have hM : ∀ z : ℂ, ‖z - cen t‖ ≤ 29 / 20 * (99 / 100) → ‖gZ z‖ ≤ 30 * (|t| + 4) ^ 2 := by
    intro z hz
    obtain ⟨hre, hnorm⟩ := wide_disc_bounds hz
    have ht := abs_nonneg t
    rcases eq_or_ne z 1 with rfl | h1
    · rw [gZ_one, norm_one]; nlinarith
    have hre0 : 0 < z.re := by linarith
    have hz1 : ‖z - 1‖ ≤ |t| + 4 := by
      have := norm_sub_le z 1; rw [norm_one] at this; linarith
    have hq : ‖z‖ * ‖z - 1‖ / z.re ≤ 20 * ((|t| + 3) * (|t| + 4)) := by
      rw [div_le_iff₀ hre0]
      have h0 : ‖z‖ * ‖z - 1‖ ≤ (|t| + 3) * (|t| + 4) :=
        mul_le_mul hnorm hz1 (norm_nonneg _) (by linarith)
      have h20 : 1 ≤ 20 * z.re := by linarith
      have hp : 0 ≤ (|t| + 3) * (|t| + 4) := by positivity
      calc ‖z‖ * ‖z - 1‖ ≤ (|t| + 3) * (|t| + 4) * 1 := by linarith
        _ ≤ (|t| + 3) * (|t| + 4) * (20 * z.re) := mul_le_mul_of_nonneg_left h20 hp
        _ = 20 * ((|t| + 3) * (|t| + 4)) * z.re := by ring
    calc ‖gZ z‖ ≤ ‖z - 1‖ + 1 + ‖z‖ * ‖z - 1‖ / z.re := norm_gZ_le hre0 h1
      _ ≤ (|t| + 4) + 1 + 20 * ((|t| + 3) * (|t| + 4)) := by linarith
      _ ≤ 30 * (|t| + 4) ^ 2 := by nlinarith
  have haM : 1 / (2 * Z) < 30 * (|t| + 4) ^ 2 := by
    have h1 : 1 / (2 * Z) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have h2 : (480 : ℝ) ≤ 30 * (|t| + 4) ^ 2 := by nlinarith [abs_nonneg t]
    linarith
  have hb := bc_wide hgd (by positivity) hfc hM haM hs hgs hη hd
  have e : 30 * (|t| + 4) ^ 2 / (1 / (2 * Z)) = 60 * (|t| + 4) ^ 2 * Z := by
    field_simp; try ring
  rwa [e] at hb

/-- `ζ'/ζ = gZ'/gZ - 1/(s - 1)` off `1` and the zeros of `ζ`. -/
lemma logDeriv_zeta_eq {s : ℂ} (h1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s = deriv gZ s / gZ s - 1 / (s - 1) := by
  have hd : deriv gZ s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [(gZ_eventuallyEq h1).deriv_eq]
    have h := ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta h1).hasDerivAt
    simp only [id] at h
    exact h.deriv.trans (by ring)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [hd, gZ_of_ne h1]
  field_simp
  try ring

end LeanLab.HardyLittlewood1923.U1503
