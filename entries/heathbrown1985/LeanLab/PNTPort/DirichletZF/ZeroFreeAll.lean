module

public import LeanLab.PNTPort.DirichletZF.ZeroFreeReal
public import LeanLab.PNTPort.DirichletZF.Page

/-!
# The full zero-free region for Dirichlet L-functions, with one possible exceptional zero

Lab proof, unit U-5110. AI wrote this file. Known mathematics, no cited input. It uses
`riemannZetaLogDerivResidueBigO` from the ported StrongPNT files, Apache-2.0, the
PrimeNumberTheoremAnd contributors.

* `zeta_near_pole`: `Re(-ζ'/ζ(s)) ≤ Re(1/(s - 1)) + A` for `1 < Re s ≤ 2`, `|Im s| ≤ 4`;
* `zero_free_real_small`: real `χ`, a zero with `|γ| < 2` and `|γ| ≥ 1/(4 M log B(γ))` has
  `β ≤ 1 - c / log B(γ)`;
* `zero_free_region`: there are absolute `c, c' > 0` such that for every `N ≥ 1` and every
  non-principal `χ` mod `N`, every zero `β + iγ` of `L(s, χ)` has `β ≤ 1 - c / log B(γ)`
  unless it lies in the box `β ≥ 1 - c / log B(0)`, `|γ| ≤ c' / log B(0)`, and that box holds
  at most one zero of `L(s, χ)`.
This is the classical statement, Davenport chapter 14, Montgomery-Vaughan Theorem 11.3, with
`log B(t) = log(2NZ(|t| + 3))` in place of `log q(|t| + 2)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter Metric

/-- `-ζ'/ζ(s) - 1/(s - 1)` is bounded on `1 < Re s ≤ 2`, `|Im s| ≤ 4`. -/
theorem zeta_near_pole : ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 4 →
    (-deriv riemannZeta s / riemannZeta s).re ≤ (1 / (s - 1)).re + A := by
  set g : ℂ → ℂ := -deriv riemannZeta / riemannZeta - fun z ↦ (z - 1)⁻¹ with hg
  obtain ⟨C, hC⟩ := riemannZetaLogDerivResidueBigO.bound
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hC
  set K : Set ℂ := {s | 1 ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ 4 ∧ ε / 2 ≤ ‖s - 1‖} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · refine IsClosed.inter (isClosed_le continuous_const continuous_re) ?_
      refine IsClosed.inter (isClosed_le continuous_re continuous_const) ?_
      refine IsClosed.inter (isClosed_le (continuous_abs.comp continuous_im) continuous_const) ?_
      exact isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 6)).subset ?_
      intro s hs
      obtain ⟨h1, h2, h3, -⟩ := hs
      rw [mem_closedBall, dist_zero_right]
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 6 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hne1 : ∀ s ∈ K, s ≠ 1 := by
    intro s hs h; rw [h] at hs
    have := hs.2.2.2; simp at this; linarith
  have hcont : ContinuousOn g K := by
    have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hdiff : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun z hz ↦
      (differentiableAt_riemannZeta hz).differentiableWithinAt
    have hder : ContinuousOn (deriv riemannZeta) {1}ᶜ :=
      ((hdiff.analyticOnNhd hopen).deriv).continuousOn
    intro s hs
    have hs1 := hne1 s hs
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.1
    refine ContinuousAt.continuousWithinAt ?_
    have c1 : ContinuousAt (deriv riemannZeta) s := hder.continuousAt (hopen.mem_nhds hs1)
    have c2 : ContinuousAt riemannZeta s := (differentiableAt_riemannZeta hs1).continuousAt
    have c3 : ContinuousAt (fun z : ℂ ↦ (z - 1)⁻¹) s :=
      (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hs1)
    exact ((c1.neg).div c2 hz).sub c3
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max (max C M) 0, le_max_right _ _, fun s hs1 hs2 hs3 ↦ ?_⟩
  have hsne : s ≠ 1 := by intro h; rw [h] at hs1; simp at hs1
  have hgs : ‖g s‖ ≤ max (max C M) 0 := by
    by_cases hnear : ‖s - 1‖ < ε / 2
    · have hmem : s ∈ ball (1 : ℂ) ε ∩ {1}ᶜ := ⟨by rw [mem_ball, dist_eq_norm]; linarith, hsne⟩
      have := hball hmem
      simp only [mem_ofPred_eq, Pi.one_apply, norm_one, mul_one] at this
      exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
    · push Not at hnear
      exact (hM s ⟨hs1.le, hs2, hs3, hnear⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  have he : -deriv riemannZeta s / riemannZeta s = g s + 1 / (s - 1) := by
    simp only [hg, Pi.sub_apply, Pi.div_apply, Pi.neg_apply, one_div]; ring
  rw [he, add_re]
  have := (Complex.re_le_norm (g s)).trans hgs
  linarith

lemma Bt_mono {N : ℕ} {s t : ℝ} (h : |s| ≤ |t|) : Bt N s ≤ Bt N t := by
  unfold Bt
  have hZ := Z_pos
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have : 2 * (N : ℝ) * (|s| + 3) ≤ 2 * N * (|t| + 3) := by nlinarith
  nlinarith

lemma log_Bt_mono {N : ℕ} [NeZero N] {s t : ℝ} (h : |s| ≤ |t|) :
    Real.log (Bt N s) ≤ Real.log (Bt N t) :=
  Real.log_le_log (by linarith [one_lt_Bt (N := N) s]) (Bt_mono h)

lemma log_N_le_log_Bt {N : ℕ} [NeZero N] (t : ℝ) : Real.log N ≤ Real.log (Bt N t) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hZ := one_le_Z
  have ht0 := abs_nonneg t
  have a' : (N : ℝ) ≤ N * (|t| + 3) := le_mul_of_one_le_right (by positivity) (by linarith)
  have b : N * (|t| + 3) ≤ N * (|t| + 3) * Z := le_mul_of_one_le_right (by positivity) hZ
  have e : Bt N t = 2 * (N * (|t| + 3) * Z) := by unfold Bt; ring
  exact Real.log_le_log (by linarith) (by rw [e]; linarith)

/-- The closing algebra with `16/5` in place of `3`. -/
lemma beta_le_of_comb' {D β : ℝ} (hD : 1 < D)
    (h : 4 / (1 + 1 / (4 * D) - β) ≤ (16 / 5) / (1 / (4 * D)) + D)
    (hpos : 0 < 1 + 1 / (4 * D) - β) :
    β ≤ 1 - 11 / (276 * D) := by
  have hDpos : 0 < D := by linarith
  have h3d : (16 / 5) / (1 / (4 * D)) = 64 / 5 * D := by field_simp; ring
  rw [h3d] at h
  have h13 : 4 ≤ 69 / 5 * D * (1 + 1 / (4 * D) - β) := by
    rw [div_le_iff₀ hpos] at h; linarith
  have : 4 / (69 / 5 * D) ≤ 1 + 1 / (4 * D) - β := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have e : 1 + 1 / (4 * D) - 4 / (69 / 5 * D) = 1 - 11 / (276 * D) := by
    field_simp; ring
  linarith

/-- Real characters, `|γ| < 2`, away from the real axis by `1/(4 M log B(γ))`. -/
theorem zero_free_real_small : ∃ M₀ : ℝ, 1 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 → ∀ ρ : ℂ,
      DirichletCharacter.LFunction χ ρ = 0 → |ρ.im| ≤ 2 →
      1 / (4 * (M * Real.log (Bt N ρ.im))) ≤ |ρ.im| →
        ρ.re ≤ 1 - 11 / (276 * M) / Real.log (Bt N ρ.im) := by
  obtain ⟨A, hA, hprin⟩ := principal_bound
  obtain ⟨A', hA', hzeta⟩ := zeta_near_pole
  have hK := K0_pos
  refine ⟨4 * K0 + 3 * A + A' + 18, by linarith, fun M hM N _ χ hχ hχ2 ρ hρ hγ2 hγd ↦ ?_⟩
  set t := ρ.im with ht
  set Lg := Real.log (Bt N t) with hLg
  have hL1 : 1 ≤ Lg := one_le_log_Bt t
  set D := M * Lg with hD
  have hMpos : 1 < M := by linarith
  have hD1 : 1 < D := by rw [hD]; nlinarith
  set d : ℝ := 1 / (4 * D) with hd
  have hd0 : d ∈ Ioo 0 1 := by
    rw [hd]; constructor
    · positivity
    · rw [div_lt_one (by linarith)]; linarith
  have hβ1 : ρ.re < 1 := by
    by_contra hc; push Not at hc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hc hρ
  have hpos : 0 < 1 + d - ρ.re := by linarith [hd0.1]
  have b0 := hprin N d hd0
  have b1 := shiftOne_bound hχ hd0 hρ
  -- the third term, `χ² = χ₀` at `1 + d + 2it`
  set s2 : ℂ := 1 + d + 2 * I * t with hs2
  have hs2re : s2.re = 1 + d := by simp [hs2]
  have hs2im : s2.im = 2 * t := by simp [hs2]
  have hz := hzeta s2 (by rw [hs2re]; linarith [hd0.1]) (by rw [hs2re]; linarith [hd0.2])
    (by rw [hs2im, abs_mul, abs_two]; linarith)
  have hdiff := logDeriv_trivChar_sub_zeta (N := N) (show 1 < s2.re by rw [hs2re]; linarith [hd0.1])
  have h3 : -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) s2 /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) s2).re ≤
      (1 / (s2 - 1)).re + A' + Real.log N := by
    have h1 := Complex.re_le_norm (-(deriv (DirichletCharacter.LFunction
      (1 : DirichletCharacter ℂ N)) s2 / DirichletCharacter.LFunction
      (1 : DirichletCharacter ℂ N) s2 - deriv riemannZeta s2 / riemannZeta s2))
    rw [norm_neg, neg_re, sub_re] at h1
    rw [neg_div_re_eq] at hz
    linarith
  -- `Re 1/(d + 2it) ≤ 1/(5d)` since `|t| ≥ d`
  have htd : d ≤ |t| := hγd
  have hre : (1 / (s2 - 1)).re ≤ 1 / (5 * d) := by
    have e : s2 - 1 = (d : ℂ) + ((2 * t : ℝ) : ℂ) * I := by rw [hs2]; push_cast; ring
    rw [e, one_div, Complex.inv_re, Complex.normSq_add_mul_I]
    simp only [ofReal_re, add_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
      zero_mul, add_zero]
    have hdpos := hd0.1
    have ht2 : d ^ 2 ≤ t ^ 2 := by
      have := sq_le_sq' (by linarith [abs_nonneg t, neg_abs_le t] : -|t| ≤ d) htd
      rwa [sq_abs] at this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlN := log_N_le_log_Bt (N := N) t
  rw [← hLg] at hlN
  have key := three_four_one χ (show 1 < 1 + d by linarith [hd0.1]) t
  rw [hχ2] at key
  simp only [Complex.ofReal_add, Complex.ofReal_one] at key
  have c1 : (1 : ℂ) + d + t * I = 1 + d + I * t := by ring
  have c2 : (1 : ℂ) + d + 2 * t * I = s2 := by rw [hs2]; ring
  rw [c1, c2] at key
  simp only [neg_div_re_eq] at key b0
  rw [← ht] at b1
  rw [← hLg] at b1
  have hcomb : 4 / (1 + d - ρ.re) ≤ (16 / 5) / d + D := by
    have e4 : 4 / (1 + d - ρ.re) = 4 * (1 / (1 + d - ρ.re)) := by ring
    have e3 : (16 / 5) / d = 3 * (1 / d) + 1 / (5 * d) := by field_simp; ring
    have hA1 : A ≤ A * Lg := le_mul_of_one_le_right (by linarith) hL1
    have hA2 : A' ≤ A' * Lg := le_mul_of_one_le_right hA' hL1
    have hML : (4 * K0 + 3 * A + A' + 18) * Lg ≤ M * Lg :=
      mul_le_mul_of_nonneg_right hM (by linarith)
    rw [e4, e3, hD]
    nlinarith
  have e : 11 / (276 * M) / Lg = 11 / (276 * D) := by rw [hD]; field_simp
  rw [e]
  exact beta_le_of_comb' hD1 hcomb hpos

/-- The zero-free region for every non-principal character, with at most one exceptional
zero in a box at `1`. -/
theorem zero_free_region : ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
        ρ.re ≤ 1 - c / Real.log (Bt N ρ.im) ∨
        (1 - c / Real.log (Bt N 0) ≤ ρ.re ∧ |ρ.im| ≤ c' / Real.log (Bt N 0))) ∧
      (∀ ρ₁ ρ₂ : ℂ, DirichletCharacter.LFunction χ ρ₁ = 0 →
        DirichletCharacter.LFunction χ ρ₂ = 0 →
        1 - c / Real.log (Bt N 0) ≤ ρ₁.re → |ρ₁.im| ≤ c' / Real.log (Bt N 0) →
        1 - c / Real.log (Bt N 0) ≤ ρ₂.re → |ρ₂.im| ≤ c' / Real.log (Bt N 0) → ρ₁ = ρ₂) := by
  obtain ⟨c0, hc0, hpage⟩ := page_two_zeros
  obtain ⟨c1, hc1, hcx⟩ := zero_free_complex
  obtain ⟨c2, hc2, hre⟩ := zero_free_real
  obtain ⟨M₀, hM₀, hsmall⟩ := zero_free_real_small
  set M : ℝ := M₀ + 1 / c0 with hMdef
  have hMM : M₀ ≤ M := by rw [hMdef]; linarith [one_div_pos.mpr hc0]
  have hMpos : 0 < M := by linarith
  set c3 : ℝ := 11 / (276 * M)
  have hc3 : 0 < c3 := by positivity
  set c := min (min c1 c2) (min c3 c0) with hc
  set c' : ℝ := 1 / (4 * M) with hc'
  have hcpos : 0 < c := lt_min (lt_min hc1 hc2) (lt_min hc3 hc0)
  have hc'pos : 0 < c' := by positivity
  have hcc0 : c ≤ c0 := (min_le_right _ _).trans (min_le_right _ _)
  have hc'c0 : c' ≤ c0 := by
    rw [hc', div_le_iff₀ (by positivity)]
    have : 1 ≤ c0 * M := by
      rw [hMdef, mul_add, mul_one_div_cancel hc0.ne']; nlinarith
    linarith
  refine ⟨c, c', hcpos, hc'pos, fun N _ χ hχ ↦ ⟨fun ρ hρ ↦ ?_, ?_⟩⟩
  · have hL := one_le_log_Bt (N := N) ρ.im
    have hLp : 0 < Real.log (Bt N ρ.im) := by linarith
    have mono : ∀ c₁ : ℝ, c ≤ c₁ → ρ.re ≤ 1 - c₁ / Real.log (Bt N ρ.im) →
        ρ.re ≤ 1 - c / Real.log (Bt N ρ.im) := by
      intro c₁ h h'
      have := div_le_div_of_nonneg_right h hLp.le
      linarith
    by_cases hsq : χ ^ 2 = 1
    · by_cases hbig : 2 ≤ |ρ.im|
      · exact Or.inl (mono c2 ((min_le_left _ _).trans (min_le_right _ _))
          (hre N χ hχ hsq ρ hρ hbig))
      · push Not at hbig
        by_cases hfar : 1 / (4 * (M * Real.log (Bt N ρ.im))) ≤ |ρ.im|
        · exact Or.inl (mono c3 ((min_le_right _ _).trans (min_le_left _ _))
            (hsmall M hMM N χ hχ hsq ρ hρ hbig.le hfar))
        · push Not at hfar
          have hL0 := one_le_log_Bt (N := N) 0
          have hmono : Real.log (Bt N 0) ≤ Real.log (Bt N ρ.im) :=
            log_Bt_mono (by simp)
          have hγ : |ρ.im| ≤ c' / Real.log (Bt N 0) := by
            rw [hc']
            have : 1 / (4 * (M * Real.log (Bt N ρ.im))) ≤ 1 / (4 * M) / Real.log (Bt N 0) := by
              rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
              nlinarith
            linarith
          by_cases hβ : 1 - c / Real.log (Bt N 0) ≤ ρ.re
          · exact Or.inr ⟨hβ, hγ⟩
          · push Not at hβ
            left
            have : c / Real.log (Bt N ρ.im) ≤ c / Real.log (Bt N 0) :=
              div_le_div_of_nonneg_left hcpos.le (by linarith) hmono
            linarith
    · exact Or.inl (mono c1 ((min_le_left _ _).trans (min_le_left _ _))
        (hcx N χ hsq ρ hρ))
  · intro ρ₁ ρ₂ h1 h2 hb1 hg1 hb2 hg2
    have hL0 := one_le_log_Bt (N := N) 0
    have hLp : 0 < Real.log (Bt N 0) := by linarith
    have hh : c / Real.log (Bt N 0) ≤ c0 / Real.log (Bt N 0) :=
      div_le_div_of_nonneg_right hcc0 hLp.le
    have hw : c' / Real.log (Bt N 0) ≤ c0 / Real.log (Bt N 0) :=
      div_le_div_of_nonneg_right hc'c0 hLp.le
    exact hpage N χ hχ ρ₁ ρ₂ h1 h2 (by linarith) (hg1.trans hw) (by linarith) (hg2.trans hw)

end LeanLab.PNTPort.DirichletZF

