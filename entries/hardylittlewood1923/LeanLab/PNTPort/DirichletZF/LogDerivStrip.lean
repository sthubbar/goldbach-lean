module

public import LeanLab.PNTPort.DirichletZF.ZeroFree

/-!
# `L'/L(s, χ) ≪ log² B(t)` in a zero-free strip, `χ` non-principal

Lab proof, unit U-5201, CLOUD 20261019T0514Z-cloud17. AI wrote this file. Known mathematics,
Davenport ch. 16 and 19, no cited input. It is the bound on the logarithmic derivative that the
contour shift for `ψ(x, χ)` needs on its left vertical line, the remaining analytic input of
Siegel-Walfisz besides Siegel's theorem.

With `c = 3/2 + it` and `B(t) = 2NZ(|t| + 3)` as in LogDeriv.lean:
* `zero_count_le`: the zeros of `L(s, χ)` in the disc `‖s - c‖ ≤ 3/4`, with multiplicity, number
  at most `log B(t) / log(10/9)`, by Jensen's formula in the form `ZerosBound` of the ported
  StrongPNT file, Apache-2.0, the PrimeNumberTheoremAnd contributors;
* `logDeriv_le_of_dist`: if `s` with `‖s - c‖ ≤ 2/3` keeps distance at least `η` from every
  zero in that disc, then `‖L'/L(s, χ)‖ ≤ K₀ log B(t) + log B(t) / (η log(10/9))`;
* `logDeriv_strip_le`: if every zero `ρ` with `‖ρ - c‖ ≤ 3/4` has
  `Re ρ ≤ 1 - c₀ / log B(Im ρ)`, then `‖L'/L(σ + it, χ)‖ ≤ K log² B(t)` for
  `1 - (2c₀/5) / log B(t) ≤ σ ≤ 2`, with `K = K₀ + 5 / (2 c₀ log(10/9))`.
The constants do not depend on `N` or `t`.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter Metric

variable {N : ℕ} [NeZero N]

/-- The zeros of `fShift χ t` in the disc of radius `3/4`, as a finset. -/
noncomputable def zset {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) : Finset ℂ :=
  (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) (fShift_finite_zeros hχ t)).toFinset

lemma mem_zset {χ : DirichletCharacter ℂ N} {hχ : χ ≠ 1} {t : ℝ} {ρ : ℂ} :
    ρ ∈ zset hχ t ↔ ‖ρ‖ ≤ 3 / 4 ∧ fShift χ t ρ = 0 := by
  unfold zset; rw [Set.Finite.mem_toFinset]; rfl

/-- `fShift` normalized to take the value `1` at the centre. -/
noncomputable def gNorm (χ : DirichletCharacter ℂ N) (t : ℝ) : ℂ → ℂ :=
  fun z ↦ fShift χ t z / fShift χ t 0

lemma gNorm_setup {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) :
    AnalyticOnNhd ℂ (gNorm χ t) (closedBall (0 : ℂ) 1) ∧ gNorm χ t 0 = 1 ∧
    (∀ R, SetOfZeros R (gNorm χ t) = SetOfZeros R (fShift χ t)) ∧
    (∀ w : ℂ, ‖w‖ ≤ 5 / 6 → ‖gNorm χ t w‖ ≤ Bt N t) := by
  set f := fShift χ t with hf
  have f0 : f 0 ≠ 0 := fShift_zero_ne χ t
  refine ⟨fun z _ ↦ (fShift_analyticAt hχ t z).div_const, by simp [gNorm, ← hf, f0], ?_, ?_⟩
  · intro R; ext ρ; simp [SetOfZeros, gNorm, ← hf, f0]
  · intro w hw
    have h1 := norm_LFunction_disc hχ t hw
    have h2 := norm_LFunction_ge χ t
    have hf0 : ‖f 0‖ = ‖DirichletCharacter.LFunction χ ((3 : ℂ) / 2 + I * t)‖ := by
      simp [hf, fShift]
    have hpos : 0 < ‖f 0‖ := norm_pos_iff.mpr f0
    simp only [gNorm, ← hf]
    rw [norm_div, div_le_iff₀ hpos]
    have hZ := Z_pos
    have : 1 ≤ Z * ‖f 0‖ := by
      rw [hf0]; rw [div_le_iff₀ hZ] at h2; linarith
    unfold Bt
    have hb : 0 ≤ 2 * (N : ℝ) * (|t| + 3) := by positivity
    calc ‖f w‖ ≤ 2 * N * (|t| + 3) := h1
      _ ≤ 2 * N * (|t| + 3) * (Z * ‖f 0‖) := le_mul_of_one_le_right hb this
      _ = 2 * N * (|t| + 3) * Z * ‖f 0‖ := by ring

/-- Jensen: the zeros in the disc of radius `3/4`, with multiplicity, number at most
`log B(t) / log(10/9)`. -/
theorem zero_count_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) :
    (∑ ρ ∈ zset hχ t, (analyticOrderNatAt (fShift χ t) ρ : ℝ)) ≤
      Real.log (Bt N t) / Real.log (10 / 9) := by
  obtain ⟨gA, g0, hz, gB⟩ := gNorm_setup hχ t
  have gFinite : (SetOfZeros 1 (gNorm χ t)).Finite := by
    rw [hz]; exact fShift_finite_zeros hχ t
  have key := ZerosBound (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
    (by norm_num : (3 / 4 : ℝ) < 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1) gA g0 gFinite gB
  have hset : (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) gFinite).toFinset =
      zset hχ t := by
    unfold zset; simp only [Set.Finite.toFinset_inj]; exact hz _
  have hord : ∀ ρ, analyticOrderNatAt (gNorm χ t) ρ = analyticOrderNatAt (fShift χ t) ρ :=
    fun ρ ↦ analyticOrderNatAt_fun_div_const (fShift_zero_ne χ t) (fShift_analyticAt hχ t ρ)
  rw [hset] at key
  simp only [hord] at key
  have e : (5 / 6 : ℝ) / (3 / 4) = 10 / 9 := by norm_num
  rw [e] at key
  push_cast at key
  calc (∑ ρ ∈ zset hχ t, (analyticOrderNatAt (fShift χ t) ρ : ℝ))
      ≤ 1 / Real.log (10 / 9) * Real.log (Bt N t) := key
    _ = Real.log (Bt N t) / Real.log (10 / 9) := by ring

/-- If `z`, `‖z‖ ≤ 2/3`, not a zero, keeps distance `η > 0` from every zero of `fShift` in the
disc of radius `3/4`, then `‖f'/f(z)‖ ≤ K₀ log B(t) + log B(t) / (η log(10/9))`. -/
theorem fShift_logDeriv_le_of_dist {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) {z : ℂ}
    (hz : ‖z‖ ≤ 2 / 3) (hfz : fShift χ t z ≠ 0) {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ ∈ zset hχ t, η ≤ ‖z - ρ‖) :
    ‖deriv (fShift χ t) z / fShift χ t z‖ ≤
      K0 * Real.log (Bt N t) + Real.log (Bt N t) / Real.log (10 / 9) / η := by
  have hz' : z ∈ closedBall (0 : ℂ) (2 / 3) \ SetOfZeros (4 / 5) (fShift χ t) :=
    ⟨mem_closedBall_zero_iff.mpr hz, fun h ↦ hfz h.2⟩
  have key := logDeriv_sub_sum_le hχ t hz'
  set S := ∑ ρ ∈ zset hχ t, (analyticOrderNatAt (fShift χ t) ρ : ℂ) / (z - ρ) with hS
  have key' : ‖deriv (fShift χ t) z / fShift χ t z - S‖ ≤ K0 * Real.log (Bt N t) := key
  have hSle : ‖S‖ ≤ Real.log (Bt N t) / Real.log (10 / 9) / η := by
    calc ‖S‖ ≤ ∑ ρ ∈ zset hχ t, ‖(analyticOrderNatAt (fShift χ t) ρ : ℂ) / (z - ρ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ ρ ∈ zset hχ t, (analyticOrderNatAt (fShift χ t) ρ : ℝ) / η := by
          apply Finset.sum_le_sum; intro ρ hρ
          rw [norm_div, Complex.norm_natCast]
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hη (hd ρ hρ)
      _ = (∑ ρ ∈ zset hχ t, (analyticOrderNatAt (fShift χ t) ρ : ℝ)) / η := by
          rw [Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right (zero_count_le hχ t) hη.le
  calc ‖deriv (fShift χ t) z / fShift χ t z‖
      = ‖(deriv (fShift χ t) z / fShift χ t z - S) + S‖ := by rw [sub_add_cancel]
    _ ≤ ‖deriv (fShift χ t) z / fShift χ t z - S‖ + ‖S‖ := norm_add_le _ _
    _ ≤ _ := add_le_add key' hSle

/-- The same for `L(s, χ)`: if `‖s - (3/2 + it)‖ ≤ 2/3`, `L(s, χ) ≠ 0`, and every zero `ρ` with
`‖ρ - (3/2 + it)‖ ≤ 3/4` has `‖s - ρ‖ ≥ η > 0`, then
`‖L'/L(s, χ)‖ ≤ K₀ log B(t) + log B(t) / (η log(10/9))`. -/
theorem logDeriv_le_of_dist {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) {s : ℂ}
    (hs : ‖s - ((3 : ℂ) / 2 + I * t)‖ ≤ 2 / 3) (hLs : DirichletCharacter.LFunction χ s ≠ 0)
    {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖ρ - ((3 : ℂ) / 2 + I * t)‖ ≤ 3 / 4 →
      η ≤ ‖s - ρ‖) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      K0 * Real.log (Bt N t) + Real.log (Bt N t) / Real.log (10 / 9) / η := by
  set c : ℂ := (3 : ℂ) / 2 + I * t with hc
  set z := s - c with hzdef
  have he : z + c = s := by rw [hzdef, sub_add_cancel]
  have hv : fShift χ t z = DirichletCharacter.LFunction χ s := by
    show DirichletCharacter.LFunction χ (z + c) = _
    rw [he]
  have hdv : deriv (fShift χ t) z = deriv (DirichletCharacter.LFunction χ) s := by
    show deriv (fun w ↦ DirichletCharacter.LFunction χ (w + c)) z = _
    rw [deriv_comp_add_const, he]
  have key := fShift_logDeriv_le_of_dist hχ t (z := z) hs (by rw [hv]; exact hLs) hη
    (fun ρ hρ ↦ by
      obtain ⟨h1, h2⟩ := mem_zset.mp hρ
      have h0 : DirichletCharacter.LFunction χ (ρ + c) = 0 := h2
      have := hd (ρ + c) h0 (by rw [add_sub_cancel_right]; exact h1)
      have e : s - (ρ + c) = z - ρ := by rw [hzdef]; ring
      rwa [e] at this)
  rwa [hdv, hv] at key

lemma log_Bt_shift_le (t γ : ℝ) (h : |γ - t| ≤ 3 / 4) :
    Real.log (Bt N γ) ≤ 5 / 4 * Real.log (Bt N t) := by
  have hL := one_le_log_Bt (N := N) t
  have hBt : 0 < Bt N t := lt_trans one_pos (one_lt_Bt t)
  have hle : Bt N γ ≤ 5 / 4 * Bt N t := by
    unfold Bt
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hZ := Z_pos
    have hγ : |γ| ≤ |t| + 3 / 4 := by
      have := abs_sub_abs_le_abs_sub γ t; linarith
    have ht := abs_nonneg t
    have : |γ| + 3 ≤ 5 / 4 * (|t| + 3) := by linarith
    have h2 : 0 ≤ 2 * (N : ℝ) * Z := by positivity
    calc 2 * (N : ℝ) * (|γ| + 3) * Z = (2 * N * Z) * (|γ| + 3) := by ring
      _ ≤ (2 * N * Z) * (5 / 4 * (|t| + 3)) := mul_le_mul_of_nonneg_left this h2
      _ = 5 / 4 * (2 * N * (|t| + 3) * Z) := by ring
  have hpos : 0 < Bt N γ := lt_trans one_pos (one_lt_Bt γ)
  calc Real.log (Bt N γ) ≤ Real.log (5 / 4 * Bt N t) := Real.log_le_log hpos hle
    _ = Real.log (5 / 4) + Real.log (Bt N t) := Real.log_mul (by norm_num) hBt.ne'
    _ ≤ 1 / 4 + Real.log (Bt N t) := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4); linarith
    _ ≤ 5 / 4 * Real.log (Bt N t) := by linarith

/-- **The strip bound.** If every zero `ρ` of `L(s, χ)` with `‖ρ - (3/2 + it)‖ ≤ 3/4` satisfies
`Re ρ ≤ 1 - c₀ / log B(Im ρ)`, `0 < c₀ ≤ 5/12`, then for `1 - (2c₀/5)/log B(t) ≤ σ ≤ 2`,
`‖L'/L(σ + it, χ)‖ ≤ (K₀ + 5 / (2 c₀ log(10/9))) log² B(t)`. -/
theorem logDeriv_strip_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ ≤ 5 / 12) (t σ : ℝ)
    (hzf : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖ρ - ((3 : ℂ) / 2 + I * t)‖ ≤ 3 / 4 →
      ρ.re ≤ 1 - c₀ / Real.log (Bt N ρ.im))
    (hσ1 : 1 - 2 * c₀ / 5 / Real.log (Bt N t) ≤ σ) (hσ2 : σ ≤ 2) :
    ‖deriv (DirichletCharacter.LFunction χ) (σ + I * t) /
        DirichletCharacter.LFunction χ (σ + I * t)‖ ≤
      (K0 + 5 / (2 * c₀ * Real.log (10 / 9))) * Real.log (Bt N t) ^ 2 := by
  set L := Real.log (Bt N t) with hLdef
  have hL : 1 ≤ L := one_le_log_Bt t
  have hLpos : 0 < L := by linarith
  set c : ℂ := (3 : ℂ) / 2 + I * t with hc
  set s : ℂ := σ + I * t with hsdef
  have hsc : s - c = ((σ - 3 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hsdef, hc]
  have hσ56 : 5 / 6 ≤ σ := by
    have : 2 * c₀ / 5 / L ≤ 1 / 6 := by
      rw [div_le_iff₀ hLpos]; nlinarith
    linarith
  have hs : ‖s - c‖ ≤ 2 / 3 := by
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
  set η := 2 * c₀ / 5 / L with hη
  have hηpos : 0 < η := by positivity
  -- every zero in the disc is at distance at least `η`
  have hdist : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖ρ - c‖ ≤ 3 / 4 →
      η ≤ σ - ρ.re := by
    intro ρ hρ hρc
    have him : |ρ.im - t| ≤ 3 / 4 := by
      have := Complex.abs_im_le_norm (ρ - c)
      have e : (ρ - c).im = ρ.im - t := by simp [hc]
      rw [e] at this; linarith
    have hlog := log_Bt_shift_le (N := N) t ρ.im him
    have hLγ : 0 < Real.log (Bt N ρ.im) := by linarith [one_le_log_Bt (N := N) ρ.im]
    have hβ := hzf ρ hρ hρc
    have h1 : 4 * c₀ / 5 / L ≤ c₀ / Real.log (Bt N ρ.im) := by
      rw [div_le_div_iff₀ hLpos hLγ]; nlinarith
    have h2 : 4 * c₀ / 5 / L = 2 * η := by rw [hη]; ring
    linarith
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro h0
    have := hdist s h0 (hs.trans (by norm_num))
    have e : s.re = σ := by simp [hsdef]
    rw [e, sub_self] at this; linarith
  have key := logDeriv_le_of_dist hχ t hs hLs hηpos (fun ρ hρ hρc ↦ by
    have h := hdist ρ hρ hρc
    have e : (s - ρ).re = σ - ρ.re := by simp [hsdef]
    have := Complex.re_le_norm (s - ρ)
    linarith)
  have hK0 := K0_pos
  have hl109 : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  have e2 : L / Real.log (10 / 9) / η = 5 / (2 * c₀ * Real.log (10 / 9)) * L ^ 2 := by
    rw [hη]; field_simp
  rw [e2] at key
  calc _ ≤ K0 * L + 5 / (2 * c₀ * Real.log (10 / 9)) * L ^ 2 := key
    _ ≤ K0 * L ^ 2 + 5 / (2 * c₀ * Real.log (10 / 9)) * L ^ 2 := by
        have : K0 * L ≤ K0 * L ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hK0.le
        linarith
    _ = _ := by ring

/-- **The strip bound at a free scale `L ≥ log B(t)`.** If every zero `ρ` of `L(s, χ)` with
`‖ρ - (3/2 + it)‖ ≤ 3/4` has `Re ρ ≤ 1 - c₀ / log B(Im ρ)` or lies at distance at least
`(2c₀/5)/L` from `σ + it`, `0 < c₀ ≤ 5/12`, then for `1 - (2c₀/5)/L ≤ σ ≤ 2`,
`‖L'/L(σ + it, χ)‖ ≤ (K₀ + 5 / (2 c₀ log(10/9))) L²`. -/
theorem logDeriv_strip_le_L {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ ≤ 5 / 12) (t σ L : ℝ) (hL : Real.log (Bt N t) ≤ L)
    (hzf : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖ρ - ((3 : ℂ) / 2 + I * t)‖ ≤ 3 / 4 →
      ρ.re ≤ 1 - c₀ / Real.log (Bt N ρ.im) ∨ 2 * c₀ / 5 / L ≤ ‖((σ : ℂ) + I * t) - ρ‖)
    (hσ1 : 1 - 2 * c₀ / 5 / L ≤ σ) (hσ2 : σ ≤ 2) :
    ‖deriv (DirichletCharacter.LFunction χ) (σ + I * t) /
        DirichletCharacter.LFunction χ (σ + I * t)‖ ≤
      (K0 + 5 / (2 * c₀ * Real.log (10 / 9))) * L ^ 2 := by
  set Lt := Real.log (Bt N t) with hLtdef
  have hLt : 1 ≤ Lt := one_le_log_Bt t
  have hL1 : 1 ≤ L := hLt.trans hL
  have hLpos : 0 < L := by linarith
  set c : ℂ := (3 : ℂ) / 2 + I * t with hc
  set s : ℂ := σ + I * t with hsdef
  have hsc : s - c = ((σ - 3 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hsdef, hc]
  have hσ56 : 5 / 6 ≤ σ := by
    have : 2 * c₀ / 5 / L ≤ 1 / 6 := by
      rw [div_le_iff₀ hLpos]; nlinarith
    linarith
  have hs : ‖s - c‖ ≤ 2 / 3 := by
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
  set η := 2 * c₀ / 5 / L with hη
  have hηpos : 0 < η := by positivity
  have hdist : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖ρ - c‖ ≤ 3 / 4 →
      η ≤ ‖s - ρ‖ := by
    intro ρ hρ hρc
    rcases hzf ρ hρ hρc with hβ | hfar
    · have him : |ρ.im - t| ≤ 3 / 4 := by
        have := Complex.abs_im_le_norm (ρ - c)
        have e : (ρ - c).im = ρ.im - t := by simp [hc]
        rw [e] at this; linarith
      have hlog := log_Bt_shift_le (N := N) t ρ.im him
      have hLγ : 0 < Real.log (Bt N ρ.im) := by linarith [one_le_log_Bt (N := N) ρ.im]
      have h1 : 4 * c₀ / 5 / L ≤ c₀ / Real.log (Bt N ρ.im) := by
        rw [div_le_div_iff₀ hLpos hLγ]; nlinarith
      have h2 : 4 * c₀ / 5 / L = 2 * η := by rw [hη]; ring
      have e : (s - ρ).re = σ - ρ.re := by simp [hsdef]
      have := Complex.re_le_norm (s - ρ)
      linarith
    · exact hfar
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro h0
    have := hdist s h0 (hs.trans (by norm_num))
    rw [sub_self, norm_zero] at this; linarith
  have key := logDeriv_le_of_dist hχ t hs hLs hηpos hdist
  have hK0 := K0_pos
  have hl109 : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  have e2 : L / Real.log (10 / 9) / η = 5 / (2 * c₀ * Real.log (10 / 9)) * L ^ 2 := by
    rw [hη]; field_simp
  have hmono : Lt / Real.log (10 / 9) / η ≤ L / Real.log (10 / 9) / η := by
    gcongr
  calc _ ≤ K0 * Lt + Lt / Real.log (10 / 9) / η := key
    _ ≤ K0 * L + L / Real.log (10 / 9) / η := by
        have : K0 * Lt ≤ K0 * L := mul_le_mul_of_nonneg_left hL hK0.le
        linarith
    _ = K0 * L + 5 / (2 * c₀ * Real.log (10 / 9)) * L ^ 2 := by rw [e2]
    _ ≤ K0 * L ^ 2 + 5 / (2 * c₀ * Real.log (10 / 9)) * L ^ 2 := by
        have : K0 * L ≤ K0 * L ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hK0.le
        linarith
    _ = _ := by ring

lemma log_Bt_mono {t T : ℝ} (h : |t| ≤ |T|) : Real.log (Bt N t) ≤ Real.log (Bt N T) := by
  apply Real.log_le_log (lt_trans one_pos (one_lt_Bt t))
  unfold Bt
  have hZ := Z_pos
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have : 2 * (N : ℝ) * (|t| + 3) ≤ 2 * N * (|T| + 3) := by nlinarith
  exact mul_le_mul_of_nonneg_right this hZ.le

end LeanLab.PNTPort.DirichletZF

