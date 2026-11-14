module

public import LeanLab.PNTPort.StrongPNT.StrongPNT
public import LeanLab.PNTPort.DirichletZF.Growth

/-!
# A local bound for `L'/L(s, χ)` near `Re s = 1`, `χ` non-principal

Lab proof, unit U-5110. AI wrote this file. Known mathematics, no cited input. It applies the
Borel-Caratheodory bound `FinalBound` of the ported StrongPNT file, Apache-2.0, the
PrimeNumberTheoremAnd contributors, to `f(z) = L(z + 3/2 + it, χ)`, exactly as StrongPNT does
for `ζ`, with the growth input `norm_LFunction_le` of Growth.lean.

* `norm_LFunction_ge`: `‖L(3/2 + it, χ)‖ ≥ 1/Z` with `Z = ∑ n^{-3/2}`, from `L · L(χμ) = 1`;
* `norm_LFunction_disc`: `‖L(z + 3/2 + it, χ)‖ ≤ 2N(|t| + 3)` for `‖z‖ ≤ 5/6`;
* `logDeriv_sub_sum_le`: on `‖z‖ ≤ 2/3`, `L'/L` minus the sum over its zeros in the disc of
  radius `3/4` is at most `K log(2NZ(|t| + 3))`, with `K` an absolute constant;
* `shiftOne_bound`: for `0 < δ < 1` and any zero `ρ = β + it` of `L(s, χ)`,
  `-Re L'/L(1 + δ + it, χ) ≤ K log(2NZ(|t| + 3)) + 4 - 1/(1 + δ - β)`;
* `shiftAny_bound`: for `0 < δ < 1`, `-Re L'/L(1 + δ + it, χ) ≤ K log(2NZ(|t| + 3))`.
The constants do not depend on `N` or `t`, which is the uniformity Siegel-Walfisz needs.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter Metric
open scoped LSeries.notation ArithmeticFunction.Moebius

variable {N : ℕ} [NeZero N]

/-- `Z = ∑_{n ≥ 1} n^{-3/2}`. -/
noncomputable def Z : ℝ := ∑' n : ℕ, ‖LSeries.term 1 ((3 : ℂ) / 2) n‖

lemma summable_Z : Summable fun n : ℕ ↦ ‖LSeries.term 1 ((3 : ℂ) / 2) n‖ :=
  (LSeriesSummable_one_iff.mpr (by norm_num)).norm

lemma one_le_Z : 1 ≤ Z := by
  have h1 : ‖LSeries.term 1 ((3 : ℂ) / 2) 1‖ = 1 := by simp [LSeries.term]
  rw [← h1]
  exact summable_Z.le_tsum 1 (fun n _ ↦ norm_nonneg _)

lemma Z_pos : 0 < Z := lt_of_lt_of_le one_pos one_le_Z

/-- An L-series with coefficients of norm at most one is at most `Z` on `Re s = 3/2`. -/
lemma norm_LSeries_le_Z {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t : ℝ) :
    ‖LSeries f ((3 : ℂ) / 2 + I * t)‖ ≤ Z := by
  set s : ℂ := (3 : ℂ) / 2 + I * t
  have hb : ∀ n, ‖LSeries.term f s n‖ ≤ ‖LSeries.term 1 ((3 : ℂ) / 2) n‖ := fun n ↦
    (LSeries.norm_term_le s (g := 1) (by simpa using hf n)).trans
      (LSeries.norm_term_le_of_re_le_re _ (by simp [s]) n)
  have hs : Summable fun n ↦ ‖LSeries.term f s n‖ :=
    summable_Z.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  calc ‖LSeries f s‖ = ‖∑' n, LSeries.term f s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ Z := hs.tsum_le_tsum hb summable_Z

lemma re_c (t : ℝ) : ((3 : ℂ) / 2 + I * t).re = 3 / 2 := by simp

/-- `‖L(3/2 + it, χ)‖ ≥ 1/Z`. -/
lemma norm_LFunction_ge (χ : DirichletCharacter ℂ N) (t : ℝ) :
    1 / Z ≤ ‖DirichletCharacter.LFunction χ ((3 : ℂ) / 2 + I * t)‖ := by
  have hs : 1 < ((3 : ℂ) / 2 + I * t).re := by rw [re_c]; norm_num
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have h := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hb : ‖LSeries (↗χ * ↗μ) ((3 : ℂ) / 2 + I * t)‖ ≤ Z := by
    refine norm_LSeries_le_Z (fun n ↦ ?_) t
    simp only [Pi.mul_apply, norm_mul]
    have h1 := χ.norm_le_one n
    have h2 : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    nlinarith [norm_nonneg (χ n), norm_nonneg ((μ n : ℤ) : ℂ)]
  have hprod : ‖LSeries ↗χ ((3 : ℂ) / 2 + I * t)‖ *
      ‖LSeries (↗χ * ↗μ) ((3 : ℂ) / 2 + I * t)‖ = 1 := by
    rw [← norm_mul, h, norm_one]
  rw [div_le_iff₀ Z_pos]
  nlinarith [norm_nonneg (LSeries ↗χ ((3 : ℂ) / 2 + I * t))]

lemma LFunction_c_ne_zero (χ : DirichletCharacter ℂ N) (t : ℝ) :
    DirichletCharacter.LFunction χ ((3 : ℂ) / 2 + I * t) ≠ 0 := by
  intro h
  have := norm_LFunction_ge χ t
  rw [h, norm_zero] at this
  have := Z_pos
  have : 0 < 1 / Z := by positivity
  linarith

/-- The growth bound on the disc of radius `5/6` about `3/2 + it`. -/
lemma norm_LFunction_disc {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) {z : ℂ}
    (hz : ‖z‖ ≤ 5 / 6) :
    ‖DirichletCharacter.LFunction χ (z + ((3 : ℂ) / 2 + I * t))‖ ≤ 2 * N * (|t| + 3) := by
  set s := z + ((3 : ℂ) / 2 + I * t) with hs
  have hzre : |z.re| ≤ 5 / 6 := (Complex.abs_re_le_norm z).trans hz
  have hre : 2 / 3 ≤ s.re := by
    rw [hs, add_re, re_c]; linarith [(abs_le.mp hzre).1]
  have hnorm : ‖s‖ ≤ |t| + 3 := by
    have h1 : ‖(3 : ℂ) / 2‖ = 3 / 2 := by
      rw [norm_div]; simp
    have h2 : ‖I * (t : ℂ)‖ = |t| := by simp
    calc ‖s‖ ≤ ‖z‖ + (‖(3 : ℂ) / 2‖ + ‖I * (t : ℂ)‖) :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ |t| + 3 := by rw [h1, h2]; linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc ‖DirichletCharacter.LFunction χ s‖ ≤ N * ‖s‖ / s.re :=
        norm_LFunction_le hχ (by linarith)
    _ ≤ N * (|t| + 3) / (2 / 3) := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnorm hN) (by norm_num) hre
    _ ≤ 2 * N * (|t| + 3) := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith [abs_nonneg t]

/-- The shifted function `f(z) = L(z + 3/2 + it, χ)`. -/
noncomputable def fShift (χ : DirichletCharacter ℂ N) (t : ℝ) : ℂ → ℂ :=
  fun z ↦ DirichletCharacter.LFunction χ (z + ((3 : ℂ) / 2 + I * t))

lemma fShift_differentiable {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) :
    Differentiable ℂ (fShift χ t) :=
  (DirichletCharacter.differentiable_LFunction hχ).comp (differentiable_id.add_const _)

lemma fShift_analyticAt {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) (z : ℂ) :
    AnalyticAt ℂ (fShift χ t) z :=
  (fShift_differentiable hχ t).analyticAt z

lemma fShift_zero_ne (χ : DirichletCharacter ℂ N) (t : ℝ) : fShift χ t 0 ≠ 0 := by
  simpa [fShift] using LFunction_c_ne_zero χ t

/-- The zeros of `fShift` in the closed unit disc are finite. -/
lemma fShift_finite_zeros {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) :
    (SetOfZeros 1 (fShift χ t)).Finite := by
  by_contra hinf; rw [Set.not_finite] at hinf
  have zerosSubset : SetOfZeros 1 (fShift χ t) ⊆ closedBall (0 : ℂ) 1 := fun _ hx ↦ by
    simpa only [mem_closedBall, dist_zero_right] using hx.1
  obtain ⟨x, hxK, hacc⟩ :=
    hinf.exists_accPt_of_subset_isCompact (isCompact_closedBall 0 1) zerosSubset
  have hfAnalytic : AnalyticOnNhd ℂ (fShift χ t) (ball (0 : ℂ) 2) :=
    fun z _ ↦ fShift_analyticAt hχ t z
  have hfeq : Set.EqOn (fShift χ t) 0 (ball (0 : ℂ) 2) := by
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hfAnalytic
      isPreconnected_ball (z₀ := x) ?_ ?_
    · simp only [mem_ball, mem_closedBall, dist_zero_right] at hxK ⊢
      linarith
    · simp only [mem_closure_iff_clusterPt, ← accPt_principal_iff_clusterPt]
      exact hacc.mono (principal_mono.mpr fun _ h ↦ h.2)
  exact fShift_zero_ne χ t (hfeq (mem_ball_self (by norm_num)))

/-- The explicit `FinalBound` constant at `r' = 2/3`, `r = 3/4`, `R' = 4/5`, `R = 5/6`. -/
noncomputable def K0 : ℝ :=
  16 * (3 / 4 : ℝ) ^ 2 / (3 / 4 - 2 / 3) ^ 3 +
    1 / (((5 / 6 : ℝ) ^ 2 / (4 / 5) - 4 / 5) * Real.log ((5 / 6) / (4 / 5)))

lemma K0_pos : 0 < K0 := by
  unfold K0
  have : 0 < Real.log ((5 / 6 : ℝ) / (4 / 5)) := Real.log_pos (by norm_num)
  have : (0 : ℝ) < (5 / 6 : ℝ) ^ 2 / (4 / 5) - 4 / 5 := by norm_num
  positivity

/-- `B(t) = 2NZ(|t| + 3)`, the bound for `f/f(0)` on the disc of radius `5/6`. -/
noncomputable def Bt (N : ℕ) (t : ℝ) : ℝ := 2 * N * (|t| + 3) * Z

lemma one_lt_Bt (t : ℝ) : 1 < Bt N t := by
  unfold Bt
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hZ := one_le_Z
  have ht := abs_nonneg t
  have h1 : (1 : ℝ) ≤ 2 * N * (|t| + 3) := by nlinarith
  nlinarith

/-- The Borel-Caratheodory bound for `L'/L` minus its nearby zeros. -/
theorem logDeriv_sub_sum_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) (2 / 3) \ SetOfZeros (4 / 5) (fShift χ t)) :
    ‖deriv (fShift χ t) z / fShift χ t z -
      ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1)
        (fShift_finite_zeros hχ t)).toFinset,
        analyticOrderNatAt (fShift χ t) ρ / (z - ρ)‖ ≤ K0 * Real.log (Bt N t) := by
  set f := fShift χ t with hf
  have f0 : f 0 ≠ 0 := fShift_zero_ne χ t
  have hfz : f z ≠ 0 := by
    intro h
    exact hz.2 ⟨(mem_closedBall_zero_iff.mp hz.1).trans (by norm_num), h⟩
  set g : ℂ → ℂ := fun z ↦ f z / f 0 with hg
  have gAnalytic : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) 1) :=
    fun z _ ↦ (fShift_analyticAt hχ t z).div_const
  have g0 : g 0 = 1 := by simp [hg, f0]
  have hzeros : ∀ R, SetOfZeros R g = SetOfZeros R f := by
    intro R; ext ρ; simp [SetOfZeros, hg, f0]
  have gFinite : (SetOfZeros 1 g).Finite := by
    rw [hzeros]; exact fShift_finite_zeros hχ t
  have gBound : ∀ w : ℂ, ‖w‖ ≤ 5 / 6 → ‖g w‖ ≤ Bt N t := by
    intro w hw
    have h1 := norm_LFunction_disc hχ t hw
    have h2 := norm_LFunction_ge χ t
    have hf0 : ‖f 0‖ = ‖DirichletCharacter.LFunction χ ((3 : ℂ) / 2 + I * t)‖ := by
      simp [hf, fShift]
    have hpos : 0 < ‖f 0‖ := norm_pos_iff.mpr f0
    rw [hg, norm_div, div_le_iff₀ hpos]
    have hZ := Z_pos
    have : 1 ≤ Z * ‖f 0‖ := by
      rw [hf0]; rw [div_le_iff₀ hZ] at h2; linarith
    unfold Bt
    have hb : 0 ≤ 2 * (N : ℝ) * (|t| + 3) := by positivity
    calc ‖f w‖ ≤ 2 * N * (|t| + 3) := h1
      _ ≤ 2 * N * (|t| + 3) * (Z * ‖f 0‖) := le_mul_of_one_le_right hb this
      _ = 2 * N * (|t| + 3) * Z * ‖f 0‖ := by ring
  have ghz : z ∈ closedBall (0 : ℂ) (2 / 3) \ SetOfZeros (4 / 5) g := by
    rw [hzeros]; exact hz
  have key := FinalBound (one_lt_Bt t) (by norm_num : (0 : ℝ) < 2 / 3)
    (by norm_num : (2 / 3 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
    (by norm_num : (3 / 4 : ℝ) < 4 / 5) (by norm_num : (4 / 5 : ℝ) < 5 / 6)
    (by norm_num : (5 / 6 : ℝ) < 1) gAnalytic g0 gFinite gBound ghz
  have hset : (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1) gFinite).toFinset =
      (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1)
        (fShift_finite_zeros hχ t)).toFinset := by
    simp only [Set.Finite.toFinset_inj]; exact hzeros _
  rw [hset] at key
  have hderiv : deriv g z / g z = deriv f z / f z := by
    have : deriv g z = deriv f z / f 0 := by
      simp only [hg]; rw [deriv_div_const]
    rw [this]; simp only [hg]; field_simp
  have hord : ∀ ρ, analyticOrderNatAt g ρ = analyticOrderNatAt f ρ := fun ρ ↦
    analyticOrderNatAt_fun_div_const f0 (fShift_analyticAt hχ t ρ)
  simp only [hderiv, hord] at key
  convert key using 2
  rfl

lemma re_natCast_div_nonneg (n : ℕ) {w : ℂ} (hw : 0 ≤ w.re) : 0 ≤ ((n : ℂ) / w).re := by
  rw [Complex.div_re]
  simp only [natCast_re, natCast_im, zero_mul, add_zero, zero_div]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hw) (normSq_nonneg w)

lemma one_le_order {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) {ρ : ℂ}
    (hρ : fShift χ t ρ = 0) : 1 ≤ analyticOrderNatAt (fShift χ t) ρ := by
  simp only [Nat.one_le_iff_ne_zero, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero,
    analyticOrderAt_eq_zero, analyticOrderAt_eq_top, not_or, not_not]
  refine ⟨⟨fShift_analyticAt hχ t ρ, hρ⟩, fun h ↦ ?_⟩
  have hU : AnalyticOnNhd ℂ (fShift χ t) univ := fun z _ ↦ fShift_analyticAt hχ t z
  have := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ ρ)
    (by simpa [EventuallyEq] using h) (mem_univ 0)
  exact fShift_zero_ne χ t this

/-- The setting of the shift bounds: `z = d - 1/2`, so `z + 3/2 + it = 1 + d + it`. -/
lemma shift_setup {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) {d : ℝ} (hd0 : d ∈ Ioo 0 1) :
    ((d : ℂ) - 1 / 2) ∈ closedBall (0 : ℂ) (2 / 3) \ SetOfZeros (4 / 5) (fShift χ t) ∧
    ((d : ℂ) - 1 / 2) + ((3 : ℂ) / 2 + I * t) = 1 + d + I * t := by
  have hn : ‖(d : ℂ) - 1 / 2‖ ≤ 1 / 2 := by
    have : (d : ℂ) - 1 / 2 = ((d - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hd0.1, hd0.2]
  have he : ((d : ℂ) - 1 / 2) + ((3 : ℂ) / 2 + I * t) = 1 + d + I * t := by ring
  refine ⟨⟨mem_closedBall_zero_iff.mpr (hn.trans (by norm_num)), fun h ↦ ?_⟩, he⟩
  have h2 := h.2
  simp only [fShift, he] at h2
  refine DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) ?_ h2
  simp; linarith [hd0.1]

/-- With no zero in hand: `-Re L'/L(1 + d + it, χ) ≤ K₀ log B(t)`. -/
theorem shiftAny_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) {d : ℝ}
    (hd0 : d ∈ Ioo 0 1) :
    -(deriv (DirichletCharacter.LFunction χ) (1 + d + I * t) /
        DirichletCharacter.LFunction χ (1 + d + I * t)).re ≤ K0 * Real.log (Bt N t) := by
  obtain ⟨hz, he⟩ := shift_setup hχ t hd0
  have key := logDeriv_sub_sum_le hχ t hz
  set z : ℂ := (d : ℂ) - 1 / 2
  set T := (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1)
    (fShift_finite_zeros hχ t)).toFinset
  have hd : deriv (fShift χ t) z = deriv (DirichletCharacter.LFunction χ) (1 + d + I * t) := by
    show deriv (fun w ↦ DirichletCharacter.LFunction χ (w + ((3 : ℂ) / 2 + I * t))) z = _
    rw [deriv_comp_add_const, he]
  have hv : fShift χ t z = DirichletCharacter.LFunction χ (1 + d + I * t) := by
    show DirichletCharacter.LFunction χ (z + ((3 : ℂ) / 2 + I * t)) = _
    rw [he]
  rw [hd, hv] at key
  have hS : 0 ≤ (∑ ρ ∈ T, (analyticOrderNatAt (fShift χ t) ρ : ℂ) / (z - ρ)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun ρ hρ ↦ re_natCast_div_nonneg _ ?_
    have hρ' := (Set.Finite.mem_toFinset _).mp hρ
    have hL : ρ + ((3 : ℂ) / 2 + I * t) ∈ {s : ℂ | s.re < 1} := by
      by_contra hc
      simp only [mem_ofPred_eq, not_lt] at hc
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hc hρ'.2
    simp only [mem_ofPred_eq] at hL
    rw [add_re, re_c] at hL
    simp [z]; linarith [hd0.1]
  have := (Complex.re_le_norm _).trans
    ((norm_neg (_ : ℂ)).le.trans key)
  rw [neg_sub, sub_re] at this
  linarith

/-- With a zero `ρ = β + it` of `L(s, χ)`:
`-Re L'/L(1 + d + it, χ) ≤ K₀ log B(t) + 4 - 1/(1 + d - β)`. -/
theorem shiftOne_bound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {d : ℝ}
    (hd0 : d ∈ Ioo 0 1) {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    -(deriv (DirichletCharacter.LFunction χ) (1 + d + I * ρ.im) /
        DirichletCharacter.LFunction χ (1 + d + I * ρ.im)).re ≤
      K0 * Real.log (Bt N ρ.im) + 4 - 1 / (1 + d - ρ.re) := by
  set t := ρ.im with ht
  have hβ : ρ.re < 1 := by
    by_contra hc; push Not at hc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hc hρ
  have hpos : 0 < 1 + d - ρ.re := by linarith [hd0.1]
  obtain ⟨hz, he⟩ := shift_setup hχ t hd0
  have key := logDeriv_sub_sum_le hχ t hz
  set z : ℂ := (d : ℂ) - 1 / 2
  set c : ℂ := (3 : ℂ) / 2 + I * t
  set T := (finiteSetOfZeros_mono (by norm_num : (3 / 4 : ℝ) < 1)
    (fShift_finite_zeros hχ t)).toFinset
  have hd : deriv (fShift χ t) z = deriv (DirichletCharacter.LFunction χ) (1 + d + I * t) := by
    show deriv (fun w ↦ DirichletCharacter.LFunction χ (w + ((3 : ℂ) / 2 + I * t))) z = _
    rw [deriv_comp_add_const, he]
  have hv : fShift χ t z = DirichletCharacter.LFunction χ (1 + d + I * t) := by
    show DirichletCharacter.LFunction χ (z + ((3 : ℂ) / 2 + I * t)) = _
    rw [he]
  rw [hd, hv] at key
  have hterm : ∀ ρ' ∈ T, 0 ≤ ((analyticOrderNatAt (fShift χ t) ρ' : ℂ) / (z - ρ')).re := by
    intro ρ' hρ'
    refine re_natCast_div_nonneg _ ?_
    have hρ'' := (Set.Finite.mem_toFinset _).mp hρ'
    have hL : (ρ' + c).re < 1 := by
      by_contra hc
      push Not at hc
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hc hρ''.2
    rw [add_re, re_c] at hL
    simp [z]; linarith [hd0.1]
  have hmain := (Complex.re_le_norm _).trans ((norm_neg (_ : ℂ)).le.trans key)
  rw [neg_sub, sub_re] at hmain
  have hlog : 0 ≤ K0 * Real.log (Bt N t) :=
    mul_nonneg K0_pos.le (Real.log_nonneg (one_lt_Bt t).le)
  have hρc : ρ - c = ((ρ.re - 3 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [c, ht]
  by_cases hin : ‖ρ - c‖ ≤ 3 / 4
  · have hmem : ρ - c ∈ T := by
      rw [Set.Finite.mem_toFinset]
      refine ⟨hin, ?_⟩
      show DirichletCharacter.LFunction χ (ρ - c + c) = 0
      rw [sub_add_cancel]; exact hρ
    have hsplit := Finset.add_sum_erase T
      (fun ρ' ↦ (analyticOrderNatAt (fShift χ t) ρ' : ℂ) / (z - ρ')) hmem
    have hrest : 0 ≤ (∑ ρ' ∈ T.erase (ρ - c),
        (analyticOrderNatAt (fShift χ t) ρ' : ℂ) / (z - ρ')).re := by
      rw [Complex.re_sum]
      exact Finset.sum_nonneg fun ρ' h ↦ hterm ρ' (Finset.mem_of_mem_erase h)
    have hzr : z - (ρ - c) = ((1 + d - ρ.re : ℝ) : ℂ) := by
      rw [hρc]; simp only [z]; push_cast; ring
    have hone : 1 / (1 + d - ρ.re) ≤
        ((analyticOrderNatAt (fShift χ t) (ρ - c) : ℂ) / (z - (ρ - c))).re := by
      have h0 : fShift χ t (ρ - c) = 0 := by
        show DirichletCharacter.LFunction χ (ρ - c + c) = 0
        rw [sub_add_cancel]; exact hρ
      have h1 : (1 : ℝ) ≤ analyticOrderNatAt (fShift χ t) (ρ - c) := by
        exact_mod_cast one_le_order hχ t h0
      rw [hzr, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
      exact div_le_div_of_nonneg_right h1 hpos.le
    rw [← hsplit, add_re] at hmain
    linarith
  · push Not at hin
    rw [hρc, Complex.norm_real, Real.norm_eq_abs] at hin
    have hβ' : ρ.re < 3 / 4 := by
      rcases lt_abs.mp hin with h | h <;> linarith
    have h4 : 1 / (1 + d - ρ.re) ≤ 4 := by
      rw [div_le_iff₀ hpos]; linarith [hd0.1]
    have hS : 0 ≤ (∑ ρ' ∈ T, (analyticOrderNatAt (fShift χ t) ρ' : ℂ) / (z - ρ')).re := by
      rw [Complex.re_sum]; exact Finset.sum_nonneg hterm
    linarith

end LeanLab.PNTPort.DirichletZF

