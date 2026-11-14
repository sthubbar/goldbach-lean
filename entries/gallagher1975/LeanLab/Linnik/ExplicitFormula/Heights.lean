module

public import LeanLab.Linnik.ExplicitFormula.LeftHalf
public import LeanLab.PNTPort.ExplicitPsi1.Edges
public import LeanLab.PNTPort.ZetaZeros.GoodHeight
public import LeanLab.HardyLittlewood1923.U1503LogDeriv
public import LeanLab.HardyLittlewood1923.U1482ZeroCount

/-!
# Good heights for `L(s, χ)`, Davenport ch. 16 and 17

AI wrote the Lean code. Binary Goldbach is OPEN.
For a fixed primitive `χ`, heights `T' ∈ [T, T+1]` with no zero on `[-1/2, 2] ± iT'` and
`|L'/L| ≤ C log²(T + 2)` there, `C` depending on `χ`. Only the limit `T' → ∞` uses these,
so no uniformity in `q` is needed here. Port of `LeanLab.PNTPort.ExplicitPsi1.Edges.good_height_pm`
with the local expansion of `L'/L` and `LeanLab.HardyLittlewood1923.U1482.zeroCountUnit`;
on `Re s < 1/2` by the functional equation.

Decomposition, all PROVED, `#print axioms good_heights` gives propext, Classical.choice,
Quot.sound only:
* `q = 1`: `L(s, χ) = ζ(s)`, and `good_height_pm` of the zeta port applies directly.
* `znear_count`: zeros with `||Im ρ| - t| ≤ 2` number `O_q(log(t + 2))`, from four unit windows of
  `U1482.zeroCountUnit`.
* `good_heights_right`: for `q ≠ 1`, one `T'` good for both `χ` and `χ⁻¹` at both `±T'` on
  `1/2 ≤ σ ≤ 2`; the port of `ZetaZeros.good_height` with `U1503.logDeriv_L_wide`.
* `logDeriv_fe_strip`: the functional equation differentiated logarithmically on `Re s ≤ 1/2`,
  `Im s ≠ 0`.
* `logDeriv_gf_strip`: Stirling for the gamma factor on `-1/2 ≤ σ ≤ 3/2`, `|t| ≥ 2`, from
  `ZetaZeros.digamma_strip`.
* `good_heights`: assembled from these.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex Set

/-- The nontrivial zeros of `L(s, ψ)` with `||Im ρ| - t| ≤ 2`. -/
def Znear {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (t : ℝ) : Set ℂ :=
  {ρ | ψ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |(|ρ.im| - t)| ≤ 2}

/-- Davenport ch. 16, from the unit window count `U1482.zeroCountUnit` over four windows: for a
fixed primitive `ψ`, the zeros in `Znear ψ t` are finite and number `O(log(t + 2))`, `t ≥ 5`. -/
theorem znear_count {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q} (hψ : ψ.IsPrimitive)
    (hq : q ≠ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 5 ≤ t → ∃ hf : (Znear ψ t).Finite,
      (hf.toFinset.card : ℝ) ≤ A * Real.log (t + 2) := by
  classical
  obtain ⟨A, hA, hU⟩ := LeanLab.HardyLittlewood1923.U1482.zeroCountUnit
  have hψ1 : q = 1 ∨ ψ ≠ 1 := Or.inr (ne_one_of_primitive hψ hq)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  refine ⟨4 * A * (Real.log q + 2), by positivity, fun t ht => ?_⟩
  let c : ℕ → ℝ := fun j => t - 2 + j
  let W : ℕ → Set ℂ := fun j =>
    {ρ | LeanLab.HardyLittlewood1923.U1479.IsNTZero ψ ρ ∧ c j ≤ |ρ.im| ∧ |ρ.im| ≤ c j + 1}
  have hc0 : ∀ j, 0 ≤ c j := fun j => by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [c]; linarith
  have hfinW : ∀ j, (W j).Finite := fun j => (hU q ψ hψ (c j) (hc0 j)).1
  have hcover : Znear ψ t ⊆ ⋃ j ∈ Finset.range 4, W j := by
    intro ρ ⟨hz, h0, h1, hi⟩
    rw [Set.mem_iUnion₂]
    rw [abs_le] at hi
    have key : ∃ j : ℕ, j < 4 ∧ c j ≤ |ρ.im| ∧ |ρ.im| ≤ c j + 1 := by
      by_cases a0 : |ρ.im| ≤ t - 1
      · exact ⟨0, by norm_num, by simp only [c]; push_cast; constructor <;> linarith⟩
      by_cases a1 : |ρ.im| ≤ t
      · exact ⟨1, by norm_num, by simp only [c]; push_cast; constructor <;> linarith⟩
      by_cases a2 : |ρ.im| ≤ t + 1
      · exact ⟨2, by norm_num, by simp only [c]; push_cast; constructor <;> linarith⟩
      · exact ⟨3, by norm_num, by simp only [c]; push_cast; constructor <;> linarith⟩
    obtain ⟨j, hj, hj1, hj2⟩ := key
    exact ⟨j, Finset.mem_range.mpr hj, ⟨hz, h0, h1⟩, hj1, hj2⟩
  have hf : (Znear ψ t).Finite :=
    (Set.Finite.biUnion (Finset.finite_toSet _) (fun j _ => hfinW j)).subset hcover
  refine ⟨hf, ?_⟩
  set F := hf.toFinset with hF
  have hsub : F ⊆ (Finset.range 4).biUnion
      (fun j => F.filter (fun ρ => c j ≤ |ρ.im| ∧ |ρ.im| ≤ c j + 1)) := by
    intro ρ hρ
    have hρ' : ρ ∈ Znear ψ t := (Set.Finite.mem_toFinset _).mp hρ
    have := hcover hρ'
    rw [Set.mem_iUnion₂] at this
    obtain ⟨j, hj, hρj⟩ := this
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hρ, hρj.2⟩⟩
  have hl1 : 1 ≤ Real.log (t + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlogj : ∀ j ∈ Finset.range 4, Real.log (q * (c j + 2)) ≤
      (Real.log q + 2) * Real.log (t + 2) := by
    intro j hj
    have hj4 : (j : ℝ) ≤ 3 := by
      have := Finset.mem_range.mp hj; exact_mod_cast (by omega : j ≤ 3)
    have hcj := hc0 j
    rw [Real.log_mul (by positivity) (by linarith)]
    have h2 : Real.log (c j + 2) ≤ 2 * Real.log (t + 2) := by
      calc Real.log (c j + 2) ≤ Real.log ((t + 2) ^ 2) :=
            Real.log_le_log (by linarith) (by simp only [c]; nlinarith)
        _ = 2 * Real.log (t + 2) := by rw [Real.log_pow]; norm_num
    nlinarith
  have hpiece : ∀ j ∈ Finset.range 4,
      ((F.filter (fun ρ => c j ≤ |ρ.im| ∧ |ρ.im| ≤ c j + 1)).card : ℝ) ≤
        A * ((Real.log q + 2) * Real.log (t + 2)) := by
    intro j hj
    set Fj := F.filter (fun ρ => c j ≤ |ρ.im| ∧ |ρ.im| ≤ c j + 1)
    have hmem : ∀ ρ ∈ Fj, LeanLab.HardyLittlewood1923.U1479.IsNTZero ψ ρ ∧ c j ≤ |ρ.im| ∧
        |ρ.im| ≤ c j + 1 := by
      intro ρ hρ
      obtain ⟨hρF, hρw⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hz, h0, h1, _⟩ := (Set.Finite.mem_toFinset _).mp hρF
      exact ⟨⟨hz, h0, h1⟩, hρw⟩
    have hsum := (hU q ψ hψ (c j) (hc0 j)).2 Fj hmem
    have hm1 : (Fj.card : ℝ) ≤ ∑ ρ ∈ Fj, LeanLab.HardyLittlewood1923.U1479.mult ψ ρ := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨⟨hz, _, h1⟩, _⟩ := hmem ρ hρ
      have hne1 : ρ ≠ 1 := by intro e; rw [e] at h1; simp at h1
      have htop := LeanLab.HardyLittlewood1923.U1482.L_ord_ne_top ψ hψ1 hne1
      have h0 : analyticOrderAt ψ.LFunction ρ ≠ 0 := by
        rw [ne_eq, analyticOrderAt_eq_zero]
        push Not
        exact ⟨LeanLab.HardyLittlewood1923.U1482.L_analyticAt ψ hne1, hz⟩
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      simp only [LeanLab.HardyLittlewood1923.U1479.mult, analyticOrderNatAt, ← hn,
        ENat.toNat_natCast, Nat.cast_one]
      rw [← hn] at h0
      have : n ≠ 0 := by exact_mod_cast h0
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    have hcj : c j + 2 = c j + 2 := rfl
    calc (Fj.card : ℝ) ≤ _ := hm1
      _ ≤ A * Real.log (q * (c j + 2)) := hsum
      _ ≤ A * ((Real.log q + 2) * Real.log (t + 2)) :=
          mul_le_mul_of_nonneg_left (hlogj j hj) hA
  calc (F.card : ℝ) ≤ (((Finset.range 4).biUnion
        (fun j => F.filter (fun ρ => c j ≤ |ρ.im| ∧ |ρ.im| ≤ c j + 1))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range 4,
          ((F.filter (fun ρ => c j ≤ |ρ.im| ∧ |ρ.im| ≤ c j + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range 4, A * ((Real.log q + 2) * Real.log (t + 2)) :=
        Finset.sum_le_sum hpiece
    _ = 4 * A * (Real.log q + 2) * Real.log (t + 2) := by simp; ring

/-- Davenport ch. 16 and 17: for a primitive `χ` mod `q ≠ 1`, good heights on `1/2 ≤ σ ≤ 2`,
one `T'` serving `χ` and `χ⁻¹` at both `T'` and `-T'`. Port of `ZetaZeros.good_height` with the
local expansion `U1503.logDeriv_L_wide` and the unit window count `U1482.zeroCountUnit`. -/
theorem good_heights_right {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 5 ≤ T → ∃ T' ∈ Icc T (T + 1),
      ∀ ψ ∈ ({χ, χ⁻¹} : Set (DirichletCharacter ℂ q)), ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
        ∀ τ ∈ ({T', -T'} : Set ℝ), ψ.LFunction (σ + τ * I) ≠ 0 ∧
          ‖deriv ψ.LFunction (σ + τ * I) / ψ.LFunction (σ + τ * I)‖ ≤
            C * Real.log (T + 2) ^ 2 := by
  open LeanLab.HardyLittlewood1923.U1503 in
  open LeanLab.PNTPort.DirichletZF in
  open LeanLab.PNTPort.DirichletZF.U1482 in
  classical
  have hχi : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hχ hq
  have hχi1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  obtain ⟨A1, hA1, hc1⟩ := znear_count hχ hq
  obtain ⟨A2, hA2, hc2⟩ := znear_count hχi hq
  have hZ := one_le_Z
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set Lq : ℝ := Real.log (20 * q * Z) + 2 with hLq
  have hLq0 : 0 ≤ Lq := by
    have : 0 ≤ Real.log (20 * q * Z) := Real.log_nonneg (by nlinarith)
    linarith
  have hKW := KW_pos
  have hlZ := lZ_pos
  refine ⟨(KW + 2 / lZ + 4 * (A1 + A2) / lZ) * Lq, by positivity, fun T hT => ?_⟩
  set T0 := T + 1 / 2 with hT0
  obtain ⟨hf1, hb1⟩ := hc1 T0 (by linarith)
  obtain ⟨hf2, hb2⟩ := hc2 T0 (by linarith)
  set G : Finset ℝ := (hf1.toFinset ∪ hf2.toFinset).image (fun ρ => |ρ.im|) with hG
  obtain ⟨T', hT'I, hfar⟩ := LeanLab.PNTPort.ZetaZeros.exists_far G T
  set δ : ℝ := 1 / (2 * ((G.card : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hℓ : 1 ≤ Real.log (T + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlT0 : Real.log (T0 + 2) ≤ 2 * Real.log (T + 2) := by
    calc Real.log (T0 + 2) ≤ Real.log ((T + 2) ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log (T + 2) := by rw [Real.log_pow]; norm_num
  have hGcard : (G.card : ℝ) ≤ 2 * (A1 + A2) * Real.log (T + 2) := by
    have h1 : G.card ≤ hf1.toFinset.card + hf2.toFinset.card :=
      Finset.card_image_le.trans (Finset.card_union_le _ _)
    have h2 : (G.card : ℝ) ≤ hf1.toFinset.card + hf2.toFinset.card := by exact_mod_cast h1
    nlinarith
  refine ⟨T', hT'I, fun ψ hψ σ hσ τ hτ => ?_⟩
  have hψ1 : ψ ≠ 1 := by rcases hψ with rfl | rfl; exacts [hχ1, hχi1]
  have hτabs : |τ| = T' := by
    rcases hτ with rfl | rfl
    · exact abs_of_nonneg (by linarith [hT'I.1])
    · rw [abs_neg]; exact abs_of_nonneg (by linarith [hT'I.1])
  set s : ℂ := σ + τ * I with hs
  have hsc : ‖s - cen τ‖ ≤ 29 / 20 * (7 / 10) := by
    have e : s - cen τ = ((σ - 3 / 2 : ℝ) : ℂ) := by simp only [hs, cen]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  -- zeros near `cen τ` have height in `G`, so they stay `δ` away
  have hfarρ : ∀ ρ : ℂ, ψ.LFunction ρ = 0 → ‖ρ - cen τ‖ ≤ 29 / 20 * (4 / 5) →
      δ ≤ |τ - ρ.im| := by
    intro ρ hz hd
    have hre : |(ρ - cen τ).re| ≤ ‖ρ - cen τ‖ := Complex.abs_re_le_norm _
    have him : |(ρ - cen τ).im| ≤ ‖ρ - cen τ‖ := Complex.abs_im_le_norm _
    have ere : (ρ - cen τ).re = ρ.re - 3 / 2 := by simp [cen]
    have eim : (ρ - cen τ).im = ρ.im - τ := by simp [cen]
    rw [ere] at hre; rw [eim] at him
    have hre' := abs_le.mp (hre.trans hd)
    have hre1 : ρ.re < 1 := by
      by_contra hc; push Not at hc
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) hc hz
    have himd : |(|ρ.im| - T0)| ≤ 2 := by
      have := abs_abs_sub_abs_le ρ.im τ
      rw [hτabs] at this
      have h3 : |ρ.im - τ| ≤ 29 / 20 * (4 / 5) := him.trans hd
      rw [abs_le] at this h3 ⊢
      constructor <;> linarith [hT'I.1, hT'I.2]
    have hmem : ρ ∈ hf1.toFinset ∪ hf2.toFinset := by
      rcases hψ with rfl | rfl
      · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr
          ⟨hz, by linarith [hre'.1], hre1, himd⟩)
      · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr
          ⟨hz, by linarith [hre'.1], hre1, himd⟩)
    have hfa := hfar |ρ.im| (Finset.mem_image.mpr ⟨ρ, hmem, rfl⟩)
    have := abs_abs_sub_abs_le τ ρ.im
    rw [hτabs] at this
    have e : |T' - (|ρ.im|)| = |(|τ| - |ρ.im|)| := by rw [hτabs]
    linarith [abs_abs_sub_abs_le τ ρ.im, e]
  have hsim : s.im = τ := by simp [hs]
  have hne : ψ.LFunction s ≠ 0 := by
    intro hz
    have := hfarρ s hz (hsc.trans (by norm_num))
    rw [hsim, sub_self, abs_zero] at this
    linarith
  refine ⟨hne, ?_⟩
  have hd : ∀ ρ : ℂ, ψ.LFunction ρ = 0 → ‖ρ - cen τ‖ ≤ 29 / 20 * (4 / 5) → δ ≤ ‖s - ρ‖ := by
    intro ρ hz hdd
    have h1 := hfarρ ρ hz hdd
    have h2 : |(s - ρ).im| ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
    have e : (s - ρ).im = τ - ρ.im := by simp [hsim]
    rw [e] at h2; linarith
  have hb := logDeriv_L_wide hψ1 τ hsc hne hδpos hd
  refine hb.trans ?_
  -- arithmetic
  set ℓ := Real.log (T + 2) with hℓdef
  have hlog1 : Real.log (20 * q * (|τ| + 3) * Z) ≤ Lq * ℓ := by
    have hpos : 0 < 20 * q * Z := by positivity
    have e : 20 * q * (|τ| + 3) * Z = (20 * q * Z) * (|τ| + 3) := by ring
    rw [e, Real.log_mul hpos.ne' (by positivity)]
    have h1 : Real.log (|τ| + 3) ≤ 2 * ℓ := by
      calc Real.log (|τ| + 3) ≤ Real.log ((T + 2) ^ 2) :=
            Real.log_le_log (by positivity) (by rw [hτabs]; nlinarith [hT'I.2])
        _ = 2 * ℓ := by rw [Real.log_pow, ← hℓdef]; norm_num
    have h0 : 0 ≤ Real.log (20 * q * Z) := Real.log_nonneg (by nlinarith)
    rw [hLq]; nlinarith
  have hinv : 1 / (lZ * δ) = 2 * ((G.card : ℝ) + 1) / lZ := by
    rw [hδ]; field_simp
  have hfac : KW + 1 / (lZ * δ) ≤ (KW + 2 / lZ + 4 * (A1 + A2) / lZ) * ℓ := by
    rw [hinv]
    have e1 : 2 * ((G.card : ℝ) + 1) / lZ = 2 / lZ + 2 * (G.card : ℝ) / lZ := by ring
    rw [e1]
    have h2 : 2 * (G.card : ℝ) / lZ ≤ 4 * (A1 + A2) / lZ * ℓ := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hlZ.le
      nlinarith
    have h3 : KW + 2 / lZ ≤ (KW + 2 / lZ) * ℓ := by
      have : 0 ≤ KW + 2 / lZ := by positivity
      nlinarith
    have e2 : (KW + 2 / lZ + 4 * (A1 + A2) / lZ) * ℓ =
        (KW + 2 / lZ) * ℓ + 4 * (A1 + A2) / lZ * ℓ := by ring
    rw [e2]; linarith
  have hfac0 : 0 ≤ KW + 1 / (lZ * δ) := by positivity
  have hlog0 : 0 ≤ Real.log (20 * q * (|τ| + 3) * Z) := Real.log_nonneg (by
    have h3 : (1 : ℝ) ≤ |τ| + 3 := by linarith [abs_nonneg τ]
    have h20 : (1 : ℝ) ≤ 20 * q := by linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h20 h3) hZ)
  calc (KW + 1 / (lZ * δ)) * Real.log (20 * q * (|τ| + 3) * Z)
      ≤ ((KW + 2 / lZ + 4 * (A1 + A2) / lZ) * ℓ) * (Lq * ℓ) :=
        mul_le_mul hfac hlog1 hlog0 (by positivity)
    _ = (KW + 2 / lZ + 4 * (A1 + A2) / lZ) * Lq * ℓ ^ 2 := by ring

/-- elementary: the gamma factor is nonzero off the real axis, its zeros being none and
`Gammaℝ` vanishing only at nonpositive even integers. -/
lemma gf_ne_zero_of_im_ne {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (h : s.im ≠ 0) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    intro h0
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
    apply h; rw [hn]; simp
  · rw [hχ.gammaFactor_def]
    intro h0
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
    apply h
    have : s = -(2 * n) - 1 := by rw [← hn]; ring
    rw [this]; simp

/-- Davenport ch. 9: for primitive `χ`, `Re s ≤ 1/2` and `Im s ≠ 0`, if `L(1 - s, χ̄) ≠ 0` then
`L(s, χ) ≠ 0` and `L'/L(s, χ) = -log q - γ'/γ(1 - s, χ̄) - γ'/γ(s, χ) - L'/L(1 - s, χ̄)`. -/
theorem logDeriv_fe_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {s : ℂ} (hre : s.re ≤ 1 / 2) (him : s.im ≠ 0) (h : (χ⁻¹).LFunction (1 - s) ≠ 0) :
    χ.LFunction s ≠ 0 ∧ deriv χ.LFunction s / χ.LFunction s =
      -(Real.log q : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)
        - logDeriv (DirichletCharacter.gammaFactor χ) s
        - deriv (χ⁻¹).LFunction (1 - s) / (χ⁻¹).LFunction (1 - s) := by
  set s0 := s with hs0def
  have hs0ne : s0 ≠ 0 := by intro e; apply him; rw [e]; simp
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  set A : ℂ → ℂ := fun s => DirichletCharacter.rootNumber χ * (q : ℂ) ^ ((1 - s) - 1 / 2) with hA
  set ref : ℂ → ℂ := fun s => 1 - s with href
  set B : ℂ → ℂ := DirichletCharacter.gammaFactor χ⁻¹ ∘ ref with hB
  set Cc : ℂ → ℂ := (χ⁻¹).LFunction ∘ ref with hCc
  have hev : χ.LFunction =ᶠ[nhds s0] A * B * Cc / DirichletCharacter.gammaFactor χ := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds
      (show s0.re < 1 by linarith),
      (isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds him] with s hs hsi
    have hs : s.re < 1 := hs
    have hsi : s.im ≠ 0 := hsi
    have hsne : s ≠ 0 := by intro e; apply hsi; rw [e]; simp
    have hr1 : 0 < (1 - s).re := by simp; linarith
    have h1ne : 1 - s ≠ 0 := by intro e; rw [e] at hr1; simp at hr1
    have hfe := hχ.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at hfe
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hsne), hfe,
      completed_eq_L_mul_gf χ⁻¹ (Or.inl h1ne) (gf_ne_zero_of_re_pos χ⁻¹ hr1)]
    simp only [Pi.mul_apply, Pi.div_apply, hA, hB, hCc, href, Function.comp_apply]
    ring
  have hr1 : 0 < (1 - s0).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hrefd : DifferentiableAt ℂ ref s0 := (differentiableAt_const _).sub differentiableAt_id
  have hderef : deriv ref s0 = -1 := by
    have hd : HasDerivAt ref (-1) s0 := by
      simpa using (hasDerivAt_id s0).const_sub (1 : ℂ)
    exact hd.deriv
  have hgfi := gf_ne_zero_of_re_pos χ⁻¹ hr1
  have hgfid : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ⁻¹) (ref s0) :=
    gf_diff_of_ne χ⁻¹ hgfi
  have hL1 : (1 - s0) ≠ 1 := by intro e; apply hs0ne; linear_combination -e
  have hLi : (χ⁻¹).LFunction (ref s0) ≠ 0 := h
  have hLid : DifferentiableAt ℂ (χ⁻¹).LFunction (ref s0) :=
    DirichletCharacter.differentiableAt_LFunction χ⁻¹ _ (Or.inl hL1)
  have hgf0 := gf_ne_zero_of_im_ne χ him
  have hgf0d := gf_diff_of_ne χ hgf0
  have hAne : A s0 ≠ 0 := mul_ne_zero (rootNumber_ne_zero' hχ) (cpow_ne_zero_iff.mpr (Or.inl hq0))
  have hAd : HasDerivAt A (DirichletCharacter.rootNumber χ *
      ((q : ℂ) ^ ((1 - s0) - 1 / 2) * Complex.log q * (-1))) s0 := by
    have h1 : HasDerivAt (fun s : ℂ => (1 - s) - 1 / 2) (-1) s0 := by
      simpa using ((hasDerivAt_id s0).const_sub (1 : ℂ)).sub_const (1 / 2 : ℂ)
    exact (h1.const_cpow (Or.inl hq0)).const_mul _
  have hBne : B s0 ≠ 0 := hgfi
  have hCne : Cc s0 ≠ 0 := hLi
  have hBd : DifferentiableAt ℂ B s0 := hgfid.comp s0 hrefd
  have hCd : DifferentiableAt ℂ Cc s0 := hLid.comp s0 hrefd
  have hlogA : logDeriv A s0 = -(Real.log q : ℂ) := by
    rw [logDeriv_apply, hAd.deriv, Complex.natCast_log]
    simp only [hA]
    have hc : (q : ℂ) ^ ((1 - s0) - 1 / 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hq0)
    rw [div_eq_iff (mul_ne_zero (rootNumber_ne_zero' hχ) hc)]
    ring
  refine ⟨?_, ?_⟩
  · rw [hev.eq_of_nhds]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hgf0
  rw [← logDeriv_apply, (logDeriv_congr_nhds hev).eq_of_nhds,
    logDeriv_div (f := A * B * Cc) (g := DirichletCharacter.gammaFactor χ) s0
      (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hgf0
      ((hAd.differentiableAt.mul hBd).mul hCd) hgf0d,
    logDeriv_mul (f := A * B) (g := Cc) s0 (mul_ne_zero hAne hBne) hCne
      (hAd.differentiableAt.mul hBd) hCd,
    logDeriv_mul (f := A) (g := B) s0 hAne hBne hAd.differentiableAt hBd, hlogA,
    hB, hCc, logDeriv_comp hgfid hrefd, logDeriv_comp hLid hrefd, hderef]
  simp only [href, logDeriv_apply]
  ring

/-- Davenport ch. 10, Stirling for the digamma function: the log derivative of the gamma factor
is `O(log(|t| + 2))` on `-1/2 ≤ σ ≤ 3/2`, `|t| ≥ 1`, uniformly in `χ`. -/
theorem logDeriv_gf_strip : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (σ t : ℝ),
    σ ∈ Icc (-1 / 2 : ℝ) (3 / 2) → 2 ≤ |t| →
      ‖logDeriv (DirichletCharacter.gammaFactor χ) (σ + t * I)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨K, hK, hb⟩ := LeanLab.PNTPort.ZetaZeros.digamma_strip
  -- both signs of the height, by `ψ(conj z) = conj ψ(z)`
  have hb' : ∀ σ u : ℝ, -1 ≤ σ → σ ≤ 2 → 1 ≤ |u| →
      ‖digamma ((σ : ℂ) + u * I)‖ ≤ K * Real.log (|u| + 3) + 2 := by
    intro σ u h1 h2 hu
    rcases le_or_gt 0 u with h0 | h0
    · rw [abs_of_nonneg h0] at hu ⊢; exact hb u hu σ h1 h2
    · rw [abs_of_neg h0] at hu ⊢
      have e : (σ : ℂ) + u * I = starRingEnd ℂ ((σ : ℂ) + ((-u : ℝ) : ℂ) * I) := by
        apply Complex.ext <;> simp
      rw [e, digamma_conj', Complex.norm_conj]
      exact hb (-u) hu σ h1 h2
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlpi : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  refine ⟨K + 4 / Real.log 4, by positivity, fun q χ σ t hσ ht => ?_⟩
  have ht4 : Real.log 4 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hhalf : Real.log (|t / 2| + 3) ≤ Real.log (|t| + 2) := by
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_two]; linarith
  have key : ∀ w : ℂ, ∀ σ' : ℝ, -1 ≤ σ' → σ' ≤ 2 →
      w / 2 = (σ' : ℂ) + ((t / 2 : ℝ) : ℂ) * I →
      ‖logDeriv Gammaℝ w‖ ≤ (K + 4 / Real.log 4) * Real.log (|t| + 2) := by
    intro w σ' h1 h2 hw
    have hnp : ∀ m : ℕ, w / 2 ≠ -m := by
      intro m hm
      have := congrArg Complex.im (hw.symm.trans hm)
      simp at this
      rw [this, abs_zero] at ht; linarith
    rw [LeanLab.Linnik.ExplicitFormula.logDeriv_Gammaℝ hnp, hw]
    have hd := hb' σ' (t / 2) h1 h2 (by rw [abs_div, abs_two]; linarith)
    calc _ ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
          ‖digamma ((σ' : ℂ) + ((t / 2 : ℝ) : ℂ) * I) / 2‖ := norm_add_le _ _
      _ ≤ 3 / 2 + (K * Real.log (|t| + 2) + 2) / 2 := by
          rw [norm_div, norm_div, norm_neg, Complex.norm_ofNat]
          gcongr
          exact hd.trans (by gcongr)
      _ ≤ (K + 4 / Real.log 4) * Real.log (|t| + 2) := by
          have h1 : 4 ≤ 4 / Real.log 4 * Real.log (|t| + 2) := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hl4]; linarith
          have h0 : 0 ≤ K * Real.log (|t| + 2) := mul_nonneg hK.le (le_trans hl4.le ht4)
          nlinarith
  rcases χ.even_or_odd with he | ho
  · have e : DirichletCharacter.gammaFactor χ = Gammaℝ := funext he.gammaFactor_def
    rw [e]
    exact key _ (σ / 2) (by linarith [hσ.1]) (by linarith [hσ.2]) (by push_cast; ring)
  · have e : DirichletCharacter.gammaFactor χ = Gammaℝ ∘ fun s => s + 1 :=
      funext ho.gammaFactor_def
    have hGd : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ Gammaℝ z := fun z hz => by
      have h : DifferentiableAt ℂ (fun s => ((Gammaℝ s)⁻¹)⁻¹) z :=
        (differentiable_Gammaℝ_inv z).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
      simpa only [inv_inv] using h
    have hw : 0 < ((σ : ℂ) + t * I + 1).re := by simp; linarith [hσ.1]
    rw [e, logDeriv_comp (f := Gammaℝ) (g := fun s : ℂ => s + 1) (hGd _ hw)
      (differentiableAt_id.add_const 1)]
    simp only [deriv_add_const', deriv_id'', mul_one]
    exact key _ ((σ + 1) / 2) (by linarith [hσ.1]) (by linarith [hσ.2]) (by push_cast; ring)

/-- elementary: for `T ≥ 5` and `|τ| ≤ T + 1`, `log(|τ| + 2) ≤ 2 log(T + 2) ≤ 2 log²(T + 2)`. -/
lemma log_tau_le {T τ : ℝ} (hT : 5 ≤ T) (hτ : |τ| ≤ T + 1) :
    Real.log (|τ| + 2) ≤ 2 * Real.log (T + 2) ^ 2 := by
  have h1 : 1 ≤ Real.log (T + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have h2 : Real.log (|τ| + 2) ≤ Real.log ((T + 2) ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith [abs_nonneg τ])
  rw [Real.log_pow] at h2
  push_cast at h2
  nlinarith

/-- Davenport ch. 17, good heights, for a fixed primitive character. -/
theorem good_heights {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 5 ≤ T → ∃ T' ∈ Icc T (T + 1), ∀ σ ∈ Icc (-1 / 2 : ℝ) 2,
      ∀ τ ∈ ({T', -T'} : Set ℝ), χ.LFunction (σ + τ * I) ≠ 0 ∧
        ‖deriv χ.LFunction (σ + τ * I) / χ.LFunction (σ + τ * I)‖ ≤
          C * Real.log (T + 2) ^ 2 := by
  rcases eq_or_ne q 1 with rfl | hq
  · -- `q = 1`: the zeta function
    obtain ⟨C, hC, hg⟩ := LeanLab.PNTPort.ExplicitPsi1.good_height_pm
    refine ⟨C, hC.le, fun T hT => ?_⟩
    obtain ⟨T', hT', hb⟩ := hg T hT
    refine ⟨T', hT', fun σ hσ τ hτ => ?_⟩
    obtain ⟨hne, hle⟩ := hb σ hσ τ hτ
    rw [DirichletCharacter.LFunction_modOne_eq]
    refine ⟨hne, hle.trans ?_⟩
    have h0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have h1 : Real.log T ≤ Real.log (T + 2) := Real.log_le_log (by linarith) (by linarith)
    gcongr
  · obtain ⟨CA, hCA, hA⟩ := good_heights_right hχ hq
    obtain ⟨CG, hCG, hG⟩ := logDeriv_gf_strip
    have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    refine ⟨Real.log q + 4 * CG + CA, by positivity, fun T hT => ?_⟩
    obtain ⟨T', hT'I, hb⟩ := hA T hT
    refine ⟨T', hT'I, fun σ hσ τ hτ => ?_⟩
    have h1 : 1 ≤ Real.log (T + 2) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hL2 : 1 ≤ Real.log (T + 2) ^ 2 := by nlinarith
    have hτabs : |τ| = T' := by
      rcases hτ with rfl | rfl
      · exact abs_of_nonneg (by linarith [hT'I.1])
      · rw [abs_neg]; exact abs_of_nonneg (by linarith [hT'I.1])
    have hτ1 : 2 ≤ |τ| := by rw [hτabs]; linarith [hT'I.1]
    have hτT : |τ| ≤ T + 1 := by rw [hτabs]; exact hT'I.2
    by_cases hσ2 : 1 / 2 ≤ σ
    · obtain ⟨hne, hle⟩ := hb χ (by simp) σ ⟨hσ2, hσ.2⟩ τ hτ
      refine ⟨hne, hle.trans ?_⟩
      have : 0 ≤ (Real.log q + 4 * CG) * Real.log (T + 2) ^ 2 := by positivity
      nlinarith
    · push Not at hσ2
      set s : ℂ := σ + τ * I with hs
      have hre : s.re = σ := by simp [hs]
      have him : s.im = τ := by simp [hs]
      have h1s : 1 - s = ((1 - σ : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
      have hτ' : -τ ∈ ({T', -T'} : Set ℝ) := by
        rcases hτ with rfl | rfl
        · right; rfl
        · left; simp
      obtain ⟨hne', hle'⟩ := hb χ⁻¹ (by simp) (1 - σ) ⟨by linarith, by linarith [hσ.1]⟩ (-τ) hτ'
      rw [← h1s] at hne' hle'
      have himne : s.im ≠ 0 := by rw [him]; intro h0; rw [h0, abs_zero] at hτ1; linarith
      obtain ⟨hne, heq⟩ := logDeriv_fe_strip hχ (by rw [hre]; exact hσ2.le) himne hne'
      refine ⟨hne, ?_⟩
      rw [heq]
      have hg1 : ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ ≤
          CG * (2 * Real.log (T + 2) ^ 2) := by
        rw [h1s]
        refine (hG q χ⁻¹ (1 - σ) (-τ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
          (by rw [abs_neg]; exact hτ1)).trans ?_
        rw [abs_neg]
        exact mul_le_mul_of_nonneg_left (log_tau_le hT hτT) hCG
      have hg2 : ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ ≤
          CG * (2 * Real.log (T + 2) ^ 2) :=
        (hG q χ σ τ ⟨hσ.1, by linarith⟩ hτ1).trans
          (mul_le_mul_of_nonneg_left (log_tau_le hT hτT) hCG)
      have hlogq : ‖(-(Real.log q : ℂ))‖ ≤ Real.log q * Real.log (T + 2) ^ 2 := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlq]
        nlinarith
      calc _ ≤ ‖-(Real.log q : ℂ) - logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)
              - logDeriv (DirichletCharacter.gammaFactor χ) s‖ +
            ‖deriv (χ⁻¹).LFunction (1 - s) / (χ⁻¹).LFunction (1 - s)‖ := norm_sub_le _ _
        _ ≤ (‖-(Real.log q : ℂ)‖ + ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ +
              ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖) +
            ‖deriv (χ⁻¹).LFunction (1 - s) / (χ⁻¹).LFunction (1 - s)‖ := by
          gcongr
          exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
        _ ≤ (Real.log q * Real.log (T + 2) ^ 2 + CG * (2 * Real.log (T + 2) ^ 2) +
              CG * (2 * Real.log (T + 2) ^ 2)) + CA * Real.log (T + 2) ^ 2 := by gcongr
        _ = (Real.log q + 4 * CG + CA) * Real.log (T + 2) ^ 2 := by ring

end LeanLab.Linnik.ExplicitFormula
