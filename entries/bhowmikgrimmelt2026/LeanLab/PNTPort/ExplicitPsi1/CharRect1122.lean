module

public import LeanLab.PNTPort.ExplicitPsi1.Residues

/-!
# The residue sum of `-L'/L(s, χ) xˢ/s` over the rectangle `[-1/2, c] × [-T, T]`

Unit P1122-0015, CLAUDE burst-20261122 S2 rect1122. AI wrote the Lean code in this file.
Binary Goldbach is OPEN; this file is analytic infrastructure for the character explicit formula,
Davenport, Multiplicative Number Theory, chapter 19, pages 115 to 118, modelled on the chapter 17
argument already ported for ζ in `Residues.lean` (`rect_explicit`).

For a nonprincipal Dirichlet character `χ`, `x > 0`, `c > 0`, `T > 0`, and no zero of `L(s, χ)` on
the border of `R = [-1/2, c] × [-T, T]`:

* `char_rect_explicit`: with `m = ord_{s=0} L(s, χ)` and `b` the constant term of the Laurent
  expansion of `L'/L(s, χ)` at `0`, i.e. the limit of `L'/L(s, χ) - m/s` as `s → 0`,
  `(1/2πi) ∮_R -L'/L(s, χ) xˢ/s ds = -(m log x + b) - Σ_{ρ ∈ R, L(ρ) = 0, ρ ≠ 0} m(ρ) x^ρ/ρ`.
  This is Davenport chapter 19 page 116: the residue at `s = 0` is `-L'(0, χ)/L(0, χ)` when
  `χ(-1) = -1`, display (2), and `-(log x + b(χ))` when `χ(-1) = 1`, display (3).
* `char_rect_explicit_of_ne_zero`: the case `L(0, χ) ≠ 0`, residue `-L'(0, χ)/L(0, χ)`.
* `char_rect_explicit_of_simple_zero`: the case of a simple zero at `0`, residue `-(log x + b)`.

The double pole at `0` in the even case is handled by subtracting the principal part `-m/s²`;
`rectIntegral_const_mul_inv_sq` shows its rectangle integral vanishes by the fundamental theorem
of calculus on each edge, `-1/s` being a primitive of `1/s²`. The remaining function has simple
poles only, and the ported residue theorem `RectangleIntegral'_eq_sumResiduesIn` applies.
No cited input, no open leaf.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.CharRect1122

open Complex Filter Topology Set

/-! ## Generic helpers -/

/-- If `(s - p) f(s)` has a limit at `p`, a meromorphic `f` has at most a simple pole at `p`. -/
lemma order_ge_neg_one_of_tendsto {f : ℂ → ℂ} {p c : ℂ} (hf : MeromorphicAt f p)
    (h : Tendsto (fun s => (s - p) * f s) (𝓝[≠] p) (𝓝 c)) :
    -1 ≤ meromorphicOrderAt f p := by
  have hlin : MeromorphicAt (fun s : ℂ => s - p) p := by fun_prop
  have hk : MeromorphicAt (fun s => (s - p) * f s) p := hlin.mul hf
  have h0 : 0 ≤ meromorphicOrderAt (fun s => (s - p) * f s) p :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg hk).mp ⟨c, h⟩
  have hmul : meromorphicOrderAt (fun s => (s - p) * f s) p =
      meromorphicOrderAt (fun s : ℂ => s - p) p + meromorphicOrderAt f p :=
    meromorphicOrderAt_mul hlin hf
  rw [hmul, meromorphicOrderAt_id_sub_const] at h0
  by_cases ht : meromorphicOrderAt f p = ⊤
  · simp [ht]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ht
  rw [← hn] at h0 ⊢
  have h1 : (0 : ℤ) ≤ 1 + n := by exact_mod_cast h0
  have h2 : ((-1 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) := WithTop.coe_le_coe.mpr (by omega)
  exact h2

/-- If `f` is analytic at `0` with finite order `m` there, `f'/f(s) - m/s` has a limit at `0`:
the constant term of the Laurent expansion of the logarithmic derivative. -/
lemma tendsto_logDeriv_sub_order {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (htop : analyticOrderAt f 0 ≠ ⊤) :
    ∃ b : ℂ, Tendsto (fun s => deriv f s / f s - (analyticOrderNatAt f 0 : ℂ) / s)
      (𝓝[≠] 0) (𝓝 b) := by
  set m := analyticOrderNatAt f 0 with hm
  have hord : analyticOrderAt f 0 = m := (Nat.cast_analyticOrderNatAt htop).symm
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp hord
  refine ⟨deriv g 0 / g 0, ?_⟩
  have hc : ContinuousAt (fun s => deriv g s / g s) 0 :=
    hg.deriv.continuousAt.div hg.continuousAt hg0
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hfg' := eventually_eventually_nhds.mpr hfg
  have hga := hg.eventually_analyticAt
  have hgne := hg.continuousAt.eventually_ne hg0
  filter_upwards [nhdsWithin_le_nhds hfg', nhdsWithin_le_nhds hga, nhdsWithin_le_nhds hgne,
    nhdsWithin_le_nhds hfg, self_mem_nhdsWithin] with s hs hsa hsne hs0 hsz
  have hsz' : s ≠ 0 := hsz
  have hfs : f s = s ^ m * g s := by simpa using hs0
  have hd : deriv f s = (m : ℂ) * s ^ (m - 1) * g s + s ^ m * deriv g s := by
    have heq : f =ᶠ[𝓝 s] fun u => u ^ m * g u := by
      filter_upwards [hs] with u hu
      simpa using hu
    rw [heq.deriv_eq]
    exact ((hasDerivAt_pow m s).mul hsa.differentiableAt.hasDerivAt).deriv
  rw [hd, hfs]
  have hsm : s ^ m ≠ 0 := pow_ne_zero _ hsz'
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0]; simp only [CharP.cast_eq_zero, zero_mul, pow_zero, zero_add, one_mul, zero_div,
      sub_zero]
  · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    field_simp
    push_cast
    ring

/-- Fundamental theorem of calculus for `A/s²` on a horizontal segment avoiding `0`. -/
lemma hIntegral_const_mul_inv_sq (A : ℂ) {x₁ x₂ y : ℝ}
    (h : ∀ t ∈ uIcc x₁ x₂, (t : ℂ) + y * I ≠ 0) :
    HIntegral (fun s : ℂ => A * (s ^ 2)⁻¹) x₁ x₂ y =
      -(A * ((x₂ : ℂ) + y * I)⁻¹) + A * ((x₁ : ℂ) + y * I)⁻¹ := by
  unfold HIntegral
  have hd : ∀ t ∈ uIcc x₁ x₂, HasDerivAt (fun t : ℝ => -(A * ((t : ℂ) + y * I)⁻¹))
      (A * (((t : ℂ) + y * I) ^ 2)⁻¹) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℂ => -(A * (u + y * I)⁻¹)) (A * (((t : ℂ) + y * I) ^ 2)⁻¹)
        (t : ℂ) := by
      have := (((hasDerivAt_id (t : ℂ)).add_const ((y : ℂ) * I)).inv (h t ht)).const_mul A
      refine this.neg.congr_deriv ?_
      simp only [id]
      ring
    exact h1.comp_ofReal (e := fun u : ℂ => -(A * (u + y * I)⁻¹))
  have hcont : ContinuousOn (fun t : ℝ => A * (((t : ℂ) + y * I) ^ 2)⁻¹) (uIcc x₁ x₂) := by
    apply continuousOn_const.mul
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (h t ht)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  ring

/-- Fundamental theorem of calculus for `A/s²` on a vertical segment avoiding `0`. -/
lemma vIntegral_const_mul_inv_sq (A : ℂ) {x y₁ y₂ : ℝ}
    (h : ∀ t ∈ uIcc y₁ y₂, (x : ℂ) + t * I ≠ 0) :
    VIntegral (fun s : ℂ => A * (s ^ 2)⁻¹) x y₁ y₂ =
      -(A * ((x : ℂ) + y₂ * I)⁻¹) + A * ((x : ℂ) + y₁ * I)⁻¹ := by
  unfold VIntegral
  have hd : ∀ t ∈ uIcc y₁ y₂, HasDerivAt (fun t : ℝ => -(A * ((x : ℂ) + t * I)⁻¹))
      (I * (A * (((x : ℂ) + t * I) ^ 2)⁻¹)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℂ => -(A * ((x : ℂ) + u * I)⁻¹))
        (I * (A * (((x : ℂ) + t * I) ^ 2)⁻¹)) (t : ℂ) := by
      have := ((((hasDerivAt_id (t : ℂ)).mul_const I).const_add (x : ℂ)).inv
        (h t ht)).const_mul A
      refine this.neg.congr_deriv ?_
      simp only [id]
      ring
    exact h1.comp_ofReal (e := fun u : ℂ => -(A * ((x : ℂ) + u * I)⁻¹))
  have hcont : ContinuousOn (fun t : ℝ => I * (A * (((x : ℂ) + t * I) ^ 2)⁻¹)) (uIcc y₁ y₂) := by
    apply continuousOn_const.mul
    apply continuousOn_const.mul
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (h t ht)
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  ring

/-- The rectangle integral of `A/s²` vanishes when `0` is not on the border: `-A/s` is a primitive
on each edge. This removes the double pole principal part in the even case, Davenport chapter 19
page 116. -/
theorem rectIntegral_const_mul_inv_sq (A : ℂ) {z w : ℂ}
    (h : ∀ s ∈ RectangleBorder z w, s ≠ 0) :
    RectangleIntegral (fun s : ℂ => A * (s ^ 2)⁻¹) z w = 0 := by
  unfold RectangleIntegral
  rw [hIntegral_const_mul_inv_sq A (fun t ht => h _ (mapsTo_rectangleBorder_left_im z w ht)),
    hIntegral_const_mul_inv_sq A (fun t ht => h _ (mapsTo_rectangleBorder_right_im z w ht)),
    vIntegral_const_mul_inv_sq A (fun t ht => h _ (mapsTo_rectangleBorder_right_re z w ht)),
    vIntegral_const_mul_inv_sq A (fun t ht => h _ (mapsTo_rectangleBorder_left_re z w ht))]
  ring

/-! ## The L-function facts -/

variable {q : ℕ} [NeZero q]

lemma analyticAt_L (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ) :
    AnalyticAt ℂ (DirichletCharacter.LFunction χ) z :=
  (DirichletCharacter.differentiable_LFunction hχ).analyticAt z

lemma analyticOrderAt_L_ne_top (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction χ) z ≠ ⊤ := by
  have hU : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Set.univ : Set ℂ) :=
    fun z _ => analyticAt_L χ hχ z
  have h2 : analyticOrderAt (DirichletCharacter.LFunction χ) 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)))]
    simp
  exact hU.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (x := 2) (y := z)
    (by simp) (by simp) h2

lemma meromorphicOrderAt_L (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ) :
    meromorphicOrderAt (DirichletCharacter.LFunction χ) z =
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℤ) := by
  rw [(analyticAt_L χ hχ z).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_L_ne_top χ hχ z)]
  simp

/-- The zeros of `L(s, χ)` in the rectangle `[-1/2, c] × [-T, T]` are finitely many. -/
theorem charZeros_rect_finite (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c T : ℝ) :
    (Rectangle (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩ ∩
      {s : ℂ | DirichletCharacter.LFunction χ s = 0}).Finite := by
  have hK : IsCompact (Rectangle (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩) :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    fun z _ => analyticAt_L χ hχ z
  have hn : DirichletCharacter.LFunction χ 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  have hd := ha.preimage_zero_mem_codiscrete hn
  have := hK.finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono (Set.subset_univ _) hd)
  refine this.subset ?_
  rintro z ⟨hz, h0⟩
  exact ⟨hz, by simpa using h0⟩

/-! ## The residue computation -/

/-- At `s = 0`: `s (-L'/L(s, χ) xˢ/s + m/s²) → -(m log x + b)`, `m` the order of `L(s, χ)` at `0`
and `b` the constant term of `L'/L(s, χ)` there; this is the residue at `0`, Davenport chapter 19
page 116. -/
lemma tendsto_zero_pt (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    {b : ℂ} (hb : Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s -
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 : ℂ) / s) (𝓝[≠] 0) (𝓝 b)) :
    Tendsto (fun s : ℂ => (s - 0) * ((-(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) +
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 : ℂ) * (s ^ 2)⁻¹)) (𝓝[≠] 0)
      (𝓝 (-((analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 : ℂ) * (Real.log x : ℂ) + b)))
      := by
  set m : ℂ := (analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 : ℂ)
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  -- `xˢ → 1`
  have hpow : Tendsto (fun s : ℂ => (x : ℂ) ^ s) (𝓝[≠] 0) (𝓝 1) := by
    have := ((analyticAt_xpow hx 0).continuousAt.tendsto).mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    simpa using this
  -- `(xˢ - 1)/s → log x`
  have hslope : Tendsto (fun s : ℂ => ((x : ℂ) ^ s - 1) / s) (𝓝[≠] 0)
      (𝓝 (Real.log x : ℂ)) := by
    have hd := (hasStrictDerivAt_const_cpow (x := (x : ℂ)) (y := 0) (Or.inl hx0)).hasDerivAt
    have := hasDerivAt_iff_tendsto_slope.mp hd
    rw [cpow_zero, one_mul, ← ofReal_log hx.le] at this
    refine this.congr' ?_
    filter_upwards with s
    simp only [slope, vsub_eq_sub, sub_zero, cpow_zero, smul_eq_mul]
    ring
  have hlim := ((hb.mul hpow).neg).sub (hslope.const_mul m)
  have hval : -(b * 1) - m * (Real.log x : ℂ) = -(m * (Real.log x : ℂ) + b) := by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  field_simp
  ring

/-- At `z ≠ 0`: `(s - z)(-L'/L(s, χ) xˢ/s + A/s²) → -m(z) x^z/z`, the residue at a zero `z ≠ 0`. -/
lemma tendsto_ne_zero_pt (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x)
    (A : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun s : ℂ => (s - z) * ((-(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) + A * (s ^ 2)⁻¹)) (𝓝[≠] z)
      (𝓝 (-((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) * (x : ℂ) ^ z / z))) := by
  have hl := tendsto_mul_logDeriv_mero (analyticAt_L χ hχ z).meromorphicAt
    (meromorphicOrderAt_L χ hχ z)
  have hk : Tendsto (fun s : ℂ => (x : ℂ) ^ s / s) (𝓝[≠] z) (𝓝 ((x : ℂ) ^ z / z)) :=
    (((analyticAt_xpow hx z).div analyticAt_id hz).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  have hsub : Tendsto (fun s : ℂ => s - z) (𝓝[≠] z) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hq : Tendsto (fun s : ℂ => A * (s ^ 2)⁻¹) (𝓝[≠] z) (𝓝 (A * (z ^ 2)⁻¹)) := by
    have : ContinuousAt (fun s : ℂ => A * (s ^ 2)⁻¹) z := by
      apply continuousAt_const.mul
      exact (continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hz)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := ((hl.mul hk).neg).add (hsub.mul hq)
  have hval : -((((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℤ) : ℂ)) *
      ((x : ℂ) ^ z / z)) + 0 * (A * (z ^ 2)⁻¹) =
      -((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) * (x : ℂ) ^ z / z) := by
    push_cast; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards with s
  ring

/-- **The residue sum over `[-1/2, c] × [-T, T]` for a character.** Let `χ ≠ 1`, `x > 0`, `c > 0`,
`T > 0`, and let `L(s, χ)` have no zero on the border of the rectangle. Let `m` be the order of
`L(s, χ)` at `s = 0`. Then the constant term `b` of `L'/L(s, χ)` at `0`, the limit of
`L'/L(s, χ) - m/s`, exists, and
`(1/2πi) ∮ -L'/L(s, χ) xˢ/s ds = -(m log x + b) - Σ_ρ m(ρ) x^ρ/ρ`,
the sum over the zeros `ρ ≠ 0` of `L(s, χ)` inside the rectangle, `m(ρ)` the multiplicity.
Davenport, Multiplicative Number Theory, chapter 19 pages 115 to 116, displays (2) and (3), the
residue computation; chapter 17 for the contour. -/
theorem char_rect_explicit (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {x c T : ℝ} (hx : 0 < x)
    (hc : 0 < c) (hT : 0 < T)
    (hbd : ∀ z ∈ RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩, DirichletCharacter.LFunction χ z ≠ 0) :
    ∃ b : ℂ, Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s -
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 : ℂ) / s) (𝓝[≠] 0) (𝓝 b) ∧
      RectangleIntegral' (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) ⟨-1 / 2, -T⟩ ⟨c, T⟩ =
        -((analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 : ℂ) * (Real.log x : ℂ) + b) -
          ∑ ρ ∈ (charZeros_rect_finite χ hχ c T).toFinset.erase 0,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  classical
  set L := DirichletCharacter.LFunction χ with hLdef
  obtain ⟨b, hb⟩ := tendsto_logDeriv_sub_order (analyticAt_L χ hχ 0) (analyticOrderAt_L_ne_top χ hχ 0)
  refine ⟨b, hb, ?_⟩
  set m : ℂ := (analyticOrderNatAt L 0 : ℂ) with hmdef
  set F : ℂ → ℂ := fun s => -(deriv L s / L s) * (x : ℂ) ^ s / s with hFdef
  set K : ℂ → ℂ := fun s => m * (s ^ 2)⁻¹ with hKdef
  set G : ℂ → ℂ := F + K with hGdef
  set R := Rectangle (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩ with hRdef
  set Z := (charZeros_rect_finite χ hχ c T).toFinset with hZdef
  have hmem := fun z => mem_rect (c := c) (T := T) (by linarith) hT.le (z := z)
  have hbR : RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩ ⊆ R := rectangleBorder_subset_rectangle _ _
  have hb0 : ∀ z ∈ RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩, z ≠ 0 := by
    intro z hz he
    rcases border_cases hz with h | h | h | h <;> rw [he] at h <;> simp at h <;> linarith
  have h0R : (0 : ℂ) ∈ R := by
    rw [hmem]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
  have hA (z : ℂ) : AnalyticAt ℂ L z := analyticAt_L χ hχ z
  have hkern (z : ℂ) : MeromorphicAt (fun s : ℂ => (x : ℂ) ^ s) z :=
    (analyticAt_xpow hx z).meromorphicAt
  have hFm (z : ℂ) : MeromorphicAt F z :=
    (((hA z).meromorphicAt.deriv.div (hA z).meromorphicAt).neg.mul (hkern z)).div
      analyticAt_id.meromorphicAt
  have hKm (z : ℂ) : MeromorphicAt K z := by
    simp only [hKdef]; fun_prop
  have hGm (z : ℂ) : MeromorphicAt G z := (hFm z).add (hKm z)
  -- analytic away from `0` and the zeros
  have hFa {z : ℂ} (hz0 : z ≠ 0) (hLz : L z ≠ 0) : AnalyticAt ℂ F z :=
    (((hA z).deriv.div (hA z) hLz).neg.mul (analyticAt_xpow hx z)).div analyticAt_id hz0
  have hKa {z : ℂ} (hz0 : z ≠ 0) : AnalyticAt ℂ K z :=
    analyticAt_const.mul ((analyticAt_id.pow 2).inv (pow_ne_zero 2 hz0))
  have hGa {z : ℂ} (hz0 : z ≠ 0) (hLz : L z ≠ 0) : AnalyticAt ℂ G z := (hFa hz0 hLz).add (hKa hz0)
  -- the limits of `(s - z) G(s)`
  have hT0 : Tendsto (fun s => (s - 0) * G s) (𝓝[≠] 0) (𝓝 (-(m * (Real.log x : ℂ) + b))) :=
    tendsto_zero_pt χ hx hb
  have hTz {z : ℂ} (hz : z ≠ 0) : Tendsto (fun s => (s - z) * G s) (𝓝[≠] z)
      (𝓝 (-((analyticOrderNatAt L z : ℂ) * (x : ℂ) ^ z / z))) :=
    tendsto_ne_zero_pt χ hχ hx m hz
  have hsimple : HasSimplePolesOn G R := by
    intro z _
    rcases eq_or_ne z 0 with rfl | hz
    · exact order_ge_neg_one_of_tendsto (hGm 0) hT0
    · exact order_ge_neg_one_of_tendsto (hGm z) (hTz hz)
  have hP : ∀ z ∈ R, meromorphicOrderAt G z < 0 → z ∈ (insert 0 (Z.erase 0) : Finset ℂ) := by
    intro z hz hneg
    by_contra hns
    simp only [Finset.mem_insert, Finset.mem_erase, not_or, not_and] at hns
    obtain ⟨h0, hZ⟩ := hns
    have hLz : L z ≠ 0 := by
      intro h; apply hZ h0; rw [hZdef, Set.Finite.mem_toFinset]; exact ⟨hz, h⟩
    exact absurd (hGa h0 hLz).meromorphicOrderAt_nonneg (not_le.mpr hneg)
  have hres := RectangleIntegral'_eq_sumResiduesIn (f := G)
    (z := ⟨-1 / 2, -T⟩) (w := ⟨c, T⟩) (by simp; linarith) (by simp; linarith)
    (fun z _ => hGm z)
    (by
      rw [Set.disjoint_left]
      intro z hz hneg
      simp only [mem_ofPred_eq] at hneg
      exact absurd (hGa (hb0 z hz) (hbd z hz)).meromorphicOrderAt_nonneg (not_le.mpr hneg))
    (by
      apply (insert 0 (Z.erase 0) : Finset ℂ).finite_toSet.subset
      intro z ⟨hz, hneg⟩
      exact hP z hz hneg)
    hsimple
  -- the rectangle integral of `G` is that of `F`
  have hFc : ContinuousOn F (RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩) := fun z hz =>
    (hFa (hb0 z hz) (hbd z hz)).continuousAt.continuousWithinAt
  have hKc : ContinuousOn K (RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩) := fun z hz =>
    (hKa (hb0 z hz)).continuousAt.continuousWithinAt
  have hGF : RectangleIntegral G (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩ =
      RectangleIntegral F (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩ := by
    rw [hGdef, RectangleBorderIntegrable.add hFc.rectangleBorder_integrable
      hKc.rectangleBorder_integrable, hKdef, rectIntegral_const_mul_inv_sq m hb0, add_zero]
  have hGF' : RectangleIntegral' F (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩ =
      RectangleIntegral' G (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩ := by
    simp only [RectangleIntegral', hGF]
  show RectangleIntegral' F _ _ = _
  rw [hGF', hres]
  have hS : R ∩ {z | meromorphicOrderAt G z < 0} =
      ((insert 0 (Z.erase 0) : Finset ℂ) : Set ℂ) ∩ {z | meromorphicOrderAt G z < 0} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hz, hneg⟩; exact ⟨hP z hz hneg, hneg⟩
    · rintro ⟨hz, hneg⟩
      refine ⟨?_, hneg⟩
      simp only [Finset.mem_insert, Finset.mem_erase] at hz
      rcases hz with rfl | ⟨_, hz⟩
      · exact h0R
      · rw [hZdef, Set.Finite.mem_toFinset] at hz; exact hz.1
  rw [sumResiduesIn_inter_eq_of_set_eq hS (fun z _ hz =>
    residue_eq_zero_of_not_pole_of_meromorphicAt (hGm z) (not_lt.mp hz))]
  rw [sumResiduesIn, Finset.tsum_subtype' (insert 0 (Z.erase 0)) (fun z => residue G z)]
  rw [Finset.sum_insert (Finset.notMem_erase 0 Z), residue_eq_of_tendsto hT0]
  have hsum : ∑ ρ ∈ Z.erase 0, residue G ρ =
      ∑ ρ ∈ Z.erase 0, -((analyticOrderNatAt L ρ : ℂ) * (x : ℂ) ^ ρ / ρ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    exact residue_eq_of_tendsto (hTz (Finset.ne_of_mem_erase hρ))
  rw [hsum, Finset.sum_neg_distrib]
  ring

/-- **Odd case**, Davenport chapter 19 page 115 display (2): if `L(0, χ) ≠ 0`, as for odd
primitive `χ`, the residue at `0` is `-L'(0, χ)/L(0, χ)`, and
`(1/2πi) ∮ -L'/L(s, χ) xˢ/s ds = -L'(0, χ)/L(0, χ) - Σ_ρ m(ρ) x^ρ/ρ`. -/
theorem char_rect_explicit_of_ne_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 0 < T) (h0 : DirichletCharacter.LFunction χ 0 ≠ 0)
    (hbd : ∀ z ∈ RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩, DirichletCharacter.LFunction χ z ≠ 0) :
    RectangleIntegral' (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) ⟨-1 / 2, -T⟩ ⟨c, T⟩ =
      -(deriv (DirichletCharacter.LFunction χ) 0 / DirichletCharacter.LFunction χ 0) -
        ∑ ρ ∈ (charZeros_rect_finite χ hχ c T).toFinset,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  obtain ⟨b, hb, he⟩ := char_rect_explicit χ hχ hx hc hT hbd
  have hm : analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 = 0 := by
    simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr h0)]
  have hcont : Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s -
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 : ℂ) / s) (𝓝[≠] 0)
      (𝓝 (deriv (DirichletCharacter.LFunction χ) 0 / DirichletCharacter.LFunction χ 0)) := by
    have := (((analyticAt_L χ hχ 0).deriv.div (analyticAt_L χ hχ 0) h0).continuousAt.tendsto).mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    refine this.congr (fun s => ?_)
    simp [hm]
  have hbv := tendsto_nhds_unique hb hcont
  have hZ : (0 : ℂ) ∉ (charZeros_rect_finite χ hχ c T).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact fun h => h0 h.2
  rw [he, Finset.erase_eq_of_notMem hZ, hm, hbv]
  simp

/-- **Even case with a simple zero at `0`**, Davenport chapter 19 page 116 display (3): if
`L(s, χ)` has a simple zero at `0`, as for even primitive `χ ≠ 1`, write
`L'/L(s, χ) = 1/s + b + ...`; the residue at `0` is `-(log x + b)` and
`(1/2πi) ∮ -L'/L(s, χ) xˢ/s ds = -(log x + b) - Σ_{ρ ≠ 0} m(ρ) x^ρ/ρ`. -/
theorem char_rect_explicit_of_simple_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 0 < T)
    (h1 : analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 = 1)
    (hbd : ∀ z ∈ RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩, DirichletCharacter.LFunction χ z ≠ 0) :
    ∃ b : ℂ, Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b) ∧
      RectangleIntegral' (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) ⟨-1 / 2, -T⟩ ⟨c, T⟩ =
        -((Real.log x : ℂ) + b) -
          ∑ ρ ∈ (charZeros_rect_finite χ hχ c T).toFinset.erase 0,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  obtain ⟨b, hb, he⟩ := char_rect_explicit χ hχ hx hc hT hbd
  rw [h1] at hb he
  refine ⟨b, by simpa using hb, ?_⟩
  rw [he]
  simp

/-! ## The simple zero at `0` of an even primitive L-function -/

/-- For an even primitive `χ ≠ 1`, `L(s, χ)` has a simple zero at `s = 0`, Davenport chapter 19
page 116, first line: the completed L-function is nonzero at `0` by the functional equation for
`χ⁻¹` at `s = 0` and `L(1, χ⁻¹) ≠ 0`, and `1/Γℝ(s)` has a simple zero at `0`, Davenport chapter 9
for the functional equation. -/
theorem analyticOrderNatAt_LFunction_zero_of_even (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (heven : χ.Even) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) 0 = 1 := by
  have hN : q ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  set Λ := DirichletCharacter.completedLFunction χ with hΛdef
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hL : ∀ s, DirichletCharacter.LFunction χ s = Λ s * (Gammaℝ s)⁻¹ := fun s => by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN),
      heven.gammaFactor_def, div_eq_mul_inv]
  have hG : ∀ s : ℂ, (Gammaℝ s)⁻¹ = s * ((2 * (Real.pi : ℂ))⁻¹ * (Gammaℝ (s + 2))⁻¹) := by
    intro s
    rcases eq_or_ne s 0 with rfl | hs
    · simp [Gammaℝ_def, Complex.Gamma_zero]
    · rw [Gammaℝ_add_two hs]
      by_cases hg : Gammaℝ s = 0
      · simp [hg]
      · field_simp
  have hΛ0 : Λ 0 ≠ 0 := by
    have hprim' : (χ⁻¹).IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hprim
    have fe := hprim'.completedLFunction_one_sub 0
    rw [inv_inv, sub_zero] at fe
    have hχi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
    have h1 : DirichletCharacter.completedLFunction χ⁻¹ 1 ≠ 0 := by
      have hL1 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ 1 (Or.inr hN)
      have hne := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχi)
        (show (1 : ℝ) ≤ (1 : ℂ).re by simp)
      intro h; rw [hL1, h, zero_div] at hne; exact hne rfl
    intro h; rw [← hΛdef, h, mul_zero] at fe; exact h1 fe
  have hga : AnalyticAt ℂ (fun s => Λ s * ((2 * (Real.pi : ℂ))⁻¹ * (Gammaℝ (s + 2))⁻¹)) 0 := by
    have hd : Differentiable ℂ (fun s => Λ s * ((2 * (Real.pi : ℂ))⁻¹ * (Gammaℝ (s + 2))⁻¹)) := by
      apply (DirichletCharacter.differentiable_completedLFunction hχ).mul
      apply (differentiable_const _).mul
      exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 2)
    exact hd.analyticAt 0
  have hg0 : Λ 0 * ((2 * (Real.pi : ℂ))⁻¹ * (Gammaℝ (0 + 2))⁻¹) ≠ 0 := by
    have h2 : Gammaℝ (0 + 2) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp)
    exact mul_ne_zero hΛ0 (mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero hπ)) (inv_ne_zero h2))
  have hord : analyticOrderAt (DirichletCharacter.LFunction χ) 0 = (1 : ℕ) :=
    (analyticAt_L χ hχ 0).analyticOrderAt_eq_natCast.mpr ⟨_, hga, hg0,
      Eventually.of_forall fun s => by
        simp only [hL, sub_zero, pow_one, smul_eq_mul]
        rw [hG s]; ring⟩
  simp [analyticOrderNatAt, hord]

/-- **Even primitive case**, Davenport chapter 19 page 116 display (3): for an even primitive
`χ ≠ 1`, `L'/L(s, χ) = 1/s + b(χ) + ...` near `0`, and
`(1/2πi) ∮ -L'/L(s, χ) xˢ/s ds = -(log x + b(χ)) - Σ_{ρ ≠ 0} m(ρ) x^ρ/ρ`. -/
theorem char_rect_explicit_even_primitive (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (heven : χ.Even) {x c T : ℝ} (hx : 0 < x) (hc : 0 < c) (hT : 0 < T)
    (hbd : ∀ z ∈ RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨c, T⟩, DirichletCharacter.LFunction χ z ≠ 0) :
    ∃ b : ℂ, Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b) ∧
      RectangleIntegral' (fun s : ℂ => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) ⟨-1 / 2, -T⟩ ⟨c, T⟩ =
        -((Real.log x : ℂ) + b) -
          ∑ ρ ∈ (charZeros_rect_finite χ hχ c T).toFinset.erase 0,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * (x : ℂ) ^ ρ / ρ :=
  char_rect_explicit_of_simple_zero χ hχ hx hc hT
    (analyticOrderNatAt_LFunction_zero_of_even χ hχ hprim heven) hbd

end LeanLab.PNTPort.ExplicitPsi1.CharRect1122
