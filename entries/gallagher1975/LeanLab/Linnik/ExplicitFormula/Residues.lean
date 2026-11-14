module

public import LeanLab.Linnik.ExplicitFormula.Defs
public import LeanLab.PNTPort.StrongPNT.ResidueCalcOnRectangles
public import LeanLab.PNTPort.ExplicitPsi1.Merom

/-!
# Residues of `F` and the rectangle formula, Davenport ch. 17 and 19

AI wrote the Lean code. Binary Goldbach is OPEN.
Port of `LeanLab.PNTPort.ExplicitPsi1.Merom` and `Residues` from `ζ` to `L(s, χ)`.
The residue of `F` at a zero `ρ` is `-m(ρ) x^ρ/((ρ+1)(ρ+2))`, at `s = 1` for the trivial
character it is `x/6`, and the kernel has no pole in `Re s ≥ -1/2`.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex Filter Topology Set

/-- For `q = 1` the L-function is `ζ`, Mathlib `LFunction_modOne_eq`. -/
lemma LFunction_modOne_fun (χ : DirichletCharacter ℂ 1) : χ.LFunction = riemannZeta :=
  DirichletCharacter.LFunction_modOne_eq

/-- `L(s, χ)` is analytic at `s` unless `χ` is trivial and `s = 1`, Mathlib. -/
lemma analyticAt_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s ≠ 1 ∨ χ ≠ 1) : AnalyticAt ℂ χ.LFunction s := by
  rcases hs with hs | hχ
  · have hU : DifferentiableOn ℂ χ.LFunction ({1}ᶜ : Set ℂ) := fun z hz =>
      (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
    exact hU.analyticAt (isOpen_compl_singleton.mem_nhds hs)
  · exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt s

/-- A primitive character of modulus `q ≠ 1` is nontrivial, since the trivial one has conductor
`1`. Elementary. -/
lemma ne_one_of_isPrimitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) : χ ≠ 1 := by
  intro h
  rw [DirichletCharacter.isPrimitive_def] at hχ
  rw [(DirichletCharacter.eq_one_iff_conductor_eq_one).mp h] at hχ
  exact hq hχ.symm

/-- `L(2, χ) ≠ 0`, Mathlib nonvanishing on `Re s ≥ 1`. -/
lemma LFunction_two_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.LFunction 2 ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)

/-- `L(s, χ)` is not locally zero at `s ≠ 1`: identity theorem on the connected set `{1}ᶜ`. -/
lemma analyticOrderAt_LFunction_ne_top {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {p : ℂ}
    (hp : p ≠ 1) : analyticOrderAt χ.LFunction p ≠ ⊤ := by
  have hU : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) := fun z hz =>
    analyticAt_LFunction χ (Or.inl hz)
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      (1 : ℂ)).isPreconnected
  have h2 : analyticOrderAt χ.LFunction 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (LFunction_two_ne_zero χ))]
    simp
  exact hU.analyticOrderAt_ne_top_of_isPreconnected hconn (x := 2) (y := p)
    (by simp) (by simpa using hp) h2

/-- Away from `1` the meromorphic order of `L(s, χ)` is `mult χ p`. -/
lemma order_LFunction_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {p : ℂ}
    (hp : p ≠ 1) : meromorphicOrderAt χ.LFunction p = (mult χ p : ℤ) := by
  rw [(analyticAt_LFunction χ (Or.inl hp)).meromorphicOrderAt_eq]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_LFunction_ne_top χ hp)
  rw [mult, analyticOrderNatAt, ← hn, ENat.toNat_natCast]
  simp

/-- `L(s, χ)` is meromorphic everywhere. -/
theorem meromorphicAt_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    MeromorphicAt χ.LFunction s := by
  by_cases h : s ≠ 1 ∨ χ ≠ 1
  · exact (analyticAt_LFunction χ h).meromorphicAt
  · simp only [not_or, ne_eq, not_not] at h
    obtain ⟨rfl, rfl⟩ := h
    have hP : AnalyticAt ℂ (fun s : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) 1 := by
      apply Finset.analyticAt_fun_prod
      intro p hp
      have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
      exact analyticAt_const.sub (analyticAt_const.cpow analyticAt_id.neg
        (Complex.natCast_mem_slitPlane.mpr hp0))
    refine (hP.meromorphicAt.mul (LeanLab.PNTPort.ExplicitPsi1.meromorphicAt_zeta 1)).congr ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs).symm

/-- The kernel `x^s / ((s+1)(s+2))` is analytic away from `-1` and `-2`. Elementary. -/
lemma analyticAt_kernel2 {x : ℝ} (hx : 0 < x) {z : ℂ} (h1 : z ≠ -1) (h2 : z ≠ -2) :
    AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / ((s + 1) * (s + 2))) z := by
  apply (analyticAt_const.cpow analyticAt_id (ofReal_mem_slitPlane.mpr hx)).div
    ((analyticAt_id.add analyticAt_const).mul (analyticAt_id.add analyticAt_const))
  refine mul_ne_zero ?_ ?_
  · intro h; apply h1; simp only [Pi.add_apply, id] at h; linear_combination h
  · intro h; apply h2; simp only [Pi.add_apply, id] at h; linear_combination h

/-- A point with `Re z ≥ -1/2` is neither `-1` nor `-2`. Elementary. -/
lemma ne_neg_one_of_re {z : ℂ} (hz : -1 / 2 ≤ z.re) : z ≠ -1 := by
  rintro rfl; norm_num at hz

/-- A point with `Re z ≥ -1/2` is not `-2`. Elementary. -/
lemma ne_neg_two_of_re {z : ℂ} (hz : -1 / 2 ≤ z.re) : z ≠ -2 := by
  rintro rfl; norm_num at hz

/-- Residue of `F` at a point `ρ ≠ 1` with `Re ρ ≥ -1/2`, zero or not; Davenport ch. 17. -/
lemma residue_Fchi_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hre : -1 / 2 ≤ ρ.re) (h1 : ρ ≠ 1) :
    Tendsto (fun s => (s - ρ) * Fchi χ x s) (𝓝[≠] ρ) (𝓝 (-zterm χ x ρ)) := by
  have hL := LeanLab.PNTPort.ExplicitPsi1.tendsto_mul_logDeriv_mero
    (meromorphicAt_LFunction χ ρ) (order_LFunction_of_ne_one χ h1)
  have hk := ((analyticAt_kernel2 hx (ne_neg_one_of_re hre)
    (ne_neg_two_of_re hre)).continuousAt.tendsto).mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ))
  have := (hL.mul hk).neg
  simp only [Int.cast_natCast] at this
  refine this.congr (fun s => ?_)
  simp only [Fchi]; ring

/-- Residue of `F` at a zero `ρ ∈ Zall`. -/
theorem residue_Fchi_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ ∈ Zall χ) :
    Tendsto (fun s => (s - ρ) * Fchi χ x s) (𝓝[≠] ρ) (𝓝 (-zterm χ x ρ)) := by
  exact residue_Fchi_of_ne_one χ hx hρ.2.1 hρ.2.2

/-- Residue of `F` at the pole `s = 1` of `ζ`, the trivial character mod 1. -/
theorem residue_Fchi_one {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s => (s - 1) * Fchi (1 : DirichletCharacter ℂ 1) x s) (𝓝[≠] 1)
      (𝓝 ((x : ℂ) / 6)) := by
  have hk := ((analyticAt_kernel2 hx (z := 1) (by norm_num) (by norm_num)).continuousAt.tendsto
    ).mono_left (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
  have := (LeanLab.PNTPort.ExplicitPsi1.tendsto_logDeriv_zeta_one.mul hk).neg
  rw [show ((x : ℂ) / 6) = -(-1 * ((x : ℂ) ^ (1 : ℂ) / ((1 + 1) * (1 + 2)))) by
    rw [cpow_one]; ring]
  refine this.congr (fun s => ?_)
  simp only [Fchi, LFunction_modOne_fun]; ring

/-- For nontrivial `χ`, a compact set holds finitely many zeros of the entire `L(s, χ)`;
identity theorem, as Mathlib's `IsCompact.inter_riemannZetaZeros_finite`. -/
lemma zeros_compact_finite_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {S : Set ℂ} (hS : IsCompact S) : (S ∩ χ.LFunction ⁻¹' {0}).Finite := by
  have hA : AnalyticOnNhd ℂ χ.LFunction univ := fun z _ => analyticAt_LFunction χ (Or.inr hχ)
  have hc : χ.LFunction ⁻¹' {0}ᶜ ∈ codiscreteWithin (univ : Set ℂ) :=
    hA.preimage_zero_mem_codiscreteWithin (x := 2) (LFunction_two_ne_zero χ) (mem_univ _)
      isConnected_univ
  have hc' : χ.LFunction ⁻¹' {0}ᶜ ∈ codiscrete ℂ := hc
  obtain ⟨hO, hD⟩ := mem_codiscrete'.mp hc'
  have hcl : IsClosed (χ.LFunction ⁻¹' {0}) := by
    simpa [Set.preimage_compl] using hO.isClosed_compl
  have hD' : IsDiscrete (χ.LFunction ⁻¹' {0}) := by
    simpa [Set.preimage_compl] using hD
  exact (hS.inter_right hcl).finite (hD'.mono Set.inter_subset_right)

/-- A zero `ρ ≠ 1` of `L(s, χ)` has `Re ρ < 1`, Mathlib nonvanishing on `Re s ≥ 1`. -/
lemma re_lt_one_of_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (h0 : χ.LFunction ρ = 0) (h1 : ρ ≠ 1) : ρ.re < 1 := by
  by_contra h
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr h1) (not_lt.mp h) h0

/-- Only finitely many zeros in `Re s ≥ -1/2`, `|Im s| ≤ T`, for a primitive character. -/
theorem zeros_rect_finite {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (T : ℝ) : {ρ | ρ ∈ Zall χ ∧ |ρ.im| ≤ T}.Finite := by
  set S : Set ℂ := Icc (-1 / 2 : ℝ) 1 ×ℂ Icc (-T) T with hS
  have hSc : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : {ρ | ρ ∈ Zall χ ∧ |ρ.im| ≤ T} ⊆ S ∩ χ.LFunction ⁻¹' {0} := by
    rintro ρ ⟨⟨h0, hre, h1⟩, him⟩
    refine ⟨?_, by simpa using h0⟩
    rw [hS, mem_reProdIm]
    exact ⟨⟨hre, (re_lt_one_of_zero χ h0 h1).le⟩, abs_le.mp him⟩
  refine Set.Finite.subset ?_ hsub
  by_cases hq : q = 1
  · subst hq
    rw [LFunction_modOne_fun]
    exact hSc.inter_riemannZetaZeros_finite
  · exact zeros_compact_finite_of_ne_one (ne_one_of_isPrimitive hχ hq) hSc

/-- A primitive character's `L(s, χ)` has finite meromorphic order everywhere. -/
lemma order_LFunction_ne_top {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (z : ℂ) : meromorphicOrderAt χ.LFunction z ≠ ⊤ := by
  rcases eq_or_ne z 1 with rfl | hz
  · by_cases hq : q = 1
    · subst hq
      rw [LFunction_modOne_fun, LeanLab.PNTPort.ExplicitPsi1.order_zeta_one]
      simp
    · have hne := ne_one_of_isPrimitive hχ hq
      have hA := analyticAt_LFunction χ (s := 1) (Or.inr hne)
      rw [hA.meromorphicOrderAt_eq,
        analyticOrderAt_eq_zero.mpr (Or.inr (DirichletCharacter.LFunction_apply_one_ne_zero hne))]
      simp
  · rw [order_LFunction_of_ne_one χ hz]; simp

/-- `F` is meromorphic everywhere. -/
lemma meromorphicAt_Fchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (z : ℂ) : MeromorphicAt (Fchi χ x) z := by
  have hL := meromorphicAt_LFunction χ z
  have hk : MeromorphicAt (fun s : ℂ => (x : ℂ) ^ s / ((s + 1) * (s + 2))) z :=
    (analyticAt_const.cpow analyticAt_id (ofReal_mem_slitPlane.mpr hx)).meromorphicAt.div
      ((analyticAt_id.add analyticAt_const).mul (analyticAt_id.add analyticAt_const)).meromorphicAt
  exact (hL.deriv.div hL).neg.mul hk

/-- `F` has at most simple poles in `Re s ≥ -1/2`, primitive `χ`. -/
lemma order_Fchi_ge {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {x : ℝ} (hx : 0 < x) {z : ℂ} (hre : -1 / 2 ≤ z.re) :
    -1 ≤ meromorphicOrderAt (Fchi χ x) z := by
  have hz := meromorphicAt_LFunction χ z
  have hF : Fchi χ x = (fun s => -logDeriv χ.LFunction s) *
      (fun s : ℂ => (x : ℂ) ^ s / ((s + 1) * (s + 2))) := by
    funext s; simp [Fchi, logDeriv_apply]
  have hk := analyticAt_kernel2 hx (ne_neg_one_of_re hre) (ne_neg_two_of_re hre)
  have hLd : MeromorphicAt (fun s => -logDeriv χ.LFunction s) z := (hz.deriv.div hz).neg
  rw [hF, meromorphicOrderAt_mul hLd hk.meromorphicAt]
  have h1 : meromorphicOrderAt (fun s => -logDeriv χ.LFunction s) z =
      meromorphicOrderAt (logDeriv χ.LFunction) z :=
    (meromorphicOrderAt_neg (f := logDeriv χ.LFunction)).symm
  rw [h1]
  have hlog : -1 ≤ meromorphicOrderAt (logDeriv χ.LFunction) z := by
    by_cases h : meromorphicOrderAt χ.LFunction z = 0
    · refine le_trans ?_ (meromorphicOrderAt_logDeriv_nonneg hz h)
      exact WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by norm_num)
    · rw [meromorphicOrderAt_logDeriv_eq_neg_one hz h (order_LFunction_ne_top hχ z)]
  calc (-1 : WithTop ℤ) = -1 + 0 := by simp
    _ ≤ _ := add_le_add hlog hk.meromorphicOrderAt_nonneg

/-- `F` is analytic at `z ≠ 1` with `Re z ≥ -1/2` and `L(z, χ) ≠ 0`. -/
lemma analyticAt_Fchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    {z : ℂ} (hre : -1 / 2 ≤ z.re) (h1 : z ≠ 1 ∨ χ ≠ 1) (hz : χ.LFunction z ≠ 0) :
    AnalyticAt ℂ (Fchi χ x) z := by
  have hA := analyticAt_LFunction χ h1
  exact ((hA.deriv.div hA hz).neg).mul
    (analyticAt_kernel2 hx (ne_neg_one_of_re hre) (ne_neg_two_of_re hre))

/-- The residue of `F` at `1`: `x/6` for `q = 1`, else `0` since `L(1, χ) ≠ 0`. -/
lemma residue_Fchi_at_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {x : ℝ} (hx : 0 < x) : residue (Fchi χ x) 1 = if q = 1 then (x : ℂ) / 6 else 0 := by
  by_cases hq : q = 1
  · subst hq
    rw [if_pos rfl]
    have hF : Fchi χ x = Fchi (1 : DirichletCharacter ℂ 1) x := by
      funext s; simp only [Fchi, LFunction_modOne_fun]
    rw [hF]
    exact residue_eq_of_tendsto (residue_Fchi_one hx)
  · rw [if_neg hq]
    have hne := ne_one_of_isPrimitive hχ hq
    exact residue_eq_zero_of_not_pole_of_meromorphicAt (meromorphicAt_Fchi χ hx 1)
      (analyticAt_Fchi χ hx (by norm_num) (Or.inr hne)
        (DirichletCharacter.LFunction_apply_one_ne_zero hne)).meromorphicOrderAt_nonneg

/-- Border points of `[-1/2, c] × [-T, T]` lie on one of the four sides. Elementary. -/
lemma border_cases2 {c T : ℝ} {z : ℂ}
    (hz : z ∈ RectangleBorder ⟨-1 / 2, -T⟩ ⟨c, T⟩) :
    z.im = -T ∨ z.re = -1 / 2 ∨ z.im = T ∨ z.re = c := by
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hz
  rcases hz with ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩) | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- Membership in the rectangle `[-1/2, c] × [-T, T]`. Elementary. -/
lemma mem_rect2 {c T : ℝ} (hc : -1 / 2 ≤ c) (hT : 0 ≤ T) {z : ℂ} :
    z ∈ Rectangle ⟨-1 / 2, -T⟩ ⟨c, T⟩ ↔ (-1 / 2 ≤ z.re ∧ z.re ≤ c) ∧ (-T ≤ z.im ∧ z.im ≤ T) := by
  simp only [Rectangle, mem_reProdIm]
  rw [uIcc_of_le hc, uIcc_of_le (by linarith)]
  simp

/-- Davenport ch. 17 and 19, the rectangle formula: if `L(s, χ)` has no zero on the border of
`[-1/2, 2] × [-T, T]`, the normalized rectangle integral of `F` is the sum of residues. -/
theorem rect_explicit_chi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {x T : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hbd : ∀ z ∈ RectangleBorder ⟨-1 / 2, -T⟩ ⟨2, T⟩, χ.LFunction z ≠ 0) :
    RectangleIntegral' (Fchi χ x) ⟨-1 / 2, -T⟩ ⟨2, T⟩ =
      (if q = 1 then (x : ℂ) / 6 else 0) -
        ∑ ρ ∈ ((zeros_rect_finite hχ T).toFinset), zterm χ x ρ := by
  set R := Rectangle (⟨-1 / 2, -T⟩ : ℂ) ⟨2, T⟩ with hRdef
  set Zf := (zeros_rect_finite hχ T).toFinset with hZf
  have hmem := fun z => mem_rect2 (c := 2) (T := T) (by norm_num) hT.le (z := z)
  have hRre : ∀ z ∈ R, -1 / 2 ≤ z.re := fun z hz => ((hmem z).mp hz).1.1
  have h1R : (1 : ℂ) ∈ R := by
    rw [hmem]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
  have hZfZ : ∀ ρ ∈ Zf, ρ ∈ Zall χ ∧ |ρ.im| ≤ T := by
    intro ρ hρ; rw [hZf, Set.Finite.mem_toFinset] at hρ; exact hρ
  have hZfR : ∀ ρ ∈ Zf, ρ ∈ R := by
    intro ρ hρ
    obtain ⟨⟨h0, hre, h1⟩, him⟩ := hZfZ ρ hρ
    rw [hmem]
    have := re_lt_one_of_zero χ h0 h1
    exact ⟨⟨hre, by linarith⟩, abs_le.mp him⟩
  have hgood : ∀ z ∈ R, z ≠ 1 → χ.LFunction z ≠ 0 → 0 ≤ meromorphicOrderAt (Fchi χ x) z :=
    fun z hz h1 hL => (analyticAt_Fchi χ hx (hRre z hz) (Or.inl h1) hL).meromorphicOrderAt_nonneg
  have hbR : RectangleBorder (⟨-1 / 2, -T⟩ : ℂ) ⟨2, T⟩ ⊆ R := rectangleBorder_subset_rectangle _ _
  have hP : ∀ z ∈ R, meromorphicOrderAt (Fchi χ x) z < 0 → z ∈ (insert 1 Zf : Finset ℂ) := by
    intro z hz hneg
    by_contra hns
    simp only [Finset.mem_insert, not_or] at hns
    obtain ⟨h1, hZ⟩ := hns
    have hL : χ.LFunction z ≠ 0 := by
      intro h; apply hZ; rw [hZf, Set.Finite.mem_toFinset]
      have hz' := (hmem z).mp hz
      exact ⟨⟨h, hz'.1.1, h1⟩, abs_le.mpr hz'.2⟩
    exact absurd (hgood z hz h1 hL) (not_le.mpr hneg)
  have hres := RectangleIntegral'_eq_sumResiduesIn (f := Fchi χ x)
    (z := ⟨-1 / 2, -T⟩) (w := ⟨2, T⟩) (by simp; norm_num) (by simp; linarith)
    (fun z _ => meromorphicAt_Fchi χ hx z)
    (by
      rw [Set.disjoint_left]
      intro z hz hneg
      simp only [mem_ofPred_eq] at hneg
      have hzR := hbR hz
      have hz1 : z ≠ 1 := by
        rintro rfl
        rcases border_cases2 hz with h | h | h | h <;> norm_num at h <;> linarith
      exact absurd (hgood z hzR hz1 (hbd z hz)) (not_le.mpr hneg))
    (by
      apply (insert 1 Zf : Finset ℂ).finite_toSet.subset
      intro z ⟨hz, hneg⟩
      exact hP z hz hneg)
    (fun z hz => order_Fchi_ge hχ hx (hRre z hz))
  rw [hres]
  have hS : R ∩ {z | meromorphicOrderAt (Fchi χ x) z < 0} =
      ((insert 1 Zf : Finset ℂ) : Set ℂ) ∩ {z | meromorphicOrderAt (Fchi χ x) z < 0} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hz, hneg⟩; exact ⟨hP z hz hneg, hneg⟩
    · rintro ⟨hz, hneg⟩
      refine ⟨?_, hneg⟩
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact h1R
      · exact hZfR z hz
  rw [sumResiduesIn_inter_eq_of_set_eq hS (fun z _ hz =>
    residue_eq_zero_of_not_pole_of_meromorphicAt (meromorphicAt_Fchi χ hx z) (not_lt.mp hz))]
  rw [sumResiduesIn, Finset.tsum_subtype' (insert 1 Zf) (fun z => residue (Fchi χ x) z)]
  have h1Z : (1 : ℂ) ∉ Zf := fun h => (hZfZ 1 h).1.2.2 rfl
  rw [Finset.sum_insert h1Z, residue_Fchi_at_one hχ hx]
  have hsum : ∑ ρ ∈ Zf, residue (Fchi χ x) ρ = ∑ ρ ∈ Zf, -zterm χ x ρ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    exact residue_eq_of_tendsto (residue_Fchi_zero χ hχ hx (hZfZ ρ hρ).1)
  rw [hsum, Finset.sum_neg_distrib]
  ring

end LeanLab.Linnik.ExplicitFormula
