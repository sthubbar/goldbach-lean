module

public import LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122

/-!
# The rectangle left of `Re s = -1/2` for primitive `L(s, χ)`: the trivial zeros

Unit P1122-0016, ROUTE BURST burst-20261122 session S2, port step 5. AI wrote the Lean code.
Binary Goldbach is OPEN; nothing here bears on it directly. Davenport, Multiplicative Number
Theory, second edition, ch. 19 pp. 115 to 117, modelled on the zeta files `TrivialRect.lean`
`rect_left` and `TrivialLimit.lean`.

For primitive `χ ≠ 1` of parity `a`, `x > 0`, `T > 0`, `K ≥ 0`, the residue theorem
`RectangleIntegral'_eq_sumResiduesIn`, ported from PrimeNumberTheoremAnd, Apache-2.0, applied to
the sharp kernel integrand `-(L'/L)(s, χ) xˢ/s` on `[-2K - 1/2, -1/2] × [-T, T]` gives

`rect_left_char`: `(1/2πi) ∮ = Σ_{k < K} x^{-m_k}/m_k`, `m_k = 2k + 2 - a`,

the trivial zeros `-m_k` inside being exactly `-1, -3, ..., -(2K - 1)` for `a = 1` and
`-2, -4, ..., -2K` for `a = 0`. `tendsto_rect_left_char`: as `K → ∞` these tend to
`-(1/2) log(1 - x⁻²)` for `a = 0` and `(1/2) log((1 + x⁻¹)/(1 - x⁻¹))` for `a = 1`, `x > 1`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122

open Complex Filter Topology Set
open scoped Real

lemma rect_mem {σ T : ℝ} (hσ : σ ≤ -1 / 2) (hT : 0 ≤ T) {z : ℂ} :
    z ∈ Rectangle ⟨σ, -T⟩ ⟨-1 / 2, T⟩ ↔ (σ ≤ z.re ∧ z.re ≤ -1 / 2) ∧ (-T ≤ z.im ∧ z.im ≤ T) := by
  simp only [Rectangle, mem_reProdIm]
  rw [uIcc_of_le hσ, uIcc_of_le (by linarith)]
  simp

lemma rect_border_cases {σ T : ℝ} {z : ℂ} (hz : z ∈ RectangleBorder ⟨σ, -T⟩ ⟨-1 / 2, T⟩) :
    z.im = -T ∨ z.re = σ ∨ z.im = T ∨ z.re = -1 / 2 := by
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hz
  rcases hz with ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩) | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- The sharp kernel integrand is meromorphic everywhere for `χ ≠ 1`. -/
lemma meromorphicAt_sharp {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {x : ℝ} (hx : 0 < x) (z : ℂ) :
    MeromorphicAt (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) z := by
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) z :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  exact (((hA.deriv.meromorphicAt.div hA.meromorphicAt).neg).mul
    (analyticAt_xpow hx z).meromorphicAt).div analyticAt_id.meromorphicAt

/-- Away from `0` and the zeros of `L(s, χ)` the integrand is analytic. -/
lemma analyticAt_sharp {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {x : ℝ} (hx : 0 < x) {z : ℂ} (h0 : z ≠ 0) (hL : DirichletCharacter.LFunction χ z ≠ 0) :
    AnalyticAt ℂ (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) z := by
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) z :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  exact (((hA.deriv.div hA hL).neg).mul (analyticAt_xpow hx z)).div analyticAt_id h0

/-- At most simple poles on `Re s ≤ 0`, `s ≠ 0`: the zeros there are the simple trivial ones. -/
lemma order_sharp_ge {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    {x : ℝ} (hx : 0 < x) {z : ℂ} (hre : z.re ≤ 0) (h0 : z ≠ 0) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) z := by
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) z :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hk : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s / s) z :=
    (analyticAt_xpow hx z).div analyticAt_id h0
  have hF : (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) =
      (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) * (fun s : ℂ => (x : ℂ) ^ s / s) := by
    funext s; simp only [Pi.mul_apply, logDeriv_apply]; ring
  have hLm : MeromorphicAt (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) z :=
    (hA.deriv.meromorphicAt.div hA.meromorphicAt).neg
  rw [hF, meromorphicOrderAt_mul hLm hk.meromorphicAt]
  have h1 : meromorphicOrderAt (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) z =
      meromorphicOrderAt (logDeriv (DirichletCharacter.LFunction χ)) z :=
    (meromorphicOrderAt_neg (f := logDeriv (DirichletCharacter.LFunction χ))).symm
  rw [h1]
  have hlog : (-1 : WithTop ℤ) ≤ meromorphicOrderAt (logDeriv (DirichletCharacter.LFunction χ)) z := by
    by_cases hLz : DirichletCharacter.LFunction χ z = 0
    · obtain ⟨k, hkz⟩ := (LFunction_eq_zero_iff_of_re_nonpos hprim hχ ha hre).mp hLz
      have ho := (analyticOrderAt_trivial hprim hχ ha k).1
      rw [← hkz] at ho
      have hmo : meromorphicOrderAt (DirichletCharacter.LFunction χ) z = 1 := by
        rw [hA.meromorphicOrderAt_eq, ho]; rfl
      rw [meromorphicOrderAt_logDeriv_eq_neg_one hA.meromorphicAt (by rw [hmo]; decide)
        (by rw [hmo]; decide)]
    · have hmo : meromorphicOrderAt (DirichletCharacter.LFunction χ) z = 0 := by
        rw [hA.meromorphicOrderAt_eq, hA.analyticOrderAt_eq_zero.mpr hLz]; rfl
      exact le_trans (by decide) (meromorphicOrderAt_logDeriv_nonneg hA.meromorphicAt hmo)
  calc (-1 : WithTop ℤ) = -1 + 0 := by simp
    _ ≤ _ := add_le_add hlog hk.meromorphicOrderAt_nonneg

/-- Residue at the trivial zero `-n`, `n = 2k + 2 - a`, in the indexing of `rect_left_char`. -/
lemma residue_trivial_index {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    {x : ℝ} (hx : 0 < x) (k : ℕ) :
    residue (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) (-((2 * k + 2 - a : ℕ) : ℂ)) =
      (x : ℂ) ^ (-((2 * k + 2 - a : ℕ) : ℂ)) / ((2 * k + 2 - a : ℕ) : ℂ) := by
  have ha1 : a ≤ 1 := by rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 2 * k + 2 - a = a + 2 * j := by
    rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨k + 1, by omega⟩
    · exact ⟨k, by omega⟩
  have hc : ((2 * k + 2 - a : ℕ) : ℂ) = (a : ℂ) + 2 * j := by rw [hj]; push_cast; ring
  rw [hc]
  exact residue_trivial_char hprim hχ ha j (by omega) hx

/-- **The residue sum left of `Re s = -1/2`.** Davenport ch. 19 pp. 115 and 116, displays (2)
and (3), the part of the residue sum from the trivial zeros: for primitive `χ ≠ 1` of parity `a`,
`x > 0`, `T > 0`, on the rectangle `[-2K - 1/2, -1/2] × [-T, T]`,
`(1/2πi) ∮ -(L'/L)(s, χ) xˢ/s ds = Σ_{k < K} x^{-m_k}/m_k`, `m_k = 2k + 2 - a`. -/
theorem rect_left_char {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    {x T : ℝ} (hx : 0 < x) (hT : 0 < T) (K : ℕ) :
    RectangleIntegral' (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s)
        ⟨-2 * (K : ℝ) - 1 / 2, -T⟩ ⟨-1 / 2, T⟩ =
      ∑ k ∈ Finset.range K, (x : ℂ) ^ (-((2 * k + 2 - a : ℕ) : ℂ)) / ((2 * k + 2 - a : ℕ) : ℂ) := by
  classical
  set F : ℂ → ℂ := fun s => -(deriv (DirichletCharacter.LFunction χ) s /
    DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s with hFdef
  have ha1 : a ≤ 1 := by rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num
  set σ : ℝ := -2 * (K : ℝ) - 1 / 2 with hσ
  have hσle : σ ≤ -1 / 2 := by rw [hσ]; linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  set R := Rectangle (⟨σ, -T⟩ : ℂ) ⟨-1 / 2, T⟩ with hRdef
  have hmem := fun z => rect_mem (σ := σ) (T := T) hσle hT.le (z := z)
  set tz : ℕ → ℂ := fun k => -((2 * k + 2 - a : ℕ) : ℂ) with htz
  set P : Finset ℂ := (Finset.range K).image tz with hP
  have hRre : ∀ z ∈ R, z.re ≤ -1 / 2 := fun z hz => ((hmem z).mp hz).1.2
  have hR0 : ∀ z ∈ R, z ≠ 0 := by
    intro z hz h; have := hRre z hz; rw [h] at this; norm_num at this
  have hRnp : ∀ z ∈ R, z.re ≤ 0 := fun z hz => by linarith [hRre z hz]
  have htz_re : ∀ k : ℕ, (tz k).re = -((2 * k + 2 - a : ℕ) : ℝ) := by intro k; simp [htz]
  have htz_im : ∀ k : ℕ, (tz k).im = 0 := by intro k; simp [htz]
  -- a zero of `L` in the rectangle is some `tz k`, `k < K`
  have hzero : ∀ z ∈ R, DirichletCharacter.LFunction χ z = 0 → ∃ k < K, tz k = z := by
    intro z hz hL
    obtain ⟨j, hj⟩ := (LFunction_eq_zero_iff_of_re_nonpos hprim hχ ha (hRnp z hz)).mp hL
    have hre := (hmem z).mp hz
    rw [hj] at hre
    simp at hre
    obtain ⟨⟨h1, h2⟩, -⟩ := hre
    -- `1/2 ≤ a + 2j ≤ 2K + 1/2`
    have hlo : 1 ≤ a + 2 * j := by
      have : (1 / 2 : ℝ) ≤ ((a + 2 * j : ℕ) : ℝ) := by push_cast; linarith
      have : (0 : ℝ) < ((a + 2 * j : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hhi : a + 2 * j ≤ 2 * K := by
      have : ((a + 2 * j : ℕ) : ℝ) < 2 * K + 1 := by push_cast; linarith
      have : a + 2 * j < 2 * K + 1 := by exact_mod_cast this
      omega
    rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · refine ⟨j - 1, by omega, ?_⟩
      rw [hj, htz]
      simp only
      have : (2 * (j - 1) + 2 - 0 : ℕ) = 0 + 2 * j := by omega
      rw [this]; push_cast; ring
    · refine ⟨j, by omega, ?_⟩
      rw [hj, htz]
      simp only
      have : (2 * j + 2 - 1 : ℕ) = 1 + 2 * j := by omega
      rw [this]; push_cast; ring
  have hgood : ∀ z ∈ R, DirichletCharacter.LFunction χ z ≠ 0 → 0 ≤ meromorphicOrderAt F z :=
    fun z hz hL => (analyticAt_sharp hχ hx (hR0 z hz) hL).meromorphicOrderAt_nonneg
  have hPR : ∀ z ∈ P, z ∈ R := by
    intro z hz
    rw [hP, Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    have hk' : k < K := Finset.mem_range.mp hk
    rw [hmem, htz_re, htz_im]
    have hb1 : 1 ≤ 2 * k + 2 - a := by omega
    have hb2 : 2 * k + 2 - a ≤ 2 * K := by omega
    have c1 : (1 : ℝ) ≤ ((2 * k + 2 - a : ℕ) : ℝ) := by exact_mod_cast hb1
    have c2 : ((2 * k + 2 - a : ℕ) : ℝ) ≤ 2 * K := by exact_mod_cast hb2
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hpoles : ∀ z ∈ R, meromorphicOrderAt F z < 0 → z ∈ P := by
    intro z hz hneg
    have hL : DirichletCharacter.LFunction χ z = 0 := by
      by_contra hL; exact absurd (hgood z hz hL) (not_le.mpr hneg)
    obtain ⟨k, hk, hkz⟩ := hzero z hz hL
    rw [hP, Finset.mem_image]
    exact ⟨k, Finset.mem_range.mpr hk, hkz⟩
  have hbR : RectangleBorder (⟨σ, -T⟩ : ℂ) ⟨-1 / 2, T⟩ ⊆ R := rectangleBorder_subset_rectangle _ _
  have hres := RectangleIntegral'_eq_sumResiduesIn (f := F)
    (z := ⟨σ, -T⟩) (w := ⟨-1 / 2, T⟩) (by simp; linarith) (by simp; linarith)
    (fun z _ => meromorphicAt_sharp hχ hx z)
    (by
      rw [Set.disjoint_left]
      intro z hz hneg
      simp only [mem_ofPred_eq] at hneg
      have hzR := hbR hz
      have hL : DirichletCharacter.LFunction χ z ≠ 0 := by
        intro hL
        obtain ⟨k, hk, hkz⟩ := hzero z hzR hL
        have hre : z.re = -((2 * k + 2 - a : ℕ) : ℝ) := by rw [← hkz, htz_re]
        have him : z.im = 0 := by rw [← hkz, htz_im]
        rcases rect_border_cases hz with h' | h' | h' | h'
        · rw [him] at h'; linarith
        · rw [hre, hσ] at h'
          have : ((4 * K + 1 : ℕ) : ℝ) = ((2 * (2 * k + 2 - a) : ℕ) : ℝ) := by
            push_cast; linarith
          have := Nat.cast_injective this
          omega
        · rw [him] at h'; linarith
        · rw [hre] at h'
          have : ((1 : ℕ) : ℝ) = ((2 * (2 * k + 2 - a) : ℕ) : ℝ) := by
            push_cast; linarith
          have := Nat.cast_injective this
          omega
      exact absurd (hgood z hzR hL) (not_le.mpr hneg))
    (by
      apply (P : Set ℂ).toFinite.subset
      intro z ⟨hz, hneg⟩
      exact hpoles z hz hneg)
    (fun z hz => order_sharp_ge hprim hχ ha hx (hRnp z hz) (hR0 z hz))
  rw [hres]
  have hS : R ∩ {z | meromorphicOrderAt F z < 0} =
      (P : Set ℂ) ∩ {z | meromorphicOrderAt F z < 0} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hz, hneg⟩; exact ⟨hpoles z hz hneg, hneg⟩
    · rintro ⟨hz, hneg⟩; exact ⟨hPR z hz, hneg⟩
  rw [sumResiduesIn_inter_eq_of_set_eq hS (fun z _ hz =>
    residue_eq_zero_of_not_pole_of_meromorphicAt (meromorphicAt_sharp hχ hx z) (not_lt.mp hz))]
  rw [sumResiduesIn, Finset.tsum_subtype' P (fun z => residue F z)]
  have hinj : Set.InjOn tz ((Finset.range K : Finset ℕ) : Set ℕ) := by
    intro i hi j hj h
    have hi' : i < K := Finset.mem_range.mp hi
    have hj' : j < K := Finset.mem_range.mp hj
    have := congr_arg Complex.re h
    rw [htz_re, htz_re, neg_inj] at this
    have := Nat.cast_injective this
    omega
  rw [hP, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro k _
  exact residue_trivial_index hprim hχ ha hx k

/-- **The trivial zero part as `K → ∞`.** Davenport ch. 19 pp. 115 and 116, the sums over `m`
in displays (2) and (3): for `x > 1` the rectangle integrals of `rect_left_char` tend to
`-(1/2) log(1 - x⁻²)` for `a = 0` and to `(1/2)(log(1 + x⁻¹) - log(1 - x⁻¹))` for `a = 1`. -/
theorem tendsto_rect_left_char {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    {x T : ℝ} (hx : 1 < x) (hT : 0 < T) :
    Tendsto (fun K : ℕ => RectangleIntegral' (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s)
        ⟨-2 * (K : ℝ) - 1 / 2, -T⟩ ⟨-1 / 2, T⟩) atTop
      (𝓝 (if a = 0 then ((-(1 / 2) * Real.log (1 - (x⁻¹) ^ 2) : ℝ) : ℂ)
        else (((1 / 2) * (Real.log (1 + x⁻¹) - Real.log (1 - x⁻¹)) : ℝ) : ℂ))) := by
  have hx0 : 0 < x := by linarith
  simp_rw [rect_left_char hprim hχ ha hx0 hT]
  rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · simp only [↓reduceIte]
    have h := (Complex.hasSum_ofReal.mpr (hasSum_trivial_even_real hx)).tendsto_sum_nat
    refine h.congr (fun K => Finset.sum_congr rfl (fun k _ => ?_))
    rw [trivial_term_eq x, Nat.sub_zero]
  · simp only [one_ne_zero, ↓reduceIte]
    have h := (Complex.hasSum_ofReal.mpr (hasSum_trivial_odd_real hx)).tendsto_sum_nat
    refine h.congr (fun K => Finset.sum_congr rfl (fun k _ => ?_))
    rw [trivial_term_eq x, show 2 * k + 2 - 1 = 2 * k + 1 by omega]

end LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122
