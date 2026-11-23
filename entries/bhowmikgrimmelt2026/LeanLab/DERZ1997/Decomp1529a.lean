module

public import Mathlib
public import LeanLab.PNTPort.DirichletZF.SiegelSigns
public import LeanLab.Routes.Decomp1551c
public import LeanLab.PNTPort.ZetaZeros.Sym
public import LeanLab.DERZ1997.Statements
public import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Unit U-1529, run 20261025T2003Z-426, DECOMPOSE of the GRH inputs of P0011,
Deshouillers, Effinger, te Riele, Zinoviev 1997, ERA-AMS 3, 99-104.

File a: zeros of the Riemann zeta function and of Dirichlet L-functions.
* `zetaZeros T`, the non-trivial zeros `ρ` (open strip `0 < Re ρ < 1`) with `|Im ρ| ≤ T`;
  `zetaZerosPos T` those with `0 < Im ρ ≤ T`; `zetaMult ρ`, the order of the zero.
* `LZeros χ T`, `LMult χ ρ`, the same for `DirichletCharacter.LFunction χ`.
Leaves: finiteness, the zero-free range below height 14, the explicit Riemann-von Mangoldt
formula in Rosser's form (Rosser 1941, Theorem 19), the count in unit windows, the sum of
`1/|ρ|` up to height T, and the analogues for `L(s, χ)` (McCurley 1984, Theorem 2.1).
Multiplicities are carried by `analyticOrderNatAt`, so no simplicity of zeros is assumed.
Sums over zeros run over `hfin.toFinset` for a finiteness proof `hfin`, which leaf
`zetaZeros_finite` (resp. `LZeros_finite`) supplies.

Source when the original is not at hand: Davenport, Multiplicative Number Theory, 3rd ed.,
chapters 15-17 and 19.
AI-written Lean code, Claude, 2026-10-25. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.DERZ1997.Decomp1529a
open Complex Filter Topology MeasureTheory Set

/-- Non-trivial zeros of `ζ` with `|Im ρ| ≤ T`. -/
def zetaZeros (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

/-- Non-trivial zeros of `ζ` with `0 < Im ρ ≤ T`. -/
def zetaZerosPos (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- Non-trivial zeros of `ζ` with `T < Im ρ ≤ T + 1`. -/
def zetaZerosWindow (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < ρ.im ∧ ρ.im ≤ T + 1}

/-- Multiplicity of a zero of `ζ`. -/
noncomputable def zetaMult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- Zeros of `L(s, χ)` in the open strip with `|Im ρ| ≤ T`. -/
def LZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Set ℂ :=
  {ρ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

/-- Multiplicity of a zero of `L(s, χ)`. -/
noncomputable def LMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/-- Reciprocal-square integral used for finite partial summation.
Helfgott arXiv:1305.2897v4 page 38, partial summation behind equation 4.26. -/
theorem reciprocal_integral193 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / t ^ 2) = 1 / a - 1 / b := by
  have hn (t : ℝ) (ht : t ∈ Set.uIcc a b) : t ≠ 0 := by
    rw [Set.uIcc_of_le hab] at ht
    linarith [ht.1]
  have hd (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivAt (fun t : ℝ => -(1 / t)) (1 / t ^ 2) t := by
    convert ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) (hn t ht)).neg using 1
    · ext y; simp
    · simp only [zero_mul, zero_sub, mul_one, neg_div, neg_neg, id_eq]
  have hi : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro t ht
    exact pow_ne_zero _ (hn t ht)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  linarith

/-- Finite weighted partial summation for real ordinates, including integrability.
Helfgott arXiv:1305.2897v4 page 38, the partial summation step. -/
theorem reciprocal_sum_partial193 {ι : Type*} (s : Finset ι) (x w : ι → ℝ)
    {a T : ℝ} (ha : 0 < a) (haT : a ≤ T)
    (hx : ∀ i ∈ s, a ≤ x i ∧ x i ≤ T) :
    IntervalIntegrable (fun t => (∑ i ∈ s.filter (fun i => x i < t), w i) / t ^ 2) volume a T ∧
    (∑ i ∈ s, w i / x i) = (∑ i ∈ s, w i) / T +
      ∫ t in a..T, (∑ i ∈ s.filter (fun i => x i < t), w i) / t ^ 2 := by
  classical
  let f : ℝ → ℝ := fun t => 1 / t ^ 2
  have hi : IntervalIntegrable f volume a T := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro t ht
    rw [Set.uIcc_of_le haT] at ht
    exact pow_ne_zero _ (show t ≠ 0 by linarith [ht.1])
  have hint (i : ι) : IntervalIntegrable ((Ioi (x i)).indicator (fun t => w i * f t)) volume a T :=
    ⟨(hi.1.const_mul _).indicator measurableSet_Ioi,
      (hi.2.const_mul _).indicator measurableSet_Ioi⟩
  have hpoint (t : ℝ) : (∑ i ∈ s.filter (fun i => x i < t), w i) / t ^ 2 =
      ∑ i ∈ s, (Ioi (x i)).indicator (fun t => w i * f t) t := by
    rw [Finset.sum_div, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : x i < t <;> simp [Set.indicator, h, f, div_eq_mul_inv]
  constructor
  · have he : (fun t => (∑ i ∈ s.filter (fun i => x i < t), w i) / t ^ 2) =
        fun t => ∑ i ∈ s, (Ioi (x i)).indicator (fun t => w i * f t) t := funext hpoint
    rw [he]
    convert IntervalIntegrable.sum s (fun i _ => hint i) using 1
    ext t; simp only [Finset.sum_apply]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  have hterm (i : ι) (his : i ∈ s) :
      (∫ t in a..T, (Ioi (x i)).indicator (fun t => w i * f t) t) =
        w i / x i - w i / T := by
    rw [intervalIntegral.integral_of_le haT,
      MeasureTheory.integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_comm, Ioc_inter_Ioi,
      sup_eq_right.mpr (hx i his).1,
      ← intervalIntegral.integral_of_le (hx i his).2,
      intervalIntegral.integral_const_mul]
    rw [show (∫ t in x i..T, f t) = 1 / x i - 1 / T from
      reciprocal_integral193 (ha.trans_le (hx i his).1) (hx i his).2]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_div]
  ring

/-- The rounded Rosser upper budget exceeds one at every allowed height.
This is a limitation of using that bound alone for the height-14 zero-free claim.
Davenport chapter 15 page 98, the rounded budget in rvm_upper. -/
theorem rosser_budget_gt_one193 {T : ℝ} (hT : Real.exp 1 ≤ T) :
    1 < T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8
      + 0.14 * Real.log T + 0.45 * Real.log (Real.log T) + 1.6 := by
  have ht0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlog : 1 ≤ Real.log T := (Real.le_log_iff_exp_le ht0).mpr hT
  have hll : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlog
  have hu : 0 < T / (2 * Real.pi) := by positivity
  have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hu) hu.le
  have he : T / (2 * Real.pi) * (T / (2 * Real.pi))⁻¹ = 1 := mul_inv_cancel₀ hu.ne'
  nlinarith

/-! ### Zeta zeros -/

/-- LEAF. For every real `T` there are only finitely many non-trivial zeros of `ζ` with
`|Im ρ| ≤ T`: `ζ` is analytic off `s = 1`, has a pole at 1, does not vanish on `Re s = 1`, and
by the functional equation does not vanish on `Re s = 0`, so zeros cannot accumulate in the
closed rectangle. Davenport ch. 15, p. 97, and Mathlib's `riemannZeta_ne_zero_of_one_le_re`.
Unit U-1529. -/
theorem zetaZeros_finite (T : ℝ) : (zetaZeros T).Finite := by
  have hf := (IsCompact.reProdIm (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
    (isCompact_Icc : IsCompact (Set.Icc (-T) T))).inter_riemannZetaZeros_finite
  apply hf.subset
  intro z hz
  refine ⟨?_, hz.1⟩
  exact ⟨⟨hz.2.1.le, hz.2.2.1.le⟩, (abs_le.mp hz.2.2.2)⟩

/-- LEAF. Non-trivial zeros are symmetric under complex conjugation, since
`ζ(conj s) = conj ζ(s)`. Davenport ch. 8, p. 61. Unit U-1529. -/
theorem conj_mem_zetaZeros {T : ℝ} {ρ : ℂ} (h : ρ ∈ zetaZeros T) :
    starRingEnd ℂ ρ ∈ zetaZeros T := by
  dsimp [zetaZeros] at *
  rcases h with ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [riemannZeta_conj, h1, map_zero]
  · exact h2
  · exact h3
  · exact (abs_neg ρ.im).symm ▸ h4

/-- LEAF. Every non-trivial zero has multiplicity at least 1: `ζ` is analytic at `ρ ≠ 1`,
vanishes there, and is not identically zero near `ρ`. Davenport ch. 15. Unit U-1529. -/
theorem one_le_zetaMult {T : ℝ} {ρ : ℂ} (h : ρ ∈ zetaZeros T) : 1 ≤ zetaMult ρ := by
  dsimp [zetaMult, zetaZeros, analyticOrderNatAt] at *
  have h1 : analyticOrderAt riemannZeta ρ ≠ 0 := by
    intro h_eq
    have h2 := analyticOrderAt_eq_zero.mp h_eq
    cases h2 with
    | inl hna =>
      have ha : AnalyticAt ℂ riemannZeta ρ := by
        have h_nhd : AnalyticOnNhd ℂ riemannZeta {1}ᶜ := by
          exact DifferentiableOn.analyticOnNhd differentiableOn_riemannZeta isOpen_compl_singleton
        apply h_nhd
        intro h_eq_1
        rw [Set.mem_singleton_iff] at h_eq_1
        rcases h with ⟨-, h2, h3, -⟩
        rw [h_eq_1] at h3
        norm_num at h3
      exact hna ha
    | inr hne =>
      exact hne h.1
  have h_not_top : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro h_top
    have h_ev : riemannZeta =ᶠ[nhds ρ] 0 := analyticOrderAt_eq_top.mp h_top
    have h2 : AnalyticOnNhd ℂ riemannZeta {1}ᶜ := by
      exact DifferentiableOn.analyticOnNhd differentiableOn_riemannZeta isOpen_compl_singleton
    have h3 : AnalyticOnNhd ℂ (fun (_ : ℂ) => (0 : ℂ)) ({1}ᶜ : Set ℂ) := analyticOnNhd_const
    have h4 : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two) (1 : ℂ)).isPreconnected
    have h5 : ρ ∈ ({1}ᶜ : Set ℂ) := by
      intro h_eq
      rw [Set.mem_singleton_iff] at h_eq
      rcases h with ⟨-, h_re2, h_re3, -⟩
      rw [h_eq] at h_re3
      norm_num at h_re3
    have h6 : ∃ᶠ (z : ℂ) in nhdsWithin ρ {ρ}ᶜ, riemannZeta z = (0 : ℂ) := by
      apply Filter.Frequently.mono (Filter.Eventually.frequently (eventually_nhdsWithin_of_eventually_nhds h_ev))
      intro x hx
      exact hx
    have h7 := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq h2 h3 h4 h5 h6
    have h8 : riemannZeta 2 = 0 := by
      have h2_mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
        intro h_eq
        rw [Set.mem_singleton_iff] at h_eq
        norm_num at h_eq
      exact h7 h2_mem
    have h9 : riemannZeta 2 ≠ 0 := by
      rw [riemannZeta_two]
      norm_num
    exact h9 h8
  change 1 ≤ (analyticOrderAt riemannZeta ρ).toNat
  generalize h_order : analyticOrderAt riemannZeta ρ = ord
  cases ord with
  | top => exact False.elim (h_not_top h_order)
  | coe n =>
    rw [ENat.toNat_natCast]
    have h4 : (n : ℕ∞) ≠ 0 := by
      rw [← h_order]
      exact h1
    exact Nat.pos_of_ne_zero (WithTop.coe_ne_zero.mp h4)

/-- Reflection pairs the two ordinate signs with multiplicity when real zeros are absent.
Davenport chapter 15 page 97, from the functional equation. -/
theorem zeta_count_both193 {T : ℝ} (hf : (zetaZeros T).Finite) (hp : (zetaZerosPos T).Finite)
    (hreal : ∀ ρ ∈ zetaZeros T, ρ.im ≠ 0) :
    (∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℝ)) =
      2 * ∑ ρ ∈ hp.toFinset, (zetaMult ρ : ℝ) := by
  classical
  let s := hf.toFinset
  let p := s.filter (fun ρ => 0 < ρ.im)
  let n := s.filter (fun ρ => ¬0 < ρ.im)
  have he : p = hp.toFinset := by
    ext ρ
    simp only [p, s, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hρ, him⟩
      exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, him, (le_abs_self ρ.im).trans hρ.2.2.2⟩
    · intro hρ
      exact ⟨⟨hρ.1, hρ.2.1, hρ.2.2.1, by rw [abs_of_pos hρ.2.2.2.1]; exact hρ.2.2.2.2⟩,
        hρ.2.2.2.1⟩
  have hmap {ρ : ℂ} (hρ : ρ ∈ zetaZeros T) : 1 - ρ ∈ zetaZeros T := by
    refine ⟨LeanLab.PNTPort.ZetaZeros.zeta_one_sub_eq_zero hρ.2.1 hρ.2.2.1 hρ.1, ?_, ?_, ?_⟩
    · simp only [sub_re, one_re]; linarith [hρ.2.2.1]
    · simp only [sub_re, one_re]; linarith [hρ.2.1]
    · simpa only [sub_im, one_im, zero_sub, abs_neg] using hρ.2.2.2
  have hnp : (∑ ρ ∈ n, (zetaMult ρ : ℝ)) = ∑ ρ ∈ p, (zetaMult ρ : ℝ) := by
    apply Finset.sum_bij (fun ρ _ => 1 - ρ)
    · intro ρ hρ
      rcases Finset.mem_filter.mp hρ with ⟨hs, him⟩
      have hz := hf.mem_toFinset.mp hs
      refine Finset.mem_filter.mpr ⟨hf.mem_toFinset.mpr (hmap hz), ?_⟩
      simp only [sub_im, one_im, zero_sub]
      have hn := hreal ρ hz
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt him) hn)
    · intro a ha b hb h
      exact sub_right_inj.mp h
    · intro ρ hρ
      rcases Finset.mem_filter.mp hρ with ⟨hs, him⟩
      have hz := hf.mem_toFinset.mp hs
      refine ⟨1 - ρ, Finset.mem_filter.mpr ⟨hf.mem_toFinset.mpr (hmap hz), ?_⟩, ?_⟩
      · simp only [sub_im, one_im, zero_sub]
        linarith
      · ring
    · intro ρ hρ
      have hz := hf.mem_toFinset.mp (Finset.mem_filter.mp hρ).1
      exact_mod_cast (LeanLab.PNTPort.ZetaZeros.ord_one_sub hz.2.1 hz.2.2.1).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun ρ => 0 < ρ.im) (fun ρ => (zetaMult ρ : ℝ))
  change (∑ ρ ∈ p, (zetaMult ρ : ℝ)) + (∑ ρ ∈ n, (zetaMult ρ : ℝ)) = _ at hsplit
  rw [hnp, he] at hsplit
  linarith

/-- The rounded Rosser budget at height four is below two.
This supplies the doublet exclusion in the small-height partial zero-free proof. -/
theorem rosser_upper_four_lt_two193 : (4 : ℝ) / (2 * Real.pi) * Real.log (4 / (2 * Real.pi)) - 4 / (2 * Real.pi) + 7 / 8
      + 0.14 * Real.log 4 + 0.45 * Real.log (Real.log 4) + 1.6 < 2 := by
  let u : ℝ := 4 / (2 * Real.pi)
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
  have hul : (5/8 : ℝ) ≤ u := by
    dsimp [u]
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_d2]
  have hlog4 : Real.log 4 ≤ 7/5 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hlogpos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hll : Real.log (Real.log 4) ≤ Real.log 4 - 1 := Real.log_le_sub_one_of_pos hlogpos
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hu0) hu0.le
  have hquad := mul_nonneg (sub_nonneg.mpr hul) (sub_nonneg.mpr hu1)
  change u * Real.log u - u + 7/8 + 0.14 * Real.log 4 + 0.45 * Real.log (Real.log 4) + 1.6 < 2
  nlinarith

/-- The existing positive critical-line certificate also covers negative ordinates.
Reuses Routes.Decomp1551c.zeta_half_ne_zero and Mathlib conjugation.
This supplies the critical-line part of P0011 page 101 zero sums without assuming RH. -/
theorem zeta_critical_height_fourteen193 {ρ : ℂ} (hhalf : ρ.re = 1/2) (hheight : |ρ.im| ≤ 14) : riemannZeta ρ ≠ 0 := by
  rcases le_total 0 ρ.im with hi | hi
  · have he : ρ = (1/2 : ℂ) + (ρ.im : ℂ) * I := by
      apply Complex.ext <;> simp [hhalf]
    rw [he]
    exact LeanLab.Routes.Decomp1551c.zeta_half_ne_zero ρ.im hi ((le_abs_self _).trans hheight)
  · have he : starRingEnd ℂ ρ = (1/2 : ℂ) + ((-ρ.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hhalf]
    intro hz
    apply LeanLab.Routes.Decomp1551c.zeta_half_ne_zero (-ρ.im) (neg_nonneg.mpr hi)
      ((neg_le_abs _).trans hheight)
    rw [← he, riemannZeta_conj, hz, map_zero]

example : riemannZeta ((1/2 : ℂ) - I) ≠ 0 := by
  apply zeta_critical_height_fourteen193 <;> norm_num

/-! ### Zeros of Dirichlet L-functions -/

/-- LEAF. For each Dirichlet character `χ` and real `T`, `L(s, χ)` has only finitely many zeros
in the open strip with `|Im ρ| ≤ T`: it is entire for `χ ≠ 1`, has only the pole at 1 for the
trivial character, and is not identically zero, so zeros are isolated and cannot accumulate at
the pole. Davenport ch. 16 and 19; Mathlib `DirichletCharacter.LFunction_ne_zero_of_one_le_re`.
Unit U-1529. -/
theorem LZeros_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (LZeros χ T).Finite := by
  have hb : ∀ z ∈ LZeros χ T, ‖z‖ ≤ |T| + 2 := by
    intro z hz
    have ht : |z.im| ≤ |T| := hz.2.2.2.trans (le_abs_self T)
    have hr : |z.re| ≤ 1 := by rw [abs_of_pos hz.2.1]; exact hz.2.2.1.le
    exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have finite_zeros : ∀ (f : ℂ → ℂ), Differentiable ℂ f →
      (∃ z, f z ≠ 0) → {z : ℂ | ‖z‖ ≤ |T| + 2 ∧ f z = 0}.Finite := by
    intro f hf ⟨w, hw⟩
    have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
    have hd : f ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ := by
      simpa [Filter.codiscrete] using ha.preimage_zero_mem_codiscreteWithin hw (Set.mem_univ w)
        isConnected_univ
    have hclosed : IsClosed (f ⁻¹' {0}) := isClosed_singleton.preimage hf.continuous
    have hdiscrete : IsDiscrete (f ⁻¹' {0}) := by
      simpa using (mem_codiscrete'.mp hd).2
    have hcompact := (isCompact_closedBall (0 : ℂ) (|T| + 2)).inter_right hclosed
    have hfinite := hcompact.finite (hdiscrete.mono Set.inter_subset_right)
    convert hfinite using 1
    ext z
    simp [Metric.mem_closedBall, dist_zero_right]
  by_cases hχ : χ = 1
  · subst χ
    have hf := finite_zeros (DirichletCharacter.LFunctionTrivChar₁ q)
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q)
      ⟨1, DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q⟩
    apply hf.subset
    intro z hz
    refine ⟨hb z hz, ?_⟩
    have hz1 : z ≠ 1 := by intro h; simpa [h] using hz.2.2.1
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1]
    exact mul_eq_zero_of_right _ hz.1
  · have hf := finite_zeros (DirichletCharacter.LFunction χ)
      (DirichletCharacter.differentiable_LFunction hχ)
      ⟨2, DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)⟩
    apply hf.subset
    intro z hz
    exact ⟨hb z hz, hz.1⟩

/-- Changing level preserves positive-half-plane zeros and their orders away from the pole.
P0011 page 101, supporting zero sums; Mathlib LFunction_changeLevel, Euler factors. -/
theorem changeLevel_zero_data193 {m n : ℕ} [NeZero m] [NeZero n] (hmn : m ∣ n)
    (χ : DirichletCharacter ℂ m) {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    (DirichletCharacter.LFunction (DirichletCharacter.changeLevel hmn χ) ρ = 0 ↔
      DirichletCharacter.LFunction χ ρ = 0) ∧
    LMult (DirichletCharacter.changeLevel hmn χ) ρ = LMult χ ρ := by
  let P : ℂ → ℂ := fun s => ∏ p ∈ n.primeFactors, (1 - χ p * (p : ℂ)^(-s))
  have hP : P ρ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp' : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have hpow : ‖(p : ℂ)^(-ρ)‖ < 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < p)]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp' (by simpa using hρ)
    have hn : ‖χ p * (p : ℂ)^(-ρ)‖ < 1 := by
      rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one p)) hpow
    intro hh
    have he : χ p * (p : ℂ)^(-ρ) = 1 := (sub_eq_zero.mp hh).symm
    rw [he, norm_one] at hn
    exact lt_irrefl _ hn
  have hPD : Differentiable ℂ P := by
    intro s
    dsimp [P]
    apply DifferentiableAt.fun_finsetProd
    intro p hp
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ := by
    apply DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ))
    · intro s hs
      exact (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
    · exact isOpen_compl_singleton.mem_nhds hρ1
  have he : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hmn χ) =ᶠ[𝓝 ρ]
      (DirichletCharacter.LFunction χ * P) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hρ1] with s hs
    exact DirichletCharacter.LFunction_changeLevel hmn χ (Or.inr hs)
  constructor
  · rw [DirichletCharacter.LFunction_changeLevel hmn χ (Or.inr hρ1), mul_eq_zero]
    exact or_iff_left hP
  · dsimp [LMult, analyticOrderNatAt]
    rw [analyticOrderAt_congr he, analyticOrderAt_mul hL (hPD.analyticAt ρ),
      analyticOrderAt_eq_zero.mpr (Or.inr hP), add_zero]

/-! ### Links and vacuity -/

/-- Under P0011's `GRH`, every zero in `zetaZeros T` lies on the critical line. Proved. -/
theorem re_eq_half_of_GRH (hG : GRH) {T : ℝ} {ρ : ℂ} (h : ρ ∈ zetaZeros T) :
    ρ.re = 1 / 2 :=
  zeta_strip_of_GRH hG ρ h.1 h.2.1 h.2.2.1

/-- Under P0011's `GRH`, every zero in `LZeros χ T` lies on the critical line, so
`LZeros_recip_sum` applies to every `χ`. Proved. -/
theorem L_re_eq_half_of_GRH (hG : GRH) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {T : ℝ} : ∀ ρ ∈ LZeros χ T, ρ.re = 1 / 2 :=
  fun ρ h => hG q χ ρ h.1 h.2.1 h.2.2.1

/-- Vacuity: the hypotheses `T ≥ e`, `T ≥ 15`, `T ≥ 1` of the leaves hold at `T = 15`. -/
example : Real.exp 1 ≤ (15 : ℝ) ∧ (15 : ℝ) ≤ 15 ∧ (1 : ℝ) ≤ 15 := by
  refine ⟨?_, le_rfl, by norm_num⟩
  have := Real.exp_one_lt_d9
  linarith

/-! ### CODEX task193, concrete instances
The conditional height inputs remain named. AI wrote the Lean code. Goldbach is open. -/

example : (∫ t : ℝ in (1 : ℝ)..2, 1 / t^2) = 1/2 := by
  convert reciprocal_integral193 (a := 1) (b := 2) (by norm_num) (by norm_num) using 1 <;> norm_num

example : IntervalIntegrable (fun t : ℝ =>
    (∑ i ∈ ({1, 2} : Finset ℕ).filter (fun i : ℕ => (i : ℝ) < t), (1 : ℝ)) / t^2) volume 1 2 := by
  apply (reciprocal_sum_partial193 ({1, 2} : Finset ℕ) (fun i => (i : ℝ)) (fun _ => 1)
    one_pos (by norm_num) ?_).1
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> norm_num

example : zetaZeros (-1) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ρ hρ
  have hh := hρ.2.2.2
  linarith [abs_nonneg ρ.im]

example : ∃ hf : (zetaZeros (-1)).Finite, ∃ hp : (zetaZerosPos (-1)).Finite,
    ∀ ρ ∈ zetaZeros (-1), ρ.im ≠ 0 := by
  have hp : (zetaZerosPos (-1)).Finite := by
    apply (zetaZeros_finite (-1)).subset
    intro ρ hρ
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, by rw [abs_of_pos hρ.2.2.2.1]; exact hρ.2.2.2.2⟩
  refine ⟨zetaZeros_finite (-1), hp, ?_⟩
  intro ρ hρ hzero
  have hh := hρ.2.2.2
  rw [hzero, abs_zero] at hh
  linarith

example : Real.exp 1 ≤ (3 : ℝ) ∧ (zetaZerosPos 3).Finite := by
  refine ⟨by linarith [Real.exp_one_lt_d9], ?_⟩
  apply (zetaZeros_finite 3).subset
  intro ρ hρ
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, by rw [abs_of_pos hρ.2.2.2.1]; exact hρ.2.2.2.2⟩

example : (14 : ℝ) ≤ 14 ∧ (zetaZerosPos 14).Finite := by
  refine ⟨le_rfl, ?_⟩
  apply (zetaZeros_finite 14).subset
  intro ρ hρ
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, by rw [abs_of_pos hρ.2.2.2.1]; exact hρ.2.2.2.2⟩

example : (15 : ℝ) ≤ 15 ∧ (zetaZeros 15).Finite := ⟨le_rfl, zetaZeros_finite 15⟩

example : (1 : DirichletCharacter ℂ 1).IsPrimitive ∧ (1 : ℝ) ≤ 1 ∧
    (LZeros (1 : DirichletCharacter ℂ 1) 1).Finite :=
  ⟨DirichletCharacter.isPrimitive_one_level_one, le_rfl, LZeros_finite _ _⟩

example : LMult (DirichletCharacter.changeLevel (by decide : 1 ∣ 4)
      (1 : DirichletCharacter ℂ 1)) ((1/2 : ℂ) + I) =
    LMult (1 : DirichletCharacter ℂ 1) ((1/2 : ℂ) + I) := by
  apply (changeLevel_zero_data193 (by decide : 1 ∣ 4) (1 : DirichletCharacter ℂ 1)
    (by norm_num) ?_).2
  intro h
  have hh := congrArg Complex.re h
  norm_num at hh

example : 0 < ((1/2 : ℂ) + I).re ∧ ((1/2 : ℂ) + I).re < 1 ∧
    ((1/2 : ℂ) + I).im ≠ 0 ∧ |((1/2 : ℂ) + I).im| ≤ 4 := by norm_num

end LeanLab.DERZ1997.Decomp1529a
