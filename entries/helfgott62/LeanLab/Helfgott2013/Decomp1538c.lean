module

public import Mathlib
public import LeanLab.Helfgott2013.Decomp1538b

/-!
# Proposition 6.2 of Helfgott's ternary Goldbach paper, for the arcs of display 3.5

H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2, Proposition 6.2 on
page 47 for the major arcs `M_{δ0,r}` of display 3.5 on page 10, with `R/Z` modelled as `[0, 1)`
and `S1` a trigonometric polynomial `S1(α) = ∑_{n ∈ A} c_n e(αn)`, `A` finite. The paper allows
any `{a_n}` in `L¹`; the finite case is a special case.

Lab unit U-1538: Claude, Anthropic, an AI agent, wrote the statements and the skeleton of this
file. Later AI prover agents of the lab closed the leaves, as listed in PORTING.md. Checked only
by the Lean kernel; no human expert has reviewed it. Binary Goldbach is open. This file does not
formalize the ternary Goldbach theorem.
-/

@[expose] public section

namespace LeanLab.Helfgott2013.U1538

open Finset MeasureTheory intervalIntegral

/-- `e(t) = exp(2πit)`, p. 8, Section 2.1. -/
noncomputable def eC (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- The trigonometric polynomial `S1(α) = ∑_{n ∈ A} c_n e(αn)`, p. 47, Prop. 6.2 with finitely
many nonzero `a_n`. -/
noncomputable def trig (A : Finset ℤ) (c : ℤ → ℂ) (α : ℝ) : ℂ := ∑ n ∈ A, c n * eC (α * n)

/-- The major arcs `M_{δ0,r}` of display 3.5, p. 10, as a subset of `ℝ`, periodic mod `1`, closing the open
arcs of the paper: the closed arcs `[a/q - δ0 r/(2qx), a/q + δ0 r/(2qx)]` for odd `q ≤ r`, and
`[a/q - δ0 r/(qx), a/q + δ0 r/(qx)]` for even `q ≤ 2r`, with `(a, q) = 1`. -/
def majorArcs (δ0 x r : ℝ) : Set ℝ :=
  {α | ∃ q : ℕ, ∃ a : ℤ, 0 < q ∧ Int.gcd a q = 1 ∧
    ((Odd q ∧ (q : ℝ) ≤ r ∧ |α - a / q| ≤ δ0 * r / (2 * q * x)) ∨
      (Even q ∧ (q : ℝ) ≤ 2 * r ∧ |α - a / q| ≤ δ0 * r / (q * x)))}

/-! ### Auxiliary lemmas -/

/-- For `δ0 ≥ 0` and `x > 0` the arcs `M_{δ0,r}` of display 3.5, p. 10, grow
with `r`: more moduli and wider arcs; used on p. 48 for the shells `M_{δ0,r+1} \ M_{δ0,r}`. -/
theorem majorArcs_mono {δ0 x : ℝ} (hδ : 0 ≤ δ0) (hx : 0 < x) :
    Monotone fun r : ℕ => majorArcs δ0 x r := by
  intro r1 r2 hr
  intro α hα
  dsimp [majorArcs] at *
  rcases hα with ⟨q, a, hq, hgcd, h1 | h2⟩
  · use q, a
    refine ⟨hq, hgcd, Or.inl ⟨h1.1, ?_, ?_⟩⟩
    · exact le_trans h1.2.1 (Nat.mono_cast hr)
    · apply le_trans h1.2.2
      apply div_le_div_of_nonneg_right
      · gcongr
      · positivity
  · use q, a
    refine ⟨hq, hgcd, Or.inr ⟨h2.1, ?_, ?_⟩⟩
    · refine le_trans h2.2.1 ?_
      gcongr
    · apply le_trans h2.2.2
      apply div_le_div_of_nonneg_right
      · gcongr
      · positivity

/-- The arcs `M_{δ0,r}` of display 3.5, p. 10, form a measurable set: a countable
union of closed intervals. -/
theorem majorArcs_measurable (δ0 x r : ℝ) : MeasurableSet (majorArcs δ0 x r) := by
  have : majorArcs δ0 x r = ⋃ q : ℕ, ⋃ a : ℤ,
    {α | 0 < q ∧ Int.gcd a q = 1 ∧
    ((Odd q ∧ (q : ℝ) ≤ r ∧ |α - a / (q:ℝ)| ≤ δ0 * r / (2 * q * x)) ∨
      (Even q ∧ (q : ℝ) ≤ 2 * r ∧ |α - a / (q:ℝ)| ≤ δ0 * r / (q * x)))} := by
    ext α
    simp [majorArcs]
  rw [this]
  refine MeasurableSet.iUnion ?_
  intro q
  refine MeasurableSet.iUnion ?_
  intro a
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  refine MeasurableSet.union ?_ ?_
  · refine MeasurableSet.inter (MeasurableSet.const _) ?_
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    exact measurableSet_le (Continuous.measurable (continuous_id.sub continuous_const).norm) measurable_const
  · refine MeasurableSet.inter (MeasurableSet.const _) ?_
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    exact measurableSet_le (Continuous.measurable (continuous_id.sub continuous_const).norm) measurable_const

/-- Orthogonality: `∫_0^1 e(αk) dα = 1` if `k = 0` and `0` otherwise, for
`k ∈ ℤ`; behind the normalisation `∫_{R/Z} |S1|² = ∑ |a_n|²` used on p. 48. -/
theorem integral_eC (k : ℤ) :
    ∫ α in (0 : ℝ)..1, eC (α * k) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk
    simp [eC]
  · dsimp [eC]
    have h1 : ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (α * k : ℝ)) =
        ∫ α in (0 : ℝ)..1, Complex.exp ((2 * Real.pi * (k : ℂ) * Complex.I) * α) := by
      congr 1
      ext α
      congr 1
      push_cast
      ring
    rw [h1]
    have hz : (2 * Real.pi * (k : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have h1 : 2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I = 0 := h
      simp only [mul_eq_zero, Complex.I_ne_zero, or_false] at h1
      have h2 : (k : ℂ) = 0 := by
        rcases h1 with h1 | h1
        · rcases h1 with h1 | h1
          · norm_num at h1
          · exact False.elim (Real.pi_ne_zero (Complex.ofReal_eq_zero.mp h1))
        · exact h1
      exact hk (Int.cast_eq_zero.mp h2)
    let c := 2 * Real.pi * (k : ℂ) * Complex.I
    have H : ∀ x : ℝ, HasDerivAt (fun (x : ℝ) => c⁻¹ * Complex.exp (c * x)) (Complex.exp (c * x)) x := by
      intro x
      have hd1 : HasDerivAt (fun (y : ℂ) => Complex.exp (c * y)) (c * Complex.exp (c * x)) ↑x := by
        have H3 : HasDerivAt (fun (y : ℂ) => Complex.exp (c * y)) (Complex.exp (c * x) * c) ↑x := by
          apply HasDerivAt.comp
          · exact Complex.hasDerivAt_exp (c * x)
          · have H3' : HasDerivAt (fun (y : ℂ) => c * y) (c * 1) ↑x := HasDerivAt.const_mul c (hasDerivAt_id (↑x : ℂ))
            rw [mul_one] at H3'
            exact H3'
        have H4 : Complex.exp (c * x) * c = c * Complex.exp (c * x) := by ring
        rw [H4] at H3
        exact H3
      have hd2 := HasDerivAt.comp_ofReal hd1
      have hd3 := HasDerivAt.const_mul c⁻¹ hd2
      have H5 : c⁻¹ * (c * Complex.exp (c * ↑x)) = Complex.exp (c * ↑x) := by
        rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
      rw [H5] at hd3
      exact hd3
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun (x : ℝ) => c⁻¹ * Complex.exp (c * x)) (Complex.exp (c * x)) x := fun x _ => H x
    rw [integral_eq_sub_of_hasDerivAt hd]
    · change c⁻¹ * _ - c⁻¹ * _ = 0
      rw [← mul_sub]
      simp only [mul_eq_zero, inv_eq_zero, sub_eq_zero]
      right
      have h2 : Complex.exp (c * 1) = Complex.exp (c * 0) := by
        dsimp [c]
        simp only [mul_one, mul_zero, Complex.exp_zero]
        have h3 : 2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I = (k : ℂ) * (2 * Real.pi * Complex.I) := by ring
        rw [h3]
        exact Complex.exp_int_mul_two_pi_mul_I k
      push_cast
      exact h2
    · apply Continuous.intervalIntegrable
      apply Continuous.comp
      · exact Complex.continuous_exp
      · refine Continuous.mul continuous_const ?_
        exact continuous_algebraMap ℝ ℂ

private lemma eC_star (t : ℝ) : starRingEnd ℂ (eC t) = eC (-t) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring_nf

private lemma eC_add (s t : ℝ) : eC s * eC t = eC (s + t) := by
  simp [eC, Complex.exp_add, mul_add]

private lemma trig_mul_star (A : Finset ℤ) (c : ℤ → ℂ) (α : ℝ) :
    trig A c α * starRingEnd ℂ (trig A c α)
      = ∑ m ∈ A, ∑ n ∈ A, c m * starRingEnd ℂ (c n) * eC (α * ((m - n : ℤ) : ℝ)) := by
  simp only [trig, map_sum, map_mul, eC_star]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have step : c m * eC (α * (m : ℝ)) * (starRingEnd ℂ (c n) * eC (-(α * (n : ℝ))))
      = c m * starRingEnd ℂ (c n) * (eC (α * (m : ℝ)) * eC (-(α * (n : ℝ)))) := by ring_nf
  rw [step, eC_add]
  congr 1
  push_cast
  ring_nf

private lemma integrable_eC_mul (z : ℂ) (k : ℤ) :
    Integrable (fun α : ℝ => z * eC (α * (k : ℝ))) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hcont : Continuous fun α : ℝ => z * eC (α * (k : ℝ)) := by
    have h1 : Continuous fun α : ℝ => eC (α * (k : ℝ)) := by
      unfold eC
      fun_prop
    exact continuous_const.mul h1
  exact MeasureTheory.IntegrableOn.mono_set (Continuous.integrableOn_Icc hcont) Set.Ioc_subset_Icc_self

private lemma integral_eC_restrict (k : ℤ) :
    ∫ α, eC (α * (k : ℝ)) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
      = if k = 0 then (1 : ℂ) else 0 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_eC k

/-- Parseval for a trigonometric polynomial:
`∫_0^1 |S1(α)|² dα = ∑_{n ∈ A} |c_n|²`; p. 48, the line
`(1/∑|a_n|²) ∫_{R/Z} |S1(α)|² dα = 1`. -/
theorem parseval_trig (A : Finset ℤ) (c : ℤ → ℂ) :
    ∫ α in (0 : ℝ)..1, ‖trig A c α‖ ^ 2 = ∑ n ∈ A, ‖c n‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  have hcont : Continuous fun α : ℝ => trig A c α := by
    unfold trig
    refine continuous_finsetSum _ ?_
    intro n _
    exact Continuous.mul continuous_const (by unfold eC; fun_prop)
  have hFcont : Continuous fun α : ℝ => trig A c α * starRingEnd ℂ (trig A c α) :=
    hcont.mul hcont.star
  have hFint : Integrable (fun α : ℝ => trig A c α * starRingEnd ℂ (trig A c α)) μ :=
    MeasureTheory.IntegrableOn.mono_set (Continuous.integrableOn_Icc hFcont) Set.Ioc_subset_Icc_self
  have hpt : ∀ α : ℝ, RCLike.re (trig A c α * starRingEnd ℂ (trig A c α)) = ‖trig A c α‖ ^ 2 := by
    intro α
    rw [Complex.mul_conj', ← Complex.ofReal_pow]
    exact RCLike.ofReal_re _
  have key : ∫ α, (trig A c α * starRingEnd ℂ (trig A c α)) ∂μ
      = ∑ n ∈ A, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : ∫ α, (trig A c α * starRingEnd ℂ (trig A c α)) ∂μ
        = ∫ α, ∑ m ∈ A, ∑ n ∈ A,
            c m * starRingEnd ℂ (c n) * eC (α * ((m - n : ℤ) : ℝ)) ∂μ := by
      simp only [trig_mul_star]
    rw [h1, MeasureTheory.integral_finsetSum]
    swap
    · intro m _
      exact MeasureTheory.integrable_finsetSum A
        (fun n _ => integrable_eC_mul (c m * starRingEnd ℂ (c n)) (m - n))
    have h2 : ∀ m ∈ A, ∫ α, ∑ n ∈ A, c m * starRingEnd ℂ (c n) * eC (α * ((m - n : ℤ) : ℝ)) ∂μ
        = ∑ n ∈ A, c m * starRingEnd ℂ (c n) * (if m - n = 0 then (1 : ℂ) else 0) := by
      intro m _
      rw [MeasureTheory.integral_finsetSum]
      swap
      · intro n _
        exact integrable_eC_mul (c m * starRingEnd ℂ (c n)) (m - n)
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [MeasureTheory.integral_const_mul, integral_eC_restrict]
    rw [Finset.sum_congr rfl h2]
    have h3 : ∀ m ∈ A, ∑ n ∈ A, c m * starRingEnd ℂ (c n) * (if m - n = 0 then (1 : ℂ) else 0)
        = c m * starRingEnd ℂ (c m) := by
      intro m hm
      have h4 : ∑ n ∈ A, c m * starRingEnd ℂ (c n) * (if m - n = 0 then (1 : ℂ) else 0)
          = ∑ n ∈ A, (if m = n then c m * starRingEnd ℂ (c n) else 0) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases hmn : n = m
        · subst hmn; simp
        · have h1 : ¬ (m - n = 0) := sub_ne_zero.mpr (fun h => hmn h.symm)
          have h2 : ¬ (m = n) := fun h => hmn h.symm
          simp [h1, h2]
      rw [h4, Finset.sum_ite_eq]
      simp [hm]
    rw [Finset.sum_congr rfl h3]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.mul_conj', ← Complex.ofReal_pow]
  calc ∫ α, ‖trig A c α‖ ^ 2 ∂μ
      = ∫ α, RCLike.re (trig A c α * starRingEnd ℂ (trig A c α)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun α => (hpt α).symm)
    _ = RCLike.re (∫ α, trig A c α * starRingEnd ℂ (trig A c α) ∂μ) := integral_re hFint
    _ = RCLike.re (∑ n ∈ A, ((‖c n‖ ^ 2 : ℝ) : ℂ)) := by rw [key]
    _ = ∑ n ∈ A, ‖c n‖ ^ 2 := by
        rw [← Complex.ofReal_sum]
        exact RCLike.ofReal_re _

/-- A trigonometric polynomial is continuous; p. 47, Prop. 6.2. -/
theorem continuous_trig (A : Finset ℤ) (c : ℤ → ℂ) : Continuous (trig A c) := by
  change Continuous (fun α => ∑ n ∈ A, c n * eC (α * n))
  refine continuous_finsetSum _ ?_
  intro n _
  refine Continuous.mul continuous_const ?_
  have h_eC_fun : (fun (α : ℝ) => eC (α * n)) = fun (α : ℝ) => Complex.exp ((2 * Real.pi * Complex.I * (n : ℝ)) * (α : ℂ)) := by
    ext α; dsimp [eC]; congr 1; push_cast; ring_nf
  rw [h_eC_fun]
  exact Complex.continuous_exp.comp (continuous_const.mul (continuous_algebraMap ℝ ℂ))

/-- The integral over `[0, 1)` equals the interval integral from `0` to `1`,
the two sets differing by two points; p. 47, `R/Z` as a fundamental domain. -/
theorem setIntegral_Ico_eq (f : ℝ → ℝ) :
    ∫ α in Set.Ico (0 : ℝ) 1, f α = ∫ α in (0 : ℝ)..1, f α := by
  rw [integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply setIntegral_congr_set
  rw [ae_eq_set]
  constructor
  · have h1 : Set.Ico (0 : ℝ) 1 \ Set.Ioc (0 : ℝ) 1 ⊆ {0} := by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_Ioc] at hx
      have ⟨⟨h_le, h_lt⟩, h_n⟩ := hx
      have h_not_gt : ¬ (0 < x) := fun h => h_n ⟨h, le_of_lt h_lt⟩
      exact le_antisymm (not_lt.mp h_not_gt) h_le
    apply measure_mono_null h1
    exact measure_singleton 0
  · have h1 : Set.Ioc (0 : ℝ) 1 \ Set.Ico (0 : ℝ) 1 ⊆ {1} := by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_Ioc] at hx
      have ⟨⟨h_gt, h_le⟩, h_n⟩ := hx
      have h_not_lt : ¬ (x < 1) := fun h => h_n ⟨le_of_lt h_gt, h⟩
      exact le_antisymm h_le (not_lt.mp h_not_lt)
    apply measure_mono_null h1
    exact measure_singleton 1

/-- A continuous real function is integrable on `[0, 1)`; p. 47, the
integrands of display 6.4 and display 6.6. -/
theorem integrable_Ico_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  have h1 : Set.Ico (0 : ℝ) 1 ⊆ Set.Icc 0 1 := Set.Ico_subset_Icc_self
  apply IntegrableOn.mono_set (Continuous.integrableOn_Icc hf) h1

/-- A continuous `S2` is bounded on `[0, 1)`; p. 47, `S2 : R/Z → C`
continuous. -/
theorem bounded_Ico_of_continuous {S2 : ℝ → ℂ} (hS2 : Continuous S2) :
    ∃ C : ℝ, ∀ α ∈ Set.Ico (0 : ℝ) 1, ‖S2 α‖ ≤ C := by
  have hs : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr (by norm_num)
  have hc : ContinuousOn (fun x => ‖S2 x‖) (Set.Icc (0 : ℝ) 1) := (Continuous.norm hS2).continuousOn
  rcases hs.exists_isMaxOn hne hc with ⟨x, _, hmax⟩
  use ‖S2 x‖
  intro α hα
  exact hmax (Set.Ico_subset_Icc_self hα)

/-! ### Main statements -/

/-- Proposition 6.2, p. 47, for the
arcs of display 3.5 and `S1 = ∑_{n ∈ A} c_n e(αn)` with `N = ∑ |c_n|² > 0`. If `H` is non-decreasing
with density `H'` on `[r0, r1]`, `H(r1) = 1`, display 6.4 `(1/N) ∫_{M_{δ0,r+1}} |S1|² ≤ H(r)` and
display 6.5 `|S2(α)| ≤ g(r)` off `M_{δ0,r}` for integers `r0 ≤ r ≤ r1`, with `g ≥ 0` non-increasing,
then display 6.6:
`(1/N) ∫_{[0,1) \ M_{δ0,r0}} |S1|² |S2| ≤ g(r0) (H(r0) - I0) + ∫_{r0}^{r1} g(r) H'(r) dr`,
with `I0 = (1/N) ∫_{M_{δ0,r0}} |S1|²` as in display 6.7. -/
theorem prop62_arcs (A : Finset ℤ) (c : ℤ → ℂ) (hN : 0 < ∑ n ∈ A, ‖c n‖ ^ 2)
    {S2 : ℝ → ℂ} (hS2 : Continuous S2) {δ0 x : ℝ} (hδ : 0 ≤ δ0) (hx : 0 < x) {r0 r1 : ℕ}
    (hr : r0 ≤ r1) {H H' g : ℝ → ℝ} (hH : NondecFTC H H' r0 r1) (hH1 : H r1 = 1)
    (h64 : ∀ r : ℕ, r0 ≤ r → r ≤ r1 →
      (∫ α in majorArcs δ0 x (r + 1 : ℕ) ∩ Set.Ico 0 1, ‖trig A c α‖ ^ 2) /
        ∑ n ∈ A, ‖c n‖ ^ 2 ≤ H r)
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) r1, 0 ≤ g u) (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) r1))
    (h65 : ∀ r : ℕ, r0 ≤ r → r ≤ r1 → ∀ α ∈ Set.Ico (0 : ℝ) 1, α ∉ majorArcs δ0 x r →
      ‖S2 α‖ ≤ g r) :
    (∫ α in (majorArcs δ0 x r0)ᶜ ∩ Set.Ico 0 1, ‖trig A c α‖ ^ 2 * ‖S2 α‖) /
        ∑ n ∈ A, ‖c n‖ ^ 2 ≤
      g r0 * (H r0 - (∫ α in majorArcs δ0 x r0 ∩ Set.Ico 0 1, ‖trig A c α‖ ^ 2) /
        ∑ n ∈ A, ‖c n‖ ^ 2) + ∫ u in (r0 : ℝ)..r1, g u * H' u := by
  set N := ∑ n ∈ A, ‖c n‖ ^ 2 with hNdef
  set μ : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 1) with hμ
  set w : ℝ → ℝ := fun α => ‖trig A c α‖ ^ 2 / N with hw
  set s : ℝ → ℝ := fun α => ‖S2 α‖ with hs
  set M : ℕ → Set ℝ := fun r => majorArcs δ0 x r with hMdef
  have hcont : Continuous fun α => ‖trig A c α‖ ^ 2 := (continuous_trig A c).norm.pow 2
  have hw0 : ∀ y, 0 ≤ w y := fun y => div_nonneg (sq_nonneg _) hN.le
  have hwi : Integrable w μ := (integrable_Ico_of_continuous hcont).div_const N
  have hw1 : ∫ y, w y ∂μ = 1 := by
    simp only [hw, hμ]
    rw [MeasureTheory.integral_div, setIntegral_Ico_eq, parseval_trig, div_self hN.ne']
  have hsm : AEStronglyMeasurable s μ := hS2.norm.aestronglyMeasurable
  have hs0 : ∀ y, 0 ≤ s y := fun y => norm_nonneg _
  obtain ⟨C, hC⟩ := bounded_Ico_of_continuous hS2
  have hsC : ∀ᵐ y ∂μ, s y ≤ C := ae_restrict_of_forall_mem measurableSet_Ico hC
  have hM : ∀ r, MeasurableSet (M r) := fun r => majorArcs_measurable δ0 x r
  have hmono : Monotone M := majorArcs_mono hδ hx
  have hset : ∀ r, ∫ y in M r, w y ∂μ =
      (∫ α in majorArcs δ0 x r ∩ Set.Ico 0 1, ‖trig A c α‖ ^ 2) / N := by
    intro r
    simp only [hμ, hw, hMdef]
    rw [Measure.restrict_restrict (majorArcs_measurable δ0 x r), MeasureTheory.integral_div]
  have h64' : ∀ r : ℕ, r0 ≤ r → r ≤ r1 → ∫ y in M (r + 1), w y ∂μ ≤ H r := by
    intro r h1 h2
    rw [hset]
    exact h64 r h1 h2
  have h65' : ∀ r : ℕ, r0 ≤ r → r ≤ r1 → ∀ᵐ y ∂μ, y ∉ M r → s y ≤ g r := fun r h1 h2 =>
    ae_restrict_of_forall_mem measurableSet_Ico fun α hα hn => h65 r h1 h2 α hα hn
  have key := prop62 hw0 hwi hw1 hsm hs0 hsC hM hmono hr hH hH1 h64' hg0 hganti h65'
  rw [hset] at key
  have hlhs : ∫ y in (M r0)ᶜ, w y * s y ∂μ =
      (∫ α in (majorArcs δ0 x r0)ᶜ ∩ Set.Ico 0 1, ‖trig A c α‖ ^ 2 * ‖S2 α‖) / N := by
    simp only [hμ, hw, hs, hMdef]
    rw [Measure.restrict_restrict (majorArcs_measurable δ0 x r0).compl, ← MeasureTheory.integral_div]
    congr 1
    funext α
    ring
  rw [hlhs] at key
  exact key

end LeanLab.Helfgott2013.U1538
