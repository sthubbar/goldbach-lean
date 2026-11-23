module

public import Mathlib

/-!
The shared zero count of P0014 for primitive Dirichlet characters. Unit U-1623.
The single open statement is `book_zero_count`, the estimate that the book cites as display
3.95 of section 3.7.3.3 and uses on pages 431 and 432 with the error of display 16.21.
Chapter 3 of the book is NOT FOUND IN EITHER paper store, so the statement is read from its
use on those two pages, where N of T counts zeros with imaginary part from 0 to T
and only half of a zero at height exactly 0 or T.
The conjugate symmetry, the right limit and the arithmetic below are proved.
Every other count in the Helfgott and DERZ folders follows from this one statement.
This file imports only Mathlib, so that any older leaf file can import it.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- Zeros in the open strip with absolute imaginary part at most T.
This is arXiv 1305.2897v4 page 38, the set counted by N of T in display 4.26. -/
def stripZeros (χ : DirichletCharacter ℂ q) (T : ℝ) : Set ℂ :=
  {ρ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

/-- Multiplicity of a zero of L of s and chi. -/
noncomputable abbrev mult (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/-- The strip zeros up to a fixed height form a finite set. No hypothesis on chi. -/
theorem stripZeros_finite (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (stripZeros χ T).Finite := by
  have hb : ∀ z ∈ stripZeros χ T, ‖z‖ ≤ |T| + 2 := by
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

/-- The book weight on page 431, one half at height exactly 0 or T and one otherwise. -/
noncomputable def halfWeight (T γ : ℝ) : ℝ := if γ = 0 ∨ γ = T then 1 / 2 else 1

/-- The book count N of T and chi, page 431, proof of Lemma 16.9.
Zeros with imaginary part from 0 to T, with multiplicity, half at each end height. -/
noncomputable def bookCount (χ : DirichletCharacter ℂ q) (T : ℝ) : ℝ :=
  ∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im),
    halfWeight T ρ.im * (mult χ ρ : ℝ)

/-- The main term on book page 431, T over 2 pi times log of qT over 2 pi e. -/
noncomputable def bookMain (q : ℕ) (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))

/-- The error function of book page 431, display 16.21. -/
noncomputable def bookError (q : ℕ) (T : ℝ) : ℝ := 0.15 * Real.log ((q : ℝ) * T) + 3.389

/-! ### Conjugate symmetry. Proved, no input. -/

lemma conj_chi (χ : DirichletCharacter ℂ q) (a : ZMod q) : conj (χ a) = χ⁻¹ a := by
  simpa using MulChar.star_apply' χ a

/-- Conjugation reflects the L-function of chi to that of the inverse character. -/
theorem LFunction_inv_conj (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunction χ⁻¹ (conj s) = conj (DirichletCharacter.LFunction χ s) := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hg : AnalyticOnNhd ℂ (fun z ↦ conj (DirichletCharacter.LFunction χ (conj z))) {1}ᶜ := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hU
    have hz' : conj z ≠ 1 := by
      intro h; apply hz; simpa using congrArg conj h
    exact (differentiableAt_conj_conj_iff.mpr
      (DirichletCharacter.differentiableAt_LFunction χ _ (Or.inl hz'))).differentiableWithinAt
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ⁻¹) {1}ᶜ := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hU
    exact (DirichletCharacter.differentiableAt_LFunction _ _ (Or.inl hz)).differentiableWithinAt
  have hgz (z : ℂ) (hz : 1 < z.re) :
      conj (DirichletCharacter.LFunction χ (conj z)) = DirichletCharacter.LFunction χ⁻¹ z := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ (by rwa [conj_re]),
      DirichletCharacter.LFunction_eq_LSeries χ⁻¹ hz, LSeries, LSeries, conj_tsum]
    refine tsum_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
      ← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]
    congr 1
    exact conj_chi χ n
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have heq : EqOn (fun z ↦ conj (DirichletCharacter.LFunction χ (conj z)))
      (DirichletCharacter.LFunction χ⁻¹) {1}ᶜ := by
    refine hg.eqOn_of_preconnected_of_eventuallyEq hf hpc (z₀ := 2) (by simp) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact hgz z hz
  have hs' : conj s ≠ 1 := by
    intro h; apply hs; simpa using congrArg conj h
  have := heq (show conj s ∈ ({1}ᶜ : Set ℂ) from hs')
  simp only [conj_conj] at this
  exact this.symm

lemma analyticAt_conj_conj {g : ℂ → ℂ} {w : ℂ} (hg : AnalyticAt ℂ g w) :
    AnalyticAt ℂ (fun z ↦ conj (g (conj z))) (conj w) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hg ⊢
  have hc : Tendsto (fun z : ℂ ↦ conj z) (𝓝 (conj w)) (𝓝 w) := by
    have := (Complex.continuous_conj.tendsto (conj w))
    simpa using this
  filter_upwards [hc.eventually hg] with z hz
  exact differentiableAt_conj_conj_iff.mpr hz

lemma order_le_conj {g : ℂ → ℂ} {w : ℂ} (hg : AnalyticAt ℂ g w) {n : ℕ}
    (hn : (n : ℕ∞) ≤ analyticOrderAt g w) :
    (n : ℕ∞) ≤ analyticOrderAt (fun z ↦ conj (g (conj z))) (conj w) := by
  rw [natCast_le_analyticOrderAt hg] at hn
  rw [natCast_le_analyticOrderAt (analyticAt_conj_conj hg)]
  obtain ⟨h, hh, he⟩ := hn
  refine ⟨_, analyticAt_conj_conj hh, ?_⟩
  have hc : Tendsto (fun z : ℂ ↦ conj z) (𝓝 (conj w)) (𝓝 w) := by
    have := (Complex.continuous_conj.tendsto (conj w))
    simpa using this
  filter_upwards [hc.eventually he] with z hz
  rw [hz]
  simp [map_mul, map_pow, map_sub]

/-- Conjugating an analytic function preserves its analytic order. -/
theorem order_conj {g : ℂ → ℂ} {w : ℂ} (hg : AnalyticAt ℂ g w) :
    analyticOrderAt (fun z ↦ conj (g (conj z))) (conj w) = analyticOrderAt g w := by
  apply le_antisymm
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    have := order_le_conj (analyticAt_conj_conj hg) hn
    simpa using this
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    exact order_le_conj hg hn

/-- A zero of chi at rho has the same multiplicity as the zero of the inverse at conj rho. -/
theorem mult_inv_conj (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hρ : ρ ≠ 1) :
    mult χ⁻¹ (conj ρ) = mult χ ρ := by
  have hρ' : conj ρ ≠ 1 := by
    intro h; apply hρ; simpa using congrArg conj h
  have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ := by
    apply DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ))
    · intro s hs
      exact (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
    · exact isOpen_compl_singleton.mem_nhds hρ
  have he : DirichletCharacter.LFunction χ⁻¹ =ᶠ[𝓝 (conj ρ)]
      fun z ↦ conj (DirichletCharacter.LFunction χ (conj z)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hρ'] with z hz
    have hz' : conj z ≠ 1 := by
      intro h; apply hz; simpa using congrArg conj h
    simpa using LFunction_inv_conj χ hz'
  simp only [mult, analyticOrderNatAt]
  rw [analyticOrderAt_congr he, order_conj han]

lemma stripZeros_conj (χ : DirichletCharacter ℂ q) {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ stripZeros χ T) :
    conj ρ ∈ stripZeros χ⁻¹ T := by
  have h1 : ρ ≠ 1 := by intro h; have := hρ.2.2.1; simp [h] at this
  refine ⟨?_, by simpa using hρ.2.1, by simpa using hρ.2.2.1, by simpa using hρ.2.2.2⟩
  rw [LFunction_inv_conj χ h1, hρ.1, map_zero]

/-- The book count of the inverse character is the lower half count of chi. -/
theorem bookCount_inv (χ : DirichletCharacter ℂ q) (T : ℝ) :
    bookCount χ⁻¹ T = ∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => ρ.im ≤ 0),
      halfWeight T (-ρ.im) * (mult χ ρ : ℝ) := by
  unfold bookCount
  symm
  refine Finset.sum_nbij' (fun z ↦ conj z) (fun z ↦ conj z) ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ ⊢
    exact ⟨stripZeros_conj χ hρ.1, by simpa using hρ.2⟩
  · intro ρ hρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ ⊢
    have := stripZeros_conj χ⁻¹ hρ.1
    rw [inv_inv] at this
    exact ⟨this, by simpa using hρ.2⟩
  · intro ρ _; simp
  · intro ρ _; simp
  · intro ρ hρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
    have h1 : ρ ≠ 1 := by intro h; have := hρ.1.2.2.1; simp [h] at this
    have hm := mult_inv_conj χ h1
    simp [hm]

/-! ### The two sided count. Proved from the leaf. -/

lemma two_sided_split (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : 0 < T)
    (hgap : ∀ ρ ∈ stripZeros χ T, |ρ.im| ≠ T) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ)) =
      bookCount χ T + bookCount χ⁻¹ T := by
  rw [bookCount_inv]
  unfold bookCount
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hρ' := (stripZeros_finite χ T).mem_toFinset.mp hρ
  have hne := hgap ρ hρ'
  have h1 : ρ.im ≠ T := fun h => hne (by rw [h, abs_of_pos hT])
  have h2 : -ρ.im ≠ T := fun h => hne (by rw [abs_of_nonpos (by linarith [hT]), h])
  rcases lt_trichotomy ρ.im 0 with h | h | h
  · have h3 : ¬ 0 ≤ ρ.im := not_le.mpr h
    rw [ite_eq_right h3, ite_eq_left h.le, zero_add, halfWeight,
      ite_eq_right (not_or.mpr ⟨neg_ne_zero.mpr h.ne, h2⟩), one_mul]
  · have a : halfWeight T 0 = 1 / 2 := by simp [halfWeight]
    have b : halfWeight T (-0) = 1 / 2 := by simp [halfWeight]
    rw [h, ite_eq_left le_rfl, ite_eq_left le_rfl, a, b]
    ring
  · have h3 : ¬ ρ.im ≤ 0 := not_le.mpr h
    rw [ite_eq_left h.le, ite_eq_right h3, add_zero, halfWeight,
      ite_eq_right (not_or.mpr ⟨h.ne', h1⟩), one_mul]

lemma exists_gap (χ : DirichletCharacter ℂ q) (T : ℝ) :
    ∃ ε > 0, ∀ t, T < t → t < T + ε → stripZeros χ t = stripZeros χ T := by
  classical
  let A : Set ℝ := (fun ρ : ℂ ↦ |ρ.im|) '' (stripZeros χ (T + 1) ∩ {ρ | T < |ρ.im|})
  have hA : A.Finite := ((stripZeros_finite χ (T + 1)).inter_of_left _).image _
  have hT : T ∉ A := by
    rintro ⟨ρ, ⟨_, h⟩, he⟩
    have h' : T < |ρ.im| := h
    have he' : |ρ.im| = T := he
    linarith
  have hn : Aᶜ ∈ 𝓝 T := hA.isClosed.isOpen_compl.mem_nhds hT
  obtain ⟨r, hrr, hb⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨min r 1, lt_min hrr one_pos, ?_⟩
  intro t ht1 ht2
  have hrrt : t < T + r := ht2.trans_le (by linarith [min_le_left r 1])
  have h1t : t ≤ T + 1 := (ht2.trans_le (by linarith [min_le_right r 1])).le
  ext ρ
  constructor
  · intro hρ
    refine ⟨hρ.1, hρ.2.1, hρ.2.2.1, ?_⟩
    by_contra hc
    have hlt : T < |ρ.im| := not_le.mp hc
    have hmem : |ρ.im| ∈ A :=
      ⟨ρ, ⟨⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans h1t⟩, hlt⟩, rfl⟩
    have hball : |ρ.im| ∈ Metric.ball T r := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      have := hρ.2.2.2
      constructor <;> linarith
    exact hb hball hmem
  · intro hρ
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans ht1.le⟩

lemma sum_eq_of_strip_eq (χ : DirichletCharacter ℂ q) {s t : ℝ}
    (h : stripZeros χ s = stripZeros χ t) (F : ℂ → ℝ) :
    (∑ ρ ∈ (stripZeros_finite χ s).toFinset, F ρ) =
      ∑ ρ ∈ (stripZeros_finite χ t).toFinset, F ρ := by
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext ρ
  simp [h]

/-! ### The subtype sums used by the older leaves. Proved from the leaf. -/

/-- The index type of the sums over zeros in the sealed Helfgott files. -/
abbrev ZeroIdx (χ : DirichletCharacter ℂ q) (T : ℝ) : Type :=
  {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

instance zeroIdx_finite (χ : DirichletCharacter ℂ q) (T : ℝ) : Finite (ZeroIdx χ T) :=
  (stripZeros_finite χ T).to_subtype

/-- Every real family indexed by low zeros is summable, with no assumption on the zeros.
The source needs no summability hypothesis, because the index set is finite. -/
theorem summable_zeroIdx (χ : DirichletCharacter ℂ q) (T : ℝ) (F : ZeroIdx χ T → ℝ) :
    Summable F := by
  letI := Fintype.ofFinite (ZeroIdx χ T)
  exact (hasSum_fintype F).summable

/-- A sum over the index type is the finite sum over the strip zeros. -/
theorem tsum_zeroIdx (χ : DirichletCharacter ℂ q) (T : ℝ) (F : ℂ → ℝ) :
    (∑' ρ : ZeroIdx χ T, F ρ.val) = ∑ ρ ∈ (stripZeros_finite χ T).toFinset, F ρ := by
  classical
  letI := Fintype.ofFinite (ZeroIdx χ T)
  rw [tsum_fintype]
  exact (Finset.sum_subtype (p := fun ρ : ℂ => DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) _
    (fun x => (stripZeros_finite χ T).mem_toFinset) F).symm

lemma log_two_pi_e_ge : (2.8294 : ℝ) ≤ Real.log (2 * Real.pi * Real.exp 1) := by
  have hpi := Real.pi_gt_d4
  have hl2 := Real.log_two_gt_d9
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h1 : Real.log (1.0625 : ℝ) ≤ 0.0625 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.0625 by norm_num)
    linarith
  have h2 : Real.log (8 : ℝ) ≤ Real.log (2 * Real.pi) + 4 * Real.log 1.0625 := by
    have : Real.log (2 * Real.pi) + 4 * Real.log 1.0625 =
        Real.log (2 * Real.pi * 1.0625 ^ 4) := by
      have hm := Real.log_mul (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
        (show (1.0625 : ℝ) ^ 4 ≠ 0 by positivity)
      rw [hm, Real.log_pow]; norm_num
    rw [this]
    apply Real.log_le_log (by norm_num)
    nlinarith
  rw [Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
  linarith

/-- The multiplicity below height 1, and zero above. -/
noncomputable def lowTerm (χ : DirichletCharacter ℂ q) (z : ℂ) : ℝ :=
  if |z.im| ≤ 1 then (mult χ z : ℝ) else 0

/-- Instance of the hypotheses. The modulus 1 character is primitive and height 1 is allowed. -/
example : (1 : DirichletCharacter ℂ 1).IsPrimitive ∧ (1 : ℝ) ≤ 1 :=
  ⟨DirichletCharacter.isPrimitive_one_level_one, le_refl _⟩

end LeanLab.HelfgottMajor.ZeroCount1623
