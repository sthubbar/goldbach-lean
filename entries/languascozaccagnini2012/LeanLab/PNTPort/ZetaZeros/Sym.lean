module

public import LeanLab.PNTPort.ZetaZeros.Count

/-!
# All zeros of `ζ` near height `t`, with multiplicity, number `O(log |t|)`

Lab proof, unit U-5262, CLOUD 20261019T0715Z-cloud19. AI wrote this file. Known mathematics,
Davenport ch. 15, no cited input.

* `ord_one_sub`: in the strip `0 < Re ρ < 1`, `ζ` has the same order at `1 - ρ` as at `ρ`, from
  Mathlib's functional equation `ζ(1 - s) = 2 (2π)^{-s} Γ(s) cos(πs/2) ζ(s)`, whose factor is
  analytic and nonzero there.
* `zeta_ne_zero_of_re_nonpos`: `ζ s ≠ 0` for `Re s ≤ 0` and `Im s ≠ 0`.
* `zero_count`: an absolute `C` such that for `|t| ≥ 3` the zeros `ρ` of `ζ` with
  `|Im ρ - t| ≤ 2/5` form a finite set and, with multiplicity, number at most `C log |t|`;
  the classical `N(t + 2/5) - N(t - 2/5) ≪ log |t|`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ZetaZeros

open Complex Set Filter Metric Topology
open scoped Real

local notation "ζ" => riemannZeta

/-- The factor of the functional equation. -/
noncomputable def feF (s : ℂ) : ℂ := 2 * (2 * (π : ℂ)) ^ (-s) * Gamma s * cos (π * s / 2)

lemma not_neg_nat_of_re_pos {s : ℂ} (h : 0 < s.re) : ∀ n : ℕ, s ≠ -n := by
  intro n hn; rw [hn] at h; simp at h; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

lemma cos_ne_zero_of_not_odd {s : ℂ} (h : ∀ k : ℤ, s ≠ 2 * k + 1) : cos (π * s / 2) ≠ 0 := by
  intro hc
  rw [Complex.cos_eq_zero_iff] at hc
  obtain ⟨k, hk⟩ := hc
  apply h k
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : (π : ℂ) * s = (2 * k + 1) * π := by linear_combination 2 * hk
  have := mul_left_cancel₀ hπ (this.trans (mul_comm _ _))
  exact this

lemma not_odd_of_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : ∀ k : ℤ, s ≠ 2 * k + 1 := by
  intro k hk
  have hre := congr_arg Complex.re hk
  simp at hre
  rw [hre] at h0 h1
  have a : (-1 : ℝ) < k := by linarith
  have b : (k : ℝ) < 0 := by linarith
  have a' : (-1 : ℤ) < k := by exact_mod_cast a
  have b' : k < 0 := by exact_mod_cast b
  omega

lemma not_odd_of_im {s : ℂ} (h : s.im ≠ 0) : ∀ k : ℤ, s ≠ 2 * k + 1 := by
  intro k hk; apply h; rw [hk]; simp

lemma feF_ne_zero {s : ℂ} (h0 : 0 < s.re) (hodd : ∀ k : ℤ, s ≠ 2 * k + 1) : feF s ≠ 0 := by
  unfold feF
  have h2π : (2 * (π : ℂ)) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_
  · exact (cpow_ne_zero_iff).2 (Or.inl h2π)
  · exact Complex.Gamma_ne_zero (not_neg_nat_of_re_pos h0)
  · exact cos_ne_zero_of_not_odd hodd

lemma feF_differentiableAt {s : ℂ} (h0 : 0 < s.re) : DifferentiableAt ℂ feF s := by
  unfold feF
  have h2π : (2 * (π : ℂ)) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · apply DifferentiableAt.const_mul
      exact (differentiableAt_id.neg).const_cpow (Or.inl h2π)
    · exact Complex.differentiableAt_Gamma s (not_neg_nat_of_re_pos h0)
  · exact (Complex.differentiableAt_cos).comp s
      ((differentiableAt_id.const_mul _).div_const _)

/-- The open strip `0 < Re s < 1`. -/
def strip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}

lemma strip_open : IsOpen strip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma feF_analyticAt {s : ℂ} (h0 : 0 < s.re) : AnalyticAt ℂ feF s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ feF {z : ℂ | 0 < z.re} :=
    fun z hz => (feF_differentiableAt hz).differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds h0)

lemma fe_strip {s : ℂ} (hs : s ∈ strip) : ζ (1 - s) = feF s * ζ s := by
  unfold feF
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp [strip] at hs
  rw [riemannZeta_one_sub (not_neg_nat_of_re_pos hs.1) hs1]

/-- In the strip, `ζ` has the same order at `1 - ρ` as at `ρ`. -/
theorem ord_one_sub {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderNatAt ζ (1 - ρ) = analyticOrderNatAt ζ ρ := by
  have hρ : ρ ∈ strip := ⟨h0, h1⟩
  have hne1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
  have hζ : AnalyticAt ℂ ζ ρ := analyticAt_riemannZeta hne1
  -- order of `s ↦ ζ(1 - s)` at `ρ`
  have hAff : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := analyticAt_const.sub analyticAt_id
  have hcomp : analyticOrderAt (ζ ∘ fun s : ℂ => 1 - s) ρ = analyticOrderAt ζ (1 - ρ) := by
    apply analyticOrderAt_comp_of_deriv_ne_zero hAff
    have : deriv (fun s : ℂ => 1 - s) ρ = -1 := by
      have hd : HasDerivAt (fun s : ℂ => 1 - s) (-1) ρ := by
        simpa using (hasDerivAt_id ρ).const_sub (1 : ℂ)
      exact hd.deriv
    rw [this]; norm_num
  have hev : (ζ ∘ fun s : ℂ => 1 - s) =ᶠ[𝓝 ρ] (feF * ζ) := by
    filter_upwards [strip_open.mem_nhds hρ] with s hs
    simp only [Function.comp_apply, Pi.mul_apply]
    exact fe_strip hs
  have hmul : analyticOrderAt (feF * ζ) ρ = analyticOrderAt ζ ρ := by
    rw [analyticOrderAt_mul (feF_analyticAt h0) hζ, analyticOrderAt_eq_zero.mpr
      (Or.inr (feF_ne_zero h0 (not_odd_of_strip h0 h1))), zero_add]
  have : analyticOrderAt ζ (1 - ρ) = analyticOrderAt ζ ρ := by
    rw [← hcomp, analyticOrderAt_congr hev, hmul]
  simp only [analyticOrderNatAt, this]

lemma zeta_one_sub_eq_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : ζ ρ = 0) :
    ζ (1 - ρ) = 0 := by
  rw [fe_strip ⟨h0, h1⟩, hz, mul_zero]

/-- `ζ s ≠ 0` for `Re s ≤ 0` off the real axis. -/
theorem zeta_ne_zero_of_re_nonpos {s : ℂ} (hre : s.re ≤ 0) (him : s.im ≠ 0) : ζ s ≠ 0 := by
  set w := 1 - s with hw
  have hw0 : 1 ≤ w.re := by rw [hw]; simp; linarith
  have hwim : w.im ≠ 0 := by rw [hw]; simpa using him
  have hw1 : w ≠ 1 := by intro h; apply hwim; rw [h]; simp
  have e : ζ s = feF w * ζ w := by
    have := riemannZeta_one_sub (not_neg_nat_of_re_pos (by linarith : 0 < w.re)) hw1
    rw [show 1 - w = s by rw [hw]; ring] at this
    rw [this]; rfl
  rw [e]
  exact mul_ne_zero (feF_ne_zero (by linarith) (not_odd_of_im hwim))
    (riemannZeta_ne_zero_of_one_le_re hw0)

/-- All zeros of `ζ` with `|Im ρ - t| ≤ 2/5`. -/
def ZA (t : ℝ) : Set ℂ := {ρ : ℂ | ζ ρ = 0 ∧ |ρ.im - t| ≤ 2 / 5}

/-- The left half: zeros with `Re ρ < 1/2`. -/
def ZL (t : ℝ) : Set ℂ := {ρ : ℂ | ζ ρ = 0 ∧ ρ.re < 1 / 2 ∧ |ρ.im - t| ≤ 2 / 5}

lemma ZA_eq {t : ℝ} : ZA t = ZW t ∪ ZL t := by
  ext ρ
  simp only [ZA, ZW, ZL, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, hi⟩
    rcases le_or_gt (1 / 2) ρ.re with h | h
    · exact Or.inl ⟨hz, h, hi⟩
    · exact Or.inr ⟨hz, h, hi⟩
  · rintro (⟨hz, _, hi⟩ | ⟨hz, _, hi⟩) <;> exact ⟨hz, hi⟩

lemma ZL_re_pos {t : ℝ} (ht : 3 ≤ |t|) {ρ : ℂ} (hρ : ρ ∈ ZL t) : 0 < ρ.re := by
  obtain ⟨hz, _, hi⟩ := hρ
  by_contra h; push_neg at h
  apply zeta_ne_zero_of_re_nonpos h _ hz
  intro h0; rw [h0] at hi
  cases abs_cases t <;> cases abs_cases (0 - t) <;> linarith

lemma ZL_map {t : ℝ} (ht : 3 ≤ |t|) {ρ : ℂ} (hρ : ρ ∈ ZL t) : 1 - ρ ∈ ZW (-t) := by
  have h0 := ZL_re_pos ht hρ
  obtain ⟨hz, hre, hi⟩ := hρ
  refine ⟨zeta_one_sub_eq_zero h0 (by linarith) hz, ?_, ?_⟩
  · simp; linarith
  · have : (1 - ρ).im - -t = -(ρ.im - t) := by simp; ring
    rw [this, abs_neg]; exact hi

/-- **`N(t + 2/5) - N(t - 2/5) ≪ log |t|`**, all zeros, with multiplicity. -/
theorem zero_count : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ |t| →
    ∃ hfin : (ZA t).Finite,
      (∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) ≤ C * Real.log |t| := by
  obtain ⟨C, hC, hW⟩ := zero_window_count
  refine ⟨2 * C, by positivity, fun t ht => ?_⟩
  obtain ⟨hfW, hsW⟩ := hW t ht
  have ht' : 3 ≤ |-t| := by rwa [abs_neg]
  obtain ⟨hfW', hsW'⟩ := hW (-t) ht'
  rw [abs_neg] at hsW'
  have hfL : (ZL t).Finite := by
    apply (hfW'.image (fun z => 1 - z)).subset
    intro ρ hρ
    exact ⟨1 - ρ, ZL_map ht hρ, by ring⟩
  have hfA : (ZA t).Finite := by rw [ZA_eq]; exact hfW.union hfL
  refine ⟨hfA, ?_⟩
  have hsplit : hfA.toFinset ⊆ hfW.toFinset ∪ hfL.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset, ZA_eq] at hρ
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact hρ
  have hL : (∑ ρ ∈ hfL.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) ≤ C * Real.log |t| := by
    have hinj : Set.InjOn (fun z : ℂ => 1 - z) (hfL.toFinset : Set ℂ) := by
      intro a _ b _ hab; simpa using hab
    have hsub : hfL.toFinset.image (fun z : ℂ => 1 - z) ⊆ hfW'.toFinset := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨ρ, hρ, rfl⟩ := hz
      rw [Set.Finite.mem_toFinset] at hρ ⊢
      exact ZL_map ht hρ
    have heq : (∑ ρ ∈ hfL.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) =
        ∑ z ∈ hfL.toFinset.image (fun z : ℂ => 1 - z), (analyticOrderNatAt ζ z : ℝ) := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ
      have h0 := ZL_re_pos ht hρ
      rw [ord_one_sub h0 (by linarith [hρ.2.1])]
    rw [heq]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans hsW'
  calc (∑ ρ ∈ hfA.toFinset, (analyticOrderNatAt ζ ρ : ℝ))
      ≤ ∑ ρ ∈ hfW.toFinset ∪ hfL.toFinset, (analyticOrderNatAt ζ ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsplit (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ (∑ ρ ∈ hfW.toFinset, (analyticOrderNatAt ζ ρ : ℝ)) +
        ∑ ρ ∈ hfL.toFinset, (analyticOrderNatAt ζ ρ : ℝ) := by
        have hu := Finset.sum_union_inter (s₁ := hfW.toFinset) (s₂ := hfL.toFinset)
          (f := fun ρ => (analyticOrderNatAt ζ ρ : ℝ))
        have hi : 0 ≤ ∑ ρ ∈ hfW.toFinset ∩ hfL.toFinset, (analyticOrderNatAt ζ ρ : ℝ) :=
          Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
        linarith
    _ ≤ C * Real.log |t| + C * Real.log |t| := add_le_add hsW hL
    _ = 2 * C * Real.log |t| := by ring

end LeanLab.PNTPort.ZetaZeros

