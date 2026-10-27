module

public import LeanLab.PNTPort.ExplicitPsi1.Final
public import LeanLab.PNTPort.ExplicitPsi1.LeftZeta

/-!
# The residues left of `Re s = -1/2`: the pole at `-1` and the trivial zeros

Lab proof, CLOUD 20261020T1518Z-cloud45, unit U-6551. AI wrote this file. Known mathematics,
Davenport chapter 17, no cited input. It applies the ported residue theorem
`RectangleIntegral'_eq_sumResiduesIn`, Apache-2.0, PrimeNumberTheoremAnd contributors, as
`Residues.rect_explicit` does, now on the rectangle `[-2K - 1/2, -1/2] × [-T, T]`.

With `F(s) = -ζ'/ζ(s) xˢ/(s(s + 1))`:
* `residue_F_neg_one`: the residue at `-1` is `(ζ'/ζ)(-1) x⁻¹`;
* `tendsto_logDeriv_trivial`: `(s - ρ) ζ'/ζ(s) → 1` at `ρ = -2(n + 1)`, so the trivial zeros are
  simple, read off the pole of `ψ` in the functional equation;
* `residue_F_trivial`: the residue at `ρ = -2(n + 1)` is `-x^ρ/(ρ(ρ + 1))`;
* `rect_left`: `(1/2πi) ∮ F = (ζ'/ζ)(-1) x⁻¹ - Σ_{n < K} x^{ρₙ}/(ρₙ(ρₙ + 1))` on that rectangle.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Complex Set Filter Metric Topology
open scoped Real
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.ZetaZeros

local notation "ζ" => riemannZeta

lemma zeta_neg_one_ne : ζ (-1) ≠ 0 := by
  have := riemannZeta_neg_nat_eq_bernoulli' 1
  rw [show ((-(1 : ℕ) : ℂ)) = -1 by push_cast; ring] at this
  rw [this]; norm_num [bernoulli'_two]

/-- `-ζ'/ζ(s) xˢ/s`, analytic at `-1`. -/
lemma analyticAt_H1 {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℂ (fun s => -(deriv ζ s / ζ s) * ((x : ℂ) ^ s / s)) (-1) := by
  apply (analyticAt_logDeriv (by norm_num) zeta_neg_one_ne).neg.mul
  exact (analyticAt_xpow hx _).div analyticAt_id (by norm_num)

/-- The residue of `F` at `-1` is `(ζ'/ζ)(-1) x⁻¹`. -/
lemma residue_F_neg_one {x : ℝ} (hx : 0 < x) :
    residue (F x) (-1) = (deriv ζ (-1) / ζ (-1)) * (x : ℂ) ^ (-1 : ℂ) := by
  apply residue_eq_of_tendsto
  have ht := ((analyticAt_H1 hx).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := {(-1 : ℂ)}ᶜ))
  have hv : -(deriv ζ (-1) / ζ (-1)) * ((x : ℂ) ^ (-1 : ℂ) / (-1)) =
      (deriv ζ (-1) / ζ (-1)) * (x : ℂ) ^ (-1 : ℂ) := by ring
  rw [hv] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_ne_nhds (show (-1 : ℂ) ≠ 0 by norm_num))] with s hs h0
  have hs' : s + 1 ≠ 0 := by
    intro h; apply hs; show s = -1; linear_combination h
  simp only [F]
  field_simp
  ring

/-- `F` has at most a simple pole at `-1`. -/
lemma order_F_neg_one {x : ℝ} (hx : 0 < x) : -1 ≤ meromorphicOrderAt (F x) (-1) := by
  have hH := analyticAt_H1 hx
  have hF : F x = (fun s => -(deriv ζ s / ζ s) * ((x : ℂ) ^ s / s)) *
      (fun s : ℂ => s - (-1))⁻¹ := by
    funext s
    simp only [F, Pi.mul_apply, Pi.inv_apply, sub_neg_eq_add, div_eq_mul_inv, mul_inv]
    ring
  have hinv : meromorphicOrderAt (fun s : ℂ => s - (-1))⁻¹ (-1) = -1 := by
    rw [meromorphicOrderAt_inv, meromorphicOrderAt_id_sub_const]
  rw [hF, meromorphicOrderAt_mul hH.meromorphicAt
    (show MeromorphicAt (fun s : ℂ => s - (-1))⁻¹ (-1) from
      (analyticAt_id.sub analyticAt_const).meromorphicAt.inv), hinv]
  have := hH.meromorphicOrderAt_nonneg
  calc (-1 : WithTop ℤ) = 0 + -1 := by simp
    _ ≤ _ := add_le_add_left this _

/-- `digamma` is continuous at `w` with `Re w > 0`. -/
lemma continuousAt_digamma {w : ℂ} (hw : 0 < w.re) : ContinuousAt digamma w := by
  have hA := gamma_analyticAt hw
  have := hA.deriv.continuousAt.div hA.continuousAt (gamma_ne_zero_of_re_pos hw)
  refine this.congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.div_apply, digamma_def, logDeriv_apply]

/-- **The trivial zeros are simple**: `(s - ρ) ζ'/ζ(s) → 1` at `ρ = -2(n + 1)`. -/
theorem tendsto_logDeriv_trivial (n : ℕ) :
    Tendsto (fun s => (s - (-2 * ((n : ℂ) + 1))) * (deriv ζ s / ζ s))
      (𝓝[≠] (-2 * ((n : ℂ) + 1))) (𝓝 1) := by
  set ρ : ℂ := -2 * ((n : ℂ) + 1) with hρ
  set N : ℕ := 2 * n + 3 with hN
  set j0 : ℕ := 2 * n + 2 with hj0
  have hj0N : j0 ∈ Finset.range N := by simp [hN, hj0]
  have hρj0 : ∀ s : ℂ, s + (j0 : ℂ) = s - ρ := by intro s; rw [hρ, hj0]; push_cast; ring
  set G : ℂ → ℂ := fun s => -(deriv ζ (1 - s) / ζ (1 - s)) + Complex.log (2 * π) -
      digamma (s + N) + π / 2 * Complex.tan (π * s / 2) +
      ∑ j ∈ (Finset.range N).erase j0, (s + j)⁻¹ with hG
  -- `G` is continuous at `ρ`
  have hGc : ContinuousAt G ρ := by
    have h1ρ : (1 : ℂ) - ρ = ((2 * n + 3 : ℝ) : ℂ) := by rw [hρ]; push_cast; ring
    have hA : AnalyticAt ℂ ζ (1 - ρ) := analyticAt_riemannZeta (by
      rw [h1ρ]; intro h; have := congr_arg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n])
    have hζ1 : ζ (1 - ρ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by
      rw [h1ρ]; simp; linarith [Nat.cast_nonneg (α := ℝ) n])
    have hc : ContinuousAt (fun s : ℂ => 1 - s) ρ := by fun_prop
    have hL : ContinuousAt (fun s => deriv ζ (1 - s) / ζ (1 - s)) ρ :=
      (ContinuousAt.comp (g := deriv ζ) hA.deriv.continuousAt hc).div
        (ContinuousAt.comp (g := ζ) hA.continuousAt hc) hζ1
    have hρN : ρ + N = 1 := by rw [hρ, hN]; push_cast; ring
    have hψ : ContinuousAt (fun s => digamma (s + N)) ρ :=
      ContinuousAt.comp (g := digamma) (by rw [hρN]; exact continuousAt_digamma (by norm_num))
        (by fun_prop)
    have hcos : Complex.cos (π * ρ / 2) ≠ 0 := by
      rw [show (π : ℂ) * ρ / 2 = ((-(((n + 1 : ℕ) : ℝ) * π) : ℝ) : ℂ) by rw [hρ]; push_cast; ring,
        ← Complex.ofReal_cos, Complex.ofReal_ne_zero, Real.cos_neg, Real.cos_nat_mul_pi]
      exact pow_ne_zero _ (by norm_num)
    have htan : ContinuousAt (fun s : ℂ => Complex.tan (π * s / 2)) ρ :=
      ContinuousAt.comp (g := Complex.tan) (Complex.continuousAt_tan.mpr hcos) (by fun_prop)
    have hsum : ContinuousAt (fun s : ℂ => ∑ j ∈ (Finset.range N).erase j0, (s + j)⁻¹) ρ := by
      refine tendsto_finsetSum _ fun j hj => ?_
      have hne : ρ + j ≠ 0 := by
        intro h
        have hj' : j ≠ j0 := Finset.ne_of_mem_erase hj
        apply hj'
        have e : ρ + (j : ℂ) = (j : ℂ) - (j0 : ℂ) := by rw [hρ, hj0]; push_cast; ring
        rw [e, sub_eq_zero] at h
        exact_mod_cast h
      exact ((continuousAt_id.add continuousAt_const).inv₀ hne).tendsto
    exact (((hL.neg.add continuousAt_const).sub hψ).add (continuousAt_const.mul htan)).add hsum
  -- the identity `(s - ρ) ζ'/ζ(s) = (s - ρ) G(s) + 1` near `ρ`
  have hev : ∀ᶠ s in 𝓝[≠] ρ, (s - ρ) * G s + 1 = (s - ρ) * (deriv ζ s / ζ s) := by
    have hball : ball ρ (1 / 2) ∈ 𝓝 ρ := ball_mem_nhds _ (by norm_num)
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with s hs hsρ
    have hsρ' : s ≠ ρ := hsρ
    rw [mem_ball, dist_eq_norm] at hs
    have hint : ∀ m : ℤ, s ≠ m := by
      intro m hm
      apply hsρ'
      have hm2 : ‖(m : ℂ) - ρ‖ < 1 / 2 := by rw [← hm]; exact hs
      have e : ((m : ℂ) - ρ) = (((m : ℝ) + 2 * ((n : ℝ) + 1) : ℝ) : ℂ) := by rw [hρ]; push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_lt] at hm2
      have h1 : (m : ℝ) + 2 * n + 2 < 1 / 2 := by linarith
      have h2 : -(1 / 2) < (m : ℝ) + 2 * n + 2 := by linarith
      have : m = -(2 * n + 2) := by
        have a : m + 2 * n + 2 < 1 := by
          have : ((m + 2 * n + 2 : ℤ) : ℝ) < 1 := by push_cast; linarith
          exact_mod_cast this
        have b : -1 < m + 2 * n + 2 := by
          have : (-1 : ℝ) < ((m + 2 * n + 2 : ℤ) : ℝ) := by push_cast; linarith
          exact_mod_cast this
        omega
      rw [hm, this, hρ]; push_cast; ring
    have hre : s.re < 0 := by
      have hr := Complex.abs_re_le_norm (s - ρ)
      have : (s - ρ).re = s.re + 2 * ((n : ℝ) + 1) := by rw [hρ]; simp
      rw [this] at hr
      have := lt_of_le_of_lt hr hs
      rw [abs_lt] at this
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hodd : ∀ k : ℤ, 1 - s ≠ 2 * k + 1 := by
      intro k hk; exact hint (-2 * k) (by push_cast; linear_combination -hk)
    have hζs : ζ s ≠ 0 := zeta_ne_zero_of_re_neg hre hodd
    have hFE := logDeriv_riemannZeta_one_sub hint hζs
    rw [logDeriv_apply, logDeriv_apply] at hFE
    have hnm : ∀ m : ℕ, s ≠ -(m : ℂ) := by
      intro m h; exact hint (-(m : ℤ)) (by rw [h]; push_cast; ring)
    have hsh := digamma_apply_add_nat hnm N
    rw [← Finset.add_sum_erase _ _ hj0N, hρj0] at hsh
    have hne : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ'
    rw [hFE, hG]
    simp only
    have hψ : digamma s = digamma (s + N) - (s - ρ)⁻¹ -
        ∑ j ∈ (Finset.range N).erase j0, (s + j)⁻¹ := by rw [hsh]; ring
    rw [hψ]
    field_simp
    ring
  have hlim : Tendsto (fun s => (s - ρ) * G s + 1) (𝓝[≠] ρ) (𝓝 ((ρ - ρ) * G ρ + 1)) :=
    (((continuousAt_id.sub continuousAt_const).mul hGc).add continuousAt_const).tendsto.mono_left
      nhdsWithin_le_nhds
  rw [sub_self, zero_mul, zero_add] at hlim
  exact hlim.congr' hev

/-- The residue of `F` at the trivial zero `ρ = -2(n + 1)` is `-x^ρ/(ρ(ρ + 1))`. -/
lemma residue_F_trivial {x : ℝ} (hx : 0 < x) (n : ℕ) :
    residue (F x) (-2 * ((n : ℂ) + 1)) =
      -((x : ℂ) ^ (-2 * ((n : ℂ) + 1)) /
        ((-2 * ((n : ℂ) + 1)) * (-2 * ((n : ℂ) + 1) + 1))) := by
  set ρ : ℂ := -2 * ((n : ℂ) + 1) with hρ
  have h0 : ρ ≠ 0 := by
    rw [hρ]; intro h; have := congr_arg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm1 : ρ ≠ -1 := by
    rw [hρ]; intro h; have := congr_arg Complex.re h; simp at this
    have : (2 * n + 1 : ℤ) = 0 := by
      have : ((2 * n + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
      exact_mod_cast this
    omega
  apply residue_eq_of_tendsto
  have hk := ((analyticAt_kernel hx h0 hm1).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := {ρ}ᶜ))
  have := ((tendsto_logDeriv_trivial n).mul hk).neg
  rw [show -((x : ℂ) ^ ρ / (ρ * (ρ + 1))) = -(1 * ((x : ℂ) ^ ρ / (ρ * (ρ + 1)))) by ring]
  refine this.congr (fun s => ?_)
  simp only [F]; ring

/-- The horizontal integral `∫_{σ}^{-1/2} F(u + iy) du`. -/
noncomputable def HIntL (x σ y : ℝ) : ℂ := ∫ u in σ..(-1 / 2 : ℝ), F x ((u : ℂ) + y * I)

theorem rect_decomp_left (x σ T : ℝ) :
    RectangleIntegral' (F x) ⟨σ, -T⟩ ⟨-1 / 2, T⟩ =
      (1 / (2 * π)) * (VInt x (-1 / 2) T - VInt x σ T) +
        (1 / (2 * π * I)) * (HIntL x σ (-T) - HIntL x σ T) := by
  simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul, VInt, HIntL]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : I ≠ 0 := I_ne_zero
  rw [div_mul_eq_mul_div, one_mul]
  field_simp
  ring

lemma mem_rectL {σ T : ℝ} (hσ : σ ≤ -1 / 2) (hT : 0 ≤ T) {z : ℂ} :
    z ∈ Rectangle ⟨σ, -T⟩ ⟨-1 / 2, T⟩ ↔ (σ ≤ z.re ∧ z.re ≤ -1 / 2) ∧ (-T ≤ z.im ∧ z.im ≤ T) := by
  simp only [Rectangle, mem_reProdIm]
  rw [uIcc_of_le hσ, uIcc_of_le (by linarith)]
  simp

lemma border_casesL {σ T : ℝ} {z : ℂ} (hz : z ∈ RectangleBorder ⟨σ, -T⟩ ⟨-1 / 2, T⟩) :
    z.im = -T ∨ z.re = σ ∨ z.im = T ∨ z.re = -1 / 2 := by
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hz
  rcases hz with ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩) | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- **The residue sum left of `Re s = -1/2`.** For `K ≥ 1`, `T > 0`, on the rectangle
`[-2K - 1/2, -1/2] × [-T, T]`: `(1/2πi) ∮ F = (ζ'/ζ)(-1) x⁻¹ - Σ_{n < K} x^{ρₙ}/(ρₙ(ρₙ + 1))`,
`ρₙ = -2(n + 1)`. -/
theorem rect_left {x T : ℝ} (hx : 0 < x) {K : ℕ} (hK : 1 ≤ K) (hT : 0 < T) :
    RectangleIntegral' (F x) ⟨-2 * (K : ℝ) - 1 / 2, -T⟩ ⟨-1 / 2, T⟩ =
      (deriv ζ (-1) / ζ (-1)) * (x : ℂ) ^ (-1 : ℂ) -
        ∑ n ∈ Finset.range K, (x : ℂ) ^ (-2 * ((n : ℂ) + 1)) /
          ((-2 * ((n : ℂ) + 1)) * (-2 * ((n : ℂ) + 1) + 1)) := by
  classical
  set σ : ℝ := -2 * (K : ℝ) - 1 / 2 with hσ
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hσle : σ ≤ -1 / 2 := by rw [hσ]; linarith
  set R := Rectangle (⟨σ, -T⟩ : ℂ) ⟨-1 / 2, T⟩ with hRdef
  have hmem := fun z => mem_rectL (σ := σ) (T := T) hσle hT.le (z := z)
  set tz : ℕ → ℂ := fun n => -2 * ((n : ℂ) + 1) with htz
  set P : Finset ℂ := insert (-1) ((Finset.range K).image tz) with hP
  have hRre : ∀ z ∈ R, z.re ≤ -1 / 2 := fun z hz => ((hmem z).mp hz).1.2
  have hR0 : ∀ z ∈ R, z ≠ 0 := by
    intro z hz h; have := hRre z hz; rw [h] at this; norm_num at this
  have hR1 : ∀ z ∈ R, z ≠ 1 := by
    intro z hz h; have := hRre z hz; rw [h] at this; norm_num at this
  have hgood : ∀ z ∈ R, z ≠ -1 → ζ z ≠ 0 → 0 ≤ meromorphicOrderAt (F x) z :=
    fun z hz hm1 hζ => (analyticAt_F hx (hR0 z hz) hm1 (hR1 z hz) hζ).meromorphicOrderAt_nonneg
  have htz_re : ∀ n : ℕ, (tz n).re = -2 * ((n : ℝ) + 1) := by intro n; simp [htz]
  have htz_im : ∀ n : ℕ, (tz n).im = 0 := by intro n; simp [htz]
  have hPR : ∀ z ∈ P, z ∈ R := by
    intro z hz
    rw [hP, Finset.mem_insert, Finset.mem_image] at hz
    rw [hmem]
    rcases hz with rfl | ⟨n, hn, rfl⟩
    · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
    · have hn' : (n : ℝ) + 1 ≤ K := by
        have : n + 1 ≤ K := Finset.mem_range.mp hn
        exact_mod_cast this
      rw [htz_re, htz_im]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Nat.cast_nonneg (α := ℝ) n]
  have hpoles : ∀ z ∈ R, meromorphicOrderAt (F x) z < 0 → z ∈ P := by
    intro z hz hneg
    by_contra hns
    rw [hP, Finset.mem_insert, not_or] at hns
    obtain ⟨hm1, hni⟩ := hns
    have hζ : ζ z = 0 := by
      by_contra hζ; exact absurd (hgood z hz hm1 hζ) (not_le.mpr hneg)
    obtain ⟨n, hn⟩ := zero_of_re_neg (by linarith [hRre z hz]) hζ
    apply hni
    rw [Finset.mem_image]
    refine ⟨n, Finset.mem_range.mpr ?_, hn.symm⟩
    have hre := ((hmem z).mp hz).1.1
    rw [hn] at hre
    simp at hre
    have : (n : ℝ) + 1 < K + 1 := by linarith
    have : n + 1 < K + 1 := by exact_mod_cast this
    omega
  have hbR : RectangleBorder (⟨σ, -T⟩ : ℂ) ⟨-1 / 2, T⟩ ⊆ R := rectangleBorder_subset_rectangle _ _
  obtain ⟨AL, _, hline⟩ := logDeriv_line
  have hres := RectangleIntegral'_eq_sumResiduesIn (f := F x)
    (z := ⟨σ, -T⟩) (w := ⟨-1 / 2, T⟩) (by simp; linarith) (by simp; linarith)
    (fun z _ => meromorphicAt_F hx z)
    (by
      rw [Set.disjoint_left]
      intro z hz hneg
      simp only [mem_ofPred_eq] at hneg
      have hzR := hbR hz
      have hzz : z = (z.re : ℂ) + (z.im : ℂ) * I := (re_add_im z).symm
      have hm1 : z ≠ -1 := by
        intro h
        rcases border_casesL hz with h' | h' | h' | h' <;> rw [h] at h' <;> simp at h' <;> linarith
      have hζ : ζ z ≠ 0 := by
        rcases border_casesL hz with h' | h' | h' | h'
        · exact zeta_ne_zero_of_re_nonpos (by linarith [hRre z hzR]) (by rw [h']; linarith)
        · rw [hzz, h']; exact (hline K z.im).1
        · exact zeta_ne_zero_of_re_nonpos (by linarith [hRre z hzR]) (by rw [h']; linarith)
        · rw [hzz, h']; exact zeta_left_ne z.im
      exact absurd (hgood z hzR hm1 hζ) (not_le.mpr hneg))
    (by
      apply (P : Set ℂ).toFinite.subset
      intro z ⟨hz, hneg⟩
      exact hpoles z hz hneg)
    (fun z hz => by
      rcases eq_or_ne z (-1) with rfl | hm1
      · exact order_F_neg_one hx
      · exact order_F_ge hx hm1)
  rw [hres]
  have hS : R ∩ {z | meromorphicOrderAt (F x) z < 0} =
      (P : Set ℂ) ∩ {z | meromorphicOrderAt (F x) z < 0} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hz, hneg⟩; exact ⟨hpoles z hz hneg, hneg⟩
    · rintro ⟨hz, hneg⟩; exact ⟨hPR z hz, hneg⟩
  rw [sumResiduesIn_inter_eq_of_set_eq hS (fun z _ hz =>
    residue_eq_zero_of_not_pole_of_meromorphicAt (meromorphicAt_F hx z) (not_lt.mp hz))]
  rw [sumResiduesIn, Finset.tsum_subtype' P (fun z => residue (F x) z)]
  have hnot : (-1 : ℂ) ∉ (Finset.range K).image tz := by
    rw [Finset.mem_image]
    rintro ⟨n, _, hn⟩
    have := congr_arg Complex.re hn
    rw [htz_re] at this
    simp at this
    have : (2 * n + 1 : ℤ) = 0 := by
      have : ((2 * n + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
      exact_mod_cast this
    omega
  have hinj : Set.InjOn tz ((Finset.range K : Finset ℕ) : Set ℕ) := by
    intro a _ b _ h
    have := congr_arg Complex.re h
    rw [htz_re, htz_re] at this
    have : (a : ℝ) = b := by linarith
    exact_mod_cast this
  rw [hP, Finset.sum_insert hnot, Finset.sum_image hinj, residue_F_neg_one hx]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [htz]
  exact residue_F_trivial hx n

end LeanLab.PNTPort.ExplicitPsi1.Trivial
