module

public import LeanLab.PNTPort.Selberg.Explicit
public import LeanLab.PNTPort.Selberg.Weighted

/-!
# Selberg's mean square under RH, smoothed form

Lab proof, unit U-5920, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, Selberg 1943 in a smoothed form, CONDITIONAL ON RiemannHypothesis,
Mathlib's own definition; no other cited input.

With `ψ₁(x) = ∫₀ˣ ψ`, the lab's `psi1`, and
`D₂(λ, u) = ψ₁(e^{u+λ}) - 2ψ₁(e^u) + ψ₁(e^{u-λ}) - e^{2u}(e^{2λ} - 2 + e^{-2λ})/2`,
the multiplicative second difference minus its main term,

`selberg_smoothed`: assuming RH, there is `C` such that for `0 < λ ≤ 1` and every real `U`,
`u ↦ ‖e^{-3u/2} D₂(λ, u)‖² e^{-(u-U)²/2}` is integrable and

  `∫ ‖e^{-3u/2} D₂(λ, u)‖² e^{-(u-U)²/2} du ≤ C (λ³ (log(1/λ) + 3)² + λ⁴ e^{-U} + e^{-2U})`.

In the variable `x = e^u` near `X = e^U` with `h = λX`: `D₂` is `∫ (ψ(t) - t) K(t) dt` for a
tent `K` of width about `h` and height about `h`, so the bound says the mean square of the
`h`-smoothed short interval error of `ψ` near `X` is `≪ h log²(X/h) + h²/X² + X/h²`, which is
Selberg's `h log² X`, in the Saffari-Vaughan form `h log²(X/h)`, when `h ≥ X^{1/3}/log X`. The
`X/h²` term is the `O(x^{1/2})` remainder of the lab's ψ₁ formula. An earlier version of this file,
U-5920, had `log³`, from bounding `m(ρ)²` by `m(ρ) log |ρ|`; U-5921 removed it with the
multiplicity-weighted Schur test `Weighted.zero_mean_value_mult`.

Route: `second_difference` from `explicit_exp`; under RH `e^{u(ρ+1)} = e^{3u/2} e^{iγu}`;
`zero_mean_value_mult` on finite truncations, `key_sum_one` for the coefficients.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex Finset MeasureTheory Filter Topology
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.Gallagher

local notation "ζ" => riemannZeta

/-! ## The second difference, unconditional -/

lemma ztE_shift (v w : ℝ) (ρ : ℂ) : ztE (v + w) ρ = ztE v ρ * cexp (w * (ρ + 1)) := by
  unfold ztE
  rw [show ((v + w : ℝ) : ℂ) * (ρ + 1) = v * (ρ + 1) + w * (ρ + 1) by push_cast; ring,
    Complex.exp_add]
  ring

lemma main_identity (u l L : ℝ) :
    (Real.exp (2 * (u + l)) / 2 - Real.exp (u + l) * L) -
      2 * (Real.exp (2 * u) / 2 - Real.exp u * L) +
      (Real.exp (2 * (u - l)) / 2 - Real.exp (u - l) * L) -
      Real.exp (2 * u) * (Real.exp (2 * l) - 2 + Real.exp (-(2 * l))) / 2
    = -(L * (Real.exp u * (Real.exp l - 2 + Real.exp (-l)))) := by
  rw [show 2 * (u + l) = 2 * u + 2 * l by ring, show 2 * (u - l) = 2 * u + -(2 * l) by ring,
    show u - l = u + -l by ring, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
  ring

/-- The remainder of the explicit formula for `ψ₁(e^v)`. -/
noncomputable def Rem (v : ℝ) : ℂ :=
  psi1 (Real.exp v) - (((Real.exp (2 * v) / 2 - Real.exp v * Real.log (2 * Real.pi) : ℝ) : ℂ) -
    ∑' ρ : NZs, ztE v ρ.1)

/-- The second difference is exactly the second difference of the remainder. -/
lemma second_difference_eq (l u : ℝ) :
    D2 l u + ((Real.log (2 * Real.pi) * (Real.exp u * (Real.exp l - 2 + Real.exp (-l))) : ℝ) : ℂ)
      + ∑' ρ : NZs, ztE u ρ.1 * Ez (l * (ρ.1 + 1)) = Rem (u + l) - 2 * Rem u + Rem (u - l) := by
  set L := Real.log (2 * Real.pi)
  set M : ℝ → ℝ := fun v => Real.exp (2 * v) / 2 - Real.exp v * L with hM
  set Z : ℝ → ℂ := fun v => ∑' ρ : NZs, ztE v ρ.1 with hZ
  set R : ℝ → ℂ := Rem with hR
  have hpsi : ∀ v, psi1 (Real.exp v) = (M v : ℂ) - Z v + R v := fun v => by
    simp only [hR, Rem, hM, hZ]; ring
  -- the zero sums combine
  have hZc : Z (u + l) - 2 * Z u + Z (u - l) = ∑' ρ : NZs, ztE u ρ.1 * Ez (l * (ρ.1 + 1)) := by
    have h1 : Z (u + l) = ∑' ρ : NZs, ztE u ρ.1 * cexp (l * (ρ.1 + 1)) := by
      simp only [hZ]; congr 1; ext ρ; exact ztE_shift u l ρ.1
    have h2 : Z (u - l) = ∑' ρ : NZs, ztE u ρ.1 * cexp (-(l * (ρ.1 + 1))) := by
      simp only [hZ]; congr 1; ext ρ
      rw [show u - l = u + -l by ring, ztE_shift]; push_cast; ring_nf
    have s1 : Summable (fun ρ : NZs => ztE u ρ.1 * cexp (l * (ρ.1 + 1))) := by
      have := summable_ztE (u + l); simp_rw [ztE_shift] at this; exact this
    have s2 : Summable (fun ρ : NZs => ztE u ρ.1 * cexp (-(l * (ρ.1 + 1)))) := by
      have := summable_ztE (u + -l); simp_rw [ztE_shift] at this
      convert this using 2; push_cast; ring_nf
    have s0 := summable_ztE u
    rw [h1, h2, hZ]
    simp only
    rw [← tsum_mul_left, ← s1.tsum_sub (s0.mul_left 2), ← (s1.sub (s0.mul_left 2)).tsum_add s2]
    congr 1; ext ρ; unfold Ez; ring
  have hD : D2 l u + ((L * (Real.exp u * (Real.exp l - 2 + Real.exp (-l))) : ℝ) : ℂ)
      + ∑' ρ : NZs, ztE u ρ.1 * Ez (l * (ρ.1 + 1)) = R (u + l) - 2 * R u + R (u - l) := by
    unfold D2
    rw [hpsi, hpsi, hpsi, ← hZc]
    have hm := main_identity u l L
    have hm' : ((M (u + l) : ℝ) : ℂ) - 2 * (M u : ℂ) + (M (u - l) : ℂ) -
        ((Real.exp (2 * u) * (Real.exp (2 * l) - 2 + Real.exp (-(2 * l))) / 2 : ℝ) : ℂ)
        = -(((L * (Real.exp u * (Real.exp l - 2 + Real.exp (-l))) : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_neg, ← hm]; simp only [hM]; push_cast; ring
    linear_combination hm'
  exact hD

/-- **The second difference.** For `0 ≤ λ ≤ 1` and every `u`,
`‖D₂(λ, u) + log 2π · e^u (e^λ - 2 + e^{-λ}) + Σ_ρ ztE u ρ · E(λ(ρ+1))‖ ≤ 5 K e^{u/2}`. -/
theorem second_difference : ∃ K : ℝ, 0 ≤ K ∧ ∀ l u : ℝ, 0 ≤ l → l ≤ 1 →
    ‖D2 l u + ((Real.log (2 * Real.pi) * (Real.exp u * (Real.exp l - 2 + Real.exp (-l))) : ℝ) : ℂ)
      + ∑' ρ : NZs, ztE u ρ.1 * Ez (l * (ρ.1 + 1))‖ ≤ 5 * K * Real.exp (u / 2) := by
  obtain ⟨K, hK0, hK⟩ := explicit_exp
  refine ⟨K, hK0, fun l u hl0 hl1 => ?_⟩
  set L := Real.log (2 * Real.pi)
  set M : ℝ → ℝ := fun v => Real.exp (2 * v) / 2 - Real.exp v * L with hM
  set Z : ℝ → ℂ := fun v => ∑' ρ : NZs, ztE v ρ.1 with hZ
  set R : ℝ → ℂ := fun v => psi1 (Real.exp v) - ((M v : ℝ) - Z v) with hR
  have hpsi : ∀ v, psi1 (Real.exp v) = (M v : ℂ) - Z v + R v := fun v => by simp only [hR]; ring
  have hRb : ∀ v, ‖R v‖ ≤ K * Real.exp (v / 2) := fun v => hK v
  -- the zero sums combine
  have hZc : Z (u + l) - 2 * Z u + Z (u - l) = ∑' ρ : NZs, ztE u ρ.1 * Ez (l * (ρ.1 + 1)) := by
    have h1 : Z (u + l) = ∑' ρ : NZs, ztE u ρ.1 * cexp (l * (ρ.1 + 1)) := by
      simp only [hZ]; congr 1; ext ρ; exact ztE_shift u l ρ.1
    have h2 : Z (u - l) = ∑' ρ : NZs, ztE u ρ.1 * cexp (-(l * (ρ.1 + 1))) := by
      simp only [hZ]; congr 1; ext ρ
      rw [show u - l = u + -l by ring, ztE_shift]; push_cast; ring_nf
    have s1 : Summable (fun ρ : NZs => ztE u ρ.1 * cexp (l * (ρ.1 + 1))) := by
      have := summable_ztE (u + l); simp_rw [ztE_shift] at this; exact this
    have s2 : Summable (fun ρ : NZs => ztE u ρ.1 * cexp (-(l * (ρ.1 + 1)))) := by
      have := summable_ztE (u + -l); simp_rw [ztE_shift] at this
      convert this using 2; push_cast; ring_nf
    have s0 := summable_ztE u
    rw [h1, h2, hZ]
    simp only
    rw [← tsum_mul_left, ← s1.tsum_sub (s0.mul_left 2), ← (s1.sub (s0.mul_left 2)).tsum_add s2]
    congr 1; ext ρ; unfold Ez; ring
  have hD : D2 l u + ((L * (Real.exp u * (Real.exp l - 2 + Real.exp (-l))) : ℝ) : ℂ)
      + ∑' ρ : NZs, ztE u ρ.1 * Ez (l * (ρ.1 + 1)) = R (u + l) - 2 * R u + R (u - l) := by
    unfold D2
    rw [hpsi, hpsi, hpsi, ← hZc]
    have hm := main_identity u l L
    have hm' : ((M (u + l) : ℝ) : ℂ) - 2 * (M u : ℂ) + (M (u - l) : ℂ) -
        ((Real.exp (2 * u) * (Real.exp (2 * l) - 2 + Real.exp (-(2 * l))) / 2 : ℝ) : ℂ)
        = -(((L * (Real.exp u * (Real.exp l - 2 + Real.exp (-l))) : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_neg, ← hm]; simp only [hM]; push_cast; ring
    linear_combination hm'
  rw [hD]
  have e1 : Real.exp ((u + l) / 2) ≤ Real.exp (1 / 2) * Real.exp (u / 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp ((u - l) / 2) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by linarith)
  have eh : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hu := Real.exp_pos (u / 2)
  calc ‖R (u + l) - 2 * R u + R (u - l)‖
      ≤ ‖R (u + l)‖ + 2 * ‖R u‖ + ‖R (u - l)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_ofNat]
    _ ≤ K * Real.exp ((u + l) / 2) + 2 * (K * Real.exp (u / 2)) + K * Real.exp ((u - l) / 2) := by
        gcongr <;> exact hRb _
    _ ≤ K * (2 * Real.exp (u / 2)) + 2 * (K * Real.exp (u / 2)) + K * Real.exp (u / 2) := by
        gcongr; nlinarith
    _ = 5 * K * Real.exp (u / 2) := by ring

/-! ## Under RH: the zero sum -/

/-- The coefficient `m(ρ) E(λ(ρ+1))/(ρ(ρ+1))`. -/
noncomputable def cf (l : ℝ) (ρ : ℂ) : ℂ :=
  (analyticOrderNatAt ζ ρ : ℂ) * (Ez (l * (ρ + 1)) / (ρ * (ρ + 1)))

/-- The normalised zero sum `Σ_ρ cf λ ρ e^{iγu}`. -/
noncomputable def fz (l u : ℝ) : ℂ := ∑' ρ : NZs, cf l ρ.1 * cexp (ρ.1.im * u * I)

lemma re_half (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : NZ ρ) : ρ.re = 1 / 2 := by
  apply hRH ρ hρ.1
  · rintro ⟨n, hn⟩
    have h := hρ.2.1
    rw [hn] at h
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h; have := hρ.2.2; rw [h, one_re] at this; exact lt_irrefl _ this

lemma NZ_of_NZs (ρ : NZs) : NZ ρ.1 := ρ.2

lemma ztE_RH (hRH : RiemannHypothesis) (l u : ℝ) {ρ : ℂ} (hρ : NZ ρ) :
    ztE u ρ * Ez (l * (ρ + 1)) =
      (Real.exp (3 / 2 * u) : ℂ) * (cf l ρ * cexp (ρ.im * u * I)) := by
  unfold ztE cf
  have hr := re_half hRH hρ
  have key : (u : ℂ) * (ρ + 1) = ((3 / 2 * u : ℝ) : ℂ) + ρ.im * u * I := by
    apply Complex.ext <;> simp [hr] <;> ring
  rw [key, Complex.exp_add, ← Complex.ofReal_exp]
  ring

lemma norm_cexp_im (γ u : ℝ) : ‖cexp (γ * u * I)‖ = 1 := by
  rw [show (γ : ℂ) * u * I = ((γ * u : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_le_norm_add_one {ρ : ℂ} (h : 0 ≤ ρ.re) : ‖ρ‖ ≤ ‖ρ + 1‖ := by
  have h2 : ‖ρ‖ ^ 2 ≤ ‖ρ + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, one_re, add_im, one_im, add_zero]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h2

/-- **Coefficient bound** under RH: `‖cf λ ρ‖ ≤ 36 m(ρ) min(λ², ‖ρ‖⁻²)`. -/
lemma cf_bound (hRH : RiemannHypothesis) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {ρ : ℂ}
    (hρ : NZ ρ) : ‖cf l ρ‖ ≤ 36 * mz ρ * min (l ^ 2) (‖ρ‖⁻¹ ^ 2) := by
  have hr := re_half hRH hρ
  have hn : 1 / 2 ≤ ‖ρ‖ := by rw [← hr]; exact (le_abs_self _).trans (abs_re_le_norm ρ)
  have hp : 0 < ‖ρ‖ := by linarith
  have h1 : ‖ρ‖ ≤ ‖ρ + 1‖ := norm_le_norm_add_one (by rw [hr]; norm_num)
  have h3 : ‖ρ + 1‖ ≤ 3 * ‖ρ‖ := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have hz : |(l * (ρ + 1) : ℂ).re| ≤ 3 / 2 := by
    have : ((l : ℂ) * (ρ + 1)).re = l * (3 / 2) := by
      simp only [mul_re, ofReal_re, ofReal_im, add_re, one_re, add_im, one_im, zero_mul, sub_zero, hr]
      ring
    rw [this, abs_of_nonneg (by positivity)]; linarith
  have hE := norm_E_le _ hz
  have hzn : ‖(l : ℂ) * (ρ + 1)‖ = l * ‖ρ + 1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0]
  rw [hzn] at hE
  have hm := mz_nonneg ρ
  have hcf : ‖cf l ρ‖ = mz ρ * ‖Ez (l * (ρ + 1))‖ / (‖ρ‖ * ‖ρ + 1‖) := by
    unfold cf mz Ez
    rw [norm_mul, norm_div, norm_mul, Complex.norm_natCast]; ring
  have hq : 0 < ‖ρ‖ * ‖ρ + 1‖ := mul_pos hp (lt_of_lt_of_le hp h1)
  rw [mul_min_of_nonneg _ _ (by positivity)]
  apply le_min
  · rw [hcf, div_le_iff₀ hq]
    have : ‖Ez (l * (ρ + 1))‖ ≤ 12 * (l * ‖ρ + 1‖) ^ 2 :=
      hE.trans (by gcongr; exact min_le_left _ _)
    have : mz ρ * ‖Ez (l * (ρ + 1))‖ ≤ mz ρ * (12 * (l * ‖ρ + 1‖) ^ 2) :=
      mul_le_mul_of_nonneg_left this hm
    have : mz ρ * (12 * (l * ‖ρ + 1‖) ^ 2) ≤ 36 * mz ρ * l ^ 2 * (‖ρ‖ * ‖ρ + 1‖) := by
      have e : mz ρ * (12 * (l * ‖ρ + 1‖) ^ 2) = 12 * mz ρ * l ^ 2 * ‖ρ + 1‖ * ‖ρ + 1‖ := by ring
      rw [e]
      have : 12 * mz ρ * l ^ 2 * ‖ρ + 1‖ * ‖ρ + 1‖ ≤ 12 * mz ρ * l ^ 2 * ‖ρ + 1‖ * (3 * ‖ρ‖) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith
    linarith
  · rw [hcf, div_le_iff₀ hq]
    have : ‖Ez (l * (ρ + 1))‖ ≤ 12 := hE.trans (by
      have := min_le_right ((l * ‖ρ + 1‖) ^ 2) 1; linarith)
    have : mz ρ * ‖Ez (l * (ρ + 1))‖ ≤ mz ρ * 12 := mul_le_mul_of_nonneg_left this hm
    have e : 36 * mz ρ * ‖ρ‖⁻¹ ^ 2 * (‖ρ‖ * ‖ρ + 1‖) = 36 * mz ρ * (‖ρ + 1‖ / ‖ρ‖) := by
      field_simp
    rw [e]
    have : 1 ≤ ‖ρ + 1‖ / ‖ρ‖ := by rw [le_div_iff₀ hp]; linarith
    nlinarith

/-- The coefficient without its multiplicity, `E(λ(ρ+1))/(ρ(ρ+1))`. -/
noncomputable def cq (l : ℝ) (ρ : ℂ) : ℂ := Ez (l * (ρ + 1)) / (ρ * (ρ + 1))

/-- Under RH, `‖cq λ ρ‖ ≤ 36 min(λ², ‖ρ‖⁻²)`. -/
lemma cq_bound (hRH : RiemannHypothesis) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {ρ : ℂ}
    (hρ : NZ ρ) : ‖cq l ρ‖ ≤ 36 * min (l ^ 2) (‖ρ‖⁻¹ ^ 2) := by
  have h := cf_bound hRH hl0 hl1 hρ
  have hk1 : ρ ≠ 1 := by
    intro e; have := hρ.2.2; rw [e, one_re] at this; exact lt_irrefl _ this
  have hm1 : 1 ≤ mz ρ := by unfold mz; exact_mod_cast ZetaZeros.ord_pos hρ.1 hk1
  have e : ‖cf l ρ‖ = mz ρ * ‖cq l ρ‖ := by
    unfold cf cq mz; rw [norm_mul, Complex.norm_natCast]
  rw [e] at h
  have hmin : 0 ≤ min (l ^ 2) (‖ρ‖⁻¹ ^ 2) := le_min (by positivity) (by positivity)
  by_contra hc
  push_neg at hc
  have : mz ρ * (36 * min (l ^ 2) (‖ρ‖⁻¹ ^ 2)) < mz ρ * ‖cq l ρ‖ :=
    mul_lt_mul_of_pos_left hc (by linarith)
  nlinarith

lemma summable_hw_NZs : Summable (fun ρ : NZs => hw ρ.1) := by
  have h := summable_hw
  have e : Zall = {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} := Zall_eq
  revert h; rw [e]; exact id

lemma cf_le_hw (hRH : RiemannHypothesis) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {ρ : ℂ}
    (hρ : NZ ρ) : ‖cf l ρ‖ ≤ 108 * hw ρ := by
  refine (cf_bound hRH hl0 hl1 hρ).trans ?_
  have hr := re_half hRH hρ
  have hn : 1 / 2 ≤ ‖ρ‖ := by rw [← hr]; exact (le_abs_self _).trans (abs_re_le_norm ρ)
  have hp : 0 < ‖ρ‖ := by linarith
  have h3 : ‖ρ + 1‖ ≤ 3 * ‖ρ‖ := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have h1 : 0 < ‖ρ + 1‖ := lt_of_lt_of_le hp (norm_le_norm_add_one (by rw [hr]; norm_num))
  have hm := mz_nonneg ρ
  unfold hw
  rw [norm_mul]
  calc 36 * mz ρ * min (l ^ 2) (‖ρ‖⁻¹ ^ 2) ≤ 36 * mz ρ * ‖ρ‖⁻¹ ^ 2 := by
        gcongr; exact min_le_right _ _
    _ ≤ 108 * ((analyticOrderNatAt ζ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)) := by
        unfold mz at hm ⊢
        rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        rw [show 108 * ((analyticOrderNatAt ζ ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)) * ‖ρ‖ ^ 2 =
          36 * (analyticOrderNatAt ζ ρ : ℝ) * (3 * ‖ρ‖ / ‖ρ + 1‖) by field_simp; ring]
        have : 1 ≤ 3 * ‖ρ‖ / ‖ρ + 1‖ := by rw [le_div_iff₀ h1]; linarith
        nlinarith

lemma summable_cf (hRH : RiemannHypothesis) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    Summable (fun ρ : NZs => ‖cf l ρ.1‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => cf_le_hw hRH hl0 hl1 ρ.2)
    (summable_hw_NZs.mul_left 108)

lemma continuous_fz (hRH : RiemannHypothesis) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    Continuous (fz l) := by
  unfold fz
  refine continuous_tsum (fun ρ => by fun_prop) (summable_cf hRH hl0 hl1) (fun ρ u => ?_)
  rw [norm_mul, norm_cexp_im, mul_one]

lemma norm_fz_le (hRH : RiemannHypothesis) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (u : ℝ) :
    ‖fz l u‖ ≤ ∑' ρ : NZs, ‖cf l ρ.1‖ := by
  unfold fz
  have hs : Summable (fun ρ : NZs => ‖cf l ρ.1 * cexp (ρ.1.im * u * I)‖) := by
    simp_rw [norm_mul, norm_cexp_im, mul_one]; exact summable_cf hRH hl0 hl1
  refine (norm_tsum_le_tsum_norm hs).trans_eq ?_
  simp_rw [norm_mul, norm_cexp_im, mul_one]

/-! ## Gaussian helpers -/

lemma gw_continuous (U : ℝ) : Continuous (gw U) := by unfold gw; fun_prop

lemma gw_nonneg (U u : ℝ) : 0 ≤ gw U u := by unfold gw; positivity

lemma gw_integrable (U : ℝ) : Integrable (gw U) := by
  have h := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).comp_sub_right U
  refine h.congr (ae_of_all _ fun u => ?_)
  simp only [gw]; congr 1; ring

lemma integral_gw (U : ℝ) : ∫ u, gw U u = ∫ u, gw 0 u := by
  have := integral_sub_right_eq_self (μ := volume) (fun u => gw 0 u) U
  rw [← this]; congr 1; ext u; simp [gw]

lemma exp_mul_gw (k U u : ℝ) :
    Real.exp (-(k * u)) * gw U u = Real.exp (-(k * U) + k ^ 2 / 2) * gw (U - k) u := by
  unfold gw; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

lemma integrable_sq_gw {h : ℝ → ℂ} (hc : Continuous h) {M : ℝ} (hM : ∀ u, ‖h u‖ ≤ M) (U : ℝ) :
    Integrable (fun u => ‖h u‖ ^ 2 * gw U u) := by
  refine ((gw_integrable U).const_mul (M ^ 2)).mono'
    ((hc.norm.pow 2).mul (gw_continuous U)).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gw_nonneg U u))]
  have := gw_nonneg U u
  gcongr
  exact hM u

/-- **The mean square of the zero sum** under RH. -/
theorem fz_mean (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, 0 < l → l ≤ 1 →
    ∀ U : ℝ, Integrable (fun u => ‖fz l u‖ ^ 2 * gw U u) ∧
      ∫ u, ‖fz l u‖ ^ 2 * gw U u ≤ C * l ^ 3 * (Real.log (1 / l) + 3) ^ 2 := by
  obtain ⟨Cmv, hCmv, hmv⟩ := zero_mean_value_mult
  obtain ⟨Ck, hCk, hkey⟩ := key_sum_one
  refine ⟨2 * (Cmv * (1296 * Ck)), by positivity, fun l hl0 hl1 U => ?_⟩
  have hint := integrable_sq_gw (continuous_fz hRH hl0.le hl1) (norm_fz_le hRH hl0.le hl1) U
  refine ⟨hint, ?_⟩
  set A := Real.log (1 / l) + 3
  set cG := ∫ u, gw U u with hcG
  have hcG0 : 0 ≤ cG := integral_nonneg (gw_nonneg U)
  set g : NZs → ℝ := fun ρ => ‖cf l ρ.1‖ with hg
  have hgs : Summable g := summable_cf hRH hl0.le hl1
  -- the bound on every finite truncation
  have hfin : ∀ s : Finset NZs,
      ∫ u : ℝ, ‖∑ ρ ∈ s, cf l ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 * gw U u
        ≤ Cmv * (1296 * Ck) * l ^ 3 * A ^ 2 := by
    intro s
    set S := s.map (Function.Embedding.subtype _)
    have hS : ∀ ρ ∈ S, NZ ρ := by
      intro ρ hρ
      obtain ⟨σ, _, rfl⟩ := Finset.mem_map.mp hρ
      exact σ.2
    have e : ∀ u : ℝ, ∑ ρ ∈ s, cf l ρ.1 * cexp (ρ.1.im * u * I)
        = ∑ ρ ∈ S, cf l ρ * cexp (ρ.im * u * I) := fun u => by
      rw [Finset.sum_map]; rfl
    simp_rw [e]
    have hcf : ∀ ρ : ℂ, cf l ρ = (mz ρ : ℂ) * cq l ρ := fun ρ => by
      unfold cf cq mz; push_cast; ring
    simp_rw [hcf]
    refine (hmv S hS (cq l) U).trans ?_
    have hb : ∀ ρ ∈ S, mz ρ * ‖cq l ρ‖ ^ 2 * Real.log (‖ρ‖ + 4)
        ≤ 1296 * (mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4)) := by
      intro ρ hρ
      have h := cq_bound hRH hl0.le hl1 (hS ρ hρ)
      have hmin : 0 ≤ min (l ^ 2) (‖ρ‖⁻¹ ^ 2) := le_min (by positivity) (by positivity)
      have hsq : ‖cq l ρ‖ ^ 2 ≤ (36 * min (l ^ 2) (‖ρ‖⁻¹ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      have hmin2 : min (l ^ 2) (‖ρ‖⁻¹ ^ 2) ^ 2 ≤ min (l ^ 4) (‖ρ‖⁻¹ ^ 4) := by
        apply le_min
        · calc _ ≤ (l ^ 2) ^ 2 := pow_le_pow_left₀ hmin (min_le_left _ _) 2
            _ = l ^ 4 := by ring
        · calc _ ≤ (‖ρ‖⁻¹ ^ 2) ^ 2 := pow_le_pow_left₀ hmin (min_le_right _ _) 2
            _ = ‖ρ‖⁻¹ ^ 4 := by ring
      have hL := one_le_log_add_four (norm_nonneg ρ)
      have hm := mz_nonneg ρ
      calc mz ρ * ‖cq l ρ‖ ^ 2 * Real.log (‖ρ‖ + 4)
          ≤ mz ρ * (36 * min (l ^ 2) (‖ρ‖⁻¹ ^ 2)) ^ 2 * Real.log (‖ρ‖ + 4) := by gcongr
        _ = 1296 * mz ρ * (min (l ^ 2) (‖ρ‖⁻¹ ^ 2) ^ 2) * Real.log (‖ρ‖ + 4) := by ring
        _ ≤ 1296 * mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4) := by gcongr
        _ = _ := by ring
    calc Cmv * ∑ ρ ∈ S, mz ρ * ‖cq l ρ‖ ^ 2 * Real.log (‖ρ‖ + 4)
        ≤ Cmv * ∑ ρ ∈ S, 1296 * (mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4)) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hb) hCmv.le
      _ = Cmv * (1296 * ∑ ρ ∈ S, mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4)) := by
          rw [← mul_sum]
      _ ≤ Cmv * (1296 * (Ck * l ^ 3 * A ^ 2)) := by gcongr; exact hkey l hl0 hl1 S hS
      _ = Cmv * (1296 * Ck) * l ^ 3 * A ^ 2 := by ring
  -- approximation
  apply le_of_forall_pos_le_add
  intro ε hε
  set δ := min 1 (ε / (2 * (cG + 1))) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : 2 * δ ^ 2 * cG ≤ ε := by
    have h1 : δ ≤ ε / (2 * (cG + 1)) := min_le_right _ _
    have h2 : δ ^ 2 ≤ δ := by nlinarith
    have h3 : 2 * δ * (cG + 1) ≤ ε := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith
    nlinarith
  obtain ⟨s, hs⟩ := ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero g)).2 δ hδ0).exists
  -- pointwise
  have hpt : ∀ u : ℝ, ‖fz l u‖ ^ 2 * gw U u ≤
      2 * (‖∑ ρ ∈ s, cf l ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 * gw U u) + 2 * δ ^ 2 * gw U u := by
    intro u
    have hsu : Summable (fun ρ : NZs => cf l ρ.1 * cexp (ρ.1.im * u * I)) := by
      refine Summable.of_norm_bounded hgs (fun ρ => ?_)
      rw [norm_mul, norm_cexp_im, mul_one]
    have hsplit := hsu.sum_add_tsum_subtype_compl s
    have htail : ‖∑' ρ : {ρ // ρ ∉ s}, cf l ρ.1.1 * cexp (ρ.1.1.im * u * I)‖ ≤ δ := by
      have hn : Summable (fun ρ : {ρ // ρ ∉ s} => ‖cf l ρ.1.1 * cexp (ρ.1.1.im * u * I)‖) := by
        simp_rw [norm_mul, norm_cexp_im, mul_one]; exact hgs.subtype _
      refine (norm_tsum_le_tsum_norm hn).trans ?_
      simp_rw [norm_mul, norm_cexp_im, mul_one]
      exact hs.le
    have : ‖fz l u‖ ≤ ‖∑ ρ ∈ s, cf l ρ.1 * cexp (ρ.1.im * u * I)‖ + δ := by
      unfold fz; rw [← hsplit]
      exact (norm_add_le _ _).trans (by linarith)
    have hgw := gw_nonneg U u
    have h2 : ‖fz l u‖ ^ 2 ≤ 2 * ‖∑ ρ ∈ s, cf l ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 + 2 * δ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith [sq_nonneg (‖∑ ρ ∈ s, cf l ρ.1 * cexp (ρ.1.im * u * I)‖ - δ)]
    nlinarith
  have hint_s : Integrable
      (fun u : ℝ => ‖∑ ρ ∈ s, cf l ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 * gw U u) :=
    integrable_sq_gw (continuous_finsetSum _ (fun ρ _ => by fun_prop))
      (M := ∑ ρ ∈ s, ‖cf l ρ.1‖)
      (fun u => (norm_sum_le _ _).trans_eq (by simp_rw [norm_mul, norm_cexp_im, mul_one])) U
  calc ∫ u, ‖fz l u‖ ^ 2 * gw U u
      ≤ ∫ u : ℝ, (2 * (‖∑ ρ ∈ s, cf l ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 * gw U u)
          + 2 * δ ^ 2 * gw U u) :=
        integral_mono hint ((hint_s.const_mul 2).add ((gw_integrable U).const_mul _)) hpt
    _ = 2 * (∫ u : ℝ, ‖∑ ρ ∈ s, cf l ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 * gw U u) + 2 * δ ^ 2 * cG := by
        rw [integral_add (hint_s.const_mul 2) ((gw_integrable U).const_mul _),
          integral_const_mul, integral_const_mul]
    _ ≤ 2 * (Cmv * (1296 * Ck) * l ^ 3 * A ^ 2) + ε := by
        have := hfin s; linarith
    _ = 2 * (Cmv * (1296 * Ck)) * l ^ 3 * A ^ 2 + ε := by ring

/-! ## Measurability of `ψ₁ ∘ exp` -/

lemma w1_eq_zero {y : ℝ} (h : 1 ≤ y) : ZetaZeros.w1 y = 0 := by
  unfold ZetaZeros.w1; exact max_eq_left (by linarith)

lemma hasSum_P (v : ℝ) :
    HasSum (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * ZetaZeros.w1 (n / Real.exp v))
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * ZetaZeros.w1 (n / Real.exp v)) := by
  refine (hasSum_sum_of_ne_finset_zero (s := Finset.range ⌈Real.exp v⌉₊) ?_).summable.hasSum
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  have : 1 ≤ (n : ℝ) / Real.exp v := by
    rw [le_div_iff₀ (Real.exp_pos v), one_mul]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [w1_eq_zero this]; simp

lemma measurable_psi1_exp : Measurable (fun v : ℝ => psi1 (Real.exp v)) := by
  unfold psi1
  refine Measurable.mul (Continuous.measurable (by fun_prop)) ?_
  refine measurable_of_tendsto_metrizable
    (f := fun N v => ∑ n ∈ Finset.range N,
      (ArithmeticFunction.vonMangoldt n : ℂ) * ZetaZeros.w1 (n / Real.exp v)) (fun N => ?_) ?_
  · refine (continuous_finsetSum _ fun n _ => ?_).measurable
    exact continuous_const.mul (Complex.continuous_ofReal.comp (ZetaZeros.w1_continuous.comp
      (continuous_const.div Real.continuous_exp fun v => (Real.exp_pos v).ne')))
  · rw [tendsto_pi_nhds]; intro v; exact (hasSum_P v).tendsto_sum_nat

lemma measurable_D2 (l : ℝ) : Measurable (D2 l) := by
  have h := measurable_psi1_exp
  have h1 : Measurable (fun u => psi1 (Real.exp (u + l))) := h.comp (measurable_id.add_const l)
  have h3 : Measurable (fun u => psi1 (Real.exp (u - l))) := h.comp (measurable_id.sub_const l)
  unfold D2
  exact ((h1.sub (h.const_mul 2)).add h3).sub (Continuous.measurable (by fun_prop))

/-! ## The theorem -/

lemma integrable_exp_gw (k U : ℝ) : Integrable (fun u => Real.exp (-(k * u)) * gw U u) := by
  simp_rw [exp_mul_gw]; exact (gw_integrable _).const_mul _

lemma integral_exp_gw (k U : ℝ) :
    ∫ u, Real.exp (-(k * u)) * gw U u = Real.exp (-(k * U) + k ^ 2 / 2) * ∫ u, gw 0 u := by
  simp_rw [exp_mul_gw]; rw [integral_const_mul, integral_gw]

/-- **The assembly**: any remainder bound `K r(λ) e^{u/2}` for the second difference gives the
mean square with the remainder term `r(λ)² e^{-2U}`. -/
theorem selberg_of_remainder (hRH : RiemannHypothesis) (rr : ℝ → ℝ)
    (hrem : ∃ K : ℝ, 0 ≤ K ∧ ∀ l u : ℝ, 0 ≤ l → l ≤ 1 →
      ‖D2 l u + ((Real.log (2 * Real.pi) * (Real.exp u * (Real.exp l - 2 + Real.exp (-l))) : ℝ) : ℂ)
        + ∑' ρ : NZs, ztE u ρ.1 * Ez (l * (ρ.1 + 1))‖ ≤ K * rr l * Real.exp (u / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, 0 < l → l ≤ 1 →
    ∀ U : ℝ, Integrable (fun u => ‖(Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u‖ ^ 2 * gw U u) ∧
      ∫ u, ‖(Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u‖ ^ 2 * gw U u
        ≤ C * (l ^ 3 * (Real.log (1 / l) + 3) ^ 2 + l ^ 4 * Real.exp (-U) +
          rr l ^ 2 * Real.exp (-(2 * U))) := by
  obtain ⟨K, hK0, hsd⟩ := hrem
  obtain ⟨Cf, hCf0, hfz⟩ := fz_mean hRH
  set L := Real.log (2 * Real.pi) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [Real.pi_gt_three])
  set c0 := ∫ u, gw 0 u with hc0def
  have hc0 : 0 ≤ c0 := integral_nonneg (gw_nonneg 0)
  refine ⟨3 * Cf + 432 * L ^ 2 * Real.exp (1 / 2) * c0 + 3 * K ^ 2 * Real.exp 2 * c0,
    by positivity, fun l hl0 hl1 U => ?_⟩
  obtain ⟨hint, hbound⟩ := hfz l hl0 hl1 U
  have hE : |Real.exp l - 2 + Real.exp (-l)| ≤ 12 * l ^ 2 := by
    have h := norm_E_le (l : ℂ) (by
      rw [Complex.ofReal_re, abs_of_nonneg hl0.le]; linarith)
    have e : ((Real.exp l - 2 + Real.exp (-l) : ℝ) : ℂ) = cexp l - 2 + cexp (-(l : ℂ)) := by
      push_cast [Complex.ofReal_exp]; ring
    rw [← Real.norm_eq_abs, ← Complex.norm_real, e]
    refine h.trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0.le]
    have := min_le_left (l ^ 2) 1
    linarith
  -- the pointwise bound
  have hpt : ∀ u : ℝ, ‖(Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u‖ ≤
      ‖fz l u‖ + 12 * L * l ^ 2 * Real.exp (-(1 / 2 * u)) + (K * rr l) * Real.exp (-(1 * u)) := by
    intro u
    have hW := hsd l u hl0.le hl1
    have hsum : ∑' ρ : NZs, ztE u ρ.1 * Ez (l * (ρ.1 + 1)) =
        (Real.exp (3 / 2 * u) : ℂ) * fz l u := by
      unfold fz; rw [← tsum_mul_left]; congr 1; ext ρ; exact ztE_RH hRH l u ρ.2
    rw [hsum] at hW
    set Lt : ℂ := ((L * (Real.exp u * (Real.exp l - 2 + Real.exp (-l))) : ℝ) : ℂ) with hLt
    set W := D2 l u + Lt + (Real.exp (3 / 2 * u) : ℂ) * fz l u with hWdef
    set e := (Real.exp (-(3 / 2 * u)) : ℂ) with he
    have h1 : e * (Real.exp (3 / 2 * u) : ℂ) = 1 := by
      rw [he, ← Complex.ofReal_mul, ← Real.exp_add]; simp
    have hx : e * D2 l u = e * W - e * Lt - fz l u := by
      rw [hWdef]; linear_combination (-(fz l u)) * h1
    have hen : ‖e‖ = Real.exp (-(3 / 2 * u)) := by
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hA : ‖e * W‖ ≤ (K * rr l) * Real.exp (-(1 * u)) := by
      rw [norm_mul, hen]
      calc Real.exp (-(3 / 2 * u)) * ‖W‖ ≤ Real.exp (-(3 / 2 * u)) * ((K * rr l) * Real.exp (u / 2)) := by
            gcongr
        _ = (K * rr l) * (Real.exp (-(3 / 2 * u)) * Real.exp (u / 2)) := by ring
        _ = (K * rr l) * Real.exp (-(1 * u)) := by rw [← Real.exp_add]; ring_nf
    have hB : ‖e * Lt‖ ≤ 12 * L * l ^ 2 * Real.exp (-(1 / 2 * u)) := by
      rw [norm_mul, hen, hLt, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hL0, abs_of_pos (Real.exp_pos u)]
      calc Real.exp (-(3 / 2 * u)) * (L * (Real.exp u * |Real.exp l - 2 + Real.exp (-l)|))
          ≤ Real.exp (-(3 / 2 * u)) * (L * (Real.exp u * (12 * l ^ 2))) := by gcongr
        _ = 12 * L * l ^ 2 * (Real.exp (-(3 / 2 * u)) * Real.exp u) := by ring
        _ = 12 * L * l ^ 2 * Real.exp (-(1 / 2 * u)) := by rw [← Real.exp_add]; ring_nf
    rw [hx]
    calc ‖e * W - e * Lt - fz l u‖ ≤ ‖e * W‖ + ‖e * Lt‖ + ‖fz l u‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ _ := by linarith
  -- the dominating function
  set a := 3 * (12 * L * l ^ 2) ^ 2 with ha
  set b := 3 * ((K * rr l)) ^ 2 with hb
  have hG : ∀ u : ℝ, ‖(Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u‖ ^ 2 * gw U u ≤
      3 * (‖fz l u‖ ^ 2 * gw U u) + a * (Real.exp (-(1 * u)) * gw U u) +
        b * (Real.exp (-(2 * u)) * gw U u) := by
    intro u
    have h := hpt u
    have hg := gw_nonneg U u
    have e1 : Real.exp (-(1 / 2 * u)) ^ 2 = Real.exp (-(1 * u)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have e2 : Real.exp (-(1 * u)) ^ 2 = Real.exp (-(2 * u)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    set p := ‖fz l u‖
    set q := 12 * L * l ^ 2 * Real.exp (-(1 / 2 * u))
    set r := (K * rr l) * Real.exp (-(1 * u))
    have hsq : ‖(Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u‖ ^ 2 ≤ 3 * p ^ 2 + 3 * q ^ 2 + 3 * r ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) h 2
      nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r)]
    have hq2 : 3 * q ^ 2 = a * Real.exp (-(1 * u)) := by
      rw [ha, ← e1]; ring
    have hr2 : 3 * r ^ 2 = b * Real.exp (-(2 * u)) := by
      rw [hb, ← e2]; ring
    calc _ ≤ (3 * p ^ 2 + 3 * q ^ 2 + 3 * r ^ 2) * gw U u := mul_le_mul_of_nonneg_right hsq hg
      _ = _ := by rw [hq2, hr2]; ring
  have hGint : Integrable (fun u : ℝ => 3 * (‖fz l u‖ ^ 2 * gw U u) +
      a * (Real.exp (-(1 * u)) * gw U u) + b * (Real.exp (-(2 * u)) * gw U u)) :=
    ((hint.const_mul 3).add ((integrable_exp_gw 1 U).const_mul a)).add
      ((integrable_exp_gw 2 U).const_mul b)
  have hmeas : Measurable (fun u : ℝ => (Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u) :=
    (Continuous.measurable (by fun_prop)).mul (measurable_D2 l)
  have hLint : Integrable (fun u => ‖(Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u‖ ^ 2 * gw U u) := by
    refine hGint.mono' ((hmeas.norm.pow_const 2).mul (gw_continuous U).measurable).aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gw_nonneg U u))]
    exact hG u
  refine ⟨hLint, ?_⟩
  calc ∫ u, ‖(Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u‖ ^ 2 * gw U u
      ≤ ∫ u : ℝ, (3 * (‖fz l u‖ ^ 2 * gw U u) + a * (Real.exp (-(1 * u)) * gw U u) +
          b * (Real.exp (-(2 * u)) * gw U u)) := integral_mono hLint hGint hG
    _ = 3 * (∫ u, ‖fz l u‖ ^ 2 * gw U u) + a * (Real.exp (-(1 * U) + 1 ^ 2 / 2) * c0) +
          b * (Real.exp (-(2 * U) + 2 ^ 2 / 2) * c0) := by
        have I1 : Integrable (fun u : ℝ => 3 * (‖fz l u‖ ^ 2 * gw U u)) := hint.const_mul 3
        have I2 : Integrable (fun u : ℝ => a * (Real.exp (-(1 * u)) * gw U u)) :=
          (integrable_exp_gw 1 U).const_mul a
        have I3 : Integrable (fun u : ℝ => b * (Real.exp (-(2 * u)) * gw U u)) :=
          (integrable_exp_gw 2 U).const_mul b
        have I12 : Integrable (fun u : ℝ => 3 * (‖fz l u‖ ^ 2 * gw U u) +
            a * (Real.exp (-(1 * u)) * gw U u)) := I1.add I2
        rw [integral_add I12 I3, integral_add I1 I2,
          integral_const_mul, integral_const_mul, integral_const_mul,
          integral_exp_gw, integral_exp_gw]
    _ ≤ 3 * (Cf * l ^ 3 * (Real.log (1 / l) + 3) ^ 2) +
          a * (Real.exp (-U) * Real.exp (1 / 2) * c0) + b * (Real.exp (-(2 * U)) * Real.exp 2 * c0) := by
        rw [show -(1 * U) + 1 ^ 2 / 2 = -U + 1 / 2 by ring,
          show -(2 * U) + 2 ^ 2 / 2 = -(2 * U) + 2 by ring, Real.exp_add, Real.exp_add]
        linarith
    _ ≤ _ := by
        set X := l ^ 3 * (Real.log (1 / l) + 3) ^ 2
        set Y := l ^ 4 * Real.exp (-U)
        set Z := rr l ^ 2 * Real.exp (-(2 * U))
        have hX : 0 ≤ X := by
          have : 0 ≤ Real.log (1 / l) := Real.log_nonneg (by rw [le_div_iff₀ hl0]; linarith)
          positivity
        have hY : 0 ≤ Y := by positivity
        have hZ : 0 ≤ Z := by positivity
        have ea : a * (Real.exp (-U) * Real.exp (1 / 2) * c0) =
            432 * L ^ 2 * Real.exp (1 / 2) * c0 * Y / l ^ 4 * l ^ 4 := by
          rw [ha]; field_simp; ring
        have ea' : a * (Real.exp (-U) * Real.exp (1 / 2) * c0) =
            432 * L ^ 2 * Real.exp (1 / 2) * c0 * Y := by
          rw [ea]; field_simp
        have eb : b * (Real.exp (-(2 * U)) * Real.exp 2 * c0) = 3 * K ^ 2 * Real.exp 2 * c0 * Z := by
          rw [hb]; ring
        rw [ea', eb]
        have h1 : 0 ≤ 432 * L ^ 2 * Real.exp (1 / 2) * c0 := by positivity
        have h2 : 0 ≤ 3 * K ^ 2 * Real.exp 2 * c0 := by positivity
        have e : (3 * Cf + 432 * L ^ 2 * Real.exp (1 / 2) * c0 + 3 * K ^ 2 * Real.exp 2 * c0) *
            (X + Y + Z) = 3 * (Cf * X) + 432 * L ^ 2 * Real.exp (1 / 2) * c0 * Y +
              3 * K ^ 2 * Real.exp 2 * c0 * Z + (3 * Cf * (Y + Z) +
              432 * L ^ 2 * Real.exp (1 / 2) * c0 * (X + Z) +
              3 * K ^ 2 * Real.exp 2 * c0 * (X + Y)) := by ring
        have : 0 ≤ 3 * Cf * (Y + Z) + 432 * L ^ 2 * Real.exp (1 / 2) * c0 * (X + Z) +
            3 * K ^ 2 * Real.exp 2 * c0 * (X + Y) := by positivity
        have e3 : Cf * l ^ 3 * (Real.log (1 / l) + 3) ^ 2 = Cf * X := by ring
        rw [e3, e]; linarith

/-- **Selberg's mean square under RH, smoothed form.** -/
theorem selberg_smoothed (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, 0 < l → l ≤ 1 →
    ∀ U : ℝ, Integrable (fun u => ‖(Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u‖ ^ 2 * gw U u) ∧
      ∫ u, ‖(Real.exp (-(3 / 2 * u)) : ℂ) * D2 l u‖ ^ 2 * gw U u
        ≤ C * (l ^ 3 * (Real.log (1 / l) + 3) ^ 2 + l ^ 4 * Real.exp (-U) +
          Real.exp (-(2 * U))) := by
  obtain ⟨K, hK0, hsd⟩ := second_difference
  obtain ⟨C, hC, h⟩ := selberg_of_remainder hRH (fun _ => 1)
    ⟨5 * K, by positivity, fun l u h0 h1 => (hsd l u h0 h1).trans_eq (by ring)⟩
  refine ⟨C, hC, fun l hl0 hl1 U => ?_⟩
  obtain ⟨hi, hb⟩ := h l hl0 hl1 U
  exact ⟨hi, hb.trans_eq (by ring)⟩

end LeanLab.PNTPort.Selberg

