module

public import LeanLab.PNTPort.Selberg.ZeroMVAll

/-!
# A multiplicity-weighted mean value theorem over zeta zeros

Lab proof, unit U-5921, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, no cited input, unconditional.

* `gauss_mean_value_pair`: `∫ ‖Σ_j a_j e^{iγ_j u}‖² e^{-(u-U)²/2} du ≤ √(2π) Σ_{j,k} ‖a_j‖‖a_k‖ e^{-(γ_j-γ_k)²/2}`,
  the first half of the lab's `Gallagher.gauss_mean_value`, copied from its proof.
* `gauss_mean_value_weighted`, the Schur test: for positive weights `w`,
  `∫ ... ≤ √(2π) Σ_j (‖a_j‖²/w_j) Σ_k w_k e^{-(γ_j-γ_k)²/2}`.
* `zero_mean_value_mult`: for every finite set `S` of nontrivial zeros and every `c`,
  `∫ ‖Σ_{ρ∈S} m(ρ) c_ρ e^{iγ_ρ u}‖² e^{-(u-U)²/2} du ≤ C Σ_{ρ∈S} m(ρ) ‖c_ρ‖² log(‖ρ‖ + 4)`,
  one factor `m(ρ)` where `zero_mean_value_all` with `a_ρ = m(ρ) c_ρ` gives `m(ρ)²`.
* `key_sum_one`: `Σ_ρ m(ρ) min(λ⁴, ‖ρ‖⁻⁴) log(‖ρ‖ + 4) ≤ C λ³ (log(1/λ) + 3)²`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex MeasureTheory Finset
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.Gallagher LeanLab.PNTPort.ZetaZeros

local notation "ζ" => riemannZeta

theorem gauss_mean_value_pair {ι : Type*} (s : Finset ι) (a : ι → ℂ) (γ : ι → ℝ) (U : ℝ) :
    ∫ u : ℝ, ‖∑ j ∈ s, a j * cexp (γ j * u * I)‖ ^ 2 * gw U u
      ≤ (2 * Real.pi) ^ (1 / 2 : ℝ) *
          ∑ j ∈ s, ∑ k ∈ s, ‖a j‖ * ‖a k‖ * Real.exp (-(γ j - γ k) ^ 2 / 2) := by
  set κ : ℂ := ((Real.pi : ℂ) / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ)
  -- expand the square and integrate term by term
  have hterm : ∀ j k : ι, ∫ u : ℝ, a j * (starRingEnd ℂ) (a k) *
      (cexp (((γ j - γ k : ℝ) : ℂ) * u * I) * (gw U u : ℂ))
      = a j * (starRingEnd ℂ) (a k) * (κ * cexp (((γ j - γ k : ℝ) : ℂ) * U * I
          - (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2)) := by
    intro j k
    rw [integral_const_mul, integral_gauss_char]
  have hint : ∀ j k : ι, Integrable (fun u : ℝ => a j * (starRingEnd ℂ) (a k) *
      (cexp (((γ j - γ k : ℝ) : ℂ) * u * I) * (gw U u : ℂ))) :=
    fun j k => (integrable_gauss_char U (γ j - γ k)).const_mul _
  have hexp : ∀ u : ℝ, ((‖∑ j ∈ s, a j * cexp (γ j * u * I)‖ ^ 2 * gw U u : ℝ) : ℂ)
      = ∑ j ∈ s, ∑ k ∈ s, a j * (starRingEnd ℂ) (a k) *
          (cexp (((γ j - γ k : ℝ) : ℂ) * u * I) * (gw U u : ℂ)) := by
    intro u
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum,
      sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    have : (starRingEnd ℂ) ((γ k : ℂ) * u * I) = -((γ k : ℂ) * u * I) := by
      simp [Complex.conj_ofReal]
    rw [this]
    have h2 : cexp (((γ j - γ k : ℝ) : ℂ) * u * I)
        = cexp ((γ j : ℂ) * u * I) * cexp (-((γ k : ℂ) * u * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h2]; ring
  -- the real integral is the real part of the complex one
  have hC : ((∫ u : ℝ, ‖∑ j ∈ s, a j * cexp (γ j * u * I)‖ ^ 2 * gw U u : ℝ) : ℂ)
      = ∑ j ∈ s, ∑ k ∈ s, a j * (starRingEnd ℂ) (a k) * (κ * cexp (((γ j - γ k : ℝ) : ℂ) * U * I
          - (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2)) := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => hint j k]
    refine sum_congr rfl fun j _ => ?_
    rw [integral_finset_sum _ fun k _ => hint j k]
    exact sum_congr rfl fun k _ => hterm j k
  have hle : (∫ u : ℝ, ‖∑ j ∈ s, a j * cexp (γ j * u * I)‖ ^ 2 * gw U u)
      ≤ ‖((∫ u : ℝ, ‖∑ j ∈ s, a j * cexp (γ j * u * I)‖ ^ 2 * gw U u : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  refine hle.trans ?_
  rw [hC]
  -- each term has norm `√(2π) ‖a j‖ ‖a k‖ e^{-(γ_j - γ_k)²/2}`
  have hnorm : ∀ j k : ι, ‖a j * (starRingEnd ℂ) (a k) * (κ * cexp (((γ j - γ k : ℝ) : ℂ) * U * I
      - (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2))‖
      = (2 * Real.pi) ^ (1 / 2 : ℝ) * (‖a j‖ * ‖a k‖ * Real.exp (-(γ j - γ k) ^ 2 / 2)) := by
    intro j k
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, norm_const, Complex.norm_exp]
    have : (((γ j - γ k : ℝ) : ℂ) * U * I - (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2).re
        = -(γ j - γ k) ^ 2 / 2 := by
      rw [show (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2 = (((γ j - γ k) ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.sub_re, Complex.ofReal_re]
      simp
      ring
    rw [this]; ring
  calc ‖∑ j ∈ s, ∑ k ∈ s, a j * (starRingEnd ℂ) (a k) * (κ * cexp (((γ j - γ k : ℝ) : ℂ) * U * I
          - (((γ j - γ k : ℝ) : ℂ)) ^ 2 / 2))‖
      ≤ ∑ j ∈ s, ∑ k ∈ s, (2 * Real.pi) ^ (1 / 2 : ℝ) *
          (‖a j‖ * ‖a k‖ * Real.exp (-(γ j - γ k) ^ 2 / 2)) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => hnorm j k))
    _ = (2 * Real.pi) ^ (1 / 2 : ℝ) *
          ∑ j ∈ s, ∑ k ∈ s, ‖a j‖ * ‖a k‖ * Real.exp (-(γ j - γ k) ^ 2 / 2) := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by rw [mul_sum]

/-- **The Schur test** with positive weights. -/
theorem gauss_mean_value_weighted {ι : Type*} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ j ∈ s, 0 < w j) (γ : ι → ℝ) (U : ℝ) :
    ∫ u : ℝ, ‖∑ j ∈ s, a j * cexp (γ j * u * I)‖ ^ 2 * gw U u
      ≤ (2 * Real.pi) ^ (1 / 2 : ℝ) *
          ∑ j ∈ s, ‖a j‖ ^ 2 / w j * ∑ k ∈ s, w k * Real.exp (-(γ j - γ k) ^ 2 / 2) := by
  refine (gauss_mean_value_pair s a γ U).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set E : ι → ι → ℝ := fun j k => Real.exp (-(γ j - γ k) ^ 2 / 2) with hE
  have hpt : ∀ j ∈ s, ∀ k ∈ s, ‖a j‖ * ‖a k‖ * E j k
      ≤ (‖a j‖ ^ 2 / w j * (w k * E j k) + ‖a k‖ ^ 2 / w k * (w j * E j k)) / 2 := by
    intro j hj k hk
    have hj0 := hw j hj; have hk0 := hw k hk
    have he : 0 < E j k := Real.exp_pos _
    have key : ‖a j‖ * ‖a k‖ ≤ (‖a j‖ ^ 2 * (w k / w j) + ‖a k‖ ^ 2 * (w j / w k)) / 2 := by
      have h1 : 0 ≤ (‖a j‖ * w k - ‖a k‖ * w j) ^ 2 := sq_nonneg _
      have e : (‖a j‖ ^ 2 * (w k / w j) + ‖a k‖ ^ 2 * (w j / w k)) / 2 - ‖a j‖ * ‖a k‖
          = (‖a j‖ * w k - ‖a k‖ * w j) ^ 2 / (2 * w j * w k) := by
        field_simp; ring
      have : 0 ≤ (‖a j‖ * w k - ‖a k‖ * w j) ^ 2 / (2 * w j * w k) := by positivity
      linarith
    have e2 : (‖a j‖ ^ 2 / w j * (w k * E j k) + ‖a k‖ ^ 2 / w k * (w j * E j k)) / 2
        = (‖a j‖ ^ 2 * (w k / w j) + ‖a k‖ ^ 2 * (w j / w k)) / 2 * E j k := by
      field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_right key he.le
  have hsym : ∑ j ∈ s, ∑ k ∈ s, ‖a k‖ ^ 2 / w k * (w j * E j k)
      = ∑ j ∈ s, ∑ k ∈ s, ‖a j‖ ^ 2 / w j * (w k * E j k) := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
    simp only [hE]
    rw [show (γ k - γ j) ^ 2 = (γ j - γ k) ^ 2 by ring]
  calc ∑ j ∈ s, ∑ k ∈ s, ‖a j‖ * ‖a k‖ * E j k
      ≤ ∑ j ∈ s, ∑ k ∈ s,
          (‖a j‖ ^ 2 / w j * (w k * E j k) + ‖a k‖ ^ 2 / w k * (w j * E j k)) / 2 :=
        sum_le_sum fun j hj => sum_le_sum fun k hk => hpt j hj k hk
    _ = (∑ j ∈ s, ∑ k ∈ s, ‖a j‖ ^ 2 / w j * (w k * E j k)
          + ∑ j ∈ s, ∑ k ∈ s, ‖a k‖ ^ 2 / w k * (w j * E j k)) / 2 := by
        rw [← sum_add_distrib, sum_div]
        exact sum_congr rfl fun j _ => by rw [← sum_add_distrib, sum_div]
    _ = ∑ j ∈ s, ‖a j‖ ^ 2 / w j * ∑ k ∈ s, w k * E j k := by
        rw [hsym, add_self_div_two]
        exact sum_congr rfl fun j _ => by rw [mul_sum]

/-- **The zero mean value theorem with one factor of multiplicity.** -/
theorem zero_mean_value_mult : ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℂ), (∀ ρ ∈ S, NZ ρ) →
    ∀ (c : ℂ → ℂ) (U : ℝ),
    ∫ u : ℝ, ‖∑ ρ ∈ S, (mz ρ : ℂ) * c ρ * cexp (ρ.im * u * I)‖ ^ 2 * gw U u
      ≤ C * ∑ ρ ∈ S, mz ρ * ‖c ρ‖ ^ 2 * Real.log (‖ρ‖ + 4) := by
  obtain ⟨C₁, hC₁, hZ⟩ := gauss_zero_sum
  obtain ⟨B, hB0, hB⟩ := sum_mz_low
  refine ⟨(2 * Real.pi) ^ (1 / 2 : ℝ) * (C₁ + 30 * B), by positivity, fun S hS c U => ?_⟩
  have hm1 : ∀ ρ ∈ S, 1 ≤ mz ρ := by
    intro ρ hρ
    have hk1 : ρ ≠ 1 := by
      intro h; have := (hS ρ hρ).2.2; rw [h, one_re] at this; exact lt_irrefl _ this
    unfold mz; exact_mod_cast ord_pos (hS ρ hρ).1 hk1
  refine (gauss_mean_value_weighted S (fun ρ => (mz ρ : ℂ) * c ρ) mz
    (fun ρ hρ => by linarith [hm1 ρ hρ]) (fun ρ => ρ.im) U).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [mul_sum]
  refine sum_le_sum fun j hj => ?_
  have hL1 := one_le_log_add_four (norm_nonneg j)
  have hLj : Real.log (|j.im| + 4) ≤ Real.log (‖j‖ + 4) :=
    Real.log_le_log (by positivity) (by linarith [abs_im_le_norm j])
  have hin : ∑ k ∈ S, mz k * Real.exp (-(j.im - k.im) ^ 2 / 2)
      ≤ (C₁ + 30 * B) * Real.log (‖j‖ + 4) := by
    rw [← sum_filter_add_sum_filter_not S (fun k => 4 ≤ |k.im|)]
    have h1 : ∑ k ∈ S.filter (fun k => 4 ≤ |k.im|), mz k * Real.exp (-(j.im - k.im) ^ 2 / 2)
        ≤ C₁ * Real.log (|j.im| + 4) :=
      hZ j.im (S.filter (fun k => 4 ≤ |k.im|)) fun k hk => by
        rw [mem_filter] at hk; exact ⟨(hS k hk.1).1, hk.2⟩
    have h2 : ∑ k ∈ S.filter (fun k => ¬ 4 ≤ |k.im|), mz k * Real.exp (-(j.im - k.im) ^ 2 / 2)
        ≤ 30 * B := by
      have hlow := hB 4 (by norm_num) (S.filter (fun k => ¬ 4 ≤ |k.im|)) fun k hk => by
        rw [mem_filter] at hk; exact ⟨hS k hk.1, (not_le.mp hk.2).le⟩
      refine le_trans (sum_le_sum fun k hk => ?_) (hlow.trans_eq (by ring))
      have : Real.exp (-(j.im - k.im) ^ 2 / 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (j.im - k.im)]
      exact mul_le_of_le_one_right (mz_nonneg k) this
    have : C₁ * Real.log (|j.im| + 4) ≤ C₁ * Real.log (‖j‖ + 4) := by gcongr
    nlinarith
  have hmj := hm1 j hj
  have e : ‖(mz j : ℂ) * c j‖ ^ 2 / mz j = mz j * ‖c j‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mz_nonneg j)]
    field_simp
  rw [e]
  calc mz j * ‖c j‖ ^ 2 * ∑ k ∈ S, mz k * Real.exp (-(j.im - k.im) ^ 2 / 2)
      ≤ mz j * ‖c j‖ ^ 2 * ((C₁ + 30 * B) * Real.log (‖j‖ + 4)) := by
        gcongr
    _ = (C₁ + 30 * B) * (mz j * ‖c j‖ ^ 2 * Real.log (‖j‖ + 4)) := by ring

/-- **The key zero sum with one factor of multiplicity**:
`Σ m(ρ) min(λ⁴, ‖ρ‖⁻⁴) log(‖ρ‖ + 4) ≤ C λ³ (log(1/λ) + 3)²` for `0 < λ ≤ 1`. -/
theorem key_sum_one : ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, 0 < l → l ≤ 1 → ∀ S : Finset ℂ,
    (∀ ρ ∈ S, NZ ρ) →
    ∑ ρ ∈ S, mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4)
      ≤ C * l ^ 3 * (Real.log (1 / l) + 3) ^ 2 := by
  obtain ⟨H, hH, hhead⟩ := head_count
  obtain ⟨C₃, hC₃, htail⟩ := tail_count
  refine ⟨12 * H + C₃, by positivity, fun l hl0 hl1 S hS => ?_⟩
  set T := 6 / l with hT
  have hT6 : 6 ≤ T := by rw [hT, le_div_iff₀ hl0]; linarith
  set A := Real.log (1 / l) + 3 with hA
  have hlA : 0 ≤ Real.log (1 / l) := Real.log_nonneg (by rw [le_div_iff₀ hl0]; linarith)
  set LT := Real.log (T + 4) with hLT
  have hLT1 : 1 ≤ LT := one_le_log_add_four (by linarith)
  have hLTA : LT ≤ A := by
    have : T + 4 ≤ 10 * (1 / l) := by
      rw [hT]; have : 4 ≤ 4 / l := by rw [le_div_iff₀ hl0]; linarith
      have e : 6 / l + 4 / l = 10 * (1 / l) := by ring
      linarith
    have h10 : Real.log 10 < 3 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h := Real.exp_one_gt_d9
      have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3
      have : (10 : ℝ) < 2.7182818283 ^ 3 := by norm_num
      linarith
    calc LT ≤ Real.log (10 * (1 / l)) := Real.log_le_log (by linarith) this
      _ = Real.log 10 + Real.log (1 / l) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ A := by rw [hA]; linarith
  have hlogT : Real.log T + 2 ≤ 2 * A := by
    have : Real.log T = Real.log 6 + Real.log (1 / l) := by
      rw [hT, div_eq_mul_one_div, Real.log_mul (by norm_num) (by positivity)]
    have h6 : Real.log 6 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h := Real.exp_one_gt_d9
      have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h.le 2
      have : (6 : ℝ) < 2.7182818283 ^ 2 := by norm_num
      linarith
    rw [hA]; linarith
  rw [← sum_filter_add_sum_filter_not S (fun ρ => ‖ρ‖ ≤ T)]
  have hhd : ∑ ρ ∈ S.filter (fun ρ => ‖ρ‖ ≤ T),
      mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4) ≤ 12 * H * l ^ 3 * A ^ 2 := by
    calc _ ≤ ∑ ρ ∈ S.filter (fun ρ => ‖ρ‖ ≤ T), mz ρ * (l ^ 4 * LT) := by
          refine sum_le_sum fun ρ hρ => ?_
          rw [mem_filter] at hρ
          have hlog : Real.log (‖ρ‖ + 4) ≤ LT := Real.log_le_log (by positivity) (by linarith)
          have := mz_nonneg ρ
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ this
          exact mul_le_mul (min_le_left _ _) hlog
            (Real.log_nonneg (by linarith [norm_nonneg ρ])) (by positivity)
      _ = (∑ ρ ∈ S.filter (fun ρ => ‖ρ‖ ≤ T), mz ρ) * (l ^ 4 * LT) := by rw [sum_mul]
      _ ≤ (H * T * (Real.log T + 2)) * (l ^ 4 * LT) := by
          gcongr
          exact hhead T hT6 _ (fun ρ hρ => by
            rw [mem_filter] at hρ; exact ⟨hS ρ hρ.1, hρ.2⟩)
      _ ≤ (H * T * (2 * A)) * (l ^ 4 * A) := by gcongr
      _ = 12 * H * l ^ 3 * A ^ 2 := by rw [hT]; field_simp; ring
  have htl : ∑ ρ ∈ S.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
      mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4) ≤ C₃ * l ^ 3 * A ^ 2 := by
    calc _ ≤ ∑ ρ ∈ S.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
          (LT / T ^ 2) * ((analyticOrderNatAt ζ ρ : ℝ) / ‖ρ‖ ^ 2) := by
          refine sum_le_sum fun ρ hρ => ?_
          rw [mem_filter] at hρ
          have hr : T < ‖ρ‖ := lt_of_not_ge hρ.2
          have hp : 0 < ‖ρ‖ := by linarith
          have hT0 : 0 < T := by linarith
          have hrat := log_ratio_le hT0 hr.le
          -- `log(r + 4)/r² ≤ LT/T²`
          have hq : Real.log (‖ρ‖ + 4) / ‖ρ‖ ^ 2 ≤ LT / T ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have hL0 : 0 ≤ Real.log (‖ρ‖ + 4) := Real.log_nonneg (by linarith)
            have h1 : T * Real.log (‖ρ‖ + 4) * T ≤ ‖ρ‖ * LT * T :=
              mul_le_mul_of_nonneg_right hrat hT0.le
            have h2 : ‖ρ‖ * LT * T ≤ ‖ρ‖ * LT * ‖ρ‖ :=
              mul_le_mul_of_nonneg_left hr.le (by positivity)
            nlinarith
          have e : mz ρ * min (l ^ 4) (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4)
              ≤ (Real.log (‖ρ‖ + 4) / ‖ρ‖ ^ 2) * ((analyticOrderNatAt ζ ρ : ℝ) / ‖ρ‖ ^ 2) := by
            have : mz ρ * (‖ρ‖⁻¹ ^ 4) * Real.log (‖ρ‖ + 4)
                = (Real.log (‖ρ‖ + 4) / ‖ρ‖ ^ 2) * ((analyticOrderNatAt ζ ρ : ℝ) / ‖ρ‖ ^ 2) := by
              unfold mz; field_simp
            rw [← this]
            have := mz_nonneg ρ
            have hL0 : 0 ≤ Real.log (‖ρ‖ + 4) := Real.log_nonneg (by linarith)
            gcongr
            exact min_le_right _ _
          exact e.trans (mul_le_mul_of_nonneg_right hq (by positivity))
      _ = (LT / T ^ 2) * ∑ ρ ∈ S.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
          (analyticOrderNatAt ζ ρ : ℝ) / ‖ρ‖ ^ 2 := by rw [mul_sum]
      _ ≤ (LT / T ^ 2) * (C₃ * (Real.log T + 1) / T) := by
          gcongr
          exact htail T hT6 _ (fun ρ hρ => by
            rw [mem_filter] at hρ
            exact ⟨(hS ρ hρ.1).1, (hS ρ hρ.1).2.1, (hS ρ hρ.1).2.2, lt_of_not_ge hρ.2⟩)
      _ ≤ (A / T ^ 2) * (C₃ * (2 * A) / T) := by
          have h0 : 0 ≤ LT := by linarith
          have hT0 : 0 < T := by linarith
          have h1 : LT / T ^ 2 ≤ A / T ^ 2 := div_le_div_of_nonneg_right hLTA (by positivity)
          have h2 : C₃ * (Real.log T + 1) / T ≤ C₃ * (2 * A) / T := by
            apply div_le_div_of_nonneg_right _ hT0.le
            exact mul_le_mul_of_nonneg_left (by linarith) hC₃
          have h3 : 0 ≤ C₃ * (Real.log T + 1) / T :=
            div_nonneg (mul_nonneg hC₃ (by linarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ T)]))
              hT0.le
          exact mul_le_mul h1 h2 h3 (by positivity)
      _ = C₃ * l ^ 3 * A ^ 2 / 108 := by rw [hT]; field_simp; ring
      _ ≤ C₃ * l ^ 3 * A ^ 2 := by
          have : 0 ≤ C₃ * l ^ 3 * A ^ 2 := by positivity
          linarith
  calc _ ≤ 12 * H * l ^ 3 * A ^ 2 + C₃ * l ^ 3 * A ^ 2 := add_le_add hhd htl
    _ = (12 * H + C₃) * l ^ 3 * A ^ 2 := by ring

end LeanLab.PNTPort.Selberg

