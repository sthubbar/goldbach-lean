module

public import LeanLab.PNTPort.Selberg.Sharp1

/-!
# Sharp windows, part 2: zero sums

Lab proof, unit U-5924, CLOUD 20261020T0216Z-cloud32, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, no cited input, unconditional.

* `tail_log_sum`: for `T ≥ 6`, zeros with `‖ρ‖ > T` have `Σ m(ρ) log(‖ρ‖ + 4)/‖ρ‖² ≤ C (log(T + 4) + 3)²/T`,
  by dyadic shells and a telescoping potential `Φ(T) = 10H (log(T + 4) + 3)²/T`;
* `key_sum_two`: for `0 < δ ≤ 1`, `Σ m(ρ) min(δ², ‖ρ‖⁻²) log(‖ρ‖ + 4) ≤ C δ (log(1/δ) + 3)²`;
* `zs_mean`: if every finite truncation of `Σ_ρ d ρ e^{iγu}` has Gaussian mean square at most `B`
  and `Σ ‖d ρ‖ < ∞`, the full sum is integrable against the weight with mean square at most `2B`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Complex Finset MeasureTheory Filter Topology
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.Gallagher

local notation "ζ" => riemannZeta

/-- `log(r + 4)/r²` decreases. -/
lemma log_div_sq_le {T r : ℝ} (hT : 0 < T) (hr : T ≤ r) :
    Real.log (r + 4) / r ^ 2 ≤ Real.log (T + 4) / T ^ 2 := by
  have hp : 0 < r := lt_of_lt_of_le hT hr
  have hrat := log_ratio_le hT hr
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hL0 : 0 ≤ Real.log (r + 4) := Real.log_nonneg (by linarith)
  have hLT : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have h1 : T * Real.log (r + 4) * T ≤ r * Real.log (T + 4) * T :=
    mul_le_mul_of_nonneg_right hrat hT.le
  have h2 : r * Real.log (T + 4) * T ≤ r * Real.log (T + 4) * r :=
    mul_le_mul_of_nonneg_left hr (by positivity)
  nlinarith

/-- **The log-weighted tail.** -/
theorem tail_log_sum : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 6 ≤ T → ∀ S : Finset ℂ,
    (∀ ρ ∈ S, NZ ρ ∧ T < ‖ρ‖) →
    ∑ ρ ∈ S, mz ρ * Real.log (‖ρ‖ + 4) / ‖ρ‖ ^ 2 ≤ C * (Real.log (T + 4) + 3) ^ 2 / T := by
  obtain ⟨H, hH, hhead⟩ := head_count
  set Φ : ℝ → ℝ := fun T => 10 * H * (Real.log (T + 4) + 3) ^ 2 / T with hΦ
  -- one shell
  have hshell : ∀ T : ℝ, 6 ≤ T → ∀ S : Finset ℂ, (∀ ρ ∈ S, NZ ρ ∧ T < ‖ρ‖ ∧ ‖ρ‖ ≤ 2 * T) →
      ∑ ρ ∈ S, mz ρ * Real.log (‖ρ‖ + 4) / ‖ρ‖ ^ 2 ≤ 2 * H * (Real.log (T + 4) + 3) ^ 2 / T := by
    intro T hT S hS
    have hT0 : 0 < T := by linarith
    set L := Real.log (T + 4)
    have hL1 : 1 ≤ L := one_le_log_add_four hT0.le
    calc ∑ ρ ∈ S, mz ρ * Real.log (‖ρ‖ + 4) / ‖ρ‖ ^ 2
        ≤ ∑ ρ ∈ S, mz ρ * (L / T ^ 2) := by
          refine sum_le_sum fun ρ hρ => ?_
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (log_div_sq_le hT0 (hS ρ hρ).2.1.le) (mz_nonneg ρ)
      _ = (∑ ρ ∈ S, mz ρ) * (L / T ^ 2) := by rw [sum_mul]
      _ ≤ (H * (2 * T) * (Real.log (2 * T) + 2)) * (L / T ^ 2) := by
          gcongr
          exact hhead (2 * T) (by linarith) S fun ρ hρ => ⟨(hS ρ hρ).1, (hS ρ hρ).2.2⟩
      _ ≤ (H * (2 * T) * (L + 3)) * ((L + 3) / T ^ 2) := by
          have h2 : Real.log (2 * T) ≤ L + 1 := by
            rw [Real.log_mul (by norm_num) hT0.ne']
            have h3 : Real.log T ≤ Real.log (T + 4) := Real.log_le_log hT0 (by linarith)
            have h4 : Real.log 2 < 1 := by
              have := Real.log_two_lt_d9; linarith
            linarith
          have h0 : 0 ≤ Real.log (2 * T) + 2 := by
            have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith); linarith
          apply mul_le_mul _ _ (by positivity) (by positivity)
          · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          · exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 2 * H * (L + 3) ^ 2 / T := by field_simp
  have hstep : ∀ T : ℝ, 6 ≤ T → 2 * H * (Real.log (T + 4) + 3) ^ 2 / T + Φ (2 * T) ≤ Φ T := by
    intro T hT
    have hT0 : 0 < T := by linarith
    have hL1 : 1 ≤ Real.log (T + 4) := one_le_log_add_four hT0.le
    have hL2 : Real.log (2 * T + 4) ≤ Real.log (T + 4) + 1 := by
      have h5 : Real.log (2 * T + 4) ≤ Real.log (2 * (T + 4)) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) (by linarith)] at h5
      have h6 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    have hl0 : 0 ≤ Real.log (2 * T + 4) := Real.log_nonneg (by linarith)
    have hsq : (Real.log (2 * T + 4) + 3) ^ 2 ≤ 25 / 16 * (Real.log (T + 4) + 3) ^ 2 := by
      have : Real.log (2 * T + 4) + 3 ≤ 5 / 4 * (Real.log (T + 4) + 3) := by linarith
      nlinarith
    have h1 : Φ (2 * T) ≤ 10 * H * (25 / 16 * (Real.log (T + 4) + 3) ^ 2) / (2 * T) := by
      simp only [hΦ]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)
    have e : 2 * H * (Real.log (T + 4) + 3) ^ 2 / T +
        10 * H * (25 / 16 * (Real.log (T + 4) + 3) ^ 2) / (2 * T)
        = (157 / 16) * (H * (Real.log (T + 4) + 3) ^ 2) / T := by field_simp; ring
    have hH0 : 0 ≤ H * (Real.log (T + 4) + 3) ^ 2 / T := by positivity
    have e2 : Φ T = 10 * (H * (Real.log (T + 4) + 3) ^ 2) / T := by simp only [hΦ]; ring
    rw [e2]
    have : (157 / 16) * (H * (Real.log (T + 4) + 3) ^ 2) / T ≤
        10 * (H * (Real.log (T + 4) + 3) ^ 2) / T := by
      apply div_le_div_of_nonneg_right _ hT0.le
      have : 0 ≤ H * (Real.log (T + 4) + 3) ^ 2 := by positivity
      linarith
    linarith
  -- induction on the dyadic range
  have hind : ∀ k : ℕ, ∀ T : ℝ, 6 ≤ T → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, NZ ρ ∧ T < ‖ρ‖ ∧ ‖ρ‖ ≤ 2 ^ k * T) →
      ∑ ρ ∈ S, mz ρ * Real.log (‖ρ‖ + 4) / ‖ρ‖ ^ 2 ≤ Φ T := by
    intro k
    induction k with
    | zero =>
      intro T hT S hS
      have : S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ρ hρ
        have := hS ρ hρ
        simp at this; linarith [this.2.1, this.2.2]
      rw [this, sum_empty]
      simp only [hΦ]
      have hT0 : 0 < T := by linarith
      have := one_le_log_add_four hT0.le
      positivity
    | succ k ih =>
      intro T hT S hS
      rw [← sum_filter_add_sum_filter_not S (fun ρ => ‖ρ‖ ≤ 2 * T)]
      have h1 := hshell T hT (S.filter (fun ρ => ‖ρ‖ ≤ 2 * T)) fun ρ hρ => by
        rw [mem_filter] at hρ; exact ⟨(hS ρ hρ.1).1, (hS ρ hρ.1).2.1, hρ.2⟩
      have h2 := ih (2 * T) (by linarith) (S.filter (fun ρ => ¬ ‖ρ‖ ≤ 2 * T)) fun ρ hρ => by
        rw [mem_filter] at hρ
        refine ⟨(hS ρ hρ.1).1, lt_of_not_ge hρ.2, ?_⟩
        have := (hS ρ hρ.1).2.2
        rw [pow_succ] at this; linarith
      linarith [hstep T hT]
  refine ⟨10 * H, by positivity, fun T hT S hS => ?_⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((∑ ρ ∈ S, ‖ρ‖) / T) (by norm_num : (1 : ℝ) < 2)
  have hT0 : 0 < T := by linarith
  have := hind k T hT S fun ρ hρ => by
    refine ⟨(hS ρ hρ).1, (hS ρ hρ).2, ?_⟩
    have h1 : ‖ρ‖ ≤ ∑ ρ ∈ S, ‖ρ‖ := single_le_sum (fun ρ _ => norm_nonneg ρ) hρ
    rw [div_lt_iff₀ hT0] at hk
    linarith
  simpa [hΦ, mul_div_assoc] using this

/-- **The key sum for sharp windows.** -/
theorem key_sum_two : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ S : Finset ℂ,
    (∀ ρ ∈ S, NZ ρ) →
    ∑ ρ ∈ S, mz ρ * min (δ ^ 2) (‖ρ‖⁻¹ ^ 2) * Real.log (‖ρ‖ + 4)
      ≤ C * δ * (Real.log (1 / δ) + 3) ^ 2 := by
  obtain ⟨H, hH, hhead⟩ := head_count
  obtain ⟨C₃, hC₃, htail⟩ := tail_log_sum
  refine ⟨12 * H + 4 * C₃, by positivity, fun l hl0 hl1 S hS => ?_⟩
  set T := 6 / l with hT
  have hT6 : 6 ≤ T := by rw [hT, le_div_iff₀ hl0]; linarith
  have hT0 : 0 < T := by linarith
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
      mz ρ * min (l ^ 2) (‖ρ‖⁻¹ ^ 2) * Real.log (‖ρ‖ + 4) ≤ 12 * H * l * A ^ 2 := by
    calc _ ≤ ∑ ρ ∈ S.filter (fun ρ => ‖ρ‖ ≤ T), mz ρ * (l ^ 2 * LT) := by
          refine sum_le_sum fun ρ hρ => ?_
          rw [mem_filter] at hρ
          have hlog : Real.log (‖ρ‖ + 4) ≤ LT := Real.log_le_log (by positivity) (by linarith)
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (mz_nonneg ρ)
          exact mul_le_mul (min_le_left _ _) hlog
            (Real.log_nonneg (by linarith [norm_nonneg ρ])) (by positivity)
      _ = (∑ ρ ∈ S.filter (fun ρ => ‖ρ‖ ≤ T), mz ρ) * (l ^ 2 * LT) := by rw [sum_mul]
      _ ≤ (H * T * (Real.log T + 2)) * (l ^ 2 * LT) := by
          gcongr
          exact hhead T hT6 _ (fun ρ hρ => by
            rw [mem_filter] at hρ; exact ⟨hS ρ hρ.1, hρ.2⟩)
      _ ≤ (H * T * (2 * A)) * (l ^ 2 * A) := by gcongr
      _ = 12 * H * l * A ^ 2 := by rw [hT]; field_simp; ring
  have htl : ∑ ρ ∈ S.filter (fun ρ => ¬ ‖ρ‖ ≤ T),
      mz ρ * min (l ^ 2) (‖ρ‖⁻¹ ^ 2) * Real.log (‖ρ‖ + 4) ≤ 4 * C₃ * l * A ^ 2 := by
    calc _ ≤ ∑ ρ ∈ S.filter (fun ρ => ¬ ‖ρ‖ ≤ T), mz ρ * Real.log (‖ρ‖ + 4) / ‖ρ‖ ^ 2 := by
          refine sum_le_sum fun ρ hρ => ?_
          have hm := mz_nonneg ρ
          have hL := Real.log_nonneg (show (1 : ℝ) ≤ ‖ρ‖ + 4 by linarith [norm_nonneg ρ])
          calc mz ρ * min (l ^ 2) (‖ρ‖⁻¹ ^ 2) * Real.log (‖ρ‖ + 4)
              ≤ mz ρ * (‖ρ‖⁻¹ ^ 2) * Real.log (‖ρ‖ + 4) := by
                gcongr; exact min_le_right _ _
            _ = _ := by rw [inv_pow]; ring
      _ ≤ C₃ * (LT + 3) ^ 2 / T := htail T hT6 _ fun ρ hρ => by
          rw [mem_filter] at hρ; exact ⟨hS ρ hρ.1, lt_of_not_ge hρ.2⟩
      _ ≤ C₃ * (2 * A) ^ 2 / T := by
          gcongr; linarith
      _ = 4 * C₃ * l * A ^ 2 / 6 := by rw [hT]; field_simp; ring
      _ ≤ 4 * C₃ * l * A ^ 2 := by
          have : 0 ≤ 4 * C₃ * l * A ^ 2 := by positivity
          linarith
  calc _ ≤ 12 * H * l * A ^ 2 + 4 * C₃ * l * A ^ 2 := add_le_add hhd htl
    _ = (12 * H + 4 * C₃) * l * A ^ 2 := by ring

/-- A general zero sum `Σ_ρ d ρ e^{iγu}`. -/
noncomputable def fS (d : ℂ → ℂ) (u : ℝ) : ℂ := ∑' ρ : NZs, d ρ.1 * cexp (ρ.1.im * u * I)

/-- **The mean square of a zero sum from its finite truncations.** -/
theorem zs_mean (d : ℂ → ℂ) (hd : Summable (fun ρ : NZs => ‖d ρ.1‖)) (U B : ℝ)
    (hfin : ∀ s : Finset NZs,
      ∫ u : ℝ, ‖∑ ρ ∈ s, d ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 * gw U u ≤ B) :
    Integrable (fun u => ‖fS d u‖ ^ 2 * gw U u) ∧ ∫ u, ‖fS d u‖ ^ 2 * gw U u ≤ 2 * B := by
  have hcont : Continuous (fS d) := by
    unfold fS
    refine continuous_tsum (fun ρ => by fun_prop) hd (fun ρ u => ?_)
    rw [norm_mul, norm_cexp_im, mul_one]
  have hbd : ∀ u, ‖fS d u‖ ≤ ∑' ρ : NZs, ‖d ρ.1‖ := by
    intro u
    unfold fS
    have hs : Summable (fun ρ : NZs => ‖d ρ.1 * cexp (ρ.1.im * u * I)‖) := by
      simp_rw [norm_mul, norm_cexp_im, mul_one]; exact hd
    refine (norm_tsum_le_tsum_norm hs).trans_eq ?_
    simp_rw [norm_mul, norm_cexp_im, mul_one]
  have hint := integrable_sq_gw hcont hbd U
  refine ⟨hint, ?_⟩
  set cG := ∫ u, gw U u with hcG
  have hcG0 : 0 ≤ cG := integral_nonneg (gw_nonneg U)
  set g : NZs → ℝ := fun ρ => ‖d ρ.1‖ with hg
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
  have hpt : ∀ u : ℝ, ‖fS d u‖ ^ 2 * gw U u ≤
      2 * (‖∑ ρ ∈ s, d ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 * gw U u) + 2 * δ ^ 2 * gw U u := by
    intro u
    have hsu : Summable (fun ρ : NZs => d ρ.1 * cexp (ρ.1.im * u * I)) := by
      refine Summable.of_norm_bounded hd (fun ρ => ?_)
      rw [norm_mul, norm_cexp_im, mul_one]
    have hsplit := hsu.sum_add_tsum_subtype_compl s
    have htail : ‖∑' ρ : {ρ // ρ ∉ s}, d ρ.1.1 * cexp (ρ.1.1.im * u * I)‖ ≤ δ := by
      have hn : Summable (fun ρ : {ρ // ρ ∉ s} => ‖d ρ.1.1 * cexp (ρ.1.1.im * u * I)‖) := by
        simp_rw [norm_mul, norm_cexp_im, mul_one]; exact hd.subtype _
      refine (norm_tsum_le_tsum_norm hn).trans ?_
      simp_rw [norm_mul, norm_cexp_im, mul_one]
      exact hs.le
    have : ‖fS d u‖ ≤ ‖∑ ρ ∈ s, d ρ.1 * cexp (ρ.1.im * u * I)‖ + δ := by
      unfold fS; rw [← hsplit]
      exact (norm_add_le _ _).trans (by linarith)
    have hgw := gw_nonneg U u
    have h2 : ‖fS d u‖ ^ 2 ≤ 2 * ‖∑ ρ ∈ s, d ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 + 2 * δ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith [sq_nonneg (‖∑ ρ ∈ s, d ρ.1 * cexp (ρ.1.im * u * I)‖ - δ)]
    nlinarith
  have hint_s : Integrable
      (fun u : ℝ => ‖∑ ρ ∈ s, d ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 * gw U u) :=
    integrable_sq_gw (continuous_finsetSum _ (fun ρ _ => by fun_prop))
      (M := ∑ ρ ∈ s, ‖d ρ.1‖)
      (fun u => (norm_sum_le _ _).trans_eq (by simp_rw [norm_mul, norm_cexp_im, mul_one])) U
  calc ∫ u, ‖fS d u‖ ^ 2 * gw U u
      ≤ ∫ u : ℝ, (2 * (‖∑ ρ ∈ s, d ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 * gw U u)
          + 2 * δ ^ 2 * gw U u) :=
        integral_mono hint ((hint_s.const_mul 2).add ((gw_integrable U).const_mul _)) hpt
    _ = 2 * (∫ u : ℝ, ‖∑ ρ ∈ s, d ρ.1 * cexp (ρ.1.im * u * I)‖ ^ 2 * gw U u) + 2 * δ ^ 2 * cG := by
        rw [integral_add (hint_s.const_mul 2) ((gw_integrable U).const_mul _),
          integral_const_mul, integral_const_mul]
    _ ≤ 2 * B + ε := by have := hfin s; linarith

end LeanLab.PNTPort.Selberg

