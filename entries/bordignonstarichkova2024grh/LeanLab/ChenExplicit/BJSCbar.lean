module

public import LeanLab.ChenExplicit.C2Bound

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0503Z-16389, unit U-0916.
P0009 Bordignon, Johnston, Starichkova, An explicit version of Chen's theorem and the
linear sieve, arXiv 2207.09452, latest HTML, read in Claude in Chrome per RULES_BLOCKERS B1.

Lemma 52 defines `c̄ = ∫_{1/8}^{1/3} log(2 - 3β) / (β(1 - β)) dβ < 0.363084`, the same
integral as Yamada's `c₂` without the `10⁻⁸`. Section 9 says the method cannot reach
`N ≥ exp(exp 22)` because
`𝓕(X₂, δ) = 2 log 3 - (1 + ε₁(X₂, δ)) log 6 - (1 + ε₂(X₂^{1/8}, δ)) c̄`
has `𝓕(exp(exp 22), 2) < 0`, with `ε_i(X, δ) = 1/(p̄ - 2)` from Lemma 41, (121):
`p̄` the largest prime with `log^δ x_i(X) ≥ ∏_{2<p≤p̄} p`, `x₁(N) = N / log⁵ N` and
`x₂(Y) = Y / log¹⁵ Y`, (75).

Here: `cbar_lt`, the printed `c̄ < 0.363084`, PROVED; `cbar_gt`, a lower bound; the
primorial brackets that give `p̄ = 47` and `p̄ = 43` at `X₂ = exp(exp 22)`, `δ = 2`; and
`F_neg`, the printed `𝓕(exp(exp 22), 2) < 0`, PROVED.
-/

@[expose] public section

open Finset Real intervalIntegral

noncomputable section
namespace LeanLab.ChenExplicit.BJS

open LeanLab.ChenExplicit.Yamada

/-- `c̄`, Lemma 52. -/
def cbar : ℝ := ∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))

/-- The series bound of C2Bound.lean, the integral of `g1 n β + g2 n (1 - β)`. -/
def R (n : ℕ) : ℝ :=
  (log 2 * log ((1 / 3) / (1 / 8)) - ∑ k ∈ range n, (3 / 2 : ℝ) ^ (k + 1) / (k + 1) *
      (((1 / 3 : ℝ) ^ (k + 1) - (1 / 8) ^ (k + 1)) / (k + 1))) +
  (log 3 * log ((7 / 8) / (2 / 3)) + (log (7 / 8) ^ 2 / 2 - log (2 / 3) ^ 2 / 2) -
    ∑ k ∈ range n, (1 / 3 : ℝ) ^ (k + 1) / (k + 1) *
      (((3 / 2 : ℝ) ^ (k + 1) - (8 / 7) ^ (k + 1)) / (k + 1)))

lemma log_bounds_setup :
    log ((1 / 3 : ℝ) / (1 / 8)) = 3 * log 2 - log 3 ∧
    log ((7 / 8 : ℝ) / (2 / 3)) = log (7 / 8) - (log 2 - log 3) ∧
    log ((2 : ℝ) / 3) = log 2 - log 3 := by
  have e23 : log ((2 : ℝ) / 3) = log 2 - log 3 := Real.log_div (by norm_num) (by norm_num)
  refine ⟨?_, ?_, e23⟩
  · rw [show (1 / 3 : ℝ) / (1 / 8) = 2 ^ 3 / 3 by norm_num, Real.log_div (by norm_num)
      (by norm_num), Real.log_pow]; push_cast; ring
  · rw [Real.log_div (by norm_num) (by norm_num), e23]

/-- **Lemma 52, the printed bound, PROVED: `c̄ < 0.363084`.** Margin about `2.6 · 10⁻⁷`;
our quadrature gives `c̄ = 0.36308372925`. -/
theorem cbar_lt : cbar < 363084 / 1000000 := by
  unfold cbar
  have h := c2_integral_le 20
  have l2a := log_two_gt_d9
  have l2b := log_two_lt_d9
  have l3a := log_three_gt_d9
  have l3b := log_three_lt_d9
  have l7 := log_seven_eighths
  rw [abs_le] at l7
  obtain ⟨l7a, l7b⟩ := l7
  obtain ⟨e1, e2, e23⟩ := log_bounds_setup
  rw [e1, e2, e23] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  norm_num at l2a l2b l3a l3b
  set a := log 2
  set b := log 3
  set c := log (7 / 8)
  have hc1 : c ^ 2 ≤ (133531392634 / 1000000000000 : ℝ) ^ 2 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos
      (by linarith : (0 : ℝ) ≤ c + 133531392634 / 1000000000000)
      (by linarith : c - 133531392634 / 1000000000000 ≤ 0)]
  have hd : (40546510 / 100000000 : ℝ) ^ 2 ≤ (a - b) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -(a - b) - 40546510 / 100000000)
      (by linarith : (0 : ℝ) ≤ -(a - b) + 40546510 / 100000000)]
  have hab : a * (3 * a - b) ≤ 6931471808 / 10000000000 * (3 * (6931471808 / 10000000000) -
      10986122885 / 10000000000) := by nlinarith
  have hbc : b * (c - (a - b)) ≤ 10986122888 / 10000000000 *
      (-133531392614 / 1000000000000 - (6931471803 / 10000000000 - 10986122888 / 10000000000)) := by
    nlinarith
  linarith

/-! ### A lower bound for `c̄` -/

/-- `log(1 - x) ≥ -∑_{k<n} x^{k+1}/(k+1) - (1/2)^n` for `0 ≤ x ≤ 1/2`. -/
lemma log_one_sub_ge (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) (n : ℕ) :
    -∑ k ∈ range n, x ^ (k + 1) / (k + 1) - (1 / 2) ^ n ≤ log (1 - x) := by
  have hx : |x| = x := abs_of_nonneg h0
  have z := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [hx]; linarith) n
  rw [hx] at z
  have hb : x ^ (n + 1) / (1 - x) ≤ (1 / 2) ^ n := by
    rw [div_le_iff₀ (by linarith)]
    have hp : x ^ n ≤ (1 / 2) ^ n := pow_le_pow_left₀ h0 h1 n
    have hxn : 0 ≤ x ^ n := pow_nonneg h0 n
    rw [pow_succ]
    nlinarith
  have hs : ∑ i ∈ range n, x ^ (i + 1) / (i + 1) = ∑ k ∈ range n, x ^ (k + 1) / (k + 1) := rfl
  rw [abs_le] at z
  linarith [z.1, z.2]

lemma f1_ge (n : ℕ) (β : ℝ) (h0 : 0 < β) (h1 : β ≤ 1 / 3) :
    g1 n β - (1 / 2) ^ n * β⁻¹ ≤ log (2 - 3 * β) / β := by
  have e : 2 - 3 * β = 2 * (1 - 3 * β / 2) := by ring
  rw [e, Real.log_mul (by norm_num) (by linarith)]
  have hl := log_one_sub_ge (3 * β / 2) (by positivity) (by linarith) n
  unfold g1
  rw [le_div_iff₀ h0, sub_mul, sub_mul, Finset.sum_mul]
  have : ∑ k ∈ range n, (3 / 2 : ℝ) ^ (k + 1) / (k + 1) * β ^ k * β =
      ∑ k ∈ range n, (3 * β / 2) ^ (k + 1) / (k + 1) := by
    apply Finset.sum_congr rfl; intro k _
    rw [show 3 * β / 2 = 3 / 2 * β by ring, mul_pow, pow_succ β k]; ring
  rw [this, mul_assoc, inv_mul_cancel₀ h0.ne', mul_assoc, inv_mul_cancel₀ h0.ne']
  linarith

lemma f2_ge (n : ℕ) (u : ℝ) (h0 : 2 / 3 ≤ u) :
    g2 n u - (1 / 2) ^ n * u⁻¹ ≤ log (3 * u - 1) / u := by
  have hu : 0 < u := by linarith
  have e : 3 * u - 1 = 3 * u * (1 - (3 * u)⁻¹) := by field_simp
  have hx0 : 0 ≤ (3 * u)⁻¹ := by positivity
  have hx1 : (3 * u)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have hx1' : (3 * u)⁻¹ < 1 := by linarith
  rw [e, Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) hu.ne']
  have hl := log_one_sub_ge ((3 * u)⁻¹) hx0 hx1 n
  have : ∑ k ∈ range n, (1 / 3 : ℝ) ^ (k + 1) / (k + 1) * u⁻¹ ^ (k + 2) =
      (∑ k ∈ range n, (3 * u)⁻¹ ^ (k + 1) / (k + 1)) * u⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _
    rw [mul_inv, mul_pow, pow_succ u⁻¹ (k + 1)]; ring
  unfold g2
  rw [this, div_eq_mul_inv _ u]
  have hui : 0 < u⁻¹ := inv_pos.mpr hu
  nlinarith

lemma f_ge (n : ℕ) (β : ℝ) (h0 : 1 / 8 ≤ β) (h1 : β ≤ 1 / 3) :
    g1 n β + g2 n (1 - β) - (1 / 2) ^ n * (β⁻¹ + (1 - β)⁻¹) ≤
      log (2 - 3 * β) / (β * (1 - β)) := by
  have hb : 0 < β := by linarith
  have hb1 : 0 < 1 - β := by linarith
  have e : log (2 - 3 * β) / (β * (1 - β)) =
      log (2 - 3 * β) / β + log (3 * (1 - β) - 1) / (1 - β) := by
    rw [show 3 * (1 - β) - 1 = 2 - 3 * β by ring]
    field_simp
    ring
  rw [e]
  have := f1_ge n β hb h1
  have := f2_ge n (1 - β) (by linarith)
  linarith

/-- The integral of the lower function. -/
theorem cbar_ge_R (n : ℕ) :
    R n - (1 / 2) ^ n * (log ((1 / 3) / (1 / 8)) + log ((7 / 8) / (2 / 3))) ≤ cbar := by
  have hne : ∀ x ∈ Set.uIcc (1 / 8 : ℝ) (1 / 3), x ≠ 0 ∧ 1 - x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    constructor <;> linarith [hx.1, hx.2]
  have hg2 : IntervalIntegrable (fun β : ℝ => g2 n (1 - β)) MeasureTheory.volume (1 / 8) (1 / 3) := by
    have := (g2_cont n).intervalIntegrable (μ := MeasureTheory.volume)
    have h := this.comp_sub_left 1
    norm_num at h ⊢
    exact h.symm
  have hinv1 : IntervalIntegrable (fun β : ℝ => β⁻¹) MeasureTheory.volume (1 / 8) (1 / 3) :=
    ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun x hx => (hne x hx).1)
  have hinv2 : IntervalIntegrable (fun β : ℝ => (1 - β)⁻¹) MeasureTheory.volume (1 / 8) (1 / 3) :=
    ContinuousOn.intervalIntegrable ((continuousOn_inv₀.comp (by fun_prop :
      ContinuousOn (fun β : ℝ => 1 - β) _) (fun x hx => (hne x hx).2)))
  have hcorr : IntervalIntegrable (fun β : ℝ => (1 / 2 : ℝ) ^ n * (β⁻¹ + (1 - β)⁻¹))
      MeasureTheory.volume (1 / 8) (1 / 3) := (hinv1.add hinv2).const_mul _
  have hlow : IntervalIntegrable (fun β : ℝ => g1 n β + g2 n (1 - β) -
      (1 / 2) ^ n * (β⁻¹ + (1 - β)⁻¹)) MeasureTheory.volume (1 / 8) (1 / 3) :=
    (((g1_cont n).intervalIntegrable).add hg2).sub hcorr
  have hmono := integral_mono_on (μ := MeasureTheory.volume) (a := (1 / 8 : ℝ)) (b := 1 / 3)
    (by norm_num) hlow (f_cont.intervalIntegrable)
    (fun β hβ => f_ge n β hβ.1 hβ.2)
  rw [integral_sub (((g1_cont n).intervalIntegrable).add hg2) hcorr,
    integral_add ((g1_cont n).intervalIntegrable) hg2, integral_g1,
    integral_comp_sub_left (fun u => g2 n u) 1, integral_const_mul,
    integral_add hinv1 hinv2, integral_inv_of_pos (by norm_num) (by norm_num),
    integral_comp_sub_left (fun u => u⁻¹) 1] at hmono
  norm_num at hmono
  rw [integral_g2] at hmono
  unfold cbar R
  norm_num at hmono ⊢
  linarith

/-- **A lower bound: `c̄ > 0.3630`.** -/
theorem cbar_gt : 3630 / 10000 < cbar := by
  have h := cbar_ge_R 20
  unfold R at h
  have l2a := log_two_gt_d9
  have l2b := log_two_lt_d9
  have l3a := log_three_gt_d9
  have l3b := log_three_lt_d9
  have l7 := log_seven_eighths
  rw [abs_le] at l7
  obtain ⟨l7a, l7b⟩ := l7
  obtain ⟨e1, e2, e23⟩ := log_bounds_setup
  rw [e1, e2, e23] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  norm_num at l2a l2b l3a l3b
  set a := log 2
  set b := log 3
  set c := log (7 / 8)
  have hc1 : (133531392614 / 1000000000000 : ℝ) ^ 2 ≤ c ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -c - 133531392614 / 1000000000000)
      (by linarith : (0 : ℝ) ≤ -c + 133531392614 / 1000000000000)]
  have hd : (a - b) ^ 2 ≤ (40546511 / 100000000 : ℝ) ^ 2 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos
      (by linarith : (0 : ℝ) ≤ -(a - b) + 40546511 / 100000000)
      (by linarith : -(a - b) - 40546511 / 100000000 ≤ 0)]
  have hab : 6931471803 / 10000000000 * (3 * (6931471803 / 10000000000) -
      10986122888 / 10000000000) ≤ a * (3 * a - b) := by nlinarith
  have hbc : 10986122885 / 10000000000 *
      (-133531392634 / 1000000000000 - (6931471808 / 10000000000 - 10986122885 / 10000000000))
      ≤ b * (c - (a - b)) := by
    nlinarith
  nlinarith

/-! ### `𝓕(exp(exp 22), 2) < 0`, Section 9 -/

/-- The product of the odd primes up to `p`. -/
def oddPrimorial (p : ℕ) : ℕ := ∏ q ∈ (range (p + 1)).filter (fun q => q.Prime ∧ 2 < q), q

theorem oddPrimorial_43 : oddPrimorial 43 = 6541380665835015 := by
  unfold oddPrimorial; decide

theorem oddPrimorial_47 : oddPrimorial 47 = 307444891294245705 := by
  unfold oddPrimorial; decide

theorem oddPrimorial_53 : oddPrimorial 53 = 16294579238595022365 := by
  unfold oddPrimorial; decide

theorem nextprime_47 : ∀ q ∈ Finset.Ioo 47 53, ¬ Nat.Prime q := by decide

theorem nextprime_43 : ∀ q ∈ Finset.Ioo 43 47, ¬ Nat.Prime q := by decide

/-- `e^22` between `3584912840` and `3584912851`. -/
theorem exp22_bounds : 3584912840 < exp 22 ∧ exp 22 < 3584912851 := by
  have he : exp 22 = exp 1 ^ 22 := by rw [← Real.exp_nat_mul]; norm_num
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  rw [he]
  constructor
  · calc (3584912840 : ℝ) < 2.7182818283 ^ 22 := by norm_num
      _ < exp 1 ^ 22 := by gcongr
  · calc exp 1 ^ 22 < 2.7182818286 ^ 22 := by gcongr
      _ < 3584912851 := by norm_num

/-- `x₁(X₂)` at `X₂ = exp(exp 22)`: `log x₁ = e^22 - 5 · 22`. With `δ = 2`, the odd
primorials bracket `log² x₁` between `p = 47` and the next prime `53`, so `p̄ = 47` and
`ε₁ = 1/45`. -/
theorem pbar1 : (oddPrimorial 47 : ℝ) ≤ (exp 22 - 5 * 22) ^ 2 ∧
    (exp 22 - 5 * 22) ^ 2 < (oddPrimorial 53 : ℝ) := by
  rw [oddPrimorial_47, oddPrimorial_53]
  obtain ⟨h1, h2⟩ := exp22_bounds
  constructor <;> push_cast <;> nlinarith

/-- `x₂(X₂^{1/8})`: `log Y = e^22/8`, `log x₂ = e^22/8 - 15 log(e^22/8)
= e^22/8 - 15 (22 - 3 log 2)`. Its square lies between the odd primorials of 43 and 47,
so `p̄ = 43` and `ε₂ = 1/41`. -/
theorem pbar2 : (oddPrimorial 43 : ℝ) ≤ (exp 22 / 8 - 15 * (22 - 3 * log 2)) ^ 2 ∧
    (exp 22 / 8 - 15 * (22 - 3 * log 2)) ^ 2 < (oddPrimorial 47 : ℝ) := by
  rw [oddPrimorial_43, oddPrimorial_47]
  obtain ⟨h1, h2⟩ := exp22_bounds
  have l2a := log_two_gt_d9
  have l2b := log_two_lt_d9
  constructor <;> push_cast <;> nlinarith

/-- **Section 9, PROVED: `𝓕(exp(exp 22), 2) < 0`**, with `ε₁ = 1/(47 - 2)` and
`ε₂ = 1/(43 - 2)` from `pbar1` and `pbar2`, and `c̄` from Lemma 52. -/
theorem F_neg : 2 * log 3 - (1 + 1 / (47 - 2)) * log 6 - (1 + 1 / (43 - 2)) * cbar < 0 := by
  have hc := cbar_gt
  have h6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have l2a := log_two_gt_d9
  have l3b := log_three_lt_d9
  rw [h6]
  norm_num at l2a l3b ⊢
  nlinarith

end LeanLab.ChenExplicit.BJS
