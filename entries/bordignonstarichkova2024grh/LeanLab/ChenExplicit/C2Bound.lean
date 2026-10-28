module

public import LeanLab.ChenExplicit.Yamada

/-!
AI-written Lean code, Claude, 2026-10-17, run 20261017T2104Z-19452, unit U-0372.
P0010 T. Yamada, Explicit Chen's theorem, arXiv 1511.03409v2, Lemma 7.3, numerical part:
`c₂ = ∫_{1/8}^{1/3} log(2 - 3β) / (β(1 - β)) dβ + 10⁻⁸ < 0.36309`.

Method. Split `1/(β(1-β)) = 1/β + 1/(1-β)`. In the first part write
`log(2 - 3β) = log 2 + log(1 - 3β/2)`, in the second substitute `u = 1 - β` and write
`log(3u - 1) = log 3 + log u + log(1 - 1/(3u))`. Since `log(1 - x) ≤ -∑_{k<n} x^{k+1}/(k+1)`
for `0 ≤ x < 1`, each integrand is below an explicit function we integrate exactly, with
`n = 20` terms. The bound obtained is about `0.3630837`, margin about `6 · 10⁻⁶`.
-/

@[expose] public section

open Finset Real intervalIntegral

noncomputable section
namespace LeanLab.ChenExplicit.Yamada

/-- `log(1 - x) ≤ -∑_{k<n} x^{k+1}/(k+1)` for `0 ≤ x < 1`. -/
lemma log_one_sub_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    log (1 - x) ≤ -∑ k ∈ range n, x ^ (k + 1) / (k + 1) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  have := sum_le_hasSum (range n) (fun i _ => by positivity) hs
  linarith

/-- The upper function for the first part. -/
def g1 (n : ℕ) (β : ℝ) : ℝ :=
  log 2 * β⁻¹ - ∑ k ∈ range n, (3 / 2 : ℝ) ^ (k + 1) / (k + 1) * β ^ k

lemma f1_le (n : ℕ) (β : ℝ) (h0 : 0 < β) (h1 : β ≤ 1 / 3) :
    log (2 - 3 * β) / β ≤ g1 n β := by
  have e : 2 - 3 * β = 2 * (1 - 3 * β / 2) := by ring
  rw [e, Real.log_mul (by norm_num) (by linarith)]
  have hl := log_one_sub_le (3 * β / 2) (by positivity) (by linarith) n
  unfold g1
  rw [div_le_iff₀ h0, sub_mul, Finset.sum_mul]
  have : ∑ k ∈ range n, (3 / 2 : ℝ) ^ (k + 1) / (k + 1) * β ^ k * β =
      ∑ k ∈ range n, (3 * β / 2) ^ (k + 1) / (k + 1) := by
    apply Finset.sum_congr rfl; intro k _
    rw [show 3 * β / 2 = 3 / 2 * β by ring, mul_pow, pow_succ β k]; ring
  rw [this, mul_assoc, inv_mul_cancel₀ h0.ne']
  linarith

lemma g1_cont (n : ℕ) : ContinuousOn (g1 n) (Set.uIcc (1 / 8 : ℝ) (1 / 3)) := by
  unfold g1
  apply ContinuousOn.sub
  · apply ContinuousOn.mul continuousOn_const
    apply continuousOn_inv₀.mono
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [hx.1]
  · exact (continuous_finsetSum _ fun k _ => by fun_prop).continuousOn

lemma integral_g1 (n : ℕ) : ∫ β in (1 / 8 : ℝ)..(1 / 3), g1 n β =
    log 2 * log ((1 / 3) / (1 / 8)) - ∑ k ∈ range n, (3 / 2 : ℝ) ^ (k + 1) / (k + 1) *
      (((1 / 3 : ℝ) ^ (k + 1) - (1 / 8) ^ (k + 1)) / (k + 1)) := by
  unfold g1
  rw [integral_sub, integral_const_mul, integral_inv_of_pos (by norm_num) (by norm_num),
    integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, integral_pow]
  · intro k _
    exact (by fun_prop : Continuous fun β : ℝ => (3 / 2 : ℝ) ^ (k + 1) / (k + 1) * β ^ k)
      |>.intervalIntegrable _ _
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply continuousOn_inv₀.mono
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [hx.1]
  · exact (continuous_finsetSum _ fun k _ => by fun_prop).intervalIntegrable _ _

/-- The upper function for the second part, in `u = 1 - β`. -/
def g2 (n : ℕ) (u : ℝ) : ℝ :=
  log 3 * u⁻¹ + log u * u⁻¹ - ∑ k ∈ range n, (1 / 3 : ℝ) ^ (k + 1) / (k + 1) * u⁻¹ ^ (k + 2)

lemma f2_le (n : ℕ) (u : ℝ) (h0 : 1 / 2 < u) :
    log (3 * u - 1) / u ≤ g2 n u := by
  have hu : 0 < u := by linarith
  have e : 3 * u - 1 = 3 * u * (1 - (3 * u)⁻¹) := by field_simp
  have hx0 : 0 ≤ (3 * u)⁻¹ := by positivity
  have hx1 : (3 * u)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  rw [e, Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) hu.ne']
  have hl := log_one_sub_le ((3 * u)⁻¹) hx0 hx1 n
  unfold g2
  rw [div_eq_mul_inv]
  have : ∑ k ∈ range n, (1 / 3 : ℝ) ^ (k + 1) / (k + 1) * u⁻¹ ^ (k + 2) =
      (∑ k ∈ range n, (3 * u)⁻¹ ^ (k + 1) / (k + 1)) * u⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _
    rw [mul_inv, mul_pow, pow_succ u⁻¹ (k + 1)]; ring
  rw [this]
  have hui : 0 < u⁻¹ := inv_pos.mpr hu
  nlinarith

lemma g2_cont (n : ℕ) : ContinuousOn (g2 n) (Set.uIcc (2 / 3 : ℝ) (7 / 8)) := by
  have hne : ∀ x ∈ Set.uIcc (2 / 3 : ℝ) (7 / 8), x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
  unfold g2
  apply ContinuousOn.sub
  · apply ContinuousOn.add
    · exact continuousOn_const.mul (continuousOn_inv₀.mono fun x hx => hne x hx)
    · exact (continuousOn_log.mono fun x hx => hne x hx).mul
        (continuousOn_inv₀.mono fun x hx => hne x hx)
  · apply continuousOn_finsetSum
    intro k _
    exact continuousOn_const.mul ((continuousOn_inv₀.mono fun x hx => hne x hx).pow _)

lemma integral_log_mul_inv : ∫ u in (2 / 3 : ℝ)..(7 / 8), log u * u⁻¹ =
    log (7 / 8) ^ 2 / 2 - log (2 / 3) ^ 2 / 2 := by
  have hpos : ∀ x ∈ Set.uIcc (2 / 3 : ℝ) (7 / 8), 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
  rw [integral_eq_sub_of_hasDerivAt (f := fun u => log u ^ 2 / 2)]
  · intro x hx
    have h := (Real.hasDerivAt_log (hpos x hx).ne').pow 2
    convert h.div_const 2 using 1
    push_cast; ring
  · apply ContinuousOn.intervalIntegrable
    exact (continuousOn_log.mono fun x hx => (hpos x hx).ne').mul
      (continuousOn_inv₀.mono fun x hx => (hpos x hx).ne')

lemma integral_inv_pow (k : ℕ) : ∫ u in (2 / 3 : ℝ)..(7 / 8), u⁻¹ ^ (k + 2) =
    ((3 / 2 : ℝ) ^ (k + 1) - (8 / 7) ^ (k + 1)) / (k + 1) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc (2 / 3 : ℝ) (7 / 8) := by
    rw [Set.uIcc_of_le (by norm_num)]; simp only [Set.mem_Icc, not_and, not_le]
    intro h; linarith
  have e : (fun u : ℝ => u⁻¹ ^ (k + 2)) = fun u => u ^ (-((k : ℤ) + 2)) := by
    funext u
    rw [inv_pow, zpow_neg, show ((k : ℤ) + 2) = ((k + 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
  rw [e, integral_zpow (Or.inr ⟨by omega, h0⟩)]
  have e2 : -((k : ℤ) + 2) + 1 = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
  have e3 : ∀ x : ℝ, x ^ (-((k : ℤ) + 2) + 1) = (x⁻¹) ^ (k + 1) := by
    intro x; rw [e2, zpow_neg, zpow_natCast, inv_pow]
  have e4 : (((-((k : ℤ) + 2) : ℤ) : ℝ) + 1) = -((k : ℝ) + 1) := by push_cast; ring
  rw [e3, e3, e4, show (7 / 8 : ℝ)⁻¹ = 8 / 7 by norm_num, show (2 / 3 : ℝ)⁻¹ = 3 / 2 by norm_num,
    div_neg, ← neg_div, neg_sub]

lemma integral_g2 (n : ℕ) : ∫ u in (2 / 3 : ℝ)..(7 / 8), g2 n u =
    log 3 * log ((7 / 8) / (2 / 3)) + (log (7 / 8) ^ 2 / 2 - log (2 / 3) ^ 2 / 2) -
      ∑ k ∈ range n, (1 / 3 : ℝ) ^ (k + 1) / (k + 1) *
        (((3 / 2 : ℝ) ^ (k + 1) - (8 / 7) ^ (k + 1)) / (k + 1)) := by
  have hne : ∀ x ∈ Set.uIcc (2 / 3 : ℝ) (7 / 8), x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
  have hi1 : IntervalIntegrable (fun u : ℝ => log 3 * u⁻¹) MeasureTheory.volume (2 / 3) (7 / 8) :=
    ContinuousOn.intervalIntegrable (continuousOn_const.mul
      (continuousOn_inv₀.mono fun x hx => hne x hx))
  have hi2 : IntervalIntegrable (fun u : ℝ => log u * u⁻¹) MeasureTheory.volume (2 / 3) (7 / 8) :=
    ContinuousOn.intervalIntegrable ((continuousOn_log.mono fun x hx => hne x hx).mul
      (continuousOn_inv₀.mono fun x hx => hne x hx))
  have hi3 : ∀ k ∈ range n, IntervalIntegrable
      (fun u : ℝ => (1 / 3 : ℝ) ^ (k + 1) / (k + 1) * u⁻¹ ^ (k + 2)) MeasureTheory.volume
      (2 / 3) (7 / 8) := fun k _ =>
    ContinuousOn.intervalIntegrable (continuousOn_const.mul
      ((continuousOn_inv₀.mono fun x hx => hne x hx).pow _))
  have hi4 : IntervalIntegrable (fun u : ℝ => ∑ k ∈ range n, (1 / 3 : ℝ) ^ (k + 1) / (k + 1) *
      u⁻¹ ^ (k + 2)) MeasureTheory.volume (2 / 3) (7 / 8) :=
    ContinuousOn.intervalIntegrable (continuousOn_finsetSum _ fun k _ => continuousOn_const.mul
      ((continuousOn_inv₀.mono fun x hx => hne x hx).pow _))
  unfold g2
  rw [integral_sub (hi1.add hi2) hi4, integral_add hi1 hi2,
    integral_const_mul, integral_inv_of_pos (by norm_num) (by norm_num), integral_log_mul_inv,
    integral_finsetSum hi3]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul, integral_inv_pow]

/-- The integrand of `c₂` is below `g1 n β + g2 n (1 - β)` on `[1/8, 1/3]`. -/
lemma f_le (n : ℕ) (β : ℝ) (h0 : 1 / 8 ≤ β) (h1 : β ≤ 1 / 3) :
    log (2 - 3 * β) / (β * (1 - β)) ≤ g1 n β + g2 n (1 - β) := by
  have hb : 0 < β := by linarith
  have hb1 : 0 < 1 - β := by linarith
  have e : log (2 - 3 * β) / (β * (1 - β)) =
      log (2 - 3 * β) / β + log (3 * (1 - β) - 1) / (1 - β) := by
    rw [show 3 * (1 - β) - 1 = 2 - 3 * β by ring]
    field_simp
    ring
  rw [e]
  exact add_le_add (f1_le n β hb h1) (f2_le n (1 - β) (by linarith))

lemma f_cont : ContinuousOn (fun β : ℝ => log (2 - 3 * β) / (β * (1 - β)))
    (Set.uIcc (1 / 8 : ℝ) (1 / 3)) := by
  have hI : ∀ x ∈ Set.uIcc (1 / 8 : ℝ) (1 / 3), 1 / 8 ≤ x ∧ x ≤ 1 / 3 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact hx
  apply ContinuousOn.div
  · apply ContinuousOn.log (by fun_prop)
    intro x hx; have := hI x hx; linarith
  · fun_prop
  · intro x hx
    have := hI x hx
    have : 0 < x * (1 - x) := by apply mul_pos <;> linarith
    exact this.ne'

/-- The integral of `c₂` is below the explicit series bound with `n` terms. -/
theorem c2_integral_le (n : ℕ) :
    (∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) ≤
      (log 2 * log ((1 / 3) / (1 / 8)) - ∑ k ∈ range n, (3 / 2 : ℝ) ^ (k + 1) / (k + 1) *
          (((1 / 3 : ℝ) ^ (k + 1) - (1 / 8) ^ (k + 1)) / (k + 1))) +
      (log 3 * log ((7 / 8) / (2 / 3)) + (log (7 / 8) ^ 2 / 2 - log (2 / 3) ^ 2 / 2) -
        ∑ k ∈ range n, (1 / 3 : ℝ) ^ (k + 1) / (k + 1) *
          (((3 / 2 : ℝ) ^ (k + 1) - (8 / 7) ^ (k + 1)) / (k + 1))) := by
  have hg2 : IntervalIntegrable (fun β : ℝ => g2 n (1 - β)) MeasureTheory.volume (1 / 8) (1 / 3) := by
    have := (g2_cont n).intervalIntegrable (μ := MeasureTheory.volume)
    have h := this.comp_sub_left 1
    norm_num at h ⊢
    exact h.symm
  have hmono := integral_mono_on (μ := MeasureTheory.volume) (a := (1 / 8 : ℝ)) (b := 1 / 3)
    (by norm_num) (f_cont.intervalIntegrable) (((g1_cont n).intervalIntegrable).add hg2)
    (fun β hβ => f_le n β hβ.1 hβ.2)
  rw [integral_add ((g1_cont n).intervalIntegrable) hg2, integral_g1,
    integral_comp_sub_left (fun u => g2 n u) 1] at hmono
  norm_num at hmono
  rw [integral_g2] at hmono
  norm_num at hmono ⊢
  linarith

/-! ### Logarithm bounds -/

lemma log_seven_eighths : |log (7 / 8) + 133531392624 / 1000000000000| ≤ 1 / 10 ^ 11 := by
  have t : |(1 / 8 : ℝ)| = 1 / 8 := by norm_num
  have z := abs_log_sub_add_sum_range_le (x := 1 / 8) (by rw [t]; norm_num) 14
  rw [t, show (1 - (1 : ℝ) / 8) = 7 / 8 by norm_num] at z
  have hs : ∑ i ∈ range 14, (1 / 8 : ℝ) ^ (i + 1) / (i + 1) =
      ∑ i ∈ range 14, (1 / 8 : ℝ) ^ (i + 1) / (i + 1) := rfl
  rw [abs_le] at z ⊢
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at z
  norm_num at z
  constructor <;> linarith [z.1, z.2]

/-- **Lemma 7.3, numerical part, PROVED: `c₂ < 0.36309`.** -/
theorem c2Bound : C2Bound := by
  unfold C2Bound c2
  have h := c2_integral_le 20
  have l2a := log_two_gt_d9
  have l2b := log_two_lt_d9
  have l3a := log_three_gt_d9
  have l3b := log_three_lt_d9
  have l7 := log_seven_eighths
  rw [abs_le] at l7
  obtain ⟨l7a, l7b⟩ := l7
  have e1 : log ((1 / 3 : ℝ) / (1 / 8)) = 3 * log 2 - log 3 := by
    rw [show (1 / 3 : ℝ) / (1 / 8) = 2 ^ 3 / 3 by norm_num, Real.log_div (by norm_num)
      (by norm_num), Real.log_pow]; push_cast; ring
  have e23 : log ((2 : ℝ) / 3) = log 2 - log 3 := Real.log_div (by norm_num) (by norm_num)
  have e2 : log ((7 / 8 : ℝ) / (2 / 3)) = log (7 / 8) - (log 2 - log 3) := by
    rw [Real.log_div (by norm_num) (by norm_num), e23]
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

/-- **Yamada Theorem 1.1 from the sieve theorems alone.** CONDITIONAL ON (48) and Theorems
5.1, 6.1, 7.1; the numerical input `c₂ < 0.36309` is now PROVED. -/
theorem yamada_of_sieve (h48 : Thm48) (h51 : Thm51) (h61 : Thm61) (h71 : Thm71) : Yamada :=
  yamada_of_section8 h48 h51 h61 h71 c2Bound

end LeanLab.ChenExplicit.Yamada
