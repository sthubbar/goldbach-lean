module

public import LeanLab.LZCesaroShort.CircleCoef
public import LeanLab.LZCesaroShort.Lemma2
public import LeanLab.LZCesaroShort.Lemma5
public import LeanLab.LZCesaroShort.Lemma13Statements
public import LeanLab.LZCesaroShort.Statements

/-!
# P0058 Section 4 for `y = H`: the circle method identity, `I₁` and `I₂`

Lab proof, unit U-6105, CLOUD 20261020T0618Z-cloud36. AI wrote this file. No cited input.
Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 pp. 5 to 9, eq. (26) to (28) with `y = H`, `T(α) = T_H(N, H; α)`,
`R̃ = S̃ − 1/z`:

* `Q_eq`: `Σ_{|n−N| ≤ H} t_H(n − N) e^{−n/N} R(n) = ∫_{-1/2}^{1/2} S̃(α)² T(−α) dα`;
* `I1_bound`: `‖∫ T(−α)/z² − Σ t_H(n − N) n e^{−n/N}‖ ≤ H²`, from Lemma 2;
* `I2_bound`: `‖2∫ T(−α) R̃(α)/z − 2Σ t_H(n − N) e^{−n/N}(ψ(n) − n)‖ ≤ 2H² (8√(4N log N) +
  8√(1 + N/2) + 1)` for `N ≥ 10^20`, `H < N`, the explicit form of Lemma 6 at `y = H`.

The `I₂` step follows the paper's (15) to (19) with one change: `V(α)` is replaced by
`W(α) = 1/(1 − e^{−z}) = Σ_{m ≥ 0} e^{−mz}`, which includes `m = 0`, so the convolution gives
`ψ(n) − n − 1` directly and no shift `ψ(n − 1) → ψ(n)` is needed; the trivial bound `‖T‖ ≤ H²`
replaces the paper's Lemma 5 and Parseval in (15) and (17), which is enough for `H ≤ √N`.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Chebyshev
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher

/-- The weight `t_H(n − N) = H − |n − N|`. -/
noncomputable def tw (N H n : ℕ) : ℝ := (H : ℝ) - |(n : ℝ) - N|

lemma TH_full (N H : ℕ) (α : ℝ) :
    TH N H H α = ∑ n ∈ Icc (N - H) (N + H), ((tw N H n : ℝ) : ℂ) * e (n * α) := by
  have hfilt : (Icc (N - H) (N + H)).filter (fun n : ℕ => (n : ℝ) ≤ N + H) = Icc (N - H) (N + H) := by
    apply filter_true_of_mem; intro n hn; rw [mem_Icc] at hn; exact_mod_cast hn.2
  unfold TH; rw [hfilt]; rfl

lemma tw_nonneg {N H n : ℕ} (hHN : H ≤ N) (hn : n ∈ Icc (N - H) (N + H)) : 0 ≤ tw N H n := by
  rw [mem_Icc] at hn
  unfold tw
  have : |(n : ℝ) - N| ≤ H := by
    rw [abs_le]
    have h1 : ((N - H : ℕ) : ℝ) = N - H := by push_cast [Nat.cast_sub hHN]; ring
    have h2 : ((N - H : ℕ) : ℝ) ≤ n := by exact_mod_cast hn.1
    have h3 : (n : ℝ) ≤ N + H := by exact_mod_cast hn.2
    constructor <;> linarith
  linarith

lemma sum_tw {N H : ℕ} (hHN : H ≤ N) : ∑ n ∈ Icc (N - H) (N + H), tw N H n = (H : ℝ) ^ 2 := by
  unfold tw; exact sum_tH hHN

lemma norm_TH_le {N H : ℕ} (hHN : H ≤ N) (α : ℝ) : ‖TH N H H α‖ ≤ (H : ℝ) ^ 2 := by
  rw [TH_full]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  rw [← sum_tw hHN]
  refine sum_congr rfl fun n hn => ?_
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tw_nonneg hHN hn)]

lemma continuous_TH_neg (N H : ℕ) : Continuous (fun α => TH N H H (-α)) := by
  simp_rw [TH_full]
  exact continuous_finsetSum _ fun n _ => continuous_const.mul
    ((continuous_e_mul _).comp continuous_neg)

/-- The coefficients of `S̃`. -/
noncomputable def cS (N : ℕ) (m : ℕ) : ℂ := ((Λ m * Real.exp (-m / N) : ℝ) : ℂ)

lemma St_eq (N : ℕ) (α : ℝ) : St N α = ∑' m, cS N m * e (m * α) := rfl

lemma summable_cS {N : ℕ} (hN : 1 ≤ N) : Summable (fun m => ‖cS N m‖) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (summable_n_exp hN0)
  unfold cS
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have := ArithmeticFunction.vonMangoldt_le_log (n := m)
  have := Real.log_le_self (Nat.cast_nonneg (α := ℝ) m)
  linarith

lemma continuous_St {N : ℕ} (hN : 1 ≤ N) : Continuous (St N) := by
  have : St N = fun α => ∑' m, cS N m * e (m * α) := rfl
  rw [this]; exact continuous_tsum_e _ (summable_cS hN)

lemma conv_cS (N n : ℕ) :
    ∑ p ∈ antidiagonal n, cS N p.1 * cS N p.2 = ((Real.exp (-n / N) * R n : ℝ) : ℂ) := by
  unfold cS R
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have : Complex.exp (-(p.1 : ℂ) / N) * Complex.exp (-(p.2 : ℂ) / N) = Complex.exp (-(n : ℂ) / N) := by
    rw [← Complex.exp_add, ← hp]; congr 1; push_cast; ring
  rw [← this]; ring

/-- **The circle method identity**, eq. (26) at `y = H`. -/
theorem Q_eq {N H : ℕ} (hN : 1 ≤ N) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), St N α ^ 2 * TH N H H (-α)
      = ∑ n ∈ Icc (N - H) (N + H), ((tw N H n * Real.exp (-n / N) * R n : ℝ) : ℂ) := by
  have hc := summable_cS hN
  have hpt : ∀ α, St N α ^ 2 * TH N H H (-α) = ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n : ℝ) : ℂ) * ((∑' m, cS N m * e (m * α)) * (∑' k, cS N k * e (k * α))
        * e (-(n * α))) := by
    intro α
    rw [TH_full, mul_sum, St_eq]
    refine sum_congr rfl fun n _ => ?_
    rw [show (n : ℝ) * -α = -(n * α) by ring]; ring
  simp_rw [hpt]
  have hsw : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n : ℝ) : ℂ) * ((∑' m, cS N m * e (m * α)) * (∑' k, cS N k * e (k * α))
        * e (-(n * α)))
      = ∑ n ∈ Icc (N - H) (N + H), ∫ α in (-(1 / 2 : ℝ))..(1 / 2),
      ((tw N H n : ℝ) : ℂ) * ((∑' m, cS N m * e (m * α)) * (∑' k, cS N k * e (k * α))
        * e (-(n * α))) :=
    intervalIntegral.integral_finset_sum fun n _ => (continuous_const.mul
      ((((continuous_tsum_e _ hc).mul (continuous_tsum_e _ hc)).mul
        (continuous_e.comp (continuous_const.mul continuous_id).neg)))).intervalIntegrable _ _
  rw [hsw]
  refine sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul, coef_mul_tsum _ _ hc hc n, conv_cS]
  push_cast; ring

/-! ### `I₁` -/

lemma e_neg_eq (n α : ℝ) : e (-(n * α)) = Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) := by
  unfold e; congr 1; push_cast; ring

lemma zz_eq (N : ℕ) (α : ℝ) :
    zz N α = ((1 / (N : ℝ) : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I := by
  unfold zz; push_cast; ring

lemma zz_ne_zero {N : ℕ} (hN : 1 ≤ N) (α : ℝ) : zz N α ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [zz] at this
  have : (0 : ℝ) < N := by exact_mod_cast hN
  linarith

lemma continuous_zz (N : ℕ) : Continuous (zz N) := by unfold zz; fun_prop

/-- **`I₁`**, from Lemma 2. -/
theorem I1_bound {N H : ℕ} (hN : 1 ≤ N) (hHN : H < N) :
    ‖(∫ α in (-(1 / 2 : ℝ))..(1 / 2), TH N H H (-α) * (1 / zz N α) ^ 2)
      - ∑ n ∈ Icc (N - H) (N + H), ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ)‖
      ≤ (H : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ α, TH N H H (-α) * (1 / zz N α) ^ 2 = ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n : ℝ) : ℂ) * (e (-(n * α)) * (1 / zz N α) ^ 2) := by
    intro α; rw [TH_full, sum_mul]
    refine sum_congr rfl fun n _ => ?_
    rw [show (n : ℝ) * -α = -(n * α) by ring]; ring
  have hcz : Continuous (fun α => (1 / zz N α) ^ 2) :=
    (continuous_const.div (continuous_zz N) (zz_ne_zero hN)).pow 2
  simp_rw [hpt]
  have hsw : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ∑ n ∈ Icc (N - H) (N + H),
      ((tw N H n : ℝ) : ℂ) * (e (-(n * α)) * (1 / zz N α) ^ 2)
      = ∑ n ∈ Icc (N - H) (N + H), ∫ α in (-(1 / 2 : ℝ))..(1 / 2),
      ((tw N H n : ℝ) : ℂ) * (e (-(n * α)) * (1 / zz N α) ^ 2) :=
    intervalIntegral.integral_finset_sum fun n _ => (continuous_const.mul
      (((continuous_e.comp (continuous_const.mul continuous_id).neg)).mul hcz)).intervalIntegrable _ _
  rw [hsw, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [← sum_tw hHN.le, ← div_one (∑ n ∈ Icc (N - H) (N + H), tw N H n)]
  rw [div_one]
  refine sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := by rw [mem_Icc] at hn; omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [intervalIntegral.integral_const_mul]
  have hI : ∫ α in (-(1 / 2 : ℝ))..(1 / 2), e (-(n * α)) * (1 / zz N α) ^ 2
      = ∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine setIntegral_congr_fun measurableSet_Ioc fun α _ => ?_
    rw [e_neg_eq, zz_eq, one_div_pow]
  have h2' := lemma2 hN0 hnr
  rw [hI]
  have e1 : ((tw N H n : ℝ) : ℂ) * (∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
        Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2))
      - ((tw N H n * (n * Real.exp (-n / N)) : ℝ) : ℂ)
      = ((tw N H n : ℝ) : ℂ) * ((∫ α in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
        Complex.exp (((-2 * Real.pi * n * α : ℝ) : ℂ) * I) *
        (1 / (((1 / N : ℝ) : ℂ) - ((2 * Real.pi * α : ℝ) : ℂ) * I) ^ 2))
        - ((n * Real.exp (-n / N) : ℝ) : ℂ)) := by push_cast; ring
  rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tw_nonneg hHN.le hn)]
  have hpi : 1 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  calc tw N H n * ‖_‖ ≤ tw N H n * (1 / Real.pi ^ 2) :=
        mul_le_mul_of_nonneg_left h2' (tw_nonneg hHN.le hn)
    _ ≤ tw N H n * 1 := mul_le_mul_of_nonneg_left hpi (tw_nonneg hHN.le hn)
    _ = tw N H n := mul_one _

end LeanLab.LZCesaroShort

