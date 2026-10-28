module

public import LeanLab.BS2022GRH.JournalMargin
public import LeanLab.Helfgott2013.GammaFine

/-!
P0021, T2 FRONTIER, I-0088 follow-up, unit U-1193: the journal version's own Section 5.4 argument,
asked only for a POSITIVE constant, as Corollary 1, Chen's theorem itself, needs, closes at
exp(exp 13.375) under GRH, in place of exp(exp 13.45) with constant 4·10⁻³ and the printed
exp(exp 14).

Bordignon-Starichkova, Ramanujan J. 64 (2024). Same inputs as JournalLower.lean, u = 1500,
ε(1500) < 1/8349, Table 1 row 6100, C₁ = 112, C₂ = 114, A = 10, ε₁ = 10⁻²⁰, with
α₁ = α₂ = α₃ = 0.00256 in place of 0.0024. Theorems 5, 6, 7 allow α₁ < 1/8, α₂ < 1/24,
α₃ < 1/16, and need log X₂ ≥ (A + 1)/αᵢ and α log X₂ − (A + 1) log log X₂ ≥ u, displays (19),
(21), (25).
* `theorem3_positive_main`: K3J(0.00256, e^γ, 1/8349, 112, 114, c̄) > 10⁻⁴; Python value 1.586·10⁻⁴.
* `conditions_13375`: 0.00256 e^{13.375} − 11·13.375 ≥ 1500 and e^{13.375} ≥ 11/0.00256.
The terms K3J leaves out, the factors 1 + 1/y and the 1/log² N terms of Theorems 6 and 7, total
about 6·10⁻⁶ at log log N = 13.375, numerics/journal54_U1193.py, total 1.535·10⁻⁴. So GRH and the
journal's Theorems 5 to 7 and Lemma 9, at these parameters, give π₂(N) > 9·10⁻⁵ U_N N/log² N > 0
for every even N ≥ exp(exp 13.375). CONDITIONAL ON GRH and those cited results; a re-choice of
the authors' own parameters inside their method.

e^γ is bracketed by Helfgott2013.GammaFine, 1.7810699 < e^γ < 1.7810725; the coarser
Constants.g_bounds lose about 2·10⁻⁴ here, more than the whole margin.

AI-written Lean code, Claude, PC run 20261020T0802Z-20406, unit U-1193. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH.Journal
open Real

lemma log297952_ge : (1.09176 : ℝ) ≤ log (3 - 8 * 0.00256) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have e : (1.09176 : ℝ) = 1 + 0.09176 := by norm_num
  rw [e, exp_add]
  have h1 := Real.exp_one_lt_d9
  have h2 : exp (0.09176 : ℝ) ≤ 1.0961021 := by
    have h := Real.exp_bound' (x := (0.09176 : ℝ)) (by norm_num) (by norm_num) (n := 10) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  calc exp 1 * exp 0.09176 ≤ 2.7182818286 * 1.0961021 := by gcongr
    _ ≤ 3 - 8 * 0.00256 := by norm_num

lemma exp197952_le : exp (8 * 0.00256 - 2 : ℝ) ≤ 0.13814 := by
  have h2 : (7.2392 : ℝ) ≤ exp 1.97952 := by
    have h := Real.sum_le_exp_of_nonneg (x := (1.97952 : ℝ)) (by norm_num) 18
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have e : (8 * 0.00256 - 2 : ℝ) = -1.97952 := by norm_num
  rw [e, exp_neg]
  have : (exp 1.97952)⁻¹ ≤ (7.2392 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
  have : (7.2392 : ℝ)⁻¹ ≤ 0.13814 := by norm_num
  linarith

/-- `log(2.97952/2.95392) ≤ 0.00863`, through `exp 0.00863 ≥ 1 + 0.00863 + 0.00863²/2`; the
cruder `log x ≤ x − 1` loses 3.7·10⁻⁵, about 1.3·10⁻⁴ in K3J. -/
lemma logr256_le : log ((3 - 8 * 0.00256) / (3 - 18 * 0.00256) : ℝ) ≤ 0.00863 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (x := (0.00863 : ℝ)) (by norm_num) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢; linarith

/-- **The main-term margin at u = 1500, α = 0.00256**: K3J > 10⁻⁴ > 0. -/
theorem theorem3_positive_main :
    (0.0001 : ℝ) < K3J 0.00256 (exp eulerMascheroniConstant) (1 / 8349) 112 114
      LeanLab.ChenExplicit.BJS.cbar := by
  have hg1 := LeanLab.Helfgott2013.GammaFine.exp_gamma_gt
  have hg2 := LeanLab.Helfgott2013.GammaFine.exp_gamma_lt
  have hc := LeanLab.ChenExplicit.BJS.cbar_lt
  have hc0 := LeanLab.ChenExplicit.BJS.cbar_gt
  have hl3 := log297952_ge
  have he := exp197952_le
  have hl6 := log6_le
  have hl83 := log83_le
  have hlr := logr256_le
  have hl83' : 0 ≤ log (8 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have hr0 : 0 ≤ log ((3 - 8 * 0.00256) / (3 - 18 * 0.00256) : ℝ) := Real.log_nonneg (by norm_num)
  have hl60 : 0 ≤ log (6 : ℝ) := Real.log_nonneg (by norm_num)
  set g := exp eulerMascheroniConstant
  set cb := LeanLab.ChenExplicit.BJS.cbar
  set r := log ((3 - 8 * 0.00256) / (3 - 18 * 0.00256) : ℝ)
  have hg0 : 0 ≤ g := (exp_pos _).le
  have hl30 : 0 ≤ log (3 - 8 * 0.00256 : ℝ) := by linarith
  have T1 : 1.7810699 * 1.09176 ≤ g * log (3 - 8 * 0.00256 : ℝ) :=
    mul_le_mul hg1.le hl3 (by norm_num) hg0
  have T3 : g * (log 6 + r) ≤ 1.7810725 * (1.79176 + 0.00863) :=
    mul_le_mul hg2.le (add_le_add hl6 hlr) (by linarith) (by norm_num)
  have T4 : (2 * g / (1 / 2 - 0.00256) + 3 * (1 / 8349) * 112) * cb ≤
      (2 * 1.7810725 / (1 / 2 - 0.00256) + 3 * (1 / 8349) * 112) * 0.363084 := by
    have h1 : 2 * g / (1 / 2 - 0.00256) ≤ 2 * 1.7810725 / (1 / 2 - 0.00256) := by
      apply div_le_div_of_nonneg_right _ (by norm_num); linarith
    have h2 : 0 ≤ 2 * g / (1 / 2 - 0.00256) + 3 * (1 / 8349) * 112 := by positivity
    exact mul_le_mul (by linarith) (by norm_num at hc ⊢; linarith) (by linarith) (by norm_num)
  have T5 : log (8 / 3) * (1 / 8349) * 112 ≤ (0.98083 : ℝ) * (1 / 8349) * 112 := by nlinarith
  unfold K3J
  have e1 : 2 * g * log (3 - 8 * 0.00256) / (4 - 8 * 0.00256) =
      2 * (g * log (3 - 8 * 0.00256)) / 3.97952 := by norm_num; ring
  have e2 : g / 4 * (log 6 + r) / (1 / 2 - 0.00256) = g * (log 6 + r) / 1.98976 := by
    norm_num; ring
  rw [e1, e2]
  have hE : (1 / 8349 : ℝ) * 114 * 3 * exp (8 * 0.00256 - 2) / (4 - 8 * 0.00256)
      ≤ (1 / 8349) * 114 * 3 * 0.13814 / (4 - 8 * 0.00256) := by
    apply div_le_div_of_nonneg_right _ (by norm_num); nlinarith
  have hA : 2 * (1.7810699 * 1.09176) / 3.97952 ≤
      2 * (g * log (3 - 8 * 0.00256 : ℝ)) / 3.97952 := by
    apply div_le_div_of_nonneg_right _ (by norm_num); linarith
  have hB : g * (log 6 + r) / 1.98976 ≤ 1.7810725 * (1.79176 + 0.00863) / 1.98976 :=
    div_le_div_of_nonneg_right T3 (by norm_num)
  have fin : (0.0001 : ℝ) < 8 * (2 * (1.7810699 * 1.09176) / 3.97952
      - (1 / 8349) * 114 * 3 * 0.13814 / (4 - 8 * 0.00256))
      - 1 / 2 * (8 * ((1 + 5e-5) * (1.7810725 * (1.79176 + 0.00863) / 1.98976
        + 0.98083 * (1 / 8349) * 112)))
      - 1 / 2 * ((2 * 1.7810725 / (1 / 2 - 0.00256) + 3 * (1 / 8349) * 112) * 0.363084) := by
    norm_num
  nlinarith

/-- `e^{13.375} ≥ 643700`, from `e > 2.7182818283` and `e^{0.375} ≥ 1.45499`. -/
lemma exp13375_ge : (643700 : ℝ) ≤ exp 13.375 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : (1.45499 : ℝ) ≤ exp 0.375 := by
    have h := Real.sum_le_exp_of_nonneg (x := (0.375 : ℝ)) (by norm_num) 10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have e : exp (13.375 : ℝ) = exp 1 ^ 13 * exp 0.375 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have h13 : (2.7182818283 : ℝ) ^ 13 ≤ exp 1 ^ 13 := pow_le_pow_left₀ (by norm_num) h1.le 13
  calc (643700 : ℝ) ≤ 2.7182818283 ^ 13 * 1.45499 := by norm_num
    _ ≤ exp 1 ^ 13 * exp 0.375 := mul_le_mul h13 h2 (by norm_num) (by positivity)

/-- **Conditions (19), (21), (25) at log log X₂ = 13.375**: with L = log X₂ = e^{13.375},
`0.00256 L − 11 log L ≥ 1500` and `L ≥ 11/0.00256`. -/
theorem conditions_13375 :
    (1500 : ℝ) ≤ 0.00256 * exp 13.375 - 11 * 13.375 ∧ 11 / 0.00256 ≤ exp (13.375 : ℝ) := by
  have h := exp13375_ge
  constructor <;> nlinarith

/-- Vacuity: the parameter ranges of Theorems 5 to 7 hold at α = 0.00256, and K3J's arguments
are those of a nonempty instance, so the conjunction is not vacuous. -/
theorem params_ok_13375 :
    (0.00256 : ℝ) < 1 / 24 ∧ (400 : ℝ) ≤ 1500 ∧ (1500 : ℝ) ≤ 10 ^ 8 ∧
      (0 : ℝ) < K3J 0.00256 (exp eulerMascheroniConstant) (1 / 8349) 112 114
        LeanLab.ChenExplicit.BJS.cbar := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  have := theorem3_positive_main
  linarith


end LeanLab.BS2022GRH.Journal
