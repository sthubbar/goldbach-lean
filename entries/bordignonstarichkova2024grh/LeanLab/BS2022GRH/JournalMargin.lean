module

public import LeanLab.BS2022GRH.Constants

/-!
P0021, Bordignon-Starichkova, the Ramanujan J. 64 (2024) 1213-1242 version of record, Section 5.4,
p. 1241: Theorem 3 at its new parameters `α₁ = α₂ = α₃ = 10⁻³`, `ε = ε(1000) < 1/5235`,
`C₁ = 113`, `C₂ = 114`, `N ≥ exp(exp 14)`, constant `4·10⁻³`.

* `K3J`: the main-term constant, `K3` of Constants.lean with Lemma 11's factor `1 + 5·10⁻⁵` on
  Theorem 6's `l₁` as the journal prints it, p. 1231.
* `theorem3_journal_main`: `K3J > 0.0045 > 4·10⁻³`. Python mpmath gives `K3J = 0.0056`, and the
  whole Section 5.4 combination at `log N = e^14` gives `0.00563`, the error terms below `10⁻⁹`.

ε(1000) < 1/5235 from display (6), p. 1221, and `C₁ = 113`, `C₂ = 114` from the Table 1 row
`ε⁻¹ = 4500` are checked in Python only: ε(1000) = 1.909975·10⁻⁴ < 1/5235 = 1.910220·10⁻⁴.

AI-written Lean code, Claude, PC run 20261020T0403Z-27388, unit U-1160. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BS2022GRH.Journal
open Real

/-- Theorem 3's main-term constant in the journal version: `K3` with `(1 + 5·10⁻⁵) l₁`. -/
noncomputable def K3J (α g ε C₁ C₂ cb : ℝ) : ℝ :=
  8 * (2 * g * log (3 - 8 * α) / (4 - 8 * α) - ε * C₂ * 3 * exp (8 * α - 2) / (4 - 8 * α))
  - 1 / 2 * (8 * ((1 + 5e-5) * (g / 4 * (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α)
      + log (8 / 3) * ε * C₁)))
  - 1 / 2 * ((2 * g / (1 / 2 - α) + 3 * ε * C₁) * cb)

lemma log2992_ge : (1.0959 : ℝ) ≤ log (3 - 8 * 0.001) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have e : (1.0959 : ℝ) = 1 + 0.0959 := by norm_num
  rw [e, exp_add]
  have h1 := Real.exp_one_lt_d9
  have h2 : exp (0.0959 : ℝ) ≤ 1.1006491 := by
    have h := Real.exp_bound' (x := (0.0959 : ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  calc exp 1 * exp 0.0959 ≤ 2.7182818286 * 1.1006491 := by gcongr
    _ ≤ 3 - 8 * 0.001 := by norm_num

lemma exp1992_le : exp (8 * 0.001 - 2 : ℝ) ≤ 0.136424 := by
  have h2 : (7.3301 : ℝ) ≤ exp 1.992 := by
    have h := Real.sum_le_exp_of_nonneg (x := (1.992 : ℝ)) (by norm_num) 18
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have e : (8 * 0.001 - 2 : ℝ) = -1.992 := by norm_num
  rw [e, exp_neg]
  have : (exp 1.992)⁻¹ ≤ (7.3301 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
  have : (7.3301 : ℝ)⁻¹ ≤ 0.136424 := by norm_num
  linarith

lemma logr_journal_le : log ((3 - 8 * 0.001) / (3 - 18 * 0.001) : ℝ) ≤ 0.0033536 := by
  refine le_trans (Real.log_le_sub_one_of_pos (by norm_num)) ?_
  norm_num

/-- **Journal Theorem 3, main-term margin**: `K3J > 0.0045 > 4·10⁻³` at the journal's
Section 5.4 parameters. -/
theorem theorem3_journal_main :
    (0.0045 : ℝ) < K3J 0.001 (exp eulerMascheroniConstant) (1 / 5235) 113 114
      LeanLab.ChenExplicit.BJS.cbar := by
  obtain ⟨hg1, hg2⟩ := g_bounds
  have hc := LeanLab.ChenExplicit.BJS.cbar_lt
  have hc0 := LeanLab.ChenExplicit.BJS.cbar_gt
  have hl3 := log2992_ge
  have he := exp1992_le
  have hl6 := log6_le
  have hl83 := log83_le
  have hlr := logr_journal_le
  have hl83' : 0 ≤ log (8 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have hr0 : 0 ≤ log ((3 - 8 * 0.001) / (3 - 18 * 0.001) : ℝ) := Real.log_nonneg (by norm_num)
  have hl60 : 0 ≤ log (6 : ℝ) := Real.log_nonneg (by norm_num)
  set g := exp eulerMascheroniConstant
  set cb := LeanLab.ChenExplicit.BJS.cbar
  set r := log ((3 - 8 * 0.001) / (3 - 18 * 0.001) : ℝ)
  have hg0 : 0 ≤ g := (exp_pos _).le
  have hl30 : 0 ≤ log (3 - 8 * 0.001 : ℝ) := by linarith
  have T1 : 1.78103 * 1.0959 ≤ g * log (3 - 8 * 0.001 : ℝ) :=
    mul_le_mul hg1 hl3 (by norm_num) hg0
  have T3 : g * (log 6 + r) ≤ 1.781081 * (1.79176 + 0.0033536) :=
    mul_le_mul hg2 (add_le_add hl6 hlr) (by linarith) (by norm_num)
  have T4 : (2 * g / (1 / 2 - 0.001) + 3 * (1 / 5235) * 113) * cb ≤
      (2 * 1.781081 / (1 / 2 - 0.001) + 3 * (1 / 5235) * 113) * 0.363084 := by
    have h1 : 2 * g / (1 / 2 - 0.001) ≤ 2 * 1.781081 / (1 / 2 - 0.001) := by
      apply div_le_div_of_nonneg_right _ (by norm_num); linarith
    have h2 : 0 ≤ 2 * g / (1 / 2 - 0.001) + 3 * (1 / 5235) * 113 := by positivity
    exact mul_le_mul (by linarith) (by norm_num at hc ⊢; linarith) (by linarith) (by norm_num)
  have T5 : log (8 / 3) * (1 / 5235) * 113 ≤ (0.98083 : ℝ) * (1 / 5235) * 113 := by nlinarith
  unfold K3J
  have e1 : 2 * g * log (3 - 8 * 0.001) / (4 - 8 * 0.001) = 2 * (g * log (3 - 8 * 0.001)) / 3.992 := by
    norm_num; ring
  have e2 : g / 4 * (log 6 + r) / (1 / 2 - 0.001) = g * (log 6 + r) / 1.996 := by
    norm_num; ring
  rw [e1, e2]
  have fin : (0.0045 : ℝ) < 8 * (2 * (1.78103 * 1.0959) / 3.992
      - (1 / 5235) * 114 * 3 * 0.136424 / (4 - 8 * 0.001))
      - 1 / 2 * (8 * ((1 + 5e-5) * (1.781081 * (1.79176 + 0.0033536) / 1.996
        + 0.98083 * (1 / 5235) * 113)))
      - 1 / 2 * ((2 * 1.781081 / (1 / 2 - 0.001) + 3 * (1 / 5235) * 113) * 0.363084) := by
    norm_num
  have hE : (1 / 5235 : ℝ) * 114 * 3 * exp (8 * 0.001 - 2) / (4 - 8 * 0.001)
      ≤ (1 / 5235) * 114 * 3 * 0.136424 / (4 - 8 * 0.001) := by
    apply div_le_div_of_nonneg_right _ (by norm_num); nlinarith
  have hA : 2 * (1.78103 * 1.0959) / 3.992 ≤ 2 * (g * log (3 - 8 * 0.001 : ℝ)) / 3.992 := by
    apply div_le_div_of_nonneg_right _ (by norm_num); linarith
  have hB : g * (log 6 + r) / 1.996 ≤ 1.781081 * (1.79176 + 0.0033536) / 1.996 := by
    apply div_le_div_of_nonneg_right T3 (by norm_num)
  nlinarith


end LeanLab.BS2022GRH.Journal
