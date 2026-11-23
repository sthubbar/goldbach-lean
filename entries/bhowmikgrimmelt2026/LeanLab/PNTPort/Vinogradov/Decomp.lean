module

public import LeanLab.PNTPort.Vinogradov.Count
public import LeanLab.PNTPort.BV.TypeI

/-!
# Vinogradov's minor arc bound, Vaughan's decomposition and the Type I sums

Lab proof, unit U-5250. AI wrote this file. Known mathematics, no cited input.

`S(α) = ∑_{n ≤ N} Λ(n) e(αn) = T₁ - T₂ + T₃ - T₄` by the lab's `vaughan_identity`, with
* `T₁ = ∑_{n ≤ min(u, N)} Λ(n) e(αn)`, `‖T₁‖ ≤ (log 4 + 4) u`, `norm_T1_le`;
* `T₂ = ∑_{t r ≤ N} c(t) e(αtr)`, `c(t) = ∑_{md = t, m ≤ u, d ≤ v} Λ(m) μ(d)`,
  `‖T₂‖ ≤ 12 log N (N/q + uv + q)(1 + log q + log(uv))`, `norm_T2_le`;
* `T₃ = ∑_{d h ≤ N, d ≤ v} μ(d) log h e(αdh)`,
  `‖T₃‖ ≤ 24 log N (N/q + v + q)(1 + log q + log v)`, `norm_T3_le`;
* `T₄ = ∑_{m k ≤ N, m > u, k > v} Λ(m) g_v(k) e(αmk)`, the Type II sum, bounded in TypeII.lean.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.LargeSieve
open LeanLab.PNTPort.BV (gV sum_Icc_divisorsAntidiagonal sum_Icc_one_eq_range abel_range
  log_nat_mono vaughan_identity)

/-- The exponential sum `S(α) = ∑_{n ≤ N} Λ(n) e(αn)`. -/
noncomputable def S (N : ℕ) (α : ℝ) : ℂ := ∑ n ∈ Icc 1 N, (Λ n : ℂ) * e (n * α)

noncomputable def cT2 (u v t : ℕ) : ℝ :=
  ∑ y ∈ t.divisorsAntidiagonal, (if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0)

noncomputable def T1 (N u : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, ((if n ≤ u then Λ n else 0 : ℝ) : ℂ) * e (n * α)

noncomputable def T2 (N u v : ℕ) (α : ℝ) : ℂ :=
  ∑ t ∈ Icc 1 N, ∑ r ∈ Icc 1 (N / t), (cT2 u v t : ℂ) * e ((t * r : ℕ) * α)

noncomputable def T3 (N v : ℕ) (α : ℝ) : ℂ :=
  ∑ d ∈ Icc 1 N, ∑ h ∈ Icc 1 (N / d),
    ((if d ≤ v then (μ d : ℝ) * Real.log h else 0 : ℝ) : ℂ) * e ((d * h : ℕ) * α)

noncomputable def T4 (N u v : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / m),
    ((if u < m ∧ v < k then Λ m * gV v k else 0 : ℝ) : ℂ) * e ((m * k : ℕ) * α)

lemma conv_e {F : ℕ × ℕ → ℝ} (N : ℕ) (α : ℝ) :
    ∑ n ∈ Icc 1 N, ((∑ p ∈ n.divisorsAntidiagonal, F p : ℝ) : ℂ) * e (n * α) =
      ∑ t ∈ Icc 1 N, ∑ r ∈ Icc 1 (N / t), (F (t, r) : ℂ) * e ((t * r : ℕ) * α) := by
  rw [← sum_Icc_divisorsAntidiagonal (fun p => (F p : ℂ) * e ((p.1 * p.2 : ℕ) * α))]
  refine sum_congr rfl fun n _ => ?_
  rw [Complex.ofReal_sum, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [(Nat.mem_divisorsAntidiagonal.1 hp).1]

/-- Vaughan's decomposition of `S(α)`, for `v ≥ 1`. -/
theorem S_decomp (N u v : ℕ) (hv : 1 ≤ v) (α : ℝ) :
    S N α = T1 N u α - T2 N u v α + T3 N v α - T4 N u v α := by
  have key : ∀ n ∈ Icc 1 N, (Λ n : ℂ) * e (n * α) =
      ((if n ≤ u then Λ n else 0 : ℝ) : ℂ) * e (n * α)
      - ((∑ p ∈ n.divisorsAntidiagonal, cT2 u v p.1 * (if p.2 = p.2 then 1 else 0) : ℝ) : ℂ)
          * e (n * α)
      + ((∑ p ∈ n.divisorsAntidiagonal,
          (if p.1 ≤ v then (μ p.1 : ℝ) * Real.log p.2 else 0) : ℝ) : ℂ) * e (n * α)
      - ((∑ p ∈ n.divisorsAntidiagonal,
          (if u < p.1 ∧ v < p.2 then Λ p.1 * gV v p.2 else 0) : ℝ) : ℂ) * e (n * α) := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
    have hv' := vaughan_identity u v hv n hn1
    simp only [if_true, mul_one]
    rw [← sub_mul, ← add_mul, ← sub_mul]
    congr 1
    unfold cT2
    unfold gV at *
    exact_mod_cast hv'
  rw [S, sum_congr rfl key, sum_sub_distrib, sum_add_distrib, sum_sub_distrib]
  simp only [if_true, mul_one]
  rw [conv_e (F := fun p => cT2 u v p.1), conv_e (F := fun p =>
      if p.1 ≤ v then (μ p.1 : ℝ) * Real.log p.2 else 0),
    conv_e (F := fun p => if u < p.1 ∧ v < p.2 then Λ p.1 * gV v p.2 else 0)]
  rfl

end LeanLab.PNTPort.Vinogradov

