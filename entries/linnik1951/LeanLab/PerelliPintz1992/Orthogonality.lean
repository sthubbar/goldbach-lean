module

public import LeanLab.PerelliPintz1992.Statements
public import LeanLab.Common.CircleOrth

/-!
P0070 Perelli-Pintz 1992, Section 3, p. 358: the identity behind (4),
`Ψ(N, 2k) = ∫₀¹ |S(α)|² e(-2kα) dα`, `S(α) = Σ_{n=N}^{2N} Λ(n) e(nα)`, and (4) itself.

* `psi_orth`: `∫₀¹ |S(α)|² e(-2kα) dα = Ψ(N, 2k)`, by orthogonality, Common/CircleOrth.lean
  `integral_ee_int`.
* `psi_orth_shift`: the same over any interval `[c, c + 1]`, by periodicity; the paper's arcs
  live in `(1/Q, 1 + 1/Q)`.
* `eq4_single`: for any measurable `𝔐 ⊆ (c, c + 1]` and `𝔪` its complement there,
  `|Ψ(N,2k) - X|² ≤ 2 |∫_𝔪 |S|² e(-2kα)|² + 2 |∫_𝔐 |S|² e(-2kα) - X|²`.
* `eq4`: (4) summed over `k`, with the constant `2` in place of `≪`.

KNOWN mathematics, the first step of the circle method. AI-written Lean code, Claude, PC run
20261020T0403Z-27388, unit U-1156. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.PerelliPintz1992
open Real ArithmeticFunction MeasureTheory Set

lemma e_eq_ee (x : ℝ) : e x = LeanLab.CircleOrth.ee x := rfl

lemma conj_e (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := LeanLab.CircleOrth.conj_ee x

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := LeanLab.CircleOrth.ee_add x y

lemma continuous_e : Continuous e := LeanLab.CircleOrth.continuous_ee

lemma continuous_S (N : ℕ) : Continuous (S N) := by
  unfold S
  exact continuous_finsetSum _ fun n _ =>
    continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))

/-- The integrand `|S(α)|² e(-2kα)`, written as in `Estimate6`. -/
noncomputable def F (N k : ℕ) (α : ℝ) : ℂ := ((‖S N α‖ ^ 2 : ℝ) : ℂ) * e (-(2 * k * α))

lemma continuous_F (N k : ℕ) : Continuous (F N k) := by
  unfold F
  refine Continuous.mul ?_ (continuous_e.comp (continuous_const.mul continuous_id).neg)
  exact Complex.continuous_ofReal.comp ((continuous_S N).norm.pow 2)

/-- `|S|² e(-2kα)` as a double sum of characters. -/
lemma F_expand (N k : ℕ) (α : ℝ) :
    F N k α = ∑ m ∈ Finset.Icc N (2 * N), ∑ n ∈ Finset.Icc N (2 * N),
      ((Λ m : ℂ) * (Λ n : ℂ)) * e ((((m : ℤ) - n - 2 * k : ℤ) : ℝ) * α) := by
  unfold F
  rw [Complex.ofReal_pow, ← Complex.mul_conj', S, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, conj_e, Complex.conj_ofReal]
  have : e ((((m : ℤ) - n - 2 * k : ℤ) : ℝ) * α) = e (m * α) * e (-(n * α)) * e (-(2 * k * α)) := by
    rw [← e_add, ← e_add]; congr 1; push_cast; ring
  rw [this]; ring

/-- **Orthogonality**: `∫₀¹ |S(α)|² e(-2kα) dα = Ψ(N, 2k)`, p. 358. -/
theorem psi_orth (N k : ℕ) : ∫ α in (0 : ℝ)..1, F N k α = (Psi N k : ℂ) := by
  simp_rw [F_expand]
  have hci : ∀ (c : ℂ) (j : ℤ), IntervalIntegrable (fun α : ℝ => c * e ((j : ℝ) * α)) volume 0 1 :=
    fun c j => ((continuous_e.comp (continuous_const.mul continuous_id)).const_mul _
      ).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun m _ => by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ fun n _ =>
      (continuous_e.comp (continuous_const.mul continuous_id)).const_mul _)]
  have hin : ∀ m ∈ Finset.Icc N (2 * N), ∫ α in (0 : ℝ)..1, ∑ n ∈ Finset.Icc N (2 * N),
      ((Λ m : ℂ) * (Λ n : ℂ)) * e ((((m : ℤ) - n - 2 * k : ℤ) : ℝ) * α)
      = ∑ n ∈ Finset.Icc N (2 * N), if (m : ℤ) - n - 2 * k = 0 then (Λ m : ℂ) * (Λ n : ℂ) else 0 := by
    intro m _
    rw [intervalIntegral.integral_finsetSum (fun n _ => hci _ _)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul]
    simp_rw [e_eq_ee]
    rw [LeanLab.CircleOrth.integral_ee_int]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hin, Finset.sum_comm]
  unfold Psi
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hcond : ∀ m : ℕ, ((m : ℤ) - n - 2 * k = 0) ↔ m = n + 2 * k := by intro m; omega
  simp_rw [hcond]
  rw [Finset.sum_ite_eq']
  have hmem : (n + 2 * k ∈ Finset.Icc N (2 * N)) ↔ n + 2 * k ≤ 2 * N := by
    rw [Finset.mem_Icc]; omega
  rw [if_congr hmem rfl rfl]
  split_ifs <;> ring

/-- `F N k` has period `1`. -/
lemma F_periodic (N k : ℕ) : Function.Periodic (F N k) 1 := by
  intro α
  rw [F_expand, F_expand]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [mul_add, e_add, mul_one]
  have h1 : e ((((m : ℤ) - n - 2 * k : ℤ) : ℝ)) = 1 := by
    rw [e_eq_ee, LeanLab.CircleOrth.ee]
    have := Complex.exp_int_mul_two_pi_mul_I ((m : ℤ) - n - 2 * k)
    rw [← this]; congr 1; push_cast; ring
  rw [h1, mul_one]

/-- Orthogonality over any unit interval `[c, c + 1]`. -/
theorem psi_orth_shift (N k : ℕ) (c : ℝ) : ∫ α in c..c + 1, F N k α = (Psi N k : ℂ) := by
  rw [(F_periodic N k).intervalIntegral_add_eq c 0, zero_add, psi_orth]

/-- `|a + b|² ≤ 2|a|² + 2|b|²`. -/
lemma norm_add_sq_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h0 : 0 ≤ ‖a + b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

/-- **(4), one `k`**: for any measurable `𝔐 ⊆ (c, c + 1]` and `𝔪 = (c, c + 1] \ 𝔐`,
`|Ψ(N,2k) - X|² ≤ 2 |∫_𝔪 |S|² e(-2kα)|² + 2 |∫_𝔐 |S|² e(-2kα) - X|²`. -/
theorem eq4_single (N k : ℕ) (c : ℝ) {M : Set ℝ} (hM : MeasurableSet M)
    (hsub : M ⊆ Ioc c (c + 1)) (X : ℂ) :
    ‖(Psi N k : ℂ) - X‖ ^ 2 ≤
      2 * ‖∫ α in Ioc c (c + 1) \ M, F N k α‖ ^ 2 + 2 * ‖(∫ α in M, F N k α) - X‖ ^ 2 := by
  have hI : IntegrableOn (F N k) (Ioc c (c + 1)) :=
    (continuous_F N k).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hsplit : (Psi N k : ℂ) = (∫ α in Ioc c (c + 1) \ M, F N k α) + ∫ α in M, F N k α := by
    rw [← psi_orth_shift N k c, intervalIntegral.integral_of_le (by linarith)]
    rw [← setIntegral_union (disjoint_sdiff_self_left) hM (hI.mono_set sdiff_subset)
      (hI.mono_set hsub), sdiff_union_of_subset hsub]
  rw [hsplit, add_sub_assoc]
  exact norm_add_sq_le _ _

/-- **(4)**, p. 358, with the constant `2` for `≪`: summed over any finite set of `k`. -/
theorem eq4 (N : ℕ) (K : Finset ℕ) (c : ℝ) {M : Set ℝ} (hM : MeasurableSet M)
    (hsub : M ⊆ Ioc c (c + 1)) :
    ∑ k ∈ K, ‖(Psi N k : ℂ) - ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ)‖ ^ 2 ≤
      2 * ∑ k ∈ K, ‖∫ α in Ioc c (c + 1) \ M, F N k α‖ ^ 2 +
      2 * ∑ k ∈ K, ‖(∫ α in M, F N k α) - ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ)‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => eq4_single N k c hM hsub _

/-- Vacuity: `𝔐 = ∅` meets the hypotheses for every `c`. -/
example (N : ℕ) (K : Finset ℕ) :
    ∑ k ∈ K, ‖(Psi N k : ℂ) - ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ)‖ ^ 2 ≤
      2 * ∑ k ∈ K, ‖∫ α in Ioc (0 : ℝ) (0 + 1) \ ∅, F N k α‖ ^ 2 +
      2 * ∑ k ∈ K, ‖(∫ α in (∅ : Set ℝ), F N k α) - ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ)‖ ^ 2 :=
  eq4 N K 0 MeasurableSet.empty (empty_subset _)


end LeanLab.PerelliPintz1992
