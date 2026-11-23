module

public import LeanLab.BhowmikGrimmelt2026.MeanSquareCore150

/-!
ROUTE BURST 7, 20261112. The arc main term of P0029, Bhowmik and Grimmelt 2026, page 12:
"If in 3.5 we keep only the main term and substitute it into 3.2, then the contribution of the
arc around `a/q` can be shown to be `μ(q)²/φ(q)² N e(-aN/q) + O(N^{1/2+ε})`. Summing first over
reduced residues `a mod q` produces Ramanujan sums `c_q(-N)`."

Here the full model `W(α) = Σ_{q ≤ Q} Σ_{(a,q)=1} μ(q)²/φ(q)² T(α - a/q)²` is the square of the
major arc model with each arc extended to the whole circle.  PROVED: its `N`-th Fourier
coefficient on `[0, 1]` is exactly `(N - 1) Σ_{q ≤ Q} μ(q)²/φ(q)² c_q(-N)` for `1 ≤ N ≤ X`,
`coeff_WX150`, and Bessel bounds the coefficients of `V² - W` by `∫_0^1 |V² - W|²`,
`bessel_VW150`.  The difference `V² - W` is the sum of the arc tails of `T²`.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

/-- The weight `μ(q)²/φ(q)²` of page 12. -/
noncomputable def wq150 (q : ℕ) : ℂ :=
  ((moebius q : ℤ) : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2

/-- The full model of page 12: `W(α) = Σ_{q ≤ Q} Σ_{(a,q)=1} μ(q)²/φ(q)² T(α - a/q)²` with
`Q = ⌊X^{1/2}⌋`. -/
noncomputable def WX150 (X : ℕ) (α : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    wq150 q * TX150 X (α - (a : ℝ) / q) ^ 2

theorem continuous_WX150 (X : ℕ) : Continuous (WX150 X) := by
  unfold WX150
  exact continuous_finsetSum _ fun q _ => continuous_finsetSum _ fun a _ =>
    continuous_const.mul (((continuous_TX150 X).comp (continuous_id.sub continuous_const)).pow 2)

/-- `∫_0^1 T(α - c)² e(-Nα) dα = (N - 1) e(-Nc)` for `1 ≤ N ≤ X`: the number of
`n + m = N` with `1 ≤ n, m ≤ X` is `N - 1`. PROVED. -/
theorem integral_TX_sq_shift150 {X N : ℕ} (hN1 : 1 ≤ N) (hN : N ≤ X) (c : ℝ) :
    ∫ α in (0 : ℝ)..1, TX150 X (α - c) ^ 2 * ee (-((N : ℝ) * α)) =
      ((N : ℂ) - 1) * ee (-((N : ℝ) * c)) := by
  have e1 : ∀ α : ℝ, TX150 X (α - c) ^ 2 * ee (-((N : ℝ) * α)) =
      ∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
        ee (-(((n : ℝ) + m) * c)) * ee ((((n : ℤ) + m - N : ℤ) : ℝ) * α) := by
    intro α
    unfold TX150
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← ee_add150, ← ee_add150, ← ee_add150]
    congr 1; push_cast; ring
  simp_rw [e1]
  rw [integral_double_sum150]
  have e2 : ∀ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X, ee (-(((n : ℝ) + m) * c)) *
      (if ((n : ℤ) + m - N) = 0 then 1 else 0) =
        if n < N then ee (-((N : ℝ) * c)) else 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    split_ifs with hnN
    · rw [Finset.sum_eq_single (N - n)]
      · rw [if_pos (by omega)]
        rw [mul_one]
        congr 2
        have : ((N - n : ℕ) : ℝ) = (N : ℝ) - n := by
          rw [Nat.cast_sub (by omega)]
        rw [this]; ring
      · intro b _ hb; rw [if_neg (by omega)]; simp
      · intro h; exfalso; apply h; rw [Finset.mem_Icc]; omega
    · apply Finset.sum_eq_zero; intro m hm
      rw [Finset.mem_Icc] at hm
      rw [if_neg (by omega)]; simp
  rw [Finset.sum_congr rfl e2, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hf : (Finset.Icc 1 X).filter (fun n => n < N) = Finset.Icc 1 (N - 1) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hf, Nat.card_Icc]
  have : ((N - 1 + 1 - 1 : ℕ) : ℂ) = (N : ℂ) - 1 := by
    rw [show N - 1 + 1 - 1 = N - 1 by omega, Nat.cast_sub hN1]; simp
  rw [this]

/-- PROVED. Page 12: the `N`-th coefficient of the full model is
`(N - 1) Σ_{q ≤ Q} μ(q)²/φ(q)² c_q(-N)` for `1 ≤ N ≤ X`. -/
theorem coeff_WX150 {X N : ℕ} (hN1 : 1 ≤ N) (hN : N ≤ X) :
    ∫ α in (0 : ℝ)..1, WX150 X α * ee (-((N : ℝ) * α)) =
      ((N : ℂ) - 1) * ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), wq150 q * ramanujan q (-(N : ℤ)) := by
  have hc : ∀ (q a : ℕ), Continuous fun α : ℝ =>
      wq150 q * TX150 X (α - (a : ℝ) / q) ^ 2 * ee (-((N : ℝ) * α)) :=
    fun q a => (continuous_const.mul (((continuous_TX150 X).comp
      (continuous_id.sub continuous_const)).pow 2)).mul
      (continuous_ee150.comp (continuous_const.mul continuous_id).neg)
  have e1 : ∀ α : ℝ, WX150 X α * ee (-((N : ℝ) * α)) =
      ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        wq150 q * TX150 X (α - (a : ℝ) / q) ^ 2 * ee (-((N : ℝ) * α)) := by
    intro α
    unfold WX150
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_mul]
  simp_rw [e1]
  have hIq : ∀ q ∈ Finset.Icc 1 (Nat.sqrt X), IntervalIntegrable (fun α =>
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        wq150 q * TX150 X (α - (a : ℝ) / q) ^ 2 * ee (-((N : ℝ) * α))) volume 0 1 :=
    fun q _ => (continuous_finsetSum _ fun a _ => hc q a).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hIq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hIa : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), IntervalIntegrable
      (fun α => wq150 q * TX150 X (α - (a : ℝ) / q) ^ 2 * ee (-((N : ℝ) * α))) volume 0 1 :=
    fun a _ => (hc q a).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hIa]
  unfold ramanujan
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, integral_TX_sq_shift150 hN1 hN]
  have : ee (-((N : ℝ) * ((a : ℝ) / q))) = ee ((a : ℝ) * ((-(N : ℤ) : ℤ) : ℝ) / q) := by
    congr 1; push_cast; ring
  rw [this]; ring

/-- PROVED. Bessel for `V² - W`: for `F ⊆ [1, X]`, the coefficients of `V²` and of `W` differ in
mean square by at most `∫_0^1 |V² - W|²`. -/
theorem bessel_VW150 (X : ℕ) (F : Finset ℕ) :
    ∑ N ∈ F, ‖(∫ α in (0 : ℝ)..1, VX150 X α ^ 2 * ee (-((N : ℝ) * α))) -
        ∫ α in (0 : ℝ)..1, WX150 X α * ee (-((N : ℝ) * α))‖ ^ 2 ≤
      ∫ α in (0 : ℝ)..1, ‖VX150 X α ^ 2 - WX150 X α‖ ^ 2 := by
  set M := ∑ q ∈ Finset.Icc 1 (Nat.sqrt X),
      ‖((moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)‖ * X
  have hVM : ∀ α, ‖VX150 X α‖ ≤ M := norm_VX_le150 X
  have hWc := continuous_WX150 X
  -- `W` is bounded, being continuous and 1-periodic is not needed: bound it directly
  set MW := ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ∑ a ∈ (Finset.range q).filter
      (fun a => Nat.Coprime a q), ‖wq150 q‖ * (X : ℝ) ^ 2
  have hWM : ∀ α, ‖WX150 X α‖ ≤ MW := by
    intro α
    unfold WX150
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_TX_le150 _ _) 2)
      (norm_nonneg _)
  set g : ℝ → ℂ := fun α => VX150 X α ^ 2 - WX150 X α with hgdef
  have hgm : Measurable g := ((measurable_VX150 X).pow_const 2).sub hWc.measurable
  have hgM : ∀ α, ‖g α‖ ≤ M ^ 2 + MW := by
    intro α
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow]
    have := pow_le_pow_left₀ (norm_nonneg _) (hVM α) 2
    linarith [hWM α]
  have hbes := bessel150 g (memLp_of_bounded150 g hgm.aestronglyMeasurable _ hgM)
    (F.map Nat.castEmbedding)
  rw [Finset.sum_map] at hbes
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun N _ => ?_)) hbes
  have hcast : (((Nat.castEmbedding N : ℤ) : ℝ)) = (N : ℝ) := by simp
  rw [hcast]
  have hV : IntervalIntegrable (fun α => VX150 X α ^ 2 * ee (-((N : ℝ) * α))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.of_bound (C := M ^ 2) ?_ (ae_of_all _ fun α => ?_)
    · exact (((measurable_VX150 X).pow_const 2).mul
        (continuous_ee150.comp (by fun_prop)).measurable).aestronglyMeasurable.restrict
    · rw [norm_mul, norm_ee150, mul_one, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hVM α) 2
  have hW : IntervalIntegrable (fun α => WX150 X α * ee (-((N : ℝ) * α))) volume 0 1 :=
    (hWc.mul (continuous_ee150.comp (by fun_prop))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hV hW]
  congr 2
  refine intervalIntegral.integral_congr fun α _ => ?_
  simp only [hgdef]
  ring

end LeanLab.BhowmikGrimmelt2026
