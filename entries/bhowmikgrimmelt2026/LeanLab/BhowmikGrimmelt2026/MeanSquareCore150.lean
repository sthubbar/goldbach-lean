module

public import LeanLab.BhowmikGrimmelt2026.Statements

/-!
ROUTE BURST 7, 20261112. The elementary infrastructure of the circle method core
`major_minor_mean_square150` of P0029, Bhowmik and Grimmelt 2026, Section 3, pages 10 to 13:
display 3.2, the identity `r₂(N) = ∫_0^1 S(α)² e(-Nα) dα`; Parseval's identity
`∫_0^1 |S(α)|² dα = Σ Λ(n)²`; Bessel's inequality on `[0, 1]`, which is the form of Parseval
the sentence before display 3.8 uses; the major arc model of display 3.5 on the Dirichlet
dissection at level `Q = ⌊X^{1/2}⌋`, page 11; and the abstract assembly
`Σ_N |r₂(N) - ∫ V² e(-Nα)|² ≤ 2 B² (∫|S|² + ∫|V|²)` when `|S - V| ≤ B`.

Copies, said plainly: `integral_ee_int150` copies `integral_ee_int` of Convolution.lean;
`r2_eq_integral150` and `integral_norm_sq_Ssum150` adapt `r2_eq_integral` and
`integral_norm_sq_S` of ExceptionalSet/BG2026MinorCont.lean to `ee`, `Ssum` and the
antidiagonal `r2` of Statements.lean; `bessel150` adapts `bessel_minor` of the same file.
They are copied, not imported, to keep this module's imports to Statements only.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

/-! ### The additive character `ee` -/

theorem continuous_ee150 : Continuous ee := by unfold ee; fun_prop

theorem norm_ee150 (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * x = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem conj_ee150 (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

theorem ee_add150 (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Orthogonality on `[0, 1]`, a copy of `integral_ee_int` of Convolution.lean. -/
theorem integral_ee_int150 (j : ℤ) :
    ∫ α in (0 : ℝ)..1, ee ((j : ℝ) * α) = if j = 0 then 1 else 0 := by
  by_cases hj : j = 0
  · subst j
    simp [ee]
  · rw [if_neg hj]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hjc : (j : ℂ) ≠ 0 := by exact_mod_cast hj
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero) hjc
    have hrw : (fun α : ℝ => ee ((j : ℝ) * α)) =
        fun α : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (j : ℂ)) * α) := by
      funext α
      unfold ee
      congr 1
      push_cast
      ring
    rw [hrw, integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hphase : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * j) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * j = (j : ℂ) * (2 * Real.pi * Complex.I) by ring,
        Complex.exp_int_mul_two_pi_mul_I]
    rw [hphase, sub_self, zero_div]

/-- Integration of a double exponential sum with integer frequencies. -/
theorem integral_double_sum150 (A B : Finset ℕ) (c : ℕ → ℕ → ℂ) (f : ℕ → ℕ → ℤ) :
    ∫ x in (0 : ℝ)..1, ∑ n ∈ A, ∑ m ∈ B, c n m * ee (f n m * x) =
      ∑ n ∈ A, ∑ m ∈ B, c n m * (if f n m = 0 then 1 else 0) := by
  have hterm : ∀ n m, IntervalIntegrable (fun x : ℝ => c n m * ee (f n m * x)) volume 0 1 :=
    fun n m => (continuous_const.mul (continuous_ee150.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hi : ∀ n, IntervalIntegrable (fun x : ℝ => ∑ m ∈ B, c n m * ee (f n m * x)) volume 0 1 :=
    fun n => (continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_ee150.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun n _ => hi n)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [intervalIntegral.integral_finsetSum (fun m _ => hterm n m)]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_ee_int150]

/-! ### The prime exponential sum `Ssum` of page 14 -/

theorem Ssum_eq150 (X : ℕ) (α : ℝ) :
    Ssum X α = ∑ n ∈ Finset.Icc 1 X, (vonMangoldt n : ℂ) * ee ((n : ℝ) * α) := by
  unfold Ssum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [mul_comm α]

theorem continuous_Ssum150 (X : ℕ) : Continuous (Ssum X) := by
  have : Ssum X = fun α => ∑ n ∈ Finset.Icc 1 X, (vonMangoldt n : ℂ) * ee ((n : ℝ) * α) :=
    funext (Ssum_eq150 X)
  rw [this]
  exact continuous_finsetSum _ fun n _ =>
    continuous_const.mul (continuous_ee150.comp (continuous_const.mul continuous_id))

theorem norm_Ssum_le150 (X : ℕ) (α : ℝ) : ‖Ssum X α‖ ≤ ∑ n ∈ Finset.Icc 1 X, vonMangoldt n := by
  rw [Ssum_eq150]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun n _ => ?_)))
  rw [norm_mul, norm_ee150, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg]

/-- Display 3.2 in the sharp form, P0029 pages 10 and 14: `∫_0^1 S(α)² e(-Nα) dα = r₂(N)` for
`N ≤ X`. PROVED. -/
theorem r2_eq_integral150 {X N : ℕ} (hN : N ≤ X) :
    ∫ α in (0 : ℝ)..1, Ssum X α ^ 2 * ee (-((N : ℝ) * α)) = (r2 N : ℂ) := by
  have e1 : ∀ α : ℝ, Ssum X α ^ 2 * ee (-((N : ℝ) * α)) =
      ∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
        ((vonMangoldt n : ℂ) * vonMangoldt m) * ee ((((n : ℤ) + m - N : ℤ) : ℝ) * α) := by
    intro α
    rw [Ssum_eq150, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have : ee ((n : ℝ) * α) * ee ((m : ℝ) * α) * ee (-((N : ℝ) * α)) =
        ee ((((n : ℤ) + m - N : ℤ) : ℝ) * α) := by
      rw [← ee_add150, ← ee_add150]
      congr 1; push_cast; ring
    rw [← this]; ring
  simp_rw [e1]
  rw [integral_double_sum150]
  have e2 : ∀ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X, ((vonMangoldt n : ℂ) * vonMangoldt m) *
      (if ((n : ℤ) + m - N) = 0 then 1 else 0) =
        if n ≤ N then (vonMangoldt n : ℂ) * vonMangoldt (N - n) else 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    split_ifs with hnN
    · by_cases hNn : N - n = 0
      · rw [hNn]
        rw [Finset.sum_eq_zero]
        · simp
        · intro m hm
          rw [Finset.mem_Icc] at hm
          rw [if_neg (by omega)]; simp
      · rw [Finset.sum_eq_single (N - n)]
        · rw [if_pos (by omega)]; ring
        · intro b _ hb; rw [if_neg (by omega)]; simp
        · intro h; exfalso; apply h; rw [Finset.mem_Icc]; omega
    · apply Finset.sum_eq_zero; intro m _; rw [if_neg (by omega)]; simp
  rw [Finset.sum_congr rfl e2, ← Finset.sum_filter]
  unfold r2
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  have hf : (Finset.Icc 1 X).filter (fun n => n ≤ N) = Finset.Icc 1 N := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hf, Finset.range_eq_Ico]
  have hsplit : Finset.Ico 0 (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  simp

/-- Parseval for `S`, P0029 page 12 "Parseval implies that the average size of `|f|`":
`∫_0^1 |S(α)|² dα = Σ_{n ≤ X} Λ(n)²`. PROVED. -/
theorem integral_norm_sq_Ssum150 (X : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖Ssum X α‖ ^ 2 = ∑ n ∈ Finset.Icc 1 X, (vonMangoldt n) ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have e1 : ∀ α : ℝ, ((‖Ssum X α‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
      ((vonMangoldt n : ℂ) * vonMangoldt m) * ee ((((n : ℤ) - m : ℤ) : ℝ) * α) := by
    intro α
    rw [Complex.ofReal_pow, ← Complex.mul_conj', Ssum_eq150, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [map_mul, Complex.conj_ofReal, conj_ee150]
    have : ee ((n : ℝ) * α) * ee (-((m : ℝ) * α)) = ee ((((n : ℤ) - m : ℤ) : ℝ) * α) := by
      rw [← ee_add150]
      congr 1; push_cast; ring
    rw [← this]; ring
  simp_rw [e1]
  rw [integral_double_sum150]
  push_cast
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.sum_eq_single n]
  · simp; ring
  · intro b _ hb; rw [if_neg (by omega)]; simp
  · intro h; exact absurd hn h

/-- The trivial bound `Σ_{n ≤ X} Λ(n)² ≤ X (log X)²`. PROVED. -/
theorem sum_vonMangoldt_sq_le150 (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, (vonMangoldt n) ^ 2 ≤ (X : ℝ) * Real.log X ^ 2 := by
  have hpt : ∀ n ∈ Finset.Icc 1 X, (vonMangoldt n) ^ 2 ≤ Real.log X ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : vonMangoldt n ≤ Real.log n := vonMangoldt_le_log
    have h2 : Real.log n ≤ Real.log X :=
      Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
    exact pow_le_pow_left₀ vonMangoldt_nonneg (h1.trans h2) 2
  calc ∑ n ∈ Finset.Icc 1 X, (vonMangoldt n) ^ 2 ≤ ∑ n ∈ Finset.Icc 1 X, Real.log X ^ 2 :=
        Finset.sum_le_sum hpt
    _ = (X : ℝ) * Real.log X ^ 2 := by simp

/-! ### Bessel's inequality on `[0, 1]` -/

/-- Bessel on `[0, 1]` for square integrable `g`: `Σ_{k ∈ F} |∫_0^1 g(α) e(-kα) dα|² ≤
∫_0^1 |g|²`, from Mathlib's Parseval `hasSum_sq_fourierCoeffOn`. Adapted from `bessel_minor`
of ExceptionalSet/BG2026MinorCont.lean. PROVED. -/
theorem bessel150 (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (F : Finset ℤ) :
    ∑ k ∈ F, ‖∫ α in (0 : ℝ)..1, g α * ee (-((k : ℝ) * α))‖ ^ 2 ≤
      ∫ α in (0 : ℝ)..1, ‖g α‖ ^ 2 := by
  have h := hasSum_sq_fourierCoeffOn (zero_lt_one' ℝ) hg
  have h2 := sum_le_hasSum F (fun _ _ => by positivity) h
  have hc : ∀ k : ℤ, fourierCoeffOn (zero_lt_one' ℝ) g k =
      ∫ α in (0 : ℝ)..1, g α * ee (-((k : ℝ) * α)) := by
    intro k
    rw [fourierCoeffOn_eq_integral]
    rw [show (1 : ℝ) / (1 - 0) = 1 by norm_num, one_smul]
    refine intervalIntegral.integral_congr (fun α _ => ?_)
    rw [fourier_coe_apply, smul_eq_mul, mul_comm]
    unfold ee
    congr 2
    push_cast; ring
  simp only [hc] at h2
  simpa using h2

/-! ### The major arc model of display 3.5 on the Dirichlet dissection -/

/-- The nearest integer `⌊x + 1/2⌋`. -/
noncomputable def nint150 (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

theorem measurable_nint150 : Measurable nint150 := by
  unfold nint150
  exact (measurable_id.add_const _).floor

/-- `T(β) = Σ_{1 ≤ n ≤ X} e(nβ)`, the model sum of the main term of 3.5 in the sharp form. -/
noncomputable def TX150 (X : ℕ) (β : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 X, ee ((n : ℝ) * β)

theorem continuous_TX150 (X : ℕ) : Continuous (TX150 X) := by
  unfold TX150
  exact continuous_finsetSum _ fun n _ =>
    continuous_ee150.comp (continuous_const.mul continuous_id)

theorem norm_TX_le150 (X : ℕ) (β : ℝ) : ‖TX150 X β‖ ≤ X := by
  unfold TX150
  refine (norm_sum_le _ _).trans ?_
  simp [norm_ee150]

/-- The Dirichlet arc of denominator `q` at level `Q = ⌊X^{1/2}⌋`, page 11: the `α` with
`|qα - a| ≤ 1/Q` for the nearest integer `a`, and `q` the least such denominator.  Minimality
makes the arcs of different denominators disjoint and makes `a/q` reduced; by Dirichlet's
theorem they cover `ℝ` when `Q ≥ 1`.  Each Farey arc of order `Q` around `a/q` lies inside
`|α - a/q| ≤ 1/(qQ)`, page 11, so this is the Farey dissection up to the boundary choice. -/
def arcSet150 (X q : ℕ) : Set ℝ :=
  {α | |(q : ℝ) * α - nint150 ((q : ℝ) * α)| ≤ 1 / (Nat.sqrt X : ℝ)} ∩
    ⋂ k ∈ Finset.Ico 1 q, {α | 1 / (Nat.sqrt X : ℝ) < |(k : ℝ) * α - nint150 ((k : ℝ) * α)|}

theorem measurable_dist150 (k : ℕ) :
    Measurable fun α : ℝ => |(k : ℝ) * α - nint150 ((k : ℝ) * α)| := by
  have h1 : Measurable fun α : ℝ => (k : ℝ) * α := measurable_const.mul measurable_id
  have h2 : Measurable fun α : ℝ => ((nint150 ((k : ℝ) * α) : ℤ) : ℝ) :=
    measurable_from_top.comp (measurable_nint150.comp h1)
  exact (h1.sub h2).abs

theorem measurableSet_arcSet150 (X q : ℕ) : MeasurableSet (arcSet150 X q) := by
  unfold arcSet150
  refine MeasurableSet.inter (measurableSet_le (measurable_dist150 q) measurable_const) ?_
  exact Finset.measurableSet_biInter _ fun k _ =>
    measurableSet_lt measurable_const (measurable_dist150 k)

/-- The term of the major arc model of 3.5 on the arc of denominator `q`:
`μ(q)/φ(q) T(α - a/q)` with `a` the nearest integer to `qα`. -/
noncomputable def arcTerm150 (X q : ℕ) (α : ℝ) : ℂ :=
  ((moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) *
    TX150 X (α - ((nint150 ((q : ℝ) * α) : ℤ) : ℝ) / q)

/-- The major arc model `V(α)`, display 3.5 with only its main term kept, page 12: on the arc of
denominator `q ≤ Q` around `a/q`, `V(α) = μ(q)/φ(q) Σ_{n ≤ X} e(n(α - a/q))`. -/
noncomputable def VX150 (X : ℕ) (α : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), (arcSet150 X q).indicator (arcTerm150 X q) α

theorem measurable_arcTerm150 (X q : ℕ) : Measurable (arcTerm150 X q) := by
  unfold arcTerm150
  refine measurable_const.mul ((continuous_TX150 X).measurable.comp ?_)
  have h1 : Measurable fun α : ℝ => (q : ℝ) * α := measurable_const.mul measurable_id
  have h2 : Measurable fun α : ℝ => ((nint150 ((q : ℝ) * α) : ℤ) : ℝ) :=
    measurable_from_top.comp (measurable_nint150.comp h1)
  exact measurable_id.sub (h2.div_const _)

theorem measurable_VX150 (X : ℕ) : Measurable (VX150 X) := by
  unfold VX150
  exact Finset.measurable_sum _ fun q _ =>
    (measurable_arcTerm150 X q).indicator (measurableSet_arcSet150 X q)

theorem norm_arcTerm_le150 (X q : ℕ) (α : ℝ) :
    ‖arcTerm150 X q α‖ ≤ ‖((moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)‖ * X := by
  unfold arcTerm150
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_TX_le150 _ _) (norm_nonneg _)

theorem norm_VX_le150 (X : ℕ) (α : ℝ) :
    ‖VX150 X α‖ ≤ ∑ q ∈ Finset.Icc 1 (Nat.sqrt X),
      ‖((moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)‖ * X := by
  unfold VX150
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_indicator_eq_indicator_norm]
  exact (Set.indicator_le_self' (fun _ _ => norm_nonneg _) α).trans (norm_arcTerm_le150 X q α)

/-! ### The abstract assembly: Bessel applied to `S² - V²` -/

theorem memLp_of_bounded150 (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume) (M : ℝ)
    (hM : ∀ α, ‖g α‖ ≤ M) : MemLp g 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  MemLp.of_bound hg.restrict M (ae_of_all _ hM)

/-- The step "using Parseval's identity together with 3.7", P0029 page 13, in the abstract:
if `V` is a bounded measurable model with `|S - V| ≤ B` on `[0, 1]`, then for any set `F` of
`N ≤ X`, `Σ_{N ∈ F} |r₂(N) - ∫_0^1 V(α)² e(-Nα) dα|² ≤ 2 B² (∫|S|² + ∫|V|²)`.  PROVED: the
`N`-th coefficient of `S²` is `r₂(N)` by `r2_eq_integral150`, Bessel `bessel150` applies to
`S² - V²`, and `|S² - V²|² = |S - V|² |S + V|² ≤ 2 B² (|S|² + |V|²)`. -/
theorem bessel_model150 (X : ℕ) (V : ℝ → ℂ) (hVm : Measurable V) (M : ℝ)
    (hVM : ∀ α, ‖V α‖ ≤ M) (B : ℝ) (hB : ∀ α ∈ Set.Icc (0 : ℝ) 1, ‖Ssum X α - V α‖ ≤ B)
    (F : Finset ℕ) (hF : ∀ N ∈ F, N ≤ X) :
    ∑ N ∈ F, ‖(r2 N : ℂ) - ∫ α in (0 : ℝ)..1, V α ^ 2 * ee (-((N : ℝ) * α))‖ ^ 2 ≤
      2 * B ^ 2 * ((∫ α in (0 : ℝ)..1, ‖Ssum X α‖ ^ 2) + ∫ α in (0 : ℝ)..1, ‖V α‖ ^ 2) := by
  set S := Ssum X with hSdef
  have hSc : Continuous S := continuous_Ssum150 X
  set MS := ∑ n ∈ Finset.Icc 1 X, vonMangoldt n
  have hSM : ∀ α, ‖S α‖ ≤ MS := norm_Ssum_le150 X
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simp))
  set g : ℝ → ℂ := fun α => S α ^ 2 - V α ^ 2 with hgdef
  have hgm : Measurable g := (hSc.measurable.pow_const 2).sub (hVm.pow_const 2)
  have hgM : ∀ α, ‖g α‖ ≤ MS ^ 2 + M ^ 2 := by
    intro α
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_pow]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hSM α) 2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hVM α) 2
    linarith
  have hgL2 := memLp_of_bounded150 g hgm.aestronglyMeasurable _ hgM
  have hbes := bessel150 g hgL2 (F.map Nat.castEmbedding)
  rw [Finset.sum_map] at hbes
  -- integrability facts
  have hVint : ∀ N : ℕ, IntervalIntegrable (fun α => V α ^ 2 * ee (-((N : ℝ) * α))) volume 0 1 := by
    intro N
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.of_bound (C := M ^ 2) ?_ (ae_of_all _ fun α => ?_)
    · exact ((hVm.pow_const 2).mul
        (continuous_ee150.comp (by fun_prop)).measurable).aestronglyMeasurable.restrict
    · rw [norm_mul, norm_ee150, mul_one, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hVM α) 2
  have hSint : ∀ N : ℕ, IntervalIntegrable (fun α => S α ^ 2 * ee (-((N : ℝ) * α))) volume 0 1 :=
    fun N => ((hSc.pow 2).mul (continuous_ee150.comp (by fun_prop))).intervalIntegrable _ _
  have hcoef : ∀ N ∈ F, ∫ α in (0 : ℝ)..1, g α * ee (-(((Nat.castEmbedding N : ℤ) : ℝ) * α)) =
      (r2 N : ℂ) - ∫ α in (0 : ℝ)..1, V α ^ 2 * ee (-((N : ℝ) * α)) := by
    intro N hN
    have hcast : (((Nat.castEmbedding N : ℤ) : ℝ)) = (N : ℝ) := by simp
    simp only [hcast, hgdef, sub_mul]
    rw [intervalIntegral.integral_sub (hSint N) (hVint N), hSdef, r2_eq_integral150 (hF N hN)]
  rw [Finset.sum_congr rfl (fun N hN => by rw [hcoef N hN])] at hbes
  refine hbes.trans ?_
  -- pointwise bound on `[0, 1]`
  have hV2int : IntervalIntegrable (fun α => ‖V α‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.of_bound (C := M ^ 2) ?_ (ae_of_all _ fun α => ?_)
    · exact (hVm.norm.pow_const 2).aestronglyMeasurable.restrict
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hVM α) 2
  have hS2int : IntervalIntegrable (fun α => ‖S α‖ ^ 2) volume 0 1 :=
    ((hSc.norm).pow 2).intervalIntegrable _ _
  have hg2int : IntervalIntegrable (fun α => ‖g α‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    refine Integrable.of_bound (C := (MS ^ 2 + M ^ 2) ^ 2) ?_ (ae_of_all _ fun α => ?_)
    · exact (hgm.norm.pow_const 2).aestronglyMeasurable.restrict
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hgM α) 2
  have hrhs : (∫ α in (0 : ℝ)..1, 2 * B ^ 2 * (‖S α‖ ^ 2 + ‖V α‖ ^ 2)) =
      2 * B ^ 2 * ((∫ α in (0 : ℝ)..1, ‖S α‖ ^ 2) + ∫ α in (0 : ℝ)..1, ‖V α‖ ^ 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hS2int hV2int]
  rw [← hrhs]
  refine intervalIntegral.integral_mono_on zero_le_one hg2int
    ((hS2int.add hV2int).const_mul _) (fun α hα => ?_)
  have hfac : g α = (S α - V α) * (S α + V α) := by simp only [hgdef]; ring
  have hd := hB α hα
  have hsum : ‖S α + V α‖ ≤ ‖S α‖ + ‖V α‖ := norm_add_le _ _
  rw [hfac, norm_mul, mul_pow]
  have h1 : ‖S α - V α‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have h2 : ‖S α + V α‖ ^ 2 ≤ 2 * (‖S α‖ ^ 2 + ‖V α‖ ^ 2) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hsum 2
    nlinarith [sq_nonneg (‖S α‖ - ‖V α‖)]
  calc ‖S α - V α‖ ^ 2 * ‖S α + V α‖ ^ 2 ≤ B ^ 2 * (2 * (‖S α‖ ^ 2 + ‖V α‖ ^ 2)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 2 * B ^ 2 * (‖S α‖ ^ 2 + ‖V α‖ ^ 2) := by ring

end LeanLab.BhowmikGrimmelt2026
