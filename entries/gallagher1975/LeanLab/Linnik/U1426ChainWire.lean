module

public import LeanLab.Linnik.LiLiu2026Chain
public import LeanLab.Linnik.U1420Moment46
public import LeanLab.Linnik.U1412MuPhi

/-!
Li-Liu, arXiv 2610.15784, wiring Proposition 5.2, display (53), and the lower half of Lemma 4.3
into the Section 6 chain of `LiLiu2026Chain.lean`; then display (54), display (56) and Lemma 6.1,
display (57). Read by WebFetch on the unversioned arxiv.org/html/2610.15784, 2026-10-21.

Audit of the chain. `LiLiu2026Chain.k6_of_cited` takes the cited constants C₀R₀ < 1.2784421041,
JT's A(2), A(3), the tail T with |T_ij| ≤ √(T_ii T_jj), and a free real `H` with
`0 ≤ H` and `H < 2/15`. None of these is supplied by Proposition 5.2 or Lemma 4.3: the chain
is the numerical criterion (58), and the analytic passage "(56), (57) and Lemma 4.3 imply that
(58) gives r₆''(N) ≫ N L⁶" is not formalized anywhere in the lab. The `H` hypotheses are
discharged here by compactness and `region61`, with `H` the paper's maximum of |Q|² over D_{5/6}.
Proposition 5.2 and Lemma 4.3 are wired into the steps where the paper uses them: the measure of
the exceptional set E₆ in Lemma 6.1, and R₁(0)/(2NL) ≥ 11 log 2/50 + o(1) before (58).

Shape check. `U1420Moment46.prop52_unconditional` is stated with `U1412Display53.Dl` and
`U1420Cover.Il`; the chain uses `LiLiu.Dl` and `LiLiu.Ilam`. They agree: `Dl_eq`, `Il_eq_Ilam`.
The paper's G(α) = ∑_{ν ≤ L} e(2^ν α) and z_L = G/L match `U1412Display53.zL`: `Gs_eq`.

Contents.
* `Il_eq_Ilam`, `Dl_eq`, `Dl_compact`: bridges and compactness of D_λ. PROVED.
* `exc6`, `exc5`: Proposition 5.2 at (λ, ρ) = (5/6, 81/200) and (25/32, 347/1000). PROVED.
* `exists_H6`, `exists_H5`: the maxima H of Section 6 and 7 exist, H ≥ b², H < 2/15, resp. 41/60.
* `display54`, `display54_K6`, `display56_pt`, `display56`: (54) and (56). PROVED.
* `parseval`: ∫_0^1 |∑_{n ∈ A} a_n e(nβ)|² dβ = ∑ a_n². PROVED.
* `lemma61_bound`: the finite form of the proof of Lemma 6.1. PROVED.
* `lemma61`: Lemma 6.1, (57), CONDITIONAL ON `MinorSup1924 P`, the cited
  Maynard-Pandey-Radziwiłł bound in the consequence form used by the paper.
* `R1_ge_11log2`: R₁(0) ≥ (1 - ε)(11 log 2/50) 2NL eventually, from `lemma43_lower_logP`. PROVED.
* `k6_wired`, `k5_wired`: the chain theorems with the `H` hypotheses discharged.

Unit U-1426, PC run 20261021T1303Z-13145. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1426ChainWire

open Set Real MeasureTheory Filter
open LeanLab.Linnik.U1412Display53 (zL eC norm_zL_le continuous_zL norm_eC)

/-! ### Bridges between the two encodings of Section 5 -/

/-- `U1420Cover.Il` and `LiLiu.Ilam` are the same function, (49). -/
theorem Il_eq_Ilam (l : ℝ) : U1420Cover.Il l = LiLiu.Ilam l := rfl

/-- `U1412Display53.Dl` and `LiLiu.Dl` are the same set, (51). -/
theorem Dl_eq (l : ℝ) : U1412Display53.Dl l = LiLiu.Dl l := by
  ext z
  simp only [U1412Display53.Dl, LiLiu.Dl, mem_ofPred_eq, Complex.normSq_apply,
    U1412Display53.bl, LiLiu.betal, U1412Display53.rl, LiLiu.rl, sq]

lemma rl_nonneg (l : ℝ) : 0 ≤ LiLiu.rl l := by unfold LiLiu.rl; positivity

lemma betal_nonneg (l : ℝ) : 0 ≤ LiLiu.betal l := by
  unfold LiLiu.betal; have := rl_nonneg l; positivity

/-- `β_λ < 1 + r_λ`. -/
lemma betal_lt (l : ℝ) : LiLiu.betal l < 1 + LiLiu.rl l := by
  unfold LiLiu.betal
  have hr := rl_nonneg l
  have : Real.sqrt (LiLiu.rl l ^ 2 + 4 * LiLiu.rl l) < 2 + LiLiu.rl l := by
    rw [Real.sqrt_lt' (by linarith)]; nlinarith
  linarith

lemma Dl_eq_mul (l : ℝ) : LiLiu.Dl l = {z : ℂ | z.re ≤ LiLiu.betal l ∧
    Complex.normSq z * (1 + LiLiu.rl l - z.re) ≤ LiLiu.rl l} := by
  ext z
  simp only [LiLiu.Dl, mem_ofPred_eq]
  have hb := betal_lt l
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (le_div_iff₀ (by linarith)).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (le_div_iff₀ (by linarith)).2 h2⟩

/-- `D_λ` is compact. -/
theorem Dl_compact (l : ℝ) : IsCompact (LiLiu.Dl l) := by
  rw [Dl_eq_mul]
  have hcl : IsClosed {z : ℂ | z.re ≤ LiLiu.betal l ∧
      Complex.normSq z * (1 + LiLiu.rl l - z.re) ≤ LiLiu.rl l} :=
    (isClosed_le Complex.continuous_re continuous_const).inter
      (isClosed_le (Complex.continuous_normSq.mul (continuous_const.sub Complex.continuous_re))
        continuous_const)
  have hb := betal_lt l
  have hr := rl_nonneg l
  set c : ℝ := 1 + LiLiu.rl l - LiLiu.betal l with hc
  have hc0 : 0 < c := by linarith
  refine Metric.isCompact_of_isClosed_isBounded hcl
    ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := Real.sqrt (LiLiu.rl l / c))).subset ?_)
  rintro z ⟨h1, h2⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq, le_div_iff₀ hc0]
  have h0 := Complex.normSq_nonneg z
  nlinarith

lemma zero_mem_Dl (l : ℝ) : (0 : ℂ) ∈ LiLiu.Dl l := by
  refine ⟨by simpa using betal_nonneg l, ?_⟩
  simp only [map_zero, Complex.zero_re, sub_zero]
  exact div_nonneg (rl_nonneg l) (by linarith [rl_nonneg l])

/-- The maximum over `D_λ` of a continuous function is attained. -/
theorem exists_max (l : ℝ) {f : ℂ → ℝ} (hf : Continuous f) :
    ∃ z0 ∈ LiLiu.Dl l, ∀ z ∈ LiLiu.Dl l, f z ≤ f z0 := by
  obtain ⟨z0, hz0, hmax⟩ := (Dl_compact l).exists_isMaxOn ⟨0, zero_mem_Dl l⟩ hf.continuousOn
  exact ⟨z0, hz0, fun z hz => isMaxOn_iff.1 hmax z hz⟩

/-- The exceptional set `E_λ(L)` is measurable. -/
lemma measurableSet_exc (l : ℝ) (L : ℕ) : MeasurableSet {α : ℝ | zL L α ∉ LiLiu.Dl l} :=
  ((Dl_compact l).isClosed.isOpen_compl.preimage (continuous_zL L)).measurableSet

/-! ### Proposition 5.2 at the two parameter pairs of Sections 6 and 7 -/

/-- **Proposition 5.2 for Section 6, PROVED**: `meas E₆ ≤ C e^{-81L/200}`, with
`E₆ = {α ∈ [0,1] : z_L(α) ∉ D_{5/6}}`, using `I(5/6) > 81/200`. -/
theorem exc6 : ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
    (volume.restrict (Icc (0 : ℝ) 1) {α | zL L α ∉ LiLiu.Dl (5 / 6)}).toReal ≤
      C * Real.exp (-(81 / 200) * L) := by
  have h := U1420Moment46.prop52_unconditional (l := 5 / 6) (ρ := 81 / 200) (by norm_num)
    (by norm_num) (by rw [Il_eq_Ilam]; exact LiLiu.I56)
  rw [Dl_eq] at h
  exact h

/-- **Proposition 5.2 for Section 7, PROVED**: `meas E₅ ≤ C e^{-347L/1000}`, `λ = 25/32`. -/
theorem exc5 : ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
    (volume.restrict (Icc (0 : ℝ) 1) {α | zL L α ∉ LiLiu.Dl (25 / 32)}).toReal ≤
      C * Real.exp (-(347 / 1000) * L) := by
  have h := U1420Moment46.prop52_unconditional (l := 25 / 32) (ρ := 347 / 1000) (by norm_num)
    (by norm_num) (by rw [Il_eq_Ilam]; exact LiLiu.I2532)
  rw [Dl_eq] at h
  exact h

/-! ### The maxima H of Sections 6 and 7 -/

/-- `|Q(z)|²` with `Q(z) = z² - z/4 - 1/16`, `a = 1/4`, `b = 1/16`. -/
noncomputable def Q6 (z : ℂ) : ℝ := Complex.normSq (z ^ 2 - z / 4 - 1 / 16)

lemma continuous_Q6 : Continuous Q6 := by unfold Q6; fun_prop

/-- The Section 7 function `|z - 1/8|² + 4 |Q(z)|²`. -/
noncomputable def Q5 (z : ℂ) : ℝ :=
  Complex.normSq (z - 1 / 8) + 4 * Complex.normSq (z ^ 2 - z / 4 - 1 / 16)

lemma continuous_Q5 : Continuous Q5 := by unfold Q5; fun_prop

/-- **H of Section 6, PROVED**: `H = max_{D_{5/6}} |Q|²` exists, `b² ≤ H < 2/15`. -/
theorem exists_H6 : ∃ H : ℝ, (∃ z0 ∈ LiLiu.Dl (5 / 6), Q6 z0 = H) ∧
    (∀ z ∈ LiLiu.Dl (5 / 6), Q6 z ≤ H) ∧ (1 / 16 : ℝ) ^ 2 ≤ H ∧ H < 2 / 15 := by
  obtain ⟨z0, hz0, hmax⟩ := exists_max (5 / 6) continuous_Q6
  refine ⟨Q6 z0, ⟨z0, hz0, rfl⟩, hmax, ?_, LiLiu.region61 z0 hz0⟩
  have h := hmax 0 (zero_mem_Dl _)
  have h0 : Q6 0 = (1 / 16) ^ 2 := by
    simp [Q6, Complex.normSq_apply]; norm_num
  linarith

/-- **H of Section 7, PROVED**: the maximum over `D_{25/32}` exists and is below `41/60`. -/
theorem exists_H5 : ∃ H : ℝ, (∃ z0 ∈ LiLiu.Dl (25 / 32), Q5 z0 = H) ∧
    (∀ z ∈ LiLiu.Dl (25 / 32), Q5 z ≤ H) ∧ 0 ≤ H ∧ H < 41 / 60 := by
  obtain ⟨z0, hz0, hmax⟩ := exists_max (25 / 32) continuous_Q5
  refine ⟨Q5 z0, ⟨z0, hz0, rfl⟩, hmax, ?_, LiLiu.region67 z0 hz0⟩
  unfold Q5
  exact add_nonneg (Complex.normSq_nonneg _) (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))

/-! ### Displays (54) and (56) -/

/-- `G(α) = ∑_{ν=1}^{L} e(2^ν α)`. -/
noncomputable def Gs (L : ℕ) (α : ℝ) : ℂ := ∑ ν ∈ Finset.Icc 1 L, eC (2 ^ ν * α)

lemma continuous_Gs (L : ℕ) : Continuous (Gs L) := by
  unfold Gs
  exact continuous_finsetSum _ fun ν _ =>
    U1412Display53.continuous_eC.comp (continuous_const.mul continuous_id)

/-- `G = L z_L`. -/
lemma Gs_eq {L : ℕ} (hL : 1 ≤ L) (α : ℝ) : Gs L α = L * zL L α := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  unfold zL Gs; rw [← mul_assoc, mul_one_div_cancel hL0, one_mul]

/-- `Q(z) = z² - az - b`. -/
noncomputable def Qc (a b : ℝ) (z : ℂ) : ℂ := z ^ 2 - a * z - b

/-- `F(G(α))` with `F(z) = L² z Q(z/L)`. -/
noncomputable def FG (a b : ℝ) (L : ℕ) (α : ℝ) : ℂ := (L : ℂ) ^ 2 * Gs L α * Qc a b (Gs L α / L)

lemma continuous_FG (a b : ℝ) (L : ℕ) : Continuous (FG a b L) := by
  unfold FG Qc
  have := continuous_Gs L
  fun_prop

lemma FG_eq (a b : ℝ) {L : ℕ} (hL : 1 ≤ L) (α : ℝ) :
    FG a b L α = (L : ℂ) ^ 3 * zL L α * Qc a b (zL L α) := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  unfold FG; rw [Gs_eq hL, mul_div_cancel_left₀ _ hL0]; ring

/-- **Display (54), PROVED**: if `f ≤ H` on `D_λ`, then `α ∉ E_λ(L)` gives `f(z_L(α)) ≤ H`. -/
theorem display54 {l H : ℝ} {f : ℂ → ℝ} (hH : ∀ z ∈ LiLiu.Dl l, f z ≤ H) {L : ℕ} {α : ℝ}
    (hα : α ∉ {α : ℝ | zL L α ∉ LiLiu.Dl l}) : f (zL L α) ≤ H := by
  simp only [mem_ofPred_eq, not_not] at hα
  exact hH _ hα

/-- Display (54) for Section 6, with the paper's `H`. -/
theorem display54_K6 : ∃ H : ℝ, (∀ z ∈ LiLiu.Dl (5 / 6), Q6 z ≤ H) ∧ (1 / 16 : ℝ) ^ 2 ≤ H ∧
    H < 2 / 15 ∧ ∀ L : ℕ, ∀ α : ℝ, α ∉ {α : ℝ | zL L α ∉ LiLiu.Dl (5 / 6)} → Q6 (zL L α) ≤ H := by
  obtain ⟨H, -, hmax, hb, hH⟩ := exists_H6
  exact ⟨H, hmax, hb, hH, fun L α hα => display54 hmax hα⟩

lemma Qc6 (z : ℂ) : Qc (1 / 4) (1 / 16) z = z ^ 2 - z / 4 - 1 / 16 := by
  unfold Qc; push_cast; ring

/-- The pointwise form of (56): off `E₆`, `|S F(G)|² ≤ H L⁴ |S G|²`. -/
theorem display56_pt {H : ℝ} (hH : ∀ z ∈ LiLiu.Dl (5 / 6), Q6 z ≤ H) {L : ℕ} (hL : 1 ≤ L)
    (s : ℂ) {α : ℝ} (hα : zL L α ∈ LiLiu.Dl (5 / 6)) :
    ‖s * FG (1 / 4) (1 / 16) L α‖ ^ 2 ≤ H * (L : ℝ) ^ 4 * ‖s * Gs L α‖ ^ 2 := by
  rw [FG_eq _ _ hL, Gs_eq hL, Qc6]
  have hq := hH _ hα
  unfold Q6 at hq
  rw [Complex.normSq_eq_norm_sq] at hq
  simp only [norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
  have h1 : 0 ≤ ‖s‖ ^ 2 * ((L : ℝ) ^ 3) ^ 2 * ‖zL L α‖ ^ 2 := by positivity
  calc _ = ‖s‖ ^ 2 * ((L : ℝ) ^ 3) ^ 2 * ‖zL L α‖ ^ 2 * ‖zL L α ^ 2 - zL L α / 4 - 1 / 16‖ ^ 2 := by
        ring
    _ ≤ ‖s‖ ^ 2 * ((L : ℝ) ^ 3) ^ 2 * ‖zL L α‖ ^ 2 * H := mul_le_mul_of_nonneg_left hq h1
    _ = _ := by ring

/-- **Display (56), PROVED**: for any measurable `m ⊆ [0,1]` and continuous `S`,
`∫_{m \ E₆} |S F(G)|² ≤ H L⁴ ∫_m |S G|²`. -/
theorem display56 {H : ℝ} (hH : ∀ z ∈ LiLiu.Dl (5 / 6), Q6 z ≤ H) {L : ℕ} (hL : 1 ≤ L)
    {S : ℝ → ℂ} (hS : Continuous S) {m : Set ℝ} (hm : MeasurableSet m)
    (hm1 : m ⊆ Icc 0 1) :
    ∫ α in m \ {α | zL L α ∉ LiLiu.Dl (5 / 6)}, ‖S α * FG (1 / 4) (1 / 16) L α‖ ^ 2 ≤
      H * (L : ℝ) ^ 4 * ∫ α in m, ‖S α * Gs L α‖ ^ 2 := by
  have hE := measurableSet_exc (5 / 6) L
  have hc1 : Continuous fun α => ‖S α * FG (1 / 4) (1 / 16) L α‖ ^ 2 :=
    ((hS.mul (continuous_FG _ _ L)).norm.pow 2)
  have hc2 : Continuous fun α => ‖S α * Gs L α‖ ^ 2 := ((hS.mul (continuous_Gs L)).norm.pow 2)
  have hsub : m \ {α | zL L α ∉ LiLiu.Dl (5 / 6)} ⊆ Icc 0 1 := sdiff_subset.trans hm1
  rw [← integral_const_mul]
  calc ∫ α in m \ {α | zL L α ∉ LiLiu.Dl (5 / 6)}, ‖S α * FG (1 / 4) (1 / 16) L α‖ ^ 2
      ≤ ∫ α in m \ {α | zL L α ∉ LiLiu.Dl (5 / 6)}, H * (L : ℝ) ^ 4 * ‖S α * Gs L α‖ ^ 2 := by
        refine setIntegral_mono_on (hc1.integrableOn_Icc.mono_set hsub)
          ((hc2.integrableOn_Icc.mono_set hsub).const_mul _) (hm.diff hE) ?_
        intro α hα
        have : zL L α ∈ LiLiu.Dl (5 / 6) := by
          have := hα.2; simpa using this
        exact display56_pt hH hL _ this
    _ ≤ ∫ α in m, H * (L : ℝ) ^ 4 * ‖S α * Gs L α‖ ^ 2 := by
        have hH0 : 0 ≤ H := le_trans (Complex.normSq_nonneg _) (hH 0 (zero_mem_Dl _))
        refine setIntegral_mono_set ((hc2.integrableOn_Icc.mono_set hm1).const_mul _)
          (ae_of_all _ fun α => mul_nonneg (mul_nonneg hH0 (by positivity)) (by positivity))
          (Eventually.of_forall sdiff_subset)

/-! ### Parseval on [0, 1] -/

open LeanLab.Linnik.LiLiuLemma43 (SA)
open LeanLab.Linnik.LiLiuDisplay37 (primesIn logw)

lemma integral_cos_int (k : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * k * x) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hc : (2 * π * k : ℝ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hk'
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
    have : Real.sin (2 * π * k) = 0 := by
      rw [show 2 * π * (k : ℝ) = ((2 * k : ℤ) : ℝ) * π by push_cast; ring]
      exact Real.sin_int_mul_pi _
    simp [this]

/-- **Parseval, PROVED**: `∫_0^1 |∑_{n ∈ A} a_n e(nβ)|² dβ = ∑_{n ∈ A} a_n²`. -/
theorem parseval (A : Finset ℕ) (a : ℕ → ℝ) :
    ∫ β in Icc (0 : ℝ) 1, ‖SA A (fun n => (a n : ℂ)) β‖ ^ 2 = ∑ n ∈ A, a n ^ 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  simp_rw [LiLiuDisplay37.normSq_expand]
  have hc : ∀ m n : ℕ, Continuous
      (fun β : ℝ => a m * a n * Real.cos ((2 * π * ((m : ℝ) - n)) * β)) :=
    fun m n => by fun_prop
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    (continuous_finsetSum _ fun n _ => hc m n).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [intervalIntegral.integral_finsetSum fun n _ => (hc m n).intervalIntegrable _ _]
  have h1 : ∀ n ∈ A, ∫ β in (0 : ℝ)..1, a m * a n * Real.cos ((2 * π * ((m : ℝ) - n)) * β) =
      if m = n then a m * a n else 0 := by
    intro n _
    rw [intervalIntegral.integral_const_mul]
    have := integral_cos_int ((m : ℤ) - n)
    push_cast at this
    rw [this]
    by_cases hmn : m = n
    · subst hmn; simp
    · have : (m : ℤ) - n ≠ 0 := by omega
      simp [this, hmn]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq A m (fun n => a m * a n)]
  simp [hm, sq]

/-! ### The proof of Lemma 6.1, finite form -/

/-- `S_{≤X}(α) = ∑_{p ≤ X} log p e(pα)`. -/
noncomputable def Sle (X : ℕ) : ℝ → ℂ := SA (primesIn 0 X) logw

/-- `S(α) = ∑_{N₁ < p ≤ N} log p e(pα)`, the paper's S with `N₁ = N1`. -/
noncomputable def Sm (N1 N : ℕ) : ℝ → ℂ := SA (primesIn N1 N) logw

lemma continuous_SA (A : Finset ℕ) (w : ℕ → ℂ) : Continuous (SA A w) :=
  LeanLab.Linnik.LiLiuLemma43Int.SA_continuous A w

lemma Sm_eq {N1 N : ℕ} (h : N1 ≤ N) (α : ℝ) : Sm N1 N α = Sle N α - Sle N1 α := by
  unfold Sm Sle SA primesIn
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N1) h]
  ring

lemma norm_Qc_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Qc a b z‖ ≤ 1 + a + b := by
  unfold Qc
  have h1 : ‖(a : ℂ) * z‖ = a * ‖z‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]
  have h2 : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb]
  have h3 : ‖z ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  calc ‖z ^ 2 - a * z - b‖ ≤ ‖z ^ 2 - a * z‖ + ‖(b : ℂ)‖ := norm_sub_le _ _
    _ ≤ ‖z ^ 2‖ + ‖(a : ℂ) * z‖ + ‖(b : ℂ)‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ 1 + a + b := by rw [h1, h2]; nlinarith [norm_nonneg z]

/-- Step 1 of the proof of Lemma 6.1: `|F(G(α))| ≤ (1 + a + b) L³`. -/
lemma norm_FG_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {L : ℕ} (hL : 1 ≤ L) (α : ℝ) :
    ‖FG a b L α‖ ≤ (1 + a + b) * (L : ℝ) ^ 3 := by
  rw [FG_eq _ _ hL, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  have hz := norm_zL_le hL α
  have hq := norm_Qc_le ha hb hz
  have : ‖zL L α‖ * ‖Qc a b (zL L α)‖ ≤ 1 * (1 + a + b) :=
    mul_le_mul hz hq (norm_nonneg _) zero_le_one
  have hL3 : (0 : ℝ) ≤ (L : ℝ) ^ 3 := by positivity
  nlinarith

lemma norm_sub_sq_le (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have := norm_sub_le x y
  nlinarith [norm_nonneg (x - y), norm_nonneg x, norm_nonneg y, sq_nonneg (‖x‖ - ‖y‖)]

/-- `∑_{p ≤ X} (log p)² ≤ log N · log 4 · X` for `X ≤ N`, Chebyshev's bound. -/
lemma sum_log_sq_le {X N : ℕ} (hXN : X ≤ N) :
    ∑ p ∈ primesIn 0 X, Real.log p ^ 2 ≤ Real.log N * (Real.log 4 * X) := by
  have hθ : ∑ p ∈ primesIn 0 X, Real.log p = Chebyshev.theta X := by
    rw [LiLiuDisplay37.sum_primesIn (Nat.zero_le X)]; simp [Chebyshev.theta_zero]
  have hle : ∀ p ∈ primesIn 0 X, Real.log p ^ 2 ≤ Real.log N * Real.log p := by
    intro p hp
    simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.one_lt.le
    have h0 : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hpN : (p : ℝ) ≤ N := by exact_mod_cast hp.1.2.trans hXN
    have : Real.log p ≤ Real.log N := Real.log_le_log (by linarith) hpN
    nlinarith
  have hN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  calc ∑ p ∈ primesIn 0 X, Real.log p ^ 2 ≤ ∑ p ∈ primesIn 0 X, Real.log N * Real.log p :=
        Finset.sum_le_sum hle
    _ = Real.log N * Chebyshev.theta X := by rw [← Finset.mul_sum, hθ]
    _ ≤ Real.log N * (Real.log 4 * X) :=
        mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)) hN

/-- **The proof of Lemma 6.1, finite form, PROVED.** For `a, b ≥ 0`, `L ≥ 1`, `N₁ ≤ N`, a
measurable `m ⊆ [0,1]` on which `|S_{≤N}| ≤ B`:
`∫_{m ∩ E₆} |S F(G)|² ≤ 2(1+a+b)² L⁶ (B² meas E₆ + ∑_{p ≤ N₁} (log p)²)`. -/
theorem lemma61_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {L : ℕ} (hL : 1 ≤ L) {N1 N : ℕ}
    (hN : N1 ≤ N) {m : Set ℝ} (hm : MeasurableSet m) (hm1 : m ⊆ Icc 0 1) {B : ℝ}
    (hB : ∀ α ∈ m, ‖Sle N α‖ ≤ B) :
    ∫ α in m ∩ {α | zL L α ∉ LiLiu.Dl (5 / 6)}, ‖Sm N1 N α * FG a b L α‖ ^ 2 ≤
      2 * (1 + a + b) ^ 2 * (L : ℝ) ^ 6 *
        (B ^ 2 * (volume.restrict (Icc (0 : ℝ) 1) {α | zL L α ∉ LiLiu.Dl (5 / 6)}).toReal +
          ∑ p ∈ primesIn 0 N1, Real.log p ^ 2) := by
  set E := {α : ℝ | zL L α ∉ LiLiu.Dl (5 / 6)} with hEdef
  have hE : MeasurableSet E := measurableSet_exc (5 / 6) L
  set K : ℝ := 2 * (1 + a + b) ^ 2 * (L : ℝ) ^ 6 with hK
  have hK0 : 0 ≤ K := by positivity
  have hsub : m ∩ E ⊆ Icc 0 1 := inter_subset_left.trans hm1
  have cN := continuous_SA (primesIn 0 N) logw
  have cN1 := continuous_SA (primesIn 0 N1) logw
  have c1 : Continuous fun α => ‖Sm N1 N α * FG a b L α‖ ^ 2 :=
    ((continuous_SA _ _).mul (continuous_FG a b L)).norm.pow 2
  have c2 : Continuous fun α => ‖Sle N α‖ ^ 2 := cN.norm.pow 2
  have c3 : Continuous fun α => ‖Sle N1 α‖ ^ 2 := cN1.norm.pow 2
  have hpt : ∀ α, ‖Sm N1 N α * FG a b L α‖ ^ 2 ≤ K * (‖Sle N α‖ ^ 2 + ‖Sle N1 α‖ ^ 2) := by
    intro α
    have hF := norm_FG_le ha hb hL α
    have hF2 : ‖FG a b L α‖ ^ 2 ≤ ((1 + a + b) * (L : ℝ) ^ 3) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hF 2
    have hS := norm_sub_sq_le (Sle N α) (Sle N1 α)
    rw [← Sm_eq hN] at hS
    rw [norm_mul, mul_pow]
    calc ‖Sm N1 N α‖ ^ 2 * ‖FG a b L α‖ ^ 2
        ≤ (2 * (‖Sle N α‖ ^ 2 + ‖Sle N1 α‖ ^ 2)) * ((1 + a + b) * (L : ℝ) ^ 3) ^ 2 :=
          mul_le_mul hS hF2 (by positivity) (by positivity)
      _ = K * (‖Sle N α‖ ^ 2 + ‖Sle N1 α‖ ^ 2) := by rw [hK]; ring
  have i2 : IntegrableOn (fun α => ‖Sle N α‖ ^ 2) (m ∩ E) := c2.integrableOn_Icc.mono_set hsub
  have i3 : IntegrableOn (fun α => ‖Sle N1 α‖ ^ 2) (m ∩ E) := c3.integrableOn_Icc.mono_set hsub
  have step1 : ∫ α in m ∩ E, ‖Sm N1 N α * FG a b L α‖ ^ 2 ≤
      K * ((∫ α in m ∩ E, ‖Sle N α‖ ^ 2) + ∫ α in m ∩ E, ‖Sle N1 α‖ ^ 2) := by
    rw [← integral_add i2 i3, ← integral_const_mul]
    exact setIntegral_mono (c1.integrableOn_Icc.mono_set hsub) ((i2.add i3).const_mul K) hpt
  have hfin : volume (m ∩ E) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (measure_mono hsub)
  have step2 : ∫ α in m ∩ E, ‖Sle N α‖ ^ 2 ≤
      B ^ 2 * (volume.restrict (Icc (0 : ℝ) 1) E).toReal := by
    have hB2 : ∀ α ∈ m ∩ E, ‖Sle N α‖ ^ 2 ≤ B ^ 2 := fun α hα =>
      pow_le_pow_left₀ (norm_nonneg _) (hB α hα.1) 2
    have h1 := setIntegral_mono_on i2 (integrableOn_const hfin) (hm.inter hE) hB2
    rw [setIntegral_const, smul_eq_mul, Measure.real] at h1
    have hmono : (volume (m ∩ E)).toReal ≤ (volume.restrict (Icc (0 : ℝ) 1) E).toReal := by
      rw [Measure.restrict_apply hE]
      refine ENNReal.toReal_mono ?_ (measure_mono ?_)
      · exact ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          (measure_mono inter_subset_right)
      · exact fun α hα => ⟨hα.2, hm1 hα.1⟩
    have hB0 : 0 ≤ B ^ 2 := sq_nonneg B
    nlinarith
  have step3 : ∫ α in m ∩ E, ‖Sle N1 α‖ ^ 2 ≤ ∑ p ∈ primesIn 0 N1, Real.log p ^ 2 := by
    rw [← parseval (primesIn 0 N1) (fun n => Real.log n)]
    exact setIntegral_mono_set c3.integrableOn_Icc (ae_of_all _ fun α => by positivity)
      (Eventually.of_forall hsub)
  calc ∫ α in m ∩ E, ‖Sm N1 N α * FG a b L α‖ ^ 2
      ≤ K * ((∫ α in m ∩ E, ‖Sle N α‖ ^ 2) + ∫ α in m ∩ E, ‖Sle N1 α‖ ^ 2) := step1
    _ ≤ K * (B ^ 2 * (volume.restrict (Icc (0 : ℝ) 1) E).toReal +
          ∑ p ∈ primesIn 0 N1, Real.log p ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add step2 step3) hK0

/-! ### Lemma 6.1, display (57), asymptotic form -/

open LeanLab.PNTPort.LargeSieve (dist0)

lemma measurable_dist0 : Measurable dist0 := by
  have hr : Measurable (fun x : ℝ => ((round x : ℤ) : ℝ)) := by
    have : (fun x : ℝ => ((round x : ℤ) : ℝ)) =
        (fun k : ℤ => (k : ℝ)) ∘ (fun x : ℝ => ⌊x + 1 / 2⌋) := by
      funext x; simp [round_eq]
    rw [this]
    exact (measurable_of_countable _).comp (Int.measurable_floor.comp (measurable_id.add_const _))
  unfold dist0
  exact (measurable_id.sub hr).abs

/-- The major arcs (25) are measurable. -/
theorem measurableSet_majorArcs (P N : ℝ) :
    MeasurableSet (LiLiuLemma43Int.majorArcs P N) := by
  have : LiLiuLemma43Int.majorArcs P N = Ioc 0 1 ∩ ⋃ q ∈ Finset.Icc 1 ⌊P⌋₊,
      ⋃ r ∈ LiLiuLemma43.units q, {α : ℝ | dist0 (α - (r : ℝ) / q) ≤ P / (q * N)} := by
    ext α
    simp only [LiLiuLemma43Int.majorArcs, mem_ofPred_eq, mem_inter_iff, mem_iUnion,
      exists_prop]
  rw [this]
  exact measurableSet_Ioc.inter (Finset.measurableSet_biUnion _ fun q _ =>
    Finset.measurableSet_biUnion _ fun r _ =>
      measurableSet_le (measurable_dist0.comp (measurable_id.sub_const _)) measurable_const)

/-- The minor arcs `𝔪 = (0,1] \ 𝔐`. -/
def minorArcs (P N : ℝ) : Set ℝ := Ioc 0 1 \ LiLiuLemma43Int.majorArcs P N

lemma measurableSet_minorArcs (P N : ℝ) : MeasurableSet (minorArcs P N) :=
  measurableSet_Ioc.diff (measurableSet_majorArcs P N)

lemma minorArcs_sub (P N : ℝ) : minorArcs P N ⊆ Icc 0 1 :=
  sdiff_subset.trans Ioc_subset_Icc_self

/-- `L = ⌊log₂ N - √(log₂ N)⌋`, display (2). -/
noncomputable def Lfun (N : ℕ) : ℕ := ⌊Real.logb 2 N - Real.sqrt (Real.logb 2 N)⌋₊

/-- **The Maynard-Pandey-Radziwiłł input, cited**, in the consequence form the proof of
Lemma 6.1 uses: `sup_{α ∈ 𝔪} |S_{≤N}(α)| ≪ N^{19/24 + o(1)}`. The paper derives it from
[16, Thm 1.1], `N^{o(1)}(N P^{-1/2} + N^{19/24}) + N^{1/2} log² N`, and `P ≥ N^{11/25}`. -/
def MinorSup1924 (P : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ α ∈ minorArcs (P N) N,
    ‖Sle N α‖ ≤ C * (N : ℝ) ^ ((19 : ℝ) / 24 + ε)

lemma Lfun_lower (N : ℕ) :
    Real.logb 2 N - Real.sqrt (Real.logb 2 N) - 1 < Lfun N := by
  have := Nat.lt_floor_add_one (Real.logb 2 N - Real.sqrt (Real.logb 2 N))
  unfold Lfun; linarith

lemma Lfun_le {N : ℕ} (hN : 1 ≤ N) : (Lfun N : ℝ) ≤ Real.logb 2 N := by
  have ht : 0 ≤ Real.logb 2 N :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hN)
  unfold Lfun
  rcases le_or_gt 0 (Real.logb 2 N - Real.sqrt (Real.logb 2 N)) with h | h
  · exact (Nat.floor_le h).trans (by linarith [Real.sqrt_nonneg (Real.logb 2 N)])
  · rw [Nat.floor_of_nonpos h.le]; simpa using ht

lemma eventually_Lfun_ge_one : ∀ᶠ N : ℕ in atTop, 1 ≤ Lfun N := by
  have ht : Tendsto (fun N : ℕ => Real.logb 2 N) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop 4] with N hN
  unfold Lfun
  apply Nat.le_floor
  set t := Real.logb 2 N
  have hs : Real.sqrt t ≤ t / 2 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  push_cast; linarith

lemma rpow_sq_eq (C : ℝ) {x : ℝ} (hx : 0 < x) (s : ℝ) :
    (C * x ^ s) ^ 2 = C ^ 2 * Real.exp (2 * s * Real.log x) := by
  rw [mul_pow, Real.rpow_def_of_pos hx, sq (Real.exp _), ← Real.exp_add]
  ring_nf

/-- The exponent count of the proof of Lemma 6.1: with `t = u / log 2`, `L > t - √t - 1`,
`ρ / log 2 = 7/12 + η` and `u` large, `2(19/24 + η/4) u - ρ L ≤ u - (η/4) u`. -/
lemma exponent_le {η ρ u t Lr : ℝ} (hη0 : 0 < η) (hρ0 : 0 < ρ)
    (htu : t = u / Real.log 2) (hγ : ρ / Real.log 2 = 7 / 12 + η) (hu0 : 0 < u)
    (hsq : 8 * ρ / (η * Real.log 2) ≤ Real.sqrt t) (hu1 : 8 * ρ / η ≤ u)
    (hL : t - Real.sqrt t - 1 < Lr) :
    2 * (19 / 24 + η / 4) * u - ρ * Lr ≤ u - η / 4 * u := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht0 : 0 < t := by rw [htu]; positivity
  have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have hρt : ρ * t = (7 / 12 + η) * u := by
    rw [htu, ← hγ]; ring
  have hρsq : ρ * Real.sqrt t ≤ η / 8 * u := by
    have hc0 : 0 < 8 * ρ / (η * Real.log 2) := by positivity
    have e : 8 * ρ / (η * Real.log 2) * (η / 8 * u) = ρ * t := by
      rw [htu]; field_simp
    have h1 : 8 * ρ / (η * Real.log 2) * (ρ * Real.sqrt t) ≤
        8 * ρ / (η * Real.log 2) * (η / 8 * u) := by
      rw [e]
      calc 8 * ρ / (η * Real.log 2) * (ρ * Real.sqrt t)
          = ρ * (Real.sqrt t * (8 * ρ / (η * Real.log 2))) := by ring
        _ ≤ ρ * (Real.sqrt t * Real.sqrt t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)) hρ0.le
        _ = ρ * t := by rw [hst]
    exact le_of_mul_le_mul_left h1 hc0
  have hρu : ρ ≤ η / 8 * u := by
    have := (div_le_iff₀ hη0).1 hu1
    linarith
  have h2 : ρ * (t - Real.sqrt t - 1) ≤ ρ * Lr := mul_le_mul_of_nonneg_left hL.le hρ0.le
  nlinarith

lemma term_le {A δ x d N : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) (hN : 0 ≤ N) (hx : x ≤ N * d)
    (hd : d = δ / (2 * (A + 1))) : A * x ≤ δ / 2 * N := by
  have h1 : A * d ≤ δ / 2 := by
    rw [hd, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc A * x ≤ A * (N * d) := mul_le_mul_of_nonneg_left hx hA
    _ = N * (A * d) := by ring
    _ ≤ N * (δ / 2) := mul_le_mul_of_nonneg_left h1 hN
    _ = δ / 2 * N := by ring

/-- **Lemma 6.1, display (57), CONDITIONAL ON `MinorSup1924 P`.** For `κ > 0`, fixed
`a, b ≥ 0`, `N₁ = ⌊N^{1-κ}⌋`, `L = ⌊log₂ N - √(log₂ N)⌋`:
`∫_{𝔪 ∩ E₆} |S(α) F(G(α))|² dα = o(N L⁶)`. The paper's `a + b < 1` is not needed here. -/
theorem lemma61 {κ : ℝ} (hκ : 0 < κ) (P : ℕ → ℝ) (hM : MinorSup1924 P) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
      ∫ α in minorArcs (P N) N ∩ {α | zL (Lfun N) α ∉ LiLiu.Dl (5 / 6)},
        ‖Sm ⌊(N : ℝ) ^ (1 - κ)⌋₊ N α * FG a b (Lfun N) α‖ ^ 2 ≤ δ * N * (Lfun N : ℝ) ^ 6 := by
  intro δ hδ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨η, hη0, hγ⟩ : ∃ η : ℝ, 0 < η ∧ (81 / 200 : ℝ) / Real.log 2 = 7 / 12 + η := by
    refine ⟨81 / 200 / Real.log 2 - 7 / 12, ?_, by ring⟩
    have h := LiLiu.gamma6.2
    have : (81 / 200 : ℝ) / Real.log 2 = 81 / (200 * Real.log 2) := by field_simp
    rw [this]; linarith
  obtain ⟨C, hC⟩ := hM (η / 4) (by positivity)
  obtain ⟨C0, hC00, hC0⟩ := exc6
  obtain ⟨K, hK, hK0⟩ : ∃ K : ℝ, K = 2 * (1 + a + b) ^ 2 ∧ 0 ≤ K := ⟨_, rfl, by positivity⟩
  have hA10 : 0 ≤ K * C ^ 2 * C0 := by positivity
  have hA20 : 0 ≤ K * Real.log 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity
  have hu : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => Real.logb 2 N) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ κ) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hκ).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨d1, hd1, hd10⟩ : ∃ d1 : ℝ, d1 = δ / (2 * (K * C ^ 2 * C0 + 1)) ∧ 0 < d1 :=
    ⟨_, rfl, by positivity⟩
  obtain ⟨d2, hd2, hd20⟩ : ∃ d2 : ℝ, d2 = δ / (2 * (K * Real.log 4 + 1)) ∧ 0 < d2 :=
    ⟨_, rfl, by positivity⟩
  filter_upwards [hC, eventually_Lfun_ge_one, eventually_ge_atTop 2,
    hu.eventually_ge_atTop (8 * (81 / 200) / η),
    hu.eventually_ge_atTop (-(4 / η) * Real.log d1),
    ht.eventually_ge_atTop ((8 * (81 / 200) / (η * Real.log 2)) ^ 2),
    (tendsto_order.1 hlo).2 d2 hd20]
    with N hCN hL hN2 hu1 hu2 ht1 hlo1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hu0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpow : (N : ℝ) ^ (1 - κ) ≤ N := by
    calc (N : ℝ) ^ (1 - κ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one _
  have hN1N : ⌊(N : ℝ) ^ (1 - κ)⌋₊ ≤ N := Nat.floor_le_of_le hpow
  have hN1le : (⌊(N : ℝ) ^ (1 - κ)⌋₊ : ℝ) ≤ (N : ℝ) ^ (1 - κ) := Nat.floor_le (by positivity)
  have hB := lemma61_bound ha hb hL hN1N (measurableSet_minorArcs (P N) N)
    (minorArcs_sub (P N) N) hCN
  have hE := hC0 (Lfun N) hL
  have hsum := sum_log_sq_le hN1N
  have hμ0 : 0 ≤ (volume.restrict (Icc (0 : ℝ) 1)
      {α | zL (Lfun N) α ∉ LiLiu.Dl (5 / 6)}).toReal := ENNReal.toReal_nonneg
  have hsq : 8 * (81 / 200) / (η * Real.log 2) ≤ Real.sqrt (Real.logb 2 N) := by
    rw [show 8 * (81 / 200) / (η * Real.log 2) =
      Real.sqrt ((8 * (81 / 200) / (η * Real.log 2)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt ht1
  have hexp := exponent_le hη0 (by norm_num : (0 : ℝ) < 81 / 200) rfl hγ hu0 hsq hu1
    (Lfun_lower N)
  have hd1u : Real.exp (-(η / 4) * Real.log N) ≤ d1 := by
    rw [← Real.exp_log hd10]
    apply Real.exp_le_exp.2
    have h := mul_le_mul_of_nonneg_left hu2 (show 0 ≤ η / 4 by positivity)
    have e : η / 4 * (-(4 / η) * Real.log d1) = -Real.log d1 := by field_simp
    rw [e] at h
    linarith
  -- term 1
  have hT1 : K * ((C * (N : ℝ) ^ ((19 : ℝ) / 24 + η / 4)) ^ 2 *
      (volume.restrict (Icc (0 : ℝ) 1) {α | zL (Lfun N) α ∉ LiLiu.Dl (5 / 6)}).toReal) ≤
      δ / 2 * N := by
    rw [rpow_sq_eq C hNpos]
    have h2 : Real.exp (2 * ((19 : ℝ) / 24 + η / 4) * Real.log N) *
        Real.exp (-(81 / 200) * (Lfun N : ℝ)) ≤ N * d1 := by
      rw [← Real.exp_add]
      calc Real.exp (2 * ((19 : ℝ) / 24 + η / 4) * Real.log N + -(81 / 200) * (Lfun N : ℝ))
          ≤ Real.exp (Real.log N + -(η / 4) * Real.log N) :=
            Real.exp_le_exp.2 (by linarith)
        _ = N * Real.exp (-(η / 4) * Real.log N) := by
            rw [Real.exp_add, Real.exp_log hNpos]
        _ ≤ N * d1 := mul_le_mul_of_nonneg_left hd1u hNpos.le
    have h3 := term_le hA10 hδ hNpos.le h2 hd1
    have h4 := mul_le_mul_of_nonneg_left hE
      (show 0 ≤ K * (C ^ 2 * Real.exp (2 * ((19 : ℝ) / 24 + η / 4) * Real.log N)) by
        positivity)
    calc _ = K * (C ^ 2 * Real.exp (2 * ((19 : ℝ) / 24 + η / 4) * Real.log N)) *
          (volume.restrict (Icc (0 : ℝ) 1) {α | zL (Lfun N) α ∉ LiLiu.Dl (5 / 6)}).toReal := by
          ring
      _ ≤ K * (C ^ 2 * Real.exp (2 * ((19 : ℝ) / 24 + η / 4) * Real.log N)) *
          (C0 * Real.exp (-(81 / 200) * (Lfun N : ℝ))) := h4
      _ = K * C ^ 2 * C0 * (Real.exp (2 * ((19 : ℝ) / 24 + η / 4) * Real.log N) *
          Real.exp (-(81 / 200) * (Lfun N : ℝ))) := by ring
      _ ≤ δ / 2 * N := h3
  -- term 2
  have hT2 : K * ∑ p ∈ primesIn 0 ⌊(N : ℝ) ^ (1 - κ)⌋₊, Real.log p ^ 2 ≤ δ / 2 * N := by
    have h1 : (⌊(N : ℝ) ^ (1 - κ)⌋₊ : ℝ) * Real.log N ≤ N * d2 := by
      have hk : (N : ℝ) ^ (1 - κ) = N / (N : ℝ) ^ κ := by
        rw [Real.rpow_sub hNpos, Real.rpow_one]
      calc (⌊(N : ℝ) ^ (1 - κ)⌋₊ : ℝ) * Real.log N ≤ (N : ℝ) ^ (1 - κ) * Real.log N :=
            mul_le_mul_of_nonneg_right hN1le hu0.le
        _ = N * (Real.log N / (N : ℝ) ^ κ) := by rw [hk]; ring
        _ ≤ N * d2 := mul_le_mul_of_nonneg_left hlo1.le hNpos.le
    have h3 := term_le hA20 hδ hNpos.le h1 hd2
    calc K * ∑ p ∈ primesIn 0 ⌊(N : ℝ) ^ (1 - κ)⌋₊, Real.log p ^ 2
        ≤ K * (Real.log N * (Real.log 4 * ⌊(N : ℝ) ^ (1 - κ)⌋₊)) :=
          mul_le_mul_of_nonneg_left hsum hK0
      _ = K * Real.log 4 * (⌊(N : ℝ) ^ (1 - κ)⌋₊ * Real.log N) := by ring
      _ ≤ δ / 2 * N := h3
  have hL6 : (0 : ℝ) ≤ (Lfun N : ℝ) ^ 6 := by positivity
  refine hB.trans ?_
  rw [← hK]
  calc K * (Lfun N : ℝ) ^ 6 * ((C * (N : ℝ) ^ ((19 : ℝ) / 24 + η / 4)) ^ 2 *
        (volume.restrict (Icc (0 : ℝ) 1) {α | zL (Lfun N) α ∉ LiLiu.Dl (5 / 6)}).toReal +
        ∑ p ∈ primesIn 0 ⌊(N : ℝ) ^ (1 - κ)⌋₊, Real.log p ^ 2)
      = (Lfun N : ℝ) ^ 6 * (K * ((C * (N : ℝ) ^ ((19 : ℝ) / 24 + η / 4)) ^ 2 *
        (volume.restrict (Icc (0 : ℝ) 1) {α | zL (Lfun N) α ∉ LiLiu.Dl (5 / 6)}).toReal) +
        K * ∑ p ∈ primesIn 0 ⌊(N : ℝ) ^ (1 - κ)⌋₊, Real.log p ^ 2) := by ring
    _ ≤ (Lfun N : ℝ) ^ 6 * (δ / 2 * N + δ / 2 * N) :=
        mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) hL6
    _ = δ * N * (Lfun N : ℝ) ^ 6 := by ring

/-- Vacuity of `MinorSup1924`: with `P(N) = N` the minor arcs are empty, since `q = 1`,
`r = 0` covers `(0,1]`. Outside the paper's range `P ≤ N^{4/9}`; it shows only that the
Prop is satisfiable. -/
theorem minorSup_trivial : MinorSup1924 (fun N => (N : ℝ)) := by
  intro ε _
  refine ⟨0, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN α hα
  exfalso
  apply hα.2
  refine ⟨hα.1, 1, ?_, 0, ?_, ?_⟩
  · simp only [Finset.mem_Icc, le_refl, true_and]
    exact Nat.le_floor (by exact_mod_cast hN)
  · simp [LiLiuLemma43.units]
  · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := LeanLab.PNTPort.LargeSieve.dist0_le_half (α - ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ))
    have h1 : (N : ℝ) / (((1 : ℕ) : ℝ) * N) = 1 := by
      rw [Nat.cast_one, one_mul, div_self (ne_of_gt (by linarith))]
    rw [h1]; linarith

/-! ### Lemma 4.3 in the form used before (58) -/

/-- **R₁(0)/(2NL) ≥ 11 log 2/50 + o(1), PROVED**, from `U1412MuPhi.lemma43_lower_logP` and
`P ≥ N^{11/25}`, (24): for `0 < ε < 1`, eventually
`R₁(0) ≥ (1 - ε)(11 log 2/50) · 2 N L`, `L = ⌊log₂ N - √(log₂ N)⌋`. -/
theorem R1_ge_11log2 {κ : ℝ} (hκ : 0 < κ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (P : ℕ → ℝ) (hP11 : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N)
    (hPup : ∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ))
    (hP2 : ∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) :
    ∀ᶠ N : ℕ in atTop, (1 - ε) * (11 * Real.log 2 / 50) * (2 * N * (Lfun N : ℝ)) ≤
      LiLiuLemma43Int.R10 (primesIn ⌊(N : ℝ) ^ (1 - κ)⌋₊ N) logw (P N) N := by
  have hlow : Tendsto (fun N : ℕ => (N : ℝ) ^ ((11 : ℝ) / 25)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hP : Tendsto P atTop atTop := tendsto_atTop_mono' atTop hP11 hlow
  filter_upwards [U1412MuPhi.lemma43_lower_logP hκ hε hε1 P hP hPup hP2, hP11,
    eventually_ge_atTop 1] with N hN h11 hN1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogP : 11 / 25 * Real.log N ≤ Real.log (P N) := by
    rw [← Real.log_rpow hNpos]
    exact Real.log_le_log (by positivity) h11
  have hL := Lfun_le hN1
  have hLlog : (Lfun N : ℝ) * Real.log 2 ≤ Real.log N := by
    have : Real.logb 2 N * Real.log 2 = Real.log N := by
      rw [Real.logb, div_mul_cancel₀ _ hl2.ne']
    nlinarith
  have hkey : 11 * Real.log 2 / 50 * (2 * (Lfun N : ℝ)) ≤ Real.log (P N) := by nlinarith
  have h0 : 0 ≤ (1 - ε) * N := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  calc (1 - ε) * (11 * Real.log 2 / 50) * (2 * N * (Lfun N : ℝ))
      = (1 - ε) * N * (11 * Real.log 2 / 50 * (2 * (Lfun N : ℝ))) := by ring
    _ ≤ (1 - ε) * N * Real.log (P N) := mul_le_mul_of_nonneg_left hkey h0
    _ ≤ _ := hN

/-- The step before (58): since `b² ≤ H`, the lower bound on `R₁(0)` bounds the major arc
term `(b² - H) R₁(0)/(2NL)` above. -/
theorem major_term_le {b H R c : ℝ} (hbH : b ^ 2 ≤ H) (hR : c ≤ R) :
    (b ^ 2 - H) * R ≤ (b ^ 2 - H) * c :=
  mul_le_mul_of_nonpos_left hR (by linarith)

/-- Vacuity of `R1_ge_11log2`: `κ = 1/2`, `P(N) = N^{1/2}/2` meet its hypotheses. -/
theorem R1_vacuity :
    (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / 2) ∧
    (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (N : ℝ) ^ (1 - 1 / 2 : ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, 2 * ((N : ℝ) ^ (1 / 2 : ℝ) / 2) ^ 2 < N) := by
  refine ⟨?_, U1412MuPhi.vacuity_logP.2.1, U1412MuPhi.vacuity_logP.2.2⟩
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 - 11 / 25)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop 2, eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have e : (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2 - 11 / 25) * (N : ℝ) ^ ((11 : ℝ) / 25) := by
    rw [← Real.rpow_add hNpos]; norm_num
  rw [e]
  have : 0 < (N : ℝ) ^ ((11 : ℝ) / 25) := by positivity
  nlinarith

/-! ### The chain theorems with the `H` hypotheses discharged -/

/-- **(58) wired, CONDITIONAL ON the cited constants only**: C₀R₀ < 1.2784421041
(Platt-Trudgian), JT's A(2) ≤ 0.05549 and A(3) ≤ 0.013598, and a tail `T` with
`|T_ij| ≤ √(T_ii T_jj)`. The free `H` of `LiLiu2026Chain.k6_of_cited` is now the paper's
`H = max_{D_{5/6}} |Q|²`, it satisfies (54) off `E₆`, and `meas E₆ ≪ e^{-81L/200}`. -/
theorem k6_wired {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) :
    ∃ H : ℝ, (∃ z0 ∈ LiLiu.Dl (5 / 6), Q6 z0 = H) ∧ (∀ z ∈ LiLiu.Dl (5 / 6), Q6 z ≤ H) ∧
      (1 / 16 : ℝ) ^ 2 ≤ H ∧ H < 2 / 15 ∧
      (∀ L : ℕ, ∀ α : ℝ, α ∉ {α : ℝ | zL L α ∉ LiLiu.Dl (5 / 6)} → Q6 (zL L α) ≤ H) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
        (volume.restrict (Icc (0 : ℝ) 1) {α | zL L α ∉ LiLiu.Dl (5 / 6)}).toReal ≤
          C * Real.exp (-(81 / 200) * L)) ∧
      (∑ i, ∑ j, ((LiLiu.v i : ℝ)) * ((LiLiu.Astar i j : ℝ) + T i j) * (LiLiu.v j : ℝ)) +
        11 * (1 / 16) ^ 2 * Real.log 2 / 50 +
        H * ((6.7814 - 2) / 2 * CR + 7 * Real.log 2 / 25) < (1 - 1 / 4 - 1 / 16) ^ 2 := by
  obtain ⟨H, hz0, hmax, hb, hH⟩ := exists_H6
  have hH0 : 0 ≤ H := le_trans (by positivity) hb
  exact ⟨H, hz0, hmax, hb, hH, fun L α hα => display54 hmax hα, exc6,
    LiLiu.k6_of_cited T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33 hH0 hH⟩

/-- **(65) wired, CONDITIONAL ON C₀R₀ < 1.2784421041 and `WA < 37/200`**, the form (66);
the free `H` of `LiLiu2026Chain.k5_of_cited` is now the maximum over `D_{25/32}` of
`|z - 1/8|² + 4|Q(z)|²`, and `meas E₅ ≪ e^{-347L/1000}`. Section 7 is on GRH elsewhere. -/
theorem k5_wired {CR WA : ℝ} (hCR0 : 0 ≤ CR) (hPT : CR < 1.2784421041) (hWA : WA < 37 / 200) :
    ∃ H : ℝ, (∃ z0 ∈ LiLiu.Dl (25 / 32), Q5 z0 = H) ∧ (∀ z ∈ LiLiu.Dl (25 / 32), Q5 z ≤ H) ∧
      0 ≤ H ∧ H < 41 / 60 ∧
      (∀ L : ℕ, ∀ α : ℝ, α ∉ {α : ℝ | zL L α ∉ LiLiu.Dl (25 / 32)} → Q5 (zL L α) ≤ H) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
        (volume.restrict (Icc (0 : ℝ) 1) {α | zL L α ∉ LiLiu.Dl (25 / 32)}).toReal ≤
          C * Real.exp (-(347 / 1000) * L)) ∧
      WA + 1 / 32 * Real.log 2 / 4 + H * ((6.7814 - 2) / 2 * CR + Real.log 2 / 4)
        < 2 * 2 * (1 - 1 / 8) * (1 - 1 / 4 - 1 / 16) := by
  obtain ⟨H, hz0, hmax, hH0, hH⟩ := exists_H5
  exact ⟨H, hz0, hmax, hH0, hH, fun L α hα => display54 hmax hα, exc5,
    LiLiu.k5_of_cited hCR0 hPT hWA hH0 hH⟩

/-- Vacuity of `k6_wired`: the hypotheses hold at `T = 0`, `CR = 1 + (A_*)₁₁`. -/
theorem k6_wired_instance : ∃ H : ℝ, (1 / 16 : ℝ) ^ 2 ≤ H ∧ H < 2 / 15 ∧
    (∑ i, ∑ j, ((LiLiu.v i : ℝ)) * ((LiLiu.Astar i j : ℝ) + (0 : ℝ)) * (LiLiu.v j : ℝ)) +
      11 * (1 / 16) ^ 2 * Real.log 2 / 50 +
      H * ((6.7814 - 2) / 2 * (1 + (LiLiu.Astar 0 0 : ℝ)) + 7 * Real.log 2 / 25) <
        (1 - 1 / 4 - 1 / 16) ^ 2 := by
  obtain ⟨CR, A22, A33, h0, h1, h2, h3, h4, h5, h6, h7⟩ := LiLiu.k6_of_cited_vacuity
  have hCR : CR = 1 + (LiLiu.Astar 0 0 : ℝ) := by linarith
  obtain ⟨H, -, -, hb, hH, -, -, hk⟩ := k6_wired (fun _ _ => (0 : ℝ)) h0 h1 h2 h3 h7
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
  exact ⟨H, hb, hH, by rw [← hCR]; exact hk⟩

/-! ### Vacuity instances -/

/-- `lemma61` at `κ = 1/2`, `a = 1/4`, `b = 1/16` with `P(N) = N`, where `MinorSup1924` holds. -/
theorem lemma61_instance : ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
    ∫ α in minorArcs (N : ℝ) N ∩ {α | zL (Lfun N) α ∉ LiLiu.Dl (5 / 6)},
      ‖Sm ⌊(N : ℝ) ^ (1 - 1 / 2 : ℝ)⌋₊ N α * FG (1 / 4) (1 / 16) (Lfun N) α‖ ^ 2 ≤
        δ * N * (Lfun N : ℝ) ^ 6 :=
  lemma61 (by norm_num) (fun N => (N : ℝ)) minorSup_trivial (by norm_num) (by norm_num)

/-- `lemma61_bound` at `m = [0,1]`, `N₁ = 0`, `N = 3`, `L = 1`, with `B` the trivial bound. -/
theorem lemma61_bound_instance :
    ∫ α in Icc (0 : ℝ) 1 ∩ {α | zL 1 α ∉ LiLiu.Dl (5 / 6)}, ‖Sm 0 3 α * FG (1 / 4) (1 / 16) 1 α‖ ^ 2 ≤
      2 * (1 + 1 / 4 + 1 / 16) ^ 2 * ((1 : ℕ) : ℝ) ^ 6 *
        ((∑ p ∈ primesIn 0 3, Real.log p) ^ 2 *
          (volume.restrict (Icc (0 : ℝ) 1) {α | zL 1 α ∉ LiLiu.Dl (5 / 6)}).toReal +
          ∑ p ∈ primesIn 0 0, Real.log p ^ 2) := by
  refine lemma61_bound (by norm_num) (by norm_num) le_rfl (Nat.zero_le 3) measurableSet_Icc
    subset_rfl fun α _ => ?_
  unfold Sle SA
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun p hp => ?_))
  simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp
  rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, LiLiuDisplay37.logw,
    Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg p)]

/-- `display56` at `m = [0,1]`, `S = 1`, `L = 1`. -/
theorem display56_instance : ∃ H : ℝ, H < 2 / 15 ∧
    ∫ α in Icc (0 : ℝ) 1 \ {α | zL 1 α ∉ LiLiu.Dl (5 / 6)}, ‖(1 : ℂ) * FG (1 / 4) (1 / 16) 1 α‖ ^ 2 ≤
      H * ((1 : ℕ) : ℝ) ^ 4 * ∫ α in Icc (0 : ℝ) 1, ‖(1 : ℂ) * Gs 1 α‖ ^ 2 := by
  obtain ⟨H, -, hmax, -, hH⟩ := exists_H6
  exact ⟨H, hH, display56 hmax le_rfl continuous_const measurableSet_Icc subset_rfl⟩

end LeanLab.Linnik.U1426ChainWire
