module

public import LeanLab.BhowmikGrimmelt2026.Coefficients150
public import LeanLab.BhowmikGrimmelt2026.ModelL2_150
public import LeanLab.BhowmikGrimmelt2026.FareyCount451
public import LeanLab.BhowmikGrimmelt2026.ArcTails150
public import LeanLab.PNTPort.Vinogradov.Basic
public import LeanLab.BhowmikGrimmelt2026.Decomp504a

/-!
The exact denominator decomposition of the arc tails in P0029 page 12.
The least denominator assignment is retained throughout.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- P0029 page 12. Disjoint assigned arcs remove every cross term in V squared. -/
theorem VX_sq_eq_sum502 (X : ℕ) (α : ℝ) :
    VX150 X α ^ 2 = ∑ q ∈ Finset.Icc 1 (Nat.sqrt X),
      (arcSet150 X q).indicator (fun β => arcTerm150 X q β ^ 2) α := by
  classical
  by_cases hex : ∃ q ∈ Finset.Icc 1 (Nat.sqrt X), α ∈ arcSet150 X q
  · obtain ⟨q, hq, hα⟩ := hex
    have hoff : ∀ b ∈ Finset.Icc 1 (Nat.sqrt X), b ≠ q → α ∉ arcSet150 X b := by
      intro b hb hne hβ
      exact arcSet_disjoint150 X (Finset.mem_Icc.mp hq).1
        (Finset.mem_Icc.mp hb).1 hne.symm hα hβ
    unfold VX150
    rw [Finset.sum_eq_single_of_mem q hq (fun b hb hne =>
      Set.indicator_of_notMem (hoff b hb hne) _)]
    rw [Finset.sum_eq_single_of_mem q hq (fun b hb hne =>
      Set.indicator_of_notMem (hoff b hb hne) _)]
    simp only [Set.indicator_of_mem hα]
  · push_neg at hex
    unfold VX150
    rw [Finset.sum_eq_zero (fun q hq => Set.indicator_of_notMem (hex q hq) _),
      Finset.sum_eq_zero (fun q hq => Set.indicator_of_notMem (hex q hq) _)]
    norm_num

/-- P0029 page 12. The full model restricted to rational terms within their Dirichlet width. -/
noncomputable def nearWX502 (X : ℕ) (α : ℝ) : ℂ :=
  ∑ p ∈ nearPairs451 (Nat.sqrt X : ℝ) α 1,
    wq150 p.1 * TX150 X (α - (p.2 : ℝ) / p.1) ^ 2

/-- P0029 page 12. The complementary terms outside their Dirichlet widths. -/
noncomputable def farWX502 (X : ℕ) (α : ℝ) : ℂ := by
  classical
  exact ∑ p ∈ (reducedPairs (Nat.sqrt X)).filter
    (fun p => 1 < (Nat.sqrt X : ℝ) * p.1 * intDist (α - p.2 / p.1)),
      wq150 p.1 * TX150 X (α - (p.2 : ℝ) / p.1) ^ 2

/-- P0029 page 12. The weighted absolute sum of the far terms. -/
noncomputable def farMass502 (X : ℕ) (α : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (reducedPairs (Nat.sqrt X)).filter
    (fun p => 1 < (Nat.sqrt X : ℝ) * p.1 * intDist (α - p.2 / p.1)),
      ‖wq150 p.1‖ * ‖TX150 X (α - (p.2 : ℝ) / p.1)‖ ^ 2

/-- P0029 page 12. The pure weighted inverse square kernel outside the Dirichlet widths. -/
noncomputable def farKernel502 (X : ℕ) (α : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (reducedPairs (Nat.sqrt X)).filter
    (fun p => 1 < (Nat.sqrt X : ℝ) * p.1 * intDist (α - p.2 / p.1)),
      (1 / (Nat.totient p.1 : ℝ) ^ 2) *
        (min (X : ℝ) (1 / (2 * intDist (α - (p.2 : ℝ) / p.1)))) ^ 2

/-- P0029 page 12. The nearby and far terms partition the full model exactly. -/
theorem WX_eq_near_add_far502 (X : ℕ) (α : ℝ) :
    WX150 X α = nearWX502 X α + farWX502 X α := by
  classical
  unfold WX150
  rw [← sum_reducedPairs]
  symm
  simpa only [nearWX502, farWX502, nearPairs451, Nat.floor_natCast,
    Nat.cast_one, not_le] using
    Finset.sum_filter_add_sum_filter_not (reducedPairs (Nat.sqrt X))
      (fun p => (Nat.sqrt X : ℝ) * p.1 * intDist (α - p.2 / p.1) ≤ 1)
      (fun p => wq150 p.1 * TX150 X (α - (p.2 : ℝ) / p.1) ^ 2)

/-- P0029 page 12. Taking absolute values of the far terms gives an upper bound. -/
theorem norm_farWX_le502 (X : ℕ) (α : ℝ) : ‖farWX502 X α‖ ≤ farMass502 X α := by
  classical
  unfold farWX502 farMass502
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro p hp
  rw [norm_mul, norm_pow]

/-- P0029 page 12. At most six reduced rational terms lie within their Dirichlet widths. -/
theorem near_card_le502 {X : ℕ} (hX : 1 ≤ X) (α : ℝ) :
    (nearPairs451 (Nat.sqrt X : ℝ) α 1).card ≤ 6 := by
  have hQ : 1 ≤ Nat.sqrt X := Nat.sqrt_pos.mpr (by omega)
  simpa using nearPairs_card451 (by exact_mod_cast hQ : (1 : ℝ) ≤ Nat.sqrt X)
    (by norm_num : 1 ≤ (1 : ℕ))

/-- P0029 page 12. CONDITIONAL on the two displayed near and far estimates. -/
theorem arc_tails_of_near_far502
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - nearWX502 X α‖ ≤ C * (X : ℝ) ^ (1 + ε))
    (hfar : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      farMass502 X α ≤ C * (X : ℝ) ^ (1 + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε) := by
  intro ε hε
  obtain ⟨C, hC⟩ := hnear ε hε
  obtain ⟨D, hD⟩ := hfar ε hε
  refine ⟨C + D, fun X hX α hα => ?_⟩
  calc
    ‖VX150 X α ^ 2 - WX150 X α‖ =
        ‖(VX150 X α ^ 2 - nearWX502 X α) - farWX502 X α‖ := by
      rw [WX_eq_near_add_far502]
      congr 1
      ring
    _ ≤ ‖VX150 X α ^ 2 - nearWX502 X α‖ + ‖farWX502 X α‖ := norm_sub_le _ _
    _ ≤ (C + D) * (X : ℝ) ^ (1 + ε) := by
      have hn := hC X hX α hα
      have hf := (norm_farWX_le502 X α).trans (hD X hX α hα)
      nlinarith only [hn, hf]

/-- P0029 page 11. The least denominator arcs cover every real frequency. -/
theorem exists_arc502 {X : ℕ} (hX : 1 ≤ X) (α : ℝ) :
    ∃ q ∈ Finset.Icc 1 (Nat.sqrt X), α ∈ arcSet150 X q := by
  classical
  have hQ : 0 < Nat.sqrt X := Nat.sqrt_pos.mpr (by omega)
  obtain ⟨k, hk, hkQ, hclose⟩ := Real.exists_nat_abs_mul_sub_round_le α hQ
  have hweak : |(k : ℝ) * α - nint150 ((k : ℝ) * α)| ≤ 1 / (Nat.sqrt X : ℝ) := by
    unfold nint150
    rw [← round_eq]
    exact hclose.trans (one_div_le_one_div_of_le (by exact_mod_cast hQ) (by linarith))
  have hex : ∃ q : ℕ, 1 ≤ q ∧
      |(q : ℝ) * α - nint150 ((q : ℝ) * α)| ≤ 1 / (Nat.sqrt X : ℝ) := ⟨k, hk, hweak⟩
  have hgood := Nat.find_spec hex
  have hle : Nat.find hex ≤ k := Nat.find_min' hex ⟨hk, hweak⟩
  refine ⟨Nat.find hex, Finset.mem_Icc.mpr ⟨hgood.1, hle.trans hkQ⟩, ?_⟩
  simp only [arcSet150, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
  refine ⟨hgood.2, ?_⟩
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  exact lt_of_not_ge (fun h => Nat.find_min hex hj'.2 ⟨hj'.1, h⟩)

/-- P0029 pages 11 and 12. On an assigned arc V equals that arc term. -/
theorem VX_eq_arcTerm502 {X q : ℕ} (hq : q ∈ Finset.Icc 1 (Nat.sqrt X))
    {α : ℝ} (hα : α ∈ arcSet150 X q) : VX150 X α = arcTerm150 X q α := by
  classical
  unfold VX150
  rw [Finset.sum_eq_single_of_mem q hq]
  · exact Set.indicator_of_mem hα _
  · intro b hb hne
    apply Set.indicator_of_notMem
    intro hβ
    exact arcSet_disjoint150 X (Finset.mem_Icc.mp hq).1
      (Finset.mem_Icc.mp hb).1 hne.symm hα hβ

/-- P0029 page 12. The omitted nearby denominator is large when the assigned one is minimal.
The minimum denominator hypothesis is essential. Spacing alone gives only a denominator sum. -/
theorem near_other_large502 {M : ℕ} {Q α : ℝ} (hQ : 0 < Q)
    {p₀ p : Σ _ : ℕ, ℕ} (hp₀ : p₀ ∈ reducedPairs M) (hp : p ∈ reducedPairs M)
    (hne : p₀ ≠ p)
    (hnear₀ : Q * p₀.1 * intDist (α - p₀.2 / p₀.1) ≤ 1)
    (hnear : Q * p.1 * intDist (α - p.2 / p.1) ≤ 1)
    (hmin : p₀.1 ≤ p.1) : Q ≤ 2 * (p.1 : ℝ) := by
  have h := near_pair_denominator_sum451 hQ hp₀ hp hne hnear₀ hnear
  have hmin' : (p₀.1 : ℝ) ≤ p.1 := by exact_mod_cast hmin
  linarith

/-- A concrete instance of the page 12 sharp model and its near and far decomposition. -/
theorem model_one502 :
    VX150 1 0 = 1 ∧ nearWX502 1 0 = 1 ∧ farWX502 1 0 = 0 ∧ farMass502 1 0 = 0 := by
  have hr : reducedPairs 1 = {⟨1, 0⟩} := by
    ext p
    rw [mem_reducedPairs, Finset.mem_singleton]
    constructor
    · intro h
      have hq : p.1 = 1 := by omega
      have ha : p.2 = 0 := by omega
      exact Sigma.ext hq (heq_of_eq ha)
    · rintro rfl
      norm_num
  have hmem : (0 : ℝ) ∈ arcSet150 1 1 := by
    norm_num [arcSet150, nint150]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [VX_eq_arcTerm502 (by norm_num) hmem]
    norm_num [arcTerm150, TX150, nint150, ee]
  · norm_num [nearWX502, nearPairs451, hr, Finset.filter_singleton, TX150, wq150, intDist, ee]
  · norm_num [farWX502, hr, Finset.filter_singleton, TX150, wq150, intDist, ee]
  · norm_num [farMass502, hr, Finset.filter_singleton, TX150, wq150, intDist, ee]

/-- P0029 page 11. The sharp character Chebyshev sum, including the zero coefficient. -/
noncomputable def psiCharacter502 {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (X + 1), (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)

/-- P0029 page 11. Exact discrete partial summation before estimating any zero modes. -/
theorem psi_twist_abel502 {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) (β : ℝ) :
    (∑ n ∈ Finset.range (X + 1),
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) * ee ((n : ℝ) * β)) =
      psiCharacter502 χ X * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, psiCharacter502 χ n *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)) := by
  simpa only [psiCharacter502, Nat.add_sub_cancel, smul_eq_mul] using
    Finset.sum_range_by_parts'
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q))
      (fun n => ee ((n : ℝ) * β)) (X + 1)

/-- P0029 page 11. Taking norms of partial sums first introduces a full variation factor. -/
theorem psi_twist_variation502 {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) (β B : ℝ)
    (hB : ∀ n ≤ X, ‖psiCharacter502 χ n‖ ≤ B) :
    ‖∑ n ∈ Finset.range (X + 1),
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) * ee ((n : ℝ) * β)‖ ≤
      B * (1 + (X : ℝ) * ‖ee β - 1‖) := by
  have hstep (n : ℕ) :
      ‖ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)‖ = ‖ee β - 1‖ := by
    rw [show (((n + 1 : ℕ) : ℝ) * β) = (n : ℝ) * β + β by push_cast; ring,
      ee_add150]
    rw [show ee ((n : ℝ) * β) * ee β - ee ((n : ℝ) * β) =
      ee ((n : ℝ) * β) * (ee β - 1) by ring, norm_mul, norm_ee150, one_mul]
  rw [psi_twist_abel502]
  calc
    _ ≤ ‖psiCharacter502 χ X * ee ((X : ℝ) * β)‖ +
        ‖∑ n ∈ Finset.range X, psiCharacter502 χ n *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ := norm_sub_le _ _
    _ ≤ B + (X : ℝ) * (B * ‖ee β - 1‖) := by
      apply add_le_add
      · simpa only [norm_mul, norm_ee150, mul_one] using hB X le_rfl
      · refine (norm_sum_le _ _).trans ?_
        calc
          _ ≤ ∑ _n ∈ Finset.range X, B * ‖ee β - 1‖ := by
            apply Finset.sum_le_sum
            intro n hn
            rw [norm_mul, hstep]
            exact mul_le_mul_of_nonneg_right (hB n (by have := Finset.mem_range.mp hn; omega))
              (norm_nonneg _)
          _ = _ := by simp
    _ = B * (1 + (X : ℝ) * ‖ee β - 1‖) := by ring

/-- P0029 page 11. The additive phase has variation at most two pi times its frequency. -/
theorem norm_ee_sub_one_le502 (β : ℝ) : ‖ee β - 1‖ ≤ 2 * Real.pi * |β| := by
  have he : ee β = Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) := by
    unfold ee
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one,
    show 2 * Real.pi * β / 2 = Real.pi * β by ring]
  calc
    ‖2 * Real.sin (Real.pi * β)‖ = 2 * |Real.sin (Real.pi * β)| := by
      rw [Real.norm_eq_abs, abs_mul]
      norm_num
    _ ≤ 2 * |Real.pi * β| := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs) (by norm_num)
    _ = 2 * Real.pi * |β| := by rw [abs_mul, abs_of_pos Real.pi_pos]; ring

/-- P0029 page 11. The coarse partial summation estimate has a linear beta X loss. -/
theorem psi_twist_coarse502 {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) (β B : ℝ)
    (hB : ∀ n ≤ X, ‖psiCharacter502 χ n‖ ≤ B) :
    ‖∑ n ∈ Finset.range (X + 1),
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) * ee ((n : ℝ) * β)‖ ≤
      B * (1 + 2 * Real.pi * |β| * X) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le X))
  refine (psi_twist_variation502 χ X β B hB).trans ?_
  apply mul_le_mul_of_nonneg_left _ hB0
  have h := mul_le_mul_of_nonneg_left (norm_ee_sub_one_le502 β) (Nat.cast_nonneg X)
  nlinarith only [h]

/-- P0029 page 11, a limitation of coarse partial summation, not a paper error.
For epsilon below one quarter the exponent theta plus one half cannot be uniformly bounded
by a constant times the desired exponent theta plus one quarter plus epsilon. -/
theorem naive_loss_not_power502 (Θ ε : ℝ) (hε : ε < 1 / 4) :
    ¬ ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      x ^ (Θ + 1 / 2) ≤ C * x ^ (Θ + 1 / 4 + ε) := by
  rintro ⟨C, hC⟩
  have ht := tendsto_rpow_atTop (show 0 < (1 / 4 : ℝ) - ε by linarith)
  have hev : ∀ᶠ x : ℝ in Filter.atTop, C + 1 ≤ x ^ ((1 / 4 : ℝ) - ε) :=
    ht.eventually (Filter.eventually_ge_atTop (C + 1))
  obtain ⟨x, hx, hbig⟩ := ((Filter.eventually_ge_atTop (1 : ℝ)).and hev).exists
  have hxp : 0 < x := by linarith
  have heq : x ^ (Θ + 1 / 2) = x ^ ((1 / 4 : ℝ) - ε) * x ^ (Θ + 1 / 4 + ε) := by
    rw [← Real.rpow_add hxp]
    congr 1
    ring
  have h := hC x hx
  rw [heq] at h
  have hsmall : x ^ ((1 / 4 : ℝ) - ε) ≤ C :=
    le_of_mul_le_mul_right h (Real.rpow_pos_of_pos hxp _)
  linarith

/-- P0029 page 12. The phase denominator controls distance to the nearest integer. -/
theorem four_intDist_le_phase502 (β : ℝ) : 4 * intDist β ≤ ‖ee β - 1‖ := by
  simpa only [intDist, ee_eq_library84, LeanLab.PNTPort.LargeSieve.dist0] using
    LeanLab.PNTPort.LargeSieve.four_dist0_le β

/-- P0029 page 12. The sharp geometric sum bound at nonintegral frequencies. -/
theorem norm_TX_min502 (X : ℕ) (β : ℝ) (hβ : 0 < intDist β) :
    ‖TX150 X β‖ ≤ min (X : ℝ) (1 / (2 * intDist β)) := by
  have h := LeanLab.PNTPort.Vinogradov.norm_sum_Ioc_e_le 0 X β
  have hi : Finset.Ioc 0 (0 + X) = Finset.Icc 1 X := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hi] at h
  have hTX : ‖TX150 X β‖ ≤ LeanLab.PNTPort.Vinogradov.G X β := by
    simpa only [TX150, ee_eq_library84] using h
  have hd : 0 < LeanLab.PNTPort.LargeSieve.dist0 β := hβ
  refine le_min (norm_TX_le150 X β) ?_
  simpa only [LeanLab.PNTPort.LargeSieve.dist0, intDist] using
    hTX.trans (LeanLab.PNTPort.Vinogradov.G_le_inv (Y := (X : ℝ)) hd)

/-- P0029 page 11. Assignment forces minimality against every qualifying integer numerator. -/
theorem arc_denominator_min502 {X q₀ q : ℕ} {α : ℝ}
    (hα : α ∈ arcSet150 X q₀) (hq : 1 ≤ q)
    (hnear : |(q : ℝ) * α - nint150 ((q : ℝ) * α)| ≤ 1 / (Nat.sqrt X : ℝ)) :
    q₀ ≤ q := by
  by_contra h
  have hlt : q < q₀ := by omega
  simp only [arcSet150, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter] at hα
  have hbad := hα.2 q (Finset.mem_Ico.mpr ⟨hq, hlt⟩)
  linarith

/-- P0029 page 12. The geometric sum bound removes every exponential from the far estimate. -/
theorem farMass_le_kernel502 (X : ℕ) (α : ℝ) : farMass502 X α ≤ farKernel502 X α := by
  classical
  unfold farMass502 farKernel502
  apply Finset.sum_le_sum
  intro p hp
  have hfar := (Finset.mem_filter.mp hp).2
  have hd : 0 < intDist (α - (p.2 : ℝ) / p.1) := by
    by_contra! hbad
    have hprod : (Nat.sqrt X : ℝ) * p.1 * intDist (α - (p.2 : ℝ) / p.1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hbad
    linarith
  have hT := norm_TX_min502 X (α - (p.2 : ℝ) / p.1) hd
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hT 2
  have hw : ‖wq150 p.1‖ ≤ 1 / (Nat.totient p.1 : ℝ) ^ 2 := norm_wq_le150
  exact mul_le_mul hw hsq (sq_nonneg _) (by positivity)

/-- LEAF: P0029 page 12. The far reduced fractions satisfy a pure weighted kernel bound.
This contains no prime sum and no exponential sum. The proof uses a dyadic Farey count
and the subpower bound for the ratio of a denominator to its totient. -/
theorem far_kernel502 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      farKernel502 X α ≤ C * (X : ℝ) ^ (1 + ε) := by
  classical
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := far_weighted_subpower504 (2 * ε) (by positivity)
  refine ⟨C, fun X hX α _hα => ?_⟩
  let Q := Nat.sqrt X
  have hQ : 1 ≤ Q := Nat.sqrt_pos.mpr (by omega)
  let s := (reducedPairs Q).filter
    (fun p => 1 < (Q : ℝ) * p.1 * intDist (α - p.2 / p.1))
  have hb := hC Q hQ α s (Finset.filter_subset _ _)
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have hm : farKernel502 X α ≤ ∑ p ∈ s,
      (1 / (Nat.totient p.1 : ℝ) ^ 2) * (1 / intDist (α - p.2 / p.1) ^ 2) := by
    apply Finset.sum_le_sum
    intro p hp
    have hf := (Finset.mem_filter.mp hp).2
    have hd : 0 < intDist (α - p.2 / p.1) := by
      by_contra! hbad
      have hh : (Q : ℝ) * p.1 * intDist (α - p.2 / p.1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hbad
      linarith
    have hmin : min (X : ℝ) (1 / (2 * intDist (α - p.2 / p.1))) ≤
        1 / intDist (α - p.2 / p.1) :=
      (min_le_right _ _).trans (one_div_le_one_div_of_le hd (by linarith))
    have hmin0 : 0 ≤ min (X : ℝ) (1 / (2 * intDist (α - p.2 / p.1))) := by positivity
    have hh := pow_le_pow_left₀ hmin0 hmin 2
    simpa only [one_div_pow] using
      mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1 / (Nat.totient p.1 : ℝ) ^ 2)
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hQX : (Q : ℝ) ^ 2 ≤ X := by exact_mod_cast Nat.sqrt_le' X
  have heq : (Q : ℝ) ^ (2 + 2 * ε) = ((Q : ℝ) ^ 2) ^ (1 + ε) := by
    rw [← Real.rpow_natCast_mul hQ0]
    congr 1
    push_cast
    ring
  calc
    farKernel502 X α ≤ C * (Q : ℝ) ^ (2 + 2 * ε) := hm.trans hb
    _ = C * ((Q : ℝ) ^ 2) ^ (1 + ε) := by rw [heq]
    _ ≤ C * (X : ℝ) ^ (1 + ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hQX (by positivity)) hC0

/-- P0029 page 12. The far arc mass follows from the proved pure weighted kernel bound. -/
theorem far_arc_tail502 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      farMass502 X α ≤ C * (X : ℝ) ^ (1 + ε) := by
  intro ε hε
  obtain ⟨C, hC⟩ := far_kernel502 ε hε
  exact ⟨C, fun X hX α hα => (farMass_le_kernel502 X α).trans (hC X hX α hα)⟩

/-- LEAF: P0029 page 12, the nearby arc tails. Retain the least denominator assignment.
The difference between V squared and the nearby full model has size X to one plus epsilon.
The proof identifies and cancels the assigned residue before bounding the other nearby terms. -/
theorem near_arc_tail502 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - nearWX502 X α‖ ≤ C * (X : ℝ) ^ (1 + ε) := by
  classical
  intro ε hε
  let k : ℕ := ⌈2 / ε⌉₊ + 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hkε : (k : ℝ)⁻¹ ≤ ε / 2 := by
    have hh := Nat.le_ceil (2 / ε)
    have hkbig : 2 / ε < (k : ℝ) := by dsimp [k]; push_cast; linarith
    have hh' := (div_lt_iff₀ hε).mp hkbig
    rw [← one_div, div_le_iff₀ hkp]
    nlinarith only [hh']
  obtain ⟨D, hD, hDb⟩ := totient_ratio_subpower504 k hk
  refine ⟨96 * D ^ 2, fun X hX α hα => ?_⟩
  let Q := Nat.sqrt X
  have hQ : 1 ≤ Q := Nat.sqrt_pos.mpr (by omega)
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith
  have hXQ : (X : ℝ) ≤ 4 * (Q : ℝ) ^ 2 := by
    have hh : (X : ℝ) < ((Q : ℝ) + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' X
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith only [hh, hQR, sq_nonneg ((Q : ℝ) - 1)]
  obtain ⟨q, hq, haq⟩ := exists_arc502 hX α
  obtain ⟨b, hb, hcop, hnear, hterm⟩ := assigned_residue504 hq hα haq
  let p : Σ _ : ℕ, ℕ := ⟨q, b⟩
  let s := nearPairs451 (Q : ℝ) α 1
  have hpM : p ∈ reducedPairs Q :=
    (mem_reducedPairs _ _).mpr ⟨(Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2, hb, hcop⟩
  have hp : p ∈ s := by
    simp only [s, nearPairs451, Nat.floor_natCast, Finset.mem_filter, Nat.cast_one]
    exact ⟨hpM, hnear⟩
  have hV : VX150 X α ^ 2 = wq150 p.1 * TX150 X (α - p.2 / p.1) ^ 2 := by
    rw [VX_eq_arcTerm502 hq haq]
    exact hterm
  have hlarge : ∀ r ∈ s.erase p, (Q : ℝ) ≤ 2 * r.1 := by
    intro r hr
    obtain ⟨hrne, hrs⟩ := Finset.mem_erase.mp hr
    have hrfilter := Finset.mem_filter.mp hrs
    have hrM : r ∈ reducedPairs Q := by simpa only [Nat.floor_natCast] using hrfilter.1
    have hrnear : (Q : ℝ) * r.1 * intDist (α - r.2 / r.1) ≤ 1 := by simpa only [Nat.cast_one] using hrfilter.2
    have hrq := (mem_reducedPairs _ r).mp hrM
    have hround : |(r.1 : ℝ) * α - (nint150 ((r.1 : ℝ) * α) : ℝ)| ≤
        1 / (Nat.sqrt X : ℝ) := by
      have hh := intDist_mul_nat504 r.1 r.2 α hrq.1
      have hh' : (r.1 : ℝ) * intDist (α - r.2 / r.1) ≤ 1 / (Q : ℝ) := by
        apply (le_div_iff₀ hQp).mpr
        nlinarith only [hrnear]
      have hd := hh.trans hh'
      simpa only [intDist, nint150, round_eq] using hd
    have hmin : p.1 ≤ r.1 := arc_denominator_min502 haq hrq.1 hround
    exact near_other_large502 hQp hpM hrM hrne.symm hnear hrnear hmin
  have hweight : ∀ r ∈ s.erase p, (r.1 : ℝ) ≤
      (D * (X : ℝ) ^ (ε / 2)) * Nat.totient r.1 := by
    intro r hr
    have hrs := (Finset.mem_erase.mp hr).2
    have hrM : r ∈ reducedPairs Q := by
      simpa only [Nat.floor_natCast] using (Finset.mem_filter.mp hrs).1
    have hrq := (mem_reducedPairs _ r).mp hrM
    have hrX : (r.1 : ℝ) ≤ X := by
      exact_mod_cast hrq.2.1.trans (Nat.sqrt_le_self X)
    refine (hDb r.1 hrq.1).trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hD.le
    exact (Real.rpow_le_rpow (by positivity) hrX (by positivity)).trans
      (Real.rpow_le_rpow_of_exponent_le hXR hkε)
  have hsingle : ∀ r ∈ s.erase p,
      ‖wq150 r.1 * TX150 X (α - r.2 / r.1) ^ 2‖ ≤
        16 * (D * (X : ℝ) ^ (ε / 2)) ^ 2 * X := by
    intro r hr
    have hrs := (Finset.mem_erase.mp hr).2
    have hrM : r ∈ reducedPairs Q := by
      simpa only [Nat.floor_natCast] using (Finset.mem_filter.mp hrs).1
    exact near_term_le504 hXQ ((mem_reducedPairs _ r).mp hrM).1
      (hlarge r hr) (hweight r hr) _
  have hcard : ((s.erase p).card : ℝ) ≤ 6 := by
    have hh := (Finset.card_erase_le (s := s) (a := p)).trans (near_card_le502 hX α)
    exact_mod_cast hh
  have hcancel : VX150 X α ^ 2 - nearWX502 X α =
      -(∑ r ∈ s.erase p, wq150 r.1 * TX150 X (α - r.2 / r.1) ^ 2) := by
    have hh := Finset.sum_erase_add s
      (fun r => wq150 r.1 * TX150 X (α - r.2 / r.1) ^ 2) hp
    change VX150 X α ^ 2 - (∑ r ∈ s, _) = _
    rw [hV, ← hh]
    ring
  have heq : 6 * (16 * (D * (X : ℝ) ^ (ε / 2)) ^ 2 * X) =
      96 * D ^ 2 * (X : ℝ) ^ (1 + ε) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hXp.le]
    rw [show ε / 2 * (2 : ℕ) = ε by push_cast; ring,
      Real.rpow_add hXp, Real.rpow_one]
    ring
  calc
    _ = ‖∑ r ∈ s.erase p, wq150 r.1 * TX150 X (α - r.2 / r.1) ^ 2‖ := by
      rw [hcancel, norm_neg]
    _ ≤ ∑ r ∈ s.erase p, ‖wq150 r.1 * TX150 X (α - r.2 / r.1) ^ 2‖ := norm_sum_le _ _
    _ ≤ ∑ _r ∈ s.erase p, 16 * (D * (X : ℝ) ^ (ε / 2)) ^ 2 * X :=
      Finset.sum_le_sum hsingle
    _ = ((s.erase p).card : ℝ) * (16 * (D * (X : ℝ) ^ (ε / 2)) ^ 2 * X) := by simp
    _ ≤ 6 * (16 * (D * (X : ℝ) ^ (ε / 2)) ^ 2 * X) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := heq

end LeanLab.BhowmikGrimmelt2026
