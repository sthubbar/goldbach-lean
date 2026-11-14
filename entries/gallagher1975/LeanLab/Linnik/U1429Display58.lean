module

public import LeanLab.Linnik.U1426ChainWire

/-!
Li-Liu, arXiv 2610.15784, Section 6: the passage from display (30) to the criterion (58) and
the conclusion r₆''(N) ≫ N L⁶. Read by WebFetch on the unversioned arxiv.org/html/2610.15784,
2026-10-21.

The paper's argument, Section 6. Lemma 2.1: for large even N,
  r₆''(N) ≥ 4(1-a-b)² N L⁶ - ∫_0^1 |S F(G)|² + o(N L⁶).
Split [0,1] into 𝔐, 𝔪 \ E₆, 𝔪 ∩ E₆. Display (30) bounds the major arc part by
  2NL⁶((1-a-b)² + vᵀAv + O(ε) + o(1)) + b² L⁵ R₁(0);
(56) bounds the second part by H L⁴ ∫_𝔪 |S G|², and (35), with C₁ = 6.7814 from (31), gives
  ∫_𝔪 |S G|² ≤ 2NL²((C₁-2)/2 C₀R₀ + log 2/2 + O(ε) + o(1)) - L R₁(0);
(57) makes the third part o(NL⁶). With b² - H ≤ 0 and R₁(0)/(2NL) ≥ 11 log 2/50 + o(1),
log 2/2 - 11 log 2/50 = 7 log 2/25 and one gets (58).

Contents.
* `r6pp`: the weighted count (3) for K = 6.
* `integral_split`: ∫_{[0,1]} = ∫_𝔐 + ∫_{𝔪 \ E} + ∫_{𝔪 ∩ E}. PROVED.
* `assembly58`: the real-number assembly of (30), (35), (56), (57), Lemma 2.1 and the R₁ bound
  into the margin of (58). PROVED.
* `Lemma21`, `Display30Upper`, `Minor35`: the three analytic inputs not in Lean, as Props.
* `r6_lower`: r₆''(N) ≥ c N L⁶ for large even N, CONDITIONAL ON `Lemma21`, `Display30Upper`,
  `Minor35`, `MinorSup1924` and the cited constants of `k6_wired`.
* `C1_slack`: (58) at the paper's bounds holds for every C₁ ≤ 6.93, so C₁ = 6.7814 has room. PROVED.

Unit U-1429, PC run 20261021T1303Z-13145. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1429Display58

open Set Real MeasureTheory Filter
open LeanLab.Linnik.U1412Display53 (zL)
open LeanLab.Linnik.LiLiuDisplay37 (primesIn logw)
open LeanLab.Linnik.U1426ChainWire

/-! ### The count r₆''(N), display (3) -/

/-- `r₆''(N) = ∑ (log p₁)(log p₂)` over `N = p₁ + p₂ + 2^{ν₁} + ⋯ + 2^{ν₆}`,
`N₁ < p₁, p₂ ≤ N`, `1 ≤ νⱼ ≤ L`; `ν i : Fin L` encodes `νᵢ - 1`. -/
noncomputable def r6pp (N1 N L : ℕ) : ℝ :=
  ∑ p1 ∈ primesIn N1 N, ∑ p2 ∈ primesIn N1 N, ∑ ν : Fin 6 → Fin L,
    if p1 + p2 + ∑ i, 2 ^ ((ν i : ℕ) + 1) = N then Real.log p1 * Real.log p2 else 0

/-! ### The three-way split of [0,1] -/

/-- **PROVED**: for continuous `f` and measurable `E`,
`∫_{[0,1]} f = ∫_𝔐 f + ∫_{𝔪 \ E} f + ∫_{𝔪 ∩ E} f`. -/
theorem integral_split (P N : ℝ) {f : ℝ → ℝ} (hf : Continuous f) {E : Set ℝ}
    (hE : MeasurableSet E) :
    ∫ α in Icc (0 : ℝ) 1, f α = (∫ α in LiLiuLemma43Int.majorArcs P N, f α) +
      (∫ α in minorArcs P N \ E, f α) + ∫ α in minorArcs P N ∩ E, f α := by
  have hI : IntegrableOn f (Icc (0 : ℝ) 1) := hf.integrableOn_Icc
  have hM := measurableSet_majorArcs P N
  have hm := measurableSet_minorArcs P N
  have hMsub : LiLiuLemma43Int.majorArcs P N ⊆ Ioc 0 1 := fun α hα => hα.1
  have hmsub := minorArcs_sub P N
  rw [integral_Icc_eq_integral_Ioc]
  have e1 : Ioc (0 : ℝ) 1 = LiLiuLemma43Int.majorArcs P N ∪ minorArcs P N :=
    (union_sdiff_cancel hMsub).symm
  have e2 : minorArcs P N = (minorArcs P N \ E) ∪ (minorArcs P N ∩ E) :=
    (sdiff_union_inter _ _).symm
  rw [e1, setIntegral_union (show Disjoint (LiLiuLemma43Int.majorArcs P N) (minorArcs P N) from
      disjoint_sdiff_right) hm
      (hI.mono_set (hMsub.trans Ioc_subset_Icc_self)) (hI.mono_set hmsub)]
  conv_lhs => rw [e2]
  rw [setIntegral_union disjoint_sdiff_inter (hm.inter hE)
      (hI.mono_set (diff_subset.trans hmsub)) (hI.mono_set (inter_subset_left.trans hmsub)),
    add_assoc]

/-! ### The real-number assembly -/

/-- **The assembly of Section 6, PROVED.** With `X = N L⁶`, `Y = L⁵ R₁(0)`, `Z = L⁴ ∫_𝔪 |S G|²`,
`c = 1 - a - b`, `k = 11 log 2/50`, `W = (C₁-2)/2 C₀R₀ + log 2/2`, `e₀` the `O(ε)` slack:
Lemma 2.1, the split, (30), (56), (35), (57) and `R₁(0) ≥ (1 - ε) k 2NL` give
`r ≥ 2X(c² - V - b²k - H(W - k)) - X(2(1+H)e₀ + 2Hεk + 4δ + 2Hδ)`. -/
theorem assembly58 {X Y Z r Itot IM I1 I2 c V b H W k e0 δ ε : ℝ}
    (h21 : 4 * c ^ 2 * X - Itot - δ * X ≤ r) (hdec : Itot = IM + I1 + I2)
    (h30 : IM ≤ 2 * X * (c ^ 2 + V + e0 + δ) + b ^ 2 * Y) (h56 : I1 ≤ H * Z)
    (h35 : Z ≤ 2 * X * (W + e0 + δ) - Y) (h57 : I2 ≤ δ * X)
    (hR : (1 - ε) * k * (2 * X) ≤ Y) (hbH : b ^ 2 ≤ H) (hε : 0 ≤ ε) (hk : 0 ≤ k) (hX : 0 ≤ X) :
    2 * X * (c ^ 2 - V - b ^ 2 * k - H * (W - k)) -
      X * (2 * (1 + H) * e0 + 2 * H * ε * k + 4 * δ + 2 * H * δ) ≤ r := by
  have hH0 : 0 ≤ H := le_trans (sq_nonneg b) hbH
  have hHZ : H * Z ≤ H * (2 * X * (W + e0 + δ) - Y) := mul_le_mul_of_nonneg_left h35 hH0
  have hbY : (b ^ 2 - H) * Y ≤ (b ^ 2 - H) * ((1 - ε) * k * (2 * X)) :=
    mul_le_mul_of_nonpos_left hR (by linarith)
  have hb2ε : 0 ≤ b ^ 2 * ε * k * X := by
    have := sq_nonneg b; positivity
  nlinarith

/-- Vacuity of `assembly58`: all hypotheses hold at `X = 1`, `Y = 0`, `k = 0`, `b = 0`, `H = 0`,
`IM = 2`, `I1 = I2 = 0`, `c = 1`, `V = W = e0 = δ = ε = 0`, `r = 2`. -/
theorem assembly58_instance :
    2 * (1 : ℝ) * (1 ^ 2 - 0 - 0 ^ 2 * 0 - 0 * (0 - 0)) -
      1 * (2 * (1 + 0) * 0 + 2 * 0 * 0 * 0 + 4 * 0 + 2 * 0 * 0) ≤ (2 : ℝ) :=
  assembly58 (X := 1) (Y := 0) (Z := 0) (Itot := 2) (IM := 2) (I1 := 0) (I2 := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) le_rfl le_rfl zero_le_one

/-! ### The analytic inputs not in Lean, as named Props -/

/-- The abbreviations of Section 6: `a = 1/4`, `b = 1/16`, `N₁ = ⌊N^{1-κ}⌋`, `L = Lfun N`. -/
noncomputable def N1f (κ : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) ^ (1 - κ)⌋₊

/-- The integrand `|S(α) F(G(α))|²` at `a = 1/4`, `b = 1/16`. -/
noncomputable def SFG (κ : ℝ) (N : ℕ) (α : ℝ) : ℝ :=
  ‖Sm (N1f κ N) N α * FG (1 / 4) (1 / 16) (Lfun N) α‖ ^ 2

/-- `|S(α) G(α)|²`. -/
noncomputable def SG (κ : ℝ) (N : ℕ) (α : ℝ) : ℝ := ‖Sm (N1f κ N) N α * Gs (Lfun N) α‖ ^ 2

/-- `R₁(0) = ∫_𝔐 |S|²`. -/
noncomputable def R1 (κ : ℝ) (P : ℕ → ℝ) (N : ℕ) : ℝ :=
  LiLiuLemma43Int.R10 (primesIn (N1f κ N) N) logw (P N) N

/-- **Lemma 2.1, NOT IN LEAN, a named hypothesis**: for large even `N`,
`r₆''(N) ≥ 4(1-a-b)² N L⁶ - ∫_0^1 |S F(G)|² + o(N L⁶)`. -/
def Lemma21 (κ : ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ N : ℕ in atTop, Even N →
    4 * (1 - 1 / 4 - 1 / 16 : ℝ) ^ 2 * N * (Lfun N : ℝ) ^ 6 - (∫ α in Icc (0 : ℝ) 1, SFG κ N α) -
      δ * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N)

/-- **Display (30), upper half, NOT IN LEAN, a named hypothesis**: with `V = vᵀAv` and `e₀` the
`O(ε)` slack, `∫_𝔐 |S F(G)|² ≤ 2NL⁶((1-a-b)² + V + e₀ + o(1)) + b² L⁵ R₁(0)`. -/
def Display30Upper (κ : ℝ) (P : ℕ → ℝ) (V e0 : ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
    ∫ α in LiLiuLemma43Int.majorArcs (P N) N, SFG κ N α ≤
      2 * (N * (Lfun N : ℝ) ^ 6) * ((1 - 1 / 4 - 1 / 16) ^ 2 + V + e0 + δ) +
        (1 / 16) ^ 2 * ((Lfun N : ℝ) ^ 5 * R1 κ P N)

/-- **Display (35), NOT IN LEAN, a named hypothesis**, the minor arc bound from (31) with
`C₁ = 6.7814`, (33) and (34): `∫_𝔪 |S G|² ≤ 2NL²((C₁-2)/2 C₀R₀ + log 2/2 + e₀ + o(1)) - L R₁(0)`. -/
def Minor35 (κ : ℝ) (P : ℕ → ℝ) (CR e0 : ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
    ∫ α in minorArcs (P N) N, SG κ N α ≤
      2 * N * (Lfun N : ℝ) ^ 2 * ((6.7814 - 2) / 2 * CR + Real.log 2 / 2 + e0 + δ) -
        (Lfun N : ℝ) * R1 κ P N

lemma continuous_SFG (κ : ℝ) (N : ℕ) : Continuous (SFG κ N) :=
  ((continuous_SA _ _).mul (continuous_FG _ _ _)).norm.pow 2

/-! ### The conclusion -/

/-- The error budget of `r6_core`. -/
lemma stuff_le {m0 e0 H ε k δ : ℝ} (hm : 0 ≤ m0) (he0 : 0 ≤ e0) (he01 : e0 < m0 / 4)
    (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (hε0 : 0 ≤ ε) (hε8 : ε ≤ m0 / 8) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hδ : δ = m0 / 48) :
    2 * (1 + H) * e0 + 2 * H * ε * k + 4 * δ + 2 * H * δ ≤ 11 / 8 * m0 := by
  have h1 : 2 * (1 + H) * e0 ≤ m0 := by nlinarith
  have hHk : H * k ≤ 1 := by nlinarith
  have h2 : H * ε * k ≤ ε := by nlinarith
  have h3 : H * δ ≤ δ := by subst hδ; nlinarith
  subst hδ
  linarith

/-- The core of the conclusion, with `H`, `V`, the margin `m₀` of (58) and the slack `e₀` as
parameters. CONDITIONAL ON `Lemma21 κ`, `Display30Upper`, `Minor35`, `MinorSup1924 P`. -/
theorem r6_core {H V CR W k m0 e0 κ : ℝ} (P : ℕ → ℝ) (hmax : ∀ z ∈ LiLiu.Dl (5 / 6), Q6 z ≤ H)
    (hb : (1 / 16 : ℝ) ^ 2 ≤ H) (hH1 : H ≤ 1) (hk : k = 11 * Real.log 2 / 50)
    (hW : W = (6.7814 - 2) / 2 * CR + Real.log 2 / 2)
    (hm0 : m0 = (1 - 1 / 4 - 1 / 16) ^ 2 - V - (1 / 16) ^ 2 * k - H * (W - k)) (hm0pos : 0 < m0)
    (he0 : 0 ≤ e0) (he01 : e0 < m0 / 4) (hκ : 0 < κ)
    (hP11 : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N)
    (hPup : ∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ))
    (hP2 : ∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) (hMS : MinorSup1924 P)
    (h30 : Display30Upper κ P V e0) (h35 : Minor35 κ P CR e0) (h21 : Lemma21 κ) :
    ∀ᶠ N : ℕ in atTop, Even N → m0 / 2 * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) := by
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hk1 : k ≤ 1 := by rw [hk]; linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = m0 / 48 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (1 / 2) (m0 / 8) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; exact lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := by rw [hεdef]; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hε8 : ε ≤ m0 / 8 := by rw [hεdef]; exact min_le_right _ _
  filter_upwards [h21 δ hδ, h30 δ hδ, h35 δ hδ,
    lemma61 hκ P hMS (a := 1 / 4) (b := 1 / 16) (by norm_num) (by norm_num) δ hδ,
    R1_ge_11log2 hκ hε0 hε1 P hP11 hPup hP2, eventually_Lfun_ge_one]
    with N h21N h30N h35N h57N hRN hL hEven
  have h21' := h21N hEven
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = N * (Lfun N : ℝ) ^ 6 := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hsplit := integral_split (P N) N (continuous_SFG κ N) (measurableSet_exc (5 / 6) (Lfun N))
  have h56 := display56 hmax hL (S := Sm (N1f κ N) N) (continuous_SA _ _)
    (measurableSet_minorArcs (P N) N) (minorArcs_sub (P N) N)
  have hL4 : (0 : ℝ) ≤ (Lfun N : ℝ) ^ 4 := by positivity
  have hL5 : (0 : ℝ) ≤ (Lfun N : ℝ) ^ 5 := by positivity
  have h35' : (Lfun N : ℝ) ^ 4 * (∫ α in minorArcs (P N) N, SG κ N α) ≤
      2 * X * (W + e0 + δ) - (Lfun N : ℝ) ^ 5 * R1 κ P N :=
    calc _ ≤ _ := mul_le_mul_of_nonneg_left h35N hL4
      _ = _ := by rw [hX, hW]; ring
  have hR' : (1 - ε) * k * (2 * X) ≤ (Lfun N : ℝ) ^ 5 * R1 κ P N :=
    calc (1 - ε) * k * (2 * X) = (Lfun N : ℝ) ^ 5 *
          ((1 - ε) * (11 * Real.log 2 / 50) * (2 * N * (Lfun N : ℝ))) := by rw [hX, hk]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hRN hL5
  have h21'' : 4 * (1 - 1 / 4 - 1 / 16 : ℝ) ^ 2 * X - (∫ α in Icc (0 : ℝ) 1, SFG κ N α) -
      δ * X ≤ r6pp (N1f κ N) N (Lfun N) :=
    calc _ = 4 * (1 - 1 / 4 - 1 / 16 : ℝ) ^ 2 * N * (Lfun N : ℝ) ^ 6 -
          (∫ α in Icc (0 : ℝ) 1, SFG κ N α) - δ * (N * (Lfun N : ℝ) ^ 6) := by rw [hX]; ring
      _ ≤ _ := h21'
  have h30' : (∫ α in LiLiuLemma43Int.majorArcs (P N) N, SFG κ N α) ≤
      2 * X * ((1 - 1 / 4 - 1 / 16) ^ 2 + V + e0 + δ) +
        (1 / 16) ^ 2 * ((Lfun N : ℝ) ^ 5 * R1 κ P N) := by rw [hX]; exact h30N
  have h57' : (∫ α in minorArcs (P N) N ∩ {α | zL (Lfun N) α ∉ LiLiu.Dl (5 / 6)}, SFG κ N α) ≤
      δ * X :=
    calc _ ≤ δ * N * (Lfun N : ℝ) ^ 6 := h57N
      _ = _ := by rw [hX]; ring
  have h56' : (∫ α in minorArcs (P N) N \ {α | zL (Lfun N) α ∉ LiLiu.Dl (5 / 6)}, SFG κ N α) ≤
      H * ((Lfun N : ℝ) ^ 4 * (∫ α in minorArcs (P N) N, SG κ N α)) :=
    calc _ ≤ _ := h56
      _ = _ := by rw [mul_assoc]; rfl
  have hA := assembly58 (c := 1 - 1 / 4 - 1 / 16) (b := 1 / 16) h21'' hsplit h30' h56' h35'
    h57' hR' hb hε0.le hk0 hX0
  rw [← hm0] at hA
  have hH0 : 0 ≤ H := le_trans (by positivity) hb
  have hstuff := stuff_le hm0pos.le he0 he01 hH0 hH1 hε0.le hε8 hk0 hk1 hδdef
  have hfin := mul_le_mul_of_nonneg_left hstuff hX0
  have hpos := mul_nonneg hX0 hm0pos.le
  rw [← hX]
  linarith only [hA, hfin, hpos]

/-- **r₆''(N) ≫ N L⁶, CONDITIONAL ON `Lemma21 κ`, `Display30Upper`, `Minor35`, `MinorSup1924 P`,
the conditions (24) on `P`, and the cited constants of `k6_wired`**: Platt-Trudgian
`C₀R₀ < 1.2784421041`, Johnston-Trudgian `A(2), A(3)`, the tail `T`. `V` is the paper's `vᵀAv`
with `A = A_* + T`. There is `e₁ > 0` such that for every `O(ε)` slack `e₀ < e₁` the inputs
give `r₆''(N) ≥ c N L⁶` for all large even `N`. -/
theorem r6_lower {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) :
    ∃ e1 > 0, ∀ e0 : ℝ, 0 ≤ e0 → e0 < e1 → ∀ {κ : ℝ}, 0 < κ → ∀ P : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N) →
      (∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) →
      MinorSup1924 P →
      Display30Upper κ P (∑ i, ∑ j, (LiLiu.v i : ℝ) * ((LiLiu.Astar i j : ℝ) + T i j) *
        (LiLiu.v j : ℝ)) e0 →
      Minor35 κ P CR e0 → Lemma21 κ →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) := by
  obtain ⟨H, -, hmax, hb, hH, -, -, hk6⟩ := k6_wired T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ∑ i, ∑ j, (LiLiu.v i : ℝ) * ((LiLiu.Astar i j : ℝ) + T i j) *
      (LiLiu.v j : ℝ) := ⟨_, rfl⟩
  rw [← hV] at hk6 ⊢
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℝ, m0 = (1 - 1 / 4 - 1 / 16) ^ 2 - V - (1 / 16) ^ 2 *
      (11 * Real.log 2 / 50) - H * (((6.7814 - 2) / 2 * CR + Real.log 2 / 2) -
        11 * Real.log 2 / 50) := ⟨_, rfl⟩
  have hm0pos : 0 < m0 := by rw [hm0]; linarith
  refine ⟨m0 / 4, by positivity, fun e0 he0 he01 κ hκ P hP11 hPup hP2 hMS h30 h35 h21 =>
    ⟨m0 / 2, by positivity, r6_core P hmax hb (by linarith) rfl rfl hm0 hm0pos he0 he01 hκ
      hP11 hPup hP2 hMS h30 h35 h21⟩⟩

/-! ### C₁ = 6.7814 against (58) -/

/-- **PROVED**: at the paper's bounds `vᵀAv < 13/500` (60), `H < 2/15` (61),
`C₀R₀ < 1.2784421041` and `a = 1/4`, `b = 1/16`, the criterion (58) holds for every
`C₁ ≤ 6.93`; the cited `C₁ = 6.7814` is inside. Numerically the critical value is 6.93002. -/
theorem C1_slack {V H CR C1 : ℝ} (hV : V < 13 / 500) (hH0 : 0 ≤ H) (hH : H < 2 / 15)
    (hCR0 : 0 ≤ CR) (hCR : CR < 1.2784421041) (hC2 : 2 ≤ C1) (hC1 : C1 ≤ 6.93) :
    V + 11 * (1 / 16) ^ 2 * Real.log 2 / 50 + H * ((C1 - 2) / 2 * CR + 7 * Real.log 2 / 25) <
      (1 - 1 / 4 - 1 / 16) ^ 2 := by
  have hl2 := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (C1 - 2) / 2 * CR ≤ (6.93 - 2) / 2 * 1.2784421041 := by
    have : 0 ≤ (C1 - 2) / 2 := by linarith
    nlinarith
  have h2 : 0 ≤ (C1 - 2) / 2 * CR + 7 * Real.log 2 / 25 := by
    have : 0 ≤ (C1 - 2) / 2 := by linarith
    positivity
  have h3 : H * ((C1 - 2) / 2 * CR + 7 * Real.log 2 / 25) ≤
      2 / 15 * ((6.93 - 2) / 2 * 1.2784421041 + 7 * 0.6931471808 / 25) := by
    have : (C1 - 2) / 2 * CR + 7 * Real.log 2 / 25 ≤
        (6.93 - 2) / 2 * 1.2784421041 + 7 * 0.6931471808 / 25 := by linarith
    nlinarith
  nlinarith

/-- `C₁ = 6.7814` gives `(C₁ - 2)/2 = 2.3907`, and `log 2/2 - 11 log 2/50 = 7 log 2/25`. -/
theorem C1_arith : ((6.7814 : ℝ) - 2) / 2 = 2.3907 ∧
    ∀ x : ℝ, x / 2 - 11 * x / 50 = 7 * x / 25 := ⟨by norm_num, fun x => by ring⟩

/-- Vacuity of `C1_slack` at the paper's `C₁ = 6.7814`, `V = 1/50`, `H = 1/10`, `CR = 1.27`. -/
theorem C1_slack_instance :
    (1 / 50 : ℝ) + 11 * (1 / 16) ^ 2 * Real.log 2 / 50 +
      1 / 10 * ((6.7814 - 2) / 2 * 1.27 + 7 * Real.log 2 / 25) < (1 - 1 / 4 - 1 / 16) ^ 2 :=
  C1_slack (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end LeanLab.Linnik.U1429Display58
