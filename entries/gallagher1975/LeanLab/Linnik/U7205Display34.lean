module

public import LeanLab.Linnik.U7203Display33

/-!
Li-Liu, arXiv 2610.15784, Section 4, the lower half of display (34) from Lemma 4.2 at
i = j = 1, display (29). Read by WebFetch on the unversioned arxiv.org/html/2610.15784,
2026-10-21.

The paper's argument. With `R₁(h) = ∫_𝔐 |S(α)|² e(-hα) dα`, display (26), and
`|G(α)|² = ∑_{ν, μ} e((2^ν - 2^μ)α)`, one has
  `∫_𝔐 |S G|² = ∑_h r₁,₁(h) R₁(h) = L R₁(0) + ∑_{h ≠ 0} r₁,₁(h) R₁(h)`,
since `r₁,₁(0) = L`. Lemma 4.2, display (29), at i = j = 1 gives
`∑_{h ≠ 0} r₁,₁(h) R₁(h) = 2NL²(1 + A₁₁ + O(ε) + o(1))`, and this is (34) with `1 + A₁₁ = C₀R₀`.

Contents.
* `R1h`: `R₁(h)` of (26), complex valued.
* `normG_sq`: `|G(α)|² = ∑_{ν, μ} Re e((2^ν - 2^μ)α)`. PROVED.
* `integral_major_SG`: the major arc identity `∫_𝔐 |S G|² = L R₁(0) + ∑_{ν ≠ μ} Re R₁(2^ν - 2^μ)`.
  PROVED unconditional.
* `Lemma42Lower11`: the lower half of the real part of (29) at i = j = 1, CITED, a named Prop.
* `display34Lower_of`: `Display34Lower κ P (1 + A₁₁) e₀` from `Lemma42Lower11 κ P A₁₁ e₀`.
  PROVED, CONDITIONAL ON the cited Lemma 4.2 only.
* `r6_lower4`: r₆''(N) ≫ N L⁶, CONDITIONAL ON `Display30Upper`, the cited (31), (20), Lemma 4.2,
  `MinorSup1924 P`, conditions (24) on `P` and the cited constants of `k6_wired`;
  `Display34Lower` is gone.

Unit U-7205, CLOUD MANUAL-N2. AI-written Lean code, Claude. KNOWN mathematics, the paper's own
argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U7205Display34

open Set Real MeasureTheory Filter Finset
open LeanLab.Linnik.U1412Display53 (eC continuous_eC)
open LeanLab.Linnik.LiLiuDisplay37 (primesIn logw)
open LeanLab.Linnik.LiLiuLemma43 (SA)
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U1429Display58
open LeanLab.Linnik.U7200Minor35
open LeanLab.Linnik.U7203Display33

/-- `R₁(h) = ∫_𝔐 |S(α)|² e(-hα) dα`, display (26), with `S` over `N₁ < p ≤ N`. -/
noncomputable def R1h (κ : ℝ) (P : ℕ → ℝ) (N : ℕ) (h : ℤ) : ℂ :=
  ∫ α in LiLiuLemma43Int.majorArcs (P N) N,
    ((‖Sm (N1f κ N) N α‖ ^ 2 : ℝ) : ℂ) * eC (-(h : ℝ) * α)

/-- **Lemma 4.2, display (29), at i = j = 1, lower half of the real part, CITED, a named Prop**:
`∑_{h ≠ 0} r₁,₁(h) R₁(h) = 2NL²(1 + A₁₁ + O(ε) + o(1))`, written as the sum over ordered pairs
`1 ≤ ν ≠ μ ≤ L` of `R₁(2^ν - 2^μ)`, which is the same sum since `r₁,₁(h)` counts those pairs with
`2^ν - 2^μ = h`; `e₀` is the `O(ε)` slack. -/
def Lemma42Lower11 (κ : ℝ) (P : ℕ → ℝ) (A11 e0 : ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
    2 * N * (Lfun N : ℝ) ^ 2 * (1 + A11 - e0 - δ) ≤
      ∑ ν ∈ Finset.Icc 1 (Lfun N), ∑ μ ∈ Finset.Icc 1 (Lfun N),
        (if ν = μ then 0 else (R1h κ P N ((2 : ℤ) ^ ν - 2 ^ μ)).re)

lemma conj_eC (t : ℝ) : (starRingEnd ℂ) (eC t) = eC (-t) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

/-- **`|G(α)|² = ∑_{ν, μ} Re e((2^ν - 2^μ)α)`, PROVED.** -/
lemma normG_sq (L : ℕ) (α : ℝ) :
    ‖Gs L α‖ ^ 2 = ∑ ν ∈ Finset.Icc 1 L, ∑ μ ∈ Finset.Icc 1 L,
      (eC (((2 : ℝ) ^ ν - 2 ^ μ) * α)).re := by
  have h : ((‖Gs L α‖ ^ 2 : ℝ) : ℂ) = Gs L α * (starRingEnd ℂ) (Gs L α) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : Gs L α * (starRingEnd ℂ) (Gs L α) = ∑ ν ∈ Finset.Icc 1 L, ∑ μ ∈ Finset.Icc 1 L,
      eC (((2 : ℝ) ^ ν - 2 ^ μ) * α) := by
    unfold Gs
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [conj_eC, ← U1434Lemma21.eC_add]
    congr 1; ring
  have h3 := congrArg Complex.re (h.trans h2)
  rw [Complex.ofReal_re] at h3
  rw [h3, Complex.re_sum]
  exact Finset.sum_congr rfl fun ν _ => Complex.re_sum _ _

lemma majorArcs_sub (P N : ℝ) : LiLiuLemma43Int.majorArcs P N ⊆ Icc 0 1 :=
  fun _ hα => Ioc_subset_Icc_self hα.1

lemma integrableOn_major {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f) (P N : ℝ) :
    IntegrableOn f (LiLiuLemma43Int.majorArcs P N) :=
  (hf.integrableOn_Icc (a := 0) (b := 1)).mono_set (majorArcs_sub P N)

lemma continuous_term (κ : ℝ) (N : ℕ) (c : ℝ) :
    Continuous fun α : ℝ => ((‖Sm (N1f κ N) N α‖ ^ 2 : ℝ) : ℂ) * eC (c * α) :=
  (Complex.continuous_ofReal.comp ((continuous_SA _ _).norm.pow 2)).mul
    (continuous_eC.comp (continuous_const.mul continuous_id))

/-- One term: `∫_𝔐 |S|² Re e(cα) = Re ∫_𝔐 |S|² e(cα)`. -/
lemma integral_term (κ : ℝ) (P : ℕ → ℝ) (N : ℕ) (c : ℝ) :
    ∫ α in LiLiuLemma43Int.majorArcs (P N) N, ‖Sm (N1f κ N) N α‖ ^ 2 * (eC (c * α)).re =
      (∫ α in LiLiuLemma43Int.majorArcs (P N) N,
        ((‖Sm (N1f κ N) N α‖ ^ 2 : ℝ) : ℂ) * eC (c * α)).re := by
  have h := integral_re (integrableOn_major (continuous_term κ N c) (P N) N)
  simpa only [RCLike.re_to_complex, Complex.re_ofReal_mul] using h

/-- **The major arc identity behind (34), PROVED unconditional**:
`∫_𝔐 |S G|² = L R₁(0) + ∑_{1 ≤ ν ≠ μ ≤ L} Re R₁(2^μ - 2^ν)`, the same sum as over
`R₁(2^ν - 2^μ)` after swapping ν and μ. -/
theorem integral_major_SG (κ : ℝ) (P : ℕ → ℝ) (N : ℕ) :
    ∫ α in LiLiuLemma43Int.majorArcs (P N) N, SG κ N α =
      (Lfun N : ℝ) * R1 κ P N +
        ∑ ν ∈ Finset.Icc 1 (Lfun N), ∑ μ ∈ Finset.Icc 1 (Lfun N),
          (if ν = μ then 0 else (R1h κ P N ((2 : ℤ) ^ μ - 2 ^ ν)).re) := by
  set L := Lfun N
  set I := Finset.Icc 1 L
  set M := LiLiuLemma43Int.majorArcs (P N) N
  have hpt : ∀ α, SG κ N α = ∑ ν ∈ I, ∑ μ ∈ I,
      ‖Sm (N1f κ N) N α‖ ^ 2 * (eC (((2 : ℝ) ^ ν - 2 ^ μ) * α)).re := fun α => by
    unfold SG
    rw [norm_mul, mul_pow, normG_sq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => Finset.mul_sum _ _ _
  have hint : ∀ c : ℝ, IntegrableOn
      (fun α => ‖Sm (N1f κ N) N α‖ ^ 2 * (eC (c * α)).re) M := fun c =>
    integrableOn_major (((continuous_SA _ _).norm.pow 2).mul
      (Complex.continuous_re.comp (continuous_eC.comp (continuous_const.mul continuous_id))))
        (P N) N
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun ν _ => integrable_finsetSum _ fun μ _ => hint _)]
  simp_rw [integral_finsetSum _ (fun μ _ => hint _)]
  calc _ = ∑ ν ∈ I, ∑ μ ∈ I, ((if ν = μ then R1 κ P N else 0) +
        (if ν = μ then 0 else (R1h κ P N ((2 : ℤ) ^ μ - 2 ^ ν)).re)) := by
        refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
        rw [integral_term]
        by_cases h : ν = μ
        · subst h
          rw [if_pos rfl, if_pos rfl, add_zero]
          simp only [sub_self, zero_mul, U1412Display53.eC, Complex.ofReal_zero, mul_zero,
            Complex.exp_zero, mul_one]
          have h := integral_re (integrableOn_major (Complex.continuous_ofReal.comp
              ((continuous_SA (primesIn (N1f κ N) N) logw).norm.pow 2)) (P N) N)
          simp only [RCLike.re_to_complex, Complex.ofReal_re, Function.comp_apply] at h
          rw [R1, LiLiuLemma43Int.R10]
          exact h.symm
        · rw [if_neg h, if_neg h, zero_add, R1h]
          congr 3
          funext α
          push_cast
          ring_nf
    _ = _ := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        simp only [Finset.sum_ite_eq, I, Finset.mem_Icc]
        rw [Finset.sum_ite_of_true (fun ν hν => Finset.mem_Icc.mp hν), Finset.sum_const,
          Nat.card_Icc, nsmul_eq_mul]
        simp

/-- **The lower half of (34) from Lemma 4.2, PROVED, CONDITIONAL ON the cited
`Lemma42Lower11` only**: `Display34Lower κ P (1 + A₁₁) e₀`. -/
theorem display34Lower_of {κ A11 e0 : ℝ} {P : ℕ → ℝ} (h42 : Lemma42Lower11 κ P A11 e0) :
    Display34Lower κ P (1 + A11) e0 := by
  intro δ hδ
  filter_upwards [h42 δ hδ] with N hN
  rw [integral_major_SG]
  have hswap : ∑ ν ∈ Finset.Icc 1 (Lfun N), ∑ μ ∈ Finset.Icc 1 (Lfun N),
      (if ν = μ then 0 else (R1h κ P N ((2 : ℤ) ^ μ - 2 ^ ν)).re) =
      ∑ ν ∈ Finset.Icc 1 (Lfun N), ∑ μ ∈ Finset.Icc 1 (Lfun N),
      (if ν = μ then 0 else (R1h κ P N ((2 : ℤ) ^ ν - 2 ^ μ)).re) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => ?_
    simp only [eq_comm]
  rw [hswap]
  linarith

/-- **r₆''(N) ≫ N L⁶, CONDITIONAL ON `Display30Upper`, the cited (31) `Display31 6.7814`, the cited
(20) `SingSum20 CR`, the cited Lemma 4.2 at i = j = 1 `Lemma42Lower11` with `A₁₁ = A*₁₁ + T₁₁`,
`MinorSup1924 P`, the conditions (24) on `P`, and the cited constants of `k6_wired`**. This is
`U7203Display33.r6_lower3` with `Display34Lower` replaced by `display34Lower_of`. -/
theorem r6_lower4 {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) (h31 : Display31 6.7814) (h20 : SingSum20 CR) :
    ∃ e1 > 0, ∀ e0 : ℝ, 0 ≤ e0 → e0 < e1 → ∀ {κ : ℝ}, 0 < κ → ∀ P : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N) →
      (∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) →
      MinorSup1924 P →
      Display30Upper κ P (∑ i, ∑ j, (LiLiu.v i : ℝ) * ((LiLiu.Astar i j : ℝ) + T i j) *
        (LiLiu.v j : ℝ)) e0 →
      Lemma42Lower11 κ P ((LiLiu.Astar 0 0 : ℝ) + T 0 0) e0 →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) := by
  obtain ⟨e1, he1, h⟩ := r6_lower3 T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33 h31 h20
  refine ⟨e1, he1, fun e0 he0 he01 κ hκ P hP11 hPup hP2 hMS h30 h42 => ?_⟩
  have h34 := display34Lower_of h42
  rw [hA11, show (1 : ℝ) + (CR - 1) = CR by ring] at h34
  exact h e0 he0 he01 hκ P hP11 hPup hP2 hMS h30 h34

end LeanLab.Linnik.U7205Display34

