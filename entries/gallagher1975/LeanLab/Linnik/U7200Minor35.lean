module

public import LeanLab.Linnik.U1434Lemma21

/-!
Li-Liu, arXiv 2610.15784, Section 4, the minor arc bound (35) from (33) and (34), with (31),
(14) and the singular series sum of (20) stated as cited Props. Read by WebFetch on the
unversioned arxiv.org/html/2610.15784, 2026-10-21.

The paper's argument. (31), Johnston-Trudgian, C₁ = 6.7814: for nonzero even h with |h| < N,
  #{p₁, p₂ ≤ N : p₁ - p₂ = h} ≤ (C₁ + o(1))/2 · N 𝔖(h)/(log N)².
(32): R(h) ≤ (C₁ + o(1))/2 · N 𝔖(h). (33): ∫_0^1 |S G|² = L R(0) + ∑_{h ≠ 0} r₁,₁(h) R(h)
  ≤ N L² (log 2 + C₁ C₀R₀ + o(1)).
(34): ∫_𝔐 |S G|² = L R₁(0) + 2NL²(C₀R₀ + O(ε) + o(1)).
(35) = (33) - (34): ∫_𝔪 |S G|² ≤ 2NL²((C₁-2)/2 C₀R₀ + log 2/2 + O(ε) + o(1)) - L R₁(0).

Contents.
* `minor35_arith`: the real arithmetic of (33) - (34) = (35). PROVED.
* `integral_split2`: ∫_{[0,1]} = ∫_𝔐 + ∫_𝔪 for continuous f. PROVED.
* `minor35_of`: `Minor35 κ P CR e0` from `Display33 κ CR` and `Display34Lower κ P CR e0`. PROVED,
  the step from the two Props to (35); so CONDITIONAL ON those two as inputs.
* `Display31`, `SingSum20`, `singS`, `C0`: the cited sieve bound (31), the singular series (14)
  and the upper half of the limit (20) at i = j = 1, stated for the record and for the next unit,
  which derives `Display33` from them; NOT used yet.
* `r6_lower''`: r₆''(N) ≫ N L⁶, CONDITIONAL ON `Display30Upper`, `Display33`, `Display34Lower`,
  `MinorSup1924 P`, conditions (24) and the cited constants of `k6_wired`; `Minor35` is gone.

Unit U-7200, CLOUD MANUAL-N2. AI-written Lean code, Claude. KNOWN mathematics, the paper's own
argument. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U7200Minor35

open Set Real MeasureTheory Filter
open LeanLab.Linnik.LiLiuDisplay37 (primesIn logw)
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U1429Display58

/-! ### Cited inputs, stated as printed -/

/-- `C₀ = ∏_{p > 2} (1 - 1/(p-1)²)`, the twin prime constant, display (14). -/
noncomputable def C0 : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)

/-- The singular series (14): `𝔖(h) = 2C₀ ∏_{p | h, p > 2} (p-1)/(p-2)` for nonzero even `h`.
The paper gives no value for odd `h` or `h = 0`; here it is `0` there, and no statement below
uses those values. -/
noncomputable def singS (h : ℤ) : ℝ :=
  if h ≠ 0 ∧ Even h then
    2 * C0 * ∏ p ∈ h.natAbs.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2)
  else 0

/-- The number of prime pairs `p₁, p₂ ≤ N` with `p₁ - p₂ = h`. -/
noncomputable def pairCount (N : ℕ) (h : ℤ) : ℕ :=
  ((primesIn 0 N ×ˢ primesIn 0 N).filter (fun x => (x.1 : ℤ) - x.2 = h)).card

/-- **Display (31), CITED, Johnston-Trudgian with `C₁`**: uniformly for nonzero even `h` with
`|h| < N`, `#{p₁, p₂ ≤ N : p₁ - p₂ = h} ≤ (C₁ + o(1))/2 · N 𝔖(h)/(log N)²`. The paper uses
`C₁ = 6.7814`. -/
def Display31 (C1 : ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ N : ℕ in atTop, ∀ h : ℤ, h ≠ 0 → Even h → |h| < N →
    (pairCount N h : ℝ) ≤ (C1 + δ) / 2 * (N * singS h / Real.log N ^ 2)

/-- **The upper half of (20) at i = j = 1, CITED, with `B₁₁ = C₀R₀`**: since
`(1/2L²) ∑_{h ≠ 0} r₁,₁(h) 𝔖(h) → C₀R₀`, the sum over `1 ≤ ν ≠ μ ≤ L` of `𝔖(2^ν - 2^μ)` is at
most `2L²(C₀R₀ + o(1))`. -/
def SingSum20 (CR : ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ L : ℕ in atTop,
    ∑ ν ∈ Finset.Icc 1 L, ∑ μ ∈ Finset.Icc 1 L,
      (if ν = μ then 0 else singS ((2 : ℤ) ^ ν - 2 ^ μ)) ≤ 2 * (L : ℝ) ^ 2 * (CR + δ)

/-! ### Displays (33) and (34) as named Props -/

/-- **Display (33), NOT IN LEAN, a named hypothesis**, with `C₁ = 6.7814`:
`∫_0^1 |S G|² ≤ N L² (log 2 + C₁ C₀R₀ + o(1))`. The paper derives it from (31), (32), (20) and
`R(0) = ∑ log² p`. -/
def Display33 (κ : ℝ) (CR : ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
    ∫ α in Icc (0 : ℝ) 1, SG κ N α ≤
      N * (Lfun N : ℝ) ^ 2 * (Real.log 2 + 6.7814 * CR + δ)

/-- **Display (34), lower half, NOT IN LEAN, a named hypothesis**: with `e₀` the `O(ε)` slack,
`∫_𝔐 |S G|² ≥ L R₁(0) + 2NL²(C₀R₀ - e₀ - o(1))`. The paper states (34) as an equality with
`O(ε) + o(1)`; only this half is used for (35). -/
def Display34Lower (κ : ℝ) (P : ℕ → ℝ) (CR e0 : ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
    (Lfun N : ℝ) * R1 κ P N + 2 * N * (Lfun N : ℝ) ^ 2 * (CR - e0 - δ) ≤
      ∫ α in LiLiuLemma43Int.majorArcs (P N) N, SG κ N α

/-! ### (35) from (33) and (34) -/

lemma continuous_SG (κ : ℝ) (N : ℕ) : Continuous (SG κ N) :=
  ((continuous_SA _ _).mul (continuous_Gs _)).norm.pow 2

/-- **PROVED**: `∫_{[0,1]} f = ∫_𝔐 f + ∫_𝔪 f` for continuous `f`. -/
theorem integral_split2 (P N : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ α in Icc (0 : ℝ) 1, f α = (∫ α in LiLiuLemma43Int.majorArcs P N, f α) +
      ∫ α in minorArcs P N, f α := by
  have h := integral_split P N hf (E := (∅ : Set ℝ)) MeasurableSet.empty
  simpa only [sdiff_empty, inter_empty, Measure.restrict_empty, integral_zero_measure,
    add_zero] using h

/-- **The arithmetic of (33) - (34) = (35), PROVED.** With `Y = N L²`, `C₁ = 6.7814`. -/
theorem minor35_arith {Itot IM Im Y LR CR e0 δ : ℝ} (_hY : 0 ≤ Y) (hsplit : Itot = IM + Im)
    (h33 : Itot ≤ Y * (Real.log 2 + 6.7814 * CR + δ))
    (h34 : LR + 2 * Y * (CR - e0 - δ / 2) ≤ IM) :
    Im ≤ 2 * Y * ((6.7814 - 2) / 2 * CR + Real.log 2 / 2 + e0 + δ) - LR := by
  nlinarith

/-- **Display (35) from (33) and (34), PROVED**: `Display33 κ CR` and `Display34Lower κ P CR e0`
give `Minor35 κ P CR e0` of U1429Display58. -/
theorem minor35_of {κ CR e0 : ℝ} {P : ℕ → ℝ} (h33 : Display33 κ CR)
    (h34 : Display34Lower κ P CR e0) : Minor35 κ P CR e0 := by
  intro δ hδ
  filter_upwards [h33 δ hδ, h34 (δ / 2) (by positivity)] with N h33N h34N
  have hsplit := integral_split2 (P N) N (continuous_SG κ N)
  have hY : (0 : ℝ) ≤ N * (Lfun N : ℝ) ^ 2 := by positivity
  have h := minor35_arith hY hsplit h33N
    (by have := h34N; rw [mul_assoc 2 (N : ℝ)] at this; exact this)
  calc _ ≤ _ := h
    _ = _ := by ring

/-- Vacuity of `minor35_arith`: `Y = 1`, `CR = 0`, `e0 = δ = 0`, `LR = 0`, `IM = 0`,
`Itot = Im = 0`. -/
theorem minor35_arith_instance :
    (0 : ℝ) ≤ 2 * 1 * ((6.7814 - 2) / 2 * 0 + Real.log 2 / 2 + 0 + 0) - 0 :=
  minor35_arith (Itot := 0) (IM := 0) zero_le_one (by norm_num)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); nlinarith) (by norm_num)

/-! ### The conclusion with `Minor35` removed -/

/-- **r₆''(N) ≫ N L⁶, CONDITIONAL ON `Display30Upper`, `Display33`, `Display34Lower`,
`MinorSup1924 P`, the conditions (24) on `P`, and the cited constants of `k6_wired`**:
Platt-Trudgian `C₀R₀ < 1.2784421041`, Johnston-Trudgian `A(2), A(3)`, the tail `T`. This is
`U1434Lemma21.r6_lower'` with `Minor35` replaced by (33) and the lower half of (34), via
`minor35_of`. -/
theorem r6_lower'' {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
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
      Display33 κ CR → Display34Lower κ P CR e0 →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) := by
  obtain ⟨e1, he1, h⟩ := U1434Lemma21.r6_lower' T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33
  exact ⟨e1, he1, fun e0 he0 he01 κ hκ P hP11 hPup hP2 hMS h30 h33 h34 =>
    h e0 he0 he01 hκ P hP11 hPup hP2 hMS h30 (minor35_of h33 h34)⟩

end LeanLab.Linnik.U7200Minor35

