module

public import Mathlib
public import LeanLab.Helfgott2013.Decomp1538a

/-!
# Proposition 6.2 of Helfgott's ternary Goldbach paper, abstract forms

H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2, Proposition 6.2 on
page 47, proof on page 48, in an abstract measure form. The proof splits the minor arcs
`(R/Z) \ M_{δ0,r0}` into the shells `M_{δ0,r+1} \ M_{δ0,r}`, `r0 ≤ r < r1`, plus the far part
`(R/Z) \ M_{δ0,r1}`, bounds `|S2|` on each shell by `g(r)`, and feeds the shell masses `f(r)` to
Lemma 6.1.

Lab unit U-1538: Claude, Anthropic, an AI agent, wrote the statements and the skeleton of this
file. Later AI prover agents of the lab closed the leaves, as listed in PORTING.md. Checked only
by the Lean kernel; no human expert has reviewed it. Binary Goldbach is open. This file does not
formalize the ternary Goldbach theorem.

Here the space is any measurable space with a measure `μ`; `w ≥ 0` plays
`|S1|² / ∑ |a_n|²`, of total mass `1` by Parseval, and `s ≥ 0` plays `|S2|`. The sets `M r`
are any increasing family; `Decomp1538c` specialises to the arcs of display 3.5.

Encoding choices. `prop62` takes `r1` a natural number and asks hypotheses 6.4 and 6.5 only at
integers `r`, which is weaker than the paper there. `prop62_real` allows the paper's real upper
endpoint, by constant extension to the natural ceiling. The paper's side condition
`δ0 ≤ x / 2 r1²` only prevents overlap of arcs and is not used by the proof, since shells are set
differences; it is dropped. `prop62_series_real` is the form for absolutely summable coefficients.
-/

@[expose] public section

namespace LeanLab.Helfgott2013.U1538

open Finset MeasureTheory intervalIntegral

variable {X : Type*} [MeasurableSpace X]

/-- The shells of the proof of Prop. 6.2, p. 48: for `r < r1` the set `M (r+1) \ M r`, and
for `r ≥ r1` the far part `(M r)ᶜ`, used at `r = r1`. -/
def piece (M : ℕ → Set X) (r1 r : ℕ) : Set X := if r < r1 then M (r + 1) \ M r else (M r)ᶜ

/-! ### Auxiliary lemmas -/

/-- Each shell is measurable when every `M r` is; p. 48, the sets in the
definition of `f(r)`. -/
theorem piece_measurable {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r)) (r1 r : ℕ) :
    MeasurableSet (piece M r1 r) := by
  unfold piece
  split
  · exact (hM _).diff (hM _)
  · exact (hM _).compl

/-- For increasing `M`, the shells with index in `[r0, r1]` are pairwise
disjoint; p. 48, proof of Prop. 6.2. -/
theorem piece_pairwise_disjoint {M : ℕ → Set X} (hmono : Monotone M) (r0 r1 : ℕ) :
    Set.Pairwise (↑(Icc r0 r1) : Set ℕ) (Function.onFun Disjoint (piece M r1)) := by
  have ordered : ∀ i j, i < j → j ≤ r1 → Disjoint (piece M r1 i) (piece M r1 j) := by
    intro i j hij hj
    rw [piece, ite_eq_left (lt_of_lt_of_le hij hj)]
    apply Set.disjoint_left.mpr
    intro y hy hz
    have hyj : y ∈ M j := hmono (by omega) hy.1
    unfold piece at hz
    split at hz
    · exact hz.2 hyj
    · exact hz hyj
  intro i hi j hj hij
  obtain ⟨hi0, hi1⟩ := Finset.mem_Icc.mp hi
  obtain ⟨hj0, hj1⟩ := Finset.mem_Icc.mp hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ordered i j hij hj1
  · exact (ordered j i hji hi1).symm

/-- For increasing `M` and `r0 ≤ r1`, the shells with index in `[r0, r1]`
cover exactly the complement of `M r0`; p. 48, the first display of the proof of Prop. 6.2. -/
theorem piece_iUnion {M : ℕ → Set X} (hmono : Monotone M) {r0 r1 : ℕ} (hr : r0 ≤ r1) :
    ⋃ r ∈ Icc r0 r1, piece M r1 r = (M r0)ᶜ := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_compl_iff]
  constructor
  · rintro ⟨r, hr', hy⟩ hy0
    have hyr : y ∉ M r := by
      unfold piece at hy
      split at hy
      · exact hy.2
      · exact hy
    exact hyr (hmono (Finset.mem_Icc.mp hr').1 hy0)
  · intro hy0
    by_cases hy1 : y ∈ M r1
    · have hyD : y ∈ ⋃ i ∈ Ioc r0 r1, disjointed M i := by
        rw [biUnion_Ioc_disjointed_of_monotone hmono hr]
        exact ⟨hy1, hy0⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyD
      obtain ⟨hi, hyi⟩ := Set.mem_iUnion.mp hi
      obtain ⟨hi0, hi1⟩ := Finset.mem_Ioc.mp hi
      obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
      refine ⟨r, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      rw [piece, ite_eq_left (by omega), ← hmono.disjointed_add_one]
      exact hyi
    · refine ⟨r1, Finset.mem_Icc.mpr ⟨hr, le_rfl⟩, ?_⟩
      simpa only [piece, ite_eq_right (lt_irrefl _), Set.mem_compl_iff] using hy1

/-- A nonnegative integrable `w` times a nonnegative a.e. bounded measurable
`s` is integrable; p. 48, the integrand `|S1(α)|² |S2(α)|`, `S2` continuous on `R/Z`. -/
theorem integrable_mul_bdd {μ : Measure X} {w s : X → ℝ} (hwi : Integrable w μ)
    (hsm : AEStronglyMeasurable s μ) (hs0 : ∀ y, 0 ≤ s y) {C : ℝ}
    (hsC : ∀ᵐ y ∂μ, s y ≤ C) : Integrable (fun y => w y * s y) μ := by
  apply hwi.mul_bdd hsm
  filter_upwards [hsC] with y hy
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hs0 y)] using hy

/-- On the shell `r ≤ r1`, which lies outside `M r`, a bound `s ≤ G` off
`M r` gives `∫_{shell} w s ≤ G ∫_{shell} w` for `w ≥ 0`; p. 48, "Then, by display 6.5". -/
theorem piece_bound {μ : Measure X} {w s : X → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hwi : Integrable w μ)
    (hsm : AEStronglyMeasurable s μ) (hs0 : ∀ y, 0 ≤ s y) {C : ℝ} (hsC : ∀ᵐ y ∂μ, s y ≤ C)
    {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r)) (r1 r : ℕ) {G : ℝ}
    (hG : ∀ᵐ y ∂μ, y ∉ M r → s y ≤ G) :
    ∫ y in piece M r1 r, w y * s y ∂μ ≤ G * ∫ y in piece M r1 r, w y ∂μ := by
  calc
    _ ≤ ∫ y in piece M r1 r, G * w y ∂μ := by
      apply setIntegral_mono_on_ae
        (integrable_mul_bdd hwi hsm hs0 hsC).integrableOn
        (hwi.const_mul G).integrableOn (piece_measurable hM r1 r)
      filter_upwards [hG] with y hy hpiece
      have hym : y ∉ M r := by
        unfold piece at hpiece
        split at hpiece
        · exact hpiece.2
        · exact hpiece
      calc
        w y * s y ≤ w y * G := mul_le_mul_of_nonneg_left (hy hym) (hw0 y)
        _ = G * w y := mul_comm _ _
    _ = _ := integral_const_mul _ _

/-- For measurable `A ⊆ B` and integrable `w`,
`∫_{B \ A} w = ∫_B w - ∫_A w`; p. 48, the shell masses in display 6.8. -/
theorem setIntegral_diff_of_subset {μ : Measure X} {w : X → ℝ} (hwi : Integrable w μ)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    ∫ y in B \ A, w y ∂μ = (∫ y in B, w y ∂μ) - ∫ y in A, w y ∂μ := by
  exact setIntegral_sdiff hA hwi.integrableOn hAB

/-- For measurable `A` and integrable `w`,
`∫_{Aᶜ} w = ∫ w - ∫_A w`; p. 48, the far part `(R/Z) \ M_{δ0,r1}` and the line
`= 1 - I0 = H(r1) - I0`. -/
theorem setIntegral_compl' {μ : Measure X} {w : X → ℝ} (hwi : Integrable w μ) {A : Set X}
    (hA : MeasurableSet A) : ∫ y in Aᶜ, w y ∂μ = (∫ y, w y ∂μ) - ∫ y in A, w y ∂μ := by
  exact setIntegral_compl hA hwi

/-- For `g ≥ 0` non-increasing on `[r0, r1]`, the running maximum of
`g` over the integers `n, ..., r1` is `g(n)` for `r0 ≤ n ≤ r1`; p. 48, last line of the
proof of Prop. 6.2, `max_{r ≥ r0} g(r) = g(r0)`. -/
theorem hmax_of_antitoneOn (g : ℝ → ℝ) {r0 r1 n : ℕ}
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) r1, 0 ≤ g u) (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) r1))
    (hn0 : r0 ≤ n) (hn1 : n ≤ r1) : hmax (fun r : ℕ => g r) r1 n = g n := by
  have hn : (n : ℝ) ∈ Set.Icc (r0 : ℝ) r1 :=
    ⟨by exact_mod_cast hn0, by exact_mod_cast hn1⟩
  apply le_antisymm
  · unfold hmax
    rw [Finset.fold_max_le]
    refine ⟨hg0 _ hn, ?_⟩
    intro m hm
    obtain ⟨hnm, hm1⟩ := Finset.mem_Icc.mp hm
    exact hganti hn
      ⟨by exact_mod_cast hn0.trans hnm, by exact_mod_cast hm1⟩
      (by exact_mod_cast hnm)
  · exact le_hmax (fun r : ℕ => g r) le_rfl hn1

/-- For `g ≥ 0` non-increasing on `[r0, r1]` and `H' ≥ 0` integrable there,
`∫_{r0}^{r1} (max_{r ≥ u} g(r)) H'(u) du ≤ ∫_{r0}^{r1} g(u) H'(u) du`, since
`max_{r ≥ u} g(r) = g(⌈u⌉) ≤ g(u)`; p. 48, last line of the proof of Prop. 6.2. -/
theorem integral_hmax_ceil_le (g H' : ℝ → ℝ) {r0 r1 : ℕ} (hr : r0 ≤ r1)
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) r1, 0 ≤ g u) (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) r1))
    (hH'0 : ∀ u ∈ Set.Icc (r0 : ℝ) r1, 0 ≤ H' u)
    (hH'i : IntervalIntegrable H' volume (r0 : ℝ) r1) :
    ∫ u in (r0 : ℝ)..r1, hmax (fun r : ℕ => g r) r1 ⌈u⌉₊ * H' u ≤
      ∫ u in (r0 : ℝ)..r1, g u * H' u := by
  have hab : (r0 : ℝ) ≤ r1 := by exact_mod_cast hr
  have hHi : IntegrableOn H' (Set.Icc (r0 : ℝ) r1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hH'i
  have hgi : IntervalIntegrable (fun u => g u * H' u) volume (r0 : ℝ) r1 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    simpa only [IntegrableOn, Pi.mul_def] using
      hHi.mul_of_top_right
        (hganti.memLp_top (isLeast_Icc hab) (isGreatest_Icc hab) measurableSet_Icc)
  apply intervalIntegral.integral_mono_on hab
    (intervalIntegrable_ceil_mul (hmax (fun r : ℕ => g r) r1) H' hH'i) hgi
  intro u hu
  have hceil0 : r0 ≤ ⌈u⌉₊ := by
    exact_mod_cast hu.1.trans (Nat.le_ceil u)
  have hceil1 : ⌈u⌉₊ ≤ r1 := Nat.ceil_le.mpr hu.2
  rw [hmax_of_antitoneOn g hg0 hganti hceil0 hceil1]
  apply mul_le_mul_of_nonneg_right _ (hH'0 u hu)
  exact hganti hu
    ⟨by exact_mod_cast hceil0, by exact_mod_cast hceil1⟩ (Nat.le_ceil u)

/-! ### Main statements -/

/-- The integral over the complement of `M r0` is the sum
of the integrals over the shells `r0 ≤ r ≤ r1`; p. 48. -/
theorem integral_compl_eq_sum_pieces {μ : Measure X} {φ : X → ℝ} (hφ : Integrable φ μ)
    {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r)) (hmono : Monotone M) {r0 r1 : ℕ}
    (hr : r0 ≤ r1) :
    ∫ y in (M r0)ᶜ, φ y ∂μ = ∑ r ∈ Icc r0 r1, ∫ y in piece M r1 r, φ y ∂μ := by
  rw [← piece_iUnion hmono hr]
  exact integral_biUnion_finset _ (fun r _ => piece_measurable hM r1 r)
    (piece_pairwise_disjoint hmono r0 r1) fun r _ => hφ.integrableOn

/-- Partial sums of shell masses: for `r0 ≤ n < r1`,
`∑_{r0 ≤ r ≤ n} f(r) = ∫_{M(n+1)} w - ∫_{M r0} w`; p. 48, display display 6.8. -/
theorem sum_pieces_partial {μ : Measure X} {w : X → ℝ} (hwi : Integrable w μ)
    {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r)) (hmono : Monotone M) {r0 r1 : ℕ} :
    ∀ n, r0 ≤ n → n < r1 →
      ∑ r ∈ Icc r0 n, ∫ y in piece M r1 r, w y ∂μ =
        (∫ y in M (n + 1), w y ∂μ) - ∫ y in M r0, w y ∂μ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro h1
    rw [Finset.Icc_self, Finset.sum_singleton, piece, if_pos h1]
    exact setIntegral_diff_of_subset hwi (hM _) (hM _) (hmono (Nat.le_succ _))
  | succ k hk ih =>
    intro h1
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega), piece, if_pos h1,
      setIntegral_diff_of_subset hwi (hM _) (hM _) (hmono (Nat.le_succ _))]
    ring

/-- Total of the shell masses: if `∫ w = 1` then
`∑_{r0 ≤ r ≤ r1} f(r) = 1 - I0`; p. 48, the line `= 1 - I0 = H(r1) - I0`. -/
theorem sum_pieces_total {μ : Measure X} {w : X → ℝ} (hwi : Integrable w μ)
    (hw1 : ∫ y, w y ∂μ = 1) {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r))
    (hmono : Monotone M) {r0 r1 : ℕ} (hr : r0 ≤ r1) :
    ∑ r ∈ Icc r0 r1, ∫ y in piece M r1 r, w y ∂μ = 1 - ∫ y in M r0, w y ∂μ := by
  rcases Nat.eq_or_lt_of_le hr with h | h
  · subst h
    rw [Finset.Icc_self, Finset.sum_singleton, piece, if_neg (lt_irrefl _),
      setIntegral_compl' hwi (hM _), hw1]
  · obtain ⟨k, rfl⟩ : ∃ k, r1 = k + 1 := ⟨r1 - 1, by omega⟩
    rw [Finset.sum_Icc_succ_top (by omega),
      sum_pieces_partial hwi hM hmono k (by omega) (by omega), piece, if_neg (lt_irrefl _),
      setIntegral_compl' hwi (hM _), hw1]
    ring

/-- Proposition 6.2, p. 47, abstract
form. Let `w ≥ 0` with `∫ w = 1`, `0 ≤ s ≤ C` a.e., `M` increasing measurable, `r0 ≤ r1`
naturals, `H` non-decreasing with density `H'` on `[r0, r1]`, `H(r1) = 1`, and
display 6.4 `∫_{M(r+1)} w ≤ H(r)`, display 6.5 `s ≤ g(r)` off `M r`, for `r0 ≤ r ≤ r1`, with `g ≥ 0`
non-increasing on `[r0, r1]`. Then display 6.6:
`∫_{(M r0)ᶜ} w s ≤ g(r0) (H(r0) - I0) + ∫_{r0}^{r1} g(r) H'(r) dr`, `I0 = ∫_{M r0} w` as in
display 6.7. -/
theorem prop62 {μ : Measure X} {w s : X → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hwi : Integrable w μ)
    (hw1 : ∫ y, w y ∂μ = 1) (hsm : AEStronglyMeasurable s μ) (hs0 : ∀ y, 0 ≤ s y) {C : ℝ}
    (hsC : ∀ᵐ y ∂μ, s y ≤ C) {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r))
    (hmono : Monotone M) {r0 r1 : ℕ} (hr : r0 ≤ r1) {H H' g : ℝ → ℝ}
    (hH : NondecFTC H H' r0 r1) (hH1 : H r1 = 1)
    (h64 : ∀ r : ℕ, r0 ≤ r → r ≤ r1 → ∫ y in M (r + 1), w y ∂μ ≤ H r)
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) r1, 0 ≤ g u) (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) r1))
    (h65 : ∀ r : ℕ, r0 ≤ r → r ≤ r1 → ∀ᵐ y ∂μ, y ∉ M r → s y ≤ g r) :
    ∫ y in (M r0)ᶜ, w y * s y ∂μ ≤
      g r0 * (H r0 - ∫ y in M r0, w y ∂μ) + ∫ u in (r0 : ℝ)..r1, g u * H' u := by
  set I0 := ∫ y in M r0, w y ∂μ with hI0
  set f : ℕ → ℝ := fun r => ∫ y in piece M r1 r, w y ∂μ with hfdef
  have hf : ∀ n, 0 ≤ f n := fun n =>
    setIntegral_nonneg (piece_measurable hM r1 n) fun y _ => hw0 y
  have hint := integrable_mul_bdd hwi hsm hs0 hsC
  have e1 := integral_compl_eq_sum_pieces hint hM hmono hr
  have e2 : ∑ r ∈ Icc r0 r1, ∫ y in piece M r1 r, w y * s y ∂μ ≤
      ∑ r ∈ Icc r0 r1, f r * (fun r : ℕ => g r) r := by
    refine Finset.sum_le_sum fun r hr' => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hr'
    have := piece_bound hw0 hwi hsm hs0 hsC hM r1 r (h65 r h1 h2)
    simp only [hfdef]
    linarith [mul_comm (g r) (∫ y in piece M r1 r, w y ∂μ)]
  have hF : NondecFTC (fun x => H x - I0) H' r0 r1 := by
    obtain ⟨h1, h2, h3⟩ := hH
    refine ⟨h1, h2, fun x y hx hxy hy => ?_⟩
    rw [← h3 x y hx hxy hy]
    ring
  have h61 : ∀ n ∈ Icc r0 r1, ∑ m ∈ Icc r0 n, f m ≤ (fun x => H x - I0) (n : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    rcases Nat.lt_or_ge n r1 with h | h
    · rw [sum_pieces_partial hwi hM hmono n h1 h]
      linarith [h64 n h1 h2]
    · have hn1 : n = r1 := le_antisymm h2 h
      subst hn1
      rw [sum_pieces_total hwi hw1 hM hmono hr]
      show _ ≤ H n - I0
      linarith [hH1, hI0]
  have hgN : ∀ n ∈ Icc r0 r1, 0 ≤ (fun r : ℕ => g r) n := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    exact hg0 n ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have L := lemma61 hr f (fun r : ℕ => g r) hf hgN (fun x => H x - I0) H' hF h61
  rw [hmax_of_antitoneOn g hg0 hganti le_rfl hr] at L
  have B6 := integral_hmax_ceil_le g H' hr hg0 hganti hH.1 hH.2.1
  rw [e1]
  linarith

/-- Constant extension of the cumulative bound in Proposition 6.2, pp. 47 to 48.
The density is zero beyond the original endpoint. -/
theorem nondecFTC_min {F F' : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hF : NondecFTC F F' a b) :
    NondecFTC (fun u => F (min u b)) ((Set.Iic b).indicator F') a c := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    by_cases hub : u ≤ b
    · simp only [Set.indicator, Set.mem_Iic, ite_eq_left hub]
      exact hF.1 u ⟨hu.1, hub⟩
    · simp only [Set.indicator, Set.mem_Iic, ite_eq_right hub]
      exact le_rfl
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (hab.trans hbc)).mpr
    apply (integrableOn_indicator_iff measurableSet_Iic).mpr
    apply hF.2.1.1.mono_set
    intro u hu
    exact ⟨hu.2.1, hu.1⟩
  · intro x y hx hxy hy
    dsimp only
    by_cases hyb : y ≤ b
    · rw [min_eq_left (hxy.trans hyb), min_eq_left hyb, hF.2.2 x y hx hxy hyb]
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hxy] at hu
      simp only [Set.indicator, Set.mem_Iic, ite_eq_left (hu.2.trans hyb)]
    · have hby : b ≤ y := le_of_not_ge hyb
      by_cases hxb : x ≤ b
      · rw [min_eq_left hxb, min_eq_right hby]
        have he := intervalIntegral.integral_indicator (f := F') (μ := volume) ⟨hxb, hby⟩
        have hs : {u : ℝ | u ≤ b} = Set.Iic b := by ext u; simp
        rw [hs] at he
        rw [he]
        exact hF.2.2 x b hx hxb le_rfl
      · have hbx : b ≤ x := le_of_not_ge hxb
        rw [min_eq_right hbx, min_eq_right hby, sub_self]
        symm
        apply intervalIntegral.integral_zero_ae
        filter_upwards [] with u hu
        rw [Set.uIoc_of_le hxy] at hu
        simp only [Set.indicator, Set.mem_Iic, ite_eq_right (not_le.mpr (lt_of_le_of_lt hbx hu.1))]

/-- Proposition 6.2, pp. 47 to 48, abstract measure form with a real upper endpoint.
Constant extension to its natural ceiling reduces this to the sealed integer theorem. -/
theorem prop62_real {μ : Measure X} {w s : X → ℝ} (hw0 : ∀ y, 0 ≤ w y)
    (hwi : Integrable w μ) (hw1 : ∫ y, w y ∂μ = 1) (hsm : AEStronglyMeasurable s μ)
    (hs0 : ∀ y, 0 ≤ s y) {C : ℝ} (hsC : ∀ᵐ y ∂μ, s y ≤ C)
    {M : ℝ → Set X} (hM : ∀ r, MeasurableSet (M r)) (hmono : Monotone M)
    {r0 : ℕ} {R : ℝ} (hr : (r0 : ℝ) ≤ R) {H H' g : ℝ → ℝ}
    (hH : NondecFTC H H' r0 R) (hH1 : H R = 1)
    (h64 : ∀ r ∈ Set.Icc (r0 : ℝ) R, ∫ y in M (r + 1), w y ∂μ ≤ H r)
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) R, 0 ≤ g u)
    (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) R))
    (h65 : ∀ r ∈ Set.Icc (r0 : ℝ) R, ∀ᵐ y ∂μ, y ∉ M r → s y ≤ g r) :
    ∫ y in (M r0)ᶜ, w y * s y ∂μ ≤
      g r0 * (H r0 - ∫ y in M r0, w y ∂μ) + ∫ u in (r0 : ℝ)..R, g u * H' u := by
  have hb : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  have hrN : r0 ≤ ⌈R⌉₊ := by exact_mod_cast hr.trans hb
  let MN : ℕ → Set X := fun n => M (min (n : ℝ) R)
  let G : ℝ → ℝ := fun u => g (min u R)
  let F : ℝ → ℝ := fun u => H (min u R)
  let D : ℝ → ℝ := (Set.Iic R).indicator H'
  have hclamp : ∀ u ∈ Set.Icc (r0 : ℝ) (⌈R⌉₊ : ℝ),
      min u R ∈ Set.Icc (r0 : ℝ) R := by
    intro u hu
    exact ⟨le_min hu.1 hr, min_le_right _ _⟩
  have hw0ae : ∀ᵐ y ∂μ, 0 ≤ w y := Filter.Eventually.of_forall hw0
  have h64N : ∀ r : ℕ, r0 ≤ r → r ≤ ⌈R⌉₊ →
      ∫ y in MN (r + 1), w y ∂μ ≤ F r := by
    intro r hr0 hr1
    dsimp only [MN, F]
    by_cases hrR : (r : ℝ) ≤ R
    · rw [min_eq_left hrR]
      have hsub : M (min ((r + 1 : ℕ) : ℝ) R) ⊆ M ((r : ℝ) + 1) := by
        apply hmono
        simpa only [Nat.cast_add, Nat.cast_one] using
          min_le_left ((r + 1 : ℕ) : ℝ) R
      exact (setIntegral_mono_set hwi.integrableOn (ae_restrict_of_ae hw0ae)
        (Filter.Eventually.of_forall fun y hy => hsub hy)).trans
          (h64 r ⟨by exact_mod_cast hr0, hrR⟩)
    · rw [min_eq_right (le_of_not_ge hrR), hH1]
      exact (setIntegral_le_integral hwi hw0ae).trans_eq hw1
  have hG0 : ∀ u ∈ Set.Icc (r0 : ℝ) (⌈R⌉₊ : ℝ), 0 ≤ G u := by
    intro u hu
    exact hg0 _ (hclamp u hu)
  have hGanti : AntitoneOn G (Set.Icc (r0 : ℝ) (⌈R⌉₊ : ℝ)) := by
    intro u hu v hv huv
    exact hganti (hclamp u hu) (hclamp v hv) (min_le_min_right R huv)
  have h65N : ∀ r : ℕ, r0 ≤ r → r ≤ ⌈R⌉₊ →
      ∀ᵐ y ∂μ, y ∉ MN r → s y ≤ G r := by
    intro r hr0 hr1
    exact h65 _ (hclamp r ⟨by exact_mod_cast hr0, by exact_mod_cast hr1⟩)
  have hFN : NondecFTC F D r0 ⌈R⌉₊ := nondecFTC_min hr hb hH
  have hF1 : F ⌈R⌉₊ = 1 := by
    dsimp only [F]
    rw [min_eq_right hb, hH1]
  have hMN : Monotone MN := by
    intro i j hij
    exact hmono (min_le_min_right R (by exact_mod_cast hij))
  have hresult := prop62 hw0 hwi hw1 hsm hs0 hsC (fun r => hM _) hMN hrN
    hFN hF1 h64N hG0 hGanti h65N
  have hI : (∫ u in (r0 : ℝ)..(⌈R⌉₊ : ℝ), g (min u R) * D u) =
      ∫ u in (r0 : ℝ)..R, g u * H' u := by
    calc
      _ = ∫ u in (r0 : ℝ)..(⌈R⌉₊ : ℝ),
          (Set.Iic R).indicator (fun u => g u * H' u) u := by
        apply intervalIntegral.integral_congr
        intro u hu
        dsimp only [D]
        by_cases huR : u ≤ R
        · simp only [Set.indicator, Set.mem_Iic, ite_eq_left huR, min_eq_left huR]
        · simp only [Set.indicator, Set.mem_Iic, ite_eq_right huR, mul_zero]
      _ = _ := by
        have he := intervalIntegral.integral_indicator
          (f := fun u => g u * H' u) (μ := volume) ⟨hr, hb⟩
        simpa only [Set.Iic_def] using he
  dsimp only [MN, G, F] at hresult
  rw [min_eq_left hr, hI] at hresult
  exact hresult

/-- Parseval for the finite exponential polynomial used in Proposition 6.2, p. 48.
This uses Mathlib's orthonormal Fourier monomials on the additive circle. -/
theorem parseval_exp (A : Finset ℤ) (c : ℤ → ℂ) :
    (∫ α in (0 : ℝ)..1,
      ‖∑ n ∈ A, c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))‖ ^ 2) =
      ∑ n ∈ A, ‖c n‖ ^ 2 := by
  classical
  let P : C(AddCircle (1 : ℝ), ℂ) := ∑ n ∈ A, c n • fourier n
  have he : inner ℂ
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ P)
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ P) =
      ∑ n ∈ A, starRingEnd ℂ (c n) * c n := by
    simpa only [P, map_sum, map_smul] using
      (orthonormal_fourier (T := (1 : ℝ))).inner_sum c c A
  rw [ContinuousMap.inner_toLp] at he
  simp_rw [Complex.mul_conj', Complex.conj_mul', ← Complex.ofReal_pow] at he
  rw [integral_complex_ofReal] at he
  have hnorm : (∫ t : AddCircle (1 : ℝ), ‖P t‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ n ∈ A, ‖c n‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [Complex.ofReal_pow] using he
  calc
    _ = ∫ α in (0 : ℝ)..1, ‖P (α : AddCircle (1 : ℝ))‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro α hα
      apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
      simp only [P, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      rw [fourier_coe_apply]
      simp only [Complex.ofReal_one, div_one]
      congr 1
      push_cast
      ring
    _ = ∫ t : AddCircle (1 : ℝ), ‖P t‖ ^ 2 := by
      simpa only [zero_add] using
        AddCircle.intervalIntegral_preimage (1 : ℝ) 0 (fun t => ‖P t‖ ^ 2)
    _ = ∫ t : AddCircle (1 : ℝ), ‖P t‖ ^ 2 ∂AddCircle.haarAddCircle := by
      rw [AddCircle.integral_haarAddCircle]
      simp
    _ = _ := hnorm

/-- The positive total mass form of Proposition 6.2, pp. 47 to 48.
Dividing the weight by its total mass gives the normalized real endpoint theorem. -/
theorem prop62_real_mass {μ : Measure X} {w s : X → ℝ} (hw0 : ∀ y, 0 ≤ w y)
    (hwi : Integrable w μ) {W : ℝ} (hW : 0 < W) (hwW : ∫ y, w y ∂μ = W)
    (hsm : AEStronglyMeasurable s μ) (hs0 : ∀ y, 0 ≤ s y) {C : ℝ}
    (hsC : ∀ᵐ y ∂μ, s y ≤ C) {M : ℝ → Set X} (hM : ∀ r, MeasurableSet (M r))
    (hmono : Monotone M) {r0 : ℕ} {R : ℝ} (hr : (r0 : ℝ) ≤ R) {H H' g : ℝ → ℝ}
    (hH : NondecFTC H H' r0 R) (hH1 : H R = 1)
    (h64 : ∀ r ∈ Set.Icc (r0 : ℝ) R, ∫ y in M (r + 1), w y ∂μ ≤ W * H r)
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) R, 0 ≤ g u)
    (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) R))
    (h65 : ∀ r ∈ Set.Icc (r0 : ℝ) R, ∀ᵐ y ∂μ, y ∉ M r → s y ≤ g r) :
    ∫ y in (M r0)ᶜ, w y * s y ∂μ ≤
      g r0 * (W * H r0 - ∫ y in M r0, w y ∂μ) +
        W * ∫ u in (r0 : ℝ)..R, g u * H' u := by
  have hnorm : (∫ y, w y / W ∂μ) = 1 := by
    rw [MeasureTheory.integral_div, hwW, div_self hW.ne']
  have h64N : ∀ r ∈ Set.Icc (r0 : ℝ) R,
      ∫ y in M (r + 1), w y / W ∂μ ≤ H r := by
    intro r hr'
    rw [MeasureTheory.integral_div]
    apply (div_le_iff₀ hW).mpr
    simpa only [mul_comm] using h64 r hr'
  have h := prop62_real (fun y => div_nonneg (hw0 y) hW.le) (hwi.div_const W)
    hnorm hsm hs0 hsC hM hmono hr hH hH1 h64N hg0 hganti h65
  simp_rw [div_mul_eq_mul_div] at h
  rw [MeasureTheory.integral_div, MeasureTheory.integral_div] at h
  have hmul := (div_le_iff₀ hW).mp h
  calc
    _ ≤ (g r0 * (H r0 - (∫ y in M r0, w y ∂μ) / W) +
        ∫ u in (r0 : ℝ)..R, g u * H' u) * W := hmul
    _ = _ := by
      field_simp

/-- Parseval for absolutely summable coefficients, as used in Proposition 6.2, pp. 47 to 48.
The finite polynomial identity passes to the series by dominated convergence. -/
theorem hasSum_norm_sq_exp (c : ℤ → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    HasSum (fun n => ‖c n‖ ^ 2)
      (∫ α in (0 : ℝ)..1,
        ‖∑' n : ℤ, c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))‖ ^ 2) := by
  classical
  let term : ℤ → ℝ → ℂ := fun n α =>
    c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))
  have hn : ∀ n α, ‖term n α‖ = ‖c n‖ := by
    intro n α
    simp [term, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hs : ∀ α, Summable (fun n => term n α) := by
    intro α
    apply Summable.of_norm
    simpa only [hn] using hc
  let B : ℝ := ∑' n, ‖c n‖
  have hbound : ∀ (A : Finset ℤ) α, ‖∑ n ∈ A, term n α‖ ≤ B := by
    intro A α
    calc
      _ ≤ ∑ n ∈ A, ‖term n α‖ := norm_sum_le _ _
      _ = ∑ n ∈ A, ‖c n‖ := by simp only [hn]
      _ ≤ B := hc.sum_le_tsum A (fun n hn => norm_nonneg (c n))
  have hmeas : ∀ A : Finset ℤ, AEStronglyMeasurable
      (fun α => ‖∑ n ∈ A, term n α‖ ^ 2) (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    intro A
    have hcont : Continuous (fun α => ‖∑ n ∈ A, term n α‖ ^ 2) := by
      dsimp only [term]
      fun_prop
    exact hcont.aestronglyMeasurable.restrict
  have hconv := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := Filter.atTop) (F := fun (A : Finset ℤ) α => ‖∑ n ∈ A, term n α‖ ^ 2)
    (f := fun α => ‖∑' n, term n α‖ ^ 2) (fun _ => B ^ 2)
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall fun A => Filter.Eventually.of_forall fun α hα => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound A α) 2)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun α hα => by
      simpa only [Function.comp_def, Pi.pow_def, SummationFilter.unconditional] using
        ((continuous_norm.pow 2).tendsto _).comp (hs α).hasSum)
  have heq : (fun A : Finset ℤ => ∫ α in (0 : ℝ)..1, ‖∑ n ∈ A, term n α‖ ^ 2) =
      fun A => ∑ n ∈ A, ‖c n‖ ^ 2 := by
    funext A
    exact parseval_exp A c
  rw [heq] at hconv
  exact hconv


/-- Proposition 6.2, pp. 47 to 48, for an absolutely summable exponential series and continuous S2,
with a real upper endpoint and any increasing measurable family on the unit interval. -/
theorem prop62_series_real (c : ℤ → ℂ) (hc : Summable (fun n => ‖c n‖))
    (hN : 0 < ∑' n : ℤ, ‖c n‖ ^ 2)
    (S2 : ℝ → ℂ) (hS2 : Continuous S2) {M : ℝ → Set ℝ}
    (hM : ∀ r, MeasurableSet (M r)) (hmono : Monotone M)
    {r0 : ℕ} {R : ℝ} (hr : (r0 : ℝ) ≤ R) {H H' g : ℝ → ℝ}
    (hH : NondecFTC H H' r0 R) (hH1 : H R = 1)
    (h64 : ∀ r ∈ Set.Icc (r0 : ℝ) R,
      (∫ α in M (r + 1),
        ‖∑' n : ℤ, c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))‖ ^ 2
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤ (∑' n : ℤ, ‖c n‖ ^ 2) * H r)
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) R, 0 ≤ g u)
    (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) R))
    (h65 : ∀ r ∈ Set.Icc (r0 : ℝ) R, ∀ α ∈ Set.Ioc (0 : ℝ) 1,
      α ∉ M r → ‖S2 α‖ ≤ g r) :
    (∫ α in (M r0)ᶜ,
      ‖∑' n : ℤ, c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))‖ ^ 2 * ‖S2 α‖
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤
      g r0 * ((∑' n : ℤ, ‖c n‖ ^ 2) * H r0 -
        ∫ α in M r0,
          ‖∑' n : ℤ, c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))‖ ^ 2
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) +
      (∑' n : ℤ, ‖c n‖ ^ 2) * ∫ u in (r0 : ℝ)..R, g u * H' u := by
  let P : ℝ → ℂ := fun α =>
    ∑' n : ℤ, c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))
  have hP : Continuous P := by
    apply continuous_tsum (fun n => by fun_prop) hc
    intro n α
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hwi : Integrable (fun α => ‖P α‖ ^ 2) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (hP.norm.pow 2).integrableOn_Ioc
  have hmass : (∫ α in Set.Ioc (0 : ℝ) 1, ‖P α‖ ^ 2) = ∑' n : ℤ, ‖c n‖ ^ 2 := by
    simpa only [P, intervalIntegral.integral_of_le zero_le_one] using (hasSum_norm_sq_exp c hc).tsum_eq.symm
  obtain ⟨C, hC⟩ : BddAbove ((fun α => ‖S2 α‖) '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hS2.norm.continuousOn
  have hsC : ∀ᵐ α ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖S2 α‖ ≤ C := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with α hα
    exact hC (Set.mem_image_of_mem _ (Set.Ioc_subset_Icc_self hα))
  refine prop62_real_mass (fun α => sq_nonneg (‖P α‖)) hwi hN hmass
    hS2.norm.aestronglyMeasurable.restrict (fun α => norm_nonneg (S2 α))
    hsC hM hmono hr hH hH1 h64 hg0 hganti ?_
  intro r hr'
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with α hα
  exact h65 r hr' α hα

end LeanLab.Helfgott2013.U1538
