module

public import LeanLab.Linnik.LiLiuLemma43

/-!
Li-Liu, arXiv 2610.15784 v1, Lemma 4.3, (36): R₁(0) = (1 + o(1)) N log P, its lower half, the
integration step. Read through WebFetch on arxiv.org/html/2610.15784, Section 4, run
20261021T0703Z-4724, unit U-1365.

Paper, (25): 𝔐 = ⋃_{q ≤ P} ⋃_{(r,q)=1} {α ∈ (0,1] : ‖α - r/q‖ ≤ P/(qN)}; (26): R₁(h) =
∫_𝔐 |S(α)|² e(-hα) dα. Proof of Lemma 4.3: for fixed T ≥ 1, q ≤ P/T gives T/N ≤ P/(qN), and
  R₁(0) ≥ ∑_{q ≤ P/T} μ(q)²/φ(q) ∫_{-T/N}^{T/N} |S(β)|² dβ.
The paper does not spell out why the small arcs |α - r/q| ≤ T/N may be summed; here that is the
hypothesis `2 δ Q² < 1`, which makes them pairwise disjoint modulo 1, and with P ≤ N^{4/9} and
T ≥ 1 it holds since 2 P²/(T N) < 1.

Here, for any continuous, nonnegative, 1-periodic F:
* `sum_arcs_le`: ∑_{q ≤ Q} ∑_{(r,q)=1} ∫_{-δ}^{δ} F(r/q + β) dβ ≤ ∫_{𝔐(P,N)} F, given
  Q ≤ P, δ Q N ≤ P and 2 δ Q² < 1;
* `lemma43_integrated`: for S(α) = ∑_{p ∈ A} w(p) e(pα), A a finite set of primes above Q,
  log(Q + 1) ∫_{-δ}^{δ} |S(β)|² dβ ≤ R₁(0) = ∫_{𝔐} |S(α)|² dα, PROVED unconditional;
* `lemma43_lower_conditional`: R₁(0) ≥ c N log(Q + 1), CONDITIONAL ON the central arc input
  (37) in the one-sided form ∫_{-δ}^{δ} |S|² ≥ c N, a named hypothesis.

Unit U-1365, PC run 20261021T0703Z-4724. AI-written Lean code, Claude. KNOWN mathematics, the
paper's own step. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.LiLiuLemma43Int

open MeasureTheory Set Real
open LeanLab.Linnik.LiLiuLemma43
open LeanLab.PNTPort.LargeSieve

/-- The paper's major arcs (25), as a subset of `(0, 1]`; `dist0` is the distance to the nearest
integer. -/
def majorArcs (P N : ℝ) : Set ℝ :=
  {α | α ∈ Ioc (0 : ℝ) 1 ∧ ∃ q ∈ Finset.Icc 1 ⌊P⌋₊, ∃ r ∈ units q,
      dist0 (α - (r : ℝ) / q) ≤ P / (q * N)}

/-- `R₁(0) = ∫_𝔐 |S(α)|² dα`, (26) at h = 0. -/
noncomputable def R10 (A : Finset ℕ) (w : ℕ → ℂ) (P N : ℝ) : ℝ :=
  ∫ α in majorArcs P N, ‖SA A w α‖ ^ 2

/-- The small arc around `r/q` of half width `δ`, folded into `(0, 1]`. -/
def arc (δ : ℝ) (q r : ℕ) : Set ℝ :=
  if r = 0 then Ioc 0 δ ∪ Ioc (1 - δ) 1 else Ioc ((r : ℝ) / q - δ) ((r : ℝ) / q + δ)

lemma mem_units {q r : ℕ} : r ∈ units q ↔ r < q ∧ Nat.Coprime r q := by
  simp [units]

lemma units_zero {q r : ℕ} (h : r ∈ units q) (hr : r = 0) : q = 1 := by
  rw [mem_units] at h
  subst hr
  exact Nat.coprime_zero_left _ |>.mp h.2

/-- Distinct reduced fractions with denominators `q, q'` have `r q' ≠ r' q`. -/
lemma cross_ne {q r q' r' : ℕ} (h : r ∈ units q) (h' : r' ∈ units q')
    (hne : (⟨q, r⟩ : Σ _ : ℕ, ℕ) ≠ ⟨q', r'⟩) : r * q' ≠ r' * q := by
  intro heq
  rw [mem_units] at h h'
  have hq : q ∣ q' := by
    have : q ∣ r * q' := ⟨r', by rw [heq]; ring⟩
    exact (Nat.Coprime.symm h.2).dvd_of_dvd_mul_left this
  have hq' : q' ∣ q := by
    have : q' ∣ r' * q := ⟨r, by rw [← heq]; ring⟩
    exact (Nat.Coprime.symm h'.2).dvd_of_dvd_mul_left this
  have hqq : q = q' := Nat.dvd_antisymm hq hq'
  subst hqq
  have hq0 : 0 < q := by omega
  have : r = r' := Nat.eq_of_mul_eq_mul_right hq0 heq
  subst this
  exact hne rfl

/-- Two distinct reduced fractions with denominators at most `Q` are at least `1/Q²` apart. -/
lemma sep {Q q r q' r' : ℕ} (hq : q ∈ Finset.Icc 1 Q) (hq' : q' ∈ Finset.Icc 1 Q)
    (h : r ∈ units q) (h' : r' ∈ units q')
    (hne : (⟨q, r⟩ : Σ _ : ℕ, ℕ) ≠ ⟨q', r'⟩) :
    1 / ((Q : ℝ) ^ 2) ≤ |(r : ℝ) / q - (r' : ℝ) / q'| := by
  rw [Finset.mem_Icc] at hq hq'
  have hc := cross_ne h h' hne
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq.1
  have hqp' : (0 : ℝ) < q' := by exact_mod_cast hq'.1
  have hint : (1 : ℝ) ≤ |(r : ℝ) * q' - r' * q| := by
    have : ((r * q' : ℕ) : ℤ) ≠ ((r' * q : ℕ) : ℤ) := by exact_mod_cast hc
    have h1 : (1 : ℤ) ≤ |((r * q' : ℕ) : ℤ) - ((r' * q : ℕ) : ℤ)| :=
      Int.one_le_abs (sub_ne_zero.mpr this)
    have : ((|((r * q' : ℕ) : ℤ) - ((r' * q : ℕ) : ℤ)| : ℤ) : ℝ) =
        |(r : ℝ) * q' - r' * q| := by push_cast; rfl
    rw [← this]; exact_mod_cast h1
  have heq : (r : ℝ) / q - (r' : ℝ) / q' = ((r : ℝ) * q' - r' * q) / (q * q') := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hqp hqp'), le_div_iff₀ (mul_pos hqp hqp')]
  have hQq : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    have a : (q : ℝ) ≤ Q := by exact_mod_cast hq.2
    have b : (q' : ℝ) ≤ Q := by exact_mod_cast hq'.2
    nlinarith
  have hQ : (0 : ℝ) < (Q : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hq.1.trans hq.2
    positivity
  calc 1 / (Q : ℝ) ^ 2 * (q * q') ≤ 1 / (Q : ℝ) ^ 2 * (Q : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hQq; positivity
    _ = 1 := by rw [one_div, inv_mul_cancel₀ hQ.ne']
    _ ≤ _ := hint

/-- Location of a nonzero reduced fraction: `1/q ≤ r/q ≤ 1 - 1/q`. -/
lemma frac_bounds {q r : ℕ} (h : r ∈ units q) (hr : r ≠ 0) :
    1 / (q : ℝ) ≤ (r : ℝ) / q ∧ (r : ℝ) / q ≤ 1 - 1 / (q : ℝ) := by
  rw [mem_units] at h
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have h1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
  have h2 : (r : ℝ) + 1 ≤ q := by exact_mod_cast h.1
  constructor
  · exact div_le_div_of_nonneg_right h1 hq.le
  · rw [div_le_iff₀ hq]
    have : (1 - 1 / (q : ℝ)) * q = q - 1 := by field_simp
    rw [this]; linarith

/-- `δ < 1/(2q)` for every `q ≤ Q`, from `2 δ Q² < 1`. -/
lemma delta_small {Q q : ℕ} {δ : ℝ} (hδ : 0 < δ) (hsep : 2 * δ * (Q : ℝ) ^ 2 < 1)
    (hq : q ∈ Finset.Icc 1 Q) : 2 * δ * q < 1 := by
  rw [Finset.mem_Icc] at hq
  have a : (1 : ℝ) ≤ q := by exact_mod_cast hq.1
  have b : (q : ℝ) ≤ Q := by exact_mod_cast hq.2
  nlinarith

lemma arc_disjoint {Q : ℕ} {δ : ℝ} (hδ : 0 < δ) (hsep : 2 * δ * (Q : ℝ) ^ 2 < 1)
    {q r q' r' : ℕ} (hq : q ∈ Finset.Icc 1 Q) (hq' : q' ∈ Finset.Icc 1 Q)
    (h : r ∈ units q) (h' : r' ∈ units q')
    (hne : (⟨q, r⟩ : Σ _ : ℕ, ℕ) ≠ ⟨q', r'⟩) :
    Disjoint (arc δ q r) (arc δ q' r') := by
  have hd := delta_small hδ hsep hq
  have hd' := delta_small hδ hsep hq'
  have hqp : (0 : ℝ) < q := by have := (Finset.mem_Icc.mp hq).1; exact_mod_cast this
  have hqp' : (0 : ℝ) < q' := by have := (Finset.mem_Icc.mp hq').1; exact_mod_cast this
  have hinv : δ < 1 / (q : ℝ) - δ := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hqp]; linarith
  have hinv' : δ < 1 / (q' : ℝ) - δ := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hqp']; linarith
  -- a nonzero fraction's arc sits inside (δ, 1 - δ]
  have inside : ∀ {q r : ℕ}, r ∈ units q → r ≠ 0 → δ < 1 / (q : ℝ) - δ →
      Ioc ((r : ℝ) / q - δ) ((r : ℝ) / q + δ) ⊆ Ioc δ (1 - δ) := by
    intro q r h hr hi x hx
    obtain ⟨b1, b2⟩ := frac_bounds h hr
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have zero_side : Disjoint (Ioc (0 : ℝ) δ ∪ Ioc (1 - δ) 1) (Ioc δ (1 - δ)) := by
    rw [Set.disjoint_union_left]
    constructor
    · exact Set.disjoint_left.mpr fun x hx hy => absurd hy.1 (not_lt.mpr hx.2)
    · exact Set.disjoint_left.mpr fun x hx hy => absurd hy.2 (not_le.mpr hx.1)
  by_cases hr : r = 0
  · by_cases hr' : r' = 0
    · exfalso
      apply hne
      rw [units_zero h hr, units_zero h' hr', hr, hr']
    · unfold arc; rw [if_pos hr, if_neg hr']
      exact zero_side.mono_right (inside h' hr' hinv')
  · by_cases hr' : r' = 0
    · unfold arc; rw [if_neg hr, if_pos hr']
      exact (zero_side.mono_right (inside h hr hinv)).symm
    · unfold arc; rw [if_neg hr, if_neg hr']
      have hs := sep hq hq' h h' hne
      have hQ : (1 : ℝ) ≤ Q := by
        have := Finset.mem_Icc.mp hq; exact_mod_cast this.1.trans this.2
      have h2δ : 2 * δ < 1 / (Q : ℝ) ^ 2 := by
        rw [lt_div_iff₀ (by positivity)]; linarith
      rw [Set.Ioc_disjoint_Ioc]
      rcases le_total ((r : ℝ) / q) ((r' : ℝ) / q') with hle | hle
      · rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hs
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)] at hs
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
        linarith

lemma arc_subset {P N : ℝ} {Q : ℕ} {δ : ℝ} (hδ : 0 < δ) (hN : 0 < N)
    (hQP : (Q : ℝ) ≤ P) (hδP : δ * Q * N ≤ P) (hsep : 2 * δ * (Q : ℝ) ^ 2 < 1)
    {q r : ℕ} (hq : q ∈ Finset.Icc 1 Q) (h : r ∈ units q) :
    arc δ q r ⊆ majorArcs P N := by
  have hd := delta_small hδ hsep hq
  have hqI := Finset.mem_Icc.mp hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast hqI.1
  have hqP : q ∈ Finset.Icc 1 ⌊P⌋₊ := by
    rw [Finset.mem_Icc]
    refine ⟨hqI.1, Nat.le_floor ?_⟩
    have : (q : ℝ) ≤ Q := by exact_mod_cast hqI.2
    linarith
  have hδq : δ ≤ P / (q * N) := by
    rw [le_div_iff₀ (mul_pos hqp hN)]
    have : (q : ℝ) ≤ Q := by exact_mod_cast hqI.2
    nlinarith
  have hinv : δ < 1 / (q : ℝ) - δ := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hqp]; linarith
  intro x hx
  unfold arc at hx
  split_ifs at hx with hr
  · subst hr
    have hq1 := units_zero h rfl
    have hδ1 : δ < 1 := by
      have : (1 : ℝ) ≤ q := by exact_mod_cast hqI.1
      nlinarith
    refine ⟨?_, q, hqP, 0, h, ?_⟩
    · rcases hx with hx | hx
      · exact ⟨hx.1, by linarith [hx.2]⟩
      · exact ⟨by linarith [hx.1], hx.2⟩
    · simp only [Nat.cast_zero, zero_div, sub_zero]
      rcases hx with hx | hx
      · calc dist0 x ≤ |x - ((0 : ℤ) : ℝ)| := dist0_le_abs_sub_int x 0
          _ = x := by simp [abs_of_pos hx.1]
          _ ≤ δ := hx.2
          _ ≤ _ := hδq
      · calc dist0 x ≤ |x - ((1 : ℤ) : ℝ)| := dist0_le_abs_sub_int x 1
          _ = 1 - x := by
              push_cast; rw [abs_of_nonpos (by linarith [hx.2])]; ring
          _ ≤ δ := by linarith [hx.1]
          _ ≤ _ := hδq
  · obtain ⟨b1, b2⟩ := frac_bounds h hr
    refine ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, q, hqP, r, h, ?_⟩
    calc dist0 (x - (r : ℝ) / q) ≤ |x - (r : ℝ) / q - ((0 : ℤ) : ℝ)| :=
          dist0_le_abs_sub_int _ 0
      _ ≤ δ := by
          push_cast; rw [sub_zero, abs_le]
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      _ ≤ _ := hδq

lemma arc_measurable (δ : ℝ) (q r : ℕ) : MeasurableSet (arc δ q r) := by
  unfold arc; split_ifs
  · exact measurableSet_Ioc.union measurableSet_Ioc
  · exact measurableSet_Ioc

lemma arc_subset_Icc {δ : ℝ} (hδ2 : δ < 1 / 2) {q r : ℕ} (h : r ∈ units q) :
    arc δ q r ⊆ Icc (-1 : ℝ) 2 := by
  intro x hx
  unfold arc at hx
  split_ifs at hx with hr
  · rcases hx with hx | hx
    · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · have hq : 0 < q := by have := (mem_units.mp h).1; omega
    have hqp : (0 : ℝ) < q := by exact_mod_cast hq
    have h0 : (0 : ℝ) ≤ (r : ℝ) / q := by positivity
    have h1 : (r : ℝ) / q ≤ 1 := by
      rw [div_le_one hqp]; exact_mod_cast (mem_units.mp h).1.le
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The integral over a folded arc is the integral over `[-δ, δ]` of the shifted function. -/
lemma integral_arc {F : ℝ → ℝ} (hF : Continuous F) (hper : ∀ x, F (x + 1) = F x)
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) {q r : ℕ} :
    ∫ x in arc δ q r, F x = ∫ β in (-δ)..δ, F ((r : ℝ) / q + β) := by
  unfold arc
  split_ifs with hr
  · subst hr
    simp only [Nat.cast_zero, zero_div, zero_add]
    have hdisj : Disjoint (Ioc (0 : ℝ) δ) (Ioc (1 - δ) 1) := by
      rw [Set.Ioc_disjoint_Ioc]
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    rw [setIntegral_union hdisj measurableSet_Ioc hF.integrableOn_Ioc hF.integrableOn_Ioc,
      ← intervalIntegral.integral_of_le hδ.le,
      ← intervalIntegral.integral_of_le (by linarith)]
    have hshift : ∫ x in (-δ)..0, F x = ∫ x in (1 - δ)..1, F x := by
      have := intervalIntegral.integral_comp_add_right (a := -δ) (b := 0) F (1 : ℝ)
      simp only [hper] at this
      rw [this]; congr 1 <;> ring
    rw [← hshift, add_comm, intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)]
  · rw [← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_add_left F ((r : ℝ) / q)]
    ring_nf

/-- **Summing the small arcs.** For continuous, nonnegative, 1-periodic `F`, with `Q ≤ P`,
`δ Q N ≤ P` and `2 δ Q² < 1`:
`∑_{q ≤ Q} ∑_{(r,q)=1} ∫_{-δ}^{δ} F(r/q + β) dβ ≤ ∫_{𝔐(P,N)} F`. -/
theorem sum_arcs_le {F : ℝ → ℝ} (hF : Continuous F) (hF0 : ∀ x, 0 ≤ F x)
    (hper : ∀ x, F (x + 1) = F x) {P N δ : ℝ} {Q : ℕ} (hδ : 0 < δ) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hQP : (Q : ℝ) ≤ P) (hδP : δ * Q * N ≤ P) (hsep : 2 * δ * (Q : ℝ) ^ 2 < 1) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ units q, ∫ β in (-δ)..δ, F ((r : ℝ) / q + β) ≤
      ∫ x in majorArcs P N, F x := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hδ2 : δ < 1 / 2 := by nlinarith
  set I := (Finset.Icc 1 Q).sigma units with hI
  have hsum : ∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ units q, ∫ β in (-δ)..δ, F ((r : ℝ) / q + β) =
      ∑ i ∈ I, ∫ x in arc δ i.1 i.2, F x := by
    rw [hI, Finset.sum_sigma]
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro r _
    rw [integral_arc hF hper hδ hδ2]
  have hpd : Set.Pairwise (↑I : Set (Σ _ : ℕ, ℕ)) (Function.onFun Disjoint fun i => arc δ i.1 i.2) := by
    rintro ⟨q, r⟩ hi ⟨q', r'⟩ hi' hne
    simp only [hI, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at hi hi'
    exact arc_disjoint hδ hsep hi.1 hi'.1 hi.2 hi'.2 hne
  have hint : ∀ i ∈ I, IntegrableOn F (arc δ i.1 i.2) :=
    fun i hi => (hF.integrableOn_Icc (a := -1) (b := 2)).mono_set
      (arc_subset_Icc hδ2 (Finset.mem_sigma.mp hi).2)
  rw [hsum, ← integral_biUnion_finset I (fun i _ => arc_measurable δ i.1 i.2) hpd hint]
  have hsub : (⋃ i ∈ I, arc δ i.1 i.2) ⊆ majorArcs P N := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hx⟩ := hx
    simp only [hI, Finset.mem_sigma] at hi
    exact arc_subset hδ hN hQP hδP hsep hi.1 hi.2 hx
  have hM : majorArcs P N ⊆ Icc (0 : ℝ) 1 := fun x hx => Ioc_subset_Icc_self hx.1
  apply setIntegral_mono_set ((hF.integrableOn_Icc (a := 0) (b := 1)).mono_set hM)
  · exact Filter.Eventually.of_forall (fun x => hF0 x)
  · exact Filter.Eventually.of_forall hsub

/-- `S` is continuous. -/
lemma SA_continuous (A : Finset ℕ) (w : ℕ → ℂ) : Continuous (SA A w) := by
  unfold SA e; fun_prop

/-- `S` has period 1. -/
lemma SA_periodic (A : Finset ℕ) (w : ℕ → ℂ) (x : ℝ) : SA A w (x + 1) = SA A w x := by
  unfold SA
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_add, mul_one, e_add, show (p : ℝ) = ((p : ℤ) : ℝ) by simp, e_int, mul_one]

/-- **Li-Liu Lemma 4.3, lower half, integrated.** For a finite set `A` of primes above `Q`,
any weights, `Q ≤ P`, `δ Q N ≤ P` and `2 δ Q² < 1`:
`log(Q + 1) ∫_{-δ}^{δ} |S(β)|² dβ ≤ R₁(0)`. PROVED unconditional. -/
theorem lemma43_integrated (A : Finset ℕ) (w : ℕ → ℂ) {P N δ : ℝ} {Q : ℕ}
    (hA : ∀ p ∈ A, p.Prime ∧ Q < p) (hδ : 0 < δ) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hQP : (Q : ℝ) ≤ P) (hδP : δ * Q * N ≤ P) (hsep : 2 * δ * (Q : ℝ) ^ 2 < 1) :
    Real.log ((Q : ℝ) + 1) * ∫ β in (-δ)..δ, ‖SA A w β‖ ^ 2 ≤ R10 A w P N := by
  have hc : Continuous (fun α => ‖SA A w α‖ ^ 2) := (SA_continuous A w).norm.pow 2
  have hcs : ∀ (q r : ℕ), Continuous (fun β => ‖SA A w ((r : ℝ) / q + β)‖ ^ 2) :=
    fun q r => hc.comp (continuous_const.add continuous_id)
  calc Real.log ((Q : ℝ) + 1) * ∫ β in (-δ)..δ, ‖SA A w β‖ ^ 2
      = ∫ β in (-δ)..δ, Real.log ((Q : ℝ) + 1) * ‖SA A w β‖ ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ ∫ β in (-δ)..δ, ∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ units q,
          ‖SA A w ((r : ℝ) / q + β)‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · exact (continuous_const.mul hc).intervalIntegrable _ _
        · exact (continuous_finsetSum _ fun q _ => continuous_finsetSum _
            fun r _ => hcs q r).intervalIntegrable _ _
        · intro β _
          exact lemma43_core A w Q hA β
    _ = ∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ units q,
          ∫ β in (-δ)..δ, ‖SA A w ((r : ℝ) / q + β)‖ ^ 2 := by
        rw [intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl; intro q _
          rw [intervalIntegral.integral_finsetSum]
          intro r _; exact (hcs q r).intervalIntegrable _ _
        · intro q _
          exact (continuous_finsetSum _ fun r _ => hcs q r).intervalIntegrable _ _
    _ ≤ R10 A w P N :=
        sum_arcs_le (F := fun α => ‖SA A w α‖ ^ 2) hc (fun _ => by positivity)
          (fun x => by simp only [SA_periodic]) hδ hN hQ hQP hδP hsep

/-- **Lemma 4.3, lower half, CONDITIONAL ON the central arc input (37)** in one-sided form:
if `∫_{-δ}^{δ} |S|² ≥ c N` then `R₁(0) ≥ c N log(Q + 1)`. With δ = T/N and Q = ⌊P/T⌋, (37)
gives c = 1 + O(1/T) + o_T(1), and letting T → ∞ yields R₁(0) ≥ (1 - o(1)) N log P. -/
theorem lemma43_lower_conditional (A : Finset ℕ) (w : ℕ → ℂ) {P N δ c : ℝ} {Q : ℕ}
    (hA : ∀ p ∈ A, p.Prime ∧ Q < p) (hδ : 0 < δ) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hQP : (Q : ℝ) ≤ P) (hδP : δ * Q * N ≤ P) (hsep : 2 * δ * (Q : ℝ) ^ 2 < 1)
    (h37 : c * N ≤ ∫ β in (-δ)..δ, ‖SA A w β‖ ^ 2) :
    c * N * Real.log ((Q : ℝ) + 1) ≤ R10 A w P N := by
  have h := lemma43_integrated A w hA hδ hN hQ hQP hδP hsep
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hlog : 0 ≤ Real.log ((Q : ℝ) + 1) := Real.log_nonneg (by linarith)
  nlinarith

/-- The paper's parameters satisfy the hypotheses: with δ = T/N and `Q T ≤ P`, the condition
`2 P² < T N`, true for P ≤ N^{4/9}, T ≥ 1 and N > 2⁹, gives `δ Q N ≤ P` and `2 δ Q² < 1`. -/
theorem params_ok {P N T : ℝ} {Q : ℕ} (hT : 0 < T) (hN : 0 < N) (hQT : (Q : ℝ) * T ≤ P)
    (hP : 2 * P ^ 2 < T * N) :
    T / N * Q * N ≤ P ∧ 2 * (T / N) * (Q : ℝ) ^ 2 < 1 := by
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  constructor
  · rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hN.ne']; linarith
  · have h1 : ((Q : ℝ) * T) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (by positivity) hQT 2
    rw [show 2 * (T / N) * (Q : ℝ) ^ 2 = 2 * ((Q : ℝ) * T) ^ 2 / (T * N) by
      field_simp]
    rw [div_lt_one (by positivity)]
    linarith

/-- Vacuity: N = 10⁶, P = 100, T = 1, Q = 100, A = {101} satisfy every hypothesis. -/
theorem vacuity :
    (∀ p ∈ ({101} : Finset ℕ), p.Prime ∧ 100 < p) ∧ (0 : ℝ) < 1 / 10 ^ 6 ∧
      ((100 : ℕ) : ℝ) ≤ 100 ∧ 1 / 10 ^ 6 * ((100 : ℕ) : ℝ) * 10 ^ 6 ≤ 100 ∧
      2 * (1 / 10 ^ 6 : ℝ) * ((100 : ℕ) : ℝ) ^ 2 < 1 := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  intro p hp
  rw [Finset.mem_singleton] at hp
  subst hp
  exact ⟨by norm_num, by norm_num⟩

end LeanLab.Linnik.LiLiuLemma43Int
