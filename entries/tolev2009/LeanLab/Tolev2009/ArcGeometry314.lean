module

public import LeanLab.Tolev2009.Decomp286a

/-!
AI wrote this Lean code. Codex task314.
Binary Goldbach is open.
Source: Tolev 2009 page 3, the rational major arcs.
These elementary geometry results support the rational arc expansion leaf.
-/

@[expose] public section

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.ArcGeometry314
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful

/-- Tolev page 3, clear the positive denominator in one rational arc. -/
theorem arc_membership_scaled (q a : ℕ) (τ x : ℝ) (hq : 1 ≤ q)
    (hx : x ∈ Set.Icc ((a : ℝ) / q - 1 / (q * τ)) ((a : ℝ) / q + 1 / (q * τ))) :
    (a : ℝ) - 1 / τ ≤ x * q ∧ x * q ≤ (a : ℝ) + 1 / τ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hl : (a : ℝ) / q - 1 / (q * τ) = ((a : ℝ) - 1 / τ) / q := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hr : (a : ℝ) / q + 1 / (q * τ) = ((a : ℝ) + 1 / τ) / q := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [Set.mem_Icc, hl, hr] at hx
  exact ⟨(div_le_iff₀ hq0).mp hx.1, (le_div_iff₀ hq0).mp hx.2⟩

/-- Tolev page 3, intersecting narrow arcs have equal rational centres. -/
theorem overlap_cross_product (q r a b : ℕ) (τ x : ℝ)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hτ : (q : ℝ) + r < τ)
    (ha : x ∈ Set.Icc ((a : ℝ) / q - 1 / (q * τ)) ((a : ℝ) / q + 1 / (q * τ)))
    (hb : x ∈ Set.Icc ((b : ℝ) / r - 1 / (r * τ)) ((b : ℝ) / r + 1 / (r * τ))) :
    a * r = b * q := by
  obtain ⟨ha₁, ha₂⟩ := arc_membership_scaled q a τ x hq ha
  obtain ⟨hb₁, hb₂⟩ := arc_membership_scaled r b τ x hr hb
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hτ0 : 0 < τ := by linarith
  have hsmall : ((q : ℝ) + r) / τ < 1 := (div_lt_one hτ0).mpr hτ
  have hd₁ : -1 < (a : ℝ) * r - (b : ℝ) * q := by
    have h1 := mul_le_mul_of_nonneg_right ha₂ hr0.le
    have h2 := mul_le_mul_of_nonneg_right hb₁ hq0.le
    have hid : ((q : ℝ) + r) / τ = (q : ℝ) / τ + (r : ℝ) / τ := by ring
    rw [hid] at hsmall
    simp only [div_eq_mul_inv] at hsmall h1 h2
    nlinarith
  have hd₂ : (a : ℝ) * r - (b : ℝ) * q < 1 := by
    have h1 := mul_le_mul_of_nonneg_right ha₁ hr0.le
    have h2 := mul_le_mul_of_nonneg_right hb₂ hq0.le
    have hid : ((q : ℝ) + r) / τ = (q : ℝ) / τ + (r : ℝ) / τ := by ring
    rw [hid] at hsmall
    simp only [div_eq_mul_inv] at hsmall h1 h2
    nlinarith
  have hdi₁ : (-1 : ℤ) < (a : ℤ) * r - (b : ℤ) * q := by exact_mod_cast hd₁
  have hdi₂ : (a : ℤ) * r - (b : ℤ) * q < 1 := by exact_mod_cast hd₂
  have he : (a : ℤ) * r = (b : ℤ) * q := by omega
  exact_mod_cast he

/-- Tolev page 3, two different reduced rational arcs are disjoint. -/
theorem reduced_arcs_disjoint (q r a b : ℕ) (τ : ℝ)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hτ : (q : ℝ) + r < τ)
    (ha : Nat.Coprime a q) (hb : Nat.Coprime b r) (hne : (q, a) ≠ (r, b)) :
    Disjoint (Set.Icc ((a : ℝ) / q - 1 / (q * τ)) ((a : ℝ) / q + 1 / (q * τ)))
      (Set.Icc ((b : ℝ) / r - 1 / (r * τ)) ((b : ℝ) / r + 1 / (r * τ))) := by
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  have he := overlap_cross_product q r a b τ x hq hr hτ hxa hxb
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hf : (a : ℚ) / q = (b : ℚ) / r := (div_eq_div_iff hqQ hrQ).mpr (by exact_mod_cast he)
  have hi := Rat.div_int_inj (show (0 : ℤ) < q by exact_mod_cast (show 0 < q by omega))
    (show (0 : ℤ) < r by exact_mod_cast (show 0 < r by omega))
    (by simpa using ha) (by simpa using hb) hf
  apply hne
  have hab : a = b := by exact_mod_cast hi.1
  have hqr : q = r := by exact_mod_cast hi.2
  simp [hab, hqr]

/-- Tolev page 3, every complete arc lies in the chosen unit interval. -/
theorem arc_subset_unit (q a : ℕ) (τ : ℝ) (hq : 1 ≤ q) (ha : a < q)
    (hτ : (q : ℝ) + 1 ≤ τ) :
    Set.Icc ((a : ℝ) / q - 1 / (q * τ)) ((a : ℝ) / q + 1 / (q * τ)) ⊆
      Set.Icc (-1 / τ) (1 - 1 / τ) := by
  intro x hx
  obtain ⟨hl, hr⟩ := arc_membership_scaled q a τ x hq hx
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have haq : (a : ℝ) ≤ q - 1 := by
    have hh : (a : ℝ) + 1 ≤ q := by exact_mod_cast (show a + 1 ≤ q by omega)
    linarith
  have hτ0 : 0 < τ := by linarith
  have hinv : 0 ≤ 1 / τ := by positivity
  have hsize : ((q : ℝ) + 1) * (1 / τ) ≤ 1 := by
    simpa only [div_eq_mul_inv, one_mul] using (div_le_one hτ0).mpr hτ
  constructor
  · apply (mul_le_mul_iff_right₀ hq0).mp
    have hh := mul_nonneg (sub_nonneg.mpr hq1) hinv
    simp only [div_eq_mul_inv, one_mul, neg_one_mul] at hl hh ⊢
    nlinarith
  · apply (mul_le_mul_iff_right₀ hq0).mp
    simp only [div_eq_mul_inv] at hr hsize ⊢
    nlinarith

/-- Tolev page 3, the finite index set of reduced rational arc centres. -/
noncomputable def arcIndices (Q : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (Icc 1 ⌊Q⌋₊).sigma (fun q => (range q).filter (fun a => Nat.Coprime a q))

/-- Tolev page 3, rewrite the major arcs as one finite union. -/
theorem majorArcs_eq_union (Q τ : ℝ) :
    majorArcs Q τ = ⋃ p ∈ arcIndices Q,
      Set.Icc ((p.2 : ℝ) / p.1 - 1 / (p.1 * τ))
        ((p.2 : ℝ) / p.1 + 1 / (p.1 * τ)) := by
  ext x
  simp [majorArcs, arcIndices, and_assoc, and_comm, and_left_comm]

/-- Tolev page 3, the finite family of complete major arcs is pairwise disjoint. -/
theorem arc_family_disjoint (Q τ : ℝ) (hQ : 1 ≤ Q) (hτ : 2 * Q < τ) :
    Set.Pairwise (↑(arcIndices Q)) (fun p s : Σ _ : ℕ, ℕ => Disjoint
      (Set.Icc ((p.2 : ℝ) / p.1 - 1 / (p.1 * τ)) ((p.2 : ℝ) / p.1 + 1 / (p.1 * τ)))
      (Set.Icc ((s.2 : ℝ) / s.1 - 1 / (s.1 * τ)) ((s.2 : ℝ) / s.1 + 1 / (s.1 * τ)))) := by
  intro p hp s hs hne
  obtain ⟨hpq, hpa⟩ := mem_sigma.mp hp
  obtain ⟨hsq, hsa⟩ := mem_sigma.mp hs
  have hpQ : (p.1 : ℝ) ≤ Q :=
    (Nat.cast_le.mpr (mem_Icc.mp hpq).2).trans (Nat.floor_le (by linarith))
  have hsQ : (s.1 : ℝ) ≤ Q :=
    (Nat.cast_le.mpr (mem_Icc.mp hsq).2).trans (Nat.floor_le (by linarith))
  apply reduced_arcs_disjoint p.1 s.1 p.2 s.2 τ (mem_Icc.mp hpq).1
    (mem_Icc.mp hsq).1 (by linarith) (mem_filter.mp hpa).2 (mem_filter.mp hsa).2
  intro he
  apply hne
  cases p
  cases s
  simp only [Prod.mk.injEq] at he
  cases he.1
  cases he.2
  rfl

/-- Tolev page 3, every major arc is contained in the selected unit interval. -/
theorem majorArcs_subset_unit (Q τ : ℝ) (hQ : 1 ≤ Q) (hτ : 2 * Q < τ) :
    majorArcs Q τ ⊆ Set.Icc (-1 / τ) (1 - 1 / τ) := by
  rw [majorArcs_eq_union]
  intro x hx
  obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨hpq, hpa⟩ := mem_sigma.mp hp
  have hpQ : (p.1 : ℝ) ≤ Q :=
    (Nat.cast_le.mpr (mem_Icc.mp hpq).2).trans (Nat.floor_le (by linarith))
  exact arc_subset_unit p.1 p.2 τ (mem_Icc.mp hpq).1
    (mem_range.mp (mem_filter.mp hpa).1) (by linarith) hx

/-- Tolev page 3 and Halupczok page 8, integrate a continuous function over complete disjoint arcs. -/
theorem integral_majorArcs (Q τ : ℝ) (f : ℝ → ℂ) (hf : Continuous f)
    (hQ : 1 ≤ Q) (hτ : 2 * Q < τ) :
    (∫ α in (-1 / τ)..(1 - 1 / τ), (majorArcs Q τ).indicator f α) =
      ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ β in (-1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)), f ((a : ℝ) / q + β) := by
  have hτ0 : 0 < τ := by linarith
  have hmajor := majorArcs_subset_unit Q τ hQ hτ
  have hset : majorArcs Q τ ∩ Set.Icc (-1 / τ) (1 - 1 / τ) = majorArcs Q τ :=
    Set.inter_eq_left.mpr hmajor
  rw [intervalIntegral.integral_of_le (by simp only [neg_div]; linarith),
    ← integral_Icc_eq_integral_Ioc, integral_indicator (measurableSet_majorArcs Q τ)]
  rw [Measure.restrict_restrict (measurableSet_majorArcs Q τ), hset, majorArcs_eq_union]
  rw [integral_biUnion_finset (arcIndices Q) (fun _ _ => measurableSet_Icc)
    (arc_family_disjoint Q τ hQ hτ) (fun _ _ => hf.continuousOn.integrableOn_Icc)]
  rw [arcIndices, sum_sigma]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro a ha
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q from (mem_Icc.mp hq).1)
  have hrad : 0 ≤ 1 / ((q : ℝ) * τ) := by positivity
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_comp_add_left]
  congr 1 <;> ring

end LeanLab.Tolev2009.ArcGeometry314
