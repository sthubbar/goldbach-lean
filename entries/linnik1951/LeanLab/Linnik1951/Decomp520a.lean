module

public import LeanLab.Linnik1951.CircleSplit111
public import LeanLab.Perelli1996.Ramanujan103
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import LeanLab.PNTPort.Selberg.WeightedMeanB

/-!
P0093 pages 156 and 159 through 165. Upstream local major arc decomposition.
Geometry proofs are ported from Geometry491 because that file imports the target.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open Finset MeasureTheory
/-- LEAF. P0093 page 165 before equation 8.1. Distinct rational centres are
separated by the reciprocal product of their denominators. -/
theorem rational_separation520 (a b : ℤ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hne : a * (r : ℤ) - b * (q : ℤ) ≠ 0) :
    1 / ((q : ℝ) * r) ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hi : (1 : ℤ) ≤ |a * (r : ℤ) - b * (q : ℤ)| := by
    have hp := abs_pos.mpr hne
    omega
  have hn : (1 : ℝ) ≤ |(a : ℝ) * r - (b : ℝ) * q| := by exact_mod_cast hi
  have heq : (a : ℝ) / q - (b : ℝ) / r =
      ((a : ℝ) * r - (b : ℝ) * q) / ((q : ℝ) * r) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hq0 hr0)]
  exact div_le_div_of_nonneg_right hn (mul_pos hq0 hr0).le

/-- LEAF. P0093 page 165 before equation 8.1. Two rational major arcs are
disjoint when their denominator sum is strictly smaller than tau. -/
theorem rational_arcs_disjoint520 (a b : ℤ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hne : a * (r : ℤ) - b * (q : ℤ) ≠ 0) (τ : ℝ)
    (hτsum : (q : ℝ) + r < τ) :
    Disjoint
      (Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * τ))
        ((a : ℝ) / q + 1 / ((q : ℝ) * τ)))
      (Set.Icc ((b : ℝ) / r - 1 / ((r : ℝ) * τ))
        ((b : ℝ) / r + 1 / ((r : ℝ) * τ))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hτ : 0 < τ := by linarith
  have hrad : 1 / ((q : ℝ) * τ) + 1 / ((r : ℝ) * τ) < 1 / ((q : ℝ) * r) := by
    apply (lt_div_iff₀ (mul_pos hq0 hr0)).mpr
    have heq : (1 / ((q : ℝ) * τ) + 1 / ((r : ℝ) * τ)) * ((q : ℝ) * r) =
        ((q : ℝ) + r) / τ := by field_simp; ring
    rw [heq]
    exact (div_lt_one hτ).mpr hτsum
  rw [Set.disjoint_left]
  intro α hα hβ
  have ha : |(a : ℝ) / q - α| ≤ 1 / ((q : ℝ) * τ) := by
    apply abs_le.mpr
    constructor <;> linarith [hα.1, hα.2]
  have hb : |α - (b : ℝ) / r| ≤ 1 / ((r : ℝ) * τ) := by
    apply abs_le.mpr
    constructor <;> linarith [hβ.1, hβ.2]
  have hd := rational_separation520 a b q r hq hr hne
  have ht := abs_sub_le ((a : ℝ) / q) α ((b : ℝ) / r)
  linarith


/-- P0093 page 165 equation 8.1 and page 166 equation 8.2. The finite reduced rational centres, including both endpoint representatives at modulus one. -/
noncomputable def arcIndices520 (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 Q) ×ˢ (Icc 0 Q)).filter fun p => p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1
/-- P0093 page 165 equation 8.1 and page 166 equation 8.2. The full closed rational arc of radius one over q tau. -/
noncomputable def rationalArc520 (q a : ℕ) (τ : ℝ) : Set ℝ :=
  Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * τ)) ((a : ℝ) / q + 1 / ((q : ℝ) * τ))
/-- P0093 page 165 equation 8.1 and page 166 equation 8.2. The rational major arcs with natural denominator cutoff, clipped to the unit interval. -/
noncomputable def rationalMajor520 (Q : ℕ) (τ : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 1 ∧ ∃ r : ℚ, r.den ≤ Q ∧ |α - r| ≤ 1 / ((r.den : ℝ) * τ)}

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. Membership in the finite rational centre index set. -/
theorem arcIndices_mem520 (Q : ℕ) (p : ℕ × ℕ) :
    p ∈ arcIndices520 Q ↔ 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1 := by
  constructor
  · intro h
    obtain ⟨hpair, ha, hcop⟩ := Finset.mem_filter.mp h
    obtain ⟨hq, haQ⟩ := Finset.mem_product.mp hpair
    exact ⟨(mem_Icc.mp hq).1, (mem_Icc.mp hq).2, ha, hcop⟩
  · rintro ⟨hq, hqQ, ha, hcop⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨mem_Icc.mpr ⟨hq, hqQ⟩,
      mem_Icc.mpr ⟨Nat.zero_le _, ha.trans hqQ⟩⟩, ha, hcop⟩


/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The rational definition equals the explicit finite union of clipped arcs. -/
theorem rational_major_cover520 (Q : ℕ) (τ : ℝ) (hτ : 1 < τ) :
    rationalMajor520 Q τ =
      ⋃ p ∈ arcIndices520 Q, Set.Icc (0 : ℝ) 1 ∩ rationalArc520 p.1 p.2 τ := by
  ext α
  constructor
  · rintro ⟨hα, r, hrQ, hrα⟩
    have hq : 0 < r.den := r.pos
    have hqr : (0 : ℝ) < r.den := by exact_mod_cast hq
    have hc : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by
      rw [Rat.cast_def, div_mul_cancel₀ _ (ne_of_gt hqr)]
    have hm := mul_le_mul_of_nonneg_right hrα hqr.le
    have hdist : |α * (r.den : ℝ) - (r.num : ℝ)| < 1 := by
      have he : |α - (r : ℝ)| * (r.den : ℝ) =
          |α * (r.den : ℝ) - (r.num : ℝ)| := by
        calc
          _ = |(α - (r : ℝ)) * (r.den : ℝ)| := by rw [abs_mul, abs_of_pos hqr]
          _ = _ := by rw [sub_mul, hc]
      rw [he] at hm
      have he' : (1 / ((r.den : ℝ) * τ)) * (r.den : ℝ) = 1 / τ := by field_simp
      rw [he'] at hm
      exact hm.trans_lt ((div_lt_one (by linarith : 0 < τ)).mpr hτ)
    have hlow : (-1 : ℝ) < (r.num : ℝ) := by
      have hh := (abs_lt.mp hdist).2
      nlinarith [hα.1]
    have hhigh : (r.num : ℝ) < (r.den : ℝ) + 1 := by
      have hh := (abs_lt.mp hdist).1
      nlinarith [hα.2]
    have hn0 : 0 ≤ r.num := by
      have hi : (-1 : ℤ) < r.num := by exact_mod_cast hlow
      omega
    have hnq : r.num ≤ (r.den : ℤ) := by
      have hi : r.num < (r.den : ℤ) + 1 := by exact_mod_cast hhigh
      omega
    let a := r.num.toNat
    have ha : (a : ℤ) = r.num := Int.toNat_of_nonneg hn0
    have haq : a ≤ r.den := by omega
    have hcop : Nat.Coprime a r.den := by
      have hh := r.reduced
      simpa [← ha] using hh
    have hp : (r.den, a) ∈ arcIndices520 Q :=
      (arcIndices_mem520 Q _).mpr ⟨hq, hrQ, haq, hcop⟩
    have heq : (a : ℝ) / r.den = (r : ℝ) := by
      rw [Rat.cast_def]
      congr 1
      exact_mod_cast ha
    apply Set.mem_iUnion.mpr
    refine ⟨(r.den, a), Set.mem_iUnion.mpr ⟨hp, hα, ?_⟩⟩
    change α ∈ Set.Icc ((a : ℝ) / r.den - 1 / ((r.den : ℝ) * τ))
      ((a : ℝ) / r.den + 1 / ((r.den : ℝ) * τ))
    rw [heq]
    have hh := abs_le.mp hrα
    constructor <;> linarith
  · intro hα
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hα
    obtain ⟨hp, hunit, harc⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hq, hqQ, ha, hcop⟩ := (arcIndices_mem520 Q p).mp hp
    let r : ℚ := (p.2 : ℚ) / p.1
    have hd : r.den = p.1 := by
      have hh := Rat.den_div_eq_of_coprime
        (a := (p.2 : ℤ)) (b := (p.1 : ℤ))
        (by exact_mod_cast hq : (0 : ℤ) < (p.1 : ℤ)) (by simpa using hcop)
      have hdi : ((((p.2 : ℚ) / p.1).den : ℤ)) = (p.1 : ℤ) := by
        simpa only [Int.cast_natCast] using hh
      exact Int.ofNat_inj.mp hdi
    refine ⟨hunit, r, by simpa [hd] using hqQ, ?_⟩
    rw [hd]
    have heq : (r : ℝ) = (p.2 : ℝ) / p.1 := by simp [r]
    rw [heq]
    apply abs_le.mpr
    change α ∈ Set.Icc ((p.2 : ℝ) / p.1 - 1 / ((p.1 : ℝ) * τ))
      ((p.2 : ℝ) / p.1 + 1 / ((p.1 : ℝ) * τ)) at harc
    constructor <;> linarith [harc.1, harc.2]
/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. Distinct reduced rational representatives have nonzero cross difference. -/
theorem arcIndices_cross_ne520 (Q : ℕ) (p t : ℕ × ℕ)
    (hp : p ∈ arcIndices520 Q) (ht : t ∈ arcIndices520 Q) (hne : p ≠ t) :
    (p.2 : ℤ) * t.1 - (t.2 : ℤ) * p.1 ≠ 0 := by
  obtain ⟨hp1, hpQ, hp2, hpc⟩ := (arcIndices_mem520 Q p).mp hp
  obtain ⟨ht1, htQ, ht2, htc⟩ := (arcIndices_mem520 Q t).mp ht
  intro h
  have hm : p.2 * t.1 = t.2 * p.1 := by exact_mod_cast sub_eq_zero.mp h
  have hpt : p.1 ∣ t.1 := hpc.symm.dvd_mul_left.mp (by rw [hm]; exact dvd_mul_left _ _)
  have htp : t.1 ∣ p.1 := htc.symm.dvd_mul_left.mp (by rw [← hm]; exact dvd_mul_left _ _)
  have heq : p.1 = t.1 := Nat.dvd_antisymm hpt htp
  have ha : p.2 = t.2 := by
    rw [heq] at hm
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < t.1) hm
  exact hne (Prod.ext heq ha)

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The integral over the major arcs is the sum of the clipped arc integrals. -/
theorem rational_clipped_integral520 (Q : ℕ) (hQ : 1 ≤ Q) (τ : ℝ)
    (hτ : 2 * (Q : ℝ) < τ) (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ α in rationalMajor520 Q τ, f α) =
      ∑ p ∈ arcIndices520 Q,
        ∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc520 p.1 p.2 τ, f α := by
  have hτ1 : 1 < τ := by
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  rw [rational_major_cover520 Q τ hτ1]
  apply integral_biUnion_finset
  · intro p hp
    exact measurableSet_Icc.inter measurableSet_Icc
  · intro p hp t ht hne
    have hpQ := ((arcIndices_mem520 Q p).mp hp).2.1
    have htQ := ((arcIndices_mem520 Q t).mp ht).2.1
    have hsum : (p.1 : ℝ) + t.1 < τ := by
      have hpr : (p.1 : ℝ) ≤ Q := by exact_mod_cast hpQ
      have htr : (t.1 : ℝ) ≤ Q := by exact_mod_cast htQ
      linarith
    have hd := rational_arcs_disjoint520 (p.2 : ℤ) (t.2 : ℤ) p.1 t.1
      ((arcIndices_mem520 Q p).mp hp).1 ((arcIndices_mem520 Q t).mp ht).1
      (arcIndices_cross_ne520 Q p t hp ht hne) τ hsum
    exact hd.mono Set.inter_subset_right Set.inter_subset_right
  · intro p hp
    exact hf.integrableOn_Icc.mono_set Set.inter_subset_left

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. Translation converts a full rational arc integral to its symmetric local coordinate integral. -/
theorem rational_arc_integral520 (q a : ℕ) (hq : 1 ≤ q) (τ : ℝ) (hτ : 0 < τ)
    (f : ℝ → ℂ) :
    (∫ α in rationalArc520 q a τ, f α) =
      ∫ z in -(1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)), f ((a : ℝ) / q + z) := by
  have hR : 0 ≤ 1 / ((q : ℝ) * τ) := by positivity
  unfold rationalArc520
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_comp_add_left]
  congr 1 <;> ring

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. For denominator at least two, every reduced representative arc lies inside the unit interval. -/
theorem interior_arc_subset520 (q a : ℕ) (hq : 2 ≤ q) (ha : a < q)
    (hc : Nat.Coprime a q) (τ : ℝ) (hτ : 1 ≤ τ) :
    rationalArc520 q a τ ⊆ Set.Icc 0 1 := by
  have ha1 : 1 ≤ a := by
    by_contra hh
    have hz : a = 0 := by omega
    simp [hz] at hc
    omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hrad : 1 / ((q : ℝ) * τ) ≤ 1 / (q : ℝ) := by
    apply one_div_le_one_div_of_le hq0
    nlinarith
  have hlo : 1 / (q : ℝ) ≤ (a : ℝ) / q :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha1) hq0.le
  have hhi : (a : ℝ) / q + 1 / q ≤ 1 := by
    rw [← add_div]
    apply (div_le_one hq0).mpr
    exact_mod_cast (show a + 1 ≤ q by omega)
  intro α hα
  change α ∈ Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * τ))
    ((a : ℝ) / q + 1 / ((q : ℝ) * τ)) at hα
  constructor <;> linarith [hα.1, hα.2]

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The clipped endpoint arcs join into the symmetric unit modulus arc by period one. -/
theorem unit_arc_join520 (τ : ℝ) (hτ : 2 < τ) (f : ℝ → ℂ)
    (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc520 1 0 τ, f α) +
      (∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc520 1 1 τ, f α) =
      ∫ z in -(1 / τ)..(1 / τ), f z := by
  let R : ℝ := 1 / τ
  have hτ0 : 0 < τ := by linarith
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := (div_le_one hτ0).mpr (by linarith)
  have hh : Set.Icc (0 : ℝ) 1 ∩ rationalArc520 1 0 τ = Set.Icc 0 R := by
    ext α
    simp only [rationalArc520, Nat.cast_one, Nat.cast_zero, zero_div, one_mul, zero_sub,
      zero_add, Set.mem_inter_iff, Set.mem_Icc]
    dsimp [R] at *
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.1, h2.2⟩
    · intro h
      constructor <;> constructor <;> linarith [h.1, h.2]
  have ht : Set.Icc (0 : ℝ) 1 ∩ rationalArc520 1 1 τ = Set.Icc (1 - R) 1 := by
    ext α
    simp only [rationalArc520, Nat.cast_one, div_one, one_mul, Set.mem_inter_iff, Set.mem_Icc]
    dsimp [R] at *
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2.1, h1.2⟩
    · intro h
      constructor <;> constructor <;> linarith [h.1, h.2]
  rw [hh, ht, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hR0,
    ← intervalIntegral.integral_of_le (show 1 - R ≤ 1 by linarith)]
  have hs : (∫ x in (1 - R)..1, f x) = ∫ x in -R..0, f x := by
    have h := intervalIntegral.integral_comp_add_right (a := -R) (b := (0 : ℝ)) f 1
    have hfun : (fun x : ℝ => f (x + 1)) = f := funext hp
    rw [hfun] at h
    simpa only [zero_add, neg_add_eq_sub] using h.symm
  rw [hs, add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. At each denominator the clipped representatives give the required full local arc sum. -/
theorem denominator_arc_sum520 (q : ℕ) (hq : 1 ≤ q) (τ : ℝ) (hτ : 2 < τ)
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∑ a ∈ (Icc 0 q).filter (fun a => Nat.Coprime a q),
      ∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc520 q a τ, f α) =
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ∫ z in -(1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)), f ((a : ℝ) / q + z) := by
  classical
  by_cases hq1 : q = 1
  · subst q
    have hi : (Icc 0 (1 : ℕ)).filter (fun a => Nat.Coprime a 1) = {0, 1} := by decide
    have hr : (range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
    rw [hi, hr]
    simpa using unit_arc_join520 τ hτ f hf hp
  · have hq2 : 2 ≤ q := by omega
    have heq : (Icc 0 q).filter (fun a => Nat.Coprime a q) =
        (range q).filter (fun a => Nat.Coprime a q) := by
      ext a
      simp only [mem_filter, mem_Icc, mem_range]
      constructor
      · rintro ⟨ha, hc⟩
        have hne : a ≠ q := by intro h; subst a; exact hq1 (by simpa using hc)
        exact ⟨by omega, hc⟩
      · rintro ⟨ha, hc⟩
        exact ⟨⟨Nat.zero_le _, ha.le⟩, hc⟩
    rw [heq]
    apply Finset.sum_congr rfl
    intro a ha
    have has := (mem_filter.mp ha).1
    have hac := (mem_filter.mp ha).2
    have hsub := interior_arc_subset520 q a hq2 (mem_range.mp has) hac τ (by linarith)
    rw [Set.inter_eq_right.mpr hsub]
    exact rational_arc_integral520 q a hq τ (by linarith) f

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The pair index sum equals the iterated denominator and reduced numerator sum. -/
theorem arcIndices_sum520 (Q : ℕ) (H : ℕ × ℕ → ℂ) :
    (∑ p ∈ arcIndices520 Q, H p) =
      ∑ q ∈ Icc 1 Q, ∑ a ∈ (Icc 0 q).filter (fun a => Nat.Coprime a q), H (q, a) := by
  classical
  simp only [arcIndices520, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  have hqQ : q ≤ Q := (mem_Icc.mp hq).2
  have hset : (Icc 0 Q).filter (fun a => a ≤ q ∧ Nat.Coprime a q) =
      (Icc 0 q).filter (fun a => Nat.Coprime a q) := by
    ext a
    simp only [mem_filter, mem_Icc]
    omega
  rw [← Finset.sum_filter, ← Finset.sum_filter, hset]

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. A continuous periodic function has the exact rational arc partition when tau exceeds twice Q. -/
theorem rational_partition520 (Q : ℕ) (hQ : 1 ≤ Q) (τ : ℝ)
    (hτ : 2 * (Q : ℝ) < τ) (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ α in rationalMajor520 Q τ, f α) =
      ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)), f ((a : ℝ) / q + z) := by
  rw [rational_clipped_integral520 Q hQ τ hτ f hf, arcIndices_sum520]
  apply Finset.sum_congr rfl
  intro q hq
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  exact denominator_arc_sum520 q (mem_Icc.mp hq).1 τ (by linarith) f hf hp

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. Above two to power seventy the chosen tau exceeds twice the integer Q. -/
theorem major_parameters_separated520 (N : ℕ) (hN : 2 ^ 70 < N) :
    1 ≤ ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ ∧
      2 * (⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by positivity
  have hbase : (2 : ℝ) ^ (70 : ℕ) < N := by exact_mod_cast hN
  have hpow := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ 2 ^ (70 : ℕ)) hbase
    (show (0 : ℝ) < 3 / 70 by norm_num)
  have he : ((2 : ℝ) ^ (70 : ℕ)) ^ (3 / 70 : ℝ) = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [he] at hpow
  have hsave : 2 * (N : ℝ) ^ (1 / 10 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := by
    have hm := mul_lt_mul_of_pos_right (show (2 : ℝ) < (N : ℝ) ^ (3 / 70 : ℝ) by linarith)
      (Real.rpow_pos_of_pos hN0 (1 / 10 : ℝ))
    have heq : (N : ℝ) ^ (3 / 70 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) =
        (N : ℝ) ^ (1 / 7 : ℝ) := by
      rw [← Real.rpow_add hN0]
      norm_num
    rwa [heq] at hm
  constructor
  · apply (Nat.le_floor_iff (show 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) by positivity)).mpr
    simpa only [Nat.cast_one] using Real.one_le_rpow hNr (show (0 : ℝ) ≤ 1 / 10 by norm_num)
  · exact (mul_le_mul_of_nonneg_left (Nat.floor_le (show 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) by positivity))
      (show (0 : ℝ) ≤ 2 by norm_num)).trans_lt hsave

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The exact major arc partition at the parameters used by the sealed target. -/
theorem major_arc_partition_proved520 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ f : ℝ → ℂ,
      Continuous f → Function.Periodic f 1 →
      (∫ α in majorArcs280_up111 N, f α) =
        ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
                (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
              f ((a : ℝ) / q + z) := by
  refine ⟨2 ^ 70, ?_⟩
  intro N hN f hf hp
  have hsep := major_parameters_separated520 N hN
  have heq : majorArcs280_up111 N = rationalMajor520 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊
      ((N : ℝ) ^ (1 / 7 : ℝ)) := by
    ext α
    simp only [majorArcs280_up111, rationalMajor520, Set.mem_setOf_eq,
      Nat.le_floor_iff (show 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) by positivity)]
  rw [heq]
  exact rational_partition520 _ hsep.1 _ hsep.2 f hf hp

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- P0093 page 159 before equation 5.1. The principal character prime series
is the prime series with the prime divisors of the modulus removed. -/
noncomputable def principalPrime520 (N q : ℕ) (z : ℝ) : ℂ :=
  primeFourier111_up111 N z - ∑ p ∈ q.primeFactors,
    (Real.exp (-(p : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)

/-- P0093 page 156 equation 3.4. The principal rational coefficient. -/
noncomputable def principalCoefficient520 (q : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) : ℝ)

/-- P0093 page 156 equation 3.4. The residue error retains the omitted
prime divisor terms after removing the principal character contribution. -/
noncomputable def residueError520 (N q a : ℕ) (z : ℝ) : ℂ :=
  primeFourier111_up111 N ((a : ℝ) / q + z) -
    principalCoefficient520 q * principalPrime520 N q z

/-- P0093 pages 155 and 156 equations 3.1 and 3.4. The local prime square integral. -/
noncomputable def localArc520 (N q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      (primeFourier111_up111 N ((a : ℝ) / q + z) ^ 2) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)

/-- P0093 pages 155 and 156 equations 3.1 and 3.4. The mixed local contribution. -/
noncomputable def mixedIntegral520 (N q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      (2 * principalCoefficient520 q * principalPrime520 N q z * residueError520 N q a z) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)

/-- P0093 pages 155 and 156 equations 3.1 and 3.4. The square of the residue error. -/
noncomputable def errorIntegral520 (N q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      (residueError520 N q a z ^ 2) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)

/-- P0093 page 160 equation 6.1. The principal square on one centred arc. -/
noncomputable def principalIntegral520 (N q : ℕ) (n : ℤ) : ℂ :=
  ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
    principalPrime520 N q z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)

/-- P0093 page 156 equation 3.4. The Ramanujan phase at a signed residual. -/
noncomputable def signedRamanujan520 (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)

/-- P0093 page 161 after equation 6.3. The exact logarithmic convolution. -/
noncomputable def logConvolution520 (n : ℕ) : ℝ :=
  ∑ m ∈ Icc 2 (n - 2), 1 / (Real.log m * Real.log (n - m : ℕ))

/-- P0093 page 161 equation 6.4. The exact damped local main term. -/
noncomputable def localMain520 (N q : ℕ) (n : ℤ) : ℂ :=
  principalCoefficient520 q ^ 2 * signedRamanujan520 q n *
    ((Real.exp (-(n : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ)

/-- P0093 page 159 equation 5.1. The principal series is continuous. -/
theorem continuous_principal520 (N q : ℕ) (hN : 1 ≤ N) :
    Continuous (principalPrime520 N q) := by
  unfold principalPrime520
  exact (continuous_prime_fourier111_up111 N hN).sub (by fun_prop)

/-- P0093 page 156 equation 3.4. Every residue error is continuous. -/
theorem continuous_residue520 (N q a : ℕ) (hN : 1 ≤ N) :
    Continuous (residueError520 N q a) := by
  unfold residueError520
  exact ((continuous_prime_fourier111_up111 N hN).comp (by fun_prop)).sub
    (continuous_const.mul (continuous_principal520 N q hN))

/-- P0093 page 156 equation 3.4. Exact square expansion at one residue. -/
theorem residue_square520 (N q a : ℕ) (z : ℝ) :
    primeFourier111_up111 N ((a : ℝ) / q + z) ^ 2 =
      principalCoefficient520 q ^ 2 * principalPrime520 N q z ^ 2 +
        2 * principalCoefficient520 q * principalPrime520 N q z * residueError520 N q a z +
        residueError520 N q a z ^ 2 := by
  unfold residueError520
  ring

/-- P0093 page 156 equation 3.4. The centred phase factors exactly. -/
theorem centred_phase520 (q a : ℕ) (n : ℤ) (z : ℝ) :
    Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- P0093 page 156 equation 3.4. Exact principal, mixed and error square split. -/
theorem local_decomposition520 (N q : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    localArc520 N q n =
      principalCoefficient520 q ^ 2 * signedRamanujan520 q n * principalIntegral520 N q n +
        mixedIntegral520 N q n + errorIntegral520 N q n := by
  classical
  have hmain : principalCoefficient520 q ^ 2 * signedRamanujan520 q n *
      principalIntegral520 N q n =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))), principalCoefficient520 q ^ 2 * principalPrime520 N q z ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I) := by
    unfold signedRamanujan520 principalIntegral520
    rw [mul_sum, sum_mul]
    apply sum_congr rfl
    intro a ha
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only
    rw [centred_phase520]
    ring
  unfold localArc520 mixedIntegral520 errorIntegral520
  rw [hmain, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have hA := continuous_principal520 N q hN
  have hE := continuous_residue520 N q a hN
  have hp : Continuous (fun z : ℝ => Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have h1 : IntervalIntegrable (fun z : ℝ =>
      (principalCoefficient520 q ^ 2 * principalPrime520 N q z ^ 2) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
    (show Continuous (fun z : ℝ => (principalCoefficient520 q ^ 2 * principalPrime520 N q z ^ 2) *
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) from by fun_prop).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun z : ℝ =>
      (2 * principalCoefficient520 q * principalPrime520 N q z * residueError520 N q a z) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
    (show Continuous (fun z : ℝ => (2 * principalCoefficient520 q * principalPrime520 N q z * residueError520 N q a z) *
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) from by fun_prop).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun z : ℝ =>
      (residueError520 N q a z ^ 2) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
    (show Continuous (fun z : ℝ => (residueError520 N q a z ^ 2) *
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) from by fun_prop).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add h1 h2,
    ← intervalIntegral.integral_add (h1.add h2) h3]
  apply intervalIntegral.integral_congr
  intro z hz
  dsimp only
  rw [residue_square520]
  ring



/-- P0093 page 161 equation 6.3. The damped reciprocal logarithm coefficient,
extended by zero at frequencies zero and one. -/
noncomputable def logCoefficient520 (N m : ℕ) : ℂ :=
  if 2 ≤ m then ((Real.exp (-(m : ℝ) / N) / Real.log m : ℝ) : ℂ) else 0

/-- P0093 page 161 equation 6.3. The model series S one. -/
noncomputable def logFourier520 (N : ℕ) (z : ℝ) : ℂ :=
  ∑' m : ℕ, logCoefficient520 N m *
    Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)

/-- P0093 page 161 equation 6.3. The logarithmic coefficients are absolutely
summable by comparison with the geometric damping series. -/
theorem logCoefficient_summable520 (N : ℕ) (hN : 1 ≤ N) :
    Summable (logCoefficient520 N) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _
    ((damping_summable111_up111 N hN).mul_right (1 / Real.log 2))
  intro m
  by_cases hm : 2 ≤ m
  · have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hl : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hmR
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    simp only [logCoefficient520, if_pos hm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.exp_pos _).le (hl2.le.trans hl))]
    simpa only [mul_one_div] using div_le_div_of_nonneg_left (Real.exp_pos _).le hl2 hl
  · simp only [logCoefficient520, if_neg hm, norm_zero]
    positivity

/-- P0093 page 161 equation 6.3. Mathlib Cauchy multiplication groups the
square of an absolutely convergent Fourier series by its total frequency. -/
theorem fourier_square_group520 (a : ℕ → ℂ) (ha : Summable a) (z : ℝ) :
    (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2 =
      ∑' m : ℕ, (∑ j ∈ range (m + 1), a j * a (m - j)) *
        Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I) := by
  have hs : Summable (fun m : ℕ => ‖a m *
      Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)‖) := by
    simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using ha.norm
  rw [pow_two, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hs hs]
  apply tsum_congr
  intro m
  rw [sum_mul]
  apply sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by have := mem_range.mp hj; omega
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast [Nat.cast_sub hjm]
  ring

/-- P0093 page 161 equation 6.3. The full period coefficient of the square
is its Cauchy convolution at nonnegative residuals and zero at negative residuals. -/
theorem fourier_square_integral520 (a : ℕ → ℂ) (ha : Summable a) (n : ℤ) :
    (∫ z in (0 : ℝ)..1,
      (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2 *
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      if 0 ≤ n then ∑ j ∈ range (n.toNat + 1), a j * a (n.toNat - j) else 0 := by
  let b : ℕ → ℂ := fun m => ∑ j ∈ range (m + 1), a j * a (m - j)
  have hb : Summable b := (summable_norm_sum_mul_range_of_summable_norm ha.norm ha.norm).of_norm
  have hc := negative_series_coefficient_proved357_up111 b hb (-n)
  rw [coefficient_integral357_up111] at hc
  have he (z : ℝ) : LeanLab.Perelli1996.Kernel.e (-((-n : ℤ) : ℝ) * z) =
      Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    unfold LeanLab.Perelli1996.Kernel.e
    congr 1
    push_cast
    ring
  simp_rw [he] at hc
  have hi : (∫ z in (0 : ℝ)..1,
      (∑' m : ℕ, a m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I)) ^ 2 *
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ∫ z in (0 : ℝ)..1, Complex.exp
        (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) *
          ∑' m : ℕ, b m * Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only
    rw [fourier_square_group520 a ha]
    exact mul_comm _ _
  rw [hi, hc]
  by_cases hn : 0 ≤ n
  · have habs : (-n).natAbs = n.toNat := by omega
    simp [hn, neg_nonpos.mpr hn, habs, b]
  · have hp : ¬ -n ≤ 0 := by omega
    simp [hn, hp]

/-- P0093 page 161 after equation 6.3. The Cauchy coefficient of S one
squared is exactly the exponentially damped finite logarithmic convolution. -/
theorem logCoefficient_convolution520 (N m : ℕ) :
    (∑ j ∈ range (m + 1), logCoefficient520 N j * logCoefficient520 N (m - j)) =
      ((Real.exp (-(m : ℝ) / N) * logConvolution520 m : ℝ) : ℂ) := by
  classical
  have hsum : (∑ j ∈ range (m + 1), logCoefficient520 N j * logCoefficient520 N (m - j)) =
      ∑ j ∈ Icc 2 (m - 2), logCoefficient520 N j * logCoefficient520 N (m - j) := by
    symm
    apply sum_subset
    · intro j hj
      have hh := mem_Icc.mp hj
      exact mem_range.mpr (by omega)
    · intro j hj hout
      by_cases hj2 : 2 ≤ j
      · have hmj : ¬ 2 ≤ m - j := by
          intro h
          apply hout
          exact mem_Icc.mpr ⟨hj2, by omega⟩
        simp [logCoefficient520, hmj]
      · simp [logCoefficient520, hj2]
  rw [hsum, logConvolution520, mul_sum, Complex.ofReal_sum]
  apply sum_congr rfl
  intro j hj
  obtain ⟨hj2, hjm⟩ := mem_Icc.mp hj
  have hjle : j ≤ m := by omega
  have hmj : 2 ≤ m - j := by omega
  simp only [logCoefficient520, if_pos hj2, if_pos hmj, ← Complex.ofReal_mul]
  congr 1
  rw [div_mul_div_comm, ← Real.exp_add]
  have he : -(j : ℝ) / N + -((m - j : ℕ) : ℝ) / N = -(m : ℝ) / N := by
    push_cast [Nat.cast_sub hjle]
    ring
  rw [he]
  ring

/-- P0093 page 161 after equation 6.3. The exact signed full period
model integral is the damped convolution, including every negative residual. -/
theorem logFourier_square_integral520 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ((Real.exp (-(n : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ) := by
  unfold logFourier520
  rw [fourier_square_integral520 _ (logCoefficient_summable520 N hN)]
  by_cases hn : 0 ≤ n
  · rw [if_pos hn, logCoefficient_convolution520]
    have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    rw [hc]
  · rw [if_neg hn]
    have hz : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    simp [hz, logConvolution520]



/-! ## Ported analytic inputs. The modules that carry these estimates
(Decomp519a, PrimeArcLeaf491, PrincipalTail491, LogFourierMass491, ArcCross520,
PrimeArcRadius520) either transitively import the sealed target or need
Decomp552b's own definition, so their content is reproduced here as private
helpers over `PNTPort.Selberg`. -/
/-- Zeros in the open strip on the line give Mathlib's `RiemannHypothesis`. -/
private theorem rh_of_strip_p (h : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2) :
    RiemannHypothesis := by
  intro s hz hnt hs1
  rcases lt_or_ge 0 s.re with hpos | hneg
  · rcases lt_or_ge s.re 1 with hlt | hge
    · exact h s hz hpos hlt
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hge)
  · exfalso
    set w := 1 - s with hw
    have hwre : 1 ≤ w.re := by simp [hw]; linarith
    have hs : s = 1 - w := by rw [hw]; ring
    have hw1 : w ≠ 1 := by
      intro h1
      have : s = 0 := by rw [hs, h1]; ring
      rw [this, riemannZeta_zero] at hz; norm_num at hz
    have hwn : ∀ n : ℕ, w ≠ -n := by
      intro n hn
      have := congrArg Complex.re hn
      simp at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub hwn hw1
    rw [← hs, hz] at hfe
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have hpi : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
      have h2p : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl h2p)
    have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
    have hcos : Complex.cos (Real.pi * w / 2) = 0 := by
      by_contra hc
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hpi) hG) hc) hzw) hfe.symm
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
    have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hwk : w = 2 * k + 1 := by
      have := hk
      field_simp at this
      exact this
    have hsk : s = -(2 * (k : ℂ)) := by rw [hs, hwk]; ring
    have hkre := congrArg Complex.re hsk
    simp at hkre
    have hk0 : 0 ≤ k := by
      have : (0 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    have hk1 : k ≠ 0 := by
      rintro rfl
      have : s = 0 := by rw [hsk]; simp
      rw [this, riemannZeta_zero] at hz; norm_num at hz
    apply hnt
    refine ⟨(k - 1).toNat, ?_⟩
    have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    rw [hsk]
    have : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by exact_mod_cast this
    rw [this]; ring

/-- P0011's `LeanLab.DERZ1997.GRH` gives Mathlib's `RiemannHypothesis`, through `q = 1`. -/
private theorem rh_of_GRH_p (hG : LeanLab.DERZ1997.GRH) : RiemannHypothesis := by
  apply rh_of_strip_p
  intro s hz h0 h1
  have := hG 1 (1 : DirichletCharacter ℂ 1) s (by rw [DirichletCharacter.LFunction_modOne_eq]; exact hz) h0 h1
  exact this




/-- P0093 page 154, the series S, and page 161, the series S one. A bound for
the square integral of every truncation of an absolutely convergent series of
negative frequencies passes to the full series. Proved by dominated convergence
on the arc, with the constant bound given by the square of the sum of the norms.
Standard analysis, not in the print. -/
private theorem series_arc_limit491 (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) (r K : ℝ)
    (hr : 0 ≤ r)
    (h : ∀ M : ℕ, (∫ z in -r..r, ‖∑ n ∈ range M, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) ≤ K) :
    (∫ z in -r..r, ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) ≤ K := by
  have hnorm : ∀ (n : ℕ) (z : ℝ),
      ‖a n * Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ = ‖a n‖ := by
    intro n z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsum : ∀ z : ℝ, Summable
      (fun n : ℕ => a n * Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)) := by
    intro z
    refine Summable.of_norm ?_
    simpa only [hnorm] using ha
  have hb : ∀ (M : ℕ) (z : ℝ), ‖∑ n ∈ range M, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ≤ ∑' n, ‖a n‖ := by
    intro M z
    refine (norm_sum_le _ _).trans ?_
    simp only [hnorm]
    exact ha.sum_le_tsum _ (fun i _ => norm_nonneg _)
  have hcont : ∀ M : ℕ, Continuous (fun z : ℝ => ‖∑ n ∈ range M, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) := by
    intro M
    fun_prop
  have key := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := -r) (b := r) (l := Filter.atTop)
    (F := fun (M : ℕ) (z : ℝ) => ‖∑ n ∈ range M, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2)
    (f := fun z : ℝ => ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2)
    (fun _ => (∑' n, ‖a n‖) ^ 2)
    (Filter.Eventually.of_forall fun M => (hcont M).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun M => Filter.Eventually.of_forall fun z _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb M z) 2)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun z _ =>
      (((hsum z).hasSum.tendsto_sum_nat).norm).pow 2)
  exact le_of_tendsto' key h





/-- The weights one over ln of max n 2 are antitone. -/
private lemma logWeight_antitone491 :
    Antitone (fun n : ℕ => 1 / Real.log ((max n 2 : ℕ) : ℝ)) := by
  intro m n hmn
  have h2 : (2 : ℝ) ≤ ((max m 2 : ℕ) : ℝ) := by exact_mod_cast le_max_right m 2
  have hle : ((max m 2 : ℕ) : ℝ) ≤ ((max n 2 : ℕ) : ℝ) := by
    exact_mod_cast max_le_max hmn le_rfl
  have hpos : 0 < Real.log ((max m 2 : ℕ) : ℝ) := Real.log_pos (by linarith)
  exact one_div_le_one_div_of_le hpos (Real.log_le_log (by linarith) hle)

/-- The weights one over ln of max n 2 are nonnegative. -/
private lemma logWeight_nonneg491 (n : ℕ) : 0 ≤ 1 / Real.log ((max n 2 : ℕ) : ℝ) := by
  have h2 : (2 : ℝ) ≤ ((max n 2 : ℕ) : ℝ) := by exact_mod_cast le_max_right n 2
  exact le_of_lt (one_div_pos.mpr (Real.log_pos (by linarith)))

/-- The damped terms are continuous in the frequency. -/
private lemma term_continuous491 (N n : ℕ) : Continuous (fun β : ℝ =>
    (Real.exp (-(n / N)) : ℂ) *
      (LeanLab.PNTPort.Gallagher.lam1 n * LeanLab.PNTPort.LargeSieve.e (n * β))) := by
  unfold LeanLab.PNTPort.LargeSieve.e
  fun_prop

/-- Abstract step: weights with total mass w 0 against integrals all at most B. -/
private lemma abel_bracket491 (w : ℕ → ℝ) (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n)
    (I : ℕ → ℝ) (J B : ℝ) (hI : ∀ n, I n ≤ B) (hJ : J ≤ B) (M : ℕ) :
    (∑ n ∈ range M, (w n - w (n + 1)) * I n) + w M * J ≤ w 0 * B := by
  have h1 : ∑ n ∈ range M, (w n - w (n + 1)) * I n ≤
      ∑ n ∈ range M, (w n - w (n + 1)) * B :=
    sum_le_sum fun n _ =>
      mul_le_mul_of_nonneg_left (hI n) (sub_nonneg.mpr (hw (Nat.le_succ n)))
  have h2 : w M * J ≤ w M * B := mul_le_mul_of_nonneg_left hJ (hw0 M)
  have h3 : ∑ n ∈ range M, (w n - w (n + 1)) * B + w M * B = w 0 * B := by
    rw [← sum_mul, sum_range_sub']; ring
  linarith

/-- Not in P0093. Formalizer's replacement for the Lemma 2 step of page 160
equation 6.1 and for the unargued step to page 161 equation 6.3.
Under the Riemann hypothesis the damped series with coefficients von Mangoldt
minus one, weighted by one over ln n, has square integral over the arc of radius
one over 2 L at most the short interval mean square bound, uniformly in the
truncation. Inputs: PNTPort.Selberg.weighted_mean_b, the mean square without the
logarithmic weights, conditional on the Riemann hypothesis, and
PNTPort.Selberg.abel_cs_integral, partial summation with Cauchy-Schwarz. The
constant is the one of weighted_mean_b divided by the square of ln 2. -/
private theorem lam_log_mean_square491 (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N L M : ℕ, 1 ≤ L → L ≤ N →
    ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)),
        ‖∑ n ∈ range M, ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) *
            (LeanLab.PNTPort.Gallagher.lam1 n * LeanLab.PNTPort.LargeSieve.e (n * β)))‖ ^ 2 ≤
      C * (N * (Real.log (N / L) + 3) ^ 2 / L +
        N * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2 +
        L * (Real.log N + 1) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := LeanLab.PNTPort.Selberg.weighted_mean_b hRH
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C / (Real.log 2) ^ 2, by positivity, fun N L M hL hLN => ?_⟩
  have hξ : (0 : ℝ) ≤ 1 / (2 * L) := by positivity
  have habel := LeanLab.PNTPort.Selberg.abel_cs_integral
    (fun (n : ℕ) (β : ℝ) => (Real.exp (-(n / N)) : ℂ) *
      (LeanLab.PNTPort.Gallagher.lam1 n * LeanLab.PNTPort.LargeSieve.e (n * β)))
    (term_continuous491 N) (fun n : ℕ => 1 / Real.log ((max n 2 : ℕ) : ℝ))
    logWeight_antitone491 logWeight_nonneg491 M hξ
  have hbr := abel_bracket491 (fun n : ℕ => 1 / Real.log ((max n 2 : ℕ) : ℝ))
    logWeight_antitone491 logWeight_nonneg491 _ _ _
    (fun n => hb N L (n + 1) hL hLN) (hb N L M hL hLN) M
  have hw0 : (0 : ℝ) ≤ 1 / Real.log ((max 0 2 : ℕ) : ℝ) := logWeight_nonneg491 0
  have hw0e : 1 / Real.log ((max 0 2 : ℕ) : ℝ) = 1 / Real.log 2 := by norm_num
  refine (habel.trans (mul_le_mul_of_nonneg_left hbr hw0)).trans (le_of_eq ?_)
  simp only [hw0e]
  field_simp



/-- P0093 page 159 passes from the logarithm of L to the prime series without
mentioning the proper prime powers; this is the formalizer's filling. The weight of a
natural number in the logarithm of zeta minus its weight in the prime series is
one over k at a proper prime power p to the k and zero elsewhere, so it is
nonnegative. -/
private theorem proper_power_weight_nonneg491 (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0) := by
  by_cases hp : n.Prime
  · have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    simp only [hp, ↓reduceIte]
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp, div_self hl, sub_self]
  · simp only [hp, ↓reduceIte, sub_zero]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n)

private lemma weight_le_one491 (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0) ≤ 1 := by
  have h1 : ArithmeticFunction.vonMangoldt n / Real.log n ≤ 1 :=
    div_le_one_of_le₀ ArithmeticFunction.vonMangoldt_le_log (Real.log_natCast_nonneg n)
  have h2 : (0 : ℝ) ≤ (if n.Prime then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  linarith

private lemma weight_ne_zero491 (n : ℕ)
    (h : ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0) ≠ 0) :
    ∃ a k : ℕ, (a + 2) ^ (k + 2) = n := by
  by_cases hp : n.Prime
  · exfalso
    apply h
    have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    simp only [hp, ↓reduceIte]
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp, div_self hl, sub_self]
  · have hL : ArithmeticFunction.vonMangoldt n ≠ 0 := by
      intro h0
      apply h
      simp [h0, hp]
    rw [Ne, ArithmeticFunction.vonMangoldt_eq_zero_iff, not_not] at hL
    obtain ⟨p, k, hpp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hL
    have hk2 : 2 ≤ k := by
      by_contra hk'
      have : k = 1 := by omega
      subst this
      exact hp (by simpa using hpp)
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hpp.two_le
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk2
    exact ⟨a, j, rfl⟩

private lemma sum_split491 (f : ℕ → ℝ) (hf : ∀ x, 0 ≤ f x) (L M : ℕ) :
    ∑ x ∈ range M, f x ≤ ∑ x ∈ range L, f x + ∑ j ∈ range M, f (L + j) := by
  rw [← Finset.sum_range_add]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun x _ _ => hf x)

private lemma exp_neg_le_inv491 (t : ℝ) (ht : 0 < t) : Real.exp (-t) ≤ 1 / t := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ ht (by linarith [Real.add_one_le_exp t])

private lemma tele491 (m : ℕ) (hm : 1 ≤ m) (K : ℕ) :
    ∑ j ∈ range K, 1 / (((m + 1 + j : ℕ) : ℝ)) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((m : ℝ) + K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hx : (0 : ℝ) < (m : ℝ) + K := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      positivity
    have key : 1 / (((m + 1 + K : ℕ) : ℝ)) ^ 2 ≤ 1 / ((m : ℝ) + K) - 1 / ((m : ℝ) + (K + 1 : ℕ)) := by
      push_cast
      rw [div_sub_div _ _ hx.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

private lemma sumA491 (N M : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ range M, Real.exp (-((a : ℝ) ^ 2 / (2 * N))) ≤ 8 * Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set m := Nat.sqrt N + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hNm : (N : ℝ) ≤ (m : ℝ) ^ 2 := by
    have : N < m ^ 2 := by rw [hm]; exact Nat.lt_succ_sqrt' N
    exact_mod_cast this.le
  have h0 := sum_split491 (fun a : ℕ => Real.exp (-((a : ℝ) ^ 2 / (2 * N))))
    (fun x => (Real.exp_pos _).le) (m + 1) M
  have h1 : ∑ a ∈ range (m + 1), Real.exp (-((a : ℝ) ^ 2 / (2 * N))) ≤ (m : ℝ) + 1 := by
    calc ∑ a ∈ range (m + 1), Real.exp (-((a : ℝ) ^ 2 / (2 * N)))
        ≤ ∑ a ∈ range (m + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a _
          rw [Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ (a : ℝ) ^ 2 / (2 * N) := by positivity
          linarith
      _ = (m : ℝ) + 1 := by simp
  have h2 : ∑ j ∈ range M, Real.exp (-((((m + 1 + j : ℕ) : ℝ)) ^ 2 / (2 * N))) ≤ 2 * (m : ℝ) := by
    calc ∑ j ∈ range M, Real.exp (-((((m + 1 + j : ℕ) : ℝ)) ^ 2 / (2 * N)))
        ≤ ∑ j ∈ range M, 2 * (m : ℝ) ^ 2 * (1 / (((m + 1 + j : ℕ) : ℝ)) ^ 2) := by
          apply Finset.sum_le_sum
          intro j _
          have hpos : (0 : ℝ) < (((m + 1 + j : ℕ) : ℝ)) ^ 2 := by
            have : (0 : ℝ) < ((m + 1 + j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + 1 + j)
            positivity
          refine (exp_neg_le_inv491 _ (by positivity)).trans ?_
          rw [one_div_div, mul_one_div]
          apply div_le_div_of_nonneg_right _ hpos.le
          linarith
      _ = 2 * (m : ℝ) ^ 2 * ∑ j ∈ range M, 1 / (((m + 1 + j : ℕ) : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ 2 * (m : ℝ) ^ 2 * (1 / (m : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := tele491 m hm1 M
          have h3 : (0 : ℝ) ≤ 1 / ((m : ℝ) + M) := by positivity
          linarith
      _ = 2 * (m : ℝ) := by field_simp
  have hs : (m : ℝ) ≤ 2 * Real.sqrt N := by
    have ha : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
    have hb : (1 : ℝ) ≤ Real.sqrt N := by
      rw [Real.one_le_sqrt]; exact_mod_cast hN
    rw [hm]; push_cast; linarith
  linarith

private lemma sumB491 (N M : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ range M, Real.exp (-((2 : ℝ) ^ k / (2 * N))) ≤ 5 * (Real.log N + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set L := Nat.log 2 N + 1 with hL
  have hNL : (N : ℝ) ≤ (2 : ℝ) ^ L := by
    have : N < 2 ^ L := by rw [hL]; exact Nat.lt_pow_succ_log_self (by norm_num) N
    exact_mod_cast this.le
  have h0 := sum_split491 (fun k : ℕ => Real.exp (-((2 : ℝ) ^ k / (2 * N))))
    (fun x => (Real.exp_pos _).le) L M
  have h1 : ∑ k ∈ range L, Real.exp (-((2 : ℝ) ^ k / (2 * N))) ≤ (L : ℝ) := by
    calc ∑ k ∈ range L, Real.exp (-((2 : ℝ) ^ k / (2 * N)))
        ≤ ∑ k ∈ range L, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a _
          rw [Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ (2 : ℝ) ^ a / (2 * N) := by positivity
          linarith
      _ = (L : ℝ) := by simp
  have h2 : ∑ j ∈ range M, Real.exp (-((2 : ℝ) ^ (L + j) / (2 * N))) ≤ 4 := by
    calc ∑ j ∈ range M, Real.exp (-((2 : ℝ) ^ (L + j) / (2 * N)))
        ≤ ∑ j ∈ range M, 2 * (1 / 2 : ℝ) ^ j := by
          apply Finset.sum_le_sum
          intro j _
          refine (exp_neg_le_inv491 _ (by positivity)).trans ?_
          rw [one_div_div, one_div_pow, mul_one_div, pow_add,
            div_le_div_iff₀ (by positivity) (by positivity)]
          have : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
          nlinarith
      _ = 2 * ∑ j ∈ range M, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
      _ ≤ 2 * 2 := by
          apply mul_le_mul_of_nonneg_left (sum_geometric_two_le M) (by norm_num)
      _ = 4 := by norm_num
  have hlog : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * Real.log N := by
    have hp : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have h3 := Real.log_le_log (by positivity) hp
    rw [Real.log_pow] at h3
    have h4 := Real.log_two_gt_d9
    have h5 : (0 : ℝ) ≤ (Nat.log 2 N : ℕ) := by positivity
    nlinarith
  have hLR : (L : ℝ) = (Nat.log 2 N : ℕ) + 1 := by rw [hL]; push_cast; ring
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  linarith

private lemma pair_bound491 (N a k : ℕ) (hN : 1 ≤ N) :
    Real.exp (-((((a + 2) ^ (k + 2) : ℕ) : ℝ) / N)) ≤
      Real.exp (-((a : ℝ) ^ 2 / (2 * N))) * Real.exp (-((2 : ℝ) ^ k / (2 * N))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.exp_add, Real.exp_le_exp]
  have ha : a ^ 2 ≤ (a + 2) ^ (k + 2) :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hk : 2 ^ k ≤ (a + 2) ^ (k + 2) :=
    (Nat.pow_le_pow_right (by omega) (by omega : k ≤ k + 2)).trans
      (Nat.pow_le_pow_left (by omega) _)
  have ha' : (a : ℝ) ^ 2 ≤ (((a + 2) ^ (k + 2) : ℕ) : ℝ) := by exact_mod_cast ha
  have hk' : (2 : ℝ) ^ k ≤ (((a + 2) ^ (k + 2) : ℕ) : ℝ) := by exact_mod_cast hk
  have e : -((a : ℝ) ^ 2 / (2 * N)) + -((2 : ℝ) ^ k / (2 * N)) =
      -((((a : ℝ) ^ 2 + (2 : ℝ) ^ k) / 2) / N) := by field_simp; ring
  rw [e, neg_le_neg_iff]
  apply div_le_div_of_nonneg_right _ hN0.le
  linarith

/-- P0093 page 159 passes from the logarithm of L to the prime series without
mentioning the proper prime powers; this elementary bound is the formalizer's
filling. The damped sum of
the proper prime power weights is at most a constant times the square root of N
times ln N plus one, uniformly in the truncation. -/
private theorem proper_power_damped491 : ∃ C : ℝ, 0 ≤ C ∧ ∀ N M : ℕ, 1 ≤ N →
    ∑ n ∈ range M, Real.exp (-(n / N : ℝ)) *
      (ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0)) ≤
      C * Real.sqrt N * (Real.log N + 1) := by
  refine ⟨40, by norm_num, fun N M hN => ?_⟩
  have h1 : ∀ n ∈ range M, Real.exp (-(n / N : ℝ)) *
      (ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0)) ≤
      ∑ p ∈ range M ×ˢ range M,
        (if (p.1 + 2) ^ (p.2 + 2) = n then Real.exp (-(n / N : ℝ)) else 0) := by
    intro n hn
    have hnM : n < M := Finset.mem_range.1 hn
    have hnn : ∀ q ∈ range M ×ˢ range M, (0 : ℝ) ≤
        (if (q.1 + 2) ^ (q.2 + 2) = n then Real.exp (-(n / N : ℝ)) else 0) := by
      intro q _
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    by_cases h0 : ArithmeticFunction.vonMangoldt n / Real.log n -
        (if n.Prime then (1 : ℝ) else 0) = 0
    · rw [h0, mul_zero]
      exact Finset.sum_nonneg hnn
    · obtain ⟨a, k, hak⟩ := weight_ne_zero491 n h0
      have ha : a + 2 ≤ (a + 2) ^ (k + 2) := Nat.le_self_pow (by omega) _
      have hk : k + 2 < (a + 2) ^ (k + 2) :=
        (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left (by omega) _)
      have hmem : (a, k) ∈ range M ×ˢ range M := by
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        constructor <;> simp only <;> omega
      calc Real.exp (-(n / N : ℝ)) *
            (ArithmeticFunction.vonMangoldt n / Real.log n - (if n.Prime then (1 : ℝ) else 0))
          ≤ Real.exp (-(n / N : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left (weight_le_one491 n) (Real.exp_pos _).le
        _ = (if (((a, k) : ℕ × ℕ).1 + 2) ^ (((a, k) : ℕ × ℕ).2 + 2) = n
              then Real.exp (-(n / N : ℝ)) else 0) := by simp [hak]
        _ ≤ _ := Finset.single_le_sum hnn hmem
  have h2 : ∑ n ∈ range M, ∑ p ∈ range M ×ˢ range M,
        (if (p.1 + 2) ^ (p.2 + 2) = n then Real.exp (-(n / N : ℝ)) else 0) ≤
      ∑ p ∈ range M ×ˢ range M,
        Real.exp (-((((p.1 + 2) ^ (p.2 + 2) : ℕ) : ℝ) / N)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro p _
    rw [Finset.sum_ite_eq]
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have h3 : ∑ p ∈ range M ×ˢ range M,
        Real.exp (-((((p.1 + 2) ^ (p.2 + 2) : ℕ) : ℝ) / N)) ≤
      (∑ a ∈ range M, Real.exp (-((a : ℝ) ^ 2 / (2 * N)))) *
        ∑ k ∈ range M, Real.exp (-((2 : ℝ) ^ k / (2 * N))) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    apply Finset.sum_le_sum
    intro p _
    exact pair_bound491 N p.1 p.2 hN
  have hA := sumA491 N M hN
  have hB := sumB491 N M hN
  have hBn : (0 : ℝ) ≤ ∑ k ∈ range M, Real.exp (-((2 : ℝ) ^ k / (2 * N))) :=
    Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have h4 : (∑ a ∈ range M, Real.exp (-((a : ℝ) ^ 2 / (2 * N)))) *
        ∑ k ∈ range M, Real.exp (-((2 : ℝ) ^ k / (2 * N))) ≤
      (8 * Real.sqrt N) * (5 * (Real.log N + 1)) :=
    mul_le_mul hA hB hBn (by positivity)
  calc _ ≤ _ := Finset.sum_le_sum h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ ≤ _ := h4
    _ = 40 * Real.sqrt N * (Real.log N + 1) := by ring




/-- Damping: the natural prime coefficients are absolutely summable at every
positive scale (ported form of `prime_coefficients_summable552`, with the
coefficient written out because a new definition is not allowed). -/
private theorem prime_coefficients_summable520p (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun k : ℕ => (if k.Prime then ((Real.exp (-(k : ℝ) / N) : ℝ) : ℂ) else 0)) := by
  apply Summable.of_norm_bounded (damping_summable111_up111 N hN)
  intro k
  by_cases hk : k.Prime
  · simp only [if_pos hk, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), le_refl]
  · simp [if_neg hk, (Real.exp_pos _).le]

/-- Zero extension from the prime subtype gives the natural negative Fourier
series (ported form of `prime_series_nat552`). -/
private theorem prime_series_nat520p (N : ℕ) (z : ℝ) :
    primeFourier111_up111 N z = ∑' k : ℕ,
      (if k.Prime then ((Real.exp (-(k : ℝ) / N) : ℝ) : ℂ) else 0) *
        Complex.exp ((-(2 * Real.pi * z * k) : ℝ) * Complex.I) := by
  classical
  let f : ℕ → ℂ := fun k =>
    (if k.Prime then ((Real.exp (-(k : ℝ) / N) : ℝ) : ℂ) else 0) *
      Complex.exp ((-(2 * Real.pi * z * k) : ℝ) * Complex.I)
  have hsupp : Function.support f ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro k hk
    by_cases hp : k.Prime
    · exact ⟨⟨k, hp⟩, rfl⟩
    · exact absurd (by simp [f, hp] : f k = 0) hk
  calc
    _ = ∑' p : Nat.Primes, f (p : ℕ) := by
      unfold primeFourier111_up111
      apply tsum_congr
      intro p
      simp [f, p.property]
    _ = ∑' k : ℕ, f k := Nat.Primes.coe_nat_injective.tsum_eq hsupp
    _ = _ := rfl



/-- The phase of the paper in the convention of the large sieve port. -/
private lemma phase_eq_partial491 (n : ℕ) (z : ℝ) :
    Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I) =
      LeanLab.PNTPort.LargeSieve.e (n * (-z)) := by
  unfold LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring

/-- Termwise decomposition of the coefficient: the von Mangoldt part, a correction
at zero and one, and the proper prime power part. -/
private lemma coeff_partial491 (N n : ℕ) :
    (if n.Prime then ((Real.exp (-(n : ℝ) / N) : ℝ) : ℂ) else 0) - logCoefficient520 N n =
      ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) * LeanLab.PNTPort.Gallagher.lam1 n) +
        (if n < 2 then
          (((1 / Real.log ((max n 2 : ℕ) : ℝ)) * Real.exp (-(n / N)) : ℝ) : ℂ) else 0) -
        ((Real.exp (-(n / N : ℝ)) * (ArithmeticFunction.vonMangoldt n / Real.log n -
          (if n.Prime then (1 : ℝ) else 0)) : ℝ) : ℂ) := by
  unfold logCoefficient520 LeanLab.PNTPort.Gallagher.lam1
  simp only [neg_div]
  by_cases h2 : 2 ≤ n
  · have hm : max n 2 = n := max_eq_left h2
    have hlt : ¬ n < 2 := by omega
    rw [hm]
    by_cases hp : n.Prime
    · simp only [hp, h2, hlt, ↓reduceIte]
      push_cast
      ring
    · simp only [hp, h2, hlt, ↓reduceIte]
      push_cast
      ring
  · have hnp : ¬ n.Prime := fun hp => h2 hp.two_le
    have hlt : n < 2 := by omega
    have hΛ : ArithmeticFunction.vonMangoldt n = 0 := by
      interval_cases n <;> simp
    simp only [hnp, h2, hlt, ↓reduceIte, hΛ]
    push_cast
    ring

/-- The correction at zero and one has size at most two. -/
private lemma corr_le_partial491 (N n : ℕ) :
    ‖(if n < 2 then
      (((1 / Real.log ((max n 2 : ℕ) : ℝ)) * Real.exp (-(n / N)) : ℝ) : ℂ) else 0)‖ ≤
      (if n < 2 then (2 : ℝ) else 0) := by
  by_cases h : n < 2
  · have hm : max n 2 = 2 := max_eq_right h.le
    simp only [h, ↓reduceIte, hm]
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      linarith
    have hl' : 1 / Real.log ((2 : ℕ) : ℝ) ≤ 2 := by
      push_cast
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hl0 : 0 ≤ 1 / Real.log ((2 : ℕ) : ℝ) := by
      push_cast
      have : 0 < Real.log 2 := by linarith
      positivity
    have he : Real.exp (-((n : ℝ) / N)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (n : ℝ) / N := by positivity
      linarith
    rw [abs_of_nonneg (mul_nonneg hl0 (Real.exp_pos _).le)]
    nlinarith [Real.exp_pos (-((n : ℝ) / N))]
  · simp [h]

private lemma corr_sum_partial491 (M : ℕ) :
    ∑ n ∈ range M, (if n < 2 then (2 : ℝ) else 0) ≤ 4 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : ((range M).filter (fun n => n < 2)).card ≤ 2 := by
    calc ((range M).filter (fun n => n < 2)).card ≤ (range 2).card :=
          Finset.card_le_card (fun x hx => by
            rw [Finset.mem_filter] at hx
            exact Finset.mem_range.mpr hx.2)
      _ = 2 := Finset.card_range 2
  have : (((range M).filter (fun n => n < 2)).card : ℝ) ≤ 2 := by exact_mod_cast hc
  linarith

/-- Pointwise bound for the square of the truncated difference. -/
private lemma pointwise_partial491 (N M : ℕ) (P : ℝ)
    (hP : ∑ n ∈ range M, Real.exp (-(n / N : ℝ)) *
      (ArithmeticFunction.vonMangoldt n / Real.log n -
        (if n.Prime then (1 : ℝ) else 0)) ≤ P) (z : ℝ) :
    ‖∑ n ∈ range M, ((if n.Prime then ((Real.exp (-(n : ℝ) / N) : ℝ) : ℂ) else 0) - logCoefficient520 N n) *
        Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2 ≤
      3 * ‖∑ n ∈ range M, ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) *
            (LeanLab.PNTPort.Gallagher.lam1 n *
              LeanLab.PNTPort.LargeSieve.e (n * (-z))))‖ ^ 2 + (48 + 3 * P ^ 2) := by
  have hsplit : ∑ n ∈ range M, ((if n.Prime then ((Real.exp (-(n : ℝ) / N) : ℝ) : ℂ) else 0) - logCoefficient520 N n) *
        Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I) =
      (∑ n ∈ range M, ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) *
            (LeanLab.PNTPort.Gallagher.lam1 n *
              LeanLab.PNTPort.LargeSieve.e (n * (-z))))) +
        (∑ n ∈ range M, (if n < 2 then
          (((1 / Real.log ((max n 2 : ℕ) : ℝ)) * Real.exp (-(n / N)) : ℝ) : ℂ) else 0) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z))) -
        ∑ n ∈ range M, ((Real.exp (-(n / N : ℝ)) *
          (ArithmeticFunction.vonMangoldt n / Real.log n -
            (if n.Prime then (1 : ℝ) else 0)) : ℝ) : ℂ) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [phase_eq_partial491, coeff_partial491]
    ring
  have hc : ‖∑ n ∈ range M, (if n < 2 then
          (((1 / Real.log ((max n 2 : ℕ) : ℝ)) * Real.exp (-(n / N)) : ℝ) : ℂ) else 0) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z))‖ ≤ 4 := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun n _ => ?_)).trans
      (corr_sum_partial491 M))
    rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one]
    exact corr_le_partial491 N n
  have hg : ‖∑ n ∈ range M, ((Real.exp (-(n / N : ℝ)) *
          (ArithmeticFunction.vonMangoldt n / Real.log n -
            (if n.Prime then (1 : ℝ) else 0)) : ℝ) : ℂ) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z))‖ ≤ P := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun n _ => ?_)).trans hP)
    rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (proper_power_weight_nonneg491 n))]
  rw [hsplit]
  set a := ∑ n ∈ range M, ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) *
            (LeanLab.PNTPort.Gallagher.lam1 n *
              LeanLab.PNTPort.LargeSieve.e (n * (-z))))
  set c := ∑ n ∈ range M, (if n < 2 then
          (((1 / Real.log ((max n 2 : ℕ) : ℝ)) * Real.exp (-(n / N)) : ℝ) : ℂ) else 0) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z))
  set g := ∑ n ∈ range M, ((Real.exp (-(n / N : ℝ)) *
          (ArithmeticFunction.vonMangoldt n / Real.log n -
            (if n.Prime then (1 : ℝ) else 0)) : ℝ) : ℂ) *
            LeanLab.PNTPort.LargeSieve.e (n * (-z))
  have h1 : ‖a + c - g‖ ≤ ‖a‖ + 4 + P :=
    (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (by linarith)) hg)
  have h2 : ‖a + c - g‖ ^ 2 ≤ (‖a‖ + 4 + P) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a‖ - 4), sq_nonneg (‖a‖ - P), sq_nonneg (P - 4)]

private lemma cont_A_partial491 (N M : ℕ) :
    Continuous (fun β : ℝ => ‖∑ n ∈ range M, ((1 / Real.log ((max n 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.exp (-(n / N)) : ℂ) *
            (LeanLab.PNTPort.Gallagher.lam1 n *
              LeanLab.PNTPort.LargeSieve.e (n * β)))‖ ^ 2) := by
  simp only [LeanLab.PNTPort.LargeSieve.e]
  fun_prop

private lemma cont_D_partial491 (N M : ℕ) :
    Continuous (fun z : ℝ => ‖∑ n ∈ range M, ((if n.Prime then ((Real.exp (-(n : ℝ) / N) : ℝ) : ℂ) else 0) - logCoefficient520 N n) *
        Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) := by
  fun_prop

/-- Integration of a pointwise bound against a reflected majorant. -/
private lemma integral_abs_partial491 (D A : ℝ → ℝ) (hD : Continuous D) (hA : Continuous A)
    (K δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ z, D z ≤ 3 * A (-z) + K) :
    (∫ z in -δ..δ, D z) ≤ 3 * (∫ β in -δ..δ, A β) + 2 * δ * K := by
  have hA' : Continuous (fun z : ℝ => A (-z)) := hA.comp continuous_neg
  have hrefl : (∫ z in -δ..δ, A (-z)) = ∫ β in -δ..δ, A β := by
    have := intervalIntegral.integral_comp_neg (a := -δ) (b := δ) A
    simpa only [neg_neg] using this
  calc (∫ z in -δ..δ, D z) ≤ ∫ z in -δ..δ, (3 * A (-z) + K) :=
        intervalIntegral.integral_mono_on (by linarith) (hD.intervalIntegrable _ _)
          (((hA'.const_mul 3).add continuous_const).intervalIntegrable _ _) (fun z _ => h z)
    _ = 3 * (∫ β in -δ..δ, A β) + 2 * δ * K := by
        rw [intervalIntegral.integral_add ((hA'.const_mul 3).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
          hrefl, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring

/-- Widening a symmetric interval increases the integral of a nonnegative function. -/
private lemma widen_partial491 (A : ℝ → ℝ) (hA : Continuous A) (h0 : ∀ x, 0 ≤ A x)
    (δ δ' : ℝ) (hδ : 0 ≤ δ) (h : δ ≤ δ') :
    (∫ β in -δ..δ, A β) ≤ ∫ β in -δ'..δ', A β :=
  intervalIntegral.integral_mono_interval (by linarith) (by linarith) h
    (Filter.Eventually.of_forall h0) (hA.intervalIntegrable _ _)

/-- Scale facts on the arc: q tau is at least two and its square is at most N. -/
private lemma scale_partial491 (N q : ℕ) (hN : 128 < N) (hq : 1 ≤ q)
    (hqQ : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    2 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ∧ ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ^ 2 ≤ N := by
  have hn : (128 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hτ2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
    have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128) hn
      (by norm_num : (0 : ℝ) ≤ 1 / 7)
    have he : (128 : ℝ) ^ (1 / 7 : ℝ) = 2 := by
      rw [show (128 : ℝ) = 2 ^ (7 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [he] at hh
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨by nlinarith, ?_⟩
  have h10 : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h7 : (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hq4 : 0 < (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hR : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    have : (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hN0]; norm_num
    rw [this]
    exact mul_le_mul (hqQ.trans h10) h7 (by positivity) hq4.le
  have hsq : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = N := by
    rw [sq, ← Real.rpow_add hN0]; norm_num
  calc ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ^ 2 ≤ ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hR 2
    _ = N := hsq

/-- Real arithmetic collecting the three terms of the mean square bound, the
correction and the proper prime power part. -/
private lemma arith_partial491 (N R L ℓ lg s Ca Cp sN : ℝ) (hN : 1 ≤ N) (hR : 2 ≤ R)
    (hRN : R ^ 2 ≤ N) (hL4 : R ≤ 4 * L) (hL2 : 2 * L ≤ R) (hL1 : 1 ≤ L) (hℓ : 1 ≤ ℓ)
    (hlg0 : 0 ≤ lg) (hlg : lg ≤ ℓ) (hs : 1 ≤ s) (hCa : 0 ≤ Ca) (hsN : sN ^ 2 = N) :
    3 * (Ca * (N * (lg + 3) ^ 2 / L + N * ((ℓ + 2) ^ 2 / s) / L ^ 2 + L * (ℓ + 1) ^ 2)) +
        2 * (1 / R) * (48 + 3 * (Cp * sN * (ℓ + 1)) ^ 2) ≤
      (306 * Ca + 96 + 24 * Cp ^ 2) * N / R * ℓ ^ 13 := by
  have hR0 : 0 < R := by linarith
  have hL0 : 0 < L := by linarith
  have hN0 : 0 < N := by linarith
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = N * ℓ ^ 2 / R := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hX : X * R = N * ℓ ^ 2 := by rw [hXdef]; field_simp
  have a2 : X * R ≤ X * (4 * L) := mul_le_mul_of_nonneg_left hL4 hX0
  have hT1 : N * (lg + 3) ^ 2 / L ≤ 64 * X := by
    rw [div_le_iff₀ hL0]
    have h : (lg + 3) ^ 2 ≤ 16 * ℓ ^ 2 := by nlinarith
    have a1 : N * (lg + 3) ^ 2 ≤ N * (16 * ℓ ^ 2) := mul_le_mul_of_nonneg_left h hN0.le
    linarith
  have hT2 : N * ((ℓ + 2) ^ 2 / s) / L ^ 2 ≤ 36 * X := by
    have b0 : (ℓ + 2) ^ 2 / s ≤ 9 * ℓ ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have h1 : (ℓ + 2) ^ 2 ≤ 9 * ℓ ^ 2 := by nlinarith
      have h2 : 9 * ℓ ^ 2 ≤ 9 * ℓ ^ 2 * s := le_mul_of_one_le_right (by positivity) hs
      linarith
    rw [div_le_iff₀ (by positivity)]
    have b1 : N * ((ℓ + 2) ^ 2 / s) ≤ N * (9 * ℓ ^ 2) := mul_le_mul_of_nonneg_left b0 hN0.le
    have b2 : L ≤ L ^ 2 := by nlinarith
    have b3 : X * L ≤ X * L ^ 2 := mul_le_mul_of_nonneg_left b2 hX0
    linarith
  have hT3 : L * (ℓ + 1) ^ 2 ≤ 2 * X := by
    have h : (ℓ + 1) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
    have c1 : L * (ℓ + 1) ^ 2 ≤ L * (4 * ℓ ^ 2) := mul_le_mul_of_nonneg_left h hL0.le
    have c2 : L * (4 * ℓ ^ 2) ≤ R / 2 * (4 * ℓ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have c3 : R * ℓ ^ 2 ≤ X := by
      rw [hXdef, le_div_iff₀ hR0]
      have : R ^ 2 * ℓ ^ 2 ≤ N * ℓ ^ 2 := mul_le_mul_of_nonneg_right hRN (by positivity)
      linarith
    linarith
  have hT4 : 2 * (1 / R) * (48 + 3 * (Cp * sN * (ℓ + 1)) ^ 2) ≤ (96 + 24 * Cp ^ 2) * X := by
    have e1 : (Cp * sN * (ℓ + 1)) ^ 2 = Cp ^ 2 * (N * (ℓ + 1) ^ 2) := by rw [← hsN]; ring
    have h : (ℓ + 1) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
    have e2 : Cp ^ 2 * (N * (ℓ + 1) ^ 2) ≤ Cp ^ 2 * (N * (4 * ℓ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hN0.le) (sq_nonneg _)
    have e3 : 1 ≤ N * ℓ ^ 2 := by nlinarith
    have e4 : 48 + 3 * (Cp * sN * (ℓ + 1)) ^ 2 ≤ (48 + 12 * Cp ^ 2) * (X * R) := by
      rw [hX, e1]
      linarith
    have e5 : 2 * (1 / R) * (48 + 3 * (Cp * sN * (ℓ + 1)) ^ 2) ≤
        2 * (1 / R) * ((48 + 12 * Cp ^ 2) * (X * R)) :=
      mul_le_mul_of_nonneg_left e4 (by positivity)
    have e6 : 2 * (1 / R) * ((48 + 12 * Cp ^ 2) * (X * R)) = (96 + 24 * Cp ^ 2) * X := by
      field_simp
      ring
    linarith
  have hX13 : X ≤ N / R * ℓ ^ 13 := by
    rw [hXdef, show N * ℓ ^ 2 / R = N / R * ℓ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hℓ (by norm_num)) (by positivity)
  have d1 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hT1 hT2) hT3) hCa
  have d3 : (306 * Ca + 96 + 24 * Cp ^ 2) * X ≤
      (306 * Ca + 96 + 24 * Cp ^ 2) * (N / R * ℓ ^ 13) :=
    mul_le_mul_of_nonneg_left hX13 (by positivity)
  have d4 : (306 * Ca + 96 + 24 * Cp ^ 2) * N / R * ℓ ^ 13 =
      (306 * Ca + 96 + 24 * Cp ^ 2) * (N / R * ℓ ^ 13) := by ring
  rw [d4]
  linarith

/-- P0093 page 160 equation 6.1 with page 161 equation 6.3, on the arc, for
every truncation of the difference of the prime series and the model series S one.
Not a statement of the print; formalizer's route, see prime_arc_mean_square491.
Inputs: the mean square lam_log_mean_square491 of the von Mangoldt series with
weights one over ln n, which rests on the PNTPort.Selberg short interval mean
square under the Riemann hypothesis, in the conventions LargeSieve.e and
Gallagher.lam1 of PNTPort, and the proper prime power bound
proper_power_damped491. -/
private theorem prime_arc_partial491 (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ M : ℕ,
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖∑ n ∈ range M, ((if n.Prime then ((Real.exp (-(n : ℝ) / N) : ℝ) : ℂ) else 0) - logCoefficient520 N n) *
            Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) ≤
          C * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 := by
  obtain ⟨Ca, hCa, hA⟩ := lam_log_mean_square491 hRH
  obtain ⟨Cp, hCp, hPw⟩ := proper_power_damped491
  refine ⟨306 * Ca + 96 + 24 * Cp ^ 2, by positivity, 128, ?_⟩
  intro N hN q hq hqQ M
  obtain ⟨hR2, hRN⟩ := scale_partial491 N q hN hq hqQ
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl : 1 ≤ Real.log N := by
    have hN3' : (3 : ℝ) < N := by exact_mod_cast (show 3 < N by omega)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3').le
  set R : ℝ := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hRdef
  have hR0 : 0 < R := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = ⌊R / 2⌋₊ := ⟨_, rfl⟩
  have hLle : (L : ℝ) ≤ R / 2 := by rw [hLdef]; exact Nat.floor_le (by linarith)
  have hLlt : R / 2 < L + 1 := by rw [hLdef]; exact Nat.lt_floor_add_one _
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    exact Nat.le_floor (by push_cast; linarith)
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLN : L ≤ N := by
    have : (L : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hLNr : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hP := hPw N M (by omega)
  have h1 := integral_abs_partial491 _ _ (cont_D_partial491 N M) (cont_A_partial491 N M)
    (48 + 3 * (Cp * Real.sqrt N * (Real.log N + 1)) ^ 2) (1 / R) (by positivity)
    (pointwise_partial491 N M _ hP)
  have h2 := widen_partial491 _ (cont_A_partial491 N M) (fun x => by positivity)
    (1 / R) (1 / (2 * (L : ℝ))) (by positivity)
    (one_div_le_one_div_of_le (by linarith) (by linarith))
  have h3 := hA N L M hL1 hLN
  have h4 := arith_partial491 N R L (Real.log N) (Real.log (N / L)) (Real.sqrt L) Ca Cp
    (Real.sqrt N) hNr hR2 hRN (by linarith) (by linarith) hL1r hl
    (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith))
    (Real.log_le_log (by positivity) (div_le_self (by linarith) hL1r))
    (Real.one_le_sqrt.mpr hL1r) hCa (Real.sq_sqrt (by linarith))
  linarith





/-- P0093 page 154. A unimodular phase does not change the norm of a term. -/
private theorem phase_term_norm491 (c : ℂ) (z : ℝ) (n : ℕ) :
    ‖c * Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ = ‖c‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- P0093 page 154. An absolutely summable coefficient sequence gives a summable
series of negative frequencies. -/
private theorem phase_series_summable491 (c : ℕ → ℂ) (hc : Summable c) (z : ℝ) :
    Summable (fun n : ℕ => c n *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)) := by
  apply Summable.of_norm
  simp only [phase_term_norm491]
  exact hc.norm

/-- P0093 pages 154 and 161. The difference of the prime series S and the model
series S one is the series of the differences of the coefficients. -/
private theorem prime_minus_log_series491 (N : ℕ) (hN : 1 ≤ N) (z : ℝ) :
    primeFourier111_up111 N z - logFourier520 N z =
      ∑' n : ℕ, ((if n.Prime then ((Real.exp (-(n : ℝ) / N) : ℝ) : ℂ) else 0) - logCoefficient520 N n) *
        Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I) := by
  rw [prime_series_nat520p, logFourier520,
    ← (phase_series_summable491 _ (prime_coefficients_summable520p N hN) z).tsum_sub
      (phase_series_summable491 _ (logCoefficient_summable520 N hN) z)]
  simp only [sub_mul]

/-- P0093 page 160 equation 6.1 with page 161 equation 6.3, on the arc,
for the full prime series. Under the extended Riemann hypothesis the prime
series S of page 154 differs from the model series S one, with weights one over
ln m, by a function whose square integral over the arc of radius one over q tau
is at most a constant times N ln to the 13 of N over q tau. Here q only fixes the
radius. This statement is not printed. It stands in for the print's use of the
page 159 display with Lemma 2 in equation 6.1 and for the step to equation 6.3,
for which the print gives no argument. The proof is the formalizer's and does not
use the Mellin display or Lemma 2: Gallagher's lemma and the short interval mean
square under the Riemann hypothesis from PNTPort, partial summation, an elementary
prime power bound and a limit. The exponent 13 is slack; the argument gives 2.
Inputs: `rh_of_GRH_p`, the truncated estimate
`prime_arc_partial491`, which rests on the PNTPort inputs of its own file, and the
passage to the limit `series_arc_limit491`. No PNTPort result is used directly here. -/
private theorem prime_arc_mean_square491 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖primeFourier111_up111 N z - logFourier520 N z‖ ^ 2) ≤
          C * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 := by
  obtain ⟨C, hC, N0, h⟩ := prime_arc_partial491 (rh_of_GRH_p hG)
  refine ⟨C, hC, N0, fun N hN q hq hqN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  simp only [prime_minus_log_series491 N hN1]
  refine series_arc_limit491 _ ?_ _ _ ?_ (h N hN q hq hqN)
  · exact ((prime_coefficients_summable520p N hN1).sub
      (logCoefficient_summable520 N hN1)).norm
  · positivity







/-- P0093 page 160 equation 6.1 with page 161 equation 6.3, for every truncation of
the difference of the prime series and the model series S one, on the arc of radius
one over R for every real R at least two whose square is at most N. Not a statement
of the print; formalizer's route as in prime_arc_mean_square491. The proof is the
body of prime_arc_partial491, which uses its radius only through these two facts. -/
private theorem prime_arc_partial_radius520 (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 128 < N → ∀ R : ℝ, 2 ≤ R → R ^ 2 ≤ (N : ℝ) → ∀ M : ℕ,
      (∫ z in -(1 / R)..(1 / R),
        ‖∑ n ∈ range M, ((if n.Prime then ((Real.exp (-(n : ℝ) / N) : ℝ) : ℂ) else 0) - logCoefficient520 N n) *
          Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) ≤
        C * (N : ℝ) / R * Real.log N ^ 13 := by
  obtain ⟨Ca, hCa, hA⟩ := lam_log_mean_square491 hRH
  obtain ⟨Cp, hCp, hPw⟩ := proper_power_damped491
  refine ⟨306 * Ca + 96 + 24 * Cp ^ 2, by positivity, ?_⟩
  intro N hN R hR2 hRN M
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl : 1 ≤ Real.log N := by
    have hN3' : (3 : ℝ) < N := by exact_mod_cast (show 3 < N by omega)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3').le
  have hR0 : 0 < R := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = ⌊R / 2⌋₊ := ⟨_, rfl⟩
  have hLle : (L : ℝ) ≤ R / 2 := by rw [hLdef]; exact Nat.floor_le (by linarith)
  have hLlt : R / 2 < L + 1 := by rw [hLdef]; exact Nat.lt_floor_add_one _
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    exact Nat.le_floor (by push_cast; linarith)
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLN : L ≤ N := by
    have : (L : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hLNr : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hP := hPw N M (by omega)
  have h1 := integral_abs_partial491 _ _ (cont_D_partial491 N M) (cont_A_partial491 N M)
    (48 + 3 * (Cp * Real.sqrt N * (Real.log N + 1)) ^ 2) (1 / R) (by positivity)
    (pointwise_partial491 N M _ hP)
  have h2 := widen_partial491 _ (cont_A_partial491 N M) (fun x => by positivity)
    (1 / R) (1 / (2 * (L : ℝ))) (by positivity)
    (one_div_le_one_div_of_le (by linarith) (by linarith))
  have h3 := hA N L M hL1 hLN
  have h4 := arith_partial491 N R L (Real.log N) (Real.log (N / L)) (Real.sqrt L) Ca Cp
    (Real.sqrt N) hNr hR2 hRN (by linarith) (by linarith) hL1r hl
    (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith))
    (Real.log_le_log (by positivity) (div_le_self (by linarith) hL1r))
    (Real.one_le_sqrt.mpr hL1r) hCa (Real.sq_sqrt (by linarith))
  linarith

/-- P0093 page 160 equation 6.1 with page 161 equation 6.3, for the full prime series
on the arc of radius one over R, for every real R at least two whose square is at
most N. Not a statement of the print; formalizer's route as in
prime_arc_mean_square491, through the truncated estimate and the passage to the
limit series_arc_limit491. The exponent 13 is slack. -/
private theorem prime_arc_mean_square_radius520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 128 < N → ∀ R : ℝ, 2 ≤ R → R ^ 2 ≤ (N : ℝ) →
      (∫ z in -(1 / R)..(1 / R), ‖primeFourier111_up111 N z - logFourier520 N z‖ ^ 2) ≤
        C * (N : ℝ) / R * Real.log N ^ 13 := by
  obtain ⟨C, hC, h⟩ := prime_arc_partial_radius520 (rh_of_GRH_p hG)
  refine ⟨C, hC, fun N hN R hR2 hRN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  simp only [prime_minus_log_series491 N hN1]
  refine series_arc_limit491 _ ?_ _ _ ?_ (h N hN R hR2 hRN)
  · exact ((prime_coefficients_summable520p N hN1).sub
      (logCoefficient_summable520 N hN1)).norm
  · have : 0 < R := by linarith
    positivity

/-- P0093 page 161 equation 6.3. The model series S one is continuous. -/
private theorem logFourier_continuous_radius520 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (logFourier520 N) := by
  unfold logFourier520
  refine continuous_tsum (u := fun m => ‖logCoefficient520 N m‖) ?_
    (logCoefficient_summable520 N hN).norm ?_
  · intro m
    fun_prop
  · intro m z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- P0093 page 159 before equation 5.1. The removed prime divisor terms of the
principal series have total size at most the modulus. -/
private lemma divisor_terms_le_radius520 (N q : ℕ) (z : ℝ) :
    ‖∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)‖ ≤ q := by
  have hcard : q.primeFactors.card ≤ q := by
    calc q.primeFactors.card ≤ (Icc 1 q).card :=
          Finset.card_le_card (fun p hp => by
            have hp' := Nat.mem_primeFactors.mp hp
            exact Finset.mem_Icc.mpr ⟨hp'.1.one_lt.le,
              Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1⟩)
      _ = q := by simp
  have h1 : ∀ p ∈ q.primeFactors, ‖(Real.exp (-(p : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)‖ ≤ 1 := by
    intro p _
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have : 0 ≤ (p : ℝ) / N := by positivity
    rw [neg_div]
    linarith
  calc _ ≤ ∑ p ∈ q.primeFactors, (1 : ℝ) := (norm_sum_le _ _).trans (Finset.sum_le_sum h1)
    _ = q.primeFactors.card := by simp
    _ ≤ q := by exact_mod_cast hcard

/-- P0093 page 160 equation 6.1 with page 161 equation 6.3, for the principal
character prime series of page 159 on the arc of radius one over R. The principal
series is the prime series with at most q terms of size at most one removed, and q
squared is at most N. Not a statement of the print; formalizer's route as in
prime_arc_mean_square491. The exponent 13 is slack. -/
private theorem principal_arc_mean_square_radius520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 128 < N → ∀ q : ℕ, 1 ≤ q → ((q : ℝ)) ^ 2 ≤ (N : ℝ) →
      ∀ R : ℝ, 2 ≤ R → R ^ 2 ≤ (N : ℝ) →
      (∫ z in -(1 / R)..(1 / R), ‖principalPrime520 N q z - logFourier520 N z‖ ^ 2) ≤
        C * (N : ℝ) / R * Real.log N ^ 13 := by
  obtain ⟨C, hC, h⟩ := prime_arc_mean_square_radius520 hG
  refine ⟨2 * C + 4, by positivity, fun N hN q hq hqN R hR2 hRN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hR0 : 0 < R := by linarith
  have hl : 1 ≤ Real.log N := by
    have hN3' : (3 : ℝ) < N := by exact_mod_cast (show 3 < N by omega)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3').le
  have hl13 : (1 : ℝ) ≤ Real.log N ^ 13 := one_le_pow₀ hl
  have hcP : Continuous (primeFourier111_up111 N) := continuous_prime_fourier111_up111 N hN1
  have hcL := logFourier_continuous_radius520 N hN1
  have hcQ := continuous_principal520 N q hN1
  have hcA : Continuous (fun z : ℝ => ‖primeFourier111_up111 N z - logFourier520 N z‖ ^ 2) := by
    fun_prop
  have hcB : Continuous (fun z : ℝ => ‖principalPrime520 N q z - logFourier520 N z‖ ^ 2) := by
    fun_prop
  have hpt : ∀ z : ℝ, ‖principalPrime520 N q z - logFourier520 N z‖ ^ 2 ≤
      2 * ‖primeFourier111_up111 N z - logFourier520 N z‖ ^ 2 + 2 * (q : ℝ) ^ 2 := by
    intro z
    have hd := divisor_terms_le_radius520 N q z
    have he : principalPrime520 N q z - logFourier520 N z =
        (primeFourier111_up111 N z - logFourier520 N z) -
          ∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I) := by
      show primeFourier111_up111 N z - _ - logFourier520 N z = _
      ring
    rw [he]
    have h1 := norm_sub_le (primeFourier111_up111 N z - logFourier520 N z)
      (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (h1.trans (add_le_add le_rfl hd)) 2
    nlinarith [sq_nonneg (‖primeFourier111_up111 N z - logFourier520 N z‖ - (q : ℝ))]
  have hint : (∫ z in -(1 / R)..(1 / R), ‖principalPrime520 N q z - logFourier520 N z‖ ^ 2) ≤
      2 * (∫ z in -(1 / R)..(1 / R), ‖primeFourier111_up111 N z - logFourier520 N z‖ ^ 2) +
        2 * (1 / R) * (2 * (q : ℝ) ^ 2) := by
    calc _ ≤ ∫ z in -(1 / R)..(1 / R),
          (2 * ‖primeFourier111_up111 N z - logFourier520 N z‖ ^ 2 + 2 * (q : ℝ) ^ 2) :=
        intervalIntegral.integral_mono_on (by have : 0 ≤ 1 / R := by positivity
                                              linarith)
          (hcB.intervalIntegrable _ _)
          (((hcA.const_mul 2).add continuous_const).intervalIntegrable _ _) (fun z _ => hpt z)
      _ = _ := by
        rw [intervalIntegral.integral_add ((hcA.const_mul 2).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  have hmain := h N hN R hR2 hRN
  have hX : (N : ℝ) / R ≤ N / R * Real.log N ^ 13 :=
    le_mul_of_one_le_right (by positivity) hl13
  have hq2 : 2 * (1 / R) * (2 * (q : ℝ) ^ 2) ≤ 4 * (N / R) := by
    have : (q : ℝ) ^ 2 / R ≤ N / R := div_le_div_of_nonneg_right hqN hR0.le
    have e : 2 * (1 / R) * (2 * (q : ℝ) ^ 2) = 4 * ((q : ℝ) ^ 2 / R) := by ring
    rw [e]
    linarith
  have e1 : (2 * C + 4) * (N : ℝ) / R * Real.log N ^ 13 =
      2 * (C * (N : ℝ) / R * Real.log N ^ 13) + 4 * (N / R * Real.log N ^ 13) := by ring
  rw [e1]
  linarith






/-- Parseval over a full period for an absolutely summable series in the
negative natural frequencies. -/
private theorem series_square_mass491 (a : ℕ → ℂ) (ha : Summable a) :
    (∫ α in (0 : ℝ)..1, ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)‖ ^ 2) =
        ∑' n : ℕ, ‖a n‖ ^ 2 := by
  have hf : Continuous (fun α : ℝ => ∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)) := by
    apply continuous_tsum (u := fun n => ‖a n‖)
    · intro n
      fun_prop
    · exact ha.norm
    · intro n α
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
  have hs : IntervalIntegrable (fun α : ℝ => ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)‖ ^ 2) volume 0 1 :=
    (hf.norm.pow 2).intervalIntegrable 0 1
  have hL2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hs.1
  calc
    _ = ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun α => ∑' n : ℕ, a n *
          Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)) i‖ ^ 2 := by
      simpa using (tsum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hL2).symm
    _ = _ := negative_modes_sum111_up111 _ _ (negative_series_coefficient_proved357_up111 a ha)

private theorem logFourier_continuous_mass491 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (logFourier520 N) := by
  unfold logFourier520
  refine continuous_tsum (u := fun m => ‖logCoefficient520 N m‖) ?_
    (logCoefficient_summable520 N hN).norm ?_
  · intro m
    fun_prop
  · intro m z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem logFourier_periodic_mass491 (N : ℕ) :
    Function.Periodic (logFourier520 N) 1 := by
  intro z
  unfold logFourier520
  apply tsum_congr
  intro m
  congr 1
  have h : ((-(2 * Real.pi * (z + 1) * m) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * z * m) : ℝ) : ℂ) * Complex.I +
        ((-(m : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Weights three at frequency two and one from three on have prefix sums
at most the length. -/
private theorem weight_prefix_mass491 (n : ℕ) :
    ∑ i ∈ range n, (if i = 2 then (3 : ℝ) else if 3 ≤ i then 1 else 0) ≤ 1 * (n : ℝ) := by
  have h : ∑ i ∈ range n, (if i = 2 then (3 : ℝ) else if 3 ≤ i then 1 else 0) =
      if n ≤ 2 then 0 else (n : ℝ) := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h2 : k = 2
      · subst h2; norm_num
      · by_cases h3 : 3 ≤ k
        · rw [if_neg (by omega), if_neg h2, if_pos h3, if_neg (by omega)]
          push_cast; ring
        · rw [if_pos (by omega), if_neg h2, if_neg h3, if_pos (by omega)]
          ring
  rw [h]
  split_ifs <;> simp

private theorem coefficient_sq_mass491 (N m : ℕ) :
    ‖logCoefficient520 N m‖ ^ 2 ≤
      (if m = 2 then (3 : ℝ) else if 3 ≤ m then 1 else 0) *
        Real.exp (-2 * (m : ℝ) / N) := by
  have heq : Real.exp (-(m : ℝ) / N) ^ 2 = Real.exp (-2 * (m : ℝ) / N) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold logCoefficient520
  by_cases hm : 2 ≤ m
  · rw [if_pos hm, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, heq]
    have hE := Real.exp_pos (-2 * (m : ℝ) / N)
    by_cases h2 : m = 2
    · subst h2
      rw [if_pos rfl]
      have hl := Real.log_two_gt_d9
      have hl2 : (1 : ℝ) ≤ 3 * Real.log 2 ^ 2 := by nlinarith
      push_cast
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · have h3 : 3 ≤ m := by omega
      rw [if_neg h2, if_pos h3, one_mul]
      have hl : (1 : ℝ) ≤ Real.log m := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        have h3r : (3 : ℝ) ≤ m := by exact_mod_cast h3
        have := Real.exp_one_lt_d9
        linarith
      rw [div_le_iff₀ (by positivity)]
      have hl2 : (1 : ℝ) ≤ Real.log m ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hl2 hE.le]
  · rw [if_neg hm, if_neg (by omega), if_neg (by omega)]
    simp

private theorem logFourier_full_mass491 (N : ℕ) (hN : 1 ≤ N) :
    (∫ z in (0 : ℝ)..1, ‖logFourier520 N z‖ ^ 2) ≤ 2 * (N : ℝ) := by
  unfold logFourier520
  rw [series_square_mass491 _ (logCoefficient_summable520 N hN)]
  have hh := laplace_bound111_up111
    (fun i : ℕ => if i = 2 then (3 : ℝ) else if 3 ≤ i then 1 else 0) 1 N hN (by norm_num)
    (fun i => by split_ifs <;> norm_num) weight_prefix_mass491
  have hg : Summable (fun n : ℕ => Real.exp (-2 * (n : ℝ) / N)) := by
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hr : ‖Real.exp (-2 / (N : ℝ))‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hNp)
    have hs := summable_geometric_of_norm_lt_one hr
    convert hs using 1
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hw : Summable (fun n : ℕ =>
      (if n = 2 then (3 : ℝ) else if 3 ≤ n then 1 else 0) * Real.exp (-2 * (n : ℝ) / N)) := by
    apply Summable.of_nonneg_of_le _ _ (hg.mul_left 3)
    · intro n
      have := Real.exp_pos (-2 * (n : ℝ) / N)
      split_ifs <;> positivity
    · intro n
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      split_ifs <;> norm_num
  calc
    _ ≤ ∑' n : ℕ, (if n = 2 then (3 : ℝ) else if 3 ≤ n then 1 else 0) *
        Real.exp (-2 * (n : ℝ) / N) :=
      (Summable.of_nonneg_of_le (fun n => sq_nonneg _) (coefficient_sq_mass491 N) hw).tsum_le_tsum
        (coefficient_sq_mass491 N) hw
    _ ≤ _ := by simpa using hh

/-- P0093 page 159, the trivial estimate before equation 5.3, for the
model series S one of equation 6.3. Its square integral over any interval of
radius at most one half is at most the full period square sum, at most 2 N. -/
private theorem logFourier_mass491 (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 ≤ r)
    (hrh : r ≤ 1 / 2) : (∫ z in -r..r, ‖logFourier520 N z‖ ^ 2) ≤ 2 * (N : ℝ) := by
  have hc := (logFourier_continuous_mass491 N hN).norm.pow 2
  have hp : Function.Periodic (fun α => ‖logFourier520 N α‖ ^ 2) 1 :=
    (logFourier_periodic_mass491 N).comp (fun z => ‖z‖ ^ 2)
  have hi := intervalIntegral.integral_mono_interval (μ := volume)
    (show -(1 / 2 : ℝ) ≤ -r by linarith) (show -r ≤ r by linarith) hrh
    (Filter.Eventually.of_forall (fun α => sq_nonneg ‖logFourier520 N α‖))
    (hc.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2))
  have he := hp.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  norm_num only at he
  exact hi.trans (he.trans_le (logFourier_full_mass491 N hN))





/-- Partial summation identity for a real weight against powers of w. -/
private theorem abel_identity_decay491 (c : ℕ → ℝ) (w : ℂ) (M : ℕ) :
    (1 - w) * ∑ m ∈ range (M + 1), (c m : ℂ) * w ^ m =
      (c 0 : ℂ) + ∑ m ∈ range M, ((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)
        - (c M : ℂ) * w ^ (M + 1) := by
  induction M with
  | zero => simp; ring
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ (n := M)]
    ring

/-- Partial summation bound: a decreasing nonnegative weight against a unit
modulus geometric factor has partial sums at most twice the first weight after
multiplication by one minus the ratio. -/
private theorem abel_bound_decay491 (c : ℕ → ℝ) (hc : Antitone c) (h0 : ∀ m, 0 ≤ c m)
    (w : ℂ) (hw : ‖w‖ = 1) (M : ℕ) :
    ‖(1 - w) * ∑ m ∈ range M, (c m : ℂ) * w ^ m‖ ≤ 2 * c 0 := by
  rcases M with _ | M
  · simp; exact h0 0
  rw [abel_identity_decay491]
  have h1 : ‖∑ m ∈ range M, ((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)‖ ≤ c 0 - c M := by
    calc ‖∑ m ∈ range M, ((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)‖
        ≤ ∑ m ∈ range M, ‖((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)‖ := norm_sum_le _ _
      _ = ∑ m ∈ range M, (c m - c (m + 1)) := by
          apply Finset.sum_congr rfl
          intro m _
          rw [norm_mul, norm_pow, hw, one_pow, mul_one, ← Complex.ofReal_sub,
            Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
            abs_of_nonneg (sub_nonneg.mpr (hc (Nat.le_succ m)))]
      _ = c 0 - c M := Finset.sum_range_sub' c M
  have h2 : ‖(c M : ℂ) * w ^ (M + 1)‖ = c M := by
    rw [norm_mul, norm_pow, hw, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (h0 M)]
  have h3 : ‖(c 0 : ℂ)‖ = c 0 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 0)]
  calc ‖(c 0 : ℂ) + ∑ m ∈ range M, ((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)
          - (c M : ℂ) * w ^ (M + 1)‖
      ≤ ‖(c 0 : ℂ)‖ + ‖∑ m ∈ range M, ((c (m + 1) : ℂ) - (c m : ℂ)) * w ^ (m + 1)‖
          + ‖(c M : ℂ) * w ^ (M + 1)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ c 0 + (c 0 - c M) + c M := by rw [h2, h3]; linarith
    _ = 2 * c 0 := by ring

/-- The shifted weight exp of minus m plus two over N over ln of m plus two is
decreasing. -/
private theorem weight_antitone_decay491 (N : ℕ) :
    Antitone (fun m : ℕ => Real.exp (-((m + 2 : ℕ) : ℝ) / N) / Real.log ((m + 2 : ℕ) : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro m
  have hl : 0 < Real.log ((m + 2 : ℕ) : ℝ) := by
    apply Real.log_pos; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hll : Real.log ((m + 2 : ℕ) : ℝ) ≤ Real.log ((m + 1 + 2 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    · push_cast; linarith
  have he : Real.exp (-((m + 1 + 2 : ℕ) : ℝ) / N) ≤ Real.exp (-((m + 2 : ℕ) : ℝ) / N) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    push_cast; linarith
  exact div_le_div₀ (Real.exp_pos _).le he hl hll

/-- The distance of the phase to one is at least four times the distance of z
to the origin on the half period. -/
private theorem phase_distance_decay491 (z : ℝ) (hz : |z| ≤ 1 / 2) :
    4 * |z| ≤ ‖1 - Complex.exp ((-(2 * Real.pi * z) : ℝ) * Complex.I)‖ := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (-(2 * Real.pi * z))
  rw [mul_comm] at h
  rw [norm_sub_rev, h, Real.norm_eq_abs, abs_mul, abs_two,
    show -(2 * Real.pi * z) / 2 = -(Real.pi * z) by ring, Real.sin_neg, abs_neg]
  have hpi := Real.pi_pos
  have hs : 2 / Real.pi * (Real.pi * |z|) ≤ Real.sin (Real.pi * |z|) := by
    apply Real.mul_le_sin (by positivity)
    nlinarith
  have hs2 : 2 / Real.pi * (Real.pi * |z|) = 2 * |z| := by field_simp
  have hs3 : Real.sin (Real.pi * |z|) ≤ |Real.sin (Real.pi * z)| := by
    rcases abs_cases z with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; exact le_abs_self _
    · rw [h1, mul_neg, Real.sin_neg]; exact neg_le_abs _
  linarith

/-- P0093 page 160, the step from equation 6.1 to equation 6.2.
Off the arc the model series S one of equation 6.3 is at most one over the
distance to the origin. The print states the corresponding bound q tau for the
contour integrand; for S one it is partial summation with the decreasing
weights exp of minus m over N over ln m. -/
private theorem logFourier_decay491 (N : ℕ) (hN : 1 ≤ N) (z : ℝ) (hz0 : z ≠ 0)
    (hz : |z| ≤ 1 / 2) : ‖logFourier520 N z‖ ≤ 1 / |z| := by
  have hzpos : 0 < |z| := abs_pos.mpr hz0
  set w : ℂ := Complex.exp ((-(2 * Real.pi * z) : ℝ) * Complex.I) with hw
  have hwn : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hdist : 4 * |z| ≤ ‖1 - w‖ := phase_distance_decay491 z hz
  have hdpos : 0 < ‖1 - w‖ := by linarith
  set c : ℕ → ℝ :=
    fun m : ℕ => Real.exp (-((m + 2 : ℕ) : ℝ) / N) / Real.log ((m + 2 : ℕ) : ℝ) with hc
  have hcanti : Antitone c := weight_antitone_decay491 N
  have hc0 : ∀ m, 0 ≤ c m := by
    intro m
    apply div_nonneg (Real.exp_pos _).le
    apply Real.log_nonneg; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set f : ℕ → ℂ := fun m => logCoefficient520 N m *
    Complex.exp ((-(2 * Real.pi * z * m) : ℝ) * Complex.I) with hf
  have hfs : Summable f := by
    apply Summable.of_norm
    have : (fun m => ‖f m‖) = fun m => ‖logCoefficient520 N m‖ := by
      funext m
      simp only [hf, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [this]
    exact (logCoefficient_summable520 N hN).norm
  have hterm : ∀ m, f (m + 2) = w ^ 2 * ((c m : ℂ) * w ^ m) := by
    intro m
    have hexp : Complex.exp ((-(2 * Real.pi * z * ((m + 2 : ℕ) : ℝ)) : ℝ) * Complex.I)
        = w ^ (m + 2) := by
      rw [hw, ← Complex.exp_nat_mul]
      congr 1
      push_cast; ring
    simp only [hf, logCoefficient520, show 2 ≤ m + 2 by omega, ↓reduceIte]
    rw [hexp]
    simp only [hc]
    ring
  have hsplit : logFourier520 N z = ∑' m, f (m + 2) := by
    have h := hfs.sum_add_tsum_nat_add 2
    have h01 : ∑ i ∈ range 2, f i = 0 := by
      simp [Finset.sum_range_succ, hf, logCoefficient520]
    rw [h01, zero_add] at h
    exact h.symm
  have hgs : Summable (fun m => f (m + 2)) := (summable_nat_add_iff 2).mpr hfs
  have hB : ∀ n, ‖∑ m ∈ range n, f (m + 2)‖ ≤ 2 * c 0 / ‖1 - w‖ := by
    intro n
    have h := abel_bound_decay491 c hcanti hc0 w hwn n
    rw [norm_mul] at h
    have heq : ∑ m ∈ range n, f (m + 2) = w ^ 2 * ∑ m ∈ range n, (c m : ℂ) * w ^ m := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => hterm m)
    rw [heq, norm_mul, norm_pow, hwn, one_pow, one_mul, le_div_iff₀ hdpos]
    linarith [mul_comm ‖1 - w‖ ‖∑ m ∈ range n, (c m : ℂ) * w ^ m‖]
  have hlim : ‖∑' m, f (m + 2)‖ ≤ 2 * c 0 / ‖1 - w‖ :=
    le_of_tendsto (hgs.hasSum.tendsto_sum_nat.norm) (Filter.Eventually.of_forall hB)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hc0le : c 0 ≤ 2 := by
    simp only [hc]
    rw [div_le_iff₀ (by simpa using (by linarith : (0 : ℝ) < Real.log 2))]
    have he : Real.exp (-((0 + 2 : ℕ) : ℝ) / N) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg N)
      simp
    have : (1 : ℝ) ≤ 2 * Real.log ((0 + 2 : ℕ) : ℝ) := by
      simp only [zero_add, Nat.cast_ofNat]; linarith
    linarith
  rw [hsplit]
  refine hlim.trans ?_
  rw [div_le_div_iff₀ hdpos hzpos]
  nlinarith [hc0 0]



private theorem logFourier_continuous_tail491 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (logFourier520 N) := by
  unfold logFourier520
  refine continuous_tsum (u := fun m => ‖logCoefficient520 N m‖) ?_
    (logCoefficient_summable520 N hN).norm ?_
  · intro m
    fun_prop
  · intro m z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem logFourier_periodic_tail491 (N : ℕ) :
    Function.Periodic (logFourier520 N) 1 := by
  intro z
  unfold logFourier520
  apply tsum_congr
  intro m
  congr 1
  have h : ((-(2 * Real.pi * (z + 1) * m) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * z * m) : ℝ) : ℂ) * Complex.I +
        ((-(m : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem phase_periodic_tail491 (n : ℤ) :
    Function.Periodic (fun z : ℝ =>
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) 1 := by
  intro z
  dsimp only
  have h : ((2 * Real.pi * (n : ℝ) * (z + 1) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I +
        (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private theorem full_period_tail491 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    (∫ z in (-(1 / 2) : ℝ)..(1 / 2), logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ) := by
  have hper : Function.Periodic (fun z : ℝ => logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) 1 := by
    intro z
    have h1 := logFourier_periodic_tail491 N z
    have h2 := phase_periodic_tail491 n z
    dsimp only at h2 ⊢
    rw [h1, h2]
  have hshift := hper.intervalIntegral_add_eq (-(1 / 2) : ℝ) 0
  have e1 : (-(1 / 2) : ℝ) + 1 = 1 / 2 := by norm_num
  rw [e1, zero_add] at hshift
  rw [hshift]
  have hmain := logFourier_square_integral520 N hN n
  have hcongr : (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro z _
    dsimp only
    rw [show 2 * Real.pi * (n : ℝ) * z = 2 * Real.pi * z * (n : ℝ) by ring]
  rw [hcongr, hmain]
  have hconv : logConvolution520 n.toNat = logConvolution520 n.toNat := rfl
  rw [hconv]
  by_cases hn : 0 ≤ n
  · have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    rw [hc]
  · have hz : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    simp [hz, logConvolution520]

/-- The integral of the squared model series against a unimodular phase over
an interval of one sign inside the half period is at most the reciprocal of the
distance of the interval to the origin. -/
private theorem piece_bound_tail491 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    (hside : (d ≤ a ∧ b ≤ 1 / 2) ∨ (-(1 / 2) ≤ a ∧ b ≤ -d))
    (hval : (b ^ ((-2 : ℤ) + 1) - a ^ ((-2 : ℤ) + 1)) / (((-2 : ℤ) : ℝ) + 1) ≤ 1 / d) :
    ‖∫ z in a..b, logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤ 1 / d := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    rcases hside with h1 | h1 <;> linarith [h.1, h.2]
  have hint := integral_zpow (a := a) (b := b) (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, h0⟩)
  have hii : IntervalIntegrable (fun z : ℝ => z ^ (-2 : ℤ)) volume a b :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr h0)
  have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := a) (b := b)
    (f := fun z : ℝ => logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))
    (g := fun z : ℝ => z ^ (-2 : ℤ)) hab ?_ hii
  · calc _ ≤ ∫ z in a..b, z ^ (-2 : ℤ) := hle
      _ = _ := hint
      _ ≤ 1 / d := by exact_mod_cast hval
  · refine Filter.Eventually.of_forall ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      rcases hside with h1 | h1
      · have := hz.1; linarith
      · have := hz.2; intro h; linarith
    have hzh : |z| ≤ 1 / 2 := by
      rw [abs_le]
      rcases hside with h1 | h1 <;> constructor <;> linarith [hz.1, hz.2]
    have hdec := logFourier_decay491 N hN z hz0 hzh
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_pow]
    have hpos : 0 < |z| := abs_pos.mpr hz0
    calc ‖logFourier520 N z‖ ^ 2 ≤ (1 / |z|) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hdec 2
      _ = z ^ (-2 : ℤ) := by
          rw [zpow_neg, div_pow, one_pow, sq_abs, one_div]
          norm_cast

private theorem tail_bound_tail491 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (d : ℝ)
    (hd : 0 < d) (hdh : d ≤ 1 / 2) :
    ‖(∫ z in -d..d, logFourier520 N z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) -
      ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ)‖ ≤ 2 / d := by
  rw [← full_period_tail491 N hN n]
  have hcont : Continuous (fun z : ℝ => logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) := by
    have := logFourier_continuous_tail491 N hN
    fun_prop
  have hi (a b : ℝ) : IntervalIntegrable (fun z : ℝ => logFourier520 N z ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) volume a b :=
    hcont.intervalIntegrable a b
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hi (-(1 / 2)) (-d)) (hi (-d) d)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hi (-(1 / 2)) d) (hi d (1 / 2))
  have hp1 := piece_bound_tail491 N hN n (-(1 / 2)) (-d) d hd (by linarith)
    (Or.inr ⟨le_refl _, le_refl _⟩) (by
      have hdn : d ≠ 0 := hd.ne'
      have e : ((-2 : ℤ) + 1) = (-1 : ℤ) := by norm_num
      rw [e, zpow_neg_one, zpow_neg_one]
      have : ((-d)⁻¹ - (-(1 / 2 : ℝ))⁻¹) / (((-2 : ℤ) : ℝ) + 1) = 1 / d - 2 := by
        push_cast
        field_simp
        ring
      rw [this]
      linarith)
  have hp2 := piece_bound_tail491 N hN n d (1 / 2) d hd hdh
    (Or.inl ⟨le_refl _, le_refl _⟩) (by
      have hdn : d ≠ 0 := hd.ne'
      have e : ((-2 : ℤ) + 1) = (-1 : ℤ) := by norm_num
      rw [e, zpow_neg_one, zpow_neg_one]
      have : ((1 / 2 : ℝ)⁻¹ - d⁻¹) / (((-2 : ℤ) : ℝ) + 1) = 1 / d - 2 := by
        push_cast
        field_simp
        ring
      rw [this]
      linarith)
  rw [← h2, ← h1]
  have : ∀ A B D : ℂ, B - (A + B + D) = -(A + D) := by intros; ring
  rw [this, norm_neg]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 1 / d + 1 / d := add_le_add hp1 hp2
    _ = 2 / d := by ring

/-- P0093 pages 160 and 161 equations 6.2 and 6.3. The arc integral of the squared model series S one, extended to a full period, is the exactly damped logarithmic convolution, with the reciprocal length error term. The print extends the contour integral, with the bound q tau squared, and then passes to S one; here S one itself is extended, with the bound 2 q tau. -/
private theorem logFourier_arc_convolution491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  refine ⟨2, by norm_num, 128, ?_⟩
  intro N hN q hq hqN n
  have hNR : (128 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN.le
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτ
  have hτ2 : (2 : ℝ) ≤ τ := by
    have h128 : ((128 : ℝ)) ^ (1 / 7 : ℝ) = 2 := by
      have : (128 : ℝ) = (2 : ℝ) ^ (7 : ℝ) := by norm_num
      rw [this, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← h128]
    exact Real.rpow_le_rpow (by norm_num) hNR (by norm_num)
  have hD : (2 : ℝ) ≤ (q : ℝ) * τ := by nlinarith
  have hDpos : (0 : ℝ) < (q : ℝ) * τ := by linarith
  have hd : (0 : ℝ) < 1 / ((q : ℝ) * τ) := by positivity
  have hdh : 1 / ((q : ℝ) * τ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hD
  have ht := tail_bound_tail491 N (by omega) n (1 / ((q : ℝ) * τ)) hd hdh
  refine ht.trans ?_
  have hsq : ((q : ℝ) * τ) ^ 2 ≤ (N : ℝ) := by
    have h1 : ((q : ℝ) * τ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_right hqN (by positivity)
    rw [← Real.rpow_add (by linarith)] at h1
    calc ((q : ℝ) * τ) ^ 2 ≤ ((N : ℝ) ^ ((1 / 10 : ℝ) + 1 / 7)) ^ 2 :=
          pow_le_pow_left₀ hDpos.le h1 2
      _ = (N : ℝ) ^ (((1 / 10 : ℝ) + 1 / 7) * 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
          norm_num
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  have hlog : (1 : ℝ) ≤ Real.log N := by
    have h3 : Real.exp 1 ≤ (N : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) h3
  have hlog13 : (1 : ℝ) ≤ Real.log N ^ 13 := one_le_pow₀ hlog
  rw [div_le_div_iff₀ hd hDpos]
  have e : (2 : ℝ) * ((q : ℝ) * τ) = 2 * ((q : ℝ) * τ) ^ 2 * (1 / ((q : ℝ) * τ)) := by
    field_simp
  rw [e]
  apply mul_le_mul_of_nonneg_right _ hd.le
  nlinarith [mul_le_mul hsq hlog13 zero_le_one hN0]



/-- Standard analysis, the Cauchy Schwarz step of P0093 page 160 equation 5.3 in its weighted
arithmetic geometric mean form, split at an inner radius. The square of `P` is replaced by the
square of the model `L` on the arc of radius `δ`; the cross term is bounded with the sup bound
`S` outside the inner radius `ξ` and with the weight `lam` inside it. -/
private theorem arc_square_replace520 (P L : ℝ → ℂ) (hP : Continuous P) (hL : Continuous L)
    (φ : ℝ → ℂ) (hφc : Continuous φ) (hφ : ∀ z, ‖φ z‖ = 1)
    (δ ξ lam A B Mass S : ℝ) (hξ : 0 < ξ) (hξδ : ξ ≤ δ) (hlam : 0 < lam)
    (hA : (∫ z in -δ..δ, ‖P z - L z‖ ^ 2) ≤ A)
    (hB : (∫ z in -ξ..ξ, ‖P z - L z‖ ^ 2) ≤ B)
    (hMass : (∫ z in -ξ..ξ, ‖L z‖ ^ 2) ≤ Mass)
    (hS : ∀ z : ℝ, ξ ≤ |z| → |z| ≤ δ → ‖L z‖ ^ 2 ≤ S) :
    ‖(∫ z in -δ..δ, P z ^ 2 * φ z) - (∫ z in -δ..δ, L z ^ 2 * φ z)‖ ≤
      3 * A + 2 * S * δ + lam * B + Mass / lam := by
  have hδ : 0 < δ := lt_of_lt_of_le hξ hξδ
  have hfc : Continuous fun z => ‖P z - L z‖ ^ 2 := by fun_prop
  have hgc : Continuous fun z => 2 * ‖P z - L z‖ * ‖L z‖ := by fun_prop
  have hLc : Continuous fun z => ‖L z‖ ^ 2 := by fun_prop
  have hfi : ∀ a b : ℝ, IntervalIntegrable (fun z => ‖P z - L z‖ ^ 2) volume a b :=
    fun a b => hfc.intervalIntegrable a b
  have hgi : ∀ a b : ℝ, IntervalIntegrable (fun z => 2 * ‖P z - L z‖ * ‖L z‖) volume a b :=
    fun a b => hgc.intervalIntegrable a b
  have hLi : ∀ a b : ℝ, IntervalIntegrable (fun z => ‖L z‖ ^ 2) volume a b :=
    fun a b => hLc.intervalIntegrable a b
  -- step 1: pointwise bound of the difference
  have h1 : ‖(∫ z in -δ..δ, P z ^ 2 * φ z) - (∫ z in -δ..δ, L z ^ 2 * φ z)‖ ≤
      ∫ z in -δ..δ, (‖P z - L z‖ ^ 2 + 2 * ‖P z - L z‖ * ‖L z‖) := by
    rw [← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun z => P z ^ 2 * φ z).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun z => L z ^ 2 * φ z).intervalIntegrable _ _)]
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans ?_
    refine intervalIntegral.integral_mono_on (by linarith)
      ((by fun_prop : Continuous fun z => ‖P z ^ 2 * φ z - L z ^ 2 * φ z‖).intervalIntegrable _ _)
      ((hfc.add hgc).intervalIntegrable _ _) ?_
    intro z _
    have e : P z ^ 2 * φ z - L z ^ 2 * φ z = (P z - L z) * ((P z - L z) + 2 * L z) * φ z := by
      ring
    rw [e, norm_mul, norm_mul, hφ, mul_one]
    have h2 : ‖(P z - L z) + 2 * L z‖ ≤ ‖P z - L z‖ + 2 * ‖L z‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      simp
    nlinarith [norm_nonneg (P z - L z), norm_nonneg (L z)]
  rw [intervalIntegral.integral_add (hfi _ _) (hgi _ _)] at h1
  -- split
  have sf : (∫ z in -δ..δ, ‖P z - L z‖ ^ 2) =
      (∫ z in -δ..-ξ, ‖P z - L z‖ ^ 2) + (∫ z in -ξ..ξ, ‖P z - L z‖ ^ 2) +
        (∫ z in ξ..δ, ‖P z - L z‖ ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _),
      intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _)]
  have sg : (∫ z in -δ..δ, 2 * ‖P z - L z‖ * ‖L z‖) =
      (∫ z in -δ..-ξ, 2 * ‖P z - L z‖ * ‖L z‖) + (∫ z in -ξ..ξ, 2 * ‖P z - L z‖ * ‖L z‖) +
        (∫ z in ξ..δ, 2 * ‖P z - L z‖ * ‖L z‖) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _),
      intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _)]
  have fnn : ∀ a b : ℝ, a ≤ b → 0 ≤ ∫ z in a..b, ‖P z - L z‖ ^ 2 := fun a b hab =>
    intervalIntegral.integral_nonneg hab (fun z _ => by positivity)
  have hSnn : 0 ≤ S :=
    (sq_nonneg _).trans (hS δ (by rw [abs_of_pos hδ]; exact hξδ) (by rw [abs_of_pos hδ]))
  -- outer pieces
  have outer : ∀ a b : ℝ, a ≤ b → (∀ z ∈ Set.Icc a b, ξ ≤ |z| ∧ |z| ≤ δ) →
      (∫ z in a..b, 2 * ‖P z - L z‖ * ‖L z‖) ≤ (∫ z in a..b, ‖P z - L z‖ ^ 2) + S * (b - a) := by
    intro a b hab h
    have : (∫ z in a..b, ‖P z - L z‖ ^ 2) + S * (b - a) =
        ∫ z in a..b, (‖P z - L z‖ ^ 2 + S) := by
      rw [intervalIntegral.integral_add (hfi _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [this]
    refine intervalIntegral.integral_mono_on hab (hgi _ _)
      ((hfc.add continuous_const).intervalIntegrable _ _) ?_
    intro z hz
    have := hS z (h z hz).1 (h z hz).2
    nlinarith [sq_nonneg (‖P z - L z‖ - ‖L z‖)]
  have o1 := outer (-δ) (-ξ) (by linarith) (by
    intro z hz
    rw [abs_of_nonpos (by linarith [hz.2])]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩)
  have o2 := outer ξ δ hξδ (by
    intro z hz
    rw [abs_of_nonneg (by linarith [hz.1])]
    exact ⟨hz.1, hz.2⟩)
  -- inner piece
  have inner : (∫ z in -ξ..ξ, 2 * ‖P z - L z‖ * ‖L z‖) ≤
      lam * (∫ z in -ξ..ξ, ‖P z - L z‖ ^ 2) + (∫ z in -ξ..ξ, ‖L z‖ ^ 2) / lam := by
    have : lam * (∫ z in -ξ..ξ, ‖P z - L z‖ ^ 2) + (∫ z in -ξ..ξ, ‖L z‖ ^ 2) / lam =
        ∫ z in -ξ..ξ, (lam * ‖P z - L z‖ ^ 2 + ‖L z‖ ^ 2 / lam) := by
      rw [intervalIntegral.integral_add ((hfi _ _).const_mul lam) ((hLi _ _).div_const lam),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
    rw [this]
    refine intervalIntegral.integral_mono_on (by linarith) (hgi _ _)
      (((hfi _ _).const_mul lam).add ((hLi _ _).div_const lam)) ?_
    intro z _
    have key : 2 * ‖P z - L z‖ * ‖L z‖ * lam ≤
        (lam * ‖P z - L z‖ ^ 2 + ‖L z‖ ^ 2 / lam) * lam := by
      have : (lam * ‖P z - L z‖ ^ 2 + ‖L z‖ ^ 2 / lam) * lam =
          lam ^ 2 * ‖P z - L z‖ ^ 2 + ‖L z‖ ^ 2 := by
        field_simp
      rw [this]
      nlinarith [sq_nonneg (lam * ‖P z - L z‖ - ‖L z‖)]
    exact le_of_mul_le_mul_right key hlam
  have hBl : lam * (∫ z in -ξ..ξ, ‖P z - L z‖ ^ 2) ≤ lam * B :=
    mul_le_mul_of_nonneg_left hB hlam.le
  have hMl : (∫ z in -ξ..ξ, ‖L z‖ ^ 2) / lam ≤ Mass / lam :=
    div_le_div_of_nonneg_right hMass hlam.le
  have n0 := fnn (-ξ) ξ (by linarith)
  have hSξ : 0 ≤ S * ξ := mul_nonneg hSnn hξ.le
  have hAnn : 0 ≤ A := (fnn (-δ) δ (by linarith)).trans hA
  nlinarith




/-- Range facts the assembly needs: on this range the seventh root of N is
positive, N is positive and the logarithm of N is nonnegative. -/
private theorem split_range520 {N : ℕ} (hN : 3 < N) :
    1 ≤ N ∧ (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) ∧ 0 < (N : ℝ) ∧ 0 ≤ Real.log N := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  exact ⟨hN1, Real.rpow_pos_of_pos hNpos _, hNpos, Real.log_nonneg (by exact_mod_cast hN1)⟩

/-- Scale facts for the short arc, standard real arithmetic. With lam the fourth
root of N and R the product of q and the seventh root of N, on the range of the
leaf R lies between two and lam, lam is at least one, its fourth power is N, the
square of q is at most N and the logarithm of N is at least one. -/
private theorem arc_scale520 {N q : ℕ} (hN : 128 < N) (hq : 1 ≤ q)
    (hqQ : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    2 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ∧
      (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) ∧
      1 ≤ (N : ℝ) ^ (1 / 4 : ℝ) ∧
      (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) *
        ((N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ)) = (N : ℝ) ∧
      (q : ℝ) ^ 2 ≤ (N : ℝ) ∧ 1 ≤ Real.log N := by
  have hn : (128 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hτ2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
    have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128) hn
      (by norm_num : (0 : ℝ) ≤ 1 / 7)
    have he : (128 : ℝ) ^ (1 / 7 : ℝ) = 2 := by
      rw [show (128 : ℝ) = 2 ^ (7 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [he] at hh
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlam1 : 1 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have h4 : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) *
      ((N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ)) = (N : ℝ) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    norm_num
  have hR : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h1 : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤
        (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_right hqQ (Real.rpow_nonneg hN0.le _)
    have h2 : (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    exact h1.trans h2
  have hq4 : (q : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    hqQ.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
  have hq2 : (q : ℝ) ^ 2 ≤ (N : ℝ) := by
    have ha : (q : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by nlinarith
    have hb : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) := by nlinarith
    exact ha.trans hb
  have hl : 1 ≤ Real.log N := by
    have hN3' : (3 : ℝ) < N := by linarith
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3').le
  exact ⟨by nlinarith, hR, hlam1, h4, hq2, hl⟩

/-- Real arithmetic collecting the four terms of the arc comparison into the
single term of the leaf. -/
private theorem arc_collect520 (C N R lam l13 : ℝ) (hC : 0 < C) (hN : 0 < N)
    (hR : 0 < R) (hRlam : R ≤ lam) (hl : 1 ≤ l13) :
    3 * (C * N / R * l13) + 2 * N * (1 / R) + lam * (C * N / (lam * lam) * l13) +
        2 * N / lam ≤ (4 * C + 4) * N * l13 * (1 / R) := by
  have hlam : 0 < lam := lt_of_lt_of_le hR hRlam
  have hy : N / lam ≤ N / R := div_le_div_of_nonneg_left hN.le hR hRlam
  have hy0 : 0 ≤ N / lam := by positivity
  have hx0 : 0 ≤ N / R := by positivity
  have e1 : lam * (C * N / (lam * lam) * l13) = C * l13 * (N / lam) := by
    field_simp
  have e2 : 3 * (C * N / R * l13) = 3 * C * l13 * (N / R) := by ring
  have e3 : 2 * N * (1 / R) = 2 * (N / R) := by ring
  have e4 : 2 * N / lam = 2 * (N / lam) := by ring
  have e5 : (4 * C + 4) * N * l13 * (1 / R) = (4 * C + 4) * l13 * (N / R) := by ring
  rw [e1, e2, e3, e4, e5]
  have hCl : 0 ≤ C * l13 := by positivity
  have h1 : C * l13 * (N / lam) ≤ C * l13 * (N / R) := mul_le_mul_of_nonneg_left hy hCl
  have h2 : 2 * (N / R) ≤ 2 * l13 * (N / R) := by nlinarith
  have h3 : 2 * (N / lam) ≤ 2 * l13 * (N / R) := by nlinarith
  nlinarith


/-- LEAF. First error term, displays 6.1 to 6.3 of the surrounding development:
on the short arc the principal square is replaced by the square of the full
period model series, and the difference is charged to the arc length, giving
the term inverse of q times the seventh root of N. -/
private theorem short_arc_model_replace520_p (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖principalIntegral520 N q n -
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          logFourier520 N z ^ 2 *
            Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C, hC, h⟩ := principal_arc_mean_square_radius520 hG
  refine ⟨4 * C + 4, by positivity, 128, ?_⟩
  intro N hN q hq hqQ n _
  obtain ⟨hR2, hRlam, hlam1, h4, hq2, hl⟩ := arc_scale520 hN hq hqQ
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set R : ℝ := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hRdef
  set lam : ℝ := (N : ℝ) ^ (1 / 4 : ℝ) with hlamdef
  have hR0 : 0 < R := by linarith
  have hlam0 : 0 < lam := by linarith
  have hR0lam : R ≤ lam * lam := by nlinarith
  have hRsq : R ^ 2 ≤ (N : ℝ) := by nlinarith
  have hlam2 : (2 : ℝ) ≤ lam * lam := by linarith
  have hlamsq : (lam * lam) ^ 2 ≤ (N : ℝ) := by rw [sq]; exact h4.le
  have hA := h N hN q hq hq2 R hR2 hRsq
  have hB := h N hN q hq hq2 (lam * lam) hlam2 hlamsq
  have hξ : 0 < 1 / (lam * lam) := by positivity
  have hξδ : 1 / (lam * lam) ≤ 1 / R := one_div_le_one_div_of_le hR0 hR0lam
  have hδh : 1 / R ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hR2
  have hMass := logFourier_mass491 N hN1 (1 / (lam * lam)) hξ.le (hξδ.trans hδh)
  have hS : ∀ z : ℝ, 1 / (lam * lam) ≤ |z| → |z| ≤ 1 / R →
      ‖logFourier520 N z‖ ^ 2 ≤ (N : ℝ) := by
    intro z hz1 hz2
    have hzpos : 0 < |z| := lt_of_lt_of_le hξ hz1
    have hz0 : z ≠ 0 := abs_pos.mp hzpos
    have hd := logFourier_decay491 N hN1 z hz0 (hz2.trans hδh)
    have hinv : 1 / |z| ≤ lam * lam := by
      rw [div_le_iff₀ hzpos]
      have := (div_le_iff₀ (by positivity : 0 < lam * lam)).mp hz1
      linarith
    have hle : ‖logFourier520 N z‖ ≤ lam * lam := hd.trans hinv
    calc ‖logFourier520 N z‖ ^ 2 ≤ (lam * lam) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ ≤ (N : ℝ) := hlamsq
  have hφc : Continuous (fun z : ℝ =>
      Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hmain := arc_square_replace520 (principalPrime520 N q) (logFourier520 N)
    (continuous_principal520 N q hN1) (logFourier_continuous_radius520 N hN1)
    (fun z : ℝ => Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))
    hφc (fun z => Complex.norm_exp_ofReal_mul_I _)
    (1 / R) (1 / (lam * lam)) lam _ _ _ (N : ℝ) hξ hξδ hlam0 hA hB hMass hS
  have hint : principalIntegral520 N q n =
      ∫ z in -(1 / R)..(1 / R), principalPrime520 N q z ^ 2 *
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    unfold principalIntegral520
    apply intervalIntegral.integral_congr
    intro z _
    simp only []
    rw [show ((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [hint]
  refine hmain.trans ?_
  have hcol := arc_collect520 C (N : ℝ) R lam (Real.log N ^ 13) hC hNpos hR0 hRlam
    (one_le_pow₀ hl)
  have hfin : 3 * (C * (N : ℝ) / R * Real.log N ^ 13) + 2 * (N : ℝ) * (1 / R) +
      lam * (C * (N : ℝ) / (lam * lam) * Real.log N ^ 13) + 2 * (N : ℝ) / lam ≤
      (4 * C + 4) * (N : ℝ) * Real.log N ^ 13 * (1 / R) := hcol
  linarith [hfin]


/-- The two spellings of the phase on the short arc give the same integral. -/
private lemma arc_phase_order520 (N q : ℕ) (n : ℤ) :
    (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
  apply intervalIntegral.integral_congr
  intro z _
  simp only []
  rw [show ((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I by push_cast; ring]


/-- LEAF. Second error term, displays 6.1 to 6.3 of the surrounding development:
the short arc integral of the model square is extended to a full period, and
the loss is the square root saving, the term inverse of the square root of q
times the seventh root of N. -/
private theorem short_arc_extend_period520_p (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          logFourier520 N z ^ 2 *
            Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨C, hC, N0, h⟩ := logFourier_arc_convolution491
  refine ⟨C, hC, max N0 1, ?_⟩
  intro N hN q hq hqQ n hn
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by have := le_max_right N0 1; omega
  have hb := h N hN0 q hq hqQ n
  rw [arc_phase_order520 N q n]
  rw [logFourier_square_integral520 N hN1 n]
  have hconv : ∀ m : ℕ, logConvolution520 m = logConvolution520 m := fun m => rfl
  rw [hconv]
  have hconst : ((Real.exp (-(n : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ) =
      ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ) := by
    by_cases hn0 : 0 ≤ n
    · have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn0
      rw [hc]
    · have hz : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      rw [hz]
      simp [logConvolution520]
  rw [hconst]
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hRpos : 0 < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hR1 : 1 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
    nlinarith
  have hsq : Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by
    have hle : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤
        ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by nlinarith
    have h2 := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_mul_self hRpos.le] at h2
  have hnum : 0 ≤ C * (N : ℝ) * Real.log N ^ 13 := by positivity
  exact hb.trans (div_le_div_of_nonneg_left hnum (Real.sqrt_pos.mpr hRpos) hsq)




/-- LEAF. P0093 pages 160 and 161 equations 6.1 through 6.3.
Replace the principal square by the full period S one square model.
This is the analytic contour comparison. Fourier extraction is proved separately. -/
theorem principal_model520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C1, hC1, M1, hleaf1⟩ := short_arc_model_replace520_p hG
  obtain ⟨C2, hC2, M2, hleaf2⟩ := short_arc_extend_period520_p hG
  refine ⟨C1 + C2, by linarith, M1 + M2 + 3, ?_⟩
  intro N hN q hq hqQ n hn
  have hM1 : M1 < N := by omega
  have hM2 : M2 < N := by omega
  have hN3 : 3 < N := by omega
  obtain ⟨-, hT, hNpos, hlog⟩ := split_range520 hN3
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqT : 0 < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := mul_pos hqpos hT
  have hA0 : 0 ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hB0 : 0 ≤ 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hX0 : 0 ≤ (N : ℝ) * Real.log N ^ 13 :=
    mul_nonneg hNpos.le (pow_nonneg hlog 13)
  have h1 := hleaf1 N hM1 q hq hqQ n hn
  have h2 := hleaf2 N hM2 q hq hqQ n hn
  have htri :
      ‖principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          C2 * (N : ℝ) * Real.log N ^ 13 /
            Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have heq : principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
        (principalIntegral520 N q n -
          (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))) +
          ((∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) -
            (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))) := by
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have hA2 : C2 * (N : ℝ) * Real.log N ^ 13 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))
      = C2 * (N : ℝ) * Real.log N ^ 13 *
        (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    ring
  have e1 : C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hA0
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog 13)
    refine mul_le_mul_of_nonneg_right ?_ hNpos.le
    linarith
  have e2 : C2 * (N : ℝ) * Real.log N ^ 13 *
        (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
        (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hB0
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog 13)
    refine mul_le_mul_of_nonneg_right ?_ hNpos.le
    linarith
  calc
    ‖principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖
        ≤ C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
            C2 * (N : ℝ) * Real.log N ^ 13 /
              Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := htri
    _ = C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          C2 * (N : ℝ) * Real.log N ^ 13 *
            (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
        rw [hA2]
    _ ≤ (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
            (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := add_le_add e1 e2
    _ = (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
        ring

/-- P0093 pages 160 and 161 equations 6.1 through 6.3.
CONDITIONAL on principal_model520. Extend the principal square to a full period and read its exact convolution.
No fixed one over N shoulder is removed. -/
theorem principal_convolution520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖principalIntegral520 N q n -
        ((Real.exp (-(n : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ)‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C, hC, N0, hmodel⟩ := principal_model520 hG
  refine ⟨C, hC, max N0 1, ?_⟩
  intro N hN q hq hqQ n hn
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by have := le_max_right N0 1; omega
  have h := hmodel N hN0 q hq hqQ n hn
  rwa [logFourier_square_integral520 N hN1 n] at h

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- P0093 page 160 equation 5.4. The phase has unit norm, so the error
square integral is bounded by its square mean at every signed residual. -/
theorem error_integral_le520 (N q : ℕ) (n : ℤ) :
    ‖errorIntegral520 N q n‖ ≤
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖residueError520 N q a z‖ ^ 2 := by
  unfold errorIntegral520
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro a ha
  calc
    _ ≤ ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        ‖residueError520 N q a z ^ 2 * Complex.exp
          (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by
        have hr : 0 ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
        linarith)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro z hz
      dsimp only
      simp only [norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- P0093 page 161 after equation 6.3. The convolution vanishes below four. -/
theorem logConvolution_vanish520 (n : ℕ) (hn : n ≤ 3) :
    logConvolution520 n = 0 := by
  unfold logConvolution520
  exact sum_eq_zero (fun m hm => by have := mem_Icc.mp hm; omega)

/-- P0093 page 161 after equation 6.3. The first nonzero convolution. -/
theorem logConvolution_four520 :
    logConvolution520 4 = 1 / (Real.log 2 * Real.log 2) := by
  simp [logConvolution520]

/-- P0093 page 156 equation 3.4. Nonnegative signed phases equal the
natural Ramanujan sum already formalized in Ramanujan103. -/
theorem signedRamanujan_toNat520 (q : ℕ) (n : ℤ) (hn : 0 ≤ n) :
    signedRamanujan520 q n = LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat := by
  have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
  unfold signedRamanujan520 LeanLab.Perelli1996.Ramanujan103.ramanujanSum
    LeanLab.Perelli1996.Kernel.e
  apply sum_congr rfl
  intro a ha
  rw [hc]
  congr 1
  push_cast
  ring

/-- P0093 page 161 equation 6.4. The Ramanujan sum is real by its
integer Mobius divisor expansion. -/
theorem ramanujan_im_zero520 (q m : ℕ) (hq : 1 ≤ q) :
    (LeanLab.Perelli1996.Ramanujan103.ramanujanSum q m).im = 0 := by
  rw [LeanLab.Perelli1996.Ramanujan103.ramanujanSum_divisor_expansion q m (by omega)]
  simp only [Complex.im_sum]
  apply sum_eq_zero
  intro d hd
  split_ifs <;> simp

/-- P0093 page 161 equation 6.4. The complex Ramanujan sum is exactly
the cast of the finite real cosine sum used in the sealed target. -/
theorem ramanujan_cos520 (q m : ℕ) (hq : 1 ≤ q) :
    LeanLab.Perelli1996.Ramanujan103.ramanujanSum q m =
      ((∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        Real.cos (2 * Real.pi * (m : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) := by
  apply Complex.ext
  · unfold LeanLab.Perelli1996.Ramanujan103.ramanujanSum LeanLab.Perelli1996.Kernel.e
    rw [Complex.re_sum, Complex.ofReal_re]
    apply sum_congr rfl
    intro a ha
    rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]
    congr 1
    ring
  · simp only [Complex.ofReal_im, ramanujan_im_zero520 q m hq]

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951
open Finset
/-- P0093 page 156 equation 3.4. The principal arithmetic coefficient
has norm at most one for every positive modulus and every signed frequency. -/
theorem principal_coefficient_norm_real520 (q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    ‖(((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
      signedRamanujan520 q n‖ ≤ 1 := by
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hμ : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hμ2 : (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) hμ 2
  have hr : ‖signedRamanujan520 q n‖ ≤ (q.totient : ℝ) := by
    unfold signedRamanujan520
    calc
      _ ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ‖Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)‖ :=
        norm_sum_le _ _
      _ = (q.totient : ℝ) := by
        simp only [Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one]
        congr 1
        rw [Nat.totient_eq_card_coprime]
        congr 1
        ext a
        simp [Nat.coprime_comm]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) * q.totient := by
      gcongr
    _ ≤ 1 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (show (0 : ℝ) < (q.totient : ℝ) ^ 2 by positivity)).mpr
      have hsq : (q.totient : ℝ) ≤ (q.totient : ℝ) ^ 2 := by nlinarith
      exact (mul_le_mul_of_nonneg_right hμ2 (by positivity)).trans (by simpa using hsq)


/-- P0093 page 156 equation 3.4. The coefficient in the square expansion
has the same norm bound as its real fraction form. -/
theorem principal_coefficient_norm520 (q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    ‖principalCoefficient520 q ^ 2 * signedRamanujan520 q n‖ ≤ 1 := by
  have hc : principalCoefficient520 q ^ 2 =
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) := by
    simp [principalCoefficient520, div_pow]
  rw [hc]
  exact principal_coefficient_norm_real520 q hq n

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- P0093 page 165 equation 8.1. The signed residual integrand has period
one. The proof also covers every negative integer residual. -/
theorem residual_periodic520 (N : ℕ) (n : ℤ) :
    Function.Periodic (fun α : ℝ => primeFourier111_up111 N α ^ 2 *
      Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)) 1 := by
  have hS : Function.Periodic (primeFourier111_up111 N) 1 := by
    intro α
    unfold primeFourier111_up111
    apply tsum_congr
    intro p
    congr 1
    have he : ((-(2 * Real.pi * (α + 1) * (p : ℕ)) : ℝ) : ℂ) * Complex.I =
        ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) : ℂ) * Complex.I +
          ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) := by push_cast; ring
    rw [he, Complex.exp_add]
    have hp : Complex.exp ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I (-(p : ℕ) : ℤ) using 1 <;> push_cast <;> ring
    rw [hp, mul_one]
  intro α
  dsimp only
  rw [hS α]
  congr 1
  have he : (((2 * Real.pi * (α + 1) * (n : ℝ) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I) +
        (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  have hp : Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I n using 1 <;> ring
  rw [he, Complex.exp_add, hp, mul_one]

/-- P0093 page 165 equation 8.1. Join the clipped endpoints and sum the
local prime square integrals over disjoint rational arcs. -/
theorem major_integral_partition520 (N : ℕ) (hN : 2 ^ 70 < N) (n : ℤ) :
    (∫ α in majorArcs280_up111 N, primeFourier111_up111 N α ^ 2 *
      Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊, localArc520 N q n := by
  have hsep := major_parameters_separated520 N hN
  have hset : majorArcs280_up111 N = rationalMajor520 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊
      ((N : ℝ) ^ (1 / 7 : ℝ)) := by
    ext α
    simp only [majorArcs280_up111, rationalMajor520, Set.mem_setOf_eq,
      Nat.le_floor_iff (show 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) by positivity)]
  rw [hset, rational_partition520 _ hsep.1 _ hsep.2 _
    (by have hS := continuous_prime_fourier111_up111 N (show 1 ≤ N by omega); fun_prop)
    (residual_periodic520 N n)]
  apply sum_congr rfl
  intro q hq
  unfold localArc520
  apply sum_congr rfl
  intro a ha
  apply intervalIntegral.integral_congr
  intro z hz
  dsimp only
  congr 1
  congr 1
  push_cast
  ring

/-- P0093 page 161 equation 6.4. A local main term is the real cosine
coefficient times the exact damped convolution, even for negative residuals. -/
theorem local_main_cos520 (N q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    localMain520 N q n =
      ((Real.exp (-(n : ℝ) / N) *
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 *
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            Real.cos (2 * Real.pi * (n.toNat : ℝ) * (a : ℝ) / (q : ℝ))) *
        logConvolution520 n.toNat : ℝ) : ℂ) := by
  by_cases hn : 0 ≤ n
  · unfold localMain520
    rw [signedRamanujan_toNat520 q n hn, ramanujan_cos520 q n.toNat hq]
    simp only [principalCoefficient520]
    push_cast
    ring
  · have hz : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    simp [localMain520, hz, logConvolution_vanish520 0 (by omega)]

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951
open Finset

/-- P0093 page 156 equation 3.4. At modulus one no prime divisor is removed. -/
theorem principal_unit520 (N : ℕ) (z : ℝ) :
    principalPrime520 N 1 z = primeFourier111_up111 N z := by
  simp [principalPrime520]

/-- P0093 page 156 equation 3.4. At the unit modulus residue zero
is exactly principal, so its residue error vanishes pointwise. -/
theorem residue_unit520 (N : ℕ) (z : ℝ) : residueError520 N 1 0 z = 0 := by
  simp [residueError520, principalCoefficient520, principal_unit520]

/-- P0093 page 160 equation 5.4. The unit modulus error square is zero. -/
theorem error_unit520 (N : ℕ) (n : ℤ) : errorIntegral520 N 1 n = 0 := by
  have hs : (range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
  simp [errorIntegral520, hs, residue_unit520]

/-- P0093 page 160 equation 5.5. The unit modulus mixed term is zero. -/
theorem mixed_unit520 (N : ℕ) (n : ℤ) : mixedIntegral520 N 1 n = 0 := by
  have hs : (range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
  simp [mixedIntegral520, hs, residue_unit520]

/-- P0093 page 161 equation 6.4. At modulus one and residual four
the main term is positive and has the exact first convolution value. -/
theorem local_main_four_unit520 (N : ℕ) :
    localMain520 N 1 4 =
      ((Real.exp (-(4 : ℝ) / N) / (Real.log 2 * Real.log 2) : ℝ) : ℂ) := by
  simp [localMain520, principalCoefficient520, signedRamanujan520,
    logConvolution_four520, div_eq_mul_inv]

/-- P0093 pages 161 and 165 equations 6.4 and 8.1. There are arbitrarily
large admissible parameters with modulus one and a nonzero convolution. -/
theorem local_parameters_instance520 (N0 : ℕ) :
    ∃ N : ℕ, N0 < N ∧ 2 ^ 70 < N ∧ 1 ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
      (4 : ℤ) ≤ N ∧ 0 < (Real.exp (-(4 : ℝ) / N) / (Real.log 2 * Real.log 2)) := by
  refine ⟨max N0 (2 ^ 70) + 4, by omega, by omega, ?_, by omega, ?_⟩
  · apply Real.one_le_rpow
    · exact_mod_cast (show 1 ≤ max N0 (2 ^ 70) + 4 by omega)
    · norm_num
  · exact div_pos (Real.exp_pos _) (mul_pos (Real.log_pos (by norm_num))
      (Real.log_pos (by norm_num)))

end LeanLab.Linnik1951
