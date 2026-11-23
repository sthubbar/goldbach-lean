module

public import LeanLab.Linnik1951.Data357
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
P0093 pages 165 and 166. Finite rational arc geometry and periodic endpoints.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open Finset MeasureTheory
/-- LEAF. P0093 page 165 before equation 8.1. Distinct rational centres are
separated by the reciprocal product of their denominators. -/
theorem rational_separation491 (a b : ℤ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
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
theorem rational_arcs_disjoint491 (a b : ℤ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
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
  have hd := rational_separation491 a b q r hq hr hne
  have ht := abs_sub_le ((a : ℝ) / q) α ((b : ℝ) / r)
  linarith


/-- P0093 page 165 equation 8.1 and page 166 equation 8.2. The finite reduced rational centres, including both endpoint representatives at modulus one. -/
noncomputable def arcIndices491 (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 Q) ×ˢ (Icc 0 Q)).filter fun p => p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1
/-- P0093 page 165 equation 8.1 and page 166 equation 8.2. The full closed rational arc of radius one over q tau. -/
noncomputable def rationalArc491 (q a : ℕ) (τ : ℝ) : Set ℝ :=
  Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * τ)) ((a : ℝ) / q + 1 / ((q : ℝ) * τ))
/-- P0093 page 165 equation 8.1 and page 166 equation 8.2. The rational major arcs with natural denominator cutoff, clipped to the unit interval. -/
noncomputable def rationalMajor491 (Q : ℕ) (τ : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 1 ∧ ∃ r : ℚ, r.den ≤ Q ∧ |α - r| ≤ 1 / ((r.den : ℝ) * τ)}

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. Membership in the finite rational centre index set. -/
theorem arcIndices_mem491 (Q : ℕ) (p : ℕ × ℕ) :
    p ∈ arcIndices491 Q ↔ 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1 := by
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
theorem rational_major_cover491 (Q : ℕ) (τ : ℝ) (hτ : 1 < τ) :
    rationalMajor491 Q τ =
      ⋃ p ∈ arcIndices491 Q, Set.Icc (0 : ℝ) 1 ∩ rationalArc491 p.1 p.2 τ := by
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
    have hp : (r.den, a) ∈ arcIndices491 Q :=
      (arcIndices_mem491 Q _).mpr ⟨hq, hrQ, haq, hcop⟩
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
    obtain ⟨hq, hqQ, ha, hcop⟩ := (arcIndices_mem491 Q p).mp hp
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
theorem arcIndices_cross_ne491 (Q : ℕ) (p t : ℕ × ℕ)
    (hp : p ∈ arcIndices491 Q) (ht : t ∈ arcIndices491 Q) (hne : p ≠ t) :
    (p.2 : ℤ) * t.1 - (t.2 : ℤ) * p.1 ≠ 0 := by
  obtain ⟨hp1, hpQ, hp2, hpc⟩ := (arcIndices_mem491 Q p).mp hp
  obtain ⟨ht1, htQ, ht2, htc⟩ := (arcIndices_mem491 Q t).mp ht
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
theorem rational_clipped_integral491 (Q : ℕ) (hQ : 1 ≤ Q) (τ : ℝ)
    (hτ : 2 * (Q : ℝ) < τ) (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ α in rationalMajor491 Q τ, f α) =
      ∑ p ∈ arcIndices491 Q,
        ∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc491 p.1 p.2 τ, f α := by
  have hτ1 : 1 < τ := by
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  rw [rational_major_cover491 Q τ hτ1]
  apply integral_biUnion_finset
  · intro p hp
    exact measurableSet_Icc.inter measurableSet_Icc
  · intro p hp t ht hne
    have hpQ := ((arcIndices_mem491 Q p).mp hp).2.1
    have htQ := ((arcIndices_mem491 Q t).mp ht).2.1
    have hsum : (p.1 : ℝ) + t.1 < τ := by
      have hpr : (p.1 : ℝ) ≤ Q := by exact_mod_cast hpQ
      have htr : (t.1 : ℝ) ≤ Q := by exact_mod_cast htQ
      linarith
    have hd := rational_arcs_disjoint491 (p.2 : ℤ) (t.2 : ℤ) p.1 t.1
      ((arcIndices_mem491 Q p).mp hp).1 ((arcIndices_mem491 Q t).mp ht).1
      (arcIndices_cross_ne491 Q p t hp ht hne) τ hsum
    exact hd.mono Set.inter_subset_right Set.inter_subset_right
  · intro p hp
    exact hf.integrableOn_Icc.mono_set Set.inter_subset_left

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. Translation converts a full rational arc integral to its symmetric local coordinate integral. -/
theorem rational_arc_integral491 (q a : ℕ) (hq : 1 ≤ q) (τ : ℝ) (hτ : 0 < τ)
    (f : ℝ → ℂ) :
    (∫ α in rationalArc491 q a τ, f α) =
      ∫ z in -(1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)), f ((a : ℝ) / q + z) := by
  have hR : 0 ≤ 1 / ((q : ℝ) * τ) := by positivity
  unfold rationalArc491
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  rw [intervalIntegral.integral_comp_add_left]
  congr 1 <;> ring

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. For denominator at least two, every reduced representative arc lies inside the unit interval. -/
theorem interior_arc_subset491 (q a : ℕ) (hq : 2 ≤ q) (ha : a < q)
    (hc : Nat.Coprime a q) (τ : ℝ) (hτ : 1 ≤ τ) :
    rationalArc491 q a τ ⊆ Set.Icc 0 1 := by
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
theorem unit_arc_join491 (τ : ℝ) (hτ : 2 < τ) (f : ℝ → ℂ)
    (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc491 1 0 τ, f α) +
      (∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc491 1 1 τ, f α) =
      ∫ z in -(1 / τ)..(1 / τ), f z := by
  let R : ℝ := 1 / τ
  have hτ0 : 0 < τ := by linarith
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := (div_le_one hτ0).mpr (by linarith)
  have hh : Set.Icc (0 : ℝ) 1 ∩ rationalArc491 1 0 τ = Set.Icc 0 R := by
    ext α
    simp only [rationalArc491, Nat.cast_one, Nat.cast_zero, zero_div, one_mul, zero_sub,
      zero_add, Set.mem_inter_iff, Set.mem_Icc]
    dsimp [R] at *
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.1, h2.2⟩
    · intro h
      constructor <;> constructor <;> linarith [h.1, h.2]
  have ht : Set.Icc (0 : ℝ) 1 ∩ rationalArc491 1 1 τ = Set.Icc (1 - R) 1 := by
    ext α
    simp only [rationalArc491, Nat.cast_one, div_one, one_mul, Set.mem_inter_iff, Set.mem_Icc]
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
theorem denominator_arc_sum491 (q : ℕ) (hq : 1 ≤ q) (τ : ℝ) (hτ : 2 < τ)
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∑ a ∈ (Icc 0 q).filter (fun a => Nat.Coprime a q),
      ∫ α in Set.Icc (0 : ℝ) 1 ∩ rationalArc491 q a τ, f α) =
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ∫ z in -(1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)), f ((a : ℝ) / q + z) := by
  classical
  by_cases hq1 : q = 1
  · subst q
    have hi : (Icc 0 (1 : ℕ)).filter (fun a => Nat.Coprime a 1) = {0, 1} := by decide
    have hr : (range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
    rw [hi, hr]
    simpa using unit_arc_join491 τ hτ f hf hp
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
    have hsub := interior_arc_subset491 q a hq2 (mem_range.mp has) hac τ (by linarith)
    rw [Set.inter_eq_right.mpr hsub]
    exact rational_arc_integral491 q a hq τ (by linarith) f

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. The pair index sum equals the iterated denominator and reduced numerator sum. -/
theorem arcIndices_sum491 (Q : ℕ) (H : ℕ × ℕ → ℂ) :
    (∑ p ∈ arcIndices491 Q, H p) =
      ∑ q ∈ Icc 1 Q, ∑ a ∈ (Icc 0 q).filter (fun a => Nat.Coprime a q), H (q, a) := by
  classical
  simp only [arcIndices491, Finset.sum_filter, Finset.sum_product]
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
theorem rational_partition491 (Q : ℕ) (hQ : 1 ≤ Q) (τ : ℝ)
    (hτ : 2 * (Q : ℝ) < τ) (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ α in rationalMajor491 Q τ, f α) =
      ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * τ))..(1 / ((q : ℝ) * τ)), f ((a : ℝ) / q + z) := by
  rw [rational_clipped_integral491 Q hQ τ hτ f hf, arcIndices_sum491]
  apply Finset.sum_congr rfl
  intro q hq
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  exact denominator_arc_sum491 q (mem_Icc.mp hq).1 τ (by linarith) f hf hp

/-- LEAF. P0093 page 165 equation 8.1 and page 166 equation 8.2. Above two to power seventy the chosen tau exceeds twice the integer Q. -/
theorem major_parameters_separated491 (N : ℕ) (hN : 2 ^ 70 < N) :
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
theorem major_arc_partition_proved491 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ f : ℝ → ℂ,
      Continuous f → Function.Periodic f 1 →
      (∫ α in majorArcs280 N, f α) =
        ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
                (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
              f ((a : ℝ) / q + z) := by
  refine ⟨2 ^ 70, ?_⟩
  intro N hN f hf hp
  have hsep := major_parameters_separated491 N hN
  have heq : majorArcs280 N = rationalMajor491 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊
      ((N : ℝ) ^ (1 / 7 : ℝ)) := by
    ext α
    simp only [majorArcs280, rationalMajor491, Set.mem_setOf_eq,
      Nat.le_floor_iff (show 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) by positivity)]
  rw [heq]
  exact rational_partition491 _ hsep.1 _ hsep.2 f hf hp

end LeanLab.Linnik1951
