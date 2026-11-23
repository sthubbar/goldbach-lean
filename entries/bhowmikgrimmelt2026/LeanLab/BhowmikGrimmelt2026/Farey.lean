module

public import LeanLab.BhowmikGrimmelt2026.Periodicity

/-!
Farey separation used in Lemma 7.2, page 26.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Distances to the integers satisfy the triangle inequality for subtraction. -/
theorem intDist_sub_le (x y : ℝ) : intDist (x - y) ≤ intDist x + intDist y := by
  calc
    _ ≤ |x - y - ((round x - round y : ℤ) : ℝ)| := intDist_le_abs_sub _ _
    _ = |(x - round x) - (y - round y)| := by push_cast; congr 1; ring
    _ ≤ |x - round x| + |y - round y| := abs_sub _ _

/-- Distinct rationals with positive natural denominators have determinant separation. -/
theorem rational_separation {a b : ℤ} {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hne : a * (r : ℤ) ≠ b * (q : ℤ)) :
    1 / ((q : ℝ) * r) ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hint : (1 : ℤ) ≤ |a * (r : ℤ) - b * (q : ℤ)| := by
    have hpos : (0 : ℤ) < |a * (r : ℤ) - b * (q : ℤ)| := abs_pos.mpr (sub_ne_zero.mpr hne)
    omega
  have hreal : (1 : ℝ) ≤ |((a * (r : ℤ) - b * (q : ℤ) : ℤ) : ℝ)| := by
    exact_mod_cast hint
  have heq : (a : ℝ) / q - (b : ℝ) / r =
      ((a * (r : ℤ) - b * (q : ℤ) : ℤ) : ℝ) / ((q : ℝ) * r) := by
    push_cast
    field_simp
    <;> ring
  rw [heq, abs_div, abs_of_pos (mul_pos hqp hrp)]
  exact div_le_div_of_nonneg_right hreal (by positivity)

/-- A reduced fraction with positive denominator uniquely determines numerator and denominator. -/
theorem reduced_fraction_unique {a q b r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (haq : Nat.Coprime a q) (hbr : Nat.Coprime b r)
    (heq : (a : ℝ) / q = (b : ℝ) / r) : a = b ∧ q = r := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hcross : a * r = b * q := by
    have h := (div_eq_div_iff hqp.ne' hrp.ne').mp heq
    exact_mod_cast h
  have hqr : q ∣ r := haq.symm.dvd_mul_left.mp (by rw [hcross]; exact ⟨b, by ring⟩)
  have hrq : r ∣ q := hbr.symm.dvd_mul_left.mp (by rw [← hcross]; exact ⟨a, by ring⟩)
  have hden : q = r := Nat.dvd_antisymm hqr hrq
  subst r
  exact ⟨mul_right_cancel₀ hq.ne' hcross, rfl⟩

/-- Reduced residues remain distinct after arbitrary integer translations. -/
theorem reduced_fraction_add_int_unique {a q b r : ℕ} (ha : a < q) (hb : b < r)
    (haq : Nat.Coprime a q) (hbr : Nat.Coprime b r) (k l : ℤ)
    (heq : (a : ℝ) / q + k = (b : ℝ) / r + l) : a = b ∧ q = r ∧ k = l := by
  have hq : 0 < q := by omega
  have hr : 0 < r := by omega
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have ha0 : (0 : ℝ) ≤ (a : ℝ) / q := by positivity
  have hb0 : (0 : ℝ) ≤ (b : ℝ) / r := by positivity
  have ha1 : (a : ℝ) / q < 1 := (div_lt_one hqp).mpr (by exact_mod_cast ha)
  have hb1 : (b : ℝ) / r < 1 := (div_lt_one hrp).mpr (by exact_mod_cast hb)
  have hsmall : |((k - l : ℤ) : ℝ)| < 1 := by
    rw [Int.cast_sub, abs_lt]
    constructor <;> linarith
  have hsmallInt : |k - l| < 1 := by exact_mod_cast hsmall
  have hbnds := abs_lt.mp hsmallInt
  have hkl : k = l := by omega
  have heq' : (a : ℝ) / q = (b : ℝ) / r := by rw [hkl] at heq; linarith
  obtain ⟨hab, hqr⟩ := reduced_fraction_unique hq hr haq hbr heq'
  exact ⟨hab, hqr, hkl⟩

/-- Distinct reduced residues are separated modulo integers by at least one over q r. -/
theorem farey_intDist_separation {a q b r : ℕ} (ha : a < q) (hb : b < r)
    (haq : Nat.Coprime a q) (hbr : Nat.Coprime b r) (hne : (a, q) ≠ (b, r)) :
    1 / ((q : ℝ) * r) ≤ intDist ((a : ℝ) / q - (b : ℝ) / r) := by
  let k : ℤ := round ((a : ℝ) / q - (b : ℝ) / r)
  have hq : 0 < q := by omega
  have hr : 0 < r := by omega
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hdet : (a : ℤ) * r ≠ ((b : ℤ) + k * r) * q := by
    intro heq
    have hc : (a : ℝ) * r = ((b : ℝ) + (k : ℝ) * r) * q := by exact_mod_cast heq
    have heq' : (a : ℝ) / q + (0 : ℤ) = (b : ℝ) / r + k := by
      push_cast
      field_simp
      nlinarith only [hc]
    have h := reduced_fraction_add_int_unique ha hb haq hbr 0 k heq'
    exact hne (Prod.ext h.1 h.2.1)
  have h := rational_separation hq hr hdet
  have hexpr : (a : ℝ) / q - (((b : ℤ) + k * r : ℤ) : ℝ) / r =
      ((a : ℝ) / q - (b : ℝ) / r) - k := by
    push_cast
    field_simp
    <;> ring
  push_cast at h
  change 1 / ((q : ℝ) * r) ≤ |((a : ℝ) / q - (b : ℝ) / r) - k|
  convert h using 1
  congr 1
  field_simp
  <;> ring

/-- There are at most M squared reduced residue pairs with denominator at most M. -/
theorem reduced_card_sum_le (M : ℕ) :
    ∑ q ∈ Finset.Icc 1 M, ((Finset.range q).filter (fun a => Nat.Coprime a q)).card ≤ M ^ 2 := by
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 M, M := by
      apply Finset.sum_le_sum
      intro q hq
      exact (Finset.card_filter_le _ _).trans (by simpa using (Finset.mem_Icc.mp hq).2)
    _ = M ^ 2 := by simp [Nat.card_Icc, pow_two]

end LeanLab.BhowmikGrimmelt2026
