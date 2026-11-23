module

public import LeanLab.BhowmikGrimmelt2026.ReducedPairs

/-!
Normalize the major arc numerator to a reduced residue, page 26.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Every integer reduced fraction has a canonical reduced residue representative. -/
theorem reduced_residue_of_int {q : ℕ} (hq : 0 < q) {a : ℤ} (ha : Int.gcd a q = 1) :
    ∃ b : ℕ, b < q ∧ Nat.Coprime b q ∧ ∃ k : ℤ,
      (a : ℝ) / q = (b : ℝ) / q + k := by
  let b : ℕ := (a % (q : ℤ)).toNat
  have hqi : (0 : ℤ) < q := by exact_mod_cast hq
  have hnonneg := Int.emod_nonneg a hqi.ne'
  have hb : (b : ℤ) = a % q := Int.toNat_of_nonneg hnonneg
  have hblt : b < q := by
    have h := Int.emod_lt_of_pos a hqi
    rw [← hb] at h
    exact_mod_cast h
  have hcop : Nat.Coprime b q := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    have h : Int.gcd (b : ℤ) q = 1 := by rw [hb, Int.gcd_emod]; exact ha
    simpa using h
  refine ⟨b, hblt, hcop, a / q, ?_⟩
  have heq := Int.emod_add_mul_ediv a (q : ℤ)
  rw [← hb] at heq
  have her : (b : ℝ) + (q : ℝ) * ((a / q : ℤ) : ℝ) = a := by exact_mod_cast heq
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  field_simp
  nlinarith only [her]

/-- A major arc contains a canonical reduced pair with small weighted integer distance. -/
theorem majorArc_pair {N R α : ℝ} (hN : 0 < N) (hR : 1 ≤ R)
    (hmajor : MajorArc N R α) :
    ∃ p ∈ reducedPairs ⌊R⌋₊,
      (p.1 : ℝ) * intDist (α - p.2 / p.1) ≤ R / N := by
  obtain ⟨q, hq, hqR, a, ha, hα⟩ := hmajor
  obtain ⟨b, hb, hcop, k, heq⟩ := reduced_residue_of_int (by omega : 0 < q) ha
  have hqM : q ≤ ⌊R⌋₊ := Nat.le_floor hqR
  refine ⟨⟨q, b⟩, (mem_reducedPairs _ _).mpr ⟨hq, hqM, hb, hcop⟩, ?_⟩
  have hd : intDist (α - (b : ℝ) / q) ≤ |α - (a : ℝ) / q| := by
    have h := intDist_le_abs_sub (α - (b : ℝ) / q) k
    convert h using 1
    congr 1
    linarith only [heq]
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have h := mul_le_mul_of_nonneg_left (hd.trans hα) hqp.le
  calc
    _ ≤ (q : ℝ) * (R / ((q : ℝ) * N)) := h
    _ = R / N := by field_simp

end LeanLab.BhowmikGrimmelt2026
