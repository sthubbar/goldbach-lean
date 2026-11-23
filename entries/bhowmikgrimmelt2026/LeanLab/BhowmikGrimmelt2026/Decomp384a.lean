module

public import Mathlib

/-!
Finite convolution comparison for removal of higher prime powers.
Source: P0029 page 4, the omitted higher prime power contribution.
This general comparison is a derived helper, not a printed paper theorem.
It does not prove either sealed DecompJ1034 leaf.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- A bounded nonnegative convolution changes by at most twice the bound times
its total input defect. Derived helper for P0029 page 4. -/
theorem convolution_defect_le384 (N : ℕ) (f g : ℕ → ℝ) (B : ℝ)
    (h : ∀ k ≤ N, 0 ≤ g k ∧ g k ≤ f k ∧ f k ≤ B) :
    (∑ k ∈ Finset.range (N + 1), f k * f (N - k)) -
        (∑ k ∈ Finset.range (N + 1), g k * g (N - k)) ≤
      2 * B * ∑ k ∈ Finset.range (N + 1), (f k - g k) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
      f k * f (N - k) - g k * g (N - k) ≤
        B * ((f k - g k) + (f (N - k) - g (N - k))) := by
    have hkN : k ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    obtain ⟨hgk, hgfk, hfk⟩ := h k hkN
    obtain ⟨hgj, hgfj, hfj⟩ := h (N - k) (Nat.sub_le N k)
    calc
      _ = (f k - g k) * f (N - k) + g k * (f (N - k) - g (N - k)) := by ring
      _ ≤ (f k - g k) * B + B * (f (N - k) - g (N - k)) :=
        add_le_add (mul_le_mul_of_nonneg_left hfj (sub_nonneg.mpr hgfk))
          (mul_le_mul_of_nonneg_right (hgfk.trans hfk) (sub_nonneg.mpr hgfj))
      _ = _ := by ring
  have hreflect : (∑ k ∈ Finset.range (N + 1), (f (N - k) - g (N - k))) =
      ∑ k ∈ Finset.range (N + 1), (f k - g k) := by
    simpa only [Nat.add_sub_cancel] using
      (Finset.sum_range_reflect (fun k => f k - g k) (N + 1))
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1),
        B * ((f k - g k) + (f (N - k) - g (N - k))) := Finset.sum_le_sum hterm
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib, hreflect]; ring

end LeanLab.BhowmikGrimmelt2026
