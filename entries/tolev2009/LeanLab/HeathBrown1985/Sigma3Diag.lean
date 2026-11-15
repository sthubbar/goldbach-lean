module

public import Mathlib
public import LeanLab.HeathBrown1985.Sigma2

/-!
P0096 Heath-Brown 1985, pages 55 to 56, the diagonal 3.6 for Σ₃, in the counting form: for
`1 ≤ r ≤ x`, `Σ_{2x<m≤3x} Σ_n f_m(rn)² ≤ (2x/r) Σ_{k ≤ x} Δ_Q(k)²`, each class mod `r`
covered at most `2x/r` times.
PROVED here, fully proved.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset

attribute [local instance] Classical.propDecidable

/-- One `m`: the map `n ↦ m - rn` sends the support into the class of `m` mod `r` in `[1, x]`. -/
theorem diag_inner_le (x : ℝ) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (r N m : ℕ) (hr : 1 ≤ r) :
    ∑ n ∈ Icc 1 N, (if (m : ℝ) - x ≤ ((r * n : ℕ) : ℝ) ∧ r * n < m then
        g (m - r * n) else 0) ≤
      ∑ k ∈ (Icc 1 ⌊x⌋₊).filter (fun k => k % r = m % r), g k := by
  rw [← sum_filter]
  set F := (Icc 1 N).filter
    (fun n => (m : ℝ) - x ≤ ((r * n : ℕ) : ℝ) ∧ r * n < m)
  have hlt : ∀ n ∈ F, r * n < m := by
    intro n hn
    exact (mem_filter.mp hn).2.2
  have hinj : Set.InjOn (fun n => m - r * n) (F : Set ℕ) := by
    intro n₁ h₁ n₂ h₂ h
    have a1 := hlt n₁ h₁
    have a2 := hlt n₂ h₂
    have : r * n₁ = r * n₂ := by simp only at h; omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have himg := sum_image (f := g) hinj
  rw [← himg]
  apply sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    have hl := hlt n hn
    have hc := (mem_filter.mp hn).2.1
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · apply Nat.le_floor
      rw [Nat.cast_sub hl.le]
      linarith
    · have e : m = (m - r * n) + r * n := by omega
      conv_rhs => rw [e]
      rw [Nat.add_mul_mod_self_left]
  · intro k _ _; exact hg k

/-- The diagonal count: `Σ_m Σ_n [m - x ≤ rn < m] g(m - rn) ≤ (2x/r) Σ_{k ≤ x} g(k)`. -/
theorem diag_sum_le (x : ℝ) (hx : 1 ≤ x) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (r N : ℕ)
    (hr : 1 ≤ r) (hrx : (r : ℝ) ≤ x) :
    ∑ m ∈ mRange x, ∑ n ∈ Icc 1 N,
        (if (m : ℝ) - x ≤ ((r * n : ℕ) : ℝ) ∧ r * n < m then g (m - r * n) else 0) ≤
      2 * x / r * ∑ k ∈ Icc 1 ⌊x⌋₊, g k := by
  refine (sum_le_sum (fun m _ => diag_inner_le x g hg r N m hr)).trans ?_
  simp_rw [sum_filter]
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro k _
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm, mul_comm (2 * x / (r : ℝ)) (g k)]
  apply mul_le_mul_of_nonneg_left _ (hg k)
  have := card_mRange_mod_le x hx r (k % r) hr hrx
  have e : (mRange x).filter (fun m => k % r = m % r) = (mRange x).filter (fun m => m % r = k % r) := by
    ext m; simp only [mem_filter]; constructor <;> (rintro ⟨a, b⟩; exact ⟨a, b.symm⟩)
  rw [e]; exact this

/-- 3.6 in counting form for `f_m`: `Σ_m Σ_n f_m(rn)² ≤ (2x/r) Σ_{k ≤ x} Δ_Q(k)²`. -/
theorem diag_fm_sq_le (x Q : ℝ) (hx : 1 ≤ x) (r N : ℕ) (hr : 1 ≤ r) (hrx : (r : ℝ) ≤ x) :
    ∑ m ∈ mRange x, ∑ n ∈ Icc 1 N, fm x Q m (r * n) ^ 2 ≤
      2 * x / r * ∑ k ∈ Icc 1 ⌊x⌋₊, DeltaQ Q k ^ 2 := by
  have e : ∀ m n, fm x Q m (r * n) ^ 2 =
      (if (m : ℝ) - x ≤ ((r * n : ℕ) : ℝ) ∧ r * n < m then
        DeltaQ Q (m - r * n) ^ 2 else 0) := by
    intro m n; unfold fm
    by_cases h : (m : ℝ) - x ≤ ((r * n : ℕ) : ℝ) ∧ r * n < m
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; ring
  simp_rw [e]
  exact diag_sum_le x hx (fun k => DeltaQ Q k ^ 2) (fun k => sq_nonneg _) r N hr hrx

end LeanLab.HeathBrown1985
