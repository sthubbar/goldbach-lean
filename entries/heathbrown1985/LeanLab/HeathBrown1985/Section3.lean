module

public import Mathlib
public import LeanLab.HeathBrown1985.Vaughan
public import LeanLab.HeathBrown1985.Statements

/-!
P0096 Heath-Brown 1985, section 3, pages 53 to 55: the sum
`Σ = Σ_{2x < m ≤ 3x} |Σ_{n ≤ x} Δ_Q(n) Λ(m - n)|` split by Vaughan's identity 3.1 with
`N = 3x`, `u = Q`, `v = x Q⁻²`, `f(n) = Δ_Q(m - n)` for `m - x ≤ n < m`, else `0`.
PROVED here: `Σ ≤ Σ₁ + Σ₂ + Σ₃`. STATED: the bounds (3.2) for Σ₁ and the bound for Σ₂.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-- `f_m(n) = Δ_Q(m - n)` for `m - x ≤ n < m`, else `0`. -/
def fm (x Q : ℝ) (m : ℕ) : ℕ → ℝ :=
  fun n => if (m : ℝ) - x ≤ n ∧ n < m then DeltaQ Q (m - n) else 0

/-- The `m` range `2x < m ≤ 3x`. -/
def mRange (x : ℝ) : Finset ℕ := (Icc 1 ⌊3 * x⌋₊).filter (fun m => 2 * x < (m : ℝ))

/-- `Σ = Σ_{2x < m ≤ 3x} |Σ_{n ≤ x} Δ_Q(n) Λ(m - n)|`, the start of section 3. -/
def Sigma (x Q : ℝ) : ℝ :=
  ∑ m ∈ mRange x, |∑ n ∈ Icc 1 ⌊x⌋₊, DeltaQ Q n * Λ (m - n)|

/-- `Σᵢ = Σ_m |Sᵢ|` with `N = ⌊3x⌋`, `u = ⌊Q⌋`, `v = ⌊x/Q²⌋`. -/
def Sigma1 (x Q : ℝ) : ℝ := ∑ m ∈ mRange x, |S1 ⌊Q⌋₊ ⌊3 * x⌋₊ (fm x Q m)|
def Sigma2 (x Q : ℝ) : ℝ := ∑ m ∈ mRange x, |S2 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m)|
def Sigma3 (x Q : ℝ) : ℝ := ∑ m ∈ mRange x, |S3 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m)|

/-- For `2x < m ≤ 3x`, the left side of Vaughan's identity with `f = f_m` is the inner sum of `Σ`. -/
theorem vaughan_lhs_eq (x Q : ℝ) (hx : 1 ≤ x) (hQ : 1 ≤ Q) (m : ℕ) (hm : m ∈ mRange x) :
    ∑ n ∈ (Icc 1 ⌊3 * x⌋₊).filter (⌊x / Q ^ 2⌋₊ < ·), fm x Q m n * Λ n =
      ∑ n ∈ Icc 1 ⌊x⌋₊, DeltaQ Q n * Λ (m - n) := by
  simp only [mRange, mem_filter, mem_Icc] at hm
  obtain ⟨⟨hm1, hm3⟩, hm2⟩ := hm
  have hx0 : 0 < x := by linarith
  have hV : (⌊x / Q ^ 2⌋₊ : ℝ) ≤ x := by
    refine (Nat.floor_le (by positivity)).trans ?_
    have hQ2 : 1 ≤ Q ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hmR : (m : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast hm3) (Nat.floor_le (by linarith))
  have hfxm : ⌊x⌋₊ < m := by
    have : (⌊x⌋₊ : ℝ) < m := by linarith
    exact_mod_cast this
  -- restrict to the support of `f_m`
  rw [← sum_filter_ne_zero]
  symm
  rw [← sum_filter_ne_zero]
  apply Finset.sum_nbij' (fun n => m - n) (fun n => m - n)
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hnx⟩, hne⟩ := hn
    have hnR : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnx) hfx
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hlt : n < m := by omega
    have hsubR : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := by push_cast [hlt.le]; ring
    refine ⟨⟨⟨by omega, ?_⟩, ?_⟩, ?_⟩
    · have : (m - n : ℕ) ≤ m := Nat.sub_le m n
      exact this.trans hm3
    · have : (⌊x / Q ^ 2⌋₊ : ℝ) < ((m - n : ℕ) : ℝ) := by rw [hsubR]; linarith
      exact_mod_cast this
    · unfold fm
      rw [hsubR, if_pos ⟨by linarith, by omega⟩, Nat.sub_sub_self hlt.le]
      exact hne
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    obtain ⟨⟨⟨hn1, hnN⟩, hnV⟩, hne⟩ := hn
    unfold fm at hne
    split_ifs at hne with hc
    · obtain ⟨h1, h2⟩ := hc
      have hlt : n < m := by exact_mod_cast h2
      have hsubR : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := by push_cast [hlt.le]; ring
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · have : ((m - n : ℕ) : ℝ) ≤ x := by rw [hsubR]; linarith
        exact Nat.le_floor this
      · rw [Nat.sub_sub_self hlt.le]; exact hne
    · exact absurd (zero_mul _) hne
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    exact Nat.sub_sub_self (by omega)
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨_, hne⟩ := hn
    unfold fm at hne
    split_ifs at hne with hc
    · exact Nat.sub_sub_self (by exact_mod_cast hc.2.le)
    · exact absurd (zero_mul _) hne
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    have hlt : n < m := by omega
    have hsubR : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := by push_cast [hlt.le]; ring
    have hnR : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hn.1.2) hfx
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
    unfold fm
    rw [hsubR, if_pos ⟨by linarith, by omega⟩, Nat.sub_sub_self hlt.le]

/-- **`Σ ≤ Σ₁ + Σ₂ + Σ₃`**, by Vaughan's identity, page 53. -/
theorem Sigma_le_sum (x Q : ℝ) (hx : 1 ≤ x) (hQ : 1 ≤ Q) :
    Sigma x Q ≤ Sigma1 x Q + Sigma2 x Q + Sigma3 x Q := by
  unfold Sigma Sigma1 Sigma2 Sigma3
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum; intro m hm
  rw [← vaughan_lhs_eq x Q hx hQ m hm, vaughan ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊
    (Nat.le_floor (by exact_mod_cast hQ))]
  calc _ ≤ |S1 ⌊Q⌋₊ ⌊3 * x⌋₊ (fm x Q m) - S2 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m)| +
        |S3 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m)| := abs_sub _ _
    _ ≤ _ := by
        have := abs_sub (S1 ⌊Q⌋₊ ⌊3 * x⌋₊ (fm x Q m)) (S2 ⌊Q⌋₊ ⌊x / Q ^ 2⌋₊ ⌊3 * x⌋₊ (fm x Q m))
        linarith

/-- (3.2): `Σ₁ ≪ x² L⁶ Q⁻¹` for `Q = L^B`, any fixed `B > 0`. Stated. -/
def Bound3_2 : Prop :=
  ∀ B : ℝ, 0 < B → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    Sigma1 x (Real.log x ^ B) ≤ K * x ^ 2 * Real.log x ^ 6 / Real.log x ^ B

/-- Page 54: `Σ₂ ≪ x² Q^{-1/2} L⁸` for `Q = L^B`. Stated. -/
def BoundSigma2 : Prop :=
  ∀ B : ℝ, 0 < B → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    Sigma2 x (Real.log x ^ B) ≤ K * x ^ 2 * (Real.log x ^ B) ^ (-(1 : ℝ) / 2) * Real.log x ^ 8

end LeanLab.HeathBrown1985
