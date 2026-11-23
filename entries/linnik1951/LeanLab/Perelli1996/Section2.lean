module

public import LeanLab.Perelli1996.Definitions88
public import LeanLab.Perelli1996.Kernel

/-!
P0083, page 482. The Weyl lemma is a cited analytic input.
The parameter choice below is elementary arithmetic for pages 481, 482 and 486.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Section2
open Finset Real Polynomial

noncomputable section

/-- K of F and alpha on the paper's polynomial window, page 480. -/
def polynomialKernel (F : ℤ[X]) (N H α : ℝ) : ℂ :=
  ∑ n ∈ win F N H, Kernel.e ((Fv F n : ℝ) * α)

/-- Weyl exponent K equals two to the degree minus one. -/
def weylExponent (F : ℤ[X]) : ℝ := (2 : ℝ) ^ (F.natDegree - 1)

/-- Cited Weyl lemma, page 482. No proof of Vaughan's inputs is assumed here. -/
def WeylLemma (F : ℤ[X]) : Prop :=
  Admissible F → ∀ D : ℝ, 0 < D → ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧
    ∀ N H α : ℝ, N₀ ≤ N → 1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
    ∀ a : ℤ, ∀ q : ℕ, 0 < q → Nat.Coprime a.natAbs q →
      |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
      ‖polynomialKernel F N H α‖ ≤
        C * H * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree +
          Real.log N ^ (-2 * D + (F.natDegree : ℝ) ^ 2 - 2)) ^ (1 / weylExponent F) *
        Real.log N ^ ((D + 1) / weylExponent F)

/-- One explicit B makes all three final logarithmic errors save L to the A. -/
theorem parameter_choice {A c k K : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hk : 1 ≤ k) (hK : 1 ≤ K) :
    let B := 8 * K * (A + 2) + 4 * k ^ 2 + c + A + 1
    0 < B ∧
      -2 * B + c ≤ -A ∧
      -(B - 4 * k ^ 2 - 16 * K) / (8 * K) ≤ -A ∧
      -(B - k ^ 2 - 2 * K) / (2 * K) ≤ -A ∧
      0 < B / 8 + k ^ 2 / 2 - 1 ∧
      0 < (B + k ^ 2) / 2 - 1 := by
  dsimp
  have hKA : 0 ≤ K * A := mul_nonneg (by linarith) hA
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_, ?_, by nlinarith, by nlinarith⟩
  · apply (div_le_iff₀ (by linarith : 0 < 8 * K)).2
    nlinarith
  · apply (div_le_iff₀ (by linarith : 0 < 2 * K)).2
    nlinarith

/-- Heavy divisor weights are controlled by their second moment, equation 7. -/
theorem heavy_weight_cutoff {ι : Type*} (s : Finset ι) (τ u : ι → ℝ) {T U : ℝ}
    (hT : 0 < T) (hU : 0 ≤ U) (hτ : ∀ i ∈ s, 0 ≤ τ i)
    (hu : ∀ i ∈ s, u i ≤ U) :
    ∑ i ∈ s.filter (fun i => T < τ i), τ i * u i ≤
      U / T * ∑ i ∈ s, τ i ^ 2 := by
  classical
  have hterm : ∀ i ∈ s.filter (fun i => T < τ i),
      τ i * u i ≤ U / T * τ i ^ 2 := by
    intro i hi
    obtain ⟨his, hit⟩ := Finset.mem_filter.mp hi
    have hnon := hτ i his
    have h1 := mul_le_mul_of_nonneg_left (hu i his) hnon
    have h2 : τ i * U ≤ U / T * τ i ^ 2 := by
      apply (mul_le_mul_iff_right₀ hT).mp
      have heq : T * (U / T * τ i ^ 2) = U * τ i ^ 2 := by field_simp
      rw [heq]
      nlinarith [mul_nonneg hU (mul_nonneg hnon (le_of_lt (sub_pos.mpr hit)))]
    exact h1.trans h2
  calc ∑ i ∈ s.filter (fun i => T < τ i), τ i * u i
      ≤ ∑ i ∈ s.filter (fun i => T < τ i), U / T * τ i ^ 2 := Finset.sum_le_sum hterm
    _ = U / T * ∑ i ∈ s.filter (fun i => T < τ i), τ i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ U / T * ∑ i ∈ s, τ i ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hU hT.le)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => sq_nonneg _)

end
end LeanLab.Perelli1996.Section2
