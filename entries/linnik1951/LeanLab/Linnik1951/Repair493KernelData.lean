module

public import LeanLab.Linnik1951.Repair493MellinData

/-!
P0093 page 156 equation 4.1. Sealed Mellin kernel data moved before its mass proof.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 156 equation 4.1. The Mellin kernel before its coefficient M.
The factor one over two pi remains outside this kernel. -/
noncomputable def mellinKernel442 (N : ℕ) (α t : ℝ) : ℂ :=
  (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
    (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)

/-- LEAF. P0093 page 156 equation 4.1. A line bound on M bounds the
Mellin integral by B0 over two pi times its absolute weighted kernel
mass. This is the norm integral inequality alone. -/
theorem mellin_kernel_domination442 (N : ℕ) (α B0 : ℝ) (hB0 : 0 ≤ B0)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M)
    (hI : Integrable (fun t : ℝ => ‖mellinKernel442 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :
    ‖mellinU1622 N M α‖ ≤ (1 / (2 * Real.pi)) * B0 *
      (∫ t : ℝ, ‖mellinKernel442 N α t‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hb (t : ℝ) : ‖mellinKernel442 N α t * M t‖ ≤
      B0 * (‖mellinKernel442 N α t‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left (hM.2 t) (norm_nonneg (mellinKernel442 N α t))
    nlinarith
  have hnorm := norm_integral_le_of_norm_le (hI.const_mul B0) (Filter.Eventually.of_forall hb)
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ, mellinKernel442 N α t * M t)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        (∫ t : ℝ, B0 * (‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

/-- LEAF. P0093 page 158 before equation 4.8. Square root N is at
most N over square root R when one is at most R at most N. -/
theorem sqrt_scale442 (N R : ℝ) (hN : 0 < N) (hR : 0 < R) (hRN : R ≤ N) :
    Real.sqrt N ≤ N / Real.sqrt R := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hR)).mpr
  calc
    Real.sqrt N * Real.sqrt R ≤ Real.sqrt N * Real.sqrt N := by
      gcongr
    _ = N := Real.mul_self_sqrt hN.le

end LeanLab.Linnik1951
