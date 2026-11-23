module

public import LeanLab.Linnik1951.Decomp357a

/-!
P0093 page 156 equations 4.1 and 4.2. Sealed Mellin data and its zero instance.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- P0093 page 156 Lemma 2. The line s equal to 1/2 + 1/ln N + i t. -/
noncomputable def mellinLine1622 (N : ℕ) (t : ℝ) : ℂ :=
  ((1 / 2 + 1 / Real.log N : ℝ) : ℂ) + (t : ℂ) * Complex.I

/-- P0093 page 156 equation 4.1. U of alpha for a coefficient M on the line,
written over the real variable t. The factor 1 over 2 pi i and ds equal to i dt
leave 1 over 2 pi. -/
noncomputable def mellinU1622 (N : ℕ) (M : ℝ → ℂ) (α : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
    (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^ (-(mellinLine1622 N t)) *
      Complex.Gamma (mellinLine1622 N t) * M t

/-- P0093 page 156 Lemma 2 hypothesis. M is continuous on the line and bounded by
B0 times ln cubed of N times the sum of |t| and 2. -/
def LineBound1622 (N : ℕ) (B0 : ℝ) (M : ℝ → ℂ) : Prop :=
  Continuous M ∧ ∀ t : ℝ, ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3

/-- Vacuity instance for LineBound1622: the zero coefficient satisfies it. -/
theorem lineBound_zero1622 (N : ℕ) (B0 : ℝ) (hB0 : 0 ≤ B0) (hN : 1 ≤ N) :
    LineBound1622 N B0 (fun _ => 0) := by
  refine ⟨continuous_const, fun t => ?_⟩
  have h1 : (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [abs_nonneg t]
  have := Real.log_nonneg h1
  simp only [norm_zero]
  positivity

end LeanLab.Linnik1951
