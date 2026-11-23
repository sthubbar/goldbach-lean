module

public import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a

/-!
Jutila 1977, page 46, display 1.8, specialized to the box in P0045 display 8.
The density estimate stays an explicit analytic hypothesis.
Only its elementary exponential envelope is proved here.
Source: https://doi.org/10.7146/math.scand.a-11701.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real

/-- Jutila page 46, display 1.8 at epsilon one half and alpha equal to one minus H over log X.
For T at most P at most sqrt X the resulting envelope is at most exp of 4H. -/
theorem density_envelope_le481 {X P T H : ℝ} (hX : 1 < X) (hH : 0 ≤ H)
    (hT : 1 ≤ T) (hTP : T ≤ P) (hPX : P ≤ Real.sqrt X) :
    (P ^ 2 * T) ^ ((5 / 2 : ℝ) * H / Real.log X) ≤ Real.exp (4 * H) := by
  have hP : 0 < P := lt_of_lt_of_le (by linarith : (0 : ℝ) < T) hTP
  have hT0 : 0 < T := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogP : Real.log P ≤ Real.log X / 2 := by
    calc Real.log P ≤ Real.log (Real.sqrt X) := Real.log_le_log hP hPX
      _ = Real.log X / 2 := Real.log_sqrt (by linarith)
  have hlogT : Real.log T ≤ Real.log P := Real.log_le_log hT0 hTP
  have hbase : Real.log (P ^ 2 * T) ≤ (3 / 2 : ℝ) * Real.log X := by
    rw [Real.log_mul (by positivity : P ^ 2 ≠ 0) (ne_of_gt hT0), Real.log_pow]
    linarith
  have hexp : 0 ≤ (5 / 2 : ℝ) * H / Real.log X := by positivity
  have hmul := mul_le_mul_of_nonneg_right hbase hexp
  have hid : ((3 / 2 : ℝ) * Real.log X) * ((5 / 2 : ℝ) * H / Real.log X) =
      (15 / 4 : ℝ) * H := by field_simp; ring
  rw [hid] at hmul
  rw [Real.rpow_def_of_pos (by positivity : 0 < P ^ 2 * T)]
  apply Real.exp_le_exp.mpr
  linarith

/-- Jutila page 46, display 1.8, to P0045 page 5, the bound following display 8.
This bridge counts analytic multiplicities and stays CONDITIONAL on the rectangle density input.
The cutoff in that input includes alpha at least four fifths and sufficiently large X. -/
theorem jutila_of_rectangle_density481
    (hrect : ∃ C : ℝ, 0 ≤ C ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
        T ≤ P → P ≤ Real.sqrt X →
        ∀ F : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          (∀ z ∈ F, z ∈ zeroBox481 X H T P) →
          (∑ z ∈ F, (analyticOrderNatAt (Lfun481 z.2.1) z.2.2 : ℝ)) ≤
            C * (P ^ 2 * T) ^ ((5 / 2 : ℝ) * H / Real.log X)) :
    JutilaStatement481 := by
  obtain ⟨C, hC, hrect⟩ := hrect
  refine ⟨C, hC, fun H T hH hT => ?_⟩
  obtain ⟨X₀, hX₀⟩ := hrect H T hH hT
  refine ⟨max X₀ 2, fun X hX P hTP hPX F hF => ?_⟩
  have hX2 : 2 ≤ X := (le_max_right _ _).trans hX
  have hXreal : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  exact (hX₀ X ((le_max_left _ _).trans hX) P hTP hPX F hF).trans
    (mul_le_mul_of_nonneg_left (density_envelope_le481 hXreal (by linarith) hT hTP hPX) hC)

end LeanLab.LPZ2007

