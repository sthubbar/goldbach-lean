module

public import LeanLab.PNTPort.StrongPNT.StrongPNT

/-! Lab bridge, AI-written Lean, not part of the PrimeNumberTheoremAnd port.
   Restates the ported `StrongPNT` in the explicit-constant form the lab uses for
   Siegel-Walfisz at modulus 1, valid for every x ≥ 2. -/

@[expose] public section

namespace LeanLab.PNTPort

open Real Filter Asymptotics

/-- The prime number theorem with de la Vallée Poussin error term, in explicit-constant form:
there are `c > 0` and `K` with `|ψ(x) - x| ≤ K x exp(-c √(log x))` for all `x ≥ 2`. -/
theorem psi_explicit_strong : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    |Chebyshev.psi x - x| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hO⟩ := StrongPNT
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp hC
  set X := max x0 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  set m := 2 * Real.exp (-c * Real.sqrt (Real.log X)) with hm
  have hmpos : 0 < m := by positivity
  refine ⟨c, hc, max C ((Chebyshev.psi X + X) / m), fun x hx => ?_⟩
  have hxpos : 0 < x := by linarith
  have hE : 0 < x * Real.exp (-c * Real.sqrt (Real.log x)) := by positivity
  rcases le_total X x with hXx | hxX
  · have h := hx0 x (le_trans (le_max_left _ _) hXx)
    simp only [Pi.sub_apply, id, Real.norm_eq_abs] at h
    rw [← Real.sqrt_eq_rpow, abs_of_pos hE] at h
    calc |Chebyshev.psi x - x| ≤ C * (x * Real.exp (-c * Real.sqrt (Real.log x))) := h
      _ ≤ max C ((Chebyshev.psi X + X) / m) * (x * Real.exp (-c * Real.sqrt (Real.log x))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le
      _ = _ := by ring
  · have h1 : |Chebyshev.psi x - x| ≤ Chebyshev.psi X + X := by
      have := Chebyshev.psi_nonneg x
      have := Chebyshev.psi_mono hxX
      rw [abs_le]; constructor <;> linarith
    have h2 : m ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      have hl : Real.log x ≤ Real.log X := Real.log_le_log hxpos hxX
      have hs : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hl
      have he : Real.exp (-c * Real.sqrt (Real.log X)) ≤ Real.exp (-c * Real.sqrt (Real.log x)) := by
        apply Real.exp_le_exp.mpr; nlinarith
      exact mul_le_mul hx he (by positivity) (by linarith)
    have h0 : 0 ≤ Chebyshev.psi X + X := by have := Chebyshev.psi_nonneg X; linarith
    have hK : Chebyshev.psi X + X ≤
        (Chebyshev.psi X + X) / m * (x * Real.exp (-c * Real.sqrt (Real.log x))) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hmpos]
      exact mul_le_mul_of_nonneg_left h2 h0
    calc |Chebyshev.psi x - x| ≤ Chebyshev.psi X + X := h1
      _ ≤ (Chebyshev.psi X + X) / m * (x * Real.exp (-c * Real.sqrt (Real.log x))) := hK
      _ ≤ max C ((Chebyshev.psi X + X) / m) * (x * Real.exp (-c * Real.sqrt (Real.log x))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hE.le
      _ = _ := by ring

end LeanLab.PNTPort
