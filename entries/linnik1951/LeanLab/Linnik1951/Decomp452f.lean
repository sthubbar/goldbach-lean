module

public import LeanLab.Linnik1951.Decomp452e

/-!
Original page 158 radial substitution and equation 4.6.
The positive Jacobian is antitone away from its singular endpoint.
The vector valued second mean value theorem then reduces the weighted integral
back to the signed radial primitive with its logarithmic diagonal factor.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open MeasureTheory

/-- The radial substitution Jacobian in page 158 equation 4.6. -/
noncomputable def radialJacobian452 (N u : ℝ) : ℝ :=
  1 / Real.sqrt (1 - 1 / (N ^ 2 * u ^ 2))

/-- The radial Jacobian is positive and at most two once N u is at least two. -/
theorem radial_jacobian_bounds452 (N u : ℝ) (hN : 0 < N) (hu : 0 < u)
    (hNu : 2 ≤ N * u) :
    0 < radialJacobian452 N u ∧ radialJacobian452 N u ≤ 2 := by
  have h4 : (4 : ℝ) ≤ N ^ 2 * u ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hNu 2
    norm_num only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
    exact h
  have hr : 1 / (N ^ 2 * u ^ 2) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) h4
  have hp : 0 < 1 - 1 / (N ^ 2 * u ^ 2) := by linarith
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt (1 - 1 / (N ^ 2 * u ^ 2)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  constructor
  · exact div_pos one_pos (Real.sqrt_pos.mpr hp)
  · dsimp [radialJacobian452]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hp)).mpr
    linarith

/-- The radial Jacobian is antitone on the positive interval starting at two over N. -/
theorem radial_jacobian_antitone452 (N : ℝ) (hN : 0 < N) :
    AntitoneOn (radialJacobian452 N) (Set.Ici (2 / N)) := by
  intro u hu v hv huv
  have hup : 0 < u := (div_pos (by norm_num) hN).trans_le hu
  have hvp : 0 < v := hup.trans_le huv
  have hNu : 2 ≤ N * u := by
    have h := (div_le_iff₀ hN).mp hu
    nlinarith
  have hbase : 0 < Real.sqrt (1 - 1 / (N ^ 2 * u ^ 2)) :=
    one_div_pos.mp (radial_jacobian_bounds452 N u hN hup hNu).1
  have hs : N ^ 2 * u ^ 2 ≤ N ^ 2 * v ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hup.le huv 2) (sq_nonneg N)
  have hi := one_div_le_one_div_of_le (by positivity : 0 < N ^ 2 * u ^ 2) hs
  have hsqrt : Real.sqrt (1 - 1 / (N ^ 2 * u ^ 2)) ≤
      Real.sqrt (1 - 1 / (N ^ 2 * v ^ 2)) := Real.sqrt_le_sqrt (by linarith)
  exact one_div_le_one_div_of_le hbase hsqrt

/-- The weighted radial integral obeys a signed primitive bound with a logarithmic diagonal factor. -/
theorem radial_jacobian_integral_bound452 (N a b ε d : ℝ) (hN : 0 < N)
    (ha : 2 / N ≤ a) (hab : a ≤ b) (hε : 0 < ε) :
    ‖∫ u : ℝ in a..b, radialJacobian452 N u •
        (u : ℂ) ^ (-((1 + ε : ℝ) : ℂ) - (d : ℂ) * Complex.I)‖ ≤
      8 * a ^ (-ε) * (1 + Real.log (b / a)) / (1 + |d|) := by
  have hap : 0 < a := (div_pos (by norm_num) hN).trans_le ha
  have hbp : 0 < b := hap.trans_le hab
  have hNa : 2 ≤ N * a := by have h := (div_le_iff₀ hN).mp ha; nlinarith
  have hNb : 2 ≤ N * b := by nlinarith
  have hja := radial_jacobian_bounds452 N a hN hap hNa
  have hjb := radial_jacobian_bounds452 N b hN hbp hNb
  have hanti : AntitoneOn (radialJacobian452 N) (Set.Icc a b) := by
    intro u hu v hv huv
    exact radial_jacobian_antitone452 N hN (ha.trans hu.1) (ha.trans hv.1) huv
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    linarith [h.1]
  have hg : IntervalIntegrable
      (fun u : ℝ => (u : ℂ) ^ (-((1 + ε : ℝ) : ℂ) - (d : ℂ) * Complex.I))
      volume a b := intervalIntegral.intervalIntegrable_cpow (Or.inr hzero)
  obtain ⟨ξ, hξ, hmean⟩ :=
    exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn hab hjb.1.le hanti hg
  have hξp : 0 < ξ := hap.trans_le hξ.1
  have hinner := radial_mellin_uniform_bound452 a ξ ε d hap hξ.1 hε
  have hlog : Real.log (ξ / a) ≤ Real.log (b / a) :=
    Real.log_le_log (div_pos hξp hap) (div_le_div_of_nonneg_right hξ.2 hap.le)
  have hbigger : 4 * a ^ (-ε) * (1 + Real.log (ξ / a)) / (1 + |d|) ≤
      4 * a ^ (-ε) * (1 + Real.log (b / a)) / (1 + |d|) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by positivity)
  have hprod := mul_le_mul hja.2 (hinner.trans hbigger) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ 2 * (4 * a ^ (-ε) * (1 + Real.log (b / a)) / (1 + |d|)) := hmean.trans hprod
    _ = _ := by ring

end LeanLab.Linnik1951
