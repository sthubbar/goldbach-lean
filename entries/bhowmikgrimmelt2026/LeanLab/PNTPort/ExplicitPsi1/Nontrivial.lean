module

public import LeanLab.PNTPort.ExplicitPsi1.Final

/-!
# `Zall` is the set of nontrivial zeros

Lab proof, unit U-5320, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
no cited input. ζ has no zero with `-1/2 ≤ Re s ≤ 0`, by the functional equation, so the zeros
with `Re ρ ≥ -1/2` are exactly the zeros in the open strip `0 < Re ρ < 1`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1

open Complex

local notation "ζ" => riemannZeta

/-- ζ has no zero with `-1/2 ≤ Re s ≤ 0`. -/
theorem zeta_ne_zero_left {s : ℂ} (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 0) : ζ s ≠ 0 := by
  rcases eq_or_lt_of_le h2 with h0 | hneg
  · by_cases him : s.im = 0
    · have : s = 0 := Complex.ext h0 him
      rw [this, riemannZeta_zero]; norm_num
    · exact ZetaZeros.zeta_ne_zero_of_re_nonpos h2 him
  set w := 1 - s with hw
  have hwre : w.re = 1 - s.re := by rw [hw]; simp
  have hw1 : w ≠ 1 := by intro h; have := congr_arg re h; simp at this; linarith
  have e : ζ s = ZetaZeros.feF w * ζ w := by
    have := riemannZeta_one_sub (ZetaZeros.not_neg_nat_of_re_pos (by linarith : 0 < w.re)) hw1
    rw [show 1 - w = s by rw [hw]; ring] at this
    rw [this]; rfl
  have hodd : ∀ k : ℤ, w ≠ 2 * k + 1 := by
    intro k hk
    have hre := congr_arg Complex.re hk
    simp at hre
    have a : (0 : ℝ) < k := by linarith
    have b : (k : ℝ) < 1 / 2 := by linarith
    have a' : (0 : ℤ) < k := by exact_mod_cast a
    have b' : k < 1 := by
      have : (k : ℝ) < 1 := by linarith
      exact_mod_cast this
    omega
  rw [e]
  exact mul_ne_zero (ZetaZeros.feF_ne_zero (by linarith) hodd)
    (riemannZeta_ne_zero_of_one_le_re (by linarith))

/-- `Zall` is the set of zeros of ζ in the open critical strip. -/
theorem Zall_eq : Zall = {ρ : ℂ | ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} := by
  ext ρ
  constructor
  · rintro ⟨hz, hre⟩
    refine ⟨hz, ?_, Zall_re_lt ⟨hz, hre⟩⟩
    by_contra h
    exact zeta_ne_zero_left hre (not_lt.mp h) hz
  · rintro ⟨hz, h0, _⟩
    exact ⟨hz, by linarith⟩

end LeanLab.PNTPort.ExplicitPsi1

