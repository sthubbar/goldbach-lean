module

public import LeanLab.BhowmikGrimmelt2026.GaussReduction443
public import LeanLab.BhowmikGrimmelt2026.Decomp436a

/-!
The gcd frequency used in Montgomery Vaughan 1975 pages 359 and 360.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Dividing the modulus and integer frequency by their gcd produces a unit frequency.
Source: Montgomery Vaughan page 359, definition of m1 and q1. -/
theorem gcd_frequency_unit443 {q : ℕ} [NeZero q] (N : ℤ) :
    IsUnit ((N / (Nat.gcd q N.natAbs : ℤ) : ℤ) : ZMod (q / Nat.gcd q N.natAbs)) := by
  have hg : 0 < Nat.gcd q N.natAbs := Nat.gcd_pos_of_pos_left _
    (Nat.pos_of_ne_zero (NeZero.ne q))
  have h := Int.gcd_ediv_gcd_ediv_gcd (i := (q : ℤ)) (j := N) (by
    simpa only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast] using hg)
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one]
  simpa only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast, ← Int.natCast_ediv] using h

/-- A unit frequency changes a Gauss sum by a character value of norm one.
Source: Montgomery Vaughan page 358 Lemma 5.3, its first equality. -/
theorem cChi_unit_norm443 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (M : ℤ) (hM : IsUnit (M : ZMod q)) :
    ‖cChi χ M‖ = ‖cChi χ 1‖ := by
  rw [cChi_int_gauss436, ← hM.unit_spec, gaussSum_mulShift_eq, norm_mul,
    DirichletCharacter.unit_norm_eq_one, one_mul, cChi_int_gauss436]
  simp

/-- Exact gcd frequency reduction for a lifted character.
Source: Montgomery Vaughan page 360, the first displayed formula. -/
theorem cChi_gcd_factor443 {m q : ℕ} [NeZero m] [NeZero q]
    (χ : DirichletCharacter ℂ m) (N : ℤ)
    (hm : m = q / Nat.gcd q N.natAbs) :
    cChi (DirichletCharacter.changeLevel
        (hm ▸ Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q N.natAbs)) χ) N =
      ((Nat.totient q : ℂ) / (Nat.totient m : ℂ)) *
        cChi χ (N / (Nat.gcd q N.natAbs : ℤ)) := by
  have hg : (Nat.gcd q N.natAbs : ℤ) ∣ N :=
    Int.natCast_dvd.mpr (Nat.gcd_dvd_right q N.natAbs)
  have hq : q = m * Nat.gcd q N.natAbs := by
    rw [hm, Nat.div_mul_cancel (Nat.gcd_dvd_left q N.natAbs)]
  have hN : (Nat.gcd q N.natAbs : ℤ) * (N / (Nat.gcd q N.natAbs : ℤ)) = N :=
    Int.mul_ediv_cancel' hg
  convert cChi_factor443 χ
    (hm ▸ Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q N.natAbs))
    (Nat.gcd q N.natAbs) hq (N / (Nat.gcd q N.natAbs : ℤ)) using 1
  rw [hN]

end LeanLab.BhowmikGrimmelt2026

