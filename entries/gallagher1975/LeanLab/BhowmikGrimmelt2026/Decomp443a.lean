module

public import LeanLab.BhowmikGrimmelt2026.InducedGauss443
public import LeanLab.BhowmikGrimmelt2026.ReducedFrequency443
public import LeanLab.BhowmikGrimmelt2026.PrimitiveSums436

/-!
Supply for the residue fiber norm and coefficient majorant.
Source: Montgomery Vaughan 1975 printed pages 358 to 360, display 5.1.
Pintz Part I page 11 display 4.3 and page 20 display 7.13.
Existing statements remain sealed.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF. Montgomery Vaughan page 358 Lemma 5.2, the norm of the induced Gauss formula.
Pintz Part I page 11 display 4.1.
Only frequency one is involved and no gcd or totient quotient occurs. -/
theorem cChi_lift_one_norm443 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hd : r ∣ q) :
    ‖cChi (DirichletCharacter.changeLevel hd χ) 1‖ ≤ ‖cChi χ 1‖ := by
  simpa only [cChi_int_gauss436, Int.cast_one, AddChar.mulShift_one] using
    gaussSum_lift_norm443 χ hd

/-- Exact twisted_fiber_bound436 statement from the proved residue reduction and prime lifts.
Source: Montgomery Vaughan page 360, display 5.1. -/
theorem twisted_fiber_bound_supply443 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hd : r ∣ q)
    (N : ℤ) (hgood : r ∣ q / Nat.gcd q N.natAbs) :
    ‖cChi (DirichletCharacter.changeLevel hd χ) N‖ ≤
      (Nat.totient q : ℝ) / (Nat.totient (q / Nat.gcd q N.natAbs) : ℝ) *
        Real.sqrt r := by
  let m := q / Nat.gcd q N.natAbs
  have hmpos : 0 < m := Nat.div_pos (Nat.gcd_le_left N.natAbs
    (Nat.pos_of_ne_zero (NeZero.ne q)))
      (Nat.gcd_pos_of_pos_left N.natAbs (Nat.pos_of_ne_zero (NeZero.ne q)))
  haveI : NeZero m := ⟨hmpos.ne'⟩
  have hmq : m ∣ q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q N.natAbs)
  let ψ := DirichletCharacter.changeLevel hgood χ
  have he := cChi_gcd_factor443 ψ N rfl
  rw [← DirichletCharacter.changeLevel_trans χ hgood hmq] at he
  have hnorm : ‖cChi (DirichletCharacter.changeLevel hd χ) N‖ =
      (Nat.totient q : ℝ) / (Nat.totient m : ℝ) *
        ‖cChi ψ (N / (Nat.gcd q N.natAbs : ℤ))‖ := by
    rw [he, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  have hunit := gcd_frequency_unit443 (q := q) N
  have hψ : ‖cChi ψ (N / (Nat.gcd q N.natAbs : ℤ))‖ ≤ Real.sqrt r := by
    rw [cChi_unit_norm443 ψ _ hunit]
    exact (cChi_lift_one_norm443 χ hgood).trans (cChi_primitive_bound436 χ hχ 1)
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left hψ (by positivity)

/-- The positive frequency bound follows by the two residue fiber alternatives.
Source: Pintz page 20 display 7.13 and the totient quotient in display 4.3.
The residue fiber norm is proved in this file. -/
theorem twisted_primitive_bound443 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hd : r ∣ q)
    (N : ℤ) (hN : 1 ≤ N) :
    ‖cChi (DirichletCharacter.changeLevel hd χ) N‖ ≤
      (N.natAbs : ℝ) * Real.sqrt r := by
  by_cases hgood : r ∣ q / Nat.gcd q N.natAbs
  · exact (twisted_fiber_bound_supply443 χ hχ hd N hgood).trans
      (mul_le_mul_of_nonneg_right (totient_gcd_ratio247 q N.natAbs
        (Nat.pos_of_ne_zero (NeZero.ne q))
        (Int.natAbs_pos.mpr (by omega))) (Real.sqrt_nonneg _))
  · rw [twisted_fiber_vanish436 χ hχ hd N hgood, norm_zero]
    positivity

/-- Passing to the primitive character gives the same bound at any fixed source level.
Source: the primitive inducing character in Pintz page 11 Lemma 4.4.
The residue fiber norm is proved in this file. -/
theorem twisted_lift_bound443 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hd : r ∣ q) (N : ℤ) (hN : 1 ≤ N) :
    ‖cChi (DirichletCharacter.changeLevel hd χ) N‖ ≤
      (N.natAbs : ℝ) * Real.sqrt r := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := twisted_primitive_bound443 χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
    (χ.conductor_dvd_level.trans hd) N hN
  rw [DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level hd,
    DirichletCharacter.changeLevel_primitiveCharacter] at h
  have hcr : (χ.conductor : ℝ) ≤ r := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne r)) χ.conductor_dvd_level
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcr) (by positivity))

/-- The lifted conjugate Gauss norm is bounded by the square root of its source level.
Source: Pintz page 11 Lemmas 4.1 to 4.4, frequency one specialization.
The residue fiber norm is proved in this file. -/
theorem tau_lift_bound443 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hd : r ∣ q) :
    ‖tauConj (DirichletCharacter.changeLevel hd χ)‖ ≤ Real.sqrt r := by
  rw [tauConj_eq_cChi_inv436, ← map_inv]
  simpa using twisted_lift_bound443 χ⁻¹ hd 1 (by norm_num)

/-- Exact aqZero247_totient_bound statement assembled from the proved residue fiber identities.
The coefficient bound has no cited input.
Source: Pintz page 20 display 7.13. No original coefficient leaf is used. -/
theorem aqZero247_totient_supply443 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (N : ℤ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 0 < q →
      ‖aqZero247 χ₁ χ₂ N q‖ ≤ C * (1 / (Nat.totient q : ℝ) ^ 2) := by
  refine ⟨Real.sqrt r₁ * Real.sqrt r₂ * ((N.natAbs : ℝ) * Real.sqrt (Nat.lcm r₁ r₂)),
    by positivity, ?_⟩
  intro q hq
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero (Nat.lcm r₁ r₂) := ⟨Nat.lcm_ne_zero (NeZero.ne r₁) (NeZero.ne r₂)⟩
  by_cases hd : r₁ ∣ q ∧ r₂ ∣ q
  · have h₁ := tau_lift_bound443 χ₁ hd.1
    have h₂ := tau_lift_bound443 χ₂ hd.2
    have h₃ := twisted_lift_bound443 (χ₁.mul χ₂) (Nat.lcm_dvd hd.1 hd.2) N hN
    rw [lifted_product436 χ₁ χ₂ hd.1 hd.2] at h₃
    have hn := mul_le_mul h₁ h₂ (norm_nonneg _) (Real.sqrt_nonneg _)
    have hn' := mul_le_mul hn h₃ (norm_nonneg _) (by positivity)
    simp only [aqZero247, dif_neg (Nat.ne_of_gt hq), Aq, dif_pos hd, norm_div, norm_mul,
      norm_pow, Complex.norm_natCast]
    calc
      _ ≤ (Real.sqrt r₁ * Real.sqrt r₂ * ((N.natAbs : ℝ) * Real.sqrt (Nat.lcm r₁ r₂))) /
          (Nat.totient q : ℝ) ^ 2 := div_le_div_of_nonneg_right hn' (by positivity)
      _ = _ := by ring
  · simp [aqZero247, Nat.ne_of_gt hq, Aq, hd]
    positivity

end LeanLab.BhowmikGrimmelt2026

