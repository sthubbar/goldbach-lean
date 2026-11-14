module

public import LeanLab.BhowmikGrimmelt2026.Decomp436a
public import LeanLab.BhowmikGrimmelt2026.PrimeValues247
public import LeanLab.PNTPort.LargeSieve.Multiplicative

/-!
Primitive finite sum cases for the residue fiber supply.
Source: Pintz Part I page 11 Lemmas 4.1 to 4.4.
The primitive Gauss norm is reused from the PNTPort tree.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- The primitive twisted sum has norm square root q at a unit frequency and zero otherwise.
Source: Pintz page 11 Lemmas 4.1 and 4.3, including the primitive vanishing case. -/
theorem cChi_primitive_norm436 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (N : ℤ) :
    ‖cChi χ N‖ = if IsUnit (N : ZMod q) then Real.sqrt q else 0 := by
  classical
  have hnorm : ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ = Real.sqrt q := by
    rw [← LeanLab.PNTPort.LargeSieve.normSq_gaussSum_of_isPrimitive hχ,
      Real.sqrt_sq (norm_nonneg _)]
  rw [cChi_int_gauss436, gaussSum_mulShift_of_isPrimitive _ hχ, norm_mul, hnorm]
  by_cases hu : IsUnit (N : ZMod q)
  · rw [if_pos hu, ← hu.unit_spec, DirichletCharacter.unit_norm_eq_one, one_mul]
  · rw [if_neg hu, MulChar.map_nonunit _ hu, norm_zero, zero_mul]

/-- Primitive twisted sums are bounded uniformly over every integer frequency.
Source: Pintz page 11 Lemmas 4.1 and 4.3. -/
theorem cChi_primitive_bound436 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (N : ℤ) :
    ‖cChi χ N‖ ≤ Real.sqrt q := by
  rw [cChi_primitive_norm436 χ hχ N]
  split_ifs
  · exact le_rfl
  · exact Real.sqrt_nonneg _

/-- The primitive conjugate Gauss sum has the exact square root norm.
Source: Pintz page 11 Lemma 4.1 with conjugate character. -/
theorem tauConj_primitive_norm436 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖tauConj χ‖ = Real.sqrt q := by
  have hinv : χ⁻¹.IsPrimitive := by
    simpa only [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv] using hχ
  rw [tauConj_eq_cChi_inv436, cChi_primitive_norm436 χ⁻¹ hinv]
  simp

/-- The norm leaf is proved when the target modulus equals the primitive source level.
Source: Montgomery Vaughan page 360, the final primitive Gauss sum step of display 5.1.
The proper lift fiber formula remains OPEN in Decomp436a. -/
theorem twisted_fiber_same_level436 {r : ℕ} [NeZero r]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (N : ℤ)
    (hgood : r ∣ r / Nat.gcd r N.natAbs) :
    ‖cChi (DirichletCharacter.changeLevel (dvd_refl r) χ) N‖ ≤
      (Nat.totient r : ℝ) / (Nat.totient (r / Nat.gcd r N.natAbs) : ℝ) *
        Real.sqrt r := by
  have heq : r = r / Nat.gcd r N.natAbs := Nat.dvd_antisymm hgood
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r N.natAbs))
  have hphi : (Nat.totient r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne r))).ne'
  rw [← heq, div_self hphi, one_mul, DirichletCharacter.changeLevel_self]
  exact cChi_primitive_bound436 χ hχ N

/-- At a prime target level the principal character has the exact residue fiber norm.
Source: Montgomery Vaughan pages 359 and 360 display 5.1, conductor one case.
The two prime twisted sum values are reused from PrimeValues247. -/
theorem principal_prime_fiber_norm436 (p N : ℕ) (hp : p.Prime) :
    ‖@cChi p ⟨hp.ne_zero⟩ (1 : DirichletCharacter ℂ p) N‖ =
      (Nat.totient p : ℝ) / (Nat.totient (p / Nat.gcd p N) : ℝ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hphi : (Nat.totient p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
  by_cases hd : p ∣ N
  · have hg : Nat.gcd p N = p := Nat.gcd_eq_left_iff_dvd.mpr hd
    rw [cChi_principal_prime_dvd247 p N hp hd, hg, Nat.div_self hp.pos,
      Nat.totient_one, Nat.cast_one, div_one]
    simp
  · have hg : Nat.gcd p N = 1 := hp.coprime_iff_not_dvd.mpr hd
    rw [cChi_principal_prime_not_dvd247 p N hp hd, hg, Nat.div_one,
      div_self hphi, norm_neg, norm_one]

/-- The coefficient triangle budget cannot be bounded by a fixed inverse totient square.
This is a failed bound comparison, not a statement about the actual coefficients.
Source: derived route check for Pintz page 20 display 7.13. -/
theorem triangle_budget_not_uniform436 (C : ℝ) (hC : 0 ≤ C) :
    ∃ q : ℕ, 0 < q ∧ C * (1 / (Nat.totient q : ℝ) ^ 2) < Nat.totient q := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 1 + 2)
  obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes n
  have hpnR : (n : ℝ) ≤ p := by exact_mod_cast hpn
  have hphi : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hphi1 : 1 ≤ (Nat.totient p : ℝ) := by
    rw [hphi]
    linarith [le_max_right C 1]
  have hCphi : C < (Nat.totient p : ℝ) := by
    rw [hphi]
    linarith [le_max_left C 1]
  have hsq : (0 : ℝ) < (Nat.totient p : ℝ) ^ 2 := by positivity
  have hdiv : C / (Nat.totient p : ℝ) ^ 2 ≤ C := by
    apply (div_le_iff₀ hsq).mpr
    exact le_mul_of_one_le_right hC (one_le_pow₀ hphi1)
  refine ⟨p, hp.pos, ?_⟩
  simpa only [mul_one_div] using hdiv.trans_lt hCphi

end LeanLab.BhowmikGrimmelt2026

