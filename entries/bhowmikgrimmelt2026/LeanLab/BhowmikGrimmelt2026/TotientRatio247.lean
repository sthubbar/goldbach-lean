module

public import Mathlib
public import LeanLab.BhowmikGrimmelt2026.DecompJ249

/-!
Elementary arithmetic for the twisted Ramanujan bound in Pintz Part I page 11 display 4.3.
This supplies the totient ratio step for the fixed data coefficient bound.
The induced Gauss sum identities remain OPEN in Decomp247a.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Multiplying a modulus by m increases its totient by at most a factor m.
Source: elementary helper for Pintz Part I page 11 display 4.3. -/
theorem totient_mul_le247 (m n : ℕ) : Nat.totient (m * n) ≤ m * Nat.totient n := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · subst m; simp
    by_cases hm1 : m = 1
    · subst m; simp
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hklt : m / p < m := Nat.div_lt_self hmpos hp.one_lt
    have hmk : p * (m / p) = m := Nat.mul_div_cancel' hpm
    have hrec := ih (m / p) hklt
    have hprime : Nat.totient (p * (m / p * n)) ≤ p * Nat.totient (m / p * n) := by
      by_cases hd : p ∣ m / p * n
      · rw [Nat.totient_mul_of_prime_of_dvd hp hd]
      · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd]
        exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)
    calc
      Nat.totient (m * n) = Nat.totient (p * (m / p * n)) := by rw [← mul_assoc, hmk]
      _ ≤ p * Nat.totient (m / p * n) := hprime
      _ ≤ p * (m / p * Nat.totient n) := Nat.mul_le_mul_left p hrec
      _ = m * Nat.totient n := by rw [← mul_assoc, hmk]

/-- Dividing a positive modulus by a positive divisor gives a totient ratio at most that divisor.
Source: elementary helper for Pintz Part I page 11 display 4.3. -/
theorem totient_divisor_ratio247 (q d : ℕ) (hq : 0 < q) (hd : d ∣ q) (hdpos : 0 < d) :
    (Nat.totient q : ℝ) / (Nat.totient (q / d) : ℝ) ≤ d := by
  have hquot : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hd) hdpos
  have hphi : (0 : ℝ) < Nat.totient (q / d) := by exact_mod_cast Nat.totient_pos.mpr hquot
  apply (div_le_iff₀ hphi).mpr
  have h := totient_mul_le247 d (q / d)
  rw [Nat.mul_div_cancel' hd] at h
  exact_mod_cast h

/-- The totient quotient in the twisted Ramanujan formula is at most positive N.
Source: Pintz Part I page 11 display 4.3 with q one equal q divided by gcd of q and N. -/
theorem totient_gcd_ratio247 (q N : ℕ) (hq : 0 < q) (hN : 0 < N) :
    (Nat.totient q : ℝ) / (Nat.totient (q / Nat.gcd q N) : ℝ) ≤ N := by
  have h := totient_divisor_ratio247 q (Nat.gcd q N) hq
    (Nat.gcd_dvd_left q N) (Nat.gcd_pos_of_pos_left N hq)
  exact h.trans (by exact_mod_cast Nat.gcd_le_right q hN)


open Filter Topology

/-- The coefficient of display 6.4 extended by zero at modulus zero. -/
noncomputable def aqZero247 {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (N : ℤ) (q : ℕ) : ℂ :=
  if h : q = 0 then 0 else @Aq r₁ r₂ χ₁ χ₂ N q ⟨h⟩


/-- The zero extension adds no modulus zero coefficient. -/
theorem aqZero247_zero {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ) :
    aqZero247 χ₁ χ₂ N 0 = 0 := by
  simp [aqZero247]


/-- At a positive modulus the extension is the original coefficient. -/
theorem aqZero247_succ {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ) (q : ℕ) :
    aqZero247 χ₁ χ₂ N (q + 1) = Aq χ₁ χ₂ N (q + 1) := by
  simp [aqZero247]


/-- A modulus outside the conductor divisibility restriction contributes zero.
Source: P0029 page 23 display 6.4 and Pintz Part I page 19 display 7.9. -/
theorem aqZero247_eq_zero_of_not_lcm_dvd {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (N : ℤ) (q : ℕ) (hq : ¬ Nat.lcm r₁ r₂ ∣ q) :
    aqZero247 χ₁ χ₂ N q = 0 := by
  by_cases hzero : q = 0
  · simp [aqZero247, hzero]
  · have hd : ¬ (r₁ ∣ q ∧ r₂ ∣ q) := by
      simpa only [Nat.lcm_dvd_iff] using hq
    simp [aqZero247, hzero, Aq, hd]


/-- A reciprocal totient square coefficient bound gives absolute summability.
This implication uses only the proved seventh power totient estimate and the p series test. -/
theorem aqZero247_norm_summable_of_bound {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ q : ℕ, 0 < q →
      ‖aqZero247 χ₁ χ₂ N q‖ ≤ C * (1 / (Nat.totient q : ℝ) ^ 2)) :
    Summable (fun q : ℕ => ‖aqZero247 χ₁ χ₂ N q‖) := by
  have hs : Summable (fun q : ℕ => C * (7 * (q : ℝ) ^ (-(7 : ℝ) / 4))) :=
    ((Real.summable_nat_rpow.mpr (by norm_num : (-(7 : ℝ) / 4) < -1)).mul_left 7).mul_left C
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _ hs
  intro q
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst q
    simp only [aqZero247_zero, norm_zero]
    positivity
  · exact (hbound q hq).trans (mul_le_mul_of_nonneg_left
      (LeanLab.Zinoviev1997.inv_totient_sq_seven q hq) hC)


/-- Removing the zero coefficient recovers exactly the positive modulus series. -/
theorem aqZero247_tsum {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    (hsum : Summable (aqZero247 χ₁ χ₂ N)) :
    (∑' q : ℕ, aqZero247 χ₁ χ₂ N q) = genSing χ₁ χ₂ N := by
  rw [hsum.tsum_eq_zero_add, aqZero247_zero, zero_add]
  simp only [aqZero247_succ, genSing]


/-- Smooth modulus sums tend to the full series under the explicit summability hypothesis.
This uses Mathlib's smooth number tail estimate and no arithmetic leaf. -/
theorem aqZero247_smooth_tendsto {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    (hsum : Summable (aqZero247 χ₁ χ₂ N)) :
    Tendsto (fun X : ℕ => ∑' q : X.smoothNumbers, aqZero247 χ₁ χ₂ N q)
      atTop (𝓝 (genSing χ₁ χ₂ N)) := by
  rw [← aqZero247_tsum χ₁ χ₂ N hsum, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := EulerProduct.norm_tsum_smoothNumbers_sub_tsum_lt
    hsum (aqZero247_zero χ₁ χ₂ N) hε
  refine ⟨X₀, fun X hX => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact hX₀ X hX


end LeanLab.BhowmikGrimmelt2026

