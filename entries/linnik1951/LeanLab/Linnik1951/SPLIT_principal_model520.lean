module

public import LeanLab.Linnik1951.Decomp520a
public import LeanLab.Linnik1951.PrincipalTail491
public import LeanLab.Linnik1951.LogFourierMass491
public import LeanLab.Linnik1951.PrimeArcRadius520
public import LeanLab.Linnik1951.ArcCross520

/-!
Split of the sealed model comparison at the principal arc, unit
Linnik1951/Decomp520a, theorem principal_model520.

The sealed bound compares the short arc principal square integral with the full
period square of the model series, and carries two error terms: one inverse of
q times the seventh root of N, and one inverse of the square root of the same
quantity. The cut gives one leaf per term. The first leaf replaces the principal
square by the model square on the short arc. The second leaf extends that short
arc to a full period, which is where the square root term is lost. The assembly
adds the two bounds with the triangle inequality and adds the constants.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- Range facts the assembly needs: on this range the seventh root of N is
positive, N is positive and the logarithm of N is nonnegative. -/
private theorem split_range520 {N : ℕ} (hN : 3 < N) :
    1 ≤ N ∧ (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) ∧ 0 < (N : ℝ) ∧ 0 ≤ Real.log N := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  exact ⟨hN1, Real.rpow_pos_of_pos hNpos _, hNpos, Real.log_nonneg (by exact_mod_cast hN1)⟩

/-- Scale facts for the short arc, standard real arithmetic. With lam the fourth
root of N and R the product of q and the seventh root of N, on the range of the
leaf R lies between two and lam, lam is at least one, its fourth power is N, the
square of q is at most N and the logarithm of N is at least one. -/
private theorem arc_scale520 {N q : ℕ} (hN : 128 < N) (hq : 1 ≤ q)
    (hqQ : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    2 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ∧
      (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) ∧
      1 ≤ (N : ℝ) ^ (1 / 4 : ℝ) ∧
      (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) *
        ((N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ)) = (N : ℝ) ∧
      (q : ℝ) ^ 2 ≤ (N : ℝ) ∧ 1 ≤ Real.log N := by
  have hn : (128 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hτ2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
    have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128) hn
      (by norm_num : (0 : ℝ) ≤ 1 / 7)
    have he : (128 : ℝ) ^ (1 / 7 : ℝ) = 2 := by
      rw [show (128 : ℝ) = 2 ^ (7 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [he] at hh
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlam1 : 1 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have h4 : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) *
      ((N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ)) = (N : ℝ) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    norm_num
  have hR : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h1 : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤
        (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_right hqQ (Real.rpow_nonneg hN0.le _)
    have h2 : (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    exact h1.trans h2
  have hq4 : (q : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    hqQ.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
  have hq2 : (q : ℝ) ^ 2 ≤ (N : ℝ) := by
    have ha : (q : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by nlinarith
    have hb : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) := by nlinarith
    exact ha.trans hb
  have hl : 1 ≤ Real.log N := by
    have hN3' : (3 : ℝ) < N := by linarith
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3').le
  exact ⟨by nlinarith, hR, hlam1, h4, hq2, hl⟩

/-- Real arithmetic collecting the four terms of the arc comparison into the
single term of the leaf. -/
private theorem arc_collect520 (C N R lam l13 : ℝ) (hC : 0 < C) (hN : 0 < N)
    (hR : 0 < R) (hRlam : R ≤ lam) (hl : 1 ≤ l13) :
    3 * (C * N / R * l13) + 2 * N * (1 / R) + lam * (C * N / (lam * lam) * l13) +
        2 * N / lam ≤ (4 * C + 4) * N * l13 * (1 / R) := by
  have hlam : 0 < lam := lt_of_lt_of_le hR hRlam
  have hy : N / lam ≤ N / R := div_le_div_of_nonneg_left hN.le hR hRlam
  have hy0 : 0 ≤ N / lam := by positivity
  have hx0 : 0 ≤ N / R := by positivity
  have e1 : lam * (C * N / (lam * lam) * l13) = C * l13 * (N / lam) := by
    field_simp
  have e2 : 3 * (C * N / R * l13) = 3 * C * l13 * (N / R) := by ring
  have e3 : 2 * N * (1 / R) = 2 * (N / R) := by ring
  have e4 : 2 * N / lam = 2 * (N / lam) := by ring
  have e5 : (4 * C + 4) * N * l13 * (1 / R) = (4 * C + 4) * l13 * (N / R) := by ring
  rw [e1, e2, e3, e4, e5]
  have hCl : 0 ≤ C * l13 := by positivity
  have h1 : C * l13 * (N / lam) ≤ C * l13 * (N / R) := mul_le_mul_of_nonneg_left hy hCl
  have h2 : 2 * (N / R) ≤ 2 * l13 * (N / R) := by nlinarith
  have h3 : 2 * (N / lam) ≤ 2 * l13 * (N / R) := by nlinarith
  nlinarith

/-- LEAF. First error term, displays 6.1 to 6.3 of the surrounding development:
on the short arc the principal square is replaced by the square of the full
period model series, and the difference is charged to the arc length, giving
the term inverse of q times the seventh root of N. -/
theorem short_arc_model_replace520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖principalIntegral520 N q n -
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          logFourier520 N z ^ 2 *
            Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C, hC, h⟩ := principal_arc_mean_square_radius520 hG
  refine ⟨4 * C + 4, by positivity, 128, ?_⟩
  intro N hN q hq hqQ n _
  obtain ⟨hR2, hRlam, hlam1, h4, hq2, hl⟩ := arc_scale520 hN hq hqQ
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set R : ℝ := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hRdef
  set lam : ℝ := (N : ℝ) ^ (1 / 4 : ℝ) with hlamdef
  have hR0 : 0 < R := by linarith
  have hlam0 : 0 < lam := by linarith
  have hR0lam : R ≤ lam * lam := by nlinarith
  have hRsq : R ^ 2 ≤ (N : ℝ) := by nlinarith
  have hlam2 : (2 : ℝ) ≤ lam * lam := by linarith
  have hlamsq : (lam * lam) ^ 2 ≤ (N : ℝ) := by rw [sq]; exact h4.le
  have hA := h N hN q hq hq2 R hR2 hRsq
  have hB := h N hN q hq hq2 (lam * lam) hlam2 hlamsq
  have hξ : 0 < 1 / (lam * lam) := by positivity
  have hξδ : 1 / (lam * lam) ≤ 1 / R := one_div_le_one_div_of_le hR0 hR0lam
  have hδh : 1 / R ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hR2
  have hMass := logFourier_mass491 N hN1 (1 / (lam * lam)) hξ.le (hξδ.trans hδh)
  have hS : ∀ z : ℝ, 1 / (lam * lam) ≤ |z| → |z| ≤ 1 / R →
      ‖logFourier520 N z‖ ^ 2 ≤ (N : ℝ) := by
    intro z hz1 hz2
    have hzpos : 0 < |z| := lt_of_lt_of_le hξ hz1
    have hz0 : z ≠ 0 := abs_pos.mp hzpos
    have hd := logFourier_decay491 N hN1 z hz0 (hz2.trans hδh)
    have hinv : 1 / |z| ≤ lam * lam := by
      rw [div_le_iff₀ hzpos]
      have := (div_le_iff₀ (by positivity : 0 < lam * lam)).mp hz1
      linarith
    have hle : ‖logFourier520 N z‖ ≤ lam * lam := hd.trans hinv
    calc ‖logFourier520 N z‖ ^ 2 ≤ (lam * lam) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ ≤ (N : ℝ) := hlamsq
  have hφc : Continuous (fun z : ℝ =>
      Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hmain := arc_square_replace520 (principalPrime520 N q) (logFourier520 N)
    (continuous_principal520 N q hN1) (logFourier_continuous_radius520 N hN1)
    (fun z : ℝ => Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))
    hφc (fun z => Complex.norm_exp_ofReal_mul_I _)
    (1 / R) (1 / (lam * lam)) lam _ _ _ (N : ℝ) hξ hξδ hlam0 hA hB hMass hS
  have hint : principalIntegral520 N q n =
      ∫ z in -(1 / R)..(1 / R), principalPrime520 N q z ^ 2 *
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    unfold principalIntegral520
    apply intervalIntegral.integral_congr
    intro z _
    simp only []
    rw [show ((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [hint]
  refine hmain.trans ?_
  have hcol := arc_collect520 C (N : ℝ) R lam (Real.log N ^ 13) hC hNpos hR0 hRlam
    (one_le_pow₀ hl)
  have hfin : 3 * (C * (N : ℝ) / R * Real.log N ^ 13) + 2 * (N : ℝ) * (1 / R) +
      lam * (C * (N : ℝ) / (lam * lam) * Real.log N ^ 13) + 2 * (N : ℝ) / lam ≤
      (4 * C + 4) * (N : ℝ) * Real.log N ^ 13 * (1 / R) := hcol
  linarith [hfin]

/-- The two spellings of the phase on the short arc give the same integral. -/
private lemma arc_phase_order520 (N q : ℕ) (n : ℤ) :
    (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
  apply intervalIntegral.integral_congr
  intro z _
  simp only []
  rw [show ((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I by push_cast; ring]

/-- LEAF. Second error term, displays 6.1 to 6.3 of the surrounding development:
the short arc integral of the model square is extended to a full period, and
the loss is the square root saving, the term inverse of the square root of q
times the seventh root of N. -/
theorem short_arc_extend_period520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          logFourier520 N z ^ 2 *
            Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨C, hC, N0, h⟩ := logFourier_arc_convolution491
  refine ⟨C, hC, max N0 1, ?_⟩
  intro N hN q hq hqQ n hn
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by have := le_max_right N0 1; omega
  have hb := h N hN0 q hq hqQ n
  rw [arc_phase_order520 N q n]
  rw [logFourier_square_integral520 N hN1 n]
  have hconv : ∀ m : ℕ, logConvolution520 m = logConvolution1622 m := fun m => rfl
  rw [hconv]
  have hconst : ((Real.exp (-(n : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) =
      ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) := by
    by_cases hn0 : 0 ≤ n
    · have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn0
      rw [hc]
    · have hz : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      rw [hz]
      simp [logConvolution1622]
  rw [hconst]
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hRpos : 0 < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hR1 : 1 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
    nlinarith
  have hsq : Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by
    have hle : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤
        ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by nlinarith
    have h2 := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_mul_self hRpos.le] at h2
  have hnum : 0 ≤ C * (N : ℝ) * Real.log N ^ 13 := by positivity
  exact hb.trans (div_le_div_of_nonneg_left hnum (Real.sqrt_pos.mpr hRpos) hsq)


/-- The sealed statement of the unit, assembled from the two leaves by the
triangle inequality and the addition of the constants. -/
theorem principal_model520_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C1, hC1, M1, hleaf1⟩ := short_arc_model_replace520 hG
  obtain ⟨C2, hC2, M2, hleaf2⟩ := short_arc_extend_period520 hG
  refine ⟨C1 + C2, by linarith, M1 + M2 + 3, ?_⟩
  intro N hN q hq hqQ n hn
  have hM1 : M1 < N := by omega
  have hM2 : M2 < N := by omega
  have hN3 : 3 < N := by omega
  obtain ⟨-, hT, hNpos, hlog⟩ := split_range520 hN3
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqT : 0 < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := mul_pos hqpos hT
  have hA0 : 0 ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hB0 : 0 ≤ 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hX0 : 0 ≤ (N : ℝ) * Real.log N ^ 13 :=
    mul_nonneg hNpos.le (pow_nonneg hlog 13)
  have h1 := hleaf1 N hM1 q hq hqQ n hn
  have h2 := hleaf2 N hM2 q hq hqQ n hn
  have htri :
      ‖principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          C2 * (N : ℝ) * Real.log N ^ 13 /
            Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have heq : principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
        (principalIntegral520 N q n -
          (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))) +
          ((∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) -
            (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))) := by
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have hA2 : C2 * (N : ℝ) * Real.log N ^ 13 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))
      = C2 * (N : ℝ) * Real.log N ^ 13 *
        (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    ring
  have e1 : C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hA0
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog 13)
    refine mul_le_mul_of_nonneg_right ?_ hNpos.le
    linarith
  have e2 : C2 * (N : ℝ) * Real.log N ^ 13 *
        (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
        (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hB0
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog 13)
    refine mul_le_mul_of_nonneg_right ?_ hNpos.le
    linarith
  calc
    ‖principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖
        ≤ C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
            C2 * (N : ℝ) * Real.log N ^ 13 /
              Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := htri
    _ = C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          C2 * (N : ℝ) * Real.log N ^ 13 *
            (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
        rw [hA2]
    _ ≤ (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
            (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := add_le_add e1 e2
    _ = (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
        ring

end LeanLab.Linnik1951
