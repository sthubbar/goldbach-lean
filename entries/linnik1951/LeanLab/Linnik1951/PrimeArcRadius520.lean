module

public import LeanLab.Linnik1951.PrimeArcLeaf491
public import LeanLab.Linnik1951.Decomp520a
public import Batteries.Tactic.OpenPrivate
import all LeanLab.Linnik1951.PrimeArcPartial491
import all LeanLab.Linnik1951.PrimeArcLeaf491

/-!
P0093 pages 159 through 161, equations 6.1 and 6.3. The mean square estimate for the
prime series against the model series S one on an arc of general radius one over R,
for every real R with R at least two and R squared at most N, and its form for the
principal character prime series. Formalizer's route as in prime_arc_mean_square491.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

open Finset MeasureTheory

open private pointwise_partial491 integral_abs_partial491 widen_partial491 cont_A_partial491
  cont_D_partial491 arith_partial491 from LeanLab.Linnik1951.PrimeArcPartial491

open private prime_minus_log_series491 from LeanLab.Linnik1951.PrimeArcLeaf491

/-- P0093 page 160 equation 6.1 with page 161 equation 6.3, for every truncation of
the difference of the prime series and the model series S one, on the arc of radius
one over R for every real R at least two whose square is at most N. Not a statement
of the print; formalizer's route as in prime_arc_mean_square491. The proof is the
body of prime_arc_partial491, which uses its radius only through these two facts. -/
theorem prime_arc_partial_radius520 (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 128 < N → ∀ R : ℝ, 2 ≤ R → R ^ 2 ≤ (N : ℝ) → ∀ M : ℕ,
      (∫ z in -(1 / R)..(1 / R),
        ‖∑ n ∈ range M, (primeCoefficient552 N n - logCoefficient520 N n) *
          Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I)‖ ^ 2) ≤
        C * (N : ℝ) / R * Real.log N ^ 13 := by
  obtain ⟨Ca, hCa, hA⟩ := lam_log_mean_square491 hRH
  obtain ⟨Cp, hCp, hPw⟩ := proper_power_damped491
  refine ⟨306 * Ca + 96 + 24 * Cp ^ 2, by positivity, ?_⟩
  intro N hN R hR2 hRN M
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl : 1 ≤ Real.log N := by
    have hN3' : (3 : ℝ) < N := by exact_mod_cast (show 3 < N by omega)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3').le
  have hR0 : 0 < R := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = ⌊R / 2⌋₊ := ⟨_, rfl⟩
  have hLle : (L : ℝ) ≤ R / 2 := by rw [hLdef]; exact Nat.floor_le (by linarith)
  have hLlt : R / 2 < L + 1 := by rw [hLdef]; exact Nat.lt_floor_add_one _
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    exact Nat.le_floor (by push_cast; linarith)
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLN : L ≤ N := by
    have : (L : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hLNr : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hP := hPw N M (by omega)
  have h1 := integral_abs_partial491 _ _ (cont_D_partial491 N M) (cont_A_partial491 N M)
    (48 + 3 * (Cp * Real.sqrt N * (Real.log N + 1)) ^ 2) (1 / R) (by positivity)
    (pointwise_partial491 N M _ hP)
  have h2 := widen_partial491 _ (cont_A_partial491 N M) (fun x => by positivity)
    (1 / R) (1 / (2 * (L : ℝ))) (by positivity)
    (one_div_le_one_div_of_le (by linarith) (by linarith))
  have h3 := hA N L M hL1 hLN
  have h4 := arith_partial491 N R L (Real.log N) (Real.log (N / L)) (Real.sqrt L) Ca Cp
    (Real.sqrt N) hNr hR2 hRN (by linarith) (by linarith) hL1r hl
    (Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith))
    (Real.log_le_log (by positivity) (div_le_self (by linarith) hL1r))
    (Real.one_le_sqrt.mpr hL1r) hCa (Real.sq_sqrt (by linarith))
  linarith

/-- P0093 page 160 equation 6.1 with page 161 equation 6.3, for the full prime series
on the arc of radius one over R, for every real R at least two whose square is at
most N. Not a statement of the print; formalizer's route as in
prime_arc_mean_square491, through the truncated estimate and the passage to the
limit series_arc_limit491. The exponent 13 is slack. -/
theorem prime_arc_mean_square_radius520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 128 < N → ∀ R : ℝ, 2 ≤ R → R ^ 2 ≤ (N : ℝ) →
      (∫ z in -(1 / R)..(1 / R), ‖primeFourier111 N z - logFourier520 N z‖ ^ 2) ≤
        C * (N : ℝ) / R * Real.log N ^ 13 := by
  obtain ⟨C, hC, h⟩ := prime_arc_partial_radius520 (LeanLab.DERZ1997.rh_of_GRH hG)
  refine ⟨C, hC, fun N hN R hR2 hRN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  simp only [prime_minus_log_series491 N hN1]
  refine series_arc_limit491 _ ?_ _ _ ?_ (h N hN R hR2 hRN)
  · exact ((prime_coefficients_summable552 N hN1).sub
      (logCoefficient_summable520 N hN1)).norm
  · have : 0 < R := by linarith
    positivity

/-- P0093 page 161 equation 6.3. The model series S one is continuous. -/
theorem logFourier_continuous_radius520 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (logFourier520 N) := by
  unfold logFourier520
  refine continuous_tsum (u := fun m => ‖logCoefficient520 N m‖) ?_
    (logCoefficient_summable520 N hN).norm ?_
  · intro m
    fun_prop
  · intro m z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- P0093 page 159 before equation 5.1. The removed prime divisor terms of the
principal series have total size at most the modulus. -/
private lemma divisor_terms_le_radius520 (N q : ℕ) (z : ℝ) :
    ‖∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)‖ ≤ q := by
  have hcard : q.primeFactors.card ≤ q := by
    calc q.primeFactors.card ≤ (Icc 1 q).card :=
          Finset.card_le_card (fun p hp => by
            have hp' := Nat.mem_primeFactors.mp hp
            exact Finset.mem_Icc.mpr ⟨hp'.1.one_lt.le,
              Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1⟩)
      _ = q := by simp
  have h1 : ∀ p ∈ q.primeFactors, ‖(Real.exp (-(p : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)‖ ≤ 1 := by
    intro p _
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have : 0 ≤ (p : ℝ) / N := by positivity
    rw [neg_div]
    linarith
  calc _ ≤ ∑ p ∈ q.primeFactors, (1 : ℝ) := (norm_sum_le _ _).trans (Finset.sum_le_sum h1)
    _ = q.primeFactors.card := by simp
    _ ≤ q := by exact_mod_cast hcard

/-- P0093 page 160 equation 6.1 with page 161 equation 6.3, for the principal
character prime series of page 159 on the arc of radius one over R. The principal
series is the prime series with at most q terms of size at most one removed, and q
squared is at most N. Not a statement of the print; formalizer's route as in
prime_arc_mean_square491. The exponent 13 is slack. -/
theorem principal_arc_mean_square_radius520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 128 < N → ∀ q : ℕ, 1 ≤ q → ((q : ℝ)) ^ 2 ≤ (N : ℝ) →
      ∀ R : ℝ, 2 ≤ R → R ^ 2 ≤ (N : ℝ) →
      (∫ z in -(1 / R)..(1 / R), ‖principalPrime520 N q z - logFourier520 N z‖ ^ 2) ≤
        C * (N : ℝ) / R * Real.log N ^ 13 := by
  obtain ⟨C, hC, h⟩ := prime_arc_mean_square_radius520 hG
  refine ⟨2 * C + 4, by positivity, fun N hN q hq hqN R hR2 hRN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hR0 : 0 < R := by linarith
  have hl : 1 ≤ Real.log N := by
    have hN3' : (3 : ℝ) < N := by exact_mod_cast (show 3 < N by omega)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3').le
  have hl13 : (1 : ℝ) ≤ Real.log N ^ 13 := one_le_pow₀ hl
  have hcP : Continuous (primeFourier111 N) := continuous_prime_fourier111_up111 N hN1
  have hcL := logFourier_continuous_radius520 N hN1
  have hcQ := continuous_principal520 N q hN1
  have hcA : Continuous (fun z : ℝ => ‖primeFourier111 N z - logFourier520 N z‖ ^ 2) := by
    fun_prop
  have hcB : Continuous (fun z : ℝ => ‖principalPrime520 N q z - logFourier520 N z‖ ^ 2) := by
    fun_prop
  have hpt : ∀ z : ℝ, ‖principalPrime520 N q z - logFourier520 N z‖ ^ 2 ≤
      2 * ‖primeFourier111 N z - logFourier520 N z‖ ^ 2 + 2 * (q : ℝ) ^ 2 := by
    intro z
    have hd := divisor_terms_le_radius520 N q z
    have he : principalPrime520 N q z - logFourier520 N z =
        (primeFourier111 N z - logFourier520 N z) -
          ∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I) := by
      show primeFourier111 N z - _ - logFourier520 N z = _
      ring
    rw [he]
    have h1 := norm_sub_le (primeFourier111 N z - logFourier520 N z)
      (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (h1.trans (add_le_add le_rfl hd)) 2
    nlinarith [sq_nonneg (‖primeFourier111 N z - logFourier520 N z‖ - (q : ℝ))]
  have hint : (∫ z in -(1 / R)..(1 / R), ‖principalPrime520 N q z - logFourier520 N z‖ ^ 2) ≤
      2 * (∫ z in -(1 / R)..(1 / R), ‖primeFourier111 N z - logFourier520 N z‖ ^ 2) +
        2 * (1 / R) * (2 * (q : ℝ) ^ 2) := by
    calc _ ≤ ∫ z in -(1 / R)..(1 / R),
          (2 * ‖primeFourier111 N z - logFourier520 N z‖ ^ 2 + 2 * (q : ℝ) ^ 2) :=
        intervalIntegral.integral_mono_on (by have : 0 ≤ 1 / R := by positivity
                                              linarith)
          (hcB.intervalIntegrable _ _)
          (((hcA.const_mul 2).add continuous_const).intervalIntegrable _ _) (fun z _ => hpt z)
      _ = _ := by
        rw [intervalIntegral.integral_add ((hcA.const_mul 2).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  have hmain := h N hN R hR2 hRN
  have hX : (N : ℝ) / R ≤ N / R * Real.log N ^ 13 :=
    le_mul_of_one_le_right (by positivity) hl13
  have hq2 : 2 * (1 / R) * (2 * (q : ℝ) ^ 2) ≤ 4 * (N / R) := by
    have : (q : ℝ) ^ 2 / R ≤ N / R := div_le_div_of_nonneg_right hqN hR0.le
    have e : 2 * (1 / R) * (2 * (q : ℝ) ^ 2) = 4 * ((q : ℝ) ^ 2 / R) := by ring
    rw [e]
    linarith
  have e1 : (2 * C + 4) * (N : ℝ) / R * Real.log N ^ 13 =
      2 * (C * (N : ℝ) / R * Real.log N ^ 13) + 4 * (N / R * Real.log N ^ 13) := by ring
  rw [e1]
  linarith

end LeanLab.Linnik1951
