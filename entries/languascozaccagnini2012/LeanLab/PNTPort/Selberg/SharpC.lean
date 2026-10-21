module

public import LeanLab.PNTPort.Selberg.SumC
public import LeanLab.PNTPort.Selberg.GallagherEdge
public import LeanLab.PNTPort.Selberg.WeightedMean

/-!
# The sharp mean square with exact edges

Lab proof, unit U-6200, CLOUD 20261020T0817Z-cloud38, T2 toward P0058 Lemma 1 for small `ξ`.
AI wrote this file: `gallagher_psi_edge` with `selberg_sum_c` inside and `cramer_sum` on the
bottom edge. CONDITIONAL ON RiemannHypothesis only.

`sharp_bound_c`: for `1 ≤ L ≤ N` and `k ≥ 1`, with `A = log(N/L) + 3`, `Q = 1/(√L L²)` and
`G = (log N + 2)²`,
`∫_{|β| ≤ 1/(2L)} ‖∑_{n<k} (Λ(n) - 1) e(nβ)‖² ≤ K (1 + (A²/L + Q G) k + (1/(N² L) + Q/N²) k³)
   + (π/(2L))² (4 L ‖Gp(k - 1)‖² + 2 ∑_{i<L} ‖Gp(k + i - L)‖²)`.
Unlike `sharp_bound_b` there is no term `L log² N`: the top edge is left exact, for Cramér's
weighted mean square to bound on average.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Finset MeasureTheory
open LeanLab.PNTPort.Gallagher LeanLab.PNTPort.LargeSieve

set_option maxHeartbeats 2000000 in
/-- **The sharp mean square with exact top edge, under RH.** -/
theorem sharp_bound_c (hRH : RiemannHypothesis) : ∃ K : ℝ, 1 ≤ K ∧
    ∀ N L k : ℕ, 1 ≤ L → L ≤ N → 1 ≤ k →
    ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ n ∈ range k, lam1 n * LargeSieve.e (n * β)‖ ^ 2 ≤
      K * (1 + ((Real.log (N / L) + 3) ^ 2 / L + 1 / (Real.sqrt L * (L : ℝ) ^ 2) * (Real.log N + 2) ^ 2) * k
        + (1 / ((N : ℝ) ^ 2 * L) + 1 / (Real.sqrt L * (L : ℝ) ^ 2) / (N : ℝ) ^ 2) * (k : ℝ) ^ 3)
      + (Real.pi / (2 * L)) ^ 2 * (4 * L * ‖Gp (k - 1)‖ ^ 2 + 2 * ∑ i ∈ range L, ‖Gp (k + i - L)‖ ^ 2) := by
  obtain ⟨C, hC, hs⟩ := selberg_sum_c hRH
  obtain ⟨Kc, hKc0, hKc⟩ := cramer_sum hRH
  refine ⟨6 * C + 12 * Kc + 20, by linarith, fun N L k hL hLN hk => ?_⟩
  set K := 6 * C + 12 * Kc + 20 with hK
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (hL.trans hLN)
  have hN0 : (0 : ℝ) < N := by linarith
  have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  set A := Real.log (N / L) + 3 with hA
  set Q := 1 / (Real.sqrt L * (L : ℝ) ^ 2) with hQ
  set G := (Real.log N + 2) ^ 2 with hG
  set Ed := 4 * L * ‖Gp (k - 1)‖ ^ 2 + 2 * ∑ i ∈ range L, ‖Gp (k + i - L)‖ ^ 2 with hEd
  have hA3 : 3 ≤ A := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N / L by rw [le_div_iff₀ hL0]; linarith); linarith
  have hQ0 : 0 ≤ Q := by positivity
  have hG0 : 0 ≤ G := by positivity
  have hpi : (Real.pi / (2 * L)) ^ 2 ≤ 3 / (L : ℝ) ^ 2 := by
    rw [div_pow, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have := Real.pi_lt_d2
    have hp2 : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_right hp2 (sq_nonneg (L : ℝ))]
  have hgal := gallagher_psi_edge k L (by omega) hk
  -- the interior
  set Int := ∑ m ∈ Ico L k, (Chebyshev.psi (m : ℝ) - Chebyshev.psi ((m - L : ℕ) : ℝ) - L) ^ 2 with hInt
  have hInt0 : 0 ≤ Int := sum_nonneg fun _ _ => sq_nonneg _
  have hIntB : Int ≤ C * (k * L * (2 * A ^ 2 + 2 * ((k : ℝ) / N) ^ 2)
      + k * ((2 * G + 2 * ((k : ℝ) / N) ^ 2) / Real.sqrt L) + (L : ℝ) ^ 2) := by
    rcases lt_or_ge k L with hkL | hkL
    · have : Ico L k = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hInt, this, sum_empty]; positivity
    have hkLr : (L : ℝ) ≤ k := by exact_mod_cast hkL
    have hre : Int = ∑ j ∈ range (k - L), (Chebyshev.psi ((j : ℝ) + L) - Chebyshev.psi j - L) ^ 2 := by
      rw [hInt, sum_Ico_eq_sum_range]
      refine sum_congr rfl fun j _ => ?_
      rw [show L + j - L = j by omega]
      push_cast; ring_nf
    have h := hs (k - L) L k hL hkL (by omega)
    rw [← hre] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC)
    set t := (k : ℝ) / N with ht
    have p1 : (Real.log (k / L) + 3) ^ 2 ≤ 2 * A ^ 2 + 2 * t ^ 2 := by
      have hl := log_le_log_add (x := k / L) (y := N / L) (by positivity) (by positivity)
      have e : (k : ℝ) / L / (N / L) = t := by rw [ht]; field_simp
      rw [e] at hl
      have hl0 : 0 ≤ Real.log (k / L) := Real.log_nonneg (by rw [le_div_iff₀ hL0]; linarith)
      have : Real.log (k / L) + 3 ≤ A + t := by rw [hA]; linarith
      have ht0 : 0 ≤ t := by positivity
      nlinarith [sq_nonneg (A - t)]
    have p2 : (Real.log k + 2) ^ 2 ≤ 2 * G + 2 * t ^ 2 := by
      have hl := log_le_log_add hk0 hN0
      have hl0 : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
      have : Real.log k + 2 ≤ (Real.log N + 2) + t := by rw [ht]; linarith
      have ht0 : 0 ≤ t := by positivity
      rw [hG]; nlinarith [sq_nonneg (Real.log N + 2 - t)]
    have q1 : (k : ℝ) * L * (Real.log (k / L) + 3) ^ 2 ≤ k * L * (2 * A ^ 2 + 2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left p1 (by positivity)
    have q2 : (k : ℝ) * ((Real.log k + 2) ^ 2 / Real.sqrt L) ≤ k * ((2 * G + 2 * t ^ 2) / Real.sqrt L) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right p2 (Real.sqrt_nonneg _)) hk0.le
    linarith
  -- the bottom edge
  have hbot : ∑ m ∈ range L, ‖Gp m‖ ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 2 + 2 * L := by
    have h1 : ∑ m ∈ range L, ‖Gp m‖ ^ 2 ≤ ∑ m ∈ range L, (2 * (Chebyshev.psi (m : ℝ) - m) ^ 2 + 2) :=
      sum_le_sum fun m _ => norm_Gp_sq_le m
    rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at h1
    have := hKc L
    linarith
  -- assembly
  have hbig : Int + (2 * ∑ m ∈ range L, ‖Gp m‖ ^ 2 + 2 * L + Ed) ≤
      C * (k * L * (2 * A ^ 2 + 2 * ((k : ℝ) / N) ^ 2)
        + k * ((2 * G + 2 * ((k : ℝ) / N) ^ 2) / Real.sqrt L) + (L : ℝ) ^ 2)
      + (4 * Kc * (L : ℝ) ^ 2 + 6 * L) + Ed := by linarith
  have hgal' : ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ n ∈ range k, lam1 n * LargeSieve.e (n * β)‖ ^ 2
      ≤ (Real.pi / (2 * L)) ^ 2 * (C * (k * L * (2 * A ^ 2 + 2 * ((k : ℝ) / N) ^ 2)
        + k * ((2 * G + 2 * ((k : ℝ) / N) ^ 2) / Real.sqrt L) + (L : ℝ) ^ 2)
      + (4 * Kc * (L : ℝ) ^ 2 + 6 * L)) + (Real.pi / (2 * L)) ^ 2 * Ed := by
    rw [← mul_add]
    refine hgal.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith
  refine hgal'.trans (add_le_add ?_ le_rfl)
  set Z := C * (k * L * (2 * A ^ 2 + 2 * ((k : ℝ) / N) ^ 2)
        + k * ((2 * G + 2 * ((k : ℝ) / N) ^ 2) / Real.sqrt L) + (L : ℝ) ^ 2)
      + (4 * Kc * (L : ℝ) ^ 2 + 6 * L) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  refine (mul_le_mul_of_nonneg_right hpi hZ0).trans ?_
  have e1 : 3 / (L : ℝ) ^ 2 * Z = 3 * C * (2 * A ^ 2 / L * k + 2 * k ^ 3 / ((N : ℝ) ^ 2 * L))
      + 3 * C * (2 * Q * G * k + 2 * Q / (N : ℝ) ^ 2 * (k : ℝ) ^ 3) + 3 * C + 12 * Kc + 18 / L := by
    rw [hZ, hQ]
    have hs : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL0).ne'
    field_simp
    ring
  rw [e1]
  have hL' : 18 / (L : ℝ) ≤ 18 := by rw [div_le_iff₀ hL0]; linarith
  have hk3 : 0 ≤ (k : ℝ) ^ 3 := by positivity
  have hfin : 3 * C * (2 * A ^ 2 / L * k + 2 * k ^ 3 / ((N : ℝ) ^ 2 * L))
      + 3 * C * (2 * Q * G * k + 2 * Q / (N : ℝ) ^ 2 * (k : ℝ) ^ 3)
      = 6 * C * ((A ^ 2 / L + Q * G) * k + (1 / ((N : ℝ) ^ 2 * L) + Q / (N : ℝ) ^ 2) * (k : ℝ) ^ 3) := by
    field_simp; ring
  rw [hfin]
  have hX : 0 ≤ (A ^ 2 / L + Q * G) * k + (1 / ((N : ℝ) ^ 2 * L) + Q / (N : ℝ) ^ 2) * (k : ℝ) ^ 3 := by
    positivity
  have : 6 * C * ((A ^ 2 / L + Q * G) * k + (1 / ((N : ℝ) ^ 2 * L) + Q / (N : ℝ) ^ 2) * (k : ℝ) ^ 3)
      ≤ K * ((A ^ 2 / L + Q * G) * k + (1 / ((N : ℝ) ^ 2 * L) + Q / (N : ℝ) ^ 2) * (k : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_right (by rw [hK]; linarith) hX
  have e2 : K * (1 + (A ^ 2 / L + Q * G) * k + (1 / ((N : ℝ) ^ 2 * L) + Q / (N : ℝ) ^ 2) * (k : ℝ) ^ 3)
      = K + K * ((A ^ 2 / L + Q * G) * k + (1 / ((N : ℝ) ^ 2 * L) + Q / (N : ℝ) ^ 2) * (k : ℝ) ^ 3) := by ring
  rw [e2]
  have : 3 * C + 12 * Kc + 18 ≤ K := by rw [hK]; linarith
  linarith

end LeanLab.PNTPort.Selberg

