module

public import LeanLab.PNTPort.Selberg.SharpC
public import LeanLab.PNTPort.Selberg.CramerWeighted
public import LeanLab.PNTPort.Selberg.GeomMoment

/-!
# The weighted mean square with no edge term

Lab proof, unit U-6200, CLOUD 20261020T0817Z-cloud38, T2 toward P0058 Lemma 1 for small `ξ`.
AI wrote this file: `weighted_mean_b` of `WeightedMeanB.lean` redone on `sharp_bound_c`, with the
exact top edges summed against the weight by `cramer_weighted`. CONDITIONAL ON
RiemannHypothesis only.

`weighted_mean_c`: for `1 ≤ L ≤ N` and every `M`, with `q = e^{-1/N}`,
`∫_{|β| ≤ 1/(2L)} ‖∑_{n<M} e^{-n/N} (Λ(n) - 1) e(nβ)‖²
   ≤ C (N (log(N/L) + 3)²/L + N (log N + 2)²/(√L L²) + 1) + q^M ∫_{|β| ≤ 1/(2L)} ‖∑_{n<M} (Λ(n) - 1) e(nβ)‖²`.
The term `L (log N + 1)²` of `weighted_mean_b` is gone; the last term tends to `0` as `M → ∞`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Finset MeasureTheory
open LeanLab.PNTPort.Gallagher LeanLab.PNTPort.LargeSieve

/-- A shift by `s` costs at most `s u(0)` in a geometric sum. -/
lemma geom_shift_le (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (s M : ℕ) : ∑ n ∈ range M, q ^ n * u (n - s) ≤ s * u 0 + ∑ n ∈ range M, q ^ n * u n := by
  rcases le_total M s with h | h
  · have : ∀ n ∈ range M, q ^ n * u (n - s) ≤ u 0 := by
      intro n hn
      rw [show n - s = 0 by have := mem_range.mp hn; omega]
      have : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1
      nlinarith [hu 0]
    have h1 := sum_le_sum this
    rw [sum_const, card_range, nsmul_eq_mul] at h1
    have : (M : ℝ) * u 0 ≤ s * u 0 := mul_le_mul_of_nonneg_right (by exact_mod_cast h) (hu 0)
    have : 0 ≤ ∑ n ∈ range M, q ^ n * u n := sum_nonneg fun n _ => mul_nonneg (pow_nonneg hq0 n) (hu n)
    linarith
  · rw [← sum_range_add_sum_Ico _ h]
    apply add_le_add
    · have : ∀ n ∈ range s, q ^ n * u (n - s) ≤ u 0 := by
        intro n hn
        rw [show n - s = 0 by have := mem_range.mp hn; omega]
        have : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1
        nlinarith [hu 0]
      have h1 := sum_le_sum this
      rw [sum_const, card_range, nsmul_eq_mul] at h1
      exact h1
    · rw [sum_Ico_eq_sum_range]
      have : ∀ j ∈ range (M - s), q ^ (s + j) * u (s + j - s) ≤ q ^ j * u j := by
        intro j _
        rw [show s + j - s = j by omega, pow_add]
        have : q ^ s ≤ 1 := pow_le_one₀ hq0 hq1
        have := mul_nonneg (pow_nonneg hq0 j) (hu j)
        nlinarith [pow_nonneg hq0 s, pow_nonneg hq0 j, hu j]
      refine (sum_le_sum this).trans ?_
      exact sum_le_sum_of_subset_of_nonneg (fun j hj => by
        simp only [mem_range] at hj ⊢; omega) (fun j _ _ => mul_nonneg (pow_nonneg hq0 j) (hu j))

set_option maxHeartbeats 4000000 in
/-- **The weighted mean square near `0`, under RH, with no edge term.** -/
theorem weighted_mean_c (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N L M : ℕ, 1 ≤ L → L ≤ N →
    ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)),
        ‖∑ n ∈ range M, (Real.exp (-(n / N)) : ℂ) * (lam1 n * LargeSieve.e (n * β))‖ ^ 2 ≤
      C * (N * (Real.log (N / L) + 3) ^ 2 / L + N * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2
        + 1) + Real.exp (-(1 / (N : ℝ))) ^ M *
        ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ n ∈ range M, lam1 n * LargeSieve.e (n * β)‖ ^ 2 := by
  obtain ⟨K, hK1, hsb⟩ := sharp_bound_c hRH
  obtain ⟨Kw, hKw0, hKw⟩ := cramer_weighted hRH
  refine ⟨100 * K + 40 * Kw + 100, by positivity, fun N L M hL hLN => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (hL.trans hLN)
  have hN0 : (0 : ℝ) < N := by linarith
  set A := Real.log (N / L) + 3 with hA
  set Q := 1 / (Real.sqrt L * (L : ℝ) ^ 2) with hQ
  set G := (Real.log N + 2) ^ 2 with hG
  have hA3 : 3 ≤ A := by
    have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
    have := Real.log_nonneg (show (1 : ℝ) ≤ N / L by rw [le_div_iff₀ hL0]; linarith)
    linarith
  have hQ0 : 0 ≤ Q := by positivity
  have hG1 : 1 ≤ G := by have := Real.log_nonneg hN1; nlinarith
  set q := Real.exp (-(1 / N)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have : 0 < 1 / (N : ℝ) := by positivity
    have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by linarith)
    rwa [Real.exp_zero] at h
  have h1q : 0 < 1 - q := by linarith
  have h1qN : 1 - q ≤ 1 / N := by
    have := Real.add_one_le_exp (-(1 / (N : ℝ)))
    rw [hq]; linarith
  have hw : ∀ n : ℕ, Real.exp (-(n / N)) = q ^ n := by
    intro n; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  set a : ℕ → ℝ → ℂ := fun n β => lam1 n * LargeSieve.e (n * β) with ha
  have hac : ∀ n, Continuous (a n) := fun n => continuous_const.mul (continuous_e_mul _)
  have hanti : Antitone (fun n : ℕ => q ^ n) := fun i j hij => pow_le_pow_of_le_one hq0.le hq1.le hij
  have hξ : (0 : ℝ) ≤ 1 / (2 * L) := by positivity
  have hab := abel_cs_integral a hac (fun n => q ^ n) hanti (fun n => by positivity) M hξ
  simp only [pow_zero, one_mul] at hab
  have hLHS : ∀ β : ℝ, ∑ n ∈ range M, (Real.exp (-(n / N)) : ℂ) * (lam1 n * LargeSieve.e (n * β)) =
      ∑ n ∈ range M, ((q ^ n : ℝ) : ℂ) * a n β := fun β =>
    sum_congr rfl fun n _ => by rw [hw n]
  simp_rw [hLHS]
  refine hab.trans ?_
  refine add_le_add ?_ le_rfl
  -- the bound for each sharp sum
  set c1 := A ^ 2 / L + Q * G with hc1
  set c3 := 1 / ((N : ℝ) ^ 2 * L) + Q / (N : ℝ) ^ 2 with hc3
  set g : ℕ → ℝ := fun j => ‖Gp j‖ ^ 2 with hg
  have hg0 : ∀ j, 0 ≤ g j := fun j => sq_nonneg _
  set Ed : ℕ → ℝ := fun n => (Real.pi / (2 * L)) ^ 2 *
    (4 * L * g n + 2 * ∑ i ∈ range L, g (n + 1 + i - L)) with hEd
  have hF : ∀ n : ℕ, ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)),
      ‖∑ i ∈ range (n + 1), a i β‖ ^ 2 ≤ K * (1 + c1 * ((n : ℝ) + 1) + c3 * ((n : ℝ) + 1) ^ 3) + Ed n := by
    intro n
    have h := hsb N L (n + 1) hL hLN (by omega)
    simp only [Nat.add_sub_cancel] at h
    push_cast at h
    exact h
  have hstep : ∑ n ∈ range M, (q ^ n - q ^ (n + 1)) *
        ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ i ∈ range (n + 1), a i β‖ ^ 2 ≤
      (∑ n ∈ range M, (1 - q) * q ^ n * (K * (1 + c1 * ((n : ℝ) + 1) + c3 * ((n : ℝ) + 1) ^ 3)))
        + (1 - q) * ∑ n ∈ range M, q ^ n * Ed n := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun n _ => ?_
    rw [show q ^ n - q ^ (n + 1) = (1 - q) * q ^ n by ring]
    have := mul_le_mul_of_nonneg_left (hF n) (by nlinarith [pow_pos hq0 n] : 0 ≤ (1 - q) * q ^ n)
    linarith
  refine hstep.trans ?_
  -- moments
  have hD : 1 / (1 - q) ≤ 2 * N := one_sub_exp_neg_inv hN1
  have hEp : ∀ p : ℕ, ∑ n ∈ range M, (1 - q) * q ^ n * ((n : ℝ) + 1) ^ p ≤
      (p.factorial : ℝ) * (2 * N) ^ p := by
    intro p
    have h := geom_moment p M hq0.le hq1
    have : 0 ≤ q ^ M * (M : ℝ) ^ p := by positivity
    refine le_trans (by linarith) (h.trans ?_)
    rw [div_eq_mul_one_div, ← one_div_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hD p) (by positivity)
  have hmain : ∑ n ∈ range M, (1 - q) * q ^ n * (K * (1 + c1 * ((n : ℝ) + 1) + c3 * ((n : ℝ) + 1) ^ 3))
      = K * (∑ n ∈ range M, (1 - q) * q ^ n * ((n : ℝ) + 1) ^ 0)
        + K * c1 * (∑ n ∈ range M, (1 - q) * q ^ n * ((n : ℝ) + 1) ^ 1)
        + K * c3 * (∑ n ∈ range M, (1 - q) * q ^ n * ((n : ℝ) + 1) ^ 3) := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hmain]
  set S0 := ∑ n ∈ range M, (1 - q) * q ^ n * ((n : ℝ) + 1) ^ 0 with hS0
  set S1 := ∑ n ∈ range M, (1 - q) * q ^ n * ((n : ℝ) + 1) ^ 1 with hS1
  set S3 := ∑ n ∈ range M, (1 - q) * q ^ n * ((n : ℝ) + 1) ^ 3 with hS3
  have e0 : S0 ≤ 1 := by
    have := hEp 0; rw [Nat.factorial_zero, pow_zero, Nat.cast_one, one_mul] at this; exact this
  have e1 : S1 ≤ 2 * N := by
    have := hEp 1; rw [Nat.factorial_one, pow_one, Nat.cast_one, one_mul] at this; exact this
  have e3 : S3 ≤ 48 * (N : ℝ) ^ 3 := by
    have := hEp 3
    simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at this
    nlinarith
  have hc1' : 0 ≤ c1 := by positivity
  have hc3' : 0 ≤ c3 := by positivity
  have t0 : K * S0 ≤ K := by nlinarith
  have t1 := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ K * c1)
  have t3 := mul_le_mul_of_nonneg_left e3 (by positivity : (0 : ℝ) ≤ K * c3)
  have v1 : K * c1 * (2 * N) = 2 * K * (N * A ^ 2 / L) + 2 * K * (N * Q * G) := by
    rw [hc1]; ring
  have v3 : K * c3 * (48 * (N : ℝ) ^ 3) = 48 * K * (N / L) + 48 * K * (N * Q) := by
    rw [hc3]; field_simp
  -- the edges
  set Sg := ∑ n ∈ range M, q ^ n * g n with hSg
  have hSg : Sg ≤ 2 * Kw * (N : ℝ) ^ 2 + 4 * N := by
    have h1 : Sg ≤ ∑ n ∈ range M, (2 * ((Chebyshev.psi n - n) ^ 2 * Real.exp (-(n / N))) + 2 * q ^ n) := by
      refine sum_le_sum fun n _ => ?_
      rw [hw n]
      have := norm_Gp_sq_le n
      nlinarith [pow_pos hq0 n]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h1
    have h2 := hKw N (by omega) M
    have h3 : ∑ n ∈ range M, q ^ n ≤ 1 / (1 - q) := by
      rw [le_div_iff₀ h1q, mul_comm, mul_neg_geom_sum]
      have : 0 ≤ q ^ M := by positivity
      linarith
    linarith
  have hshift : ∀ i ∈ range L, ∑ n ∈ range M, q ^ n * g (n + 1 + i - L) ≤ L + Sg := by
    intro i hi
    have hiL := mem_range.mp hi
    have h := geom_shift_le g hg0 hq0.le hq1.le (L - 1 - i) M
    have e : ∀ n, n + 1 + i - L = n - (L - 1 - i) := fun n => by omega
    simp_rw [e]
    have hg00 : g 0 = 1 := by simp only [hg, norm_Gp_zero, one_pow]
    rw [hg00, mul_one] at h
    have : ((L - 1 - i : ℕ) : ℝ) ≤ L := by exact_mod_cast (by omega : L - 1 - i ≤ L)
    linarith
  have hEdsum : ∑ n ∈ range M, q ^ n * Ed n ≤ (Real.pi / (2 * L)) ^ 2 *
      (4 * L * Sg + 2 * (L * (L + Sg))) := by
    have : ∀ n ∈ range M, q ^ n * Ed n = (Real.pi / (2 * L)) ^ 2 *
        (4 * L * (q ^ n * g n) + 2 * ∑ i ∈ range L, q ^ n * g (n + 1 + i - L)) := by
      intro n _; simp only [hEd]; rw [← mul_sum]; ring
    rw [sum_congr rfl this, ← mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_comm]
    have h := sum_le_sum hshift
    rw [sum_const, card_range, nsmul_eq_mul] at h
    linarith
  have hpi : (Real.pi / (2 * L)) ^ 2 ≤ 3 / (L : ℝ) ^ 2 := by
    rw [div_pow, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have := Real.pi_lt_d2
    have hp2 : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_right hp2 (sq_nonneg (L : ℝ))]
  have hSg0 : 0 ≤ Sg := sum_nonneg fun n _ => mul_nonneg (pow_nonneg hq0.le n) (hg0 n)
  have hedge : (1 - q) * ∑ n ∈ range M, q ^ n * Ed n ≤ 36 * Kw * (N / L) + 78 := by
    have h1 := mul_le_mul_of_nonneg_left hEdsum h1q.le
    have h2 : (1 - q) * ((Real.pi / (2 * L)) ^ 2 * (4 * L * Sg + 2 * (L * (L + Sg)))) ≤
        1 / N * (3 / (L : ℝ) ^ 2 * (6 * L * Sg + 2 * (L : ℝ) ^ 2)) := by
      have : (Real.pi / (2 * L)) ^ 2 * (4 * L * Sg + 2 * (L * (L + Sg))) ≤
          3 / (L : ℝ) ^ 2 * (6 * L * Sg + 2 * (L : ℝ) ^ 2) := by
        have e : 4 * (L : ℝ) * Sg + 2 * (L * (L + Sg)) = 6 * L * Sg + 2 * (L : ℝ) ^ 2 := by ring
        rw [e]; exact mul_le_mul_of_nonneg_right hpi (by positivity)
      exact mul_le_mul h1qN this (by positivity) (by positivity)
    have h3 : 1 / N * (3 / (L : ℝ) ^ 2 * (6 * L * Sg + 2 * (L : ℝ) ^ 2)) =
        18 * (Sg / N) / L + 6 / N := by field_simp; ring
    have h4 : Sg / N ≤ 2 * Kw * N + 4 := by
      rw [div_le_iff₀ hN0]; nlinarith
    have h5 : 18 * (Sg / N) / L ≤ 18 * (2 * Kw * N + 4) / L :=
      div_le_div_of_nonneg_right (by linarith) hL0.le
    have h6 : 18 * (2 * Kw * N + 4) / L = 36 * Kw * (N / L) + 72 / L := by ring
    have h7 : 72 / (L : ℝ) ≤ 72 := by rw [div_le_iff₀ hL0]; linarith
    have h8 : 6 / (N : ℝ) ≤ 6 := by rw [div_le_iff₀ hN0]; linarith
    linarith
  -- final comparison
  have hR' : (N : ℝ) * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2 = N * Q * G := by
    rw [hQ, hG]; field_simp
  rw [hR']
  have hNAL : 0 ≤ (N : ℝ) / L := by positivity
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have w1 : (N : ℝ) / L ≤ N * A ^ 2 / L := by
    rw [mul_div_right_comm]; nlinarith [mul_le_mul_of_nonneg_left hA2 hNAL]
  have w3 : (N : ℝ) * Q ≤ N * Q * G := by
    nlinarith [mul_le_mul_of_nonneg_left hG1 (by positivity : (0 : ℝ) ≤ N * Q)]
  have hX0 : 0 ≤ (N : ℝ) * A ^ 2 / L := by positivity
  have hZ0 : 0 ≤ (N : ℝ) * Q * G := by positivity
  have u1 := mul_le_mul_of_nonneg_left w1 (by positivity : (0 : ℝ) ≤ 48 * K + 36 * Kw)
  have u3 := mul_le_mul_of_nonneg_left w3 (by positivity : (0 : ℝ) ≤ 48 * K)
  have hfin : K * S0 + K * c1 * S1 + K * c3 * S3 + (1 - q) * ∑ n ∈ range M, q ^ n * Ed n ≤
      (50 * K + 36 * Kw) * (N * A ^ 2 / L) + 50 * K * (N * Q * G) + (K + 78) := by
    nlinarith
  refine hfin.trans ?_
  have hC : (50 * K + 36 * Kw) * (N * A ^ 2 / L) + 50 * K * (N * Q * G) + (K + 78) ≤
      (100 * K + 40 * Kw + 100) * (N * A ^ 2 / L + N * Q * G + 1) := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 50 * K + 4 * Kw + 100) hX0,
      mul_nonneg (by positivity : (0 : ℝ) ≤ 50 * K + 40 * Kw + 100) hZ0]
  exact hC

end LeanLab.PNTPort.Selberg

