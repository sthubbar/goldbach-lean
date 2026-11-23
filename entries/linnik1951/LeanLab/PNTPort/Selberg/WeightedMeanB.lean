module

public import LeanLab.PNTPort.Selberg.WeightedMean
public import LeanLab.PNTPort.Selberg.AdditiveBlocksB

/-!
# The weighted mean square with the sharper remainder

Lab proof, unit U-6016, CLOUD 20261020T0415Z-cloud34, T2 toward IDEAS I-5100 and P0058. AI
wrote this file: `sharp_bound` and `weighted_mean` of `WeightedMean.lean` on
`gallagher_selberg_b`. CONDITIONAL ON RiemannHypothesis only.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Finset MeasureTheory
open LeanLab.PNTPort.Gallagher LeanLab.PNTPort.LargeSieve

set_option maxHeartbeats 1000000 in
/-- **The sharp mean square, as a cubic in the length.** -/
theorem sharp_bound_b (hRH : RiemannHypothesis) : ∃ K : ℝ, 1 ≤ K ∧
    ∀ N L k : ℕ, 1 ≤ L → L ≤ N →
    ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ n ∈ range k, lam1 n * LargeSieve.e (n * β)‖ ^ 2 ≤
      K * (2 * L * (Real.log N + 1) ^ 2) +
      (2 * K * (Real.log (N / L) + 3) ^ 2 / L +
        2 * K * (1 / (Real.sqrt L * (L : ℝ) ^ 2)) * (Real.log N + 2) ^ 2) * k +
      2 * K * L / (N : ℝ) ^ 2 * (k : ℝ) ^ 2 +
      (2 * K / ((N : ℝ) ^ 2 * L) + 2 * K * (1 / (Real.sqrt L * (L : ℝ) ^ 2)) / (N : ℝ) ^ 2) *
        (k : ℝ) ^ 3 := by
  obtain ⟨Cg, hCg, hg⟩ := gallagher_selberg_b hRH
  refine ⟨Cg + 1, by linarith, fun N L k hL hLN => ?_⟩
  set K := Cg + 1 with hK
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (hL.trans hLN)
  have hN0 : (0 : ℝ) < N := by linarith
  have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
  set A := Real.log (N / L) + 3 with hA
  set B := Real.log N + 1 with hB
  set Q := 1 / (Real.sqrt L * (L : ℝ) ^ 2) with hQ
  have hA3 : 3 ≤ A := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N / L by rw [le_div_iff₀ hL0]; linarith); linarith
  have hB1 : 1 ≤ B := by have := Real.log_nonneg hN1; linarith
  have hQ0 : 0 ≤ Q := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcub : 0 ≤ (2 * K * A ^ 2 / L + 2 * K * Q * (Real.log N + 2) ^ 2) * k +
      2 * K * L / (N : ℝ) ^ 2 * (k : ℝ) ^ 2 +
      (2 * K / ((N : ℝ) ^ 2 * L) + 2 * K * Q / (N : ℝ) ^ 2) * (k : ℝ) ^ 3 := by positivity
  rcases lt_or_ge k L with hkL | hkL
  · -- the trivial bound
    have hkLr : (k : ℝ) ≤ L := by exact_mod_cast hkL.le
    have hpt : ∀ β : ℝ, ‖∑ n ∈ range k, lam1 n * LargeSieve.e (n * β)‖ ^ 2 ≤ ((k : ℝ) * B) ^ 2 := by
      intro β
      have h1 : ‖∑ n ∈ range k, lam1 n * LargeSieve.e (n * β)‖ ≤ k * B := by
        refine (norm_sum_le _ _).trans ?_
        have : ∀ n ∈ range k, ‖lam1 n * LargeSieve.e (n * β)‖ ≤ B := by
          intro n hn
          rw [norm_mul, LargeSieve.norm_e, mul_one]
          exact norm_lam1_le (by have := mem_range.mp hn; omega)
        refine (sum_le_sum this).trans ?_
        rw [sum_const, card_range, nsmul_eq_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hξ : -(1 / (2 * (L : ℝ))) ≤ 1 / (2 * L) := by
      have : 0 ≤ 1 / (2 * (L : ℝ)) := by positivity
      linarith
    have hint : ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ n ∈ range k, lam1 n * LargeSieve.e (n * β)‖ ^ 2
        ≤ ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ((k : ℝ) * B) ^ 2 := by
      refine intervalIntegral.integral_mono_on hξ ?_ intervalIntegrable_const fun β _ => hpt β
      exact ((continuous_finsetSum _ fun n _ =>
        continuous_const.mul (continuous_e_mul _)).norm.pow 2).intervalIntegrable _ _
    rw [intervalIntegral.integral_const, smul_eq_mul] at hint
    have hlen : (1 / (2 * (L : ℝ)) - -(1 / (2 * L))) = 1 / L := by field_simp; ring
    rw [hlen] at hint
    have h2 : 1 / (L : ℝ) * ((k : ℝ) * B) ^ 2 ≤ L * B ^ 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hL0]
      have : (k : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ hk0 hkLr 2
      nlinarith [sq_nonneg B]
    have h3 : (L : ℝ) * B ^ 2 ≤ K * (2 * L * B ^ 2) := by
      have hK1 : 1 ≤ K := by rw [hK]; linarith
      have h0 : 0 ≤ 2 * L * B ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_right hK1 h0
      have : 0 ≤ L * B ^ 2 := by positivity
      linarith
    linarith
  · -- Selberg and Gallagher
    have hkLr : (L : ℝ) ≤ k := by exact_mod_cast hkL
    have hk0' : (0 : ℝ) < k := by linarith
    have h := hg k L hL hkL
    refine h.trans ?_
    set t := (k : ℝ) / N with ht
    have ht0 : 0 ≤ t := by positivity
    -- three pieces
    have p1 : (Real.log (k / L) + 3) ^ 2 ≤ 2 * A ^ 2 + 2 * t ^ 2 := by
      have hl := log_le_log_add (x := k / L) (y := N / L) (by positivity) (by positivity)
      have e : (k : ℝ) / L / (N / L) = t := by rw [ht]; field_simp
      rw [e] at hl
      have hl0 : 0 ≤ Real.log (k / L) := Real.log_nonneg (by rw [le_div_iff₀ hL0]; linarith)
      have : Real.log (k / L) + 3 ≤ A + t := by rw [hA]; linarith
      nlinarith [sq_nonneg (A - t)]
    have p2 : (Real.log k + 2) ^ 2 ≤ 2 * (Real.log N + 2) ^ 2 + 2 * t ^ 2 := by
      have hl := log_le_log_add hk0' hN0
      have hl0 : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
      have : Real.log k + 2 ≤ (Real.log N + 2) + t := by rw [ht]; linarith
      nlinarith [sq_nonneg (Real.log N + 2 - t)]
    have p3 : (Real.log k + 1) ^ 2 ≤ 2 * B ^ 2 + 2 * t ^ 2 := by
      have hl := log_le_log_add hk0' hN0
      have hl0 : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
      have : Real.log k + 1 ≤ B + t := by rw [hB, ht]; linarith
      nlinarith [sq_nonneg (B - t)]
    set M := (k : ℝ) * (Real.log (k / L) + 3) ^ 2 / L + (k : ℝ) * ((Real.log k + 2) ^ 2 /
        Real.sqrt L) / (L : ℝ) ^ 2 + L * (Real.log k + 1) ^ 2 with hM
    have hsum : M ≤ 2 * L * B ^ 2 + (2 * A ^ 2 / L + 2 * Q * (Real.log N + 2) ^ 2) * k +
        2 * L / (N : ℝ) ^ 2 * (k : ℝ) ^ 2 + (2 / ((N : ℝ) ^ 2 * L) + 2 * Q / (N : ℝ) ^ 2) * (k : ℝ) ^ 3 := by
      have q1 : (k : ℝ) * (Real.log (k / L) + 3) ^ 2 / L ≤ (k : ℝ) * (2 * A ^ 2 + 2 * t ^ 2) / L := by
        gcongr
      have q2 : (k : ℝ) * ((Real.log k + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2 ≤
          (k : ℝ) * Q * (2 * (Real.log N + 2) ^ 2 + 2 * t ^ 2) := by
        have e : (k : ℝ) * ((Real.log k + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2 =
            (k : ℝ) * Q * (Real.log k + 2) ^ 2 := by rw [hQ]; field_simp
        rw [e]; exact mul_le_mul_of_nonneg_left p2 (by positivity)
      have q3 : (L : ℝ) * (Real.log k + 1) ^ 2 ≤ L * (2 * B ^ 2 + 2 * t ^ 2) :=
        mul_le_mul_of_nonneg_left p3 hL0.le
      have e1 : (k : ℝ) * (2 * A ^ 2 + 2 * t ^ 2) / L =
          2 * A ^ 2 / L * k + 2 / ((N : ℝ) ^ 2 * L) * (k : ℝ) ^ 3 := by
        rw [ht]; field_simp
      have e2 : (k : ℝ) * Q * (2 * (Real.log N + 2) ^ 2 + 2 * t ^ 2) =
          2 * Q * (Real.log N + 2) ^ 2 * k + 2 * Q / (N : ℝ) ^ 2 * (k : ℝ) ^ 3 := by
        rw [ht]; field_simp
      have e3 : (L : ℝ) * (2 * B ^ 2 + 2 * t ^ 2) = 2 * L * B ^ 2 + 2 * L / (N : ℝ) ^ 2 * (k : ℝ) ^ 2 := by
        rw [ht]; field_simp
      rw [hM]
      nlinarith
    have hS0 : 0 ≤ M := by rw [hM]; positivity
    have hKC : Cg ≤ K := by rw [hK]; linarith
    calc Cg * M ≤ K * M := mul_le_mul_of_nonneg_right hKC hS0
      _ ≤ K * (2 * L * B ^ 2 + (2 * A ^ 2 / L + 2 * Q * (Real.log N + 2) ^ 2) * k +
        2 * L / (N : ℝ) ^ 2 * (k : ℝ) ^ 2 + (2 / ((N : ℝ) ^ 2 * L) + 2 * Q / (N : ℝ) ^ 2) * (k : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring


set_option maxHeartbeats 2000000 in
/-- **The exponentially weighted mean square, under RH.** -/
theorem weighted_mean_b (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N L M : ℕ, 1 ≤ L → L ≤ N →
    ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)),
        ‖∑ n ∈ range M, (Real.exp (-(n / N)) : ℂ) * (lam1 n * LargeSieve.e (n * β))‖ ^ 2 ≤
      C * (N * (Real.log (N / L) + 3) ^ 2 / L + N * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2
        + L * (Real.log N + 1) ^ 2) := by
  obtain ⟨K, hK1, hsb⟩ := sharp_bound_b hRH
  refine ⟨100 * K, by positivity, fun N L M hL hLN => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (hL.trans hLN)
  have hN0 : (0 : ℝ) < N := by linarith
  set A := Real.log (N / L) + 3 with hA
  set B := Real.log N + 1 with hB
  set Q := 1 / (Real.sqrt L * (L : ℝ) ^ 2) with hQ
  set G := (Real.log N + 2) ^ 2 with hG
  have hA3 : 3 ≤ A := by
    have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
    have := Real.log_nonneg (show (1 : ℝ) ≤ N / L by rw [le_div_iff₀ hL0]; linarith)
    linarith
  have hB1 : 1 ≤ B := by have := Real.log_nonneg hN1; linarith
  have hQ0 : 0 ≤ Q := by positivity
  have hG1 : 1 ≤ G := by have := Real.log_nonneg hN1; nlinarith
  set q := Real.exp (-(1 / N)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have : 0 < 1 / (N : ℝ) := by positivity
    have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by linarith)
    rwa [Real.exp_zero] at h
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
  -- the cubic bound for each sharp sum
  set P : ℝ → ℝ := fun k => K * (2 * L * B ^ 2) + (2 * K * A ^ 2 / L + 2 * K * Q * G) * k +
    2 * K * L / (N : ℝ) ^ 2 * k ^ 2 + (2 * K / ((N : ℝ) ^ 2 * L) + 2 * K * Q / (N : ℝ) ^ 2) * k ^ 3 with hP
  have hF : ∀ k : ℕ, ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)),
      ‖∑ i ∈ range k, a i β‖ ^ 2 ≤ P k := fun k => hsb N L k hL hLN
  have hc : ∀ n : ℕ, 0 ≤ q ^ n - q ^ (n + 1) := fun n => by
    rw [pow_succ]; nlinarith [pow_pos hq0 n]
  have hstep : (∑ n ∈ range M, (q ^ n - q ^ (n + 1)) *
        ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ i ∈ range (n + 1), a i β‖ ^ 2) +
      q ^ M * ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ i ∈ range M, a i β‖ ^ 2 ≤
      (∑ n ∈ range M, (1 - q) * q ^ n * P ((n : ℝ) + 1)) + q ^ M * P M := by
    refine add_le_add (sum_le_sum fun n _ => ?_) (mul_le_mul_of_nonneg_left (hF M) (by positivity))
    rw [show q ^ n - q ^ (n + 1) = (1 - q) * q ^ n by ring]
    have h := hF (n + 1)
    push_cast at h
    exact mul_le_mul_of_nonneg_left h (by nlinarith [pow_pos hq0 n])
  refine hstep.trans ?_
  -- moments
  set E : ℕ → ℝ := fun p => (∑ n ∈ range M, (1 - q) * q ^ n * ((n : ℝ) + 1) ^ p) +
    q ^ M * (M : ℝ) ^ p with hE
  have hD : 1 / (1 - q) ≤ 2 * N := one_sub_exp_neg_inv hN1
  have h1q : 0 < 1 - q := by linarith
  have hEp : ∀ p : ℕ, E p ≤ (p.factorial : ℝ) * (2 * N) ^ p := by
    intro p
    refine (geom_moment p M hq0.le hq1).trans ?_
    rw [div_eq_mul_one_div, ← one_div_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hD p) (by positivity)
  have hexp : (∑ n ∈ range M, (1 - q) * q ^ n * P ((n : ℝ) + 1)) + q ^ M * P M =
      K * (2 * L * B ^ 2) * E 0 + (2 * K * A ^ 2 / L + 2 * K * Q * G) * E 1 + 2 * K * L / (N : ℝ) ^ 2 * E 2 + (2 * K / ((N : ℝ) ^ 2 * L) + 2 * K * Q / (N : ℝ) ^ 2) * E 3 := by
    have hpt : ∀ n ∈ range M, (1 - q) * q ^ n * P ((n : ℝ) + 1) =
        K * (2 * L * B ^ 2) * ((1 - q) * q ^ n * ((n : ℝ) + 1) ^ 0) +
        (2 * K * A ^ 2 / L + 2 * K * Q * G) * ((1 - q) * q ^ n * ((n : ℝ) + 1) ^ 1) +
        2 * K * L / (N : ℝ) ^ 2 * ((1 - q) * q ^ n * ((n : ℝ) + 1) ^ 2) +
        (2 * K / ((N : ℝ) ^ 2 * L) + 2 * K * Q / (N : ℝ) ^ 2) * ((1 - q) * q ^ n * ((n : ℝ) + 1) ^ 3) := by
      intro n _; simp only [hP]; ring
    rw [sum_congr rfl hpt, sum_add_distrib, sum_add_distrib, sum_add_distrib,
      ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum]
    simp only [hE, hP]
    ring
  rw [hexp]
  have e0 := hEp 0
  have e1 := hEp 1
  have e2 := hEp 2
  have e3 := hEp 3
  simp only [Nat.factorial, Nat.cast_one, pow_zero, one_mul, pow_one, Nat.succ_eq_add_one,
    Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at e0 e1 e2 e3
  have c0 : 0 ≤ K * (2 * L * B ^ 2) := by positivity
  have c1 : 0 ≤ (2 * K * A ^ 2 / L + 2 * K * Q * G) := by positivity
  have c2 : 0 ≤ 2 * K * L / (N : ℝ) ^ 2 := by positivity
  have c3 : 0 ≤ (2 * K / ((N : ℝ) ^ 2 * L) + 2 * K * Q / (N : ℝ) ^ 2) := by positivity
  have t1 := mul_le_mul_of_nonneg_left e0 c0
  have t2 := mul_le_mul_of_nonneg_left e1 c1
  have t3 := mul_le_mul_of_nonneg_left e2 c2
  have t4 := mul_le_mul_of_nonneg_left e3 c3
  have v1 : (2 * K * A ^ 2 / L + 2 * K * Q * G) * (2 * N) = 4 * K * (N * A ^ 2 / L) + 4 * K * (N * Q * G) := by ring
  have v2 : 2 * K * L / (N : ℝ) ^ 2 * (2 * ((2 * N) ^ 2)) = 16 * K * L := by field_simp; ring
  have v3 : (2 * K / ((N : ℝ) ^ 2 * L) + 2 * K * Q / (N : ℝ) ^ 2) * (2 * 3 * ((2 * N) ^ 3)) = 96 * K * N / L + 96 * K * (N * Q) := by
    field_simp; ring
  have hNAL : 0 ≤ (N : ℝ) / L := by positivity
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hB2 : 1 ≤ B ^ 2 := by nlinarith
  have w1 : 96 * K * N / L ≤ 96 * K * (N * A ^ 2 / L) := by
    have e1 : 96 * K * N / L = 96 * K * ((N : ℝ) / L) := by ring
    have e2 : (N : ℝ) * A ^ 2 / L = ((N : ℝ) / L) * A ^ 2 := by ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hA2 hNAL]
  have w2 : 16 * K * L ≤ 16 * K * (L * B ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hB2 hL0.le]
  have w3 : 96 * K * (N * Q) ≤ 96 * K * (N * Q * G) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hG1 (by positivity : (0 : ℝ) ≤ N * Q)]
  have hR' : (N : ℝ) * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2 = N * Q * G := by
    rw [hQ, hG]; field_simp
  rw [hR']
  have hX0 : 0 ≤ (N : ℝ) * A ^ 2 / L := by positivity
  have hY0 : 0 ≤ (L : ℝ) * B ^ 2 := by positivity
  have hZ0 : 0 ≤ (N : ℝ) * Q * G := by positivity
  nlinarith

end LeanLab.PNTPort.Selberg

