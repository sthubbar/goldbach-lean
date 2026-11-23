module

public import Mathlib

/-!
AI wrote this Lean code.

P0014, Helfgott, Major arcs for Goldbach's problem, Lemma 4.2, page 37: the numerical
constant c = 5 log(2 sqrt 3 zeta(9/8)/zeta(9/4)). This file proves the enclosure
zeta(9/8)/zeta(9/4) ≤ 5.880137 that the constant needs, the leaf
`Residue123.zeta_ratio_le`. True value 5.8801339.

Method: zeta(s) is the sum of n^(-s) for real s > 1. The tail past N is bounded above
by the midpoint rule and below by the trapezoid rule, both from the tangent line
inequality of x^(-s), and the first N terms are enclosed by certified decimals.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.ZetaRatio123

open Real Finset Filter Topology

/-- Tangent line inequality for the convex function x^(-s), s > 0, from weighted AM-GM. -/
lemma tangent_le {s : ℝ} (hs : 0 < s) {x m : ℝ} (hx : 0 < x) (hm : 0 < m) :
    m ^ (-s) - s * m ^ (-s - 1) * (x - m) ≤ x ^ (-s) := by
  set y := x / m with hy
  have hy0 : 0 < y := div_pos hx hm
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have key := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / (1 + s)) (w₂ := s / (1 + s))
    (p₁ := y ^ (-s)) (p₂ := y) (by positivity) (by positivity) (by positivity) hy0.le
    (by field_simp)
  have h1 : (y ^ (-s)) ^ (1 / (1 + s)) * y ^ (s / (1 + s)) = 1 := by
    rw [← Real.rpow_mul hy0.le, ← Real.rpow_add hy0]
    have : -s * (1 / (1 + s)) + s / (1 + s) = 0 := by field_simp; ring
    rw [this, Real.rpow_zero]
  rw [h1] at key
  have h2 : 1 + s - s * y ≤ y ^ (-s) := by
    have : 1 / (1 + s) * y ^ (-s) + s / (1 + s) * y = (y ^ (-s) + s * y) / (1 + s) := by
      field_simp
    rw [this, le_div_iff₀ h1s] at key
    linarith
  have hx' : x = y * m := by rw [hy]; field_simp
  have h3 : x ^ (-s) = y ^ (-s) * m ^ (-s) := by rw [hx', Real.mul_rpow hy0.le hm.le]
  have h4 : m ^ (-s - 1) = m ^ (-s) / m := by rw [Real.rpow_sub_one hm.ne']
  have hmpos : 0 < m ^ (-s) := Real.rpow_pos_of_pos hm _
  rw [h3, h4]
  have h5 : m ^ (-s) - s * (m ^ (-s) / m) * (x - m) = (1 + s - s * y) * m ^ (-s) := by
    rw [hy]; field_simp; ring
  rw [h5]
  exact mul_le_mul_of_nonneg_right h2 hmpos.le

/-- The integral of x^(-s) over an interval of positive reals, s ≠ 1. -/
lemma integral_rpow_neg {s a b : ℝ} (hs : 1 < s) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, x ^ (-s) = (a ^ (1 - s) - b ^ (1 - s)) / (s - 1) := by
  rw [integral_rpow]
  · have h1 : -s + 1 = 1 - s := by ring
    have h2 : (1 - s) ≠ 0 := by linarith
    have h3 : (s - 1) ≠ 0 := by linarith
    rw [h1]; field_simp; ring
  · right
    refine ⟨by linarith, ?_⟩
    rw [Set.uIcc_of_le hab]
    intro h0
    exact absurd h0.1 (not_le.mpr ha)

lemma intervalIntegrable_rpow_neg {s a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => x ^ (-s)) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro x hx
  exact (Real.continuousAt_rpow_const x (-s) (Or.inl (by linarith [hx.1]))).continuousWithinAt

lemma integral_affine (a b c d : ℝ) :
    ∫ x in a..b, (c + d * x) = c * (b - a) + d * ((b ^ 2 - a ^ 2) / 2) := by
  rw [intervalIntegral.integral_add (by simp) (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp [mul_comm]

/-- Midpoint rule, upper bound for one term: m^(-s) is at most the integral of x^(-s)
over [m - 1/2, m + 1/2]. -/
lemma term_le_mid {s : ℝ} (hs : 1 < s) {m : ℝ} (hm : 1 ≤ m) :
    m ^ (-s) ≤ ((m - 1 / 2) ^ (1 - s) - (m + 1 / 2) ^ (1 - s)) / (s - 1) := by
  have ha : (0 : ℝ) < m - 1 / 2 := by linarith
  have hab : m - 1 / 2 ≤ m + 1 / 2 := by linarith
  rw [← integral_rpow_neg hs ha hab]
  set A := m ^ (-s) with hA
  set B := s * m ^ (-s - 1) with hB
  have hint : ∫ x in (m - 1 / 2)..(m + 1 / 2), ((A + B * m) + (-B) * x) = A := by
    rw [integral_affine]; ring
  calc A = ∫ x in (m - 1 / 2)..(m + 1 / 2), ((A + B * m) + (-B) * x) := hint.symm
    _ ≤ ∫ x in (m - 1 / 2)..(m + 1 / 2), x ^ (-s) := by
        apply intervalIntegral.integral_mono_on hab
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (intervalIntegrable_rpow_neg ha hab)
        intro x hx
        have := tangent_le (s := s) (by linarith) (x := x) (m := m) (by linarith [hx.1])
          (by linarith)
        rw [← hA, ← hB] at this
        linarith

/-- Trapezoid rule, lower bound: the integral of x^(-s) over [n, n+1] is at most the
mean of the end values. -/
lemma trap_le {s : ℝ} (hs : 1 < s) {n : ℝ} (hn : 0 < n) :
    (n ^ (1 - s) - (n + 1) ^ (1 - s)) / (s - 1) ≤ (n ^ (-s) + (n + 1) ^ (-s)) / 2 := by
  have hab : n ≤ n + 1 := by linarith
  rw [← integral_rpow_neg hs hn hab]
  set A := n ^ (-s) with hA
  set B := (n + 1) ^ (-s) with hB
  have hint : ∫ x in n..(n + 1), (((n + 1) * A - n * B) + (B - A) * x) = (A + B) / 2 := by
    rw [integral_affine]; ring
  rw [← hint]
  apply intervalIntegral.integral_mono_on hab (intervalIntegrable_rpow_neg hn hab)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hs0 : 0 < s := by linarith
  have t1 := tangent_le hs0 (x := n) (m := x) hn hx0
  have t2 := tangent_le hs0 (x := n + 1) (m := x) (by linarith) hx0
  rw [← hA] at t1
  rw [← hB] at t2
  set C := x ^ (-s)
  set E := s * x ^ (-s - 1)
  have h1 : 0 ≤ n + 1 - x := by linarith [hx.2]
  have h2 : 0 ≤ x - n := by linarith [hx.1]
  nlinarith [mul_le_mul_of_nonneg_left t1 h1, mul_le_mul_of_nonneg_left t2 h2]

/-- Midpoint tail bound for partial sums. -/
lemma sum_tail_le {s : ℝ} (hs : 1 < s) (N k : ℕ) :
    ∑ i ∈ range k, ((↑(i + N) : ℝ) + 1) ^ (-s) ≤
      (((N : ℝ) + 1 / 2) ^ (1 - s) - ((N : ℝ) + k + 1 / 2) ^ (1 - s)) / (s - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have h := term_le_mid hs (m := (↑(k + N) : ℝ) + 1)
      (by have : (0 : ℝ) ≤ (↑(k + N) : ℝ) := Nat.cast_nonneg _; linarith)
    have e1 : (↑(k + N) : ℝ) + 1 - 1 / 2 = (N : ℝ) + k + 1 / 2 := by push_cast; ring
    have e2 : (↑(k + N) : ℝ) + 1 + 1 / 2 = (N : ℝ) + (↑(k + 1) : ℝ) + 1 / 2 := by
      push_cast; ring
    rw [e1, e2] at h
    have hs1 : 0 < s - 1 := by linarith
    have : (((N : ℝ) + 1 / 2) ^ (1 - s) - ((N : ℝ) + (↑(k + 1) : ℝ) + 1 / 2) ^ (1 - s)) / (s - 1)
        = (((N : ℝ) + 1 / 2) ^ (1 - s) - ((N : ℝ) + k + 1 / 2) ^ (1 - s)) / (s - 1)
          + (((N : ℝ) + k + 1 / 2) ^ (1 - s) - ((N : ℝ) + (↑(k + 1) : ℝ) + 1 / 2) ^ (1 - s))
            / (s - 1) := by ring
    rw [this]
    linarith

/-- Trapezoid lower bound for partial sums. -/
lemma sum_tail_ge {s : ℝ} (hs : 1 < s) (N k : ℕ) :
    ((N : ℝ) + 1) ^ (-s) / 2 +
        (((N : ℝ) + 1) ^ (1 - s) - ((N : ℝ) + k + 1) ^ (1 - s)) / (s - 1) ≤
      ∑ i ∈ range (k + 1), ((↑(i + N) : ℝ) + 1) ^ (-s) - ((N : ℝ) + k + 1) ^ (-s) / 2 := by
  induction k with
  | zero => simp; linarith
  | succ k ih =>
    rw [sum_range_succ]
    have hpos : (0 : ℝ) < (N : ℝ) + k + 1 := by positivity
    have h := trap_le hs hpos
    have e1 : (↑(k + 1 + N) : ℝ) + 1 = (N : ℝ) + k + 1 + 1 := by push_cast; ring
    have e2 : (N : ℝ) + (↑(k + 1) : ℝ) + 1 = (N : ℝ) + k + 1 + 1 := by push_cast; ring
    rw [e1, e2]
    have : (((N : ℝ) + 1) ^ (1 - s) - ((N : ℝ) + k + 1 + 1) ^ (1 - s)) / (s - 1)
        = (((N : ℝ) + 1) ^ (1 - s) - ((N : ℝ) + k + 1) ^ (1 - s)) / (s - 1)
          + (((N : ℝ) + k + 1) ^ (1 - s) - ((N : ℝ) + k + 1 + 1) ^ (1 - s)) / (s - 1) := by ring
    rw [this]
    linarith

lemma summable_shift {s : ℝ} (hs : 1 < s) : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-s) := by
  have h := (Real.summable_nat_rpow (p := -s)).mpr (by linarith)
  have := (summable_nat_add_iff 1).mpr h
  simpa using this

/-- zeta(s) for real s > 1 as a real series. -/
lemma zeta_real {s : ℝ} (hs : 1 < s) :
    riemannZeta (s : ℂ) = ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-s) : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs), Complex.ofReal_tsum]
  congr 1
  funext n
  have h0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [Complex.ofReal_cpow h0]
  push_cast
  rw [Complex.cpow_neg, one_div]

/-- Upper bound: zeta(s) is at most the first N terms plus the midpoint tail. -/
lemma zeta_le {s : ℝ} (hs : 1 < s) (N : ℕ) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ (-s) ≤
      ∑ n ∈ range N, ((n : ℝ) + 1) ^ (-s) + ((N : ℝ) + 1 / 2) ^ (1 - s) / (s - 1) := by
  rw [← (summable_shift hs).sum_add_tsum_nat_add N]
  gcongr
  apply Real.tsum_le_of_sum_range_le
  · intro n; positivity
  · intro k
    refine (sum_tail_le hs N k).trans ?_
    have hs1 : 0 < s - 1 := by linarith
    have : (0 : ℝ) ≤ ((N : ℝ) + k + 1 / 2) ^ (1 - s) := by positivity
    rw [div_le_div_iff_of_pos_right hs1]
    linarith

/-- Lower bound: zeta(s) is at least the first N terms plus the trapezoid tail. -/
lemma le_zeta {s : ℝ} (hs : 1 < s) (N : ℕ) :
    ∑ n ∈ range N, ((n : ℝ) + 1) ^ (-s) + ((N : ℝ) + 1) ^ (-s) / 2
        + ((N : ℝ) + 1) ^ (1 - s) / (s - 1) ≤
      ∑' n : ℕ, ((n : ℝ) + 1) ^ (-s) := by
  rw [← (summable_shift hs).sum_add_tsum_nat_add N]
  have hsum : Summable fun i : ℕ => ((↑(i + N) : ℝ) + 1) ^ (-s) :=
    (summable_nat_add_iff N).mpr (summable_shift hs)
  have hs1 : 0 < s - 1 := by linarith
  suffices h : ((N : ℝ) + 1) ^ (-s) / 2 + ((N : ℝ) + 1) ^ (1 - s) / (s - 1) ≤
      ∑' i : ℕ, ((↑(i + N) : ℝ) + 1) ^ (-s) by linarith
  have hlim : Tendsto (fun k : ℕ => ((N : ℝ) + 1) ^ (-s) / 2 +
      (((N : ℝ) + 1) ^ (1 - s) - ((N : ℝ) + k + 1) ^ (1 - s)) / (s - 1)) atTop
      (𝓝 (((N : ℝ) + 1) ^ (-s) / 2 + (((N : ℝ) + 1) ^ (1 - s) - 0) / (s - 1))) := by
    apply Tendsto.const_add
    apply Tendsto.div_const
    apply Tendsto.const_sub
    have h1 : Tendsto (fun k : ℕ => (N : ℝ) + k + 1) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_neg_atTop (y := s - 1) hs1).comp h1
    have e : -(s - 1) = 1 - s := by ring
    simpa [Function.comp_def, e] using h2
  rw [sub_zero] at hlim
  refine le_of_tendsto' hlim fun k => ?_
  refine (sum_tail_ge hs N k).trans ?_
  have hp : (0 : ℝ) ≤ ((N : ℝ) + k + 1) ^ (-s) / 2 := by positivity
  have := hsum.sum_le_tsum (range (k + 1)) (fun i _ => by positivity)
  linarith

/-- Certified upper enclosure of a negative rational power: x^(-(a/b)) ≤ r when
1 ≤ r^b x^a. -/
lemma rpow_neg_le {x r : ℝ} (a b : ℕ) (hb : 0 < b) (hx : 0 < x) (hr : 0 < r)
    (h : 1 ≤ r ^ b * x ^ a) : x ^ (-((a : ℝ) / b)) ≤ r := by
  have hb' : (b : ℝ) ≠ 0 := by positivity
  have e1 : x ^ (-((a : ℝ) / b)) = ((x ^ a)⁻¹) ^ ((b : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hx.le, ← Real.rpow_mul hx.le]
    congr 1; field_simp
  have e2 : r = (r ^ b) ^ ((b : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, mul_inv_cancel₀ hb', Real.rpow_one]
  rw [e1, e2]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  exact h

/-- Certified lower enclosure of a negative rational power: r ≤ x^(-(a/b)) when
r^b x^a ≤ 1. -/
lemma le_rpow_neg {x r : ℝ} (a b : ℕ) (hb : 0 < b) (hx : 0 < x) (hr : 0 < r)
    (h : r ^ b * x ^ a ≤ 1) : r ≤ x ^ (-((a : ℝ) / b)) := by
  have hb' : (b : ℝ) ≠ 0 := by positivity
  have e1 : x ^ (-((a : ℝ) / b)) = ((x ^ a)⁻¹) ^ ((b : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hx.le, ← Real.rpow_mul hx.le]
    congr 1; field_simp
  have e2 : r = (r ^ b) ^ ((b : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, mul_inv_cancel₀ hb', Real.rpow_one]
  rw [e1, e2]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  rw [← one_div, le_div_iff₀ (by positivity)]
  exact h

/-- One step of the certified upper enclosure of a partial sum of n^(-(a/b)). -/
lemma step_up (a b : ℕ) (hb : 0 < b) (k : ℕ) (c r c' : ℝ)
    (hprev : ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-((a : ℝ) / b)) ≤ c) (hr : 0 < r)
    (h : 1 ≤ r ^ b * ((k : ℝ) + 1) ^ a) (hc : c + r ≤ c') :
    ∑ n ∈ range (k + 1), ((n : ℝ) + 1) ^ (-((a : ℝ) / b)) ≤ c' := by
  rw [sum_range_succ]
  have := rpow_neg_le a b hb (by positivity) hr h
  linarith

/-- One step of the certified lower enclosure of a partial sum of n^(-(a/b)). -/
lemma step_lo (a b : ℕ) (hb : 0 < b) (k : ℕ) (c r c' : ℝ)
    (hprev : c ≤ ∑ n ∈ range k, ((n : ℝ) + 1) ^ (-((a : ℝ) / b))) (hr : 0 < r)
    (h : r ^ b * ((k : ℝ) + 1) ^ a ≤ 1) (hc : c' ≤ c + r) :
    c' ≤ ∑ n ∈ range (k + 1), ((n : ℝ) + 1) ^ (-((a : ℝ) / b)) := by
  rw [sum_range_succ]
  have := le_rpow_neg a b hb (by positivity) hr h
  linarith

lemma upper98_20 :
    ∑ n ∈ range 20, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 3.10202339484 := by
  have hs : ∑ n ∈ range 0, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 0.00000000000 := by norm_num
  have h1 := step_up 9 8 (by norm_num) 0 0.00000000000 1.00000000000 1.00000000000 hs
    (by norm_num) (by norm_num) (by norm_num)
  have h2 := step_up 9 8 (by norm_num) 1 1.00000000000 0.45850202161 1.45850202161 h1
    (by norm_num) (by norm_num) (by norm_num)
  have h3 := step_up 9 8 (by norm_num) 2 1.45850202161 0.29056184763 1.74906386924 h2
    (by norm_num) (by norm_num) (by norm_num)
  have h4 := step_up 9 8 (by norm_num) 3 1.74906386924 0.21022410382 1.95928797306 h3
    (by norm_num) (by norm_num) (by norm_num)
  have h5 := step_up 9 8 (by norm_num) 4 1.95928797306 0.16355308680 2.12284105986 h4
    (by norm_num) (by norm_num) (by norm_num)
  have h6 := step_up 9 8 (by norm_num) 5 2.12284105986 0.13322319454 2.25606425440 h5
    (by norm_num) (by norm_num) (by norm_num)
  have h7 := step_up 9 8 (by norm_num) 6 2.25606425440 0.11201203953 2.36807629393 h6
    (by norm_num) (by norm_num) (by norm_num)
  have h8 := step_up 9 8 (by norm_num) 7 2.36807629393 0.09638817659 2.46446447052 h7
    (by norm_num) (by norm_num) (by norm_num)
  have h9 := step_up 9 8 (by norm_num) 8 2.46446447052 0.08442618730 2.54889065782 h8
    (by norm_num) (by norm_num) (by norm_num)
  have h10 := step_up 9 8 (by norm_num) 9 2.54889065782 0.07498942094 2.62388007876 h9
    (by norm_num) (by norm_num) (by norm_num)
  have h11 := step_up 9 8 (by norm_num) 10 2.62388007876 0.06736483172 2.69124491048 h10
    (by norm_num) (by norm_num) (by norm_num)
  have h12 := step_up 9 8 (by norm_num) 11 2.69124491048 0.06108310402 2.75232801450 h11
    (by norm_num) (by norm_num) (by norm_num)
  have h13 := step_up 9 8 (by norm_num) 12 2.75232801450 0.05582307151 2.80815108601 h12
    (by norm_num) (by norm_num) (by norm_num)
  have h14 := step_up 9 8 (by norm_num) 13 2.80815108601 0.05135774657 2.85950883258 h13
    (by norm_num) (by norm_num) (by norm_num)
  have h15 := step_up 9 8 (by norm_num) 14 2.85950883258 0.04752228709 2.90703111967 h14
    (by norm_num) (by norm_num) (by norm_num)
  have h16 := step_up 9 8 (by norm_num) 15 2.90703111967 0.04419417383 2.95122529350 h15
    (by norm_num) (by norm_num) (by norm_num)
  have h17 := step_up 9 8 (by norm_num) 16 2.95122529350 0.04128050138 2.99250579488 h16
    (by norm_num) (by norm_num) (by norm_num)
  have h18 := step_up 9 8 (by norm_num) 17 2.99250579488 0.03870957756 3.03121537244 h17
    (by norm_num) (by norm_num) (by norm_num)
  have h19 := step_up 9 8 (by norm_num) 18 3.03121537244 0.03642522130 3.06764059374 h18
    (by norm_num) (by norm_num) (by norm_num)
  have h20 := step_up 9 8 (by norm_num) 19 3.06764059374 0.03438280110 3.10202339484 h19
    (by norm_num) (by norm_num) (by norm_num)
  exact h20

lemma upper98_40 :
    ∑ n ∈ range 40, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 3.54941982134 := by
  have hs : ∑ n ∈ range 20, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 3.10202339484 := upper98_20
  have h21 := step_up 9 8 (by norm_num) 20 3.10202339484 0.03254642517 3.13456982001 hs
    (by norm_num) (by norm_num) (by norm_num)
  have h22 := step_up 9 8 (by norm_num) 21 3.13456982001 0.03088691153 3.16545673154 h21
    (by norm_num) (by norm_num) (by norm_num)
  have h23 := step_up 9 8 (by norm_num) 22 3.16545673154 0.02938029719 3.19483702873 h22
    (by norm_num) (by norm_num) (by norm_num)
  have h24 := step_up 9 8 (by norm_num) 23 3.19483702873 0.02800672668 3.22284375541 h23
    (by norm_num) (by norm_num) (by norm_num)
  have h25 := step_up 9 8 (by norm_num) 24 3.22284375541 0.02674961220 3.24959336761 h24
    (by norm_num) (by norm_num) (by norm_num)
  have h26 := step_up 9 8 (by norm_num) 25 3.24959336761 0.02559499114 3.27518835875 h25
    (by norm_num) (by norm_num) (by norm_num)
  have h27 := step_up 9 8 (by norm_num) 26 3.27518835875 0.02453102897 3.29971938772 h26
    (by norm_num) (by norm_num) (by norm_num)
  have h28 := step_up 9 8 (by norm_num) 27 3.29971938772 0.02354763063 3.32326701835 h27
    (by norm_num) (by norm_num) (by norm_num)
  have h29 := step_up 9 8 (by norm_num) 28 3.32326701835 0.02263613381 3.34590315216 h28
    (by norm_num) (by norm_num) (by norm_num)
  have h30 := step_up 9 8 (by norm_num) 29 3.34590315216 0.02178906470 3.36769221686 h29
    (by norm_num) (by norm_num) (by norm_num)
  have h31 := step_up 9 8 (by norm_num) 30 3.36769221686 0.02099994197 3.38869215883 h30
    (by norm_num) (by norm_num) (by norm_num)
  have h32 := step_up 9 8 (by norm_num) 31 3.38869215883 0.02026311805 3.40895527688 h31
    (by norm_num) (by norm_num) (by norm_num)
  have h33 := step_up 9 8 (by norm_num) 32 3.40895527688 0.01957364997 3.42852892685 h32
    (by norm_num) (by norm_num) (by norm_num)
  have h34 := step_up 9 8 (by norm_num) 33 3.42852892685 0.01892719334 3.44745612019 h33
    (by norm_num) (by norm_num) (by norm_num)
  have h35 := step_up 9 8 (by norm_num) 34 3.44745612019 0.01831991483 3.46577603502 h34
    (by norm_num) (by norm_num) (by norm_num)
  have h36 := step_up 9 8 (by norm_num) 35 3.46577603502 0.01774841957 3.48352445459 h35
    (by norm_num) (by norm_num) (by norm_num)
  have h37 := step_up 9 8 (by norm_num) 36 3.48352445459 0.01720969052 3.50073414511 h36
    (by norm_num) (by norm_num) (by norm_num)
  have h38 := step_up 9 8 (by norm_num) 37 3.50073414511 0.01670103761 3.51743518272 h37
    (by norm_num) (by norm_num) (by norm_num)
  have h39 := step_up 9 8 (by norm_num) 38 3.51743518272 0.01622005480 3.53365523752 h38
    (by norm_num) (by norm_num) (by norm_num)
  have h40 := step_up 9 8 (by norm_num) 39 3.53365523752 0.01576458382 3.54941982134 h39
    (by norm_num) (by norm_num) (by norm_num)
  exact h40

lemma upper98_60 :
    ∑ n ∈ range 60, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 3.79586234820 := by
  have hs : ∑ n ∈ range 40, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 3.54941982134 := upper98_40
  have h41 := step_up 9 8 (by norm_num) 40 3.54941982134 0.01533268316 3.56475250450 hs
    (by norm_num) (by norm_num) (by norm_num)
  have h42 := step_up 9 8 (by norm_num) 41 3.56475250450 0.01492260174 3.57967510624 h41
    (by norm_num) (by norm_num) (by norm_num)
  have h43 := step_up 9 8 (by norm_num) 42 3.57967510624 0.01453275619 3.59420786243 h42
    (by norm_num) (by norm_num) (by norm_num)
  have h44 := step_up 9 8 (by norm_num) 43 3.59420786243 0.01416171138 3.60836957381 h43
    (by norm_num) (by norm_num) (by norm_num)
  have h45 := step_up 9 8 (by norm_num) 44 3.60836957381 0.01380816354 3.62217773735 h44
    (by norm_num) (by norm_num) (by norm_num)
  have h46 := step_up 9 8 (by norm_num) 45 3.62217773735 0.01347092566 3.63564866301 h45
    (by norm_num) (by norm_num) (by norm_num)
  have h47 := step_up 9 8 (by norm_num) 46 3.63564866301 0.01314891476 3.64879757777 h46
    (by norm_num) (by norm_num) (by norm_num)
  have h48 := step_up 9 8 (by norm_num) 47 3.64879757777 0.01284114081 3.66163871858 h47
    (by norm_num) (by norm_num) (by norm_num)
  have h49 := step_up 9 8 (by norm_num) 48 3.66163871858 0.01254669700 3.67418541558 h48
    (by norm_num) (by norm_num) (by norm_num)
  have h50 := step_up 9 8 (by norm_num) 49 3.67418541558 0.01226475128 3.68645016686 h49
    (by norm_num) (by norm_num) (by norm_num)
  have h51 := step_up 9 8 (by norm_num) 50 3.68645016686 0.01199453876 3.69844470562 h50
    (by norm_num) (by norm_num) (by norm_num)
  have h52 := step_up 9 8 (by norm_num) 51 3.69844470562 0.01173535519 3.71018006081 h51
    (by norm_num) (by norm_num) (by norm_num)
  have h53 := step_up 9 8 (by norm_num) 52 3.71018006081 0.01148655105 3.72166661186 h52
    (by norm_num) (by norm_num) (by norm_num)
  have h54 := step_up 9 8 (by norm_num) 53 3.72166661186 0.01124752638 3.73291413824 h53
    (by norm_num) (by norm_num) (by norm_num)
  have h55 := step_up 9 8 (by norm_num) 54 3.73291413824 0.01101772617 3.74393186441 h54
    (by norm_num) (by norm_num) (by norm_num)
  have h56 := step_up 9 8 (by norm_num) 55 3.74393186441 0.01079663625 3.75472850066 h55
    (by norm_num) (by norm_num) (by norm_num)
  have h57 := step_up 9 8 (by norm_num) 56 3.75472850066 0.01058377960 3.76531228026 h56
    (by norm_num) (by norm_num) (by norm_num)
  have h58 := step_up 9 8 (by norm_num) 57 3.76531228026 0.01037871311 3.77569099337 h57
    (by norm_num) (by norm_num) (by norm_num)
  have h59 := step_up 9 8 (by norm_num) 58 3.77569099337 0.01018102461 3.78587201798 h58
    (by norm_num) (by norm_num) (by norm_num)
  have h60 := step_up 9 8 (by norm_num) 59 3.78587201798 0.00999033022 3.79586234820 h59
    (by norm_num) (by norm_num) (by norm_num)
  exact h60

lemma upper98_80 :
    ∑ n ∈ range 80, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 3.96386700124 := by
  have hs : ∑ n ∈ range 60, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 3.79586234820 := upper98_60
  have h61 := step_up 9 8 (by norm_num) 60 3.79586234820 0.00980627201 3.80566862021 hs
    (by norm_num) (by norm_num) (by norm_num)
  have h62 := step_up 9 8 (by norm_num) 61 3.80566862021 0.00962851585 3.81529713606 h61
    (by norm_num) (by norm_num) (by norm_num)
  have h63 := step_up 9 8 (by norm_num) 62 3.81529713606 0.00945674943 3.82475388549 h62
    (by norm_num) (by norm_num) (by norm_num)
  have h64 := step_up 9 8 (by norm_num) 63 3.82475388549 0.00929068059 3.83404456608 h63
    (by norm_num) (by norm_num) (by norm_num)
  have h65 := step_up 9 8 (by norm_num) 64 3.83404456608 0.00913003566 3.84317460174 h64
    (by norm_num) (by norm_num) (by norm_num)
  have h66 := step_up 9 8 (by norm_num) 65 3.84317460174 0.00897455809 3.85214915983 h65
    (by norm_num) (by norm_num) (by norm_num)
  have h67 := step_up 9 8 (by norm_num) 66 3.85214915983 0.00882400707 3.86097316690 h66
    (by norm_num) (by norm_num) (by norm_num)
  have h68 := step_up 9 8 (by norm_num) 67 3.86097316690 0.00867815641 3.86965132331 h67
    (by norm_num) (by norm_num) (by norm_num)
  have h69 := step_up 9 8 (by norm_num) 68 3.86965132331 0.00853679344 3.87818811675 h68
    (by norm_num) (by norm_num) (by norm_num)
  have h70 := step_up 9 8 (by norm_num) 69 3.87818811675 0.00839971799 3.88658783474 h69
    (by norm_num) (by norm_num) (by norm_num)
  have h71 := step_up 9 8 (by norm_num) 70 3.88658783474 0.00826674151 3.89485457625 h70
    (by norm_num) (by norm_num) (by norm_num)
  have h72 := step_up 9 8 (by norm_num) 71 3.89485457625 0.00813768625 3.90299226250 h71
    (by norm_num) (by norm_num) (by norm_num)
  have h73 := step_up 9 8 (by norm_num) 72 3.90299226250 0.00801238451 3.91100464701 h72
    (by norm_num) (by norm_num) (by norm_num)
  have h74 := step_up 9 8 (by norm_num) 73 3.91100464701 0.00789067790 3.91889532491 h73
    (by norm_num) (by norm_num) (by norm_num)
  have h75 := step_up 9 8 (by norm_num) 74 3.91889532491 0.00777241675 3.92666774166 h74
    (by norm_num) (by norm_num) (by norm_num)
  have h76 := step_up 9 8 (by norm_num) 75 3.92666774166 0.00765745951 3.93432520117 h75
    (by norm_num) (by norm_num) (by norm_num)
  have h77 := step_up 9 8 (by norm_num) 76 3.93432520117 0.00754567220 3.94187087337 h76
    (by norm_num) (by norm_num) (by norm_num)
  have h78 := step_up 9 8 (by norm_num) 77 3.94187087337 0.00743692792 3.94930780129 h77
    (by norm_num) (by norm_num) (by norm_num)
  have h79 := step_up 9 8 (by norm_num) 78 3.94930780129 0.00733110640 3.95663890769 h78
    (by norm_num) (by norm_num) (by norm_num)
  have h80 := step_up 9 8 (by norm_num) 79 3.95663890769 0.00722809355 3.96386700124 h79
    (by norm_num) (by norm_num) (by norm_num)
  exact h80

lemma upper98_100 :
    ∑ n ∈ range 100, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 4.09031712823 := by
  have hs : ∑ n ∈ range 80, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 3.96386700124 := upper98_80
  have h81 := step_up 9 8 (by norm_num) 80 3.96386700124 0.00712778111 3.97099478235 hs
    (by norm_num) (by norm_num) (by norm_num)
  have h82 := step_up 9 8 (by norm_num) 81 3.97099478235 0.00703006623 3.97802484858 h81
    (by norm_num) (by norm_num) (by norm_num)
  have h83 := step_up 9 8 (by norm_num) 82 3.97802484858 0.00693485119 3.98495969977 h82
    (by norm_num) (by norm_num) (by norm_num)
  have h84 := step_up 9 8 (by norm_num) 83 3.98495969977 0.00684204307 3.99180174284 h83
    (by norm_num) (by norm_num) (by norm_num)
  have h85 := step_up 9 8 (by norm_num) 84 3.99180174284 0.00675155343 3.99855329627 h84
    (by norm_num) (by norm_num) (by norm_num)
  have h86 := step_up 9 8 (by norm_num) 85 3.99855329627 0.00666329810 4.00521659437 h85
    (by norm_num) (by norm_num) (by norm_num)
  have h87 := step_up 9 8 (by norm_num) 86 4.00521659437 0.00657719687 4.01179379124 h86
    (by norm_num) (by norm_num) (by norm_num)
  have h88 := step_up 9 8 (by norm_num) 87 4.01179379124 0.00649317330 4.01828696454 h87
    (by norm_num) (by norm_num) (by norm_num)
  have h89 := step_up 9 8 (by norm_num) 88 4.01828696454 0.00641115450 4.02469811904 h88
    (by norm_num) (by norm_num) (by norm_num)
  have h90 := step_up 9 8 (by norm_num) 89 4.02469811904 0.00633107090 4.03102918994 h89
    (by norm_num) (by norm_num) (by norm_num)
  have h91 := step_up 9 8 (by norm_num) 90 4.03102918994 0.00625285610 4.03728204604 h90
    (by norm_num) (by norm_num) (by norm_num)
  have h92 := step_up 9 8 (by norm_num) 91 4.03728204604 0.00617644665 4.04345849269 h91
    (by norm_num) (by norm_num) (by norm_num)
  have h93 := step_up 9 8 (by norm_num) 92 4.04345849269 0.00610178194 4.04956027463 h92
    (by norm_num) (by norm_num) (by norm_num)
  have h94 := step_up 9 8 (by norm_num) 93 4.04956027463 0.00602880400 4.05558907863 h93
    (by norm_num) (by norm_num) (by norm_num)
  have h95 := step_up 9 8 (by norm_num) 94 4.05558907863 0.00595745738 4.06154653601 h94
    (by norm_num) (by norm_num) (by norm_num)
  have h96 := step_up 9 8 (by norm_num) 95 4.06154653601 0.00588768902 4.06743422503 h95
    (by norm_num) (by norm_num) (by norm_num)
  have h97 := step_up 9 8 (by norm_num) 96 4.06743422503 0.00581944810 4.07325367313 h96
    (by norm_num) (by norm_num) (by norm_num)
  have h98 := step_up 9 8 (by norm_num) 97 4.07325367313 0.00575268594 4.07900635907 h97
    (by norm_num) (by norm_num) (by norm_num)
  have h99 := step_up 9 8 (by norm_num) 98 4.07900635907 0.00568735590 4.08469371497 h98
    (by norm_num) (by norm_num) (by norm_num)
  have h100 := step_up 9 8 (by norm_num) 99 4.08469371497 0.00562341326 4.09031712823 h99
    (by norm_num) (by norm_num) (by norm_num)
  exact h100

lemma upper98_120 :
    ∑ n ∈ range 120, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 4.19116487465 := by
  have hs : ∑ n ∈ range 100, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ))) ≤ 4.09031712823 := upper98_100
  have h101 := step_up 9 8 (by norm_num) 100 4.09031712823 0.00556081510 4.09587794333 hs
    (by norm_num) (by norm_num) (by norm_num)
  have h102 := step_up 9 8 (by norm_num) 101 4.09587794333 0.00549952027 4.10137746360 h101
    (by norm_num) (by norm_num) (by norm_num)
  have h103 := step_up 9 8 (by norm_num) 102 4.10137746360 0.00543948925 4.10681695285 h102
    (by norm_num) (by norm_num) (by norm_num)
  have h104 := step_up 9 8 (by norm_num) 103 4.10681695285 0.00538068408 4.11219763693 h103
    (by norm_num) (by norm_num) (by norm_num)
  have h105 := step_up 9 8 (by norm_num) 104 4.11219763693 0.00532306830 4.11752070523 h104
    (by norm_num) (by norm_num) (by norm_num)
  have h106 := step_up 9 8 (by norm_num) 105 4.11752070523 0.00526660688 4.12278731211 h105
    (by norm_num) (by norm_num) (by norm_num)
  have h107 := step_up 9 8 (by norm_num) 106 4.12278731211 0.00521126611 4.12799857822 h106
    (by norm_num) (by norm_num) (by norm_num)
  have h108 := step_up 9 8 (by norm_num) 107 4.12799857822 0.00515701359 4.13315559181 h107
    (by norm_num) (by norm_num) (by norm_num)
  have h109 := step_up 9 8 (by norm_num) 108 4.13315559181 0.00510381813 4.13825940994 h108
    (by norm_num) (by norm_num) (by norm_num)
  have h110 := step_up 9 8 (by norm_num) 109 4.13825940994 0.00505164973 4.14331105967 h109
    (by norm_num) (by norm_num) (by norm_num)
  have h111 := step_up 9 8 (by norm_num) 110 4.14331105967 0.00500047948 4.14831153915 h110
    (by norm_num) (by norm_num) (by norm_num)
  have h112 := step_up 9 8 (by norm_num) 111 4.14831153915 0.00495027955 4.15326181870 h111
    (by norm_num) (by norm_num) (by norm_num)
  have h113 := step_up 9 8 (by norm_num) 112 4.15326181870 0.00490102312 4.15816284182 h112
    (by norm_num) (by norm_num) (by norm_num)
  have h114 := step_up 9 8 (by norm_num) 113 4.15816284182 0.00485268435 4.16301552617 h113
    (by norm_num) (by norm_num) (by norm_num)
  have h115 := step_up 9 8 (by norm_num) 114 4.16301552617 0.00480523830 4.16782076447 h114
    (by norm_num) (by norm_num) (by norm_num)
  have h116 := step_up 9 8 (by norm_num) 115 4.16782076447 0.00475866095 4.17257942542 h115
    (by norm_num) (by norm_num) (by norm_num)
  have h117 := step_up 9 8 (by norm_num) 116 4.17257942542 0.00471292910 4.17729235452 h116
    (by norm_num) (by norm_num) (by norm_num)
  have h118 := step_up 9 8 (by norm_num) 117 4.17729235452 0.00466802037 4.18196037489 h117
    (by norm_num) (by norm_num) (by norm_num)
  have h119 := step_up 9 8 (by norm_num) 118 4.18196037489 0.00462391316 4.18658428805 h118
    (by norm_num) (by norm_num) (by norm_num)
  have h120 := step_up 9 8 (by norm_num) 119 4.18658428805 0.00458058660 4.19116487465 h119
    (by norm_num) (by norm_num) (by norm_num)
  exact h120

lemma lower94_20 :
    1.44187704586 ≤ ∑ n ∈ range 20, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ))) := by
  have hs : 0.00000000000 ≤ ∑ n ∈ range 0, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ))) := by norm_num
  have h1 := step_lo 9 4 (by norm_num) 0 0.00000000000 1.00000000000 1.00000000000 hs
    (by norm_num) (by norm_num) (by norm_num)
  have h2 := step_lo 9 4 (by norm_num) 1 1.00000000000 0.21022410381 1.21022410381 h1
    (by norm_num) (by norm_num) (by norm_num)
  have h3 := step_lo 9 4 (by norm_num) 2 1.21022410381 0.08442618729 1.29465029110 h2
    (by norm_num) (by norm_num) (by norm_num)
  have h4 := step_lo 9 4 (by norm_num) 3 1.29465029110 0.04419417382 1.33884446492 h3
    (by norm_num) (by norm_num) (by norm_num)
  have h5 := step_lo 9 4 (by norm_num) 4 1.33884446492 0.02674961219 1.36559407711 h4
    (by norm_num) (by norm_num) (by norm_num)
  have h6 := step_lo 9 4 (by norm_num) 5 1.36559407711 0.01774841956 1.38334249667 h5
    (by norm_num) (by norm_num) (by norm_num)
  have h7 := step_lo 9 4 (by norm_num) 6 1.38334249667 0.01254669699 1.39588919366 h6
    (by norm_num) (by norm_num) (by norm_num)
  have h8 := step_lo 9 4 (by norm_num) 7 1.39588919366 0.00929068058 1.40517987424 h7
    (by norm_num) (by norm_num) (by norm_num)
  have h9 := step_lo 9 4 (by norm_num) 8 1.40517987424 0.00712778110 1.41230765534 h8
    (by norm_num) (by norm_num) (by norm_num)
  have h10 := step_lo 9 4 (by norm_num) 9 1.41230765534 0.00562341325 1.41793106859 h9
    (by norm_num) (by norm_num) (by norm_num)
  have h11 := step_lo 9 4 (by norm_num) 10 1.41793106859 0.00453802055 1.42246908914 h10
    (by norm_num) (by norm_num) (by norm_num)
  have h12 := step_lo 9 4 (by norm_num) 11 1.42246908914 0.00373114559 1.42620023473 h11
    (by norm_num) (by norm_num) (by norm_num)
  have h13 := step_lo 9 4 (by norm_num) 12 1.42620023473 0.00311621531 1.42931645004 h12
    (by norm_num) (by norm_num) (by norm_num)
  have h14 := step_lo 9 4 (by norm_num) 13 1.42931645004 0.00263761813 1.43195406817 h13
    (by norm_num) (by norm_num) (by norm_num)
  have h15 := step_lo 9 4 (by norm_num) 14 1.43195406817 0.00225836776 1.43421243593 h14
    (by norm_num) (by norm_num) (by norm_num)
  have h16 := step_lo 9 4 (by norm_num) 15 1.43421243593 0.00195312500 1.43616556093 h15
    (by norm_num) (by norm_num) (by norm_num)
  have h17 := step_lo 9 4 (by norm_num) 16 1.43616556093 0.00170407979 1.43786964072 h16
    (by norm_num) (by norm_num) (by norm_num)
  have h18 := step_lo 9 4 (by norm_num) 17 1.43786964072 0.00149843139 1.43936807211 h17
    (by norm_num) (by norm_num) (by norm_num)
  have h19 := step_lo 9 4 (by norm_num) 18 1.43936807211 0.00132679674 1.44069486885 h18
    (by norm_num) (by norm_num) (by norm_num)
  have h20 := step_lo 9 4 (by norm_num) 19 1.44069486885 0.00118217701 1.44187704586 h19
    (by norm_num) (by norm_num) (by norm_num)
  exact h20

lemma lower94_40 :
    1.45238225497 ≤ ∑ n ∈ range 40, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ))) := by
  have hs : 1.44187704586 ≤ ∑ n ∈ range 20, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ))) := lower94_20
  have h21 := step_lo 9 4 (by norm_num) 20 1.44187704586 0.00105926979 1.44293631565 hs
    (by norm_num) (by norm_num) (by norm_num)
  have h22 := step_lo 9 4 (by norm_num) 21 1.44293631565 0.00095400130 1.44389031695 h21
    (by norm_num) (by norm_num) (by norm_num)
  have h23 := step_lo 9 4 (by norm_num) 22 1.44389031695 0.00086320186 1.44475351881 h22
    (by norm_num) (by norm_num) (by norm_num)
  have h24 := step_lo 9 4 (by norm_num) 23 1.44475351881 0.00078437673 1.44553789554 h23
    (by norm_num) (by norm_num) (by norm_num)
  have h25 := step_lo 9 4 (by norm_num) 24 1.44553789554 0.00071554175 1.44625343729 h24
    (by norm_num) (by norm_num) (by norm_num)
  have h26 := step_lo 9 4 (by norm_num) 25 1.44625343729 0.00065510357 1.44690854086 h25
    (by norm_num) (by norm_num) (by norm_num)
  have h27 := step_lo 9 4 (by norm_num) 26 1.44690854086 0.00060177138 1.44751031224 h26
    (by norm_num) (by norm_num) (by norm_num)
  have h28 := step_lo 9 4 (by norm_num) 27 1.44751031224 0.00055449090 1.44806480314 h27
    (by norm_num) (by norm_num) (by norm_num)
  have h29 := step_lo 9 4 (by norm_num) 28 1.44806480314 0.00051239455 1.44857719769 h28
    (by norm_num) (by norm_num) (by norm_num)
  have h30 := step_lo 9 4 (by norm_num) 29 1.44857719769 0.00047476334 1.44905196103 h29
    (by norm_num) (by norm_num) (by norm_num)
  have h31 := step_lo 9 4 (by norm_num) 30 1.44905196103 0.00044099756 1.44949295859 h30
    (by norm_num) (by norm_num) (by norm_num)
  have h32 := step_lo 9 4 (by norm_num) 31 1.44949295859 0.00041059395 1.44990355254 h31
    (by norm_num) (by norm_num) (by norm_num)
  have h33 := step_lo 9 4 (by norm_num) 32 1.44990355254 0.00038312777 1.45028668031 h32
    (by norm_num) (by norm_num) (by norm_num)
  have h34 := step_lo 9 4 (by norm_num) 33 1.45028668031 0.00035823864 1.45064491895 h33
    (by norm_num) (by norm_num) (by norm_num)
  have h35 := step_lo 9 4 (by norm_num) 34 1.45064491895 0.00033561927 1.45098053822 h34
    (by norm_num) (by norm_num) (by norm_num)
  have h36 := step_lo 9 4 (by norm_num) 35 1.45098053822 0.00031500639 1.45129554461 h35
    (by norm_num) (by norm_num) (by norm_num)
  have h37 := step_lo 9 4 (by norm_num) 36 1.45129554461 0.00029617344 1.45159171805 h36
    (by norm_num) (by norm_num) (by norm_num)
  have h38 := step_lo 9 4 (by norm_num) 37 1.45159171805 0.00027892465 1.45187064270 h37
    (by norm_num) (by norm_num) (by norm_num)
  have h39 := step_lo 9 4 (by norm_num) 38 1.45187064270 0.00026309017 1.45213373287 h38
    (by norm_num) (by norm_num) (by norm_num)
  have h40 := step_lo 9 4 (by norm_num) 39 1.45213373287 0.00024852210 1.45238225497 h39
    (by norm_num) (by norm_num) (by norm_num)
  exact h40

lemma lower94_60 :
    1.45547073586 ≤ ∑ n ∈ range 60, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ))) := by
  have hs : 1.45238225497 ≤ ∑ n ∈ range 40, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ))) := lower94_40
  have h41 := step_lo 9 4 (by norm_num) 40 1.45238225497 0.00023509117 1.45261734614 hs
    (by norm_num) (by norm_num) (by norm_num)
  have h42 := step_lo 9 4 (by norm_num) 41 1.45261734614 0.00022268404 1.45284003018 h41
    (by norm_num) (by norm_num) (by norm_num)
  have h43 := step_lo 9 4 (by norm_num) 42 1.45284003018 0.00021120100 1.45305123118 h42
    (by norm_num) (by norm_num) (by norm_num)
  have h44 := step_lo 9 4 (by norm_num) 43 1.45305123118 0.00020055406 1.45325178524 h43
    (by norm_num) (by norm_num) (by norm_num)
  have h45 := step_lo 9 4 (by norm_num) 44 1.45325178524 0.00019066538 1.45344245062 h44
    (by norm_num) (by norm_num) (by norm_num)
  have h46 := step_lo 9 4 (by norm_num) 45 1.45344245062 0.00018146583 1.45362391645 h45
    (by norm_num) (by norm_num) (by norm_num)
  have h47 := step_lo 9 4 (by norm_num) 46 1.45362391645 0.00017289395 1.45379681040 h46
    (by norm_num) (by norm_num) (by norm_num)
  have h48 := step_lo 9 4 (by norm_num) 47 1.45379681040 0.00016489489 1.45396170529 h47
    (by norm_num) (by norm_num) (by norm_num)
  have h49 := step_lo 9 4 (by norm_num) 48 1.45396170529 0.00015741960 1.45411912489 h48
    (by norm_num) (by norm_num) (by norm_num)
  have h50 := step_lo 9 4 (by norm_num) 49 1.45411912489 0.00015042412 1.45426954901 h49
    (by norm_num) (by norm_num) (by norm_num)
  have h51 := step_lo 9 4 (by norm_num) 50 1.45426954901 0.00014386895 1.45441341796 h50
    (by norm_num) (by norm_num) (by norm_num)
  have h52 := step_lo 9 4 (by norm_num) 51 1.45441341796 0.00013771856 1.45455113652 h51
    (by norm_num) (by norm_num) (by norm_num)
  have h53 := step_lo 9 4 (by norm_num) 52 1.45455113652 0.00013194085 1.45468307737 h52
    (by norm_num) (by norm_num) (by norm_num)
  have h54 := step_lo 9 4 (by norm_num) 53 1.45468307737 0.00012650684 1.45480958421 h53
    (by norm_num) (by norm_num) (by norm_num)
  have h55 := step_lo 9 4 (by norm_num) 54 1.45480958421 0.00012139028 1.45493097449 h54
    (by norm_num) (by norm_num) (by norm_num)
  have h56 := step_lo 9 4 (by norm_num) 55 1.45493097449 0.00011656735 1.45504754184 h55
    (by norm_num) (by norm_num) (by norm_num)
  have h57 := step_lo 9 4 (by norm_num) 56 1.45504754184 0.00011201639 1.45515955823 h56
    (by norm_num) (by norm_num) (by norm_num)
  have h58 := step_lo 9 4 (by norm_num) 57 1.45515955823 0.00010771768 1.45526727591 h57
    (by norm_num) (by norm_num) (by norm_num)
  have h59 := step_lo 9 4 (by norm_num) 58 1.45526727591 0.00010365326 1.45537092917 h58
    (by norm_num) (by norm_num) (by norm_num)
  have h60 := step_lo 9 4 (by norm_num) 59 1.45537092917 0.00009980669 1.45547073586 h59
    (by norm_num) (by norm_num) (by norm_num)
  exact h60

lemma lower94_80 :
    1.45689416448 ≤ ∑ n ∈ range 80, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ))) := by
  have hs : 1.45547073586 ≤ ∑ n ∈ range 60, ((n : ℝ) + 1) ^ (-(((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ))) := lower94_60
  have h61 := step_lo 9 4 (by norm_num) 60 1.45547073586 0.00009616297 1.45556689883 hs
    (by norm_num) (by norm_num) (by norm_num)
  have h62 := step_lo 9 4 (by norm_num) 61 1.45556689883 0.00009270831 1.45565960714 h61
    (by norm_num) (by norm_num) (by norm_num)
  have h63 := step_lo 9 4 (by norm_num) 62 1.45565960714 0.00008943010 1.45574903724 h62
    (by norm_num) (by norm_num) (by norm_num)
  have h64 := step_lo 9 4 (by norm_num) 63 1.45574903724 0.00008631674 1.45583535398 h63
    (by norm_num) (by norm_num) (by norm_num)
  have h65 := step_lo 9 4 (by norm_num) 64 1.45583535398 0.00008335755 1.45591871153 h64
    (by norm_num) (by norm_num) (by norm_num)
  have h66 := step_lo 9 4 (by norm_num) 65 1.45591871153 0.00008054269 1.45599925422 h65
    (by norm_num) (by norm_num) (by norm_num)
  have h67 := step_lo 9 4 (by norm_num) 66 1.45599925422 0.00007786310 1.45607711732 h66
    (by norm_num) (by norm_num) (by norm_num)
  have h68 := step_lo 9 4 (by norm_num) 67 1.45607711732 0.00007531039 1.45615242771 h67
    (by norm_num) (by norm_num) (by norm_num)
  have h69 := step_lo 9 4 (by norm_num) 68 1.45615242771 0.00007287684 1.45622530455 h68
    (by norm_num) (by norm_num) (by norm_num)
  have h70 := step_lo 9 4 (by norm_num) 69 1.45622530455 0.00007055526 1.45629585981 h69
    (by norm_num) (by norm_num) (by norm_num)
  have h71 := step_lo 9 4 (by norm_num) 70 1.45629585981 0.00006833901 1.45636419882 h70
    (by norm_num) (by norm_num) (by norm_num)
  have h72 := step_lo 9 4 (by norm_num) 71 1.45636419882 0.00006622193 1.45643042075 h71
    (by norm_num) (by norm_num) (by norm_num)
  have h73 := step_lo 9 4 (by norm_num) 72 1.45643042075 0.00006419830 1.45649461905 h72
    (by norm_num) (by norm_num) (by norm_num)
  have h74 := step_lo 9 4 (by norm_num) 73 1.45649461905 0.00006226279 1.45655688184 h73
    (by norm_num) (by norm_num) (by norm_num)
  have h75 := step_lo 9 4 (by norm_num) 74 1.45655688184 0.00006041046 1.45661729230 h74
    (by norm_num) (by norm_num) (by norm_num)
  have h76 := step_lo 9 4 (by norm_num) 75 1.45661729230 0.00005863668 1.45667592898 h75
    (by norm_num) (by norm_num) (by norm_num)
  have h77 := step_lo 9 4 (by norm_num) 76 1.45667592898 0.00005693716 1.45673286614 h76
    (by norm_num) (by norm_num) (by norm_num)
  have h78 := step_lo 9 4 (by norm_num) 77 1.45673286614 0.00005530789 1.45678817403 h77
    (by norm_num) (by norm_num) (by norm_num)
  have h79 := step_lo 9 4 (by norm_num) 78 1.45678817403 0.00005374512 1.45684191915 h78
    (by norm_num) (by norm_num) (by norm_num)
  have h80 := step_lo 9 4 (by norm_num) 79 1.45684191915 0.00005224533 1.45689416448 h79
    (by norm_num) (by norm_num) (by norm_num)
  exact h80

/-- zeta(9/8) is at most 8.58624306873; true value 8.5862412945. -/
lemma zeta98_le : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(9 / 8 : ℝ)) ≤ 8.58624306873 := by
  have h := zeta_le (s := 9 / 8) (by norm_num) 120
  have e : (-(9 / 8 : ℝ)) = -(((9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) := by norm_num
  have hS := upper98_120
  rw [← e] at hS
  have ht : (((120 : ℕ) : ℝ) + 1 / 2) ^ (1 - (9 / 8 : ℝ)) ≤ 0.54938477426 := by
    have e2 : (1 - (9 / 8 : ℝ)) = -(((1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) := by norm_num
    rw [e2]
    exact rpow_neg_le 1 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd : (((120 : ℕ) : ℝ) + 1 / 2) ^ (1 - (9 / 8 : ℝ)) / (9 / 8 - 1) ≤ 8 * 0.54938477426 := by
    have : ((9 : ℝ) / 8 - 1) = 1 / 8 := by norm_num
    rw [this]
    linarith
  linarith

/-- zeta(9/4) is at least 1.46021174817; true value 1.4602118617. -/
lemma le_zeta94 : 1.46021174817 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(9 / 4 : ℝ)) := by
  have h := le_zeta (s := 9 / 4) (by norm_num) 80
  have e : (-(9 / 4 : ℝ)) = -(((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) := by norm_num
  have hS := lower94_80
  rw [← e] at hS
  have h1 : 0.00005080526 ≤ (((80 : ℕ) : ℝ) + 1) ^ (-(9 / 4 : ℝ)) := by
    rw [e]
    exact le_rpow_neg 9 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : 0.00411522633 ≤ (((80 : ℕ) : ℝ) + 1) ^ (1 - (9 / 4 : ℝ)) := by
    have e2 : (1 - (9 / 4 : ℝ)) = -(((5 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) := by norm_num
    rw [e2]
    exact le_rpow_neg 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd : (4 / 5 : ℝ) * 0.00411522633 ≤ (((80 : ℕ) : ℝ) + 1) ^ (1 - (9 / 4 : ℝ)) / (9 / 4 - 1) := by
    have : ((9 : ℝ) / 4 - 1) = 5 / 4 := by norm_num
    rw [this]
    linarith
  linarith

/-- P0014 page 37, the numerical input of the constant c of Lemma 4.2:
zeta(9/8)/zeta(9/4) ≤ 5.880137. True value 5.8801339. -/
theorem zeta_ratio_le :
    ‖riemannZeta (9 / 8)‖ / ‖riemannZeta (9 / 4)‖ ≤ 5.880137 := by
  have e1 : (9 / 8 : ℂ) = ((9 / 8 : ℝ) : ℂ) := by push_cast; rfl
  have e2 : (9 / 4 : ℂ) = ((9 / 4 : ℝ) : ℂ) := by push_cast; rfl
  have hU := zeta98_le
  have hL := le_zeta94
  rw [e1, e2, zeta_real (by norm_num), zeta_real (by norm_num), Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun n => by positivity),
    Real.norm_of_nonneg (tsum_nonneg fun n => by positivity),
    div_le_iff₀ (by linarith)]
  linarith

end LeanLab.HelfgottMajor.ZetaRatio123
