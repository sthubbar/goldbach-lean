module

public import Mathlib
public import LeanLab.HeathBrown1985.Sigma1Abel
public import LeanLab.HeathBrown1985.Sigma2
public import LeanLab.HeathBrown1985.DivMoments

/-!
P0096 Heath-Brown 1985, page 54, the bound 3.2: Σ₁ ≪ x² L⁶ Q⁻¹ for Q = L^B.
PROVED here: bound3_2_of, Bound3_2 from Lemma 1, 2.7, alone, and bound3_2_of_siegelWalfisz.
Route: partial summation in Sigma1Abel.lean reduces each inner sum to the progression sums
of Δ_Q up to t ≤ x; these are bounded by 2.7 for t > √x and trivially for t ≤ √x; the sum
over m of (c, m) is at most 2x d(c), and Σ_{c ≤ Q} d(c)²/c ≤ (1 + log Q)⁴ from DivMoments.lean.
Lemma 1 is used with A = 2B + 5; the range 2 ≤ x ≤ X0 is handled by a crude bound.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

theorem abs_DeltaQ_le_cube_log (Q : ℝ) (hQ : 0 ≤ Q) (n : ℕ) :
    |DeltaQ Q n| ≤ Q ^ 3 + Real.log n := by
  unfold DeltaQ
  refine (abs_sub _ _).trans (add_le_add (abs_LambdaQ_le_cube Q hQ n) ?_)
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact ArithmeticFunction.vonMangoldt_le_log

/-- The trivial bound `|Σ_{n ≤ t, n ≡ m (c)} Δ_Q(n)| ≤ t (Q³ + log t)`. -/
theorem abs_apSum_crude (Q : ℝ) (hQ : 0 ≤ Q) (t c m : ℕ) :
    |apSum (DeltaQ Q) (t : ℝ) c m| ≤ t * (Q ^ 3 + Real.log t) := by
  unfold apSum; rw [Nat.floor_natCast]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ n ∈ Icc 1 t, |DeltaQ Q n| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ n ∈ Icc 1 t, (Q ^ 3 + Real.log t) := by
        apply sum_le_sum; intro n hn
        have hn1 := (mem_Icc.mp hn).1
        refine (abs_DeltaQ_le_cube_log Q hQ n).trans ?_
        have : Real.log n ≤ Real.log t :=
          Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast (mem_Icc.mp hn).2)
        linarith
    _ = _ := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp

theorem gcd_le_sum_divisors (c m : ℕ) (hc : 1 ≤ c) :
    (Nat.gcd c m : ℝ) ≤ ∑ a ∈ c.divisors.filter (fun a => m % a = 0), (a : ℝ) := by
  have hmem : Nat.gcd c m ∈ c.divisors.filter (fun a => m % a = 0) := by
    simp only [mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.gcd_dvd_left c m, by omega⟩, Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right c m)⟩
  exact single_le_sum (f := fun a : ℕ => (a : ℝ)) (fun _ _ => by positivity) hmem

/-- `Σ_{2x < m ≤ 3x} (c, m) ≤ 2x d(c)` for `1 ≤ c ≤ x`. -/
theorem sum_gcd_mRange_le (x : ℝ) (hx : 1 ≤ x) (c : ℕ) (hc : 1 ≤ c) (hcx : (c : ℝ) ≤ x) :
    ∑ m ∈ mRange x, (Nat.gcd c m : ℝ) ≤ 2 * x * (c.divisors.card : ℝ) := by
  calc ∑ m ∈ mRange x, (Nat.gcd c m : ℝ)
      ≤ ∑ m ∈ mRange x, ∑ a ∈ c.divisors.filter (fun a => m % a = 0), (a : ℝ) :=
        sum_le_sum (fun m _ => gcd_le_sum_divisors c m hc)
    _ = ∑ a ∈ c.divisors, ∑ m ∈ (mRange x).filter (fun m => m % a = 0), (a : ℝ) := by
        rw [Finset.sum_comm' (t' := c.divisors)
          (s' := fun a => (mRange x).filter (fun m => m % a = 0))]
        intro m a
        simp only [mem_filter]
        tauto
    _ ≤ ∑ a ∈ c.divisors, 2 * x := by
        apply sum_le_sum; intro a ha
        have ha1 : 1 ≤ a := Nat.pos_of_mem_divisors ha
        have hac : a ≤ c := Nat.divisor_le ha
        have haR : (0 : ℝ) < a := by exact_mod_cast ha1
        rw [sum_const, nsmul_eq_mul]
        have h := card_mRange_mod_le x hx a 0 ha1 (le_trans (by exact_mod_cast hac) hcx)
        calc _ ≤ 2 * x / a * a := mul_le_mul_of_nonneg_right h haR.le
          _ = 2 * x := by field_simp
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

/-- The progression sums of `Δ_Q` up to `t ≤ x`, from 2.7 for `t > √x` and trivially below. -/
theorem apSum_bound (A K7 : ℝ) (hA : 0 < A)
    (hK7 : ∀ x : ℝ, 2 ≤ x → ∀ Q : ℝ, 1 ≤ Q → Q ≤ x → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
      |apSum (DeltaQ Q) x k l| ≤
        K7 * (Q * Real.log x ^ 2 + x * Real.log x / (k * Q) * (Nat.gcd k l : ℝ) *
          (k.divisors.card : ℝ) + x * Real.log x ^ (-A)))
    (x Q : ℝ) (hx4 : 4 ≤ x) (hQ1 : 1 ≤ Q) (hQs : Q ≤ Real.sqrt x)
    (c m : ℕ) (hc : 1 ≤ c) (hcQ : (c : ℝ) ≤ Q) (t : ℕ) (ht : 1 ≤ t) (htx : t ≤ ⌊x⌋₊) :
    |apSum (DeltaQ Q) (t : ℝ) c m| ≤
      (|K7| * (Q * Real.log x ^ 2 + x * (Real.log x / 2) ^ (-A)) +
        Real.sqrt x * (Q ^ 3 + Real.log x)) +
      |K7| * x * Real.log x * (c.divisors.card : ℝ) / (c * Q) * (Nat.gcd c m : ℝ) := by
  set L := Real.log x
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hQ0 : 0 < Q := by linarith
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hsx : 2 ≤ Real.sqrt x := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx4
  have htR : (t : ℝ) ≤ x := le_trans (by exact_mod_cast htx) (Nat.floor_le hx0.le)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlt : Real.log t ≤ L := Real.log_le_log (by linarith) htR
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hP0 : 0 ≤ |K7| * (Q * L ^ 2 + x * (L / 2) ^ (-A)) := by positivity
  have hS0 : 0 ≤ Real.sqrt x * (Q ^ 3 + L) := by positivity
  have hR0 : 0 ≤ |K7| * x * L * (c.divisors.card : ℝ) / (c * Q) * (Nat.gcd c m : ℝ) := by
    positivity
  rcases le_or_gt (t : ℝ) (Real.sqrt x) with h | h
  · have h1 := abs_apSum_crude Q hQ0.le t c m
    have h2 : (t : ℝ) * (Q ^ 3 + Real.log t) ≤ Real.sqrt x * (Q ^ 3 + L) :=
      mul_le_mul h (by linarith) (by positivity) (by positivity)
    linarith
  · have hlt2 : L / 2 ≤ Real.log t := by
      rw [← Real.log_sqrt hx0.le]
      exact Real.log_le_log (by linarith) h.le
    have ht2 : (2 : ℝ) ≤ t := by linarith
    have hQt : Q ≤ t := by linarith
    have hct : (c : ℝ) ≤ t := by linarith
    have hk := hK7 t ht2 Q hQ1 hQt c m hc hct
    set g := (Nat.gcd c m : ℝ)
    set d := (c.divisors.card : ℝ)
    have hg0 : 0 ≤ g := by positivity
    have hd0 : 0 ≤ d := by positivity
    have p1 : Q * Real.log t ^ 2 ≤ Q * L ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlt0 hlt 2) hQ0.le
    have p2 : (t : ℝ) * Real.log t / (c * Q) * g * d ≤ x * L / (c * Q) * g * d := by
      have := mul_le_mul htR hlt hlt0 hx0.le
      apply mul_le_mul_of_nonneg_right _ hd0
      apply mul_le_mul_of_nonneg_right _ hg0
      exact div_le_div_of_nonneg_right this (by positivity)
    have p3 : (t : ℝ) * Real.log t ^ (-A) ≤ x * (L / 2) ^ (-A) :=
      mul_le_mul htR (Real.rpow_le_rpow_of_nonpos (by positivity) hlt2 (by linarith))
        (by positivity) hx0.le
    have hX0 : 0 ≤ Q * Real.log t ^ 2 + (t : ℝ) * Real.log t / (c * Q) * g * d +
        (t : ℝ) * Real.log t ^ (-A) := by positivity
    have hX : Q * Real.log t ^ 2 + (t : ℝ) * Real.log t / (c * Q) * g * d +
        (t : ℝ) * Real.log t ^ (-A) ≤ Q * L ^ 2 + x * L / (c * Q) * g * d + x * (L / 2) ^ (-A) := by
      linarith
    have hk2 : K7 * (Q * Real.log t ^ 2 + (t : ℝ) * Real.log t / (c * Q) * g * d +
        (t : ℝ) * Real.log t ^ (-A)) ≤
        |K7| * (Q * L ^ 2 + x * L / (c * Q) * g * d + x * (L / 2) ^ (-A)) :=
      (mul_le_mul_of_nonneg_right (le_abs_self K7) hX0).trans
        (mul_le_mul_of_nonneg_left hX (abs_nonneg _))
    have e : |K7| * (Q * L ^ 2 + x * L / (c * Q) * g * d + x * (L / 2) ^ (-A)) =
        |K7| * (Q * L ^ 2 + x * (L / 2) ^ (-A)) + |K7| * x * L * d / (c * Q) * g := by ring
    linarith

/-- One `m`: `|S₁| ≤ Σ_{c ≤ Q} (P + R_c (c, m)) log(3x)` from a uniform progression bound. -/
theorem abs_S1_le (x Q : ℝ) (hx : 1 ≤ x) (hQ0 : 0 ≤ Q) (hQx : Q ≤ x) (m : ℕ) (hm : m ∈ mRange x)
    (P : ℝ) (R : ℕ → ℝ)
    (hB : ∀ c : ℕ, 1 ≤ c → (c : ℝ) ≤ Q → ∀ t : ℕ, 1 ≤ t → t ≤ ⌊x⌋₊ →
      |apSum (DeltaQ Q) (t : ℝ) c m| ≤ P + R c * (Nat.gcd c m : ℝ)) :
    |S1 ⌊Q⌋₊ ⌊3 * x⌋₊ (fm x Q m)| ≤
      ∑ c ∈ Icc 1 ⌊Q⌋₊, (P + R c * (Nat.gcd c m : ℝ)) * Real.log (3 * x) := by
  unfold S1
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun c hc => ?_))
  have hc1 := (mem_Icc.mp hc).1
  have hcQ : (c : ℝ) ≤ Q := le_trans (by exact_mod_cast (mem_Icc.mp hc).2) (Nat.floor_le hQ0)
  have hμ : |(μ c : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hin := abs_inner_S1_le x Q hx m c hc1 (hcQ.trans hQx) hm _ (hB c hc1 hcQ)
  rw [abs_mul]
  calc |(μ c : ℝ)| * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hin

/-- Summing over `m`. -/
theorem sigma1_le_sum (x Q : ℝ) (hx : 1 ≤ x) (hQ0 : 0 ≤ Q) (hQx : Q ≤ x)
    (P : ℝ) (hP : 0 ≤ P) (R : ℕ → ℝ) (hR : ∀ c, 0 ≤ R c)
    (hB : ∀ m ∈ mRange x, ∀ c : ℕ, 1 ≤ c → (c : ℝ) ≤ Q → ∀ t : ℕ, 1 ≤ t → t ≤ ⌊x⌋₊ →
      |apSum (DeltaQ Q) (t : ℝ) c m| ≤ P + R c * (Nat.gcd c m : ℝ)) :
    Sigma1 x Q ≤ Real.log (3 * x) *
      (2 * x * Q * P + ∑ c ∈ Icc 1 ⌊Q⌋₊, R c * (2 * x * (c.divisors.card : ℝ))) := by
  have hl3 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
  have hcard : ((mRange x).card : ℝ) ≤ 2 * x := by
    have h := card_mRange_mod_le x hx 1 0 le_rfl (by simpa using hx)
    have e : (mRange x).filter (fun m => m % 1 = 0) = mRange x := by
      apply filter_true_of_mem; intro m _; exact Nat.mod_one m
    rw [e] at h; simpa using h
  unfold Sigma1
  refine (sum_le_sum (fun m hm => abs_S1_le x Q hx hQ0 hQx m hm P R (hB m hm))).trans ?_
  rw [sum_comm]
  have hterm : ∀ c ∈ Icc 1 ⌊Q⌋₊, ∑ m ∈ mRange x, (P + R c * (Nat.gcd c m : ℝ)) * Real.log (3 * x)
      ≤ Real.log (3 * x) * (2 * x * P + R c * (2 * x * (c.divisors.card : ℝ))) := by
    intro c hc
    have hc1 := (mem_Icc.mp hc).1
    have hcQ : (c : ℝ) ≤ Q := le_trans (by exact_mod_cast (mem_Icc.mp hc).2) (Nat.floor_le hQ0)
    rw [← sum_mul, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl3
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hcard hP
    · exact mul_le_mul_of_nonneg_left (sum_gcd_mRange_le x hx c hc1 (hcQ.trans hQx)) (hR c)
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum, sum_add_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ hl3
  have hU : ((⌊Q⌋₊ + 1 - 1 : ℕ) : ℝ) ≤ Q := by simpa using Nat.floor_le hQ0
  have : ((⌊Q⌋₊ + 1 - 1 : ℕ) : ℝ) * (2 * x * P) ≤ Q * (2 * x * P) :=
    mul_le_mul_of_nonneg_right hU (by positivity)
  linarith

/-- The crude bound `Σ₁ ≤ 27 x³ Q (Q³ + 3x)`, used for bounded `x`. -/
theorem sigma1_crude (x Q : ℝ) (hx : 1 ≤ x) (hQ : 0 ≤ Q) :
    Sigma1 x Q ≤ 27 * x ^ 3 * Q * (Q ^ 3 + 3 * x) := by
  have hx0 : 0 < x := by linarith
  set N := ⌊3 * x⌋₊
  have hN : (N : ℝ) ≤ 3 * x := Nat.floor_le (by linarith)
  set E := 3 * x * (Q ^ 3 + 3 * x)
  have hE0 : 0 ≤ E := by positivity
  have hm : ∀ m ∈ mRange x, |S1 ⌊Q⌋₊ N (fm x Q m)| ≤ Q * (3 * x * E) := by
    intro m hm
    simp only [mRange, mem_filter, mem_Icc] at hm
    have hmN : (m : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast hm.1.2) hN
    have hf : ∀ n, |fm x Q m n| ≤ Q ^ 3 + 3 * x := by
      intro n
      unfold fm
      split_ifs with h
      · refine (abs_DeltaQ_le_cube_log Q hQ _).trans ?_
        have hlt : n < m := h.2
        have h1 : Real.log ((m - n : ℕ) : ℝ) ≤ ((m - n : ℕ) : ℝ) :=
          (Real.log_le_sub_one_of_pos (by exact_mod_cast (show 0 < m - n by omega))).trans
            (by linarith)
        have h2 : ((m - n : ℕ) : ℝ) ≤ 3 * x :=
          le_trans (by exact_mod_cast Nat.sub_le m n) hmN
        linarith
      · simp; positivity
    unfold S1
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ c ∈ Icc 1 ⌊Q⌋₊, 3 * x * E := by
          apply sum_le_sum; intro c hc
          have hc1 := (mem_Icc.mp hc).1
          rw [abs_mul]
          have hμ : |(μ c : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          refine (mul_le_mul_of_nonneg_right hμ (abs_nonneg _)).trans ?_
          rw [one_mul]
          refine (abs_sum_le_sum_abs _ _).trans ?_
          calc _ ≤ ∑ r ∈ Icc 1 (N / c), E := by
                apply sum_le_sum; intro r hr
                have hr1 := (mem_Icc.mp hr).1
                have hrN : (r : ℝ) ≤ 3 * x := by
                  have : r ≤ N := (mem_Icc.mp hr).2.trans (Nat.div_le_self N c)
                  exact le_trans (by exact_mod_cast this) hN
                have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
                rw [abs_mul, abs_of_nonneg (Real.log_nonneg hr1R)]
                have hlr : Real.log r ≤ 3 * x :=
                  (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
                exact mul_le_mul hlr (hf _) (abs_nonneg _) (by positivity)
            _ = ((N / c : ℕ) : ℝ) * E := by
                rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
            _ ≤ 3 * x * E := by
                apply mul_le_mul_of_nonneg_right _ hE0
                exact le_trans (by exact_mod_cast Nat.div_le_self N c) hN
      _ = ((⌊Q⌋₊ : ℕ) : ℝ) * (3 * x * E) := by
          rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
      _ ≤ Q * (3 * x * E) := mul_le_mul_of_nonneg_right (Nat.floor_le hQ) (by positivity)
  unfold Sigma1
  refine (sum_le_sum hm).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hcard : ((mRange x).card : ℝ) ≤ 3 * x := by
    have : (mRange x).card ≤ N := by
      unfold mRange
      refine (card_filter_le _ _).trans ?_
      simp
      exact le_rfl
    exact le_trans (by exact_mod_cast this) hN
  calc _ ≤ 3 * x * (Q * (3 * x * E)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by simp only [E]; ring

theorem ev_sigma1 (B : ℝ) (hB : 0 < B) : ∃ X1 : ℝ, ∀ x : ℝ, X1 ≤ x →
    4 ≤ x ∧ 1 ≤ Real.log x ∧
      (Real.log x ^ B) ^ 2 * (Real.log x * ((Real.log x ^ B) ^ 3 + Real.log x)) ≤
        Real.sqrt x := by
  have ev1 := Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)
  have ev2 := (isLittleO_log_rpow_rpow_atTop (5 * B + 2) (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  have ev3 := eventually_ge_atTop (4 : ℝ)
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp (ev1.and (ev2.and ev3))
  refine ⟨X1, fun x hx => ?_⟩
  obtain ⟨hL1, hbig, hx4⟩ := hX1 x hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hQ1 : 1 ≤ Real.log x ^ B := Real.one_le_rpow hL1 hB.le
  refine ⟨hx4, hL1, ?_⟩
  have e : (Real.log x ^ B) ^ 5 * Real.log x ^ 2 = Real.log x ^ (5 * B + 2) := by
    rw [← Real.rpow_natCast (Real.log x ^ B) 5, ← Real.rpow_mul hL0.le,
      ← Real.rpow_natCast (Real.log x) 2, ← Real.rpow_add hL0]
    congr 1; push_cast; ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _),
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hbig
  rw [Real.sqrt_eq_rpow]
  set L := Real.log x
  set Q := L ^ B
  have a1 : Q ^ 5 * L ≤ Q ^ 5 * L ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have a2 : Q ^ 2 ≤ Q ^ 5 := pow_le_pow_right₀ hQ1 (by norm_num)
  have a3 : Q ^ 2 * L ^ 2 ≤ Q ^ 5 * L ^ 2 := mul_le_mul_of_nonneg_right a2 (by positivity)
  calc Q ^ 2 * (L * (Q ^ 3 + L)) = Q ^ 5 * L + Q ^ 2 * L ^ 2 := by ring
    _ ≤ 2 * (Q ^ 5 * L ^ 2) := by linarith
    _ ≤ x ^ (1 / 2 : ℝ) := by rw [e]; linarith

/-- **3.2, page 54: `Σ₁ ≪ x² L⁶ Q⁻¹` for `Q = L^B`, from Lemma 1, 2.7.** -/
theorem bound3_2_of (h7 : Lemma1_7) : Bound3_2 := by
  intro B hB
  obtain ⟨K7, hK7⟩ := h7 (2 * B + 5) (by positivity)
  obtain ⟨X1, hX1⟩ := ev_sigma1 B hB
  set A := 2 * B + 5 with hAdef
  set X := max X1 2
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  set LX := Real.log X
  have hLX : l2 ≤ LX := Real.log_le_log (by norm_num) (le_max_right _ _)
  have hX2 : (2 : ℝ) ≤ X := le_max_right _ _
  set QX := LX ^ B
  have hQX : 0 < QX := Real.rpow_pos_of_pos (by linarith) _
  set bnd := 27 * X ^ 3 * QX * (QX ^ 3 + 3 * X)
  set low := 4 * l2 ^ 6 / QX
  have hlow : 0 < low := by positivity
  set K := |K7|
  have hK : 0 ≤ K := abs_nonneg _
  set Kb := 6 * K + 6 * K * 2 ^ A + 6 + 96 * K
  refine ⟨max (bnd / low) Kb, fun x hx2 => ?_⟩
  have hx0 : 0 < x := by linarith
  set L := Real.log x
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx2
  have hL0 : 0 < L := by linarith
  set Q := L ^ B
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hL0 _
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = x ^ 2 * L ^ 6 / Q := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  have eR : max (bnd / low) Kb * x ^ 2 * L ^ 6 / Q = max (bnd / low) Kb * T := by
    rw [hT]; ring
  rw [eR]
  rcases le_or_gt x X with hxX | hxX
  · have hLLX : L ≤ LX := Real.log_le_log hx0 hxX
    have hQQX : Q ≤ QX := Real.rpow_le_rpow hL0.le hLLX hB.le
    have h1 := sigma1_crude x Q (by linarith) hQ0.le
    have h2 : 27 * x ^ 3 * Q * (Q ^ 3 + 3 * x) ≤ bnd := by
      simp only [bnd]; gcongr
    have h3 : low ≤ T := by
      rw [hT]
      apply div_le_div₀ (by positivity) _ hQ0 hQQX
      have h4 : (2 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx2 2
      have h5 : l2 ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ hl2.le hL2 6
      calc 4 * l2 ^ 6 = 2 ^ 2 * l2 ^ 6 := by norm_num
        _ ≤ x ^ 2 * L ^ 6 := mul_le_mul h4 h5 (by positivity) (by positivity)
    calc Sigma1 x Q ≤ bnd := h1.trans h2
      _ = bnd / low * low := by field_simp
      _ ≤ bnd / low * T := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ max (bnd / low) Kb * T := mul_le_mul_of_nonneg_right (le_max_left _ _) hT0.le
  · obtain ⟨hx4, hL1, hE⟩ := hX1 x (le_trans (le_max_left _ _) hxX.le)
    have hE' : Q ^ 2 * (L * (Q ^ 3 + L)) ≤ Real.sqrt x := hE
    have hQ1 : 1 ≤ Q := Real.one_le_rpow hL1 hB.le
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hsx2 : 2 ≤ Real.sqrt x := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hx4
    have hsxx : Real.sqrt x ≤ x := by nlinarith
    have hQ3 : 1 ≤ Q ^ 3 := one_le_pow₀ hQ1
    have hQQ3 : Q ≤ Q ^ 3 := by
      calc Q = Q ^ 1 := (pow_one Q).symm
        _ ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
    have hQL : Q ≤ L * (Q ^ 3 + L) := by nlinarith
    have h1LQ : 1 ≤ L * (Q ^ 3 + L) := by linarith
    have hQ2 : 0 < Q ^ 2 := by positivity
    have hQs : Q ≤ Real.sqrt x := by
      calc Q ≤ Q ^ 2 := by nlinarith
        _ ≤ Q ^ 2 * (L * (Q ^ 3 + L)) := le_mul_of_one_le_right hQ2.le h1LQ
        _ ≤ _ := hE'
    have hQ3x : Q ^ 3 ≤ x := by
      calc Q ^ 3 = Q ^ 2 * Q := by ring
        _ ≤ Q ^ 2 * (L * (Q ^ 3 + L)) := mul_le_mul_of_nonneg_left hQL hQ2.le
        _ ≤ x := hE'.trans hsxx
    have hQx : Q ≤ x := hQs.trans hsxx
    set P := K * (Q * L ^ 2 + x * (L / 2) ^ (-A)) + Real.sqrt x * (Q ^ 3 + L) with hPdef
    set R : ℕ → ℝ := fun c => K * x * L * (c.divisors.card : ℝ) / (c * Q) with hRdef
    have hP0 : 0 ≤ P := by rw [hPdef]; positivity
    have hR0 : ∀ c, 0 ≤ R c := fun c => by rw [hRdef]; positivity
    have hB' : ∀ m ∈ mRange x, ∀ c : ℕ, 1 ≤ c → (c : ℝ) ≤ Q → ∀ t : ℕ, 1 ≤ t → t ≤ ⌊x⌋₊ →
        |apSum (DeltaQ Q) (t : ℝ) c m| ≤ P + R c * (Nat.gcd c m : ℝ) :=
      fun m _ c hc hcQ t ht htx =>
        apSum_bound A K7 (by positivity) hK7 x Q hx4 hQ1 hQs c m hc hcQ t ht htx
    have hS := sigma1_le_sum x Q (by linarith) hQ0.le hQx P hP0 R hR0 hB'
    set U := ⌊Q⌋₊
    obtain ⟨H, hH⟩ : ∃ H : ℝ, H = ∑ c ∈ Icc 1 U, (c.divisors.card : ℝ) ^ 2 / c := ⟨_, rfl⟩
    have hH0 : 0 ≤ H := by rw [hH]; exact sum_nonneg (fun _ _ => by positivity)
    have hsumR : ∑ c ∈ Icc 1 U, R c * (2 * x * (c.divisors.card : ℝ)) =
        2 * K * x ^ 2 * L / Q * H := by
      rw [hH, mul_sum]; apply sum_congr rfl; intro c hc
      have hc0 : (c : ℝ) ≠ 0 := by
        have : (0 : ℝ) < c := by exact_mod_cast (mem_Icc.mp hc).1
        exact this.ne'
      rw [hRdef]; field_simp
    have hlogU : Real.log U ≤ L := by
      rcases Nat.eq_zero_or_pos U with h | h
      · rw [h, Nat.cast_zero, Real.log_zero]; exact hL0.le
      · exact Real.log_le_log (by exact_mod_cast h) ((Nat.floor_le hQ0.le).trans hQx)
    have hHle : H ≤ (2 * L) ^ 4 := by
      rw [hH]
      refine (sum_sq_divisors_div_le U).trans (pow_le_pow_left₀ (Hn_nonneg U) ?_ 4)
      exact (Hn_le U).trans (by linarith)
    have hl3 : Real.log (3 * x) ≤ 3 * L := by
      rw [Real.log_mul (by norm_num) hx0.ne']
      have : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    rw [hsumR] at hS
    have hW0 : 0 ≤ 2 * x * Q * P + 2 * K * x ^ 2 * L / Q * H := by positivity
    have hS2 : Sigma1 x Q ≤ 3 * L * (2 * x * Q * P + 2 * K * x ^ 2 * L / Q * (16 * L ^ 4)) := by
      refine hS.trans ?_
      apply mul_le_mul hl3 _ hW0 (by positivity)
      have : 2 * K * x ^ 2 * L / Q * H ≤ 2 * K * x ^ 2 * L / Q * (16 * L ^ 4) :=
        mul_le_mul_of_nonneg_left (hHle.trans (le_of_eq (by ring))) (by positivity)
      linarith
    -- the three pieces
    have i1 : x * Q * (Q * L ^ 2) * L ≤ T := by
      rw [hT, le_div_iff₀ hQ0]
      have hxL : Q ^ 3 ≤ x * L ^ 3 :=
        hQ3x.trans (le_mul_of_one_le_right hx0.le (one_le_pow₀ hL1))
      calc x * Q * (Q * L ^ 2) * L * Q = (x * L ^ 3) * Q ^ 3 := by ring
        _ ≤ (x * L ^ 3) * (x * L ^ 3) := mul_le_mul_of_nonneg_left hxL (by positivity)
        _ = x ^ 2 * L ^ 6 := by ring
    have i3 : x * Q * (Real.sqrt x * (Q ^ 3 + L)) * L ≤ T := by
      rw [hT, le_div_iff₀ hQ0]
      calc x * Q * (Real.sqrt x * (Q ^ 3 + L)) * L * Q =
            (x * Real.sqrt x) * (Q ^ 2 * (L * (Q ^ 3 + L))) := by ring
        _ ≤ (x * Real.sqrt x) * Real.sqrt x := mul_le_mul_of_nonneg_left hE' (by positivity)
        _ = x ^ 2 := by rw [mul_assoc, hsq]; ring
        _ ≤ x ^ 2 * L ^ 6 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
    have i2 : x * Q * (x * (L / 2) ^ (-A)) * L ≤ 2 ^ A * T := by
      have e1 : (L / 2) ^ (-A) = L ^ (-A) * (2 : ℝ) ^ A := by
        rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
      have e2 : Q * L * L ^ (-A) = L ^ (B + 1 + -A) := by
        rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
      have e3 : L ^ 6 / Q = L ^ ((6 : ℝ) - B) := by
        rw [Real.rpow_sub hL0, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hle : L ^ (B + 1 + -A) ≤ L ^ ((6 : ℝ) - B) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hAdef]; linarith)
      calc x * Q * (x * (L / 2) ^ (-A)) * L = 2 ^ A * x ^ 2 * (Q * L * L ^ (-A)) := by
            rw [e1]; ring
        _ = 2 ^ A * x ^ 2 * L ^ (B + 1 + -A) := by rw [e2]
        _ ≤ 2 ^ A * x ^ 2 * L ^ ((6 : ℝ) - B) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 2 ^ A * T := by rw [hT, ← e3]; ring
    have eW : 3 * L * (2 * x * Q * P + 2 * K * x ^ 2 * L / Q * (16 * L ^ 4)) =
        6 * K * (x * Q * (Q * L ^ 2) * L) + 6 * K * (x * Q * (x * (L / 2) ^ (-A)) * L) +
          6 * (x * Q * (Real.sqrt x * (Q ^ 3 + L)) * L) + 96 * K * T := by
      rw [hPdef, hT]; ring
    have j1 := mul_le_mul_of_nonneg_left i1 (by positivity : (0 : ℝ) ≤ 6 * K)
    have j2 := mul_le_mul_of_nonneg_left i2 (by positivity : (0 : ℝ) ≤ 6 * K)
    have j3 := mul_le_mul_of_nonneg_left i3 (by norm_num : (0 : ℝ) ≤ 6)
    have hKb : Kb * T = 6 * K * T + 6 * K * (2 ^ A * T) + 6 * T + 96 * K * T := by
      simp only [Kb]; ring
    calc Sigma1 x Q ≤ _ := hS2
      _ = _ := eW
      _ ≤ Kb * T := by rw [hKb]; linarith
      _ ≤ max (bnd / low) Kb * T := mul_le_mul_of_nonneg_right (le_max_right _ _) hT0.le

/-- **3.2 from the Siegel-Walfisz theorem 1.1 alone.** Fully proved. -/
theorem bound3_2_of_siegelWalfisz (hSW : SiegelWalfisz) : Bound3_2 :=
  bound3_2_of (lemma1_7_of (bound2_4_of hSW))

end LeanLab.HeathBrown1985
