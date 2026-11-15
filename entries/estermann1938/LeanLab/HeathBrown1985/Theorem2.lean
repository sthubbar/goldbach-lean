module

public import Mathlib
public import LeanLab.HeathBrown1985.Elementary

/-!
P0096 Heath-Brown 1985, Theorem 2 deduced from Lemma 1, 2.6, and Lemma 2, 2.11, as on
pages 52 to 53 of the paper. The deduction uses only elementary facts proved in
Elementary.lean: `k/φ(k) ≤ e(1 + ω(k))`, `ψ(x;k,l) ≤ L(x/k + 1)` and
`Σ_{k ≤ N} d(k)/k ≤ (1 + log N)²`. The paper's choice `K = x L^{-C}`, `Q = L^B`, `B = 2C/3`.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

/-- `apSum Δ_Q = apSum Λ_Q - ψ`. -/
theorem apSum_DeltaQ (Q x : ℝ) (k l : ℕ) :
    apSum (DeltaQ Q) x k l = apSum (LambdaQ Q) x k l - psi x k l := by
  unfold apSum DeltaQ psi; rw [sum_sub_distrib]

/-- One modulus: `Σ_{(l,k)=1} |ψ - x/φ| ≤ δ₁(x,k,Q) + k K₁ (Q L² + x L (kQ)⁻¹ d(k))`. -/
theorem inner_bound (x Q K1 : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (h6 : ∀ l : ℕ, Nat.Coprime l k →
      |apSum (LambdaQ Q) x k l - x / (Nat.totient k : ℝ)| ≤
        K1 * (Q * Real.log x ^ 2 + x * Real.log x / (k * Q) * (k.divisors.card : ℝ))) :
    ∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k), |psi x k l - x / (Nat.totient k : ℝ)|
      ≤ delta1 x k Q + k * (K1 * (Q * Real.log x ^ 2 +
          x * Real.log x / (k * Q) * (k.divisors.card : ℝ))) := by
  set R := K1 * (Q * Real.log x ^ 2 + x * Real.log x / (k * Q) * (k.divisors.card : ℝ))
  have hR : 0 ≤ R := (abs_nonneg _).trans (h6 1 (Nat.coprime_one_left k))
  have step : ∀ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k),
      |psi x k l - x / (Nat.totient k : ℝ)| ≤ |apSum (DeltaQ Q) x k l| + R := by
    intro l hl
    have hc := (mem_filter.mp hl).2
    have e : psi x k l - x / (Nat.totient k : ℝ) =
        -(apSum (DeltaQ Q) x k l) + (apSum (LambdaQ Q) x k l - x / (Nat.totient k : ℝ)) := by
      rw [apSum_DeltaQ]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    exact add_le_add le_rfl (h6 l hc)
  refine (sum_le_sum step).trans ?_
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  apply add_le_add
  · unfold delta1
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
  · apply mul_le_mul_of_nonneg_right _ hR
    have := card_filter_le (Icc 1 k) (fun l => Nat.Coprime l k)
    simp only [Nat.card_Icc, add_tsub_cancel_right] at this
    exact_mod_cast this

theorem one_le_log_of_three_le (x : ℝ) (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- The rpow bookkeeping at the end of page 53. -/
theorem final_algebra (x L C C2 K1 : ℝ) (hx : 0 < x) (hL : 1 ≤ L) (hC : 0 < C) :
    Mpt * x * L * (C2 * x * (L ^ (2 * C / 3)) ^ (-(1 : ℝ) / 2) * L ^ 7 +
      |K1| * (x * L ^ (-C) * L ^ (2 * C / 3) * L ^ 2 + x * L / L ^ (2 * C / 3) * (4 * L ^ 2)))
    ≤ Mpt * (|C2| + 5 * |K1|) * x ^ 2 * L ^ (8 - C / 3) := by
  have hL0 : 0 < L := by linarith
  have hM := Mpt_pos
  have r7 : L ^ 7 = L ^ (7 : ℝ) := (rpow_natCast L 7).symm
  have r2 : L ^ 2 = L ^ (2 : ℝ) := (rpow_natCast L 2).symm
  have rQ : (L ^ (2 * C / 3)) ^ (-(1 : ℝ) / 2) = L ^ (-(C / 3)) := by
    rw [← rpow_mul hL0.le]; congr 1; ring
  have rinv : x * L / L ^ (2 * C / 3) = x * L * L ^ (-(2 * C / 3)) := by
    rw [rpow_neg hL0.le, div_eq_mul_inv]
  have e1 : L * (L ^ (-(C / 3)) * L ^ (7 : ℝ)) = L ^ (8 - C / 3) := by
    calc L * (L ^ (-(C / 3)) * L ^ (7 : ℝ)) = L ^ (1 : ℝ) * L ^ (-(C / 3)) * L ^ (7 : ℝ) := by
          rw [rpow_one]; ring
      _ = L ^ ((1 : ℝ) + -(C / 3) + 7) := by rw [rpow_add hL0, rpow_add hL0]
      _ = _ := by congr 1; ring
  have e2 : L * (L ^ (-C) * L ^ (2 * C / 3) * L ^ (2 : ℝ)) = L ^ (3 - C / 3) := by
    calc L * (L ^ (-C) * L ^ (2 * C / 3) * L ^ (2 : ℝ))
          = L ^ (1 : ℝ) * L ^ (-C) * L ^ (2 * C / 3) * L ^ (2 : ℝ) := by rw [rpow_one]; ring
      _ = L ^ ((1 : ℝ) + -C + 2 * C / 3 + 2) := by
          rw [rpow_add hL0, rpow_add hL0, rpow_add hL0]
      _ = _ := by congr 1; ring
  have e3 : L * (L * L ^ (-(2 * C / 3)) * L ^ (2 : ℝ)) = L ^ (4 - 2 * C / 3) := by
    calc L * (L * L ^ (-(2 * C / 3)) * L ^ (2 : ℝ))
          = L ^ (1 : ℝ) * L ^ (1 : ℝ) * L ^ (-(2 * C / 3)) * L ^ (2 : ℝ) := by
          rw [rpow_one]; ring
      _ = L ^ ((1 : ℝ) + 1 + -(2 * C / 3) + 2) := by
          rw [rpow_add hL0, rpow_add hL0, rpow_add hL0]
      _ = _ := by congr 1; ring
  have m1 : L ^ (3 - C / 3) ≤ L ^ (8 - C / 3) := rpow_le_rpow_of_exponent_le hL (by linarith)
  have m2 : L ^ (4 - 2 * C / 3) ≤ L ^ (8 - C / 3) := rpow_le_rpow_of_exponent_le hL (by linarith)
  have hP : 0 ≤ L ^ (8 - C / 3) := (rpow_pos_of_pos hL0 _).le
  have hK : 0 ≤ |K1| := abs_nonneg _
  have expand : Mpt * x * L * (C2 * x * (L ^ (2 * C / 3)) ^ (-(1 : ℝ) / 2) * L ^ 7 +
      |K1| * (x * L ^ (-C) * L ^ (2 * C / 3) * L ^ 2 + x * L / L ^ (2 * C / 3) * (4 * L ^ 2)))
      = Mpt * x ^ 2 * (C2 * (L * (L ^ (-(C / 3)) * L ^ (7 : ℝ))) +
        |K1| * (L * (L ^ (-C) * L ^ (2 * C / 3) * L ^ (2 : ℝ))) +
        4 * |K1| * (L * (L * L ^ (-(2 * C / 3)) * L ^ (2 : ℝ)))) := by
    rw [rQ, rinv, r7, r2]; ring
  rw [expand, e1, e2, e3]
  have hC2 : C2 * L ^ (8 - C / 3) ≤ |C2| * L ^ (8 - C / 3) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hP
  have hx2 : 0 ≤ Mpt * x ^ 2 := by positivity
  calc Mpt * x ^ 2 * (C2 * L ^ (8 - C / 3) + |K1| * L ^ (3 - C / 3) + 4 * |K1| * L ^ (4 - 2 * C / 3))
      ≤ Mpt * x ^ 2 * (|C2| * L ^ (8 - C / 3) + |K1| * L ^ (8 - C / 3) +
          4 * |K1| * L ^ (8 - C / 3)) := by
        apply mul_le_mul_of_nonneg_left _ hx2
        have := mul_le_mul_of_nonneg_left m1 hK
        have := mul_le_mul_of_nonneg_left m2 hK
        linarith
    _ = _ := by ring

/-- The main range of the deduction: `x ≥ 3`, so `L ≥ 1`, and `Q = L^B ≤ x`. -/
theorem big_range (C : ℝ) (hC : 0 < C) (C2 K1 : ℝ)
    (hL2 : ∀ x : ℝ, 2 ≤ x → ∀ K : ℝ, K ≤ x / Real.log x ^ (2 * C / 3) →
      ∑ k ∈ Icc 1 ⌊K⌋₊, delta1 x k (Real.log x ^ (2 * C / 3)) / k ≤
        C2 * x * (Real.log x ^ (2 * C / 3)) ^ (-(1 : ℝ) / 2) * Real.log x ^ 7)
    (hL6 : ∀ x : ℝ, 2 ≤ x → ∀ Q : ℝ, 1 ≤ Q → Q ≤ x → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
      Nat.Coprime l k →
        |apSum (LambdaQ Q) x k l - x / (Nat.totient k : ℝ)| ≤
          K1 * (Q * Real.log x ^ 2 + x * Real.log x / (k * Q) * (k.divisors.card : ℝ)))
    (x : ℝ) (hx3 : 3 ≤ x) (hQx : Real.log x ^ (2 * C / 3) ≤ x) :
    ∑ k ∈ Icc 1 ⌊x * Real.log x ^ (-C)⌋₊, ∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k),
      (psi x k l - x / (Nat.totient k : ℝ)) ^ 2
      ≤ Mpt * (|C2| + 5 * |K1|) * x ^ 2 * Real.log x ^ (8 - C / 3) := by
  have hx0 : 0 < x := by linarith
  have hL1 := one_le_log_of_three_le x hx3
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  set Q := L ^ (2 * C / 3) with hQdef
  have hQ1 : 1 ≤ Q := one_le_rpow hL1 (by positivity)
  have hQ0 : 0 < Q := by linarith
  set Kr := x * L ^ (-C) with hKrdef
  have hLC : L ^ (-C) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hKr0 : 0 ≤ Kr := by positivity
  have hKrx : Kr ≤ x := by
    calc Kr = x * L ^ (-C) := rfl
      _ ≤ x * 1 := mul_le_mul_of_nonneg_left hLC hx0.le
      _ = x := mul_one x
  have hKrQ : Kr ≤ x / Q := by
    rw [hQdef, div_eq_mul_inv, ← rpow_neg hL0.le]
    apply mul_le_mul_of_nonneg_left _ hx0.le
    exact rpow_le_rpow_of_exponent_le hL1 (by linarith)
  set N := ⌊Kr⌋₊ with hNdef
  have hkx : ∀ k ∈ Icc 1 N, (k : ℝ) ≤ x := by
    intro k hk
    have := (mem_Icc.mp hk).2
    exact (Nat.cast_le.mpr this).trans ((Nat.floor_le hKr0).trans hKrx)
  -- pointwise square bound
  have hsq : ∀ k ∈ Icc 1 N, ∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k),
      (psi x k l - x / (Nat.totient k : ℝ)) ^ 2 ≤ Mpt * x * L / k *
      ∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k), |psi x k l - x / (Nat.totient k : ℝ)| := by
    intro k hk
    have hk1 := (mem_Icc.mp hk).1
    rw [mul_sum]
    apply sum_le_sum
    intro l _
    have hb := abs_err_le x hL1 k l hk1 (hkx k hk)
    rw [← sq_abs, sq]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  -- inner sums
  have hin : ∀ k ∈ Icc 1 N, (∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k),
      |psi x k l - x / (Nat.totient k : ℝ)|) / k ≤ delta1 x k Q / k +
      |K1| * (Q * L ^ 2 + x * L / Q * ((k.divisors.card : ℝ) / k)) := by
    intro k hk
    have hk1 := (mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hb := inner_bound x Q K1 k hk1 (fun l hl => hL6 x (by linarith) Q hQ1 hQx k l hk1 (hkx k hk) hl)
    have hpos : 0 ≤ Q * L ^ 2 + x * L / (k * Q) * (k.divisors.card : ℝ) := by positivity
    have hK : K1 * (Q * L ^ 2 + x * L / (k * Q) * (k.divisors.card : ℝ)) ≤
        |K1| * (Q * L ^ 2 + x * L / (k * Q) * (k.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hpos
    rw [div_le_iff₀ hkpos]
    have e : (delta1 x k Q / k + |K1| * (Q * L ^ 2 + x * L / Q * ((k.divisors.card : ℝ) / k))) * k
        = delta1 x k Q + k * (|K1| * (Q * L ^ 2 + x * L / (k * Q) * (k.divisors.card : ℝ))) := by
      field_simp
    rw [e]
    nlinarith
  -- the divisor sum
  have hdiv : ∑ k ∈ Icc 1 N, (k.divisors.card : ℝ) / k ≤ 4 * L ^ 2 := by
    refine (sum_divisors_div_le_log N).trans ?_
    have hlogN : Real.log N ≤ L := by
      rcases Nat.eq_zero_or_pos N with h | h
      · rw [h]; simp; linarith
      · exact Real.log_le_log (by exact_mod_cast h) ((Nat.floor_le hKr0).trans hKrx)
    have : 0 ≤ 1 + Real.log N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · rw [h]; simp
      · have := Real.log_nonneg (by exact_mod_cast h : (1 : ℝ) ≤ N); linarith
    nlinarith
  have hNle : (N : ℝ) ≤ Kr := Nat.floor_le hKr0
  have hL2' := hL2 x (by linarith) Kr hKrQ
  -- assemble
  have hT : ∑ k ∈ Icc 1 N, (∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k),
      |psi x k l - x / (Nat.totient k : ℝ)|) / k ≤
      C2 * x * Q ^ (-(1 : ℝ) / 2) * L ^ 7 +
      |K1| * (Kr * Q * L ^ 2 + x * L / Q * (4 * L ^ 2)) := by
    refine (sum_le_sum hin).trans ?_
    rw [sum_add_distrib, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    apply add_le_add hL2'
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h1 : (#(Icc 1 N) : ℝ) * (Q * L ^ 2) ≤ Kr * Q * L ^ 2 := by
      simp only [Nat.card_Icc, add_tsub_cancel_right]
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hNle (by positivity)
    have h2 : x * L / Q * ∑ k ∈ Icc 1 N, (k.divisors.card : ℝ) / k ≤ x * L / Q * (4 * L ^ 2) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    linarith
  calc _ ≤ ∑ k ∈ Icc 1 N, Mpt * x * L / k *
        ∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k), |psi x k l - x / (Nat.totient k : ℝ)| :=
          sum_le_sum hsq
    _ = Mpt * x * L * ∑ k ∈ Icc 1 N, (∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k),
          |psi x k l - x / (Nat.totient k : ℝ)|) / k := by
          rw [mul_sum]; apply sum_congr rfl; intro k _; ring
    _ ≤ Mpt * x * L * (C2 * x * Q ^ (-(1 : ℝ) / 2) * L ^ 7 +
          |K1| * (Kr * Q * L ^ 2 + x * L / Q * (4 * L ^ 2))) :=
          mul_le_mul_of_nonneg_left hT (by have := Mpt_pos; positivity)
    _ ≤ _ := final_algebra x L C C2 K1 hx0 hL1 hC

/-- A bounded range `2 ≤ x ≤ X0` is absorbed into the constant. -/
theorem small_range (C : ℝ) (hC : 0 < C) (X0 : ℝ) : ∃ Ks : ℝ, ∀ x : ℝ, 2 ≤ x → x ≤ X0 →
    ∑ k ∈ Icc 1 ⌊x * Real.log x ^ (-C)⌋₊, ∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k),
      (psi x k l - x / (Nat.totient k : ℝ)) ^ 2 ≤ Ks * x ^ 2 * Real.log x ^ (8 - C / 3) := by
  set e := 8 - C / 3
  set l2 := Real.log 2
  have hl2 : 0 < l2 := Real.log_pos one_lt_two
  set LX := Real.log (max X0 2)
  have hLX : l2 ≤ LX := Real.log_le_log (by norm_num) (le_max_right _ _)
  have hLX0 : 0 < LX := by linarith
  set A := LX * (max X0 2 + 1) + max X0 2
  set Nb := max X0 2 * l2 ^ (-C)
  set m := min (l2 ^ e) (LX ^ e)
  have hm : 0 < m := lt_min (rpow_pos_of_pos hl2 _) (rpow_pos_of_pos hLX0 _)
  refine ⟨Nb ^ 2 * A ^ 2 / (4 * m), ?_⟩
  intro x hx2 hxX
  have hx0 : 0 < x := by linarith
  have hxM : x ≤ max X0 2 := le_trans hxX (le_max_left _ _)
  set L := Real.log x
  have hL2 : l2 ≤ L := Real.log_le_log (by norm_num) hx2
  have hL0 : 0 < L := by linarith
  have hLLX : L ≤ LX := Real.log_le_log hx0 hxM
  have hA0 : 0 ≤ A := by positivity
  have hNb0 : 0 ≤ Nb := by positivity
  set N := ⌊x * L ^ (-C)⌋₊
  have hN : (N : ℝ) ≤ Nb := by
    have h1 : (N : ℝ) ≤ x * L ^ (-C) := Nat.floor_le (by positivity)
    refine h1.trans ?_
    apply mul_le_mul hxM (rpow_le_rpow_of_nonpos hl2 hL2 (by linarith)) (by positivity)
      (by positivity)
  have hterm : ∀ k ∈ Icc 1 N, ∀ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k),
      (psi x k l - x / (Nat.totient k : ℝ)) ^ 2 ≤ A ^ 2 := by
    intro k hk l _
    have hk1 := (mem_Icc.mp hk).1
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hφ : (1 : ℝ) ≤ Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hψ0 := psi_nonneg x k l
    have hψ := psi_le x (by linarith) k l hk1
    have hxk : x / k ≤ x := div_le_self hx0.le hkR
    have hxφ : x / (Nat.totient k : ℝ) ≤ x := div_le_self hx0.le hφ
    have hxφ0 : 0 ≤ x / (Nat.totient k : ℝ) := by positivity
    have hψA : psi x k l ≤ LX * (max X0 2 + 1) := by
      refine hψ.trans ?_
      apply mul_le_mul hLLX (by linarith) (by positivity) hLX0.le
    have habs : |psi x k l - x / (Nat.totient k : ℝ)| ≤ A := by
      rw [abs_le]; constructor <;> linarith
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hcount : ∑ k ∈ Icc 1 N, ∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k),
      (psi x k l - x / (Nat.totient k : ℝ)) ^ 2 ≤ (N : ℝ) * ((N : ℝ) * A ^ 2) := by
    have : ∀ k ∈ Icc 1 N, ∑ l ∈ (Icc 1 k).filter (fun l => Nat.Coprime l k),
        (psi x k l - x / (Nat.totient k : ℝ)) ^ 2 ≤ (N : ℝ) * A ^ 2 := by
      intro k hk
      refine (sum_le_sum (hterm k hk)).trans ?_
      rw [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have h1 := card_filter_le (Icc 1 k) (fun l => Nat.Coprime l k)
      simp only [Nat.card_Icc, add_tsub_cancel_right] at h1
      have h2 := (mem_Icc.mp hk).2
      exact_mod_cast h1.trans h2
    refine (sum_le_sum this).trans ?_
    rw [sum_const, nsmul_eq_mul]; simp
  have hLe : m ≤ L ^ e := by
    rcases le_or_gt 0 e with he | he
    · exact (min_le_left _ _).trans (rpow_le_rpow hl2.le hL2 he)
    · exact (min_le_right _ _).trans (rpow_le_rpow_of_nonpos hL0 hLLX he.le)
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hNN : (N : ℝ) * ((N : ℝ) * A ^ 2) ≤ Nb ^ 2 * A ^ 2 := by
    have := mul_le_mul hN hN hN0 hNb0
    nlinarith [sq_nonneg A]
  refine hcount.trans (hNN.trans ?_)
  have hx4 : 4 ≤ x ^ 2 := by nlinarith
  have hK0 : 0 ≤ Nb ^ 2 * A ^ 2 / (4 * m) := by positivity
  calc Nb ^ 2 * A ^ 2 = Nb ^ 2 * A ^ 2 / (4 * m) * (4 * m) := by field_simp
    _ ≤ Nb ^ 2 * A ^ 2 / (4 * m) * (x ^ 2 * L ^ e) := by
        apply mul_le_mul_of_nonneg_left _ hK0
        exact mul_le_mul hx4 hLe hm.le (by positivity)
    _ = _ := by ring

/-- **Theorem 2 of Heath-Brown 1985 from Lemma 1, 2.6, and Lemma 2, 2.11**, as on pages 52 to
53. Zero sorry; Lemma 1 and Lemma 2 are hypotheses. -/
theorem theorem2_of (h6 : Lemma1_6) (h2 : Lemma2) : Theorem2 := by
  intro C hC
  obtain ⟨C2, hC2⟩ := h2 (2 * C / 3) (by positivity)
  obtain ⟨K1, hK1⟩ := h6
  have hev := (isLittleO_log_rpow_rpow_atTop (2 * C / 3) one_pos).bound one_pos
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp hev
  set X0 := max X1 3
  obtain ⟨Ks, hKs⟩ := small_range C hC X0
  refine ⟨max Ks (Mpt * (|C2| + 5 * |K1|)), ?_⟩
  intro x hx2
  have hpos : 0 ≤ x ^ 2 * Real.log x ^ (8 - C / 3) := by
    have := Real.log_pos (by linarith : (1 : ℝ) < x)
    positivity
  rcases le_or_gt x X0 with hx | hx
  · refine (hKs x hx2 hx).trans ?_
    rw [mul_assoc, mul_assoc (max _ _)]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
  · have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx.le
    have hxX1 : X1 ≤ x := le_trans (le_max_left _ _) hx.le
    have hQx : Real.log x ^ (2 * C / 3) ≤ x := by
      have := hX1 x hxX1
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, rpow_one, abs_of_pos (by linarith : (0:ℝ) < x)] at this
      exact (le_abs_self _).trans this
    refine (big_range C hC C2 K1 hC2 hK1 x hx3 hQx).trans ?_
    rw [mul_assoc, mul_assoc (max _ _)]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpos

end LeanLab.HeathBrown1985
