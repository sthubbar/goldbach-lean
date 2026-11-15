module

public import LeanLab.Tolev2009.Decomp336a
public import LeanLab.Tolev2009.Decomp310b
public import LeanLab.PNTPort.Vinogradov.Count
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
AI wrote this Lean code. Codex task336.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 page 86 display 65.
Finite coefficient reductions and the proved scalar phase estimate.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.Decomp336a

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310a LeanLab.Tolev2009.Decomp310b
open LeanLab.HeathBrown1985
open LeanLab.PNTPort.Vinogradov LeanLab.PNTPort.LargeSieve

/-- The finite convolution regrouping in Tolev 1999 page 86 display 65.
It bounds the restricted coefficient rectangle by the sixth convolution of zeta. -/
theorem convolution_reduction (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (L U K : ℕ) :
    ∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K, F (m*k) ≤
      ∑ n ∈ Icc 1 (U*K), (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) * F n := by
  classical
  by_cases hU : U = 0
  · subst U; simp
  by_cases hK : K = 0
  · subst K; simp
  let T := U*K
  have hUT : U ≤ T := Nat.le_mul_of_pos_right U (Nat.pos_of_ne_zero hK)
  have hKT : K ≤ T := Nat.le_mul_of_pos_left K (Nat.pos_of_ne_zero hU)
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 T) :
      (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) * F n =
        ∑ p ∈ (Ioc 0 T ×ˢ Ioc 0 T).filter (fun p : ℕ × ℕ => p.1*p.2=n),
          (tau5 p.1 : ℝ) * F n := by
    rw [show (6 : ℕ) = 5+1 by norm_num, pow_succ, ArithmeticFunction.mul_apply,
      Nat.cast_sum, sum_mul]
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (by have := (mem_Icc.mp hn).1; omega) (mem_Icc.mp hn).2]
    apply sum_congr rfl
    intro p hp
    have hp0 : p.2 ≠ 0 := by have := (mem_Ioc.mp (mem_product.mp (mem_filter.mp hp).1).2).1; omega
    simp [tau5, ArithmeticFunction.zeta_apply, hp0]
  have he : (∑ n ∈ Icc 1 T, (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) * F n) =
      ∑ p ∈ (Ioc 0 T ×ˢ Ioc 0 T).filter (fun p : ℕ × ℕ => p.1*p.2 ≤ T),
        (tau5 p.1 : ℝ) * F (p.1*p.2) := by
    rw [sum_congr rfl hpoint]
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    have hpos : 0 < p.1*p.2 := Nat.mul_pos (mem_Ioc.mp (mem_product.mp hp).1).1 (mem_Ioc.mp (mem_product.mp hp).2).1
    simp only [sum_ite_eq, mem_Icc]
    by_cases hh : p.1*p.2 ≤ T
    · simp [hh, show 1 ≤ p.1*p.2 by omega]
    · simp [hh]
  simp_rw [mul_sum]
  rw [he, ← sum_product']
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hm, hk⟩ := mem_product.mp hp
    have hm' := mem_Ioc.mp hm
    have hk' := mem_Icc.mp hk
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨by omega, hm'.2.trans hUT⟩,
      mem_Ioc.mpr ⟨by omega, hk'.2.trans hKT⟩⟩, Nat.mul_le_mul hm'.2 hk'.2⟩
  · intro p hp hnot
    exact mul_nonneg (Nat.cast_nonneg _) (hF _)

/-- The joint multiset majorant for the squared sixth divisor coefficient.
This supplies the moment component of Tolev 1999 page 86 display 65. -/
theorem zeta6_sq_le_zeta36_nat (n : ℕ) :
    (ArithmeticFunction.zeta ^ 6) n ^ 2 ≤ (ArithmeticFunction.zeta ^ 36) n := by
  have hm6 : (ArithmeticFunction.zeta ^ 6).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  have hm36 : (ArithmeticFunction.zeta ^ 36).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p e hp
    change (ArithmeticFunction.zeta ^ (5 + 1)) (p ^ e) ^ 2 ≤
      (ArithmeticFunction.zeta ^ (35 + 1)) (p ^ e)
    rw [zeta_power_prime_pow 5 p e hp, zeta_power_prime_pow 35 p e hp]
    simpa only [pow_two] using multichoose_mul_le 6 6 e
  · intro a b ha hb hab hIa hIb
    change ((ArithmeticFunction.zeta ^ 6) (a * b)) ^ 2 ≤ (ArithmeticFunction.zeta ^ 36) (a * b)
    rw [hm6.map_mul_of_coprime hab, hm36.map_mul_of_coprime hab, mul_pow]
    exact Nat.mul_le_mul hIa hIb

/-- The same pointwise comparison after casting to real coefficients. -/
theorem zeta6_sq_le_zeta36 (n : ℕ) :
    (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) ^ 2 ≤
      (((ArithmeticFunction.zeta ^ 36) n : ℕ) : ℝ) := by
  exact_mod_cast zeta6_sq_le_zeta36_nat n

 /-- The reciprocal squared sixth divisor moment in the scalar Cauchy step. -/
theorem zeta6_sq_reciprocal (N : ℕ) :
    ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) ^ 2 / n ≤
      Hn N ^ 36 := by
  apply le_trans (sum_le_sum (fun n hn =>
    div_le_div_of_nonneg_right (zeta6_sq_le_zeta36 n) (Nat.cast_nonneg n)))
  exact zeta_power_reciprocal 36 N

/-- The geometric cap retains its endpoint count, Tolev page 86 display 65. -/
theorem phaseCap_le_count (α x : ℝ) (n : ℕ) : phaseCap α x n ≤ 2*x/n+1 := by
  unfold phaseCap
  split_ifs
  · rfl
  · exact min_le_left _ _

/-- The weighted finite Cauchy step in display 65, retaining the count one. -/
theorem weighted_phase_cauchy (a : ℕ → ℝ) (T : ℕ) (α x : ℝ) (hx : 0 ≤ x) :
    (∑ n ∈ Icc 1 T, a n * phaseCap α x n) ^ 2 ≤
      (∑ n ∈ Icc 1 T, (a n) ^ 2 / n) *
        ((2*x + T) * ∑ n ∈ Icc 1 T, phaseCap α x n) := by
  let f : ℕ → ℝ := fun n => (a n)^2 / n
  let g : ℕ → ℝ := fun n => (n : ℝ) * phaseCap α x n ^ 2
  have hc : (∑ n ∈ Icc 1 T, a n * phaseCap α x n) ^ 2 ≤
      (∑ n ∈ Icc 1 T, f n) * (∑ n ∈ Icc 1 T, g n) := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro n hn
      dsimp [f]
      positivity
    · intro n hn
      dsimp [g]
      positivity
    · intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := (mem_Icc.mp hn).1; omega)
      dsimp [f, g]
      apply le_of_eq
      field_simp
  have hg : (∑ n ∈ Icc 1 T, g n) ≤ (2*x+T) * ∑ n ∈ Icc 1 T, phaseCap α x n := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (mem_Icc.mp hn).1; omega)
    have hnT : (n : ℝ) ≤ T := by exact_mod_cast (mem_Icc.mp hn).2
    have hp := phaseCap_nonneg α x n hx
    have hcap : phaseCap α x n - 1 ≤ 2*x/n := by linarith [phaseCap_le_count α x n]
    have hcap' := (le_div_iff₀ hn0).mp hcap
    have hh : (n : ℝ) * phaseCap α x n ≤ 2*x+T := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hh hp
    dsimp [g]
    nlinarith
  exact hc.trans (mul_le_mul_of_nonneg_left hg (sum_nonneg (fun n hn => by dsimp [f]; positivity)))
/-- The finite rectangle bound after Cauchy and the proved coefficient moment.
This is the coefficient part of Tolev page 86 display 65. -/
theorem rectangle_phase_sq_le (L U K : ℕ) (α x : ℝ) (hx : 0 ≤ x) :
    (∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K, phaseCap α x (m*k)) ^ 2 ≤
      Hn (U*K) ^ 36 * ((2*x + (U*K : ℕ)) *
        ∑ n ∈ Icc 1 (U*K), phaseCap α x n) := by
  have hconv := convolution_reduction (phaseCap α x) (fun n => phaseCap_nonneg α x n hx) L U K
  have hpos : 0 ≤ ∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K, phaseCap α x (m*k) := by
    apply sum_nonneg
    intro m hm
    apply mul_nonneg (Nat.cast_nonneg _)
    exact sum_nonneg (fun k hk => phaseCap_nonneg α x (m*k) hx)
  apply (pow_le_pow_left₀ hpos hconv 2).trans
  apply (weighted_phase_cauchy (fun n => (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ)) (U*K) α x hx).trans
  apply mul_le_mul_of_nonneg_right (zeta6_sq_reciprocal (U*K))
  exact mul_nonneg (by positivity) (sum_nonneg (fun n hn => phaseCap_nonneg α x n hx))

/-- The exact complex cap is at most the standard nearest integer cap plus one. -/
theorem phaseCap_le_G_add_one (α x : ℝ) (n : ℕ) :
    phaseCap α x n ≤ LeanLab.PNTPort.Vinogradov.G (2*x/n) (α*n) + 1 := by
  by_cases hd : dist0 (α*n) = 0
  · rw [LeanLab.PNTPort.Vinogradov.G, if_pos hd]
    exact phaseCap_le_count α x n
  · have hdpos : 0 < dist0 (α*n) := lt_of_le_of_ne (dist0_nonneg _) (Ne.symm hd)
    have hdist : 4 * dist0 (α*n) ≤ ‖ee (α*n)-1‖ := distance_comparison _
    have hden : 0 < ‖ee (α*n)-1‖ := by linarith
    have he : ee (α*n) ≠ 1 := by
      intro hh
      simp [hh] at hden
    have hdiv : 2 / ‖ee (α*n)-1‖ ≤ 1 / (2*dist0 (α*n)) := by
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith
    rw [phaseCap, if_neg he, LeanLab.PNTPort.Vinogradov.G, if_neg hd, ← min_add_add_right]
    apply le_min
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hdiv.trans (by linarith))

/-- The rational approximation reciprocal sum in Tolev page 72 Lemma 7 part ii. -/
theorem phaseCap_sum_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ))
    {α x : ℝ} (hα : |α - a / q| ≤ 1 / (q : ℝ)^2) (hx : 0 ≤ x) (T : ℕ) :
    ∑ n ∈ Icc 1 T, phaseCap α x n ≤
      12 * (2*x/q + T + q) * (1 + Real.log q + Real.log T) + T := by
  calc
    _ ≤ ∑ n ∈ Icc 1 T, (LeanLab.PNTPort.Vinogradov.G (2*x/n) (α*n) + 1) :=
      sum_le_sum (fun n hn => phaseCap_le_G_add_one α x n)
    _ = (∑ n ∈ Icc 1 T, LeanLab.PNTPort.Vinogradov.G (2*x/n) (α*n)) + T := by
      rw [sum_add_distrib]
      simp
    _ ≤ _ := add_le_add (sum_G_div_le hq hcop hα T (by positivity : 0 ≤ 2*x)) le_rfl
/-- Minor arcs exclude small reduced denominators, including the shifted interval endpoints. -/
theorem integer_denominator_gt_Q (Q τ α : ℝ) (q : ℕ) (a : ℤ)
    (hQ : 0 ≤ Q) (hτ : Q+1 ≤ τ)
    (hα : α ∈ Set.Ioo (-1/τ) (1-1/τ)) (hminor : α ∉ majorArcs Q τ)
    (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (herr : |α - (a : ℝ)/q| ≤ 1/((q : ℝ)*τ)) : Q < q := by
  by_contra hn
  have hqQ : (q : ℝ) ≤ Q := le_of_not_gt hn
  have ht : 0 < τ := by linarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have he : |(q : ℝ)*α-a| ≤ 1/τ := by
    have hh := mul_le_mul_of_nonneg_left herr hqr.le
    rw [show (q : ℝ) * |α - (a : ℝ)/q| = |(q : ℝ)*α-a| by
      rw [← abs_of_pos hqr, ← abs_mul, abs_of_pos hqr]
      congr 1
      field_simp] at hh
    convert hh using 1
    field_simp
  have hlo := (abs_le.mp he).1
  have hhi := (abs_le.mp he).2
  have hlα := mul_lt_mul_of_pos_left hα.1 hqr
  have huα := mul_lt_mul_of_pos_left hα.2 hqr
  have hqτ : (q : ℝ)+1 ≤ τ := by linarith
  have hl : (-1 : ℝ) < a := by
    have hh : (q : ℝ)/τ + 1/τ ≤ 1 := by
      rw [← add_div, div_le_one ht]
      exact hqτ
    have hm : (q : ℝ)*(-1/τ) = -(q:ℝ)/τ := by ring
    rw [hm, neg_div] at hlα
    linarith
  have hu : (a : ℝ) < q := by
    have hh : 1/τ ≤ (q : ℝ)/τ := div_le_div_of_nonneg_right (by exact_mod_cast hq) ht.le
    have hm : (q : ℝ)*(1-1/τ) = q-(q:ℝ)/τ := by ring
    rw [hm] at huα
    linarith
  have ha0 : 0 ≤ a := by exact_mod_cast (show (-1 : ℤ) < a by exact_mod_cast hl)
  have haq : a < (q : ℤ) := by exact_mod_cast hu
  have hac : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
  have hc : Nat.Coprime a.toNat q := by
    apply IsCoprime.natCoprime
    simpa only [hac] using hcop
  have haqr : a.toNat < q := by omega
  have her : |α - (a.toNat : ℝ)/q| ≤ 1/((q : ℝ)*τ) := by
    simpa only [show (a.toNat : ℝ) = (a : ℝ) by exact_mod_cast hac] using herr
  exact (not_lt_of_ge hqQ) (denominator_gt_Q Q τ α q a.toNat hminor hq haqr hc her)


/-- Dirichlet approximation with both required error bounds and an integer numerator. -/
theorem minor_arc_reduced_approximation (Q τ α : ℝ)
    (hQ : 0 ≤ Q) (hτ : Q+1 ≤ τ) (ht : 1 ≤ τ)
    (hα : α ∈ Set.Ioo (-1/τ) (1-1/τ)) (hminor : α ∉ majorArcs Q τ) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ Q < (q : ℝ) ∧ (q : ℝ) ≤ τ ∧
      IsCoprime a (q : ℤ) ∧
      |α - (a : ℝ)/q| ≤ 1/((q : ℝ)*τ) ∧
      |α - (a : ℝ)/q| ≤ 1/(q : ℝ)^2 := by
  have hfloor : 0 < ⌊τ⌋₊ := by
    have hh : 1 ≤ ⌊τ⌋₊ := (Nat.le_floor (by simpa using ht))
    omega
  obtain ⟨r, herr, hr⟩ := Real.exists_rat_abs_sub_le_and_den_le α hfloor
  have hq : 1 ≤ r.den := Rat.pos r
  have hqt : (r.den : ℝ) ≤ τ :=
    (show (r.den : ℝ) ≤ ⌊τ⌋₊ by exact_mod_cast hr).trans (Nat.floor_le (by linarith))
  have htf : τ ≤ (⌊τ⌋₊ : ℝ)+1 := (Nat.lt_floor_add_one τ).le
  have hqr : (0 : ℝ) < r.den := by exact_mod_cast Rat.pos r
  have he : |α - (r.num : ℝ)/r.den| ≤ 1/((r.den : ℝ)*τ) := by
    rw [← Rat.cast_def]
    apply herr.trans
    apply one_div_le_one_div_of_le (mul_pos hqr (by linarith))
    nlinarith
  have he2 : |α - (r.num : ℝ)/r.den| ≤ 1/(r.den : ℝ)^2 := by
    apply he.trans
    apply one_div_le_one_div_of_le (sq_pos_of_pos hqr)
    nlinarith
  exact ⟨r.num, r.den, hq,
    integer_denominator_gt_Q Q τ α r.den r.num hQ hτ hα hminor hq r.isCoprime_num_den he,
    hqt, r.isCoprime_num_den, he, he2⟩

/-- The major arc parameters obey the separation condition for all sufficiently large N. -/
theorem eventual_minor_arc_parameters (A : ℝ) (hA : 0 ≤ A) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ Real.log N ∧ Qof A N + 1 ≤ τof A N := by
  have he := (isLittleO_log_rpow_rpow_atTop (40*A) (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨X₀, hX⟩ := Filter.eventually_atTop.mp he
  refine ⟨max X₀ (Real.exp 2), ?_⟩
  intro N hN
  have hNe : Real.exp 2 ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) < N := (Real.exp_pos 2).trans_le hNe
  have hL : 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hNe
  have hL0 : 0 < Real.log N := by linarith
  have hQ : 1 ≤ Qof A N := by
    unfold Qof
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hQ0 : 0 < Qof A N := by linarith
  have hbound := hX (N : ℝ) ((le_max_left _ _).trans hN)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _), abs_of_pos hN0] at hbound
  have hQsq : Qof A N ^ 2 = Real.log N ^ (40*A) := by
    rw [Qof, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
    congr 1
    ring
  refine ⟨hL, ?_⟩
  unfold τof
  apply (le_div_iff₀ hQ0).mpr
  rw [← hQsq] at hbound
  nlinarith
/-- The product cutoff retains the full logarithmic saving in the Type I shell. -/
theorem shell_product_bound (A : ℝ) (N : ℕ) (x M H : ℝ)
    (hA : 10000 ≤ A) (hN : (1 : ℝ) ≤ N) (hL : 2 ≤ Real.log N)
    (hx : 0 < x) (hxN : x ≤ N) (hM : 0 < M) (hH : 0 < H)
    (hMH : M*H ≤ 2*x) (hHlo : x^((249:ℝ)/500) ≤ H) :
    let T := ⌊2*M⌋₊ * cutoff3 (10000*A) N
    (T : ℝ) ≤ 4*N*Real.log N^(-10000*A) ∧
    (T : ℝ) ≤ N ∧
    (T : ℝ) ≤ 4*N*Real.log N^(-20*A) := by
  dsimp only
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hp : 0 < x^((249:ℝ)/500) := Real.rpow_pos_of_pos hx _
  have hmp : M*x^((249:ℝ)/500) ≤ 2*x :=
    (mul_le_mul_of_nonneg_left hHlo hM.le).trans hMH
  have hm : M ≤ 2*x^((251:ℝ)/500) := by
    have hh : M ≤ 2*x / x^((249:ℝ)/500) := (le_div_iff₀ hp).mpr hmp
    convert hh using 1
    rw [mul_div_assoc]
    congr 1
    simpa only [show (1:ℝ)-(249:ℝ)/500 = (251:ℝ)/500 by norm_num, Real.rpow_one] using Real.rpow_sub hx 1 ((249:ℝ)/500)
  have hmN : M ≤ 2*(N:ℝ)^((251:ℝ)/500) :=
    hm.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxN (by norm_num)) (by norm_num))
  have hf : (⌊2*M⌋₊ : ℝ) ≤ 2*M := Nat.floor_le (by positivity)
  have hk : (cutoff3 (10000*A) N : ℝ) ≤ (N:ℝ)^((1:ℝ)/3)*Real.log N^(-10000*A) :=
    by
      unfold cutoff3
      have hh := Nat.floor_le (show 0 ≤ (N:ℝ)^((1:ℝ)/3)*Real.log N^(-(10000*A)) by positivity)
      simpa only [neg_mul] using hh
  have hfirst : ((⌊2*M⌋₊ * cutoff3 (10000*A) N : ℕ) : ℝ) ≤
      4*(N:ℝ)*Real.log N^(-10000*A) := by
    push_cast
    calc
      _ ≤ (2*M)*((N:ℝ)^((1:ℝ)/3)*Real.log N^(-10000*A)) :=
        mul_le_mul hf hk (Nat.cast_nonneg _) (by positivity)
      _ ≤ (2*(2*(N:ℝ)^((251:ℝ)/500)))*((N:ℝ)^((1:ℝ)/3)*Real.log N^(-10000*A)) := by
        gcongr
      _ = 4*(N:ℝ)^((1253:ℝ)/1500)*Real.log N^(-10000*A) := by
        rw [show (1253:ℝ)/1500 = (251:ℝ)/500 + 1/3 by norm_num, Real.rpow_add hN0]
        ring
      _ ≤ _ := by
        have hh : (N:ℝ)^((1253:ℝ)/1500) ≤ N := by
          convert Real.rpow_le_rpow_of_exponent_le hN (show (1253:ℝ)/1500 ≤ 1 by norm_num) using 1 <;> simp
        gcongr
  have hs : Real.log N^(-10000*A) ≤ (1:ℝ)/4 := by
    calc
      _ ≤ Real.log N^(-2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
      _ ≤ (2:ℝ)^(-2:ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by norm_num)
      _ = 1/4 := by norm_num
  refine ⟨hfirst, ?_, ?_⟩
  · calc
      _ ≤ 4*(N:ℝ)*Real.log N^(-10000*A) := hfirst
      _ ≤ 4*(N:ℝ)*(1/4) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  · apply hfirst.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)

/-- The rational approximation mass estimate with the exact third cutoff savings. -/
theorem phase_mass_from_approx (A : ℝ) (N T q : ℕ) (a : ℤ) (α x : ℝ)
    (hA : 0 ≤ A) (hN : 0 < (N : ℝ)) (hL : 2 ≤ Real.log N)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hTN : T ≤ N)
    (hTS : (T : ℝ) ≤ 4 * N * Real.log N ^ (-20*A))
    (hq : 1 ≤ q) (hqQ : Qof A N < q) (hqτ : (q : ℝ) ≤ τof A N)
    (hcop : IsCoprime a (q : ℤ)) (herr : |α - (a : ℝ)/q| ≤ 1/(q : ℝ)^2) :
    ∑ n ∈ Icc 1 T, phaseCap α x n ≤ 256 * N * Real.log N ^ (1-20*A) := by
  let s : ℝ := N * Real.log N ^ (-20*A)
  have hL0 : 0 < Real.log N := by linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hQ : 1 ≤ Qof A N := by
    unfold Qof
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hQ0 : 0 < Qof A N := by linarith
  have ht : τof A N = s := by
    dsimp [τof, Qof, s]
    rw [show -20*A = -(20*A) by ring, Real.rpow_neg hL0.le, div_eq_mul_inv]
  have hqS : (q : ℝ) ≤ s := by rwa [ht] at hqτ
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqN : (q : ℝ) ≤ N := hqτ.trans (div_le_self hN.le hQ)
  have hlogq : Real.log q ≤ Real.log N := Real.log_le_log hq0 hqN
  have hlogT : Real.log T ≤ Real.log N := by
    by_cases hT : T = 0
    · simp [hT]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hT) (by exact_mod_cast hTN)
  have hlog : 1 + Real.log q + Real.log T ≤ 3 * Real.log N := by linarith
  have hlog0 : 0 ≤ 1 + Real.log q + Real.log T := by positivity
  have hNq : (N : ℝ)/q ≤ s := by
    calc
      _ ≤ (N : ℝ) / Qof A N := div_le_div_of_nonneg_left hN.le hQ0 hqQ.le
      _ = s := ht
  have hxq : 2*x/q ≤ 2*s := by
    calc
      _ = 2 * (x/q) := by ring
      _ ≤ 2 * ((N : ℝ)/q) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hxN hq0.le) (by norm_num)
      _ ≤ 2*s := mul_le_mul_of_nonneg_left hNq (by norm_num)
  have hT : (T : ℝ) ≤ 4*s := by simpa only [s, mul_assoc] using hTS
  have hcoef : 2*x/q + T + q ≤ 7*s := by linarith
  have hm := phaseCap_sum_le hq hcop herr hx T
  apply hm.trans
  have hprod := mul_le_mul hcoef hlog hlog0 (by positivity : 0 ≤ 7*s)
  have hbound : 12 * (2*x/q + T + q) * (1+Real.log q+Real.log T) + T ≤
      256 * s * Real.log N := by
    nlinarith [mul_nonneg hs (show 0 ≤ Real.log N - 1 by linarith)]
  apply hbound.trans_eq
  dsimp [s]
  rw [show (1-20*A) = (-20*A) + (1:ℝ) by ring, Real.rpow_add hL0, Real.rpow_one]
  ring
/-- The scalar Cauchy estimate fits the target exponent with an absolute constant. -/
theorem rectangle_phase_of_mass (A : ℝ) (N : ℕ) (α x : ℝ) (L U K : ℕ)
    (hA : 10000 ≤ A) (hN : 0 < N) (hL : 2 ≤ Real.log N)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hT : U*K ≤ N)
    (hmass : ∑ n ∈ Icc 1 (U*K), phaseCap α x n ≤
      256*(N:ℝ)*Real.log N^(1-20*A)) :
    ∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K, phaseCap α x (m*k) ≤
      (2:ℝ)^30 * N * Real.log N^(328-4*A) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hLp : 0 < Real.log N := by linarith
  have hTc : (U*K : ℕ) ≤ (N:ℝ) := by exact_mod_cast hT
  have hlog : Real.log (U*K : ℕ) ≤ Real.log N := by
    by_cases ht0 : U*K = 0
    · simp only [ht0, Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ht0) hTc
  have hH : Hn (U*K) ≤ 2*Real.log N := (Hn_le _).trans (by linarith)
  have hHp : Hn (U*K)^36 ≤ (2*Real.log N)^36 :=
    pow_le_pow_left₀ (Hn_nonneg _) hH 36
  have hcount : 2*x+(U*K : ℕ) ≤ 3*(N:ℝ) := by linarith
  have hmass0 : 0 ≤ ∑ n ∈ Icc 1 (U*K), phaseCap α x n :=
    sum_nonneg (fun n hn => phaseCap_nonneg α x n hx)
  have hs := rectangle_phase_sq_le L U K α x hx
  have hs' : (∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K, phaseCap α x (m*k))^2 ≤
      (2*Real.log N)^36 * (3*(N:ℝ)*(256*(N:ℝ)*Real.log N^(1-20*A))) := by
    apply hs.trans
    apply mul_le_mul hHp _ (by positivity) (by positivity)
    exact mul_le_mul hcount hmass hmass0 (by positivity)
  have heq : (2*Real.log N)^36 * (3*(N:ℝ)*(256*(N:ℝ)*Real.log N^(1-20*A))) =
      (768*(2:ℝ)^36)*(N:ℝ)^2*Real.log N^(37-20*A) := by
    rw [show (37-20*A) = (36:ℝ)+(1-20*A) by ring, Real.rpow_add hLp,
      show Real.log N^(36:ℝ) = Real.log N^(36:ℕ) from Real.rpow_natCast _ 36]
    ring
  rw [heq] at hs'
  have hexp : Real.log N^(37-20*A) ≤ Real.log N^(656-8*A) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hcoeff : 768*(2:ℝ)^36 ≤ (2:ℝ)^60 := by norm_num
  have hb : (768*(2:ℝ)^36)*(N:ℝ)^2*Real.log N^(37-20*A) ≤
      (2:ℝ)^60*(N:ℝ)^2*Real.log N^(656-8*A) := by
    gcongr
  have hsq : ((2:ℝ)^30*N*Real.log N^(328-4*A))^2 =
      (2:ℝ)^60*(N:ℝ)^2*Real.log N^(656-8*A) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (Real.log N^(328-4*A)) 2,
      ← Real.rpow_mul hLp.le]
    congr 1
    · norm_num
    · congr 1; ring
  have hB : 0 ≤ (2:ℝ)^30*N*Real.log N^(328-4*A) := by positivity
  have hh := hs'.trans hb
  rw [← hsq] at hh
  nlinarith

/-- Tolev 1999 page 86 display 65 after the progression bound.
This scalar phase average has no lambda, residue, row or upper interval endpoints.
The two spare logarithmic powers supply the Abel variant in display 66.
The plus one term is retained rather than discarded. -/
theorem phase_average :
    ∀ A : ℝ, 10 ^ 4 ≤ A →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N),
          α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M H : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → 0 < H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) *
            ∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), phaseCap α x (m * k) ≤
              C * N * Real.log N ^ (328 - 4 * A) := by
  intro A hA
  obtain ⟨N₀, hN₀⟩ := eventual_minor_arc_parameters A (by linarith)
  refine ⟨(2 : ℝ)^30, N₀, by positivity, ?_⟩
  intro N hodd hNN α hα hminor x M H hxlo hxN hx hM hH hprodlo hprodhi hsize
  obtain ⟨hL, hτ⟩ := hN₀ N hNN
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hQ : 0 ≤ Qof A N := Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  obtain ⟨a, q, hq, hqQ, hqτ, hcop, herr, herr2⟩ :=
    minor_arc_reduced_approximation (Qof A N) (τof A N) α hQ hτ
      (by linarith) hα hminor
  have hprod := shell_product_bound A N x M H (by norm_num at hA ⊢; exact hA)
    hN1 hL (by linarith) hxN hM hH hprodhi hsize
  have hTN : ⌊2*M⌋₊ * cutoff3 (10000*A) N ≤ N := by exact_mod_cast hprod.2.1
  have hmass := phase_mass_from_approx A N (⌊2*M⌋₊ * cutoff3 (10000*A) N) q a α x
    (by linarith) hNpos hL (by linarith) hxN hTN hprod.2.2 hq hqQ hqτ hcop herr2
  have hres := rectangle_phase_of_mass A N α x ⌊M⌋₊ ⌊2*M⌋₊ (cutoff3 (10000*A) N)
    (by norm_num at hA ⊢; exact hA) (by exact_mod_cast hNpos) hL
    (by linarith) hxN hTN hmass
  norm_num only [show (10 : ℝ)^4 = 10000 by norm_num] at *
  exact hres

/-- The exact sealed constant row leaf from the two smaller scalar obligations.
The scalar phase average is proved with clean axioms. -/
theorem constant_rows :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
            ((tau5 m : ℝ) * Real.log N) *
              ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun _ => 1) m‖ ≤
                C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, hC, hav⟩ := phase_average A hA
  refine ⟨C, max N₀ 3, hC, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by have := (le_max_right N₀ 3).trans hN; linarith)]
    exact Real.exp_one_lt_d9.le.trans (by have := (le_max_right N₀ 3).trans hN; linarith)
  have hL0 : 0 < Real.log N := by linarith
  let P : ℕ → ℝ := fun m => ∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), phaseCap α x (m * k)
  have hP : ∀ m, 0 ≤ P m := fun m => sum_nonneg (fun k hk => phaseCap_nonneg α x (m * k) (by linarith))
  have hr : ∀ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
      ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun _ => 1) m‖ ≤ P m := by
    intro m hm
    apply row_norm_le_phase lam l₃ _ N m α x H H₁ hlam
      (by have := (mem_Ioc.mp hm).1; omega) (by linarith)
    intro k hk hc
    exact progression_bound l₃ k N m α x H H₁ (mem_Icc.mp hk).1
      (by have := (mem_Ioc.mp hm).1; omega) hc (by linarith)
  have hav' := hav N hodd ((le_max_left _ _).trans hN) α hα hminor x M H
    hxlo hxhi hx hM hH hprodlo hprodhi hsize
  have hsub : Ioc ⌊M⌋₊ ⌊M₁⌋₊ ⊆ Ioc ⌊M⌋₊ ⌊2 * M⌋₊ :=
    Ioc_subset_Ioc le_rfl (Nat.floor_mono hM₁)
  calc
    _ ≤ Real.log N * ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, (tau5 m : ℝ) * P m := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      have ht := mul_le_mul_of_nonneg_left (hr m hm)
        (show 0 ≤ (tau5 m : ℝ) * Real.log N by positivity)
      nlinarith
    _ ≤ Real.log N * ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) * P m :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun m hm hn => mul_nonneg (Nat.cast_nonneg _) (hP m))) hL0.le
    _ ≤ Real.log N * (C * N * Real.log N ^ (328 - 4 * A)) :=
      mul_le_mul_of_nonneg_left hav' hL0.le
    _ = C * N * Real.log N ^ (329 - 4 * A) := by
      rw [show (329 - 4 * A) = (1 : ℝ) + (328 - 4 * A) by ring,
        Real.rpow_add hL0, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

/-- The exact sealed logarithmic row leaf from the same two smaller obligations.
The scalar phase average is proved with clean axioms. -/
theorem logarithmic_rows :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
            ((tau5 m : ℝ) * Real.log N) *
              ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m‖ ≤
                C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, hC, hav⟩ := phase_average A hA
  refine ⟨8 * C, max N₀ 3, by positivity, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL0 : 0 < Real.log N := by linarith
  let P : ℕ → ℝ := fun m => ∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), phaseCap α x (m * k)
  have hP : ∀ m, 0 ≤ P m := fun m => sum_nonneg (fun k hk => phaseCap_nonneg α x (m * k) (by linarith))
  have hav' := hav N hodd ((le_max_left _ _).trans hN) α hα hminor x M H
    hxlo hxhi hx hM hH hprodlo hprodhi hsize
  have hsub : Ioc ⌊M⌋₊ ⌊M₁⌋₊ ⊆ Ioc ⌊M⌋₊ ⌊2 * M⌋₊ :=
    Ioc_subset_Ioc le_rfl (Nat.floor_mono hM₁)
  calc
    _ ≤ (8 * Real.log N ^ 2) * ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, (tau5 m : ℝ) * P m := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      have ht := mul_le_mul_of_nonneg_left
        (logarithmic_row_norm_le_phase lam l₃ (cutoff3 (10 ^ 4 * A) N) N m α x M M₁ H H₁ hlam
          hN3 (by linarith) hxhi hM hM₁ hH hHH₁ hH₁ hprodhi hm)
        (show 0 ≤ (tau5 m : ℝ) * Real.log N by positivity)
      nlinarith
    _ ≤ (8 * Real.log N ^ 2) * ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) * P m :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun m hm hn => mul_nonneg (Nat.cast_nonneg _) (hP m))) (by positivity)
    _ ≤ (8 * Real.log N ^ 2) * (C * N * Real.log N ^ (328 - 4 * A)) :=
      mul_le_mul_of_nonneg_left hav' (by positivity)
    _ = _ := by
      rw [show (330 - 4 * A) = (2 : ℝ) + (328 - 4 * A) by ring,
        Real.rpow_add hL0, Real.rpow_two]
      ring

end LeanLab.Tolev2009.Decomp336a
