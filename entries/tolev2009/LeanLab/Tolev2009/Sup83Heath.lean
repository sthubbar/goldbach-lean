module

public import LeanLab.Tolev2009.PublishedTheorem
public import LeanLab.HeathBrown1985.Vaughan

/-!
AI wrote this Lean code. Claude route burst 7, 2026-11-12, copy for Sup83Split.prime_decomposition.
Binary Goldbach is open.
Source: Tolev 1999 page 71 Lemma 4 and page 82 displays 52 to 54.
Written identity proof: Heath Brown 1982 pages 1367 to 1368 displays 6 to 8.
This file is a COPY of the proved parts of Decomp310c, Decomp424a and Decomp424b.
Those modules import Decomp83 through Decomp286b, so Sup83Split cannot import them.
Only the namespace and the imports differ, and nothing here mentions the block
definitions bilinear and tau5, which live in Sup83Split. Every declaration is proved.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.Sup83Heath

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic

/-! ### Copy of Decomp310c, prime power conversion and initial segment -/

/-- The von Mangoldt polynomial above the omitted initial segment.
Tolev 1999 page 82 display 52, adapted to the full interval and fixed residue.
This retains the exact same divisor weight as Kfun. -/
noncomputable def retainedMangoldt (A : ℝ) (lam : ℕ → ℝ) (l₃ K N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) * Real.log N ^ (-4 * A) < (n : ℝ)),
    (ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ)

/-- The prime power conversion estimate behind Tolev 1999 page 82 display 52.
It is uniform in the phase and uses only the bounded divisor weight. -/
theorem prime_power_mass_le (lam : ℕ → ℝ) (l₃ K N : ℕ) (α : ℝ)
    (hlam : ∀ k, |lam k| ≤ 1) (hN : 1 ≤ N) :
    ‖∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime),
      (ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ)‖ ≤
        K * (2 * Real.sqrt N * Real.log N) := by
  have hsets : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  calc
    _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime),
        ArithmeticFunction.vonMangoldt n * (K : ℝ) := by
      apply sum_le_sum
      intro n hn
      simp only [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
      exact mul_le_mul_of_nonneg_left (L2Bound.weight_le lam l₃ K n hlam)
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    _ = (K : ℝ) * (Chebyshev.psi N - Chebyshev.theta N) := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
      simp only [Nat.floor_natCast, hsets, ← sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Chebyshev.psi_sub_theta_le (by exact_mod_cast hN)) (Nat.cast_nonneg K)

/-- At the exact 2009 cutoff, prime powers alone fit the sealed remainder scale.
Tolev 1999 page 82 display 52, with the smaller 2009 third modulus cutoff.
No minor arc hypothesis or initial segment estimate is used. -/
theorem prime_power_mass_cutoff (A : ℝ) (lam : ℕ → ℝ) (l₃ N : ℕ) (α : ℝ)
    (hA : 10 ^ 4 ≤ A) (hlam : ∀ k, |lam k| ≤ 1) (hL : 1 ≤ Real.log N) :
    ‖∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime),
      (ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) *
        (L2Bound.weight lam l₃ (cutoff3 (10 ^ 4 * A) N) n : ℂ)‖ ≤
      2 * N * Real.log N ^ (330 - 4 * A) := by
  have hN : 1 ≤ N := by
    by_contra h
    have hz : N = 0 := by omega
    norm_num [hz] at hL
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hL0 : 0 < Real.log N := by linarith
  have hK : (cutoff3 (10 ^ 4 * A) N : ℝ) ≤
      (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-(10 ^ 4 * A)) :=
    Nat.floor_le (by positivity)
  have hp : (N : ℝ) ^ ((1 : ℝ) / 3) * Real.sqrt N ≤ N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0]
    calc
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
      _ = _ := Real.rpow_one _
  have hl : Real.log N ^ (-(10 ^ 4 * A)) * Real.log N ≤
      Real.log N ^ (330 - 4 * A) := by
    calc
      _ = Real.log N ^ (-(10 ^ 4 * A) + 1) := by rw [Real.rpow_add hL0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by norm_num at hA ⊢; linarith)
  calc
    _ ≤ (cutoff3 (10 ^ 4 * A) N : ℝ) * (2 * Real.sqrt N * Real.log N) :=
      prime_power_mass_le lam l₃ _ N α hlam hN
    _ ≤ ((N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-(10 ^ 4 * A))) *
        (2 * Real.sqrt N * Real.log N) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = 2 * ((N : ℝ) ^ ((1 : ℝ) / 3) * Real.sqrt N) *
        (Real.log N ^ (-(10 ^ 4 * A)) * Real.log N) := by ring
    _ ≤ 2 * N * Real.log N ^ (330 - 4 * A) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hl (by positivity) (by positivity)

/-- Exact prime to von Mangoldt conversion in Tolev 1999 page 82 display 52.
The second sum is supported on higher prime powers because von Mangoldt vanishes elsewhere. -/
theorem Kfun_add_prime_powers (lam : ℕ → ℝ) (l₃ K N : ℕ) (α : ℝ) :
    Kfun lam l₃ K N α +
      ∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ) =
      ∑ n ∈ Icc 1 N,
        (ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ) := by
  have hp : primeSet 1 0 N = (Icc 1 N).filter Nat.Prime := by
    ext n
    simp only [primeSet, mem_filter, mem_range, Nat.mod_one, and_true, mem_Icc]
    constructor
    · rintro ⟨hn, hp⟩
      exact ⟨⟨hp.one_lt.le, by omega⟩, hp⟩
    · rintro ⟨⟨hn, hN⟩, hp⟩
      exact ⟨by omega, hp⟩
  have hprime : Kfun lam l₃ K N α =
      ∑ n ∈ (Icc 1 N).filter Nat.Prime,
        (ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ) := by
    rw [L2Bound.Kfun_eq, hp]
    apply sum_congr rfl
    intro n hn
    rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hn).2]
    push_cast
    rw [mul_comm (n : ℝ) α]
    ring
  rw [hprime]
  exact sum_filter_add_sum_filter_not _ _ _

/-- The elementary progression count for the omitted segment in display 52.
The sum of absolute divisor weights through Y is at most Y H_K plus K. -/
theorem prefix_weight_mass (lam : ℕ → ℝ) (l₃ K Y : ℕ) (hlam : ∀ k, |lam k| ≤ 1) :
    ∑ n ∈ Icc 1 Y, |L2Bound.weight lam l₃ K n| ≤
      (Y : ℝ) * LeanLab.HeathBrown1985.Hn K + K := by
  have hw : ∀ n, |L2Bound.weight lam l₃ K n| ≤
      ∑ k ∈ Icc 1 K, if n % k = l₃ % k then (1 : ℝ) else 0 := by
    intro n
    unfold L2Bound.weight
    apply (abs_sum_le_sum_abs _ _).trans
    rw [sum_filter]
    apply sum_le_sum
    intro k hk
    by_cases h : Nat.Coprime k l₃ ∧ n % k = l₃ % k
    · rw [ite_eq_left h, ite_eq_left h.2]
      exact hlam k
    · rw [ite_eq_right h]
      by_cases hm : n % k = l₃ % k <;> simp only [hm, ite_true, ite_false] <;> norm_num
  have hc : ∀ k ∈ Icc 1 K,
      (((Icc 1 Y).filter (fun n => n % k = l₃ % k)).card : ℝ) ≤ (Y : ℝ) / k + 1 := by
    intro k hk
    have hcNat : ((Icc 1 Y).filter (fun n => n % k = l₃ % k)).card ≤ Y / k + 1 := by
      calc
        _ ≤ (range (Y / k + 1)).card := by
          apply card_le_card_of_injOn (fun n => n / k)
          · intro n hn
            change n / k ∈ range (Y / k + 1)
            apply mem_range.mpr
            exact Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp hn).1).2)
          · intro n hn m hm he
            change n / k = m / k at he
            have hnmod := (mem_filter.mp hn).2
            have hmmod := (mem_filter.mp hm).2
            rw [← Nat.mod_add_div n k, ← Nat.mod_add_div m k, he, hnmod, hmmod]
        _ = _ := card_range _
    have hcast : (((Icc 1 Y).filter (fun n => n % k = l₃ % k)).card : ℝ) ≤
        ((Y / k + 1 : ℕ) : ℝ) := by exact_mod_cast hcNat
    apply hcast.trans
    push_cast
    have hd : ((Y / k : ℕ) : ℝ) ≤ (Y : ℝ) / k := Nat.cast_div_le
    linarith
  calc
    _ ≤ ∑ n ∈ Icc 1 Y, ∑ k ∈ Icc 1 K, if n % k = l₃ % k then (1 : ℝ) else 0 :=
      sum_le_sum (fun n hn => hw n)
    _ = ∑ k ∈ Icc 1 K, (((Icc 1 Y).filter (fun n => n % k = l₃ % k)).card : ℝ) := by
      rw [sum_comm]
      simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ k ∈ Icc 1 K, ((Y : ℝ) / k + 1) := sum_le_sum hc
    _ = _ := by
      simp only [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul, mul_one, LeanLab.HeathBrown1985.Hn, mul_sum, div_eq_mul_inv]

/-- The omitted von Mangoldt prefix needs only progression counting and log bounds.
This is the initial segment component of Tolev 1999 page 82 display 52. -/
theorem prefix_mangoldt_mass (lam : ℕ → ℝ) (l₃ K Y N : ℕ) (α : ℝ)
    (hlam : ∀ k, |lam k| ≤ 1) (hYN : Y ≤ N) :
    ‖∑ n ∈ Icc 1 Y,
      (ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ)‖ ≤
      Real.log N * ((Y : ℝ) * LeanLab.HeathBrown1985.Hn K + K) := by
  calc
    _ ≤ ∑ n ∈ Icc 1 Y,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 Y, Real.log N * |L2Bound.weight lam l₃ K n| := by
      apply sum_le_sum
      intro n hn
      have hn1 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hbound : ArithmeticFunction.vonMangoldt n ≤ Real.log N :=
        ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_log hn1 (by exact_mod_cast (mem_Icc.mp hn).2.trans hYN))
      simp only [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
      exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
    _ = Real.log N * ∑ n ∈ Icc 1 Y, |L2Bound.weight lam l₃ K n| := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (prefix_weight_mass lam l₃ K Y hlam)
      (Real.log_natCast_nonneg N)

/-- The omitted initial segment fits the sealed remainder scale with constant three.
Tolev 1999 page 82 display 52, adapted to the full 2009 interval.
The estimate is elementary and uniform in the phase. -/
theorem initial_segment_mass_cutoff (A : ℝ) (lam : ℕ → ℝ) (l₃ N : ℕ) (α : ℝ)
    (hA : 10 ^ 4 ≤ A) (hlam : ∀ k, |lam k| ≤ 1) (hL : 1 ≤ Real.log N) :
    ‖∑ n ∈ Icc 1 ⌊(N : ℝ) * Real.log N ^ (-4 * A)⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) *
        (L2Bound.weight lam l₃ (cutoff3 (10 ^ 4 * A) N) n : ℂ)‖ ≤
      3 * N * Real.log N ^ (330 - 4 * A) := by
  have hN : 1 ≤ N := by
    by_contra h
    have hz : N = 0 := by omega
    norm_num [hz] at hL
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL0 : 0 < Real.log N := by linarith
  have hA0 : 0 ≤ A := by linarith
  let Y : ℕ := ⌊(N : ℝ) * Real.log N ^ (-4 * A)⌋₊
  let K : ℕ := cutoff3 (10 ^ 4 * A) N
  have hY : (Y : ℝ) ≤ (N : ℝ) * Real.log N ^ (-4 * A) := Nat.floor_le (by positivity)
  have hYle : (Y : ℝ) ≤ N := hY.trans
    (mul_le_of_le_one_right (Nat.cast_nonneg N)
      (Real.rpow_le_one_of_one_le_of_nonpos hL (by nlinarith)))
  have hYN : Y ≤ N := by exact_mod_cast hYle
  have hNp : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ N := by
    calc
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
      _ = _ := Real.rpow_one _
  have hK : (K : ℝ) ≤ (N : ℝ) * Real.log N ^ (-(10 ^ 4 * A)) := by
    apply (Nat.floor_le (by positivity : (0 : ℝ) ≤
      (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-(10 ^ 4 * A)))).trans
    exact mul_le_mul_of_nonneg_right hNp (by positivity)
  have hKle : (K : ℝ) ≤ N := hK.trans
    (mul_le_of_le_one_right (Nat.cast_nonneg N)
      (Real.rpow_le_one_of_one_le_of_nonpos hL (by nlinarith)))
  have hKN : K ≤ N := by exact_mod_cast hKle
  have hlogK : Real.log K ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos K with hz | hp
    · simp only [hz, Nat.cast_zero, Real.log_zero]
      exact hL0.le
    · exact Real.log_le_log (by exact_mod_cast hp) hKle
  have hH : LeanLab.HeathBrown1985.Hn K ≤ 2 * Real.log N :=
    (LeanLab.HeathBrown1985.Hn_le K).trans (by linarith)
  have hpowY : Real.log N ^ (-4 * A) * Real.log N ^ (2 : ℕ) ≤
      Real.log N ^ (330 - 4 * A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hpowK : Real.log N ^ (-(10 ^ 4 * A)) * Real.log N ≤
      Real.log N ^ (330 - 4 * A) := by
    calc
      _ = Real.log N ^ (-(10 ^ 4 * A) + 1) := by rw [Real.rpow_add hL0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by norm_num at hA ⊢; linarith)
  calc
    _ ≤ Real.log N * ((Y : ℝ) * LeanLab.HeathBrown1985.Hn K + K) :=
      prefix_mangoldt_mass lam l₃ K Y N α hlam hYN
    _ ≤ Real.log N * (((N : ℝ) * Real.log N ^ (-4 * A)) * (2 * Real.log N) +
        N * Real.log N ^ (-(10 ^ 4 * A))) := by
      apply mul_le_mul_of_nonneg_left _ hL0.le
      exact add_le_add (mul_le_mul hY hH (LeanLab.HeathBrown1985.Hn_nonneg K) (by positivity)) hK
    _ = 2 * N * (Real.log N ^ (-4 * A) * Real.log N ^ (2 : ℕ)) +
        N * (Real.log N ^ (-(10 ^ 4 * A)) * Real.log N) := by ring
    _ ≤ 2 * N * Real.log N ^ (330 - 4 * A) + N * Real.log N ^ (330 - 4 * A) :=
      add_le_add (mul_le_mul_of_nonneg_left hpowY (by positivity))
        (mul_le_mul_of_nonneg_left hpowK (Nat.cast_nonneg N))
    _ = _ := by ring

/-- Tolev 1999 page 82 display 52 and page 72 Lemma 8 part iv.
Only the prime power conversion and omitted initial segment are bounded.
No bilinear identity, Type I estimate, Type II estimate or minor arc assumption occurs.
The short initial segment is the explicit 2009 full interval adaptation.
Both error components are proved with the combined constant five. -/
theorem prime_power_and_initial_segment :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) → ∀ α : ℝ,
          ‖Kfun lam l₃ (cutoff3 (10 ^ 4 * A) N) N α -
            retainedMangoldt A lam l₃ (cutoff3 (10 ^ 4 * A) N) N α‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  refine ⟨5, 3, by norm_num, ?_⟩
  intro N hodd hN lam hlam α
  have hN3 : (3 : ℝ) ≤ N := hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  let y : ℝ := (N : ℝ) * Real.log N ^ (-4 * A)
  let Y : ℕ := ⌊y⌋₊
  let K : ℕ := cutoff3 (10 ^ 4 * A) N
  let f : ℕ → ℂ := fun n =>
    (ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hY : (Y : ℝ) ≤ y := Nat.floor_le hy0
  have hyN : y ≤ N := mul_le_of_le_one_right (Nat.cast_nonneg N)
    (Real.rpow_le_one_of_one_le_of_nonpos hL (by nlinarith))
  have hYN : Y ≤ N := by exact_mod_cast hY.trans hyN
  have hs : (Icc 1 N).filter (fun n : ℕ => ¬(y < (n : ℝ))) = Icc 1 Y := by
    ext n
    simp only [mem_filter, mem_Icc, not_lt]
    constructor
    · rintro ⟨hn, hny⟩
      exact ⟨hn.1, Nat.le_floor hny⟩
    · rintro ⟨hn1, hny⟩
      exact ⟨⟨hn1, hny.trans hYN⟩, (Nat.cast_le.mpr hny).trans hY⟩
  have hsplit : retainedMangoldt A lam l₃ K N α + ∑ n ∈ Icc 1 Y, f n =
      ∑ n ∈ Icc 1 N, f n := by
    have hh := sum_filter_add_sum_filter_not (Icc 1 N) (fun n : ℕ => y < (n : ℝ)) f
    rw [hs] at hh
    exact hh
  have hp := Kfun_add_prime_powers lam l₃ K N α
  have hid : Kfun lam l₃ K N α - retainedMangoldt A lam l₃ K N α =
      (∑ n ∈ Icc 1 Y, f n) - ∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime), f n := by
    change Kfun lam l₃ K N α + ∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime), f n =
      ∑ n ∈ Icc 1 N, f n at hp
    linear_combination hp - hsplit
  change ‖Kfun lam l₃ K N α - retainedMangoldt A lam l₃ K N α‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖∑ n ∈ Icc 1 Y, f n‖ + ‖∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime), f n‖ :=
      norm_sub_le _ _
    _ ≤ 3 * N * Real.log N ^ (330 - 4 * A) + 2 * N * Real.log N ^ (330 - 4 * A) :=
      add_le_add (initial_segment_mass_cutoff A lam l₃ N α hA hlam hL)
        (prime_power_mass_cutoff A lam l₃ N α hA hlam hL)
    _ = _ := by ring


/-! ### Copy of Decomp424a, the Heath Brown identity and the grouping combinatorics -/

/-- A Dirichlet convolution vanishes below the product of support lower bounds.
This is the finite support step behind Heath Brown 1982 page 1367 display 7. -/
theorem convolution_vanish_below {R : Type*} [Semiring R] (f g : ArithmeticFunction R)
    (u v n : ℕ) (hf : ∀ m < u, f m = 0) (hg : ∀ m < v, g m = 0)
    (hn : n < u * v) : (f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply sum_eq_zero
  intro p hp
  have he : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases h₁ : p.1 < u
  · rw [hf _ h₁, zero_mul]
  · have h₂ : p.2 < v := by
      by_contra h₂
      have hle := Nat.mul_le_mul (le_of_not_gt h₁) (le_of_not_gt h₂)
      omega
    rw [hg _ h₂, mul_zero]

/-- The kth convolution power vanishes below the kth power of a support bound.
Source: Heath Brown 1982 page 1367 display 7 and the vanishing remainder after display 6. -/
theorem convolution_pow_vanish_below {R : Type*} [Semiring R] (f : ArithmeticFunction R)
    (u k n : ℕ) (hf : ∀ m < u, f m = 0) (hn : n < u ^ k) : (f ^ k) n = 0 := by
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst n
    simp
  | succ k ih =>
    rw [pow_succ]
    exact convolution_vanish_below (f ^ k) f (u ^ k) u n (fun m hm => ih m hm) hf
      (by simpa [pow_succ] using hn)

/-- The cubic algebra identity underlying the k equal to three specialization.
Source: Heath Brown 1982 page 1367 display 6. -/
theorem heathBrown_three_ring {R : Type*} [CommRing R] (Z M L : R) :
    L = 3 * M * (Z * L) - 3 * Z * M ^ 2 * (Z * L) +
      Z ^ 2 * M ^ 3 * (Z * L) + (1 - Z * M) ^ 3 * L := by
  ring

/-- The k equal to three identity in the ring of arithmetic functions.
Mathlib supplies the truncated Moebius factor and its exact convolution with zeta.
Source: Heath Brown 1982 page 1367 displays 6 and 7. -/
theorem heathBrown_three_convolution (U : ℕ) (hU : 1 ≤ U) :
    ArithmeticFunction.vonMangoldt =
      3 * LeanLab.HeathBrown1985.muLe U * ArithmeticFunction.log -
      3 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        LeanLab.HeathBrown1985.muLe U ^ 2 * ArithmeticFunction.log +
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 *
        LeanLab.HeathBrown1985.muLe U ^ 3 * ArithmeticFunction.log -
      LeanLab.HeathBrown1985.dGt U ^ 3 * ArithmeticFunction.vonMangoldt := by
  have h := heathBrown_three_ring (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    (LeanLab.HeathBrown1985.muLe U) ArithmeticFunction.vonMangoldt
  rw [ArithmeticFunction.zeta_mul_vonMangoldt] at h
  have hd : 1 - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      LeanLab.HeathBrown1985.muLe U = -LeanLab.HeathBrown1985.dGt U := by
    rw [mul_comm, LeanLab.HeathBrown1985.muLe_mul_zeta U hU]
    ring
  rw [hd] at h
  convert h using 1 <;> ring

/-- On the range below the cubic support threshold the remainder vanishes exactly.
This is the finite coefficient form of Heath Brown 1982 page 1367 displays 6 to 8.
No dyadic factor grouping or coefficient estimate is asserted. -/
theorem heathBrown_three_coefficient (U n : ℕ) (hU : 1 ≤ U) (hn : n < (U + 1) ^ 3) :
    ArithmeticFunction.vonMangoldt n =
      (3 * LeanLab.HeathBrown1985.muLe U * ArithmeticFunction.log -
        3 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          LeanLab.HeathBrown1985.muLe U ^ 2 * ArithmeticFunction.log +
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 *
          LeanLab.HeathBrown1985.muLe U ^ 3 * ArithmeticFunction.log : ArithmeticFunction ℝ) n := by
  have hd : ∀ m < U + 1, LeanLab.HeathBrown1985.dGt U m = 0 := by
    intro m hm
    simp [LeanLab.HeathBrown1985.dGt, show ¬U < m by omega]
  have hp : ∀ m < (U + 1) ^ 3, (LeanLab.HeathBrown1985.dGt U ^ 3) m = 0 :=
    fun m hm => convolution_pow_vanish_below _ (U + 1) 3 m hd hm
  have hz : (LeanLab.HeathBrown1985.dGt U ^ 3 * ArithmeticFunction.vonMangoldt) n = 0 := by
    apply convolution_vanish_below _ _ ((U + 1) ^ 3) 1 n hp
    · intro m hm
      have hm0 : m = 0 := by omega
      subst m
      simp
    · simpa using hn
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (heathBrown_three_convolution U hU)
  change ArithmeticFunction.vonMangoldt n =
    (3 * LeanLab.HeathBrown1985.muLe U * ArithmeticFunction.log -
      3 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        LeanLab.HeathBrown1985.muLe U ^ 2 * ArithmeticFunction.log +
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 *
        LeanLab.HeathBrown1985.muLe U ^ 3 * ArithmeticFunction.log : ArithmeticFunction ℝ) n -
      (LeanLab.HeathBrown1985.dGt U ^ 3 * ArithmeticFunction.vonMangoldt) n at h
  simpa only [hz, sub_zero] using h


/-- The norm of a Dirichlet convolution is at most the convolution of pointwise majorants.
This is the triangle step in the coefficient bounds of Tolev 1999 page 71 Lemma 4. -/
theorem norm_convolution_le (f g : ArithmeticFunction ℂ) (F G : ArithmeticFunction ℝ)
    (hf : ∀ n, ‖f n‖ ≤ F n) (hg : ∀ n, ‖g n‖ ≤ G n) (n : ℕ) :
    ‖(f * g) n‖ ≤ (F * G) n := by
  simp only [ArithmeticFunction.mul_apply]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  rw [norm_mul]
  exact mul_le_mul (hf p.1) (hg p.2) (norm_nonneg _) ((norm_nonneg _).trans (hf p.1))

/-- A finite convolution of bounded factors is majorized by the matching power of zeta.
Source: the divisor coefficient bound in Tolev 1999 page 71 Lemma 4. -/
theorem norm_product_le_zeta_power {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ArithmeticFunction ℂ)
    (hf : ∀ i ∈ s, ∀ n : ℕ, n ≠ 0 → ‖f i n‖ ≤ 1) (n : ℕ) :
    ‖(∏ i ∈ s, f i) n‖ ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ s.card) n := by
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [prod_empty, card_empty, pow_zero, ArithmeticFunction.one_apply]
    split_ifs <;> simp
  | @insert i s hi ih =>
    rw [prod_insert hi, card_insert_of_notMem hi, pow_succ, mul_comm _ (ArithmeticFunction.zeta : ArithmeticFunction ℝ)]
    apply norm_convolution_le
    · intro m
      by_cases hm : m = 0
      · subst m; simp
      · simpa [ArithmeticFunction.zeta_apply, hm] using hf i (mem_insert_self _ _) m hm
    · intro m
      exact ih (fun j hj => hf j (mem_insert_of_mem hj)) m


/-- The weighted von Mangoldt polynomial on one annulus, with the original upper cap.
Tolev 1999 page 71 display 9 with G containing the phase and divisor weight. -/
noncomputable def annularMangoldt (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, if x < (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then
    (ArithmeticFunction.vonMangoldt n : ℂ) * ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ)
  else 0

/-- The explicit truncated k equal to three Heath Brown convolution polynomial.
Source: Heath Brown 1982 page 1367 display 6 after omitting the remainder. -/
noncomputable def heathBrownPolynomial (U : ℕ) : ArithmeticFunction ℝ :=
  3 * LeanLab.HeathBrown1985.muLe U * ArithmeticFunction.log -
    3 * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      LeanLab.HeathBrown1985.muLe U ^ 2 * ArithmeticFunction.log +
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ 2 *
      LeanLab.HeathBrown1985.muLe U ^ 3 * ArithmeticFunction.log

/-- The floor of the real cube root is a valid truncated Moebius cutoff.
Source: Heath Brown 1982 page 1367, the choice of X before display 7. -/
theorem cubic_cutoff (x : ℝ) (hx : 3 ≤ x) :
    1 ≤ ⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊ ∧
      2 * x < ((⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊ + 1 : ℕ) : ℝ) ^ (3 : ℕ) := by
  have hx0 : 0 ≤ 2 * x := by linarith
  have hr : 1 ≤ (2 * x) ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hp : ((2 * x) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = 2 * x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  refine ⟨?_, ?_⟩
  · exact (Nat.le_floor_iff (by positivity)).mpr (by simpa using hr)
  · have hlt := Nat.lt_floor_add_one ((2 * x) ^ ((1 : ℝ) / 3))
    have hpow := pow_lt_pow_left₀ hlt (by positivity : (0 : ℝ) ≤ (2 * x) ^ ((1 : ℝ) / 3)) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [hp, Nat.cast_add, Nat.cast_one] using hpow

/-- The weighted annular polynomial with the explicit truncated convolution coefficient.
Source: Heath Brown 1982 page 1367 displays 6 to 8. -/
noncomputable def annularHeathBrown (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, if x < (n : ℝ) ∧ (n : ℝ) ≤ 2 * x then
    (heathBrownPolynomial ⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊ n : ℂ) *
      ee (α * n) * (L2Bound.weight lam l₃ K n : ℂ)
  else 0

/-- The coefficient identity replaces von Mangoldt on an entire annulus exactly.
There is no dyadic grouping input here.
Source: Heath Brown 1982 page 1367 displays 6 to 8. -/
theorem annularMangoldt_eq_heathBrown (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x : ℝ)
    (hx : 3 ≤ x) : annularMangoldt lam l₃ K N α x = annularHeathBrown lam l₃ K N α x := by
  obtain ⟨hU, hcube⟩ := cubic_cutoff x hx
  unfold annularMangoldt annularHeathBrown
  apply sum_congr rfl
  intro n hn
  by_cases hc : x < (n : ℝ) ∧ (n : ℝ) ≤ 2 * x
  · simp only [hc, ite_true]
    have hncube : n < (⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊ + 1) ^ 3 := by
      exact_mod_cast hc.2.trans_lt hcube
    have he : ArithmeticFunction.vonMangoldt n =
        heathBrownPolynomial ⌊(2 * x) ^ ((1 : ℝ) / 3)⌋₊ n :=
      heathBrown_three_coefficient _ n hU hncube
    rw [he]
  · simp only [hc, ite_false]

/-- The printed u, v and z satisfy every numerical hypothesis of Lemma 4
at an explicit large threshold. This removes a parameter admissibility input.
Source: Tolev 1999 page 71 Lemma 4 and page 82 before display 53. -/
theorem source_parameters (x : ℝ) (hx : Real.exp 100000 ≤ x) :
    2 ≤ x ^ ((1 : ℝ) / 1000) ∧
    x ^ ((1 : ℝ) / 1000) < 2 ^ 30 * x ^ ((1 : ℝ) / 3) ∧
    2 ^ 30 * x ^ ((1 : ℝ) / 3) ≤ x ^ ((249 : ℝ) / 500) ∧
    x ^ ((249 : ℝ) / 500) ≤ x ∧
    (x ^ ((1 : ℝ) / 1000)) ^ (2 : ℕ) ≤ x ^ ((249 : ℝ) / 500) ∧
    128 * x ^ ((1 : ℝ) / 1000) * (x ^ ((249 : ℝ) / 500)) ^ (2 : ℕ) ≤ 2 * x ∧
    2 ^ 18 * (2 * x) ≤ (2 ^ 30 * x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hx
  have hL : 100000 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogv : Real.log (2 ^ 30 * x ^ ((1 : ℝ) / 3)) =
      30 * Real.log 2 + (1 / 3) * Real.log x := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_rpow hxpos]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (Real.log_le_log_iff (by norm_num) (by positivity)).mp
    rw [Real.log_rpow hxpos]
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_rpow hxpos, hlogv]
    nlinarith
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [hlogv, Real.log_rpow hxpos]
    nlinarith
  · apply (Real.log_le_log_iff (by positivity) hxpos).mp
    rw [Real.log_rpow hxpos]
    nlinarith
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow, Real.log_rpow hxpos, Real.log_rpow hxpos]
    norm_num
    nlinarith
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_rpow hxpos, Real.log_rpow hxpos, Real.log_mul (by positivity) hxpos.ne']
    have h128 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [h128]
    norm_num
    nlinarith
  · have hp : (x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
      norm_num
    rw [mul_pow, hp]
    norm_num
    nlinarith


/-- A family of factors at most u whose product reaches u contains a nonempty
subset with product from u to strictly below u squared.
Source: the small factor grouping in Heath Brown 1982 page 1368 after display 8. -/
theorem exists_subset_product_between {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (u : ℝ) (hu : 1 < u)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ u) (hprod : u ≤ ∏ i ∈ s, a i) :
    ∃ t : Finset ι, t ⊆ s ∧ t.Nonempty ∧ u ≤ ∏ i ∈ t, a i ∧ (∏ i ∈ t, a i) < u ^ (2 : ℕ) := by
  classical
  let T := s.powerset.filter (fun t => u ≤ ∏ i ∈ t, a i)
  have hT : T.Nonempty := ⟨s, by simp [T, hprod]⟩
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image T (fun t => t.card) hT
  obtain ⟨htS, htp⟩ := mem_filter.mp ht
  have hts : t ⊆ s := mem_powerset.mp htS
  have htne : t.Nonempty := by
    by_contra hn
    have he : t = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp only [he, prod_empty] at htp
    linarith
  obtain ⟨i, hi⟩ := htne
  have herase : (∏ j ∈ t.erase i, a j) < u := by
    by_contra hnot
    have hm : t.erase i ∈ T := by
      apply mem_filter.mpr
      exact ⟨mem_powerset.mpr ((erase_subset i t).trans hts), le_of_not_gt hnot⟩
    have hc := hmin (t.erase i) hm
    have hl := card_erase_lt_of_mem hi
    omega
  have hpnon : 0 ≤ ∏ j ∈ t.erase i, a j :=
    prod_nonneg (fun j hj => (ha j (hts (mem_of_mem_erase hj))).1)
  have hu0 : 0 < u := by linarith
  refine ⟨t, hts, ⟨i, hi⟩, htp, ?_⟩
  calc
    (∏ j ∈ t, a j) = (∏ j ∈ t.erase i, a j) * a i := (prod_erase_mul t a hi).symm
    _ ≤ (∏ j ∈ t.erase i, a j) * u := mul_le_mul_of_nonneg_left (ha i (hts hi)).2 hpnon
    _ < u * u := mul_lt_mul_of_pos_right herase hu0
    _ = u ^ (2 : ℕ) := by ring



/-- Small nonnegative factors partition into disjoint nonempty groups with products
from u to below u squared, and a disjoint remainder with product below u.
Source: Heath Brown 1982 page 1368, the groups P and the remainder Q. -/
theorem partition_small_products {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (u : ℝ) (hu : 1 < u)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ u) :
    ∃ R : Finset ι, ∃ T : Finset (Finset ι),
      R ⊆ s ∧
      (∀ t ∈ T, t ⊆ s ∧ t.Nonempty ∧ u ≤ ∏ i ∈ t, a i ∧ (∏ i ∈ t, a i) < u ^ (2 : ℕ)) ∧
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint t₁ t₂) ∧
      Disjoint R (T.biUnion id) ∧ R ∪ T.biUnion id = s ∧ (∏ i ∈ R, a i) < u := by
  classical
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases hp : u ≤ ∏ i ∈ s, a i
  · obtain ⟨t, hts, htne, htlo, hthi⟩ := exists_subset_product_between s a u hu ha hp
    obtain ⟨R, T, hR, hTs, hpair, hd, hcover, hprod⟩ :=
      ih (s \ t) (sdiff_ssubset hts htne) (fun i hi => ha i (mem_sdiff.mp hi).1)
    have hRt : Disjoint R t := by
      apply disjoint_left.mpr
      intro i hi hit
      exact (mem_sdiff.mp (hR hi)).2 hit
    have hTt : ∀ q ∈ T, Disjoint t q := by
      intro q hq
      apply disjoint_left.mpr
      intro i hit hiq
      exact (mem_sdiff.mp ((hTs q hq).1 hiq)).2 hit
    refine ⟨R, insert t T, hR.trans sdiff_subset, ?_, ?_, ?_, ?_, hprod⟩
    · intro q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact ⟨hts, htne, htlo, hthi⟩
      · exact ⟨(hTs q hq).1.trans sdiff_subset, (hTs q hq).2⟩
    · intro q hq q' hq' hne
      by_cases hqt : q = t
      · subst q
        exact hTt q' ((mem_insert.mp hq').resolve_left (Ne.symm hne))
      · have hqT : q ∈ T := (mem_insert.mp hq).resolve_left hqt
        by_cases hq't : q' = t
        · subst q'
          exact (hTt q hqT).symm
        · exact hpair q hqT q' ((mem_insert.mp hq').resolve_left hq't) hne
    · rw [biUnion_insert]
      exact disjoint_union_right.mpr ⟨hRt, hd⟩
    · rw [biUnion_insert]
      change R ∪ (t ∪ T.biUnion id) = s
      rw [show R ∪ (t ∪ T.biUnion id) = (R ∪ T.biUnion id) ∪ t by ac_rfl,
        hcover, sdiff_union_of_subset hts]
  · refine ⟨s, ∅, subset_rfl, ?_, ?_, ?_, ?_, lt_of_not_ge hp⟩ <;> simp


/-- Groups whose factors lie between V and z give either the two group upper bound
or the three group lower bound, after including a remainder between one and u.
Source: the two product inequalities on Heath Brown 1982 page 1368. -/
theorem group_product_dichotomy {ι : Type*} (s : Finset ι) (g : ι → ℝ)
    (Q u V z : ℝ) (hQ : 1 ≤ Q) (hQu : Q ≤ u) (hV : 1 ≤ V) (hz : 1 ≤ z)
    (hg : ∀ i ∈ s, V ≤ g i ∧ g i ≤ z) :
    Q * (∏ i ∈ s, g i) ≤ u * z ^ (2 : ℕ) ∨ V ^ (3 : ℕ) ≤ Q * (∏ i ∈ s, g i) := by
  have hnon : ∀ i ∈ s, 0 ≤ g i := fun i hi => (zero_le_one.trans hV).trans (hg i hi).1
  have hp0 : 0 ≤ ∏ i ∈ s, g i := prod_nonneg hnon
  have hpupper : (∏ i ∈ s, g i) ≤ z ^ s.card := by
    calc
      _ ≤ ∏ i ∈ s, z := prod_le_prod₀ hnon (fun i hi => (hg i hi).2)
      _ = _ := by simp
  have hplower : V ^ s.card ≤ ∏ i ∈ s, g i := by
    calc
      _ = ∏ i ∈ s, V := by simp
      _ ≤ _ := prod_le_prod₀ (fun i hi => zero_le_one.trans hV) (fun i hi => (hg i hi).1)
  by_cases hk : s.card ≤ 2
  · left
    have hp2 := hpupper.trans (pow_le_pow_right₀ hz hk)
    exact mul_le_mul hQu hp2 hp0 ((zero_le_one.trans hQ).trans hQu)
  · right
    have hp3 := (pow_le_pow_right₀ hV (show 3 ≤ s.card by omega)).trans hplower
    exact hp3.trans (le_mul_of_one_le_left hp0 hQ)



/-- The product contradiction selects a subset in the middle range for factors
at least one. Source: Heath Brown 1982 page 1368 after display 8. -/
theorem exists_subset_product_in_range {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (u V z : ℝ) (hu : 1 < u)
    (huV : u ≤ V) (hu2 : u ^ (2 : ℕ) ≤ z)
    (ha : ∀ i ∈ s, 1 ≤ a i ∧ a i ≤ z)
    (hlo : u * z ^ (2 : ℕ) < ∏ i ∈ s, a i)
    (hhi : (∏ i ∈ s, a i) < V ^ (3 : ℕ)) :
    ∃ t : Finset ι, t ⊆ s ∧ u ≤ ∏ i ∈ t, a i ∧ (∏ i ∈ t, a i) ≤ V := by
  classical
  by_contra hnone
  have hno : ∀ t : Finset ι, t ⊆ s → u ≤ ∏ i ∈ t, a i → V < ∏ i ∈ t, a i := by
    intro t hts htu
    by_contra htV
    exact hnone ⟨t, hts, htu, le_of_not_gt htV⟩
  let small := s.filter (fun i => a i < u)
  let large := s.filter (fun i => u ≤ a i)
  have hsmallS : small ⊆ s := filter_subset _ _
  have hlargeS : large ⊆ s := filter_subset _ _
  have hsl : small ∪ large = s := by
    ext i
    simp only [small, large, mem_union, mem_filter]
    constructor
    · tauto
    · intro hi
      rcases lt_or_ge (a i) u with h | h
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr ⟨hi, h⟩
  have hdsl : Disjoint small large := by
    apply disjoint_left.mpr
    intro i his hil
    exact (not_lt_of_ge (mem_filter.mp hil).2) (mem_filter.mp his).2
  obtain ⟨R, T, hR, hTs, hpair, hd, hcover, hprodR⟩ :=
    partition_small_products small a u hu (fun i hi =>
      ⟨(zero_le_one.trans (ha i (hsmallS hi)).1), (mem_filter.mp hi).2.le⟩)
  have hR1 : 1 ≤ ∏ i ∈ R, a i := by
    calc
      (1 : ℝ) = ∏ i ∈ R, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod₀ (by intro i hi; norm_num)
        (fun i hi => (ha i (hsmallS (hR hi))).1)
  have htpair : (T : Set (Finset ι)).PairwiseDisjoint id := by
    intro t ht q hq hne
    exact hpair t ht q hq hne
  have hsmallprod : (∏ i ∈ small, a i) = (∏ i ∈ R, a i) * (∏ t ∈ T, ∏ i ∈ t, a i) := by
    rw [← hcover, prod_union hd, prod_biUnion htpair]
    rfl
  let groups := large.disjSum T
  let g : Sum ι (Finset ι) → ℝ := Sum.elim a (fun t => ∏ i ∈ t, a i)
  have hgroup : ∀ j ∈ groups, V ≤ g j ∧ g j ≤ z := by
    intro j hj
    cases j with
    | inl i =>
      have hi : i ∈ large := by simpa [groups] using hj
      have his := hlargeS hi
      have htu : u ≤ a i := (mem_filter.mp hi).2
      have ht := hno {i} (singleton_subset_iff.mpr his) (by simpa using htu)
      exact ⟨by simpa [g] using ht.le, (ha i his).2⟩
    | inr t =>
      have ht : t ∈ T := by simpa [groups] using hj
      have hts := hTs t ht
      have hl := hno t (hts.1.trans hsmallS) hts.2.2.1
      exact ⟨hl.le, hts.2.2.2.le.trans hu2⟩
  have hgp : (∏ j ∈ groups, g j) = (∏ i ∈ large, a i) * (∏ t ∈ T, ∏ i ∈ t, a i) := by
    simp [groups, g]
  have hfull : (∏ i ∈ s, a i) = (∏ i ∈ R, a i) * (∏ j ∈ groups, g j) := by
    rw [hgp, ← hsl, prod_union hdsl, hsmallprod]
    ring
  have hz : 1 ≤ z := by nlinarith
  rcases group_product_dichotomy groups g (∏ i ∈ R, a i) u V z hR1 hprodR.le
    (by linarith) hz hgroup with h | h
  · rw [← hfull] at h
    linarith
  · rw [← hfull] at h
    linarith



/-- Replacing factors at least one half by their maximum with one changes the
product by at most two to the number of factors. This handles singleton dyadic intervals
in the adaptation of Heath Brown 1982 pages 1367 to 1368. -/
theorem product_max_one_bounds {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, (1 : ℝ) / 2 ≤ a i) :
    (∏ i ∈ s, a i) ≤ (∏ i ∈ s, max 1 (a i)) ∧
      (∏ i ∈ s, max 1 (a i)) ≤ 2 ^ s.card * (∏ i ∈ s, a i) := by
  constructor
  · exact prod_le_prod₀ (fun i hi => by linarith [ha i hi]) (fun i hi => le_max_right _ _)
  · calc
      _ ≤ ∏ i ∈ s, 2 * a i := prod_le_prod₀ (fun i hi => by positivity) (fun i hi => by
        apply max_le <;> linarith [ha i hi])
      _ = _ := by rw [prod_mul_distrib]; simp

/-- The middle product selection extends to at most six factors at least one half.
Explicit factors of 64 account for the dyadic singleton intervals.
Source: the adapted grouping argument of Heath Brown 1982 pages 1367 to 1368. -/
theorem exists_subset_product_half_scale {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (u V z : ℝ) (hu : 1 < u)
    (huV : 64 * u ≤ V) (hu2 : (64 * u) ^ (2 : ℕ) ≤ z)
    (ha : ∀ i ∈ s, (1 : ℝ) / 2 ≤ a i ∧ a i ≤ z) (hcard : s.card ≤ 6)
    (hlo : (64 * u) * z ^ (2 : ℕ) < ∏ i ∈ s, a i)
    (hhi : 64 * (∏ i ∈ s, a i) < V ^ (3 : ℕ)) :
    ∃ t : Finset ι, t ⊆ s ∧ u ≤ ∏ i ∈ t, a i ∧ (∏ i ∈ t, a i) ≤ V := by
  classical
  let b : ι → ℝ := fun i => max 1 (a i)
  have hz : 1 ≤ z := by nlinarith
  have hb : ∀ i ∈ s, 1 ≤ b i ∧ b i ≤ z := by
    intro i hi
    exact ⟨le_max_left _ _, max_le hz (ha i hi).2⟩
  have hbound : ∀ t : Finset ι, t ⊆ s →
      (∏ i ∈ t, a i) ≤ (∏ i ∈ t, b i) ∧
      (∏ i ∈ t, b i) ≤ 64 * (∏ i ∈ t, a i) := by
    intro t hts
    have ht := product_max_one_bounds t a (fun i hi => (ha i (hts hi)).1)
    have hp0 : 0 ≤ ∏ i ∈ t, a i := prod_nonneg (fun i hi => by linarith [(ha i (hts hi)).1])
    refine ⟨ht.1, ht.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_right ?_ hp0
    have hc : t.card ≤ 6 := (card_le_card hts).trans hcard
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hc
    norm_num at hh ⊢
    exact hh
  have hbs := hbound s subset_rfl
  obtain ⟨t, hts, htu, htV⟩ := exists_subset_product_in_range s b (64 * u) V z
    (by linarith) huV hu2 hb (hlo.trans_le hbs.1) (hbs.2.trans_lt hhi)
  have hbt := hbound t hts
  refine ⟨t, hts, ?_, hbt.1.trans htV⟩
  have hh := htu.trans hbt.2
  linarith



/-- The printed exponents have enough slack for the explicit singleton adjustment.
Source: Tolev 1999 page 82 and the adapted grouping on Heath Brown 1982 page 1368.
The constants 64 and 4096 here are implementation bounds, not printed claims. -/
theorem source_half_scale_parameters (x : ℝ) (hx : Real.exp 100000 ≤ x) :
    64 * x ^ ((1 : ℝ) / 1000) ≤ 2 ^ 24 * x ^ ((1 : ℝ) / 3) ∧
    (64 * x ^ ((1 : ℝ) / 1000)) ^ (2 : ℕ) ≤ x ^ ((249 : ℝ) / 500) ∧
    4096 * x ^ ((1 : ℝ) / 1000) * (x ^ ((249 : ℝ) / 500)) ^ (2 : ℕ) < x ∧
    128 * x < (2 ^ 24 * x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hx
  have hL : 100000 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have h4096 : Real.log 4096 = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ (12 : ℕ) by norm_num, Real.log_pow]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_rpow hxpos, Real.log_rpow hxpos, h64]
    norm_num
    nlinarith
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hxpos, Real.log_rpow hxpos, h64]
    norm_num
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) hxpos).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_rpow hxpos, Real.log_rpow hxpos, h4096]
    norm_num
    nlinarith
  · have hp : (x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
      norm_num
    rw [mul_pow, hp]
    norm_num
    nlinarith



/-! ### Copy of Decomp424b, the outer dyadic shells -/

/-- Consecutive doubled annuli telescope exactly, including both endpoints.
This is the finite outer subdivision in Tolev 1999 page 82 display 52. -/
theorem sum_doubled_annuli (f : ℕ → ℂ) (N t : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    (∑ j ∈ range t, ∑ n ∈ Icc 1 N,
      if y * 2 ^ j < (n : ℝ) ∧ (n : ℝ) ≤ 2 * (y * 2 ^ j) then f n else 0) =
    ∑ n ∈ Icc 1 N, if y < (n : ℝ) ∧ (n : ℝ) ≤ y * 2 ^ t then f n else 0 := by
  induction t with
  | zero =>
    simp only [range_zero, sum_empty, pow_zero, mul_one]
    symm
    apply sum_eq_zero
    intro n hn
    exact if_neg (fun h => (not_lt_of_ge h.2) h.1)
  | succ t ih =>
    rw [sum_range_succ, ih, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    have hp : y ≤ y * 2 ^ t := le_mul_of_one_le_right hy (one_le_pow₀ (by norm_num))
    rw [show y * 2 ^ (t + 1) = 2 * (y * 2 ^ t) by ring]
    by_cases h₁ : y < (n : ℝ) <;>
      by_cases h₂ : (n : ℝ) ≤ y * 2 ^ t <;>
        by_cases h₃ : (n : ℝ) ≤ 2 * (y * 2 ^ t) <;>
          simp_all <;> linarith

/-- Annuli above the cap are empty, so unused outer shells require no blocks.
This keeps the original cap in Tolev 1999 page 82 display 52. -/
theorem annularMangoldt_eq_zero (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x : ℝ)
    (hx : (N : ℝ) ≤ x) : annularMangoldt lam l₃ K N α x = 0 := by
  apply sum_eq_zero
  intro n hn
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  exact if_neg (fun h => (not_lt_of_ge (hnN.trans hx)) h.1)

/-- The retained polynomial is the exact sum of doubled annuli once their upper
endpoint reaches N. This is the full interval completion of Tolev 1999 display 52. -/
theorem retainedMangoldt_eq_annuli (A : ℝ) (lam : ℕ → ℝ) (l₃ K N t : ℕ) (α : ℝ)
    (hcover : (N : ℝ) ≤ (N : ℝ) * Real.log N ^ (-4 * A) * 2 ^ t) :
    retainedMangoldt A lam l₃ K N α =
      ∑ j ∈ range t, annularMangoldt lam l₃ K N α
        ((N : ℝ) * Real.log N ^ (-4 * A) * 2 ^ j) := by
  unfold annularMangoldt
  rw [sum_doubled_annuli _ _ _ _ (by positivity)]
  unfold retainedMangoldt
  rw [sum_filter]
  apply sum_congr rfl
  intro n hn
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  simp only [and_iff_left (hnN.trans hcover)]

/-- The existing logarithmic shell bound also bounds the number of retained annuli.
Source: the six log factors on Heath Brown page 1367 gain one outer log factor. -/
theorem shell_count_le (N : ℕ) (hL : 1 ≤ Real.log N) :
    (Nat.clog 2 N : ℝ) ≤ (1 / Real.log 2 + 2) * Real.log N := by
  exact (show (Nat.clog 2 N : ℝ) ≤ (Nat.clog 2 N + 1 : ℝ) by norm_num).trans
    (Dyadic.block_count_le N N le_rfl hL)

/-- The retained lower endpoint eventually exceeds any fixed positive threshold.
This justifies applying the annular identity after removing the short initial segment.
Source: the full interval adaptation of Tolev 1999 page 82 display 52. -/
theorem eventual_retained_radius (A X₀ : ℝ) (hX : 1 ≤ X₀) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      1 ≤ Real.log N ∧ X₀ ≤ (N : ℝ) * Real.log N ^ (-4 * A) := by
  have hXpos : 0 < X₀ := by linarith
  have he := (isLittleO_log_rpow_rpow_atTop (4 * A) (by norm_num : (0 : ℝ) < 1)).bound
    (show (0 : ℝ) < 1 / X₀ by positivity)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp he
  refine ⟨max T (Real.exp 1), ?_⟩
  intro N hN
  have hNe : Real.exp 1 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := (Real.exp_pos 1).trans_le hNe
  have hL : 1 ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).mpr hNe
  have hLpos : 0 < Real.log N := by linarith
  have hb := hT (N : ℝ) ((le_max_left _ _).trans hN)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one,
    abs_of_nonneg (Real.rpow_nonneg hLpos.le _), abs_of_pos hNpos] at hb
  have hb' : Real.log N ^ (4 * A) ≤ (N : ℝ) / X₀ := by
    convert hb using 1 <;> ring
  have hm := (le_div_iff₀ hXpos).mp hb'
  refine ⟨hL, ?_⟩
  rw [show -4 * A = -(4 * A) by ring, Real.rpow_neg hLpos.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hLpos _)).mpr
  nlinarith


end LeanLab.Tolev2009.Sup83Heath
