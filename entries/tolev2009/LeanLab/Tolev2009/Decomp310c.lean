module

public import LeanLab.Tolev2009.Decomp286b

/-!
AI wrote this Lean code. Codex task310.
Binary Goldbach is open.
Source: Tolev 1999 page 71 Lemma 4 and page 82 display 52.
https://doi.org/10.4064/aa-88-1-67-98.
Written identity proof: Heath Brown 1982 pages 1367 to 1368 displays 6 to 8.
https://doi.org/10.4153/CJM-1982-095-9.
The conversion is proved. The retained identity is proved.
The assembly is derived from retained_identity.
-/

@[expose] public section

open Finset Real

namespace LeanLab.Tolev2009.Decomp310c

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b

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


/-- The exact divisor identity for the von Mangoldt polynomial.
Mathlib gives it from the divisor convolution of log and the Moebius function.
This is the algebraic input for the dyadic factor pair split of the retained identity. -/
theorem vonMangoldt_moebius_log_divisor (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log ↑(n / d) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    ArithmeticFunction.log_mul_moebius_eq_vonMangoldt
  rw [ArithmeticFunction.mul_apply] at h
  calc
    (ArithmeticFunction.vonMangoldt n : ℝ) =
        ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.log x.1 *
          (ArithmeticFunction.moebius x.2 : ℝ) := h.symm
    _ = ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.2 : ℝ) * Real.log x.1 := by
          apply sum_congr rfl
          intro x hx
          rw [mul_comm]
          simp only [ArithmeticFunction.log_apply]
    _ = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log ↑(n / d) := by
          rw [Nat.sum_divisorsAntidiagonal'
            (fun i j => (ArithmeticFunction.moebius j : ℝ) * Real.log i)]

/-- Tolev 1999 page 71 Lemma 4 and page 82 displays 53 and 54.
Heath Brown 1982 pages 1367 to 1368 displays 6 to 8 give the written proof.
This is an exact finite identity for the retained von Mangoldt polynomial.
There is no prime conversion or remainder estimate. Dyadic shell counting is included.
The coefficient constants are absorbed in the bounded scalars. Proved. -/
theorem retained_identity :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) → ∀ α : ℝ,
          ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (7 : ℕ) ∧
          ∃ x M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
            retainedMangoldt A lam l₃ (cutoff3 (10 ^ 4 * A) N) N α =
              ∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
                (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
            ∀ j : Fin J,
              ‖c j‖ ≤ C ∧
              (N : ℝ) * Real.log N ^ (-4 * A) ≤ x j ∧ x j ≤ N ∧ 2 < x j ∧
              0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
              0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
              x j / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * x j ∧
              (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
              ((x j ^ ((249 : ℝ) / 500) ≤ H j ∧
                  (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
                (x j ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * x j ^ ((1 : ℝ) / 3) ∧
                  ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
  -- 2026-11-12 route burst: was an unproved placeholder; the proved twin has the same statement over
  -- copied definitions with identical bodies.
  exact LeanLab.Tolev2009.Sup83Split.retained_identity

/-- The exact sealed prime decomposition follows from the retained identity and conversion.
Derived from retained_identity only. The conversion error is proved. -/
theorem prime_decomposition :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) → ∀ α : ℝ,
          ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (7 : ℕ) ∧
          ∃ r : ℂ, ‖r‖ ≤ C * N * Real.log N ^ (330 - 4 * A) ∧
          ∃ x M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
            Kfun lam l₃ (cutoff3 (10 ^ 4 * A) N) N α = r +
              ∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
                (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
            ∀ j : Fin J,
              ‖c j‖ ≤ C ∧
              (N : ℝ) * Real.log N ^ (-4 * A) ≤ x j ∧ x j ≤ N ∧ 2 < x j ∧
              0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
              0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
              x j / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * x j ∧
              (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
              ((x j ^ ((249 : ℝ) / 500) ≤ H j ∧
                  (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
                (x j ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * x j ^ ((1 : ℝ) / 3) ∧
                  ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
  intro A hA l₃ hl₃
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := prime_power_and_initial_segment A hA l₃ hl₃
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := retained_identity A hA l₃ hl₃
  refine ⟨C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, ?_⟩
  intro N hodd hN lam hlam α
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  obtain ⟨J, hJ, x, M, M₁, H, H₁, a, b, c, he, hb⟩ := h₂ N hodd hN₂ lam hlam α
  refine ⟨J, ?_, Kfun lam l₃ (cutoff3 (10 ^ 4 * A) N) N α -
    retainedMangoldt A lam l₃ (cutoff3 (10 ^ 4 * A) N) N α, ?_,
    x, M, M₁, H, H₁, a, b, c, ?_, ?_⟩
  · exact hJ.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁) (by positivity))
  · apply (h₁ N hodd hN₁ lam hlam α).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  · rw [he]
    ring
  · intro j
    exact ⟨(hb j).1.trans (le_add_of_nonneg_left hC₁), (hb j).2⟩

end LeanLab.Tolev2009.Decomp310c
