module

public import LeanLab.Perelli1996.Divisor103

/-!
P0083 Perelli 1996, page 481 between equations 3 and 4.
Standard argument: elementary power moments of the divisor function,
sum of tau(d)^E / d and sum of tau(d)^E over d up to D, each bounded by a fixed
power of 1 + log D, and the hyperbola-restricted double sum built from them.
This replaces part of the citation of Nair 1992 by a van der Corput style input.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Nair103
open Finset Real
open LeanLab.Perelli1996.Section2 LeanLab.Perelli1996.Divisor103

/-- The number of divisors is the two fold divisor count. -/
theorem card_divisors_eq_divisorCount (d : ℕ) : d.divisors.card = divisorCount 2 d := by
  change _ = (ArithmeticFunction.zeta ^ 2) d
  rw [pow_two, ArithmeticFunction.mul_zeta_apply, Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ArithmeticFunction.zeta_apply_ne (Nat.pos_of_mem_divisors hi).ne']

/-- Iterated squaring of the divisor function stays below a higher divisor count. -/
theorem card_divisors_pow_two_pow_le (j d : ℕ) :
    d.divisors.card ^ (2 ^ j) ≤ divisorCount (2 ^ (2 ^ j)) d := by
  induction j with
  | zero =>
    rw [pow_zero, pow_one, pow_one]
    exact (card_divisors_eq_divisorCount d).le
  | succ j ih =>
    calc d.divisors.card ^ (2 ^ (j + 1)) = (d.divisors.card ^ (2 ^ j)) ^ 2 := by
          rw [← pow_mul, pow_succ]
      _ ≤ (divisorCount (2 ^ (2 ^ j)) d) ^ 2 := Nat.pow_le_pow_left ih 2
      _ ≤ divisorCount ((2 ^ (2 ^ j)) ^ 2) d := divisorCount_sq_le _ _
      _ = divisorCount (2 ^ (2 ^ (j + 1))) d := by rw [← pow_mul, ← pow_succ]

/-- Any fixed power of the divisor function is below a fixed higher divisor count. -/
theorem card_divisors_pow_le (E d : ℕ) (hd : 1 ≤ d) :
    (d.divisors.card : ℝ) ^ E ≤ (divisorCount (2 ^ (2 ^ E)) d : ℝ) := by
  have h1 : 1 ≤ d.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  have h2 : d.divisors.card ^ E ≤ d.divisors.card ^ (2 ^ E) :=
    Nat.pow_le_pow_right h1 (Nat.lt_two_pow_self).le
  exact_mod_cast h2.trans (card_divisors_pow_two_pow_le E d)

theorem tau_pow_sums (E : ℕ) : ∃ M : ℕ, ∀ D : ℕ,
    (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ E) / d ≤ (1 + Real.log D) ^ M) ∧
    (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ) ^ E) ≤ D * (1 + Real.log D) ^ M) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = 2 ^ (2 ^ E) := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := by rw [hk]; exact Nat.one_le_two_pow
  have hpow : ∀ d : ℕ, 1 ≤ d → (d.divisors.card : ℝ) ^ E ≤ (divisorCount k d : ℝ) := by
    intro d hd
    rw [hk]
    exact card_divisors_pow_le E d hd
  refine ⟨k, fun D => ?_⟩
  have hset : Icc 1 D = Ioc 0 D := by ext n; simp; omega
  have hlog : (1 : ℝ) ≤ 1 + Real.log D := by
    have := Real.log_natCast_nonneg D
    linarith
  have hhar : 0 ≤ (harmonic D : ℝ) := by
    rw [← weightedDivisor_one_sum]
    exact Finset.sum_nonneg (fun n _ => weightedDivisor_nonneg 1 n)
  constructor
  · calc ∑ d ∈ Icc 1 D, ((d.divisors.card : ℝ) ^ E) / d
        ≤ ∑ d ∈ Icc 1 D, weightedDivisor k d := by
          apply Finset.sum_le_sum
          intro d hd
          change _ ≤ (divisorCount k d : ℝ) / d
          exact div_le_div_of_nonneg_right (hpow d (Finset.mem_Icc.mp hd).1) (Nat.cast_nonneg d)
      _ = ∑ d ∈ Ioc 0 D, weightedDivisor k d := by rw [hset]
      _ ≤ (harmonic D : ℝ) ^ k := weightedDivisor_sum_le k D
      _ ≤ (1 + Real.log D) ^ k := pow_le_pow_left₀ hhar (harmonic_le_one_add_log D) k
  · have hfirst := divisor_first_moment (k - 1) D
    rw [show k - 1 + 1 = k by omega] at hfirst
    calc ∑ d ∈ Icc 1 D, ((d.divisors.card : ℝ) ^ E)
        ≤ ∑ d ∈ Icc 1 D, (divisorCount k d : ℝ) :=
          Finset.sum_le_sum (fun d hd => hpow d (Finset.mem_Icc.mp hd).1)
      _ = ∑ d ∈ Ioc 0 D, (divisorCount k d : ℝ) := by rw [hset]
      _ ≤ D * (1 + Real.log D) ^ (k - 1) := hfirst
      _ ≤ D * (1 + Real.log D) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog (Nat.sub_le k 1)) (Nat.cast_nonneg D)

/-- The hyperbola-restricted double sum for an abstract nonnegative weight with log power moments. -/
theorem pair_sum_aux (t : ℕ → ℝ) (ht0 : ∀ d, 0 ≤ t d) (M : ℕ)
    (hM : ∀ D : ℕ, (∑ d ∈ Finset.Icc 1 D, t d / d ≤ (1 + Real.log D) ^ M) ∧
      (∑ d ∈ Finset.Icc 1 D, t d ≤ D * (1 + Real.log D) ^ M))
    (D : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∑ d₁ ∈ Finset.Icc 1 D, ∑ d₂ ∈ (Finset.Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D),
      (t d₁ * t d₂ * (A / ((d₁ : ℝ) * d₂) + 1)) ≤
    (A + D) * (1 + Real.log D) ^ (2 * M) := by
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 + Real.log D := ⟨_, rfl⟩
  rw [← hL]
  have hL1 : (1 : ℝ) ≤ L := by
    have := Real.log_natCast_nonneg D
    linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hS1 : ∑ d ∈ Icc 1 D, t d / d ≤ L ^ M := by rw [hL]; exact (hM D).1
  have hdiv0 : ∀ d : ℕ, 0 ≤ t d / d := fun d => div_nonneg (ht0 d) (Nat.cast_nonneg d)
  have hinnerA : ∀ d₁ : ℕ,
      ∑ d₂ ∈ (Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D), t d₂ / d₂ ≤ L ^ M := by
    intro d₁
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun d _ _ => hdiv0 d)).trans hS1
  have hinner : ∀ d₁ ∈ Icc 1 D,
      ∑ d₂ ∈ (Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D), t d₂ ≤ (D : ℝ) / d₁ * L ^ M := by
    intro d₁ hd₁
    have hd1 : 1 ≤ d₁ := (Finset.mem_Icc.mp hd₁).1
    have hsub : (Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D) ⊆ Icc 1 (D / d₁) := by
      intro d₂ h
      rw [Finset.mem_filter, Finset.mem_Icc] at h
      rw [Finset.mem_Icc]
      exact ⟨h.1.1, (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact h.2)⟩
    have hlog0 : 0 ≤ Real.log ((D / d₁ : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hlogle : Real.log ((D / d₁ : ℕ) : ℝ) ≤ Real.log D := by
      rcases Nat.eq_zero_or_pos (D / d₁) with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg D
      · exact Real.log_le_log (by exact_mod_cast hpos)
          (by exact_mod_cast Nat.div_le_self D d₁)
    have hb : 1 + Real.log ((D / d₁ : ℕ) : ℝ) ≤ L := by rw [hL]; linarith
    calc ∑ d₂ ∈ (Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D), t d₂
        ≤ ∑ d₂ ∈ Icc 1 (D / d₁), t d₂ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => ht0 d)
      _ ≤ ((D / d₁ : ℕ) : ℝ) * (1 + Real.log ((D / d₁ : ℕ) : ℝ)) ^ M := (hM (D / d₁)).2
      _ ≤ (D : ℝ) / d₁ * L ^ M :=
          mul_le_mul Nat.cast_div_le (pow_le_pow_left₀ (by linarith) hb M)
            (pow_nonneg (by linarith) M) (div_nonneg (Nat.cast_nonneg D) (Nat.cast_nonneg d₁))
  calc ∑ d₁ ∈ Icc 1 D, ∑ d₂ ∈ (Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D),
        (t d₁ * t d₂ * (A / ((d₁ : ℝ) * d₂) + 1))
      = ∑ d₁ ∈ Icc 1 D, (A * (t d₁ / d₁) *
            (∑ d₂ ∈ (Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D), t d₂ / d₂) +
          t d₁ * ∑ d₂ ∈ (Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D), t d₂) := by
        apply Finset.sum_congr rfl
        intro d₁ _
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d₂ _
        ring
    _ ≤ ∑ d₁ ∈ Icc 1 D, (A * (t d₁ / d₁) * L ^ M + t d₁ * ((D : ℝ) / d₁ * L ^ M)) := by
        apply Finset.sum_le_sum
        intro d₁ hd₁
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hinnerA d₁) (mul_nonneg hA (hdiv0 d₁)))
          (mul_le_mul_of_nonneg_left (hinner d₁ hd₁) (ht0 d₁))
    _ = (A + D) * L ^ M * ∑ d₁ ∈ Icc 1 D, t d₁ / d₁ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d₁ _
        ring
    _ ≤ (A + D) * L ^ M * L ^ M :=
        mul_le_mul_of_nonneg_left hS1
          (mul_nonneg (add_nonneg hA (Nat.cast_nonneg D)) (pow_nonneg hL0 M))
    _ = (A + D) * L ^ (2 * M) := by rw [two_mul, pow_add]; ring

theorem tau_pair_sum (E : ℕ) : ∃ M : ℕ, ∀ (D : ℕ) (A : ℝ), 0 ≤ A →
    ∑ d₁ ∈ Finset.Icc 1 D, ∑ d₂ ∈ (Finset.Icc 1 D).filter (fun d₂ => d₁ * d₂ ≤ D),
      ((d₁.divisors.card : ℝ) ^ E * (d₂.divisors.card : ℝ) ^ E * (A / ((d₁ : ℝ) * d₂) + 1)) ≤
    (A + D) * (1 + Real.log D) ^ M := by
  obtain ⟨M, hM⟩ := tau_pow_sums E
  refine ⟨2 * M, fun D A hA => ?_⟩
  exact pair_sum_aux (fun d => (d.divisors.card : ℝ) ^ E) (fun d => by positivity) M hM D A hA

end LeanLab.Perelli1996.Nair103
