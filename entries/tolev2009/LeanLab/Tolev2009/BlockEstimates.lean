module

public import LeanLab.Tolev2009.Dyadic

/-!
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/

@[expose] public section

open Finset Real MeasureTheory

namespace LeanLab.Tolev2009.BlockEstimates

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16 LeanLab.Tolev2009.Dyadic

/-- The display 17 estimate also holds for singleton and mixed blocks. -/
theorem display17_sets (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ)
    (s t : Finset ℕ) (hK₁ : 1 ≤ K₁) (hK₁N : K₁ ≤ N)
    (hK₂ : 1 ≤ K₂) (hK₂N : K₂ ≤ N)
    (hcs : s.card = K₁) (hct : t.card = K₂)
    (hs : ∀ k ∈ s, K₁ ≤ k) (ht : ∀ k ∈ t, K₂ ≤ k) :
    let W := ∑ k₁ ∈ s, ∑ k₂ ∈ t, ∑ n ∈ nSet N k₁ k₂,
      ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖
    (∑ k₁ ∈ s, ∑ k₂ ∈ t, innerF (fun k l => Rm Q τ k l N) lam l₃ K₃ k₁ k₂) ≤
      Real.sqrt 8 * Real.log N ^ 2 * N * Real.sqrt W := by
  dsimp only
  let W := ∑ k₁ ∈ s, ∑ k₂ ∈ t, ∑ n ∈ nSet N k₁ k₂,
      ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hK₁' : (0 : ℝ) < K₁ := by exact_mod_cast hK₁
  have hK₂' : (0 : ℝ) < K₂ := by exact_mod_cast hK₂
  have hT0 : ∀ k₁ k₂, 0 ≤ ∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖ :=
    fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  have hA0 : (0 : ℝ) ≤ (N : ℝ) / K₂ + 1 := by positivity
  have hB0 : (0 : ℝ) ≤ 2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1) := by positivity
  have hterm : ∀ k₁ ∈ s, ∀ k₂ ∈ t,
      innerF (fun k l => Rm Q τ k l N) lam l₃ K₃ k₁ k₂ ≤
        Real.log N * Real.sqrt ((N : ℝ) / K₂ + 1) *
          (Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) *
            Real.sqrt (∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖)) := by
    intro k₁ hk₁ k₂ hk₂
    have hk₁ := hs k₁ hk₁
    have hk₂ := ht k₂ hk₂
    refine le_trans (innerF_Rm_le Q τ lam l₃ K₃ N k₁ k₂ (by omega) (by omega)) ?_
    rw [← Real.sqrt_mul hB0]
    have hJ : ((N / k₂ + 1 : ℕ) : ℝ) ≤ (N : ℝ) / K₂ + 1 := by
      have h1 : ((N / k₂ : ℕ) : ℝ) ≤ (N : ℝ) / k₂ := Nat.cast_div_le
      have h2 : (N : ℝ) / k₂ ≤ N / K₂ :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg N) hK₂' (by exact_mod_cast hk₂)
      push_cast; linarith
    have hk1 : (N : ℝ) / k₁ ≤ N / K₁ :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg N) hK₁' (by exact_mod_cast hk₁)
    have hBT : 2 * Real.log N ^ 2 * ((N : ℝ) / k₁ + 1) *
        ∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖ ≤
        2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1) *
        ∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖ := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
        (hT0 _ _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hJ) hL)
      (Real.sqrt_le_sqrt hBT) (Real.sqrt_nonneg _) (mul_nonneg hL (Real.sqrt_nonneg _))
  have hcard : ((s ×ˢ t).card : ℝ) = (K₁ : ℝ) * K₂ := by
    rw [card_product, hcs, hct, Nat.cast_mul]
  have hCS : ∑ k₁ ∈ s, ∑ k₂ ∈ t,
      Real.sqrt (∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖) ≤
      Real.sqrt ((K₁ : ℝ) * K₂) * Real.sqrt (W) := by
    rw [← sum_product', show W = ∑ k₁ ∈ s, ∑ k₂ ∈ t, ∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖ from rfl, ← sum_product', ← hcard]
    have h := Real.sum_sqrt_mul_sqrt_le (s ×ˢ t)
      (f := fun _ => (1 : ℝ))
      (g := fun x => ∑ n ∈ nSet N x.1 x.2, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖)
      (fun _ => zero_le_one) (fun x => hT0 _ _)
    simp only [Real.sqrt_one, one_mul, sum_const, nsmul_eq_mul, mul_one] at h
    exact h
  have hprod : ((N : ℝ) / K₂ + 1) * (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) * ((K₁ : ℝ) * K₂) ≤
      8 * Real.log N ^ 2 * (N : ℝ) ^ 2 := by
    have e1 : ((N : ℝ) / K₂ + 1) * K₂ = N + K₂ := by field_simp
    have e2 : ((N : ℝ) / K₁ + 1) * K₁ = N + K₁ := by field_simp
    have hN1 : (K₁ : ℝ) ≤ N := by exact_mod_cast hK₁N
    have hN2 : (K₂ : ℝ) ≤ N := by exact_mod_cast hK₂N
    have hm : ((N : ℝ) + K₂) * (N + K₁) ≤ (2 * N) * (2 * N) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    calc ((N : ℝ) / K₂ + 1) * (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) * ((K₁ : ℝ) * K₂)
        = 2 * Real.log N ^ 2 * ((((N : ℝ) / K₂ + 1) * K₂) * (((N : ℝ) / K₁ + 1) * K₁)) := by ring
      _ = 2 * Real.log N ^ 2 * (((N : ℝ) + K₂) * (N + K₁)) := by rw [e1, e2]
      _ ≤ 2 * Real.log N ^ 2 * ((2 * N) * (2 * N)) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = 8 * Real.log N ^ 2 * (N : ℝ) ^ 2 := by ring
  have hsq : Real.sqrt ((N : ℝ) / K₂ + 1) * Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) *
      Real.sqrt ((K₁ : ℝ) * K₂) ≤ Real.sqrt 8 * Real.log N * N := by
    rw [← Real.sqrt_mul hA0, ← Real.sqrt_mul (mul_nonneg hA0 hB0)]
    calc _ ≤ Real.sqrt (8 * Real.log N ^ 2 * (N : ℝ) ^ 2) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt 8 * Real.log N * N := by
        rw [show 8 * Real.log N ^ 2 * (N : ℝ) ^ 2 = 8 * (Real.log N * N) ^ 2 by ring,
          Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
        ring
  have hW0 : 0 ≤ Real.sqrt (W) := Real.sqrt_nonneg _
  calc ∑ k₁ ∈ s, ∑ k₂ ∈ t, innerF (fun k l => Rm Q τ k l N) lam l₃ K₃ k₁ k₂
      ≤ ∑ k₁ ∈ s, ∑ k₂ ∈ t,
          Real.log N * Real.sqrt ((N : ℝ) / K₂ + 1) *
            (Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) *
              Real.sqrt (∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖)) :=
        sum_le_sum fun k₁ h₁ => sum_le_sum fun k₂ h₂ => hterm k₁ h₁ k₂ h₂
    _ = Real.log N * Real.sqrt ((N : ℝ) / K₂ + 1) *
          Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) *
          ∑ k₁ ∈ s, ∑ k₂ ∈ t,
            Real.sqrt (∑ n ∈ nSet N k₁ k₂, ‖Kc (-1 / τ) Q τ lam l₃ K₃ N n‖) := by
        simp only [mul_sum, mul_assoc]
    _ ≤ Real.log N * Real.sqrt ((N : ℝ) / K₂ + 1) *
          Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) *
          (Real.sqrt ((K₁ : ℝ) * K₂) * Real.sqrt (W)) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = Real.log N * (Real.sqrt ((N : ℝ) / K₂ + 1) *
          Real.sqrt (2 * Real.log N ^ 2 * ((N : ℝ) / K₁ + 1)) * Real.sqrt ((K₁ : ℝ) * K₂)) *
          Real.sqrt (W) := by ring
    _ ≤ Real.log N * (Real.sqrt 8 * Real.log N * N) *
          Real.sqrt (W) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hL) hW0
    _ = Real.sqrt 8 * Real.log N ^ 2 * N * Real.sqrt (W) := by
        ring


/-- The singleton has scale one. Later scales are powers of two. -/
def scale : ℕ → ℕ
  | 0 => 1
  | j + 1 => 2 ^ j

theorem scale_pos (j : ℕ) : 1 ≤ scale j := by
  cases j with
  | zero => rfl
  | succ j => exact Nat.one_le_pow _ _ (by norm_num)

theorem block_card (j : ℕ) : (block j).card = scale j := by
  cases j with
  | zero => simp [block, scale]
  | succ j => simp [block, scale, Nat.card_Ioc]; omega

theorem scale_le_mem (j k : ℕ) (hk : k ∈ block j) : scale j ≤ k := by
  cases j with
  | zero =>
    simp only [block, mem_singleton] at hk
    simp [scale, hk]
  | succ j => exact (mem_Ioc.mp hk).1.le

theorem scale_le_N (H N j : ℕ) (hH : H ≤ N) (hN : 1 ≤ N)
    (hj : j ∈ range (Nat.clog 2 H + 1)) : scale j ≤ N := by
  cases j with
  | zero => exact hN
  | succ j =>
    have hj' : j < Nat.clog 2 H := by
      simp only [mem_range] at hj
      omega
    exact (Nat.pow_lt_of_lt_clog hj').le.trans hH

noncomputable def W (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N i j : ℕ) : ℝ :=
  ∑ x ∈ block i, ∑ y ∈ block j, ∑ n ∈ nSet N x y, ‖Kc a Q τ lam l₃ K₃ N n‖

noncomputable def W0 (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N i j : ℕ) : ℝ :=
  ∑ x ∈ block i, ∑ y ∈ block j,
    ∑ n ∈ (nSet N x y).filter (fun n => n = 0), ‖Kc a Q τ lam l₃ K₃ N n‖

noncomputable def Ws (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N i j : ℕ) : ℝ :=
  ∑ x ∈ block i, ∑ y ∈ block j,
    ∑ n ∈ (nSet N x y).filter (fun n => n ≠ 0), ‖Kc a Q τ lam l₃ K₃ N n‖

theorem W_split (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N i j : ℕ) :
    W a Q τ lam l₃ K₃ N i j = W0 a Q τ lam l₃ K₃ N i j + Ws a Q τ lam l₃ K₃ N i j := by
  simp only [W, W0, Ws, ← sum_add_distrib, sum_filter_add_sum_filter_not]

/-- Display 17 for all blocks, including both mixed singleton cases. -/
theorem display17_blocks (Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N i j : ℕ)
    (hi : scale i ≤ N) (hj : scale j ≤ N) (hL : 1 ≤ Real.log N) :
    V Q τ lam l₃ K₃ N i j ≤ Real.sqrt 8 * Real.log N ^ 3 * N *
      Real.sqrt (W0 (-1 / τ) Q τ lam l₃ K₃ N i j + Ws (-1 / τ) Q τ lam l₃ K₃ N i j) := by
  rw [← W_split]
  have h := display17_sets Q τ lam l₃ K₃ N (scale i) (scale j) (block i) (block j)
    (scale_pos i) hi (scale_pos j) hj (block_card i) (block_card j)
    (scale_le_mem i) (scale_le_mem j)
  refine h.trans ?_
  have hp : Real.log N ^ 2 ≤ Real.log N ^ 3 := pow_le_pow_right₀ hL (by norm_num)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)

/-- The E2 bound with display 10 proved. Displays 19 and 20 remain inputs for all blocks. -/
theorem E2_bound_without_display10 (lam : ℕ → ℝ) (l₃ N : ℕ) (A c₁ c₂ : ℝ)
    (hA : 10 ^ 4 ≤ A) (hL : 1 ≤ Real.log N) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h19 : ∀ i ∈ range (Nat.clog 2 (cutoff (10 ^ 4 * A) N) + 1),
      ∀ j ∈ range (Nat.clog 2 (cutoff (10 ^ 4 * A) N) + 1),
      W0 (-1 / τof A N) (Qof A N) (τof A N) lam l₃ (cutoff3 (10 ^ 4 * A) N) N i j ≤
        c₁ * Real.log N ^ (20 - 2 * (10 ^ 4 * A)) * (N : ℝ) ^ 2)
    (h20 : ∀ i ∈ range (Nat.clog 2 (cutoff (10 ^ 4 * A) N) + 1),
      ∀ j ∈ range (Nat.clog 2 (cutoff (10 ^ 4 * A) N) + 1),
      Ws (-1 / τof A N) (Qof A N) (τof A N) lam l₃ (cutoff3 (10 ^ 4 * A) N) N i j ≤
        c₂ * (N : ℝ) ^ 2 * Real.log N ^ (400 - 4 * A)) :
    E2 lam l₃ A N ≤ dyadicConstant * Real.sqrt 8 * (Real.sqrt c₁ + Real.sqrt c₂) *
      (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  obtain ⟨i, hi, j, hj, h10⟩ := E2_display10 lam l₃ N A (by linarith) hL
  have hN : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    norm_num [this] at hL
  have hH := cutoff_le (10 ^ 4 * A) N (by positivity) hL
  have h17 := display17_blocks (Qof A N) (τof A N) lam l₃ (cutoff3 (10 ^ 4 * A) N) N i j
    (scale_le_N _ _ _ hH hN hi) (scale_le_N _ _ _ hH hN hj) hL
  exact E2_bookkeeping hA rfl hL (Nat.cast_nonneg N) hc₁ hc₂ (Real.sqrt_nonneg _) (sq_nonneg _)
    (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _)
    (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _)
    (h19 i hi j hj) (h20 i hi j hj) h17 h10

end LeanLab.Tolev2009.BlockEstimates
