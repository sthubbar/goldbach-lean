module

public import LeanLab.PNTPort.Vinogradov.TypeII
public import LeanLab.PNTPort.BV.TypeIIAux

/-!
# Vinogradov's minor arc bound, the Type II sum `T₄`

Lab proof, unit U-5250. AI wrote this file. Known mathematics, no cited input.

With `L = 1 + log N`, `L_q = 1 + log q`, `c₀ = 2(log 4 + 4)`, for `(a, q) = 1`, `q ≥ 1`,
`|α - a/q| ≤ 1/q²`, `u, v ≥ 1`:
* `typeII_block_bound`: every dyadic block `M ≥ u` of `T₄` has
  `‖B_M‖² ≤ c₀ N L⁴ (9N/v + 8N/q + 2(N/u) L_q + 2q L_q)`;
* `norm_T4_le`: `‖T₄‖ ≤ (log₂ N + 1) √(c₀ N L⁴ (9N/v + 8N/q + 2(N/u) L_q + 2q L_q))`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real ArithmeticFunction
open LeanLab.PNTPort.LargeSieve
open LeanLab.PNTPort.BV (gV abs_gV_le sum_vonMangoldt_sq_block sum_Ioc_dyadic)

/-- The Type II coefficient `b_k = g_v(k)` for `k > v`, else `0`. -/
noncomputable def bII (v k : ℕ) : ℝ := if v < k then gV v k else 0

/-- The dyadic block of `T₄`. -/
noncomputable def blockII (N v M : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ Ioc M (M + M), ∑ k ∈ Icc 1 (N / m), ((Λ m * bII v k : ℝ) : ℂ) * e ((m * k : ℕ) * α)

lemma sum_bII_sq_le (v K : ℕ) :
    ∑ k ∈ Icc 1 K, bII v k ^ 2 ≤ K * (1 + Real.log K) ^ 3 := by
  calc ∑ k ∈ Icc 1 K, bII v k ^ 2 ≤ ∑ k ∈ Icc 1 K, (k.divisors.card : ℝ) ^ 2 := by
        refine sum_le_sum fun k _ => ?_
        unfold bII; split_ifs
        · rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_gV_le v k) 2
        · simp
    _ ≤ K * HeathBrown1985.Hn K ^ 3 := HeathBrown1985.sum_sq_divisors_le K
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg K)
        exact pow_le_pow_left₀ (HeathBrown1985.Hn_nonneg _) (HeathBrown1985.Hn_le _) 3

lemma sum_bII_sq_eq_zero {v K : ℕ} (h : K ≤ v) : ∑ k ∈ Icc 1 K, bII v k ^ 2 = 0 := by
  refine sum_eq_zero fun k hk => ?_
  have := (mem_Icc.1 hk).2
  unfold bII; rw [if_neg (by omega)]; simp

/-- The uniform bound for one dyadic block. -/
theorem typeII_block_bound {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {α : ℝ}
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (N : ℕ) {u v M : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (huM : u ≤ M) :
    ‖blockII N v M α‖ ^ 2 ≤ 2 * (Real.log 4 + 4) * N * (1 + Real.log N) ^ 4 *
      (9 * ((N : ℝ) / v) + 8 * ((N : ℝ) / q) + 2 * ((N : ℝ) / u) * (1 + Real.log q) +
        2 * q * (1 + Real.log q)) := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hM1 : 1 ≤ M := le_trans hu huM
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hur : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hvr : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hlq := Real.log_natCast_nonneg q
  have hlN := Real.log_natCast_nonneg N
  set K := N / M with hK
  set Lq := 1 + Real.log q with hLq
  set W : ℝ := M + 2 * (((K : ℝ) / q + 1) * (4 * M + q * Lq)) with hW
  have hWb : ∀ k₁ ∈ Icc 1 (N / M), ∑ k₂ ∈ Icc 1 (N / M), G M (α * ((k₁ : ℝ) - k₂)) ≤ W := by
    intro k₁ hk₁
    refine (sum_G_diff_le (Nat.cast_nonneg M) α hk₁).trans ?_
    have h := sum_G_le hq hcop hα (N / M) (Y := (M : ℝ)) (Nat.cast_nonneg M)
    have h' : ∑ ℓ ∈ Icc 1 (N / M), G M (α * ℓ) = ∑ m ∈ Icc 1 (N / M), G M (α * m) := rfl
    rw [hW]; linarith
  have hbl := bilinear_block (fun m => Λ m) (bII v) N M α hWb
  have hRHS0 : 0 ≤ 2 * (Real.log 4 + 4) * N * (1 + Real.log N) ^ 4 *
      (9 * ((N : ℝ) / v) + 8 * ((N : ℝ) / q) + 2 * ((N : ℝ) / u) * (1 + Real.log q) +
        2 * q * (1 + Real.log q)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  unfold blockII
  refine hbl.trans ?_
  rcases Nat.lt_or_ge v K with hvK | hvK
  · -- the main case
    have hK1 : 1 ≤ K := by omega
    have hKM : K * M ≤ N := Nat.div_mul_le_self N M
    have hMN : M ≤ N := by nlinarith
    have hKN : K ≤ N := Nat.div_le_self N M
    have hKMr : (K : ℝ) * M ≤ N := by exact_mod_cast hKM
    have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hNr : (M : ℝ) ≤ N := by exact_mod_cast hMN
    set L := 1 + Real.log N with hL
    have hL1 : 1 ≤ L := by linarith
    -- the Λ² sum
    have hA := sum_vonMangoldt_sq_block M
    have hlog2M : Real.log (2 * M) ≤ L := by
      rw [Real.log_mul (by norm_num) (by positivity)]
      have := Real.log_le_log (by positivity) hNr
      have := Real.log_two_lt_d9; linarith
    have hA' : ∑ m ∈ Ioc M (M + M), Λ m ^ 2 ≤ 2 * (Real.log 4 + 4) * M * L := by
      have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      refine hA.trans ?_
      have : Real.log (2 * M) * ((Real.log 4 + 4) * (2 * M)) =
          2 * (Real.log 4 + 4) * M * Real.log (2 * M) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hlog2M (by positivity)
    -- the b² sum
    have hB := sum_bII_sq_le v K
    have hlogK : 1 + Real.log K ≤ L := by
      have := Real.log_le_log (by linarith) (show (K : ℝ) ≤ N by exact_mod_cast hKN)
      linarith
    have hB' : ∑ k ∈ Icc 1 K, bII v k ^ 2 ≤ K * L ^ 3 := by
      refine hB.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg K))
      exact pow_le_pow_left₀ (by have := Real.log_natCast_nonneg K; linarith) hlogK 3
    -- the W bound
    have hMv : (M : ℝ) ≤ N / v := by
      rw [le_div_iff₀ (by linarith)]
      have h0 : (v : ℝ) + 1 ≤ K := by exact_mod_cast hvK
      have h1 : (M : ℝ) * (v + 1) ≤ M * K := mul_le_mul_of_nonneg_left h0 (by positivity)
      have h2 : (M : ℝ) * K = K * M := mul_comm _ _
      have h3 : (M : ℝ) * (v + 1) = M * v + M := by ring
      linarith
    have hKq : (K : ℝ) / q * (4 * M) ≤ 4 * (N / q) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hqpos]
      have : 4 * ((N : ℝ) / q) * q = 4 * N := by field_simp
      rw [this]
      have h5 : (K : ℝ) * (4 * M) = 4 * (K * M) := by ring
      rw [h5]; linarith
    have hKu : (K : ℝ) ≤ N / u := by
      refine Nat.cast_div_le.trans ?_
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by linarith)
        (by exact_mod_cast huM)
    have hWle : W ≤ 9 * ((N : ℝ) / v) + 8 * ((N : ℝ) / q) + 2 * ((N : ℝ) / u) * Lq +
        2 * q * Lq := by
      have hKLq : (K : ℝ) / q * (q * Lq) = K * Lq := by field_simp
      have hLq0 : 0 ≤ Lq := by linarith
      have : (K : ℝ) * Lq ≤ (N / u) * Lq := mul_le_mul_of_nonneg_right hKu hLq0
      have hWexp : W = 9 * M + 2 * ((K : ℝ) / q * (4 * M)) + 2 * ((K : ℝ) / q * (q * Lq)) +
          2 * q * Lq := by rw [hW]; ring
      rw [hWexp, hKLq]
      linarith
    have hLq0 : 0 ≤ Lq := by linarith
    have hW0 : 0 ≤ W := by
      rw [hW]
      have : 0 ≤ ((K : ℝ) / q + 1) * (4 * M + q * Lq) := by positivity
      linarith
    have hc0 : 0 ≤ 2 * (Real.log 4 + 4) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
    have hAnn : 0 ≤ ∑ m ∈ Ioc M (M + M), Λ m ^ 2 := sum_nonneg fun m _ => sq_nonneg _
    have hBnn : 0 ≤ ∑ k ∈ Icc 1 K, bII v k ^ 2 := sum_nonneg fun k _ => sq_nonneg _
    have hL4 : 0 ≤ L ^ 4 := by positivity
    calc (∑ m ∈ Ioc M (M + M), Λ m ^ 2) * (∑ k ∈ Icc 1 K, bII v k ^ 2) * W
        ≤ (2 * (Real.log 4 + 4) * M * L) * (K * L ^ 3) * W :=
          mul_le_mul_of_nonneg_right (mul_le_mul hA' hB' hBnn (by positivity)) hW0
      _ = 2 * (Real.log 4 + 4) * (K * M) * L ^ 4 * W := by ring
      _ ≤ 2 * (Real.log 4 + 4) * N * L ^ 4 * W :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hKMr hc0) hL4) hW0
      _ ≤ _ := mul_le_mul_of_nonneg_left hWle (by positivity)
  · rw [sum_bII_sq_eq_zero hvK, mul_zero, zero_mul]
    exact hRHS0

/-- `T₄` as a sum of dyadic blocks. -/
lemma T4_eq_blocks (N u v : ℕ) (α : ℝ) {J : ℕ} (hJ : N ≤ u * 2 ^ J) :
    T4 N u v α = ∑ j ∈ range J, blockII N v (u * 2 ^ j) α := by
  set f : ℕ → ℂ := fun m => ∑ k ∈ Icc 1 (N / m),
    ((Λ m * bII v k : ℝ) : ℂ) * e ((m * k : ℕ) * α) with hf
  have h1 : T4 N u v α = ∑ m ∈ Icc 1 N, if u < m then f m else 0 := by
    unfold T4
    refine sum_congr rfl fun m _ => ?_
    split_ifs with hm
    · refine sum_congr rfl fun k _ => ?_
      unfold bII
      by_cases hk : v < k
      · rw [if_pos ⟨hm, hk⟩, if_pos hk]
      · rw [if_neg (fun h => hk h.2), if_neg hk, mul_zero]
    · refine sum_eq_zero fun k _ => ?_
      rw [if_neg (fun h => hm h.1)]; simp
  have h2 : (∑ m ∈ Icc 1 N, if u < m then f m else 0) = ∑ m ∈ Ioc u (u * 2 ^ J), f m := by
    rw [← sum_filter]
    apply sum_subset
    · intro m hm; simp only [mem_filter, mem_Icc, mem_Ioc] at hm ⊢; omega
    · intro m hm hm'
      simp only [mem_filter, mem_Icc, mem_Ioc] at hm hm'
      have hNm : N < m := by omega
      rw [hf]; simp only
      rw [Nat.div_eq_of_lt hNm]; simp
  rw [h1, h2, sum_Ioc_dyadic]
  rfl

lemma natLog_le (N : ℕ) : (Nat.log 2 N : ℝ) ≤ 2 * Real.log N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have hp := Nat.pow_log_le_self 2 h.ne'
    have hpr : ((2 : ℝ) ^ Nat.log 2 N) ≤ N := by exact_mod_cast hp
    have := Real.log_le_log (by positivity) hpr
    rw [Real.log_pow] at this
    have h2 := Real.log_two_gt_d9
    have hl0 : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
    nlinarith

/-- The Type II bound. -/
theorem norm_T4_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {α : ℝ}
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (N : ℕ) {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    ‖T4 N u v α‖ ≤ (2 * Real.log N + 1) *
      Real.sqrt (2 * (Real.log 4 + 4) * N * (1 + Real.log N) ^ 4 *
      (9 * ((N : ℝ) / v) + 8 * ((N : ℝ) / q) + 2 * ((N : ℝ) / u) * (1 + Real.log q) +
        2 * q * (1 + Real.log q))) := by
  set J := Nat.log 2 N + 1 with hJ
  have hJN : N ≤ u * 2 ^ J := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
    have h2 : 2 ^ J ≤ u * 2 ^ J := Nat.le_mul_of_pos_left _ hu
    have h3 : 2 ^ J = 2 ^ (Nat.log 2 N + 1) := by rw [hJ]
    omega
  rw [T4_eq_blocks N u v α hJN]
  set R := Real.sqrt (2 * (Real.log 4 + 4) * N * (1 + Real.log N) ^ 4 *
      (9 * ((N : ℝ) / v) + 8 * ((N : ℝ) / q) + 2 * ((N : ℝ) / u) * (1 + Real.log q) +
        2 * q * (1 + Real.log q))) with hR
  have hblk : ∀ j ∈ range J, ‖blockII N v (u * 2 ^ j) α‖ ≤ R := by
    intro j _
    rw [hR]
    apply Real.le_sqrt_of_sq_le
    exact typeII_block_bound hq hcop hα N hu hv (Nat.le_mul_of_pos_right _ (by positivity))
  refine (norm_sum_le _ _).trans ((sum_le_sum hblk).trans ?_)
  rw [sum_const, card_range, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  rw [hJ]; push_cast
  linarith [natLog_le N]

end LeanLab.PNTPort.Vinogradov

