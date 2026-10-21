module

public import LeanLab.PNTPort.Vinogradov.Decomp

/-!
# Vinogradov's minor arc bound, the sums `T₁`, `T₂`, `T₃`

Lab proof, unit U-5250. AI wrote this file. Known mathematics, no cited input.
For `(a, q) = 1`, `q ≥ 1`, `|α - a/q| ≤ 1/q²`, `u, v ≥ 1`:
* `norm_T1_le`: `‖T₁‖ ≤ (log 4 + 4) u`;
* `norm_T2_le`: `‖T₂‖ ≤ 12 log N (N/q + uv + q)(1 + log q + log(uv))`;
* `norm_T3_le`: `‖T₃‖ ≤ 24 log N (N/q + v + q)(1 + log q + log v)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.LargeSieve
open LeanLab.PNTPort.BV (gV sum_Icc_one_eq_range abel_range log_nat_mono)

lemma norm_sum_e_Icc_le (K t : ℕ) (α : ℝ) :
    ‖∑ r ∈ Icc 1 K, e ((t * r : ℕ) * α)‖ ≤ G K (α * t) := by
  have h := norm_sum_Ioc_e_le 0 K (α * t)
  rw [zero_add] at h
  have hI : Ioc 0 K = Icc 1 K := by ext r; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  refine sum_congr rfl fun r _ => ?_
  congr 1; push_cast; ring

/-- Abel summation with partial sums bounded up to `Y`. -/
lemma norm_sum_log_le' (c : ℕ → ℂ) (B : ℝ) (Y : ℕ)
    (hB : ∀ k ≤ Y, ‖∑ h ∈ Icc 1 k, c h‖ ≤ B) :
    ‖∑ h ∈ Icc 1 Y, (Real.log h : ℂ) * c h‖ ≤ 2 * Real.log Y * B := by
  have hB' : ∀ k ≤ Y, ‖∑ j ∈ range k, c (j + 1)‖ ≤ B := fun k hk => by
    rw [← sum_Icc_one_eq_range c]; exact hB k hk
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (Nat.zero_le _))
  have hlog : 0 ≤ Real.log (Y : ℝ) := Real.log_natCast_nonneg Y
  rw [sum_Icc_one_eq_range (fun h => (Real.log h : ℂ) * c h)]
  have e' := abel_range (fun h => Real.log (h : ℝ)) c Y
  beta_reduce at e'
  rw [e']
  calc _ ≤ ‖(Real.log (Y : ℝ) : ℂ) * ∑ j ∈ range Y, c (j + 1)‖ +
        ‖∑ h ∈ range Y, ((Real.log ((h + 1 : ℕ) : ℝ) - Real.log (h : ℝ) : ℝ) : ℂ) *
          ∑ j ∈ range h, c (j + 1)‖ := norm_sub_le _ _
    _ ≤ Real.log Y * B + ∑ h ∈ range Y,
          (Real.log ((h + 1 : ℕ) : ℝ) - Real.log (h : ℝ)) * B := by
        refine add_le_add ?_ ?_
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog]
          exact mul_le_mul_of_nonneg_left (hB' Y le_rfl) hlog
        · refine (norm_sum_le _ _).trans (sum_le_sum fun h hh => ?_)
          have hm := sub_nonneg.2 (log_nat_mono h)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm]
          exact mul_le_mul_of_nonneg_left (hB' h (mem_range.1 hh).le) hm
    _ = 2 * Real.log Y * B := by
        rw [← sum_mul, sum_range_sub (fun h : ℕ => Real.log (h : ℝ))]
        simp only [Nat.cast_zero, Real.log_zero, sub_zero]
        ring

lemma G_floor_le (N t : ℕ) (θ : ℝ) : G ((N / t : ℕ) : ℝ) θ ≤ G ((N : ℝ) / t) θ :=
  G_mono Nat.cast_div_le θ

lemma log_le_of_le {a N : ℕ} (h : a ≤ N) : Real.log a ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · rw [h0]; simpa using Real.log_natCast_nonneg N
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast h)

theorem norm_T1_le (N u : ℕ) (α : ℝ) : ‖T1 N u α‖ ≤ (Real.log 4 + 4) * u := by
  unfold T1
  refine (norm_sum_le _ _).trans ?_
  have hψ := Chebyshev.psi_le_const_mul_self (x := (u : ℝ)) (by positivity)
  rw [Chebyshev.psi, Nat.floor_natCast] at hψ
  calc ∑ n ∈ Icc 1 N, ‖((if n ≤ u then Λ n else 0 : ℝ) : ℂ) * e (n * α)‖
        ≤ ∑ n ∈ Icc 1 N, (if n ≤ u then Λ n else 0) := by
        refine sum_le_sum fun n _ => ?_
        rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
        split_ifs
        · exact le_of_eq (abs_of_nonneg vonMangoldt_nonneg)
        · simp
    _ ≤ ∑ n ∈ Ioc 0 u, Λ n := by
        rw [← sum_filter]
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn; simp only [mem_filter, mem_Icc, mem_Ioc] at hn ⊢; omega
        · intro _ _ _; exact vonMangoldt_nonneg
    _ ≤ _ := by linarith

lemma abs_cT2_le (u v t : ℕ) : |cT2 u v t| ≤ Real.log t := by
  unfold cT2
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ y ∈ t.divisorsAntidiagonal,
        |if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0|
        ≤ ∑ y ∈ t.divisorsAntidiagonal, Λ y.1 := by
        refine sum_le_sum fun y _ => ?_
        split_ifs
        · rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
          have : |(μ y.2 : ℝ)| ≤ 1 := by
            have := abs_moebius_le_one (n := y.2)
            exact_mod_cast this
          have := vonMangoldt_nonneg (n := y.1)
          nlinarith [abs_nonneg (μ y.2 : ℝ)]
        · simp [vonMangoldt_nonneg]
    _ = Real.log t := by
        rw [Nat.sum_divisorsAntidiagonal (fun a _ => Λ a), vonMangoldt_sum]

lemma cT2_eq_zero {u v t : ℕ} (ht : u * v < t) : cT2 u v t = 0 := by
  unfold cT2
  refine sum_eq_zero fun y hy => ?_
  have h := (Nat.mem_divisorsAntidiagonal.1 hy).1
  rw [if_neg]
  rintro ⟨h1, h2⟩
  have := Nat.mul_le_mul h1 h2
  omega

theorem norm_T2_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {α : ℝ}
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (N u v : ℕ) :
    ‖T2 N u v α‖ ≤ Real.log N * (12 * ((N : ℝ) / q + (u * v : ℕ) + q) *
      (1 + Real.log q + Real.log (u * v : ℕ))) := by
  unfold T2
  have hlN := Real.log_natCast_nonneg N
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ t ∈ Icc 1 N, ‖∑ r ∈ Icc 1 (N / t), (cT2 u v t : ℂ) * e ((t * r : ℕ) * α)‖ ≤
      if t ≤ u * v then Real.log N * G ((N : ℝ) / t) (α * t) else 0 := by
    intro t ht
    have ht' := mem_Icc.1 ht
    rw [← mul_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with h
    · have h1 := (abs_cT2_le u v t).trans (log_le_of_le ht'.2)
      have h2 := (norm_sum_e_Icc_le (N / t) t α).trans (G_floor_le N t _)
      exact mul_le_mul h1 h2 (norm_nonneg _) hlN
    · rw [cT2_eq_zero (by omega), abs_zero, zero_mul]
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter]
  calc ∑ t ∈ (Icc 1 N).filter (fun t => t ≤ u * v), Real.log N * G ((N : ℝ) / t) (α * t)
        ≤ ∑ t ∈ Icc 1 (u * v), Real.log N * G ((N : ℝ) / t) (α * t) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro t ht; simp only [mem_filter, mem_Icc] at ht ⊢; omega
        · intro t _ _; exact mul_nonneg hlN (G_nonneg (by positivity) _)
    _ = Real.log N * ∑ t ∈ Icc 1 (u * v), G ((N : ℝ) / t) (t * α) := by
        rw [mul_sum]; simp only [mul_comm α]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hlN
        have := sum_G_div_le hq hcop hα (u * v) (X := (N : ℝ)) (Nat.cast_nonneg N)
        simpa only [mul_comm α] using this

theorem norm_T3_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ)) {α : ℝ}
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (N v : ℕ) :
    ‖T3 N v α‖ ≤ 2 * Real.log N * (12 * ((N : ℝ) / q + v + q) *
      (1 + Real.log q + Real.log v)) := by
  unfold T3
  have hlN := Real.log_natCast_nonneg N
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ d ∈ Icc 1 N, ‖∑ h ∈ Icc 1 (N / d),
      ((if d ≤ v then (μ d : ℝ) * Real.log h else 0 : ℝ) : ℂ) * e ((d * h : ℕ) * α)‖ ≤
      if d ≤ v then 2 * Real.log N * G ((N : ℝ) / d) (α * d) else 0 := by
    intro d hd
    have hd' := mem_Icc.1 hd
    split_ifs with h
    · have e1 : ∑ h ∈ Icc 1 (N / d), (((μ d : ℝ) * Real.log h : ℝ) : ℂ) * e ((d * h : ℕ) * α) =
          (μ d : ℂ) * ∑ h ∈ Icc 1 (N / d), (Real.log h : ℂ) * e ((d * h : ℕ) * α) := by
        rw [mul_sum]; refine sum_congr rfl fun h _ => ?_; push_cast; ring
      rw [e1, norm_mul]
      have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
      have hB : ∀ k ≤ N / d, ‖∑ h ∈ Icc 1 k, e ((d * h : ℕ) * α)‖ ≤ G ((N : ℝ) / d) (α * d) := by
        intro k hk
        refine (norm_sum_e_Icc_le k d α).trans ((G_mono ?_ _))
        exact (Nat.cast_le.2 hk).trans Nat.cast_div_le
      have h2 := norm_sum_log_le' (fun h => e ((d * h : ℕ) * α)) _ (N / d) hB
      have h3 : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N := log_le_of_le (Nat.div_le_self N d)
      have hG := G_nonneg (Y := (N : ℝ) / d) (by positivity) (α * d)
      calc ‖(μ d : ℂ)‖ * ‖∑ h ∈ Icc 1 (N / d), (Real.log h : ℂ) * e ((d * h : ℕ) * α)‖
          ≤ 1 * (2 * Real.log ((N / d : ℕ) : ℝ) * G ((N : ℝ) / d) (α * d)) :=
            mul_le_mul hμ h2 (norm_nonneg _) zero_le_one
        _ ≤ 2 * Real.log N * G ((N : ℝ) / d) (α * d) := by nlinarith
    · simp
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter]
  calc ∑ d ∈ (Icc 1 N).filter (fun d => d ≤ v), 2 * Real.log N * G ((N : ℝ) / d) (α * d)
        ≤ ∑ d ∈ Icc 1 v, 2 * Real.log N * G ((N : ℝ) / d) (α * d) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro t ht; simp only [mem_filter, mem_Icc] at ht ⊢; omega
        · intro t _ _; exact mul_nonneg (by positivity) (G_nonneg (by positivity) _)
    _ = 2 * Real.log N * ∑ d ∈ Icc 1 v, G ((N : ℝ) / d) (α * d) := by rw [mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_G_div_le hq hcop hα v (X := (N : ℝ)) (Nat.cast_nonneg N)

end LeanLab.PNTPort.Vinogradov

