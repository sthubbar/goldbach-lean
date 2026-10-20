module

public import LeanLab.GoldbachAverage.Sums
public import LeanLab.GoldbachAverage.PsiFromAvg
public import LeanLab.PNTPort.ZetaZeros.VonKoch

/-!
RH implies AvgRH, the forward half of Granville's equivalence `granville_equiv`, P0098 Theorem 1A
as quoted by P0060 Theorem 2, now PROVED from RH alone through the lab's von Koch theorem
`LeanLab.PNTPort.ZetaZeros.vonKoch_RH`, |ψ(X) - X| ≤ C √X log³ X. Elementary from there:
`∑_{n ≤ N} G(n) = ∑_{a ≤ N} Λ(a) ψ(N - a)`, `∑_{a ≤ N} Λ(a)(N - a) = ∑_{m < N} ψ(m)`, so
`∑_{n ≤ N} G(n) = N²/2 + O(N^{3/2} log³ N)`, which gives `AvgRH` for every `ε > 0`.
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T0715Z-cloud19, unit U-5268.
Binary Goldbach is OPEN; AvgRH is an average over n.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage

/-- `∑_{a ≤ N} Λ(a)(N - a) = ∑_{m < N} ψ(m)`. -/
theorem sum_lambda_mul_sub (N : ℕ) :
    ∑ a ∈ range (N + 1), Λ a * ((N - a : ℕ) : ℝ) = ∑ m ∈ range N, psiN m := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep : ∀ a ∈ range (N + 1), Λ a * ((N + 1 - a : ℕ) : ℝ)
        = Λ a * ((N - a : ℕ) : ℝ) + Λ a := by
      intro a ha
      rw [mem_range] at ha
      have : N + 1 - a = (N - a) + 1 := by omega
      rw [this]; push_cast; ring
    rw [sum_range_succ (fun a => Λ a * ((N + 1 - a : ℕ) : ℝ)) (N + 1), Nat.sub_self,
      Nat.cast_zero, mul_zero, add_zero, sum_congr rfl hstep, sum_add_distrib, ih,
      sum_range_succ (fun a => Λ a) N]
    rw [sum_range_succ (fun m => psiN m) N, psiN, sum_range_succ]

/-- A uniform bound `|ψ(m) - m| ≤ C √N log³ N + D` for `m ≤ N`, `N ≥ 1`, under RH. -/
theorem psi_err_uniform (hRH : RiemannHypothesis) : ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
    ∀ N m : ℕ, 1 ≤ N → m ≤ N →
      |psiN m - m| ≤ C * √(N : ℝ) * Real.log N ^ 3 + D := by
  obtain ⟨C, X₀, hC, hK⟩ := LeanLab.PNTPort.ZetaZeros.vonKoch_RH hRH
  set M0 : ℕ := ⌈max X₀ 1⌉₊ with hM0
  refine ⟨C, psiN M0 + M0, hC, by
    have : 0 ≤ psiN M0 := sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    positivity, fun N m hN hm => ?_⟩
  have hD0 : 0 ≤ C * √(N : ℝ) * Real.log N ^ 3 := by
    have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    positivity
  rcases le_or_gt (max X₀ 1) (m : ℝ) with h | h
  · -- large `m`, von Koch
    have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_right _ _) h
    have hb := hK m (le_trans (le_max_left _ _) h)
    rw [← psiN_eq] at hb
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast hm
    have hl : Real.log m ≤ Real.log N := Real.log_le_log (by linarith) hmN
    have hl0 : 0 ≤ Real.log m := Real.log_nonneg hm1
    have hs : √(m : ℝ) ≤ √(N : ℝ) := Real.sqrt_le_sqrt hmN
    have : C * √(m : ℝ) * Real.log m ^ 3 ≤ C * √(N : ℝ) * Real.log N ^ 3 := by gcongr
    have hpos : 0 ≤ psiN M0 + M0 := by
      have : 0 ≤ psiN M0 := sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
      positivity
    linarith
  · -- small `m`, a constant
    have hmM : m ≤ M0 := by
      have : (m : ℝ) ≤ M0 := le_trans h.le (Nat.le_ceil _)
      exact_mod_cast this
    have h1 : psiN m ≤ psiN M0 := psiN_mono hmM
    have h2 : 0 ≤ psiN m := sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    have h3 : (m : ℝ) ≤ M0 := by exact_mod_cast hmM
    have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [abs_le]; constructor <;> linarith

/-- **Under RH, `∑_{n ≤ N} G(n) = N²/2 + O(N^{3/2} log³ N)`.** -/
theorem sum_G_RH (hRH : RiemannHypothesis) : ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
    ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ range (N + 1), G n - (N : ℝ) ^ 2 / 2| ≤
        (N : ℝ) * (10 * (C * √(N : ℝ) * Real.log N ^ 3 + D) + 1) := by
  obtain ⟨C, D, hC, hD, hB⟩ := psi_err_uniform hRH
  refine ⟨C, D, hC, hD, fun N hN => ?_⟩
  set B := C * √(N : ℝ) * Real.log N ^ 3 + D with hBdef
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    rw [hBdef]; positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- step 1: replace ψ(N - a) by N - a
  have h1 : |∑ n ∈ range (N + 1), G n - ∑ a ∈ range (N + 1), Λ a * ((N - a : ℕ) : ℝ)| ≤
      psiN N * B := by
    rw [sum_G, ← sum_sub_distrib]
    calc |∑ a ∈ range (N + 1), (Λ a * psiN (N - a) - Λ a * ((N - a : ℕ) : ℝ))|
        ≤ ∑ a ∈ range (N + 1), |Λ a * psiN (N - a) - Λ a * ((N - a : ℕ) : ℝ)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ range (N + 1), Λ a * B := by
          apply sum_le_sum
          intro a ha
          rw [← mul_sub, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact mul_le_mul_of_nonneg_left (hB N (N - a) hN (Nat.sub_le N a))
            ArithmeticFunction.vonMangoldt_nonneg
      _ = psiN N * B := by rw [← sum_mul, psiN]
  -- step 2: ∑_{m < N} ψ(m) against ∑_{m < N} m
  have h2 : |∑ m ∈ range N, psiN m - ∑ m ∈ range N, (m : ℝ)| ≤ N * B := by
    rw [← sum_sub_distrib]
    calc |∑ m ∈ range N, (psiN m - (m : ℝ))| ≤ ∑ m ∈ range N, |psiN m - (m : ℝ)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ range N, B := by
          apply sum_le_sum
          intro m hm
          rw [mem_range] at hm
          exact hB N m hN hm.le
      _ = N * B := by simp
  have h3 : ∑ m ∈ range N, (m : ℝ) = (N : ℝ) * (N - 1) / 2 := by
    have := Finset.sum_range_id_mul_two N
    have h' : ((∑ m ∈ range N, m : ℕ) : ℝ) * 2 = (N : ℝ) * ((N : ℝ) - 1) := by
      have e : ((N * (N - 1) : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) := by
        rcases Nat.eq_zero_or_pos N with h0 | hpos
        · simp [h0]
        · push_cast [Nat.cast_sub (by omega : 1 ≤ N)]; ring
      rw [← e]; exact_mod_cast this
    push_cast at h'
    linarith
  -- step 3: ψ(N) ≤ 6N
  have h4 : psiN N ≤ 6 * N := by
    rw [psiN_eq]
    have := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) hN0
    have hl4 : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    nlinarith
  rw [sum_lambda_mul_sub] at h1
  have key : |∑ n ∈ range (N + 1), G n - (N : ℝ) ^ 2 / 2| ≤ psiN N * B + N * B + N / 2 := by
    have e : ∑ n ∈ range (N + 1), G n - (N : ℝ) ^ 2 / 2 =
        (∑ n ∈ range (N + 1), G n - ∑ m ∈ range N, psiN m) +
        (∑ m ∈ range N, psiN m - ∑ m ∈ range N, (m : ℝ)) - (N : ℝ) / 2 := by
      rw [h3]; ring
    rw [e]
    calc _ ≤ |∑ n ∈ range (N + 1), G n - ∑ m ∈ range N, psiN m| +
          |∑ m ∈ range N, psiN m - ∑ m ∈ range N, (m : ℝ)| + |(N : ℝ) / 2| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ psiN N * B + N * B + N / 2 := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ N / 2)]
          gcongr
  calc _ ≤ psiN N * B + N * B + N / 2 := key
    _ ≤ 6 * N * B + N * B + N / 2 := by gcongr
    _ ≤ (N : ℝ) * (10 * B + 1) := by nlinarith

/-- **RH ⇒ AvgRH**, the forward half of `granville_equiv`, CONDITIONAL ON RH only. -/
theorem avgRH_of_RH (hRH : RiemannHypothesis) : AvgRH := by
  obtain ⟨C, D, hC, hD, hS⟩ := sum_G_RH hRH
  intro ε hε
  set δ := ε / 3 with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨10 * C * (1 / δ) ^ 3 + 10 * D + 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  -- log N ≤ N^δ / δ
  have hlog : Real.log N ≤ (N : ℝ) ^ δ / δ := Real.log_le_rpow_div hN0.le hδ0
  have hlog3 : Real.log N ^ 3 ≤ (1 / δ) ^ 3 * (N : ℝ) ^ ε := by
    have : Real.log N ^ 3 ≤ ((N : ℝ) ^ δ / δ) ^ 3 := by gcongr
    calc _ ≤ ((N : ℝ) ^ δ / δ) ^ 3 := this
      _ = (1 / δ) ^ 3 * ((N : ℝ) ^ δ) ^ 3 := by ring
      _ = (1 / δ) ^ 3 * (N : ℝ) ^ ε := by
          rw [← Real.rpow_natCast ((N : ℝ) ^ δ) 3, ← Real.rpow_mul hN0.le]; congr 2; push_cast
          rw [hδ]; ring
  have hsq : (N : ℝ) * √(N : ℝ) = (N : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hN0.le (by norm_num)]; norm_num
  have hpow : (N : ℝ) ^ (3 / 2 + ε) = (N : ℝ) ^ (3 / 2 : ℝ) * (N : ℝ) ^ ε :=
    Real.rpow_add hN0 _ _
  have hNε : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hN32 : (N : ℝ) ≤ (N : ℝ) ^ (3 / 2 : ℝ) := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hbig : (N : ℝ) ≤ (N : ℝ) ^ (3 / 2 + ε) := by
    rw [hpow]; nlinarith [hN32, hNε]
  refine (hS N hN).trans ?_
  have hA : (N : ℝ) * (10 * (C * √(N : ℝ) * Real.log N ^ 3)) ≤
      10 * C * (1 / δ) ^ 3 * (N : ℝ) ^ (3 / 2 + ε) := by
    rw [hpow, ← hsq]
    have hC0 : 0 ≤ 10 * C * ((N : ℝ) * √(N : ℝ)) := by positivity
    calc (N : ℝ) * (10 * (C * √(N : ℝ) * Real.log N ^ 3))
        = 10 * C * ((N : ℝ) * √(N : ℝ)) * Real.log N ^ 3 := by ring
      _ ≤ 10 * C * ((N : ℝ) * √(N : ℝ)) * ((1 / δ) ^ 3 * (N : ℝ) ^ ε) := by gcongr
      _ = _ := by ring
  have hB : (N : ℝ) * (10 * D + 1) ≤ (10 * D + 1) * (N : ℝ) ^ (3 / 2 + ε) := by
    rw [mul_comm]; gcongr
  calc (N : ℝ) * (10 * (C * √(N : ℝ) * Real.log N ^ 3 + D) + 1)
      = (N : ℝ) * (10 * (C * √(N : ℝ) * Real.log N ^ 3)) + (N : ℝ) * (10 * D + 1) := by ring
    _ ≤ 10 * C * (1 / δ) ^ 3 * (N : ℝ) ^ (3 / 2 + ε) + (10 * D + 1) * (N : ℝ) ^ (3 / 2 + ε) :=
        add_le_add hA hB
    _ = (10 * C * (1 / δ) ^ 3 + 10 * D + 1) * (N : ℝ) ^ (3 / 2 + ε) := by ring

/-- `psi_sq_bounds_of_RH` without the cited `granville_equiv`. -/
theorem psi_sq_bounds_of_RH' (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) ^ 2 / 2 - K * (N : ℝ) ^ (3 / 2 + ε) ≤ psiN N ^ 2 ∧
      psiN N ^ 2 ≤ 2 * (N : ℝ) ^ 2 + K * ((2 * N : ℕ) : ℝ) ^ (3 / 2 + ε) :=
  psi_sq_bounds_of_avgRH (avgRH_of_RH hRH) hε

end LeanLab.GoldbachAverage

