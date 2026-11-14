module

public import LeanLab.SchnirelmannGoldbach.S2
public import LeanLab.SchnirelmannGoldbach.S1.Final

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Explicit constants for the analytic inputs of Schnirelmann's theorem:
Chebyshev `π m ≥ (log 2 / 2) m / log m` for `m ≥ 100`; the sieve bound S1u with
`C = 128 + 5 * 17^8 + 12`; and the mean square bound S2 with `C = 9`, via
`∑_{d ≤ N} d^{-3/2} ≤ 3`.
-/

@[expose] public section

open Finset Real

namespace LeanLab.SchnirelmannExplicit

open LeanLab.SchnirelmannGoldbach

/-- Chebyshev lower bound with explicit constant `log 2 / 2` and threshold `100`. -/
theorem pi_lower_explicit : ∀ m : ℕ, 100 ≤ m →
    Real.log 2 / 2 * m / Real.log m ≤ (Nat.primeCounting m : ℝ) := by
  intro m hm
  have hl2 := Real.log_two_gt_d9
  have hm' : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  refine le_trans ?_ (Chebyshev.pi_ge m)
  apply div_le_div_of_nonneg_right _ hlogm.le
  have h1 : Real.log ((m + 1) / 8) ≤ (m + 1) / 8 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h1
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [h8] at h1
  nlinarith

/-- The explicit sieve constant of S1u. -/
def C1 : ℝ := 128 + 5 * 17 ^ 8 + 12

open LeanLab.SchnirelmannGoldbach.S1 in
/-- **S1u, explicit.** For `3 ≤ N` and `1 ≤ n ≤ N`,
`r n ≤ (128 + 5·17^8 + 12) N / log² N · singProd n`. Same proof as `S1u_holds`. -/
theorem S1u_explicit : ∀ N : ℕ, 3 ≤ N → ∀ n ∈ Icc 1 N,
    (r n : ℝ) ≤ C1 * N / (Real.log N) ^ 2 * singProd n := by
  intro N hN n hn
  unfold C1
  simp only [mem_Icc] at hn
  have hN1 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hsp := one_le_singProd n
  have hNl : (N : ℝ) / Real.log N ^ 2 ≥ 1 / 4 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith [log_sq_le N (by linarith)]
  have hQ0 : 0 ≤ (N : ℝ) / Real.log N ^ 2 * singProd n := by positivity
  by_cases hev : Even n ∧ 4 ≤ n
  · obtain ⟨hev, hn4⟩ := hev
    have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hn4.trans hn.2
    set z := √(N : ℝ) with hz
    have hz2 : 2 ≤ z := by
      rw [hz, show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hN4
    have hrz := r_le_of_even hev (by omega) (by linarith : (1 : ℝ) < z)
    have hlogz : Real.log z = Real.log N / 2 := Real.log_sqrt (by positivity)
    have hlogz0 : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
    have hmain : 32 * n * singProd n / Real.log z ^ 2 ≤ 128 * (N / Real.log N ^ 2 * singProd n) := by
      rw [hlogz]
      rw [div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ singProd n := by linarith
      field_simp
      nlinarith
    have hlz : Real.log z ≤ Real.log N := by rw [hlogz]; linarith
    have hpow1 : 1 ≤ (1 + Real.log z) ^ 6 := one_le_pow₀ (by linarith)
    have herr1 : z * (1 + Real.log z) ^ 6 + 2 * (z + 1) ≤ 5 * (z * (1 + Real.log N) ^ 6) := by
      have : (1 + Real.log z) ^ 6 ≤ (1 + Real.log N) ^ 6 := by gcongr
      nlinarith
    have hpb := polylog_bound N (by linarith)
    have herr2 : z * (1 + Real.log N) ^ 6 ≤ 17 ^ 8 * (N / Real.log N ^ 2 * singProd n) := by
      have h1 : z * (1 + Real.log N) ^ 6 ≤ 17 ^ 8 * (N / Real.log N ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        exact hpb
      have h2 : (17 : ℝ) ^ 8 * (N / Real.log N ^ 2) ≤ 17 ^ 8 * (N / Real.log N ^ 2 * singProd n) := by
        have : (0 : ℝ) ≤ N / Real.log N ^ 2 := by positivity
        nlinarith
      linarith
    have : (r n : ℝ) ≤ (128 + 5 * 17 ^ 8) * (N / Real.log N ^ 2 * singProd n) := by
      linarith
    calc (r n : ℝ) ≤ (128 + 5 * 17 ^ 8) * (N / Real.log N ^ 2 * singProd n) := this
      _ ≤ (128 + 5 * 17 ^ 8 + 12) * (N / Real.log N ^ 2 * singProd n) := by nlinarith
      _ = _ := by ring
  · have h3 : (r n : ℝ) ≤ 3 := by exact_mod_cast r_le_three_of_not hev
    have : (3 : ℝ) ≤ 12 * (N / Real.log N ^ 2 * singProd n) := by nlinarith
    calc (r n : ℝ) ≤ 12 * (N / Real.log N ^ 2 * singProd n) := by linarith
      _ ≤ (128 + 5 * 17 ^ 8 + 12) * (N / Real.log N ^ 2 * singProd n) := by nlinarith
      _ = _ := by ring

/-- Telescoping step: `g (N+1) ≤ 2/√N - 2/√(N+1)`. -/
lemma g_succ_le (N : ℕ) (hN : 1 ≤ N) :
    g (N + 1) ≤ 2 / √(N : ℝ) - 2 / √((N : ℝ) + 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set a := √(N : ℝ) with ha
  set b := √((N : ℝ) + 1) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have haa : a * a = N := Real.mul_self_sqrt (by linarith)
  have hbb : b * b = N + 1 := Real.mul_self_sqrt (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  unfold g
  push_cast
  rw [← hb, ← hbb]
  rw [div_sub_div _ _ ha0.ne' hb0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  -- 1 * (a b) ≤ (2 b - a 2) * (b b b), using (b - a)(a + b) = 1
  have hba : (b - a) * (a + b) = 1 := by nlinarith
  have key : a * b * (a + b) ≤ 2 * (b * b * b) := by nlinarith [mul_pos ha0 hb0]
  nlinarith [mul_pos ha0 hb0, mul_pos (mul_pos ha0 hb0) hb0]

/-- `∑_{d=1}^N d^{-3/2} ≤ 3 - 2/√N`. -/
lemma sum_g_le (N : ℕ) (hN : 1 ≤ N) : ∑ d ∈ Icc 1 N, g d ≤ 3 - 2 / √(N : ℝ) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · simp [g]; norm_num
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have := ih hpos
      have hs := g_succ_le N hpos
      push_cast
      linarith

/-- `∑_{d=1}^N d^{-3/2} ≤ 3`. -/
lemma sum_g_le_three (N : ℕ) : ∑ d ∈ Icc 1 N, g d ≤ 3 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have := sum_g_le N hN
    have : 0 ≤ 2 / √(N : ℝ) := by positivity
    linarith

/-- **S2, explicit.** `∑_{n ≤ N} singProd n ^ 2 ≤ 9 N`. -/
theorem S2_explicit : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Icc 1 N, singProd n ^ 2 ≤ 9 * N := by
  intro N _
  have key : ∀ n ∈ Icc 1 N, singProd n ^ 2 ≤
      ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) := by
    intro n hn
    rw [mem_Icc] at hn
    have hsum : ∑ d ∈ n.divisors, 1 / (d : ℝ) =
        ∑ d ∈ Icc 1 N, (if d ∣ n then 1 / (d : ℝ) else 0) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext d
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨hd, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hn.2⟩, hd⟩
      · rintro ⟨-, hd⟩; exact ⟨hd, by omega⟩
    rw [← Finset.sum_mul_sum, ← sq, ← hsum]
    gcongr
    · exact singProd_nonneg n
    · exact singProd_le_sum_divisors n (by omega)
  calc ∑ n ∈ Icc 1 N, singProd n ^ 2
      ≤ ∑ n ∈ Icc 1 N, ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) :=
        Finset.sum_le_sum key
    _ = ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if d1 ∣ n then 1 / (d1 : ℝ) else 0) * (if d2 ∣ n then 1 / (d2 : ℝ) else 0) := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro _ _; rw [Finset.sum_comm]
    _ ≤ ∑ d1 ∈ Icc 1 N, ∑ d2 ∈ Icc 1 N, (N : ℝ) * (g d1 * g d2) := by
        apply Finset.sum_le_sum; intro d1 hd1; apply Finset.sum_le_sum; intro d2 hd2
        exact pair_le N d1 d2 (mem_Icc.mp hd1).1 (mem_Icc.mp hd2).1
    _ = N * (∑ d ∈ Icc 1 N, g d) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro _ _; rw [Finset.mul_sum]
    _ ≤ N * 3 ^ 2 := by
        gcongr
        · exact Finset.sum_nonneg (fun d _ => g_nonneg d)
        · exact sum_g_le_three N
    _ = 9 * N := by ring

end LeanLab.SchnirelmannExplicit
