module

public import LeanLab.BrunGap.Final
public import LeanLab.SchnirelmannExplicit.Constants

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T2303Z-22954, unit U-0080.
Brun's bound for prime pairs with one constant for every even gap `h`, and its average
over gaps: the number of prime pairs `p < N`, `q = p + h` with even `h ≤ H` is at most
`9 C₀ H N / log² N`.
-/

@[expose] public section

open Finset
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
namespace LeanLab.BrunGap

/-- The constant of the uniform bound. -/
def C₀ : ℝ := 128 + 5 * 17 ^ 8

lemma C₀_pos : 0 < C₀ := by unfold C₀; norm_num

/-- **Uniform Brun bound**: one constant `C₀` for every even gap `h ≠ 0`. -/
theorem gapUpper_uniform (h : ℕ) (hh : Even h) (hh0 : h ≠ 0) (N : ℕ) (hN : 3 ≤ N) :
    (gapCount h N : ℝ) ≤ C₀ * singProd h * N / Real.log N ^ 2 := by
  unfold C₀
  have hN1 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hsp := one_le_singProd h
  set S := singProd h
  set z := √(N : ℝ) with hz
  have hz1 : 1 < z := by
    rw [hz, Real.lt_sqrt (by norm_num)]; linarith
  have hb := gapCount_le h N hh hh0 hz1
  have hlogz : Real.log z = Real.log N / 2 := Real.log_sqrt (by positivity)
  have hmain : 32 * (N : ℝ) * S / Real.log z ^ 2 = 128 * S * N / Real.log N ^ 2 := by
    rw [hlogz]; field_simp; ring
  have hlz : Real.log z ≤ Real.log N := by rw [hlogz]; linarith
  have hlogz0 : 0 ≤ Real.log z := Real.log_nonneg hz1.le
  have herr1 : z * (1 + Real.log z) ^ 6 + (z + 1) ≤ 5 * (z * (1 + Real.log N) ^ 6) := by
    have : (1 + Real.log z) ^ 6 ≤ (1 + Real.log N) ^ 6 := by gcongr
    have hpow1 : 1 ≤ (1 + Real.log z) ^ 6 := one_le_pow₀ (by linarith)
    nlinarith
  have hpb := polylog_bound N (by linarith)
  have herr2 : z * (1 + Real.log N) ^ 6 ≤ 17 ^ 8 * N / Real.log N ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have herr3 : (17 : ℝ) ^ 8 * N / Real.log N ^ 2 ≤ 17 ^ 8 * S * N / Real.log N ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (0 : ℝ) ≤ 17 ^ 8 * N := by positivity
    nlinarith
  have : (128 + 5 * 17 ^ 8 : ℝ) * S * N / Real.log N ^ 2 =
      128 * S * N / Real.log N ^ 2 + 5 * (17 ^ 8 * S * N / Real.log N ^ 2) := by ring
  rw [this]
  linarith

/-- `∑_{h ≤ H} singProd h ≤ 9 H`, from the mean square bound `S2_explicit`. -/
lemma sum_singProd_le (H : ℕ) (hH : 1 ≤ H) : ∑ h ∈ Icc 1 H, singProd h ≤ 9 * H := by
  have h2 := LeanLab.SchnirelmannExplicit.S2_explicit H hH
  have : ∑ h ∈ Icc 1 H, singProd h ≤ ∑ h ∈ Icc 1 H, singProd h ^ 2 := by
    apply sum_le_sum
    intro h _
    have := one_le_singProd h
    nlinarith
  linarith

/-- **Prime pairs with bounded gap, on average.** For `H ≥ 1` and `N ≥ 3`, the number of
pairs of primes `(p, p + h)` with `p < N` and `h ≤ H` even is at most `9 C₀ H N / log² N`. -/
theorem sum_gapCount_le (H N : ℕ) (hH : 1 ≤ H) (hN : 3 ≤ N) :
    ∑ h ∈ (Icc 1 H).filter Even, (gapCount h N : ℝ) ≤ 9 * C₀ * H * N / Real.log N ^ 2 := by
  have hN1 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hK : 0 ≤ C₀ * N / Real.log N ^ 2 := by have := C₀_pos; positivity
  calc ∑ h ∈ (Icc 1 H).filter Even, (gapCount h N : ℝ)
      ≤ ∑ h ∈ (Icc 1 H).filter Even, C₀ * N / Real.log N ^ 2 * singProd h := by
        apply sum_le_sum
        intro h hm
        rw [mem_filter, mem_Icc] at hm
        have := gapUpper_uniform h hm.2 (by omega) N hN
        calc (gapCount h N : ℝ) ≤ C₀ * singProd h * N / Real.log N ^ 2 := this
          _ = C₀ * N / Real.log N ^ 2 * singProd h := by ring
    _ ≤ ∑ h ∈ Icc 1 H, C₀ * N / Real.log N ^ 2 * singProd h := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro h _ _
        exact mul_nonneg hK (singProd_nonneg h)
    _ = C₀ * N / Real.log N ^ 2 * ∑ h ∈ Icc 1 H, singProd h := by rw [mul_sum]
    _ ≤ C₀ * N / Real.log N ^ 2 * (9 * H) := by
        gcongr; exact sum_singProd_le H hH
    _ = 9 * C₀ * H * N / Real.log N ^ 2 := by ring

end LeanLab.BrunGap
