module

public import LeanLab.BhowmikGrimmelt2026.ApproximationError

/-!
Control of the actual scale dependent smoothing in display 7.8, pages 26 and 27.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction
open scoped NNReal

/-- The paper cutoff vanishes at every argument at least one. -/
theorem phi_zero_ge_one261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {x : ℝ} (hx : 1 ≤ x) :
    ϕ x = 0 := by
  by_contra h
  have hs := hϕ.supp (subset_tsupport ϕ h)
  linarith [hs.2]

/-- A smoothed prime sum at scale N can be written using any longer finite range. -/
theorem Sphi_extend261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N X : ℕ} (hNX : N ≤ X)
    (α : ℝ) :
    Sphi ϕ N α = ∑ n ∈ Finset.range (X + 1),
      ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n) := by
  unfold Sphi
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hnN
  have hnN' : N < n := by simp only [Finset.mem_range] at hnN; omega
  by_cases hN : N = 0
  · subst N
    have hz : ϕ 0 = 0 := by
      by_contra h
      have hs := hϕ.supp (subset_tsupport ϕ h)
      linarith [hs.1]
    simp [hz]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
    have hn : (N : ℝ) ≤ n := by exact_mod_cast hnN'.le
    rw [phi_zero_ge_one261 hϕ ((le_div_iff₀ hNpos).mpr (by simpa using hn))]
    simp

/-- Lipschitz regularity gives a uniform reciprocal scale gain in each cutoff increment. -/
theorem phi_scale_increment261 {ϕ : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L ϕ)
    {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ N - 1) :
    |ϕ ((n : ℝ) / N) - ϕ ((n : ℝ) / (N - 1 : ℕ))| ≤ (L : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hprev : (0 : ℝ) < (N - 1 : ℕ) := by exact_mod_cast (by omega : 0 < N - 1)
  have hcast : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hn' : (n : ℝ) ≤ (N - 1 : ℕ) := by exact_mod_cast hn
  have horder : (n : ℝ) / N ≤ n / (N - 1 : ℕ) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg n) hprev
    exact_mod_cast (by omega : N - 1 ≤ N)
  have hdist : |(n : ℝ) / N - n / (N - 1 : ℕ)| ≤ 1 / N := by
    rw [abs_of_nonpos (sub_nonpos.mpr horder)]
    rw [le_div_iff₀ hNpos]
    have hdiv : (n : ℝ) / (N - 1 : ℕ) ≤ 1 := (div_le_one hprev).mpr hn'
    have heq : -((n : ℝ) / N - n / (N - 1 : ℕ)) * N = n / (N - 1 : ℕ) := by
      rw [hcast]
      have hNm1 : (N : ℝ) - 1 ≠ 0 := by rw [← hcast]; exact hprev.ne'
      field_simp [hNpos.ne', hNm1]
      ring
    rw [heq]
    exact hdiv
  have h := hL.norm_sub_le ((n : ℝ) / N) ((n : ℝ) / (N - 1 : ℕ))
  simp only [Real.norm_eq_abs] at h
  exact h.trans (by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hdist L.coe_nonneg)

/-- Parseval for a fixed finite exponential polynomial in the local convention. -/
theorem finite_parseval261 (a : ℕ → ℂ) (M : ℕ) :
    (∫ α in (0 : ℝ)..1, ‖∑ n ∈ Finset.range M, a n * ee (α * n)‖ ^ 2) =
      ∑ n ∈ Finset.range M, ‖a n‖ ^ 2 := by
  have hp : Function.Periodic
      (fun α : ℝ => ‖∑ n ∈ Finset.range M, a n * ee (α * n)‖ ^ 2) 1 := by
    intro α
    apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (α + 1) * (n : ℝ) = α * n + (n : ℤ) by push_cast; ring,
      ee_add_int]
  calc
    _ = ∫ α in (-(1 / 2 : ℝ))..(1 / 2),
        ‖∑ n ∈ Finset.range M, a n * ee (α * n)‖ ^ 2 := by
      have h := hp.intervalIntegral_add_eq 0 (-(1 / 2 : ℝ))
      norm_num at h ⊢
      exact h
    _ = _ := by
      simp_rw [ee_eq_library84]
      convert LeanLab.PNTPort.Gallagher.parseval a M using 1
      congr 1
      funext α
      simp_rw [mul_comm α]

/-- Chebyshev controls the total von Mangoldt mass at every natural scale. -/
theorem mangoldt_mass261 (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), vonMangoldt n ≤ 6 * N := by
  have heq : (∑ n ∈ Finset.range (N + 1), vonMangoldt n) = Chebyshev.psi N := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Nat.range_succ_eq_Icc_zero]
  rw [heq]
  have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
  have h4 := LeanLab.PNTPort.Vinogradov.log4_bounds.2
  nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- A bounded cutoff gives a pointwise linear bound for its smoothed prime sum. -/
theorem Sphi_uniform261 {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) (N : ℕ) (α : ℝ) :
    ‖Sphi ϕ N α‖ ≤ 6 * M * N := by
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        ‖((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1), vonMangoldt n * M := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, ee_eq_library84, LeanLab.PNTPort.LargeSieve.norm_e,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_left (hbound _) vonMangoldt_nonneg
    _ = (∑ n ∈ Finset.range (N + 1), vonMangoldt n) * M := by rw [Finset.sum_mul]
    _ ≤ 6 * M * N := by nlinarith [mul_le_mul_of_nonneg_right (mangoldt_mass261 N) hM]

/-- Consecutive smoothing scales have one common finite polynomial for their difference. -/
theorem Sphi_increment261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (N : ℕ) (α : ℝ) :
    Sphi ϕ N α - Sphi ϕ (N - 1) α =
      ∑ n ∈ Finset.range (N + 1),
        ((vonMangoldt n * (ϕ (n / N) - ϕ (n / (N - 1 : ℕ))) : ℝ) : ℂ) *
          ee (α * n) := by
  rw [Sphi_extend261 hϕ (show N - 1 ≤ N by omega) α]
  unfold Sphi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

/-- The energy of one smoothing increment gains the reciprocal scale squared. -/
theorem Sphi_increment_energy261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {N : ℕ} (hN : 2 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖Sphi ϕ N α - Sphi ϕ (N - 1) α‖ ^ 2) ≤
      6 * (L : ℝ) ^ 2 * Real.log N / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hprev : (0 : ℝ) < (N - 1 : ℕ) := by exact_mod_cast (by omega : 0 < N - 1)
  have hcut (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      |ϕ ((n : ℝ) / N) - ϕ ((n : ℝ) / (N - 1 : ℕ))| ≤ (L : ℝ) / N := by
    have hnN : n ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    by_cases hn' : n ≤ N - 1
    · exact phi_scale_increment261 hL hN hn'
    · have heq : n = N := by omega
      subst n
      rw [div_self hNpos.ne', phi_zero_ge_one261 hϕ le_rfl,
        phi_zero_ge_one261 hϕ ((le_div_iff₀ hprev).mpr (by
          have hh : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N - 1 ≤ N)
          simpa using hh))]
      simp only [sub_self, abs_zero]
      positivity
  have henergy : (∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2) ≤
      6 * N * Real.log N := by
    have heq : (∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2) =
        ∑ n ∈ Finset.Icc 1 N, vonMangoldt n ^ 2 := by
      rw [Nat.range_succ_eq_Icc_zero]
      symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
      intro n hn hn'
      have hz : n = 0 := by simp only [Finset.mem_Icc] at hn hn'; omega
      simp [hz]
    rw [heq]
    exact mangoldt_energy84 N
  simp_rw [Sphi_increment261 hϕ N]
  rw [finite_parseval261]
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2 * ((L : ℝ) / N) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, mul_pow, sq_abs]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (hcut n hn) 2) (sq_nonneg _)
    _ = ((L : ℝ) / N) ^ 2 * ∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2 := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ ((L : ℝ) / N) ^ 2 * (6 * N * Real.log N) :=
      mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
    _ = _ := by field_simp

end LeanLab.BhowmikGrimmelt2026
