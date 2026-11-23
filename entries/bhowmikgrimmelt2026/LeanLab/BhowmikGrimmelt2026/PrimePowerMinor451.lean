module

public import LeanLab.BhowmikGrimmelt2026.Decomp384b
public import LeanLab.BhowmikGrimmelt2026.Smoothing261

/-!
Higher prime power energy for the smoothed minor sum in P0029 page 27.
The survey omits the higher prime powers on page 4.
These are derived bounds and do not assert the OPEN logarithm power five leaf.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

/-- The smoothed sum restricted to higher prime powers, with the original phase. -/
noncomputable def nonprimeSphi451 (ϕ : ℝ → ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    (((vonMangoldt n - if n.Prime then vonMangoldt n else 0) *
      ϕ (n / N) : ℝ) : ℂ) * ee (α * n)

/-- The same smoothing sum restricted to primes, as in the omission on page 4. -/
noncomputable def primeSphi451 (ϕ : ℝ → ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    ((if n.Prime then vonMangoldt n * ϕ (n / N) else 0 : ℝ) : ℂ) * ee (α * n)

/-- The prime and higher prime power sums retain every term of the original smoothing. -/
theorem Sphi_prime_split451 (ϕ : ℝ → ℝ) (N : ℕ) (α : ℝ) :
    Sphi ϕ N α = primeSphi451 ϕ N α + nonprimeSphi451 ϕ N α := by
  unfold Sphi primeSphi451 nonprimeSphi451
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime <;> simp [hp]

/-- Both parts of the finite exponential polynomial are continuous. -/
theorem continuous_prime_parts451 (ϕ : ℝ → ℝ) (N : ℕ) :
    Continuous (primeSphi451 ϕ N) ∧ Continuous (nonprimeSphi451 ϕ N) := by
  constructor <;> apply continuous_finset_sum <;> intro n hn <;>
    exact continuous_const.mul (ee_contDiff.continuous.comp (continuous_id.mul continuous_const))

/-- The squared higher prime power coefficients have square root size.
Derived from the omitted terms on P0029 page 4 and Mathlib Chebyshev bounds. -/
theorem nonprime_energy451 (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range (N + 1),
      (vonMangoldt n - if n.Prime then vonMangoldt n else 0) ^ 2) ≤
        2 * Real.sqrt N * Real.log N ^ 2 := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hbound (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      0 ≤ vonMangoldt n - (if n.Prime then vonMangoldt n else 0) ∧
      vonMangoldt n - (if n.Prime then vonMangoldt n else 0) ≤ Real.log N := by
    by_cases hp : n.Prime
    · simp [hp, hlog]
    · simp only [hp, ↓reduceIte, sub_zero]
      refine ⟨vonMangoldt_nonneg, ?_⟩
      rcases Nat.eq_zero_or_pos n with rfl | hnp
      · simpa using hlog
      · exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hnp)
          (by exact_mod_cast (show n ≤ N by simpa using hn)))
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), Real.log N *
        (vonMangoldt n - if n.Prime then vonMangoldt n else 0) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨h0, h1⟩ := hbound n hn
      nlinarith only [mul_nonneg h0 (sub_nonneg.mpr h1)]
    _ = Real.log N * (Chebyshev.psi N - Chebyshev.theta N) := by
      rw [← Finset.mul_sum, nonprime_mass_eq384]
    _ ≤ Real.log N * (2 * Real.sqrt N * Real.log N) :=
      mul_le_mul_of_nonneg_left (Chebyshev.psi_sub_theta_le (by exact_mod_cast hN)) hlog
    _ = _ := by ring

/-- Parseval bounds the higher prime power part of any bounded smoothing.
The bound needs no minor arc or prime distribution hypothesis. -/
theorem nonprime_smoothed_energy451 {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖nonprimeSphi451 ϕ N α‖ ^ 2) ≤
      2 * M ^ 2 * Real.sqrt N * Real.log N ^ 2 := by
  unfold nonprimeSphi451
  rw [finite_parseval261]
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), M ^ 2 *
        (vonMangoldt n - if n.Prime then vonMangoldt n else 0) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
      have hh := pow_le_pow_left₀ (abs_nonneg (ϕ ((n : ℝ) / N))) (hbound _) 2
      rw [sq_abs] at hh
      nlinarith only [mul_le_mul_of_nonneg_left hh
        (sq_nonneg (vonMangoldt n - if n.Prime then vonMangoldt n else 0))]
    _ = M ^ 2 * ∑ n ∈ Finset.range (N + 1),
        (vonMangoldt n - if n.Prime then vonMangoldt n else 0) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ M ^ 2 * (2 * Real.sqrt N * Real.log N ^ 2) :=
      mul_le_mul_of_nonneg_left (nonprime_energy451 N hN) (sq_nonneg M)
    _ = _ := by ring

/-- A bounded multiplier preserves the Cauchy Schwarz coefficient energy bound.
This is a fixed coefficient estimate for the minor step on P0029 page 27. -/
theorem product_coefficient_energy451 {f g : ℝ → ℂ} (hf : Continuous f)
    (hg : Continuous g) (W : ℝ → ℂ) (hW : ∀ α, ‖W α‖ ≤ 1) :
    ‖∫ α in (0 : ℝ)..1, f α * g α * W α‖ ^ 2 ≤
      (∫ α in (0 : ℝ)..1, ‖f α‖ ^ 2) * (∫ α in (0 : ℝ)..1, ‖g α‖ ^ 2) := by
  have hLp (u : ℝ → ℂ) (hu : Continuous u) :
      MemLp u 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
    exact ((hu.norm.pow 2).continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hf2 := hLp f hf
  have hg2 := hLp g hg
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hn := norm_integral_le_of_norm_le
    (f := fun α => f α * g α * W α)
    (hf2.norm.integrable_mul hg2.norm)
    (Filter.Eventually.of_forall (fun α => by
      simp only [norm_mul]
      simpa only [mul_one, Pi.mul_apply] using mul_le_mul_of_nonneg_left (hW α)
        (mul_nonneg (norm_nonneg (f α)) (norm_nonneg (g α)))))
  have hh := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
    Real.HolderConjugate.two_two (f := f) (g := g)
    (by simpa using hf2) (by simpa using hg2)
  simp only [Real.rpow_two] at hh
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  have hb := pow_le_pow_left₀ (norm_nonneg _) (hn.trans hh) 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun α => sq_nonneg ‖f α‖)),
    Real.sq_sqrt (integral_nonneg (fun α => sq_nonneg ‖g α‖))] at hb
  exact hb

/-- The sum of the prime and full smoothing has the same linear prime energy budget.
The coefficient twenty four is a derived constant for page 27. -/
theorem prime_plus_full_energy451 {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) (N : ℕ) :
    (∫ α in (0 : ℝ)..1, ‖Sphi ϕ N α + primeSphi451 ϕ N α‖ ^ 2) ≤
      24 * M ^ 2 * N * Real.log N := by
  have heq (α : ℝ) : Sphi ϕ N α + primeSphi451 ϕ N α =
      ∑ n ∈ Finset.range (N + 1),
        (((vonMangoldt n + if n.Prime then vonMangoldt n else 0) *
          ϕ (n / N) : ℝ) : ℂ) * ee (α * n) := by
    unfold Sphi primeSphi451
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime <;> simp [hp] <;> ring
  simp_rw [heq]
  rw [finite_parseval261]
  have henergy : (∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2) ≤
      6 * N * Real.log N := by
    have hzero : (∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2) =
        ∑ n ∈ Finset.Icc 1 N, vonMangoldt n ^ 2 := by
      rw [Nat.range_succ_eq_Icc_zero]
      symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
      intro n hn hn'
      have hz : n = 0 := by simp only [Finset.mem_Icc] at hn hn'; omega
      simp [hz]
    rw [hzero]
    exact mangoldt_energy84 N
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), 4 * M ^ 2 * vonMangoldt n ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
      have hp := pow_le_pow_left₀ (abs_nonneg (ϕ ((n : ℝ) / N))) (hbound _) 2
      rw [sq_abs] at hp
      by_cases hnP : n.Prime
      · simp only [hnP, ↓reduceIte]
        nlinarith only [mul_le_mul_of_nonneg_left hp (sq_nonneg (2 * vonMangoldt n))]
      · simp only [hnP, ↓reduceIte, add_zero]
        nlinarith only [mul_le_mul_of_nonneg_left hp (sq_nonneg (vonMangoldt n)),
          mul_nonneg (sq_nonneg M) (sq_nonneg (vonMangoldt n))]
    _ = 4 * M ^ 2 * ∑ n ∈ Finset.range (N + 1), vonMangoldt n ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ 4 * M ^ 2 * (6 * N * Real.log N) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

/-- Higher prime powers have a smaller coefficient square budget under every bounded multiplier.
The multiplier can include a minor arc mask and an additive phase. -/
theorem prime_power_coefficient_defect451 {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) (N : ℕ) (hN : 1 ≤ N)
    (W : ℝ → ℂ) (hW : ∀ α, ‖W α‖ ≤ 1) :
    ‖∫ α in (0 : ℝ)..1, (Sphi ϕ N α ^ 2 - primeSphi451 ϕ N α ^ 2) * W α‖ ^ 2 ≤
      48 * M ^ 4 * N * Real.sqrt N * Real.log N ^ 3 := by
  have heq (α : ℝ) : Sphi ϕ N α ^ 2 - primeSphi451 ϕ N α ^ 2 =
      nonprimeSphi451 ϕ N α * (Sphi ϕ N α + primeSphi451 ϕ N α) := by
    have hh := Sphi_prime_split451 ϕ N α
    linear_combination (Sphi ϕ N α + primeSphi451 ϕ N α) * hh
  simp_rw [heq]
  have hc := continuous_prime_parts451 ϕ N
  have hb := product_coefficient_energy451 hc.2 ((continuous_Sphi ϕ N).add hc.1) W hW
  apply hb.trans
  have hn := nonprime_smoothed_energy451 hM hbound N hN
  have hp := prime_plus_full_energy451 hM hbound N
  calc
    _ ≤ (2 * M ^ 2 * Real.sqrt N * Real.log N ^ 2) *
        (24 * M ^ 2 * N * Real.log N) := by
      apply mul_le_mul hn hp
      · exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
      · positivity
    _ = _ := by ring

/-- Higher prime power removal has a square root saving even for varying bounded multipliers.
This is a derived family bound for the actual changing smoothing in display 7.8. -/
theorem prime_power_family_defect451 {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) {X : ℕ} (hX : 2 ≤ X)
    (W : ℕ → ℝ → ℂ) (hW : ∀ N α, ‖W N α‖ ≤ 1) :
    (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1, (Sphi ϕ N α ^ 2 - primeSphi451 ϕ N α ^ 2) * W N α‖ ^ 2) ≤
        48 * M ^ 4 * (X : ℝ) ^ 2 * Real.sqrt X * Real.log X ^ 3 := by
  calc
    _ ≤ ∑ N ∈ Finset.Icc 1 X,
        48 * M ^ 4 * X * Real.sqrt X * Real.log X ^ 3 := by
      apply Finset.sum_le_sum
      intro N hN
      have hN1 := (Finset.mem_Icc.mp hN).1
      have hNX := (Finset.mem_Icc.mp hN).2
      apply (prime_power_coefficient_defect451 hM hbound N hN1 (W N) (hW N)).trans
      have hnp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      gcongr
    _ = _ := by simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul]; ring

/-- The higher prime power defect fits the X to thirteen fifths part of the printed budget.
This does not estimate the prime only minor coefficient. -/
theorem prime_power_family_log5_451 {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) {X : ℕ} (hX : 2 ≤ X)
    (W : ℕ → ℝ → ℂ) (hW : ∀ N α, ‖W N α‖ ≤ 1) :
    (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1, (Sphi ϕ N α ^ 2 - primeSphi451 ϕ N α ^ 2) * W N α‖ ^ 2) ≤
        192 * M ^ 4 * (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5 := by
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hpow : (X : ℝ) ^ 2 * Real.sqrt X ≤ (X : ℝ) ^ (13 / 5 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hxp]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    norm_num
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ X by exact_mod_cast hX)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by linarith [Real.log_two_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 2
  have hm := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ Real.log (X : ℝ) ^ 3)
  have hlog : Real.log (X : ℝ) ^ 3 ≤ 4 * Real.log X ^ 5 := by
    norm_num at hm
    nlinarith only [hm]
  calc
    _ ≤ 48 * M ^ 4 * (X : ℝ) ^ 2 * Real.sqrt X * Real.log X ^ 3 :=
      prime_power_family_defect451 hM hbound hX W hW
    _ = (48 * M ^ 4) * ((X : ℝ) ^ 2 * Real.sqrt X) * Real.log X ^ 3 := by ring
    _ ≤ (48 * M ^ 4) * (X : ℝ) ^ (13 / 5 : ℝ) * (4 * Real.log X ^ 5) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hpow (by positivity)
      · exact hlog
      · positivity
      · positivity
    _ = _ := by ring

end LeanLab.BhowmikGrimmelt2026
