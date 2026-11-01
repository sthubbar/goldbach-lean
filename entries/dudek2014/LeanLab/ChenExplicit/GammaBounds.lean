module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-18, run 20261018T0704Z-6940, unit U-0923.
Two-sided bounds on Euler's constant, `0.57720 < γ < 0.57722`, for the Section 9 margin of
P0009, BJS 2022, which is sensitive to `γ` at the `10⁻⁵` level. Mathlib has `1/2 < γ < 2/3`.

Method: `u n = H_n - log n - 1/(2n)` increases to `γ` and `w n = H_n - log(n + 1/2)` decreases
to `γ`; both steps come from Mathlib's series `log(1 + 1/a) = 2 Σ y^{2k+1}/(2k+1)`,
`y = 1/(2a + 1)`. Then `u 100` and `w 100` are evaluated from `H_100` and `log 2`, `log(5/4)`.
-/

@[expose] public section

open Real Filter Topology Finset

noncomputable section
namespace LeanLab.ChenExplicit.Gamma

/-- `log(1 + 1/a) ≤ 2y/(1 - y²)`, `y = 1/(2a+1)`. -/
lemma log_one_add_inv_le {a : ℝ} (ha : 0 < a) :
    log (1 + a⁻¹) ≤ 2 * (1 / (2 * a + 1)) / (1 - (1 / (2 * a + 1)) ^ 2) := by
  set y := 1 / (2 * a + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hS := hasSum_log_one_add_inv ha
  have hG : HasSum (fun k : ℕ => 2 * y * (y ^ 2) ^ k) (2 * y * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left (2 * y)
  have hle : ∀ k : ℕ, (2 : ℝ) * (1 / (2 * k + 1)) * y ^ (2 * k + 1) ≤ 2 * y * (y ^ 2) ^ k := by
    intro k
    have h1 : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
    have e : y ^ (2 * k + 1) = y * (y ^ 2) ^ k := by rw [← pow_mul, pow_succ]; ring
    rw [e]
    have : 0 ≤ y * (y ^ 2) ^ k := by positivity
    nlinarith
  have := hasSum_le hle hS hG
  rw [div_eq_mul_inv]; exact this

/-- `2y ≤ log(1 + 1/a)`, the first term of the series. -/
lemma log_one_add_inv_ge {a : ℝ} (ha : 0 < a) : 2 * (1 / (2 * a + 1)) ≤ log (1 + a⁻¹) := by
  have hS := hasSum_log_one_add_inv ha
  have h := le_hasSum hS 0 (fun k _ => by positivity)
  simpa using h

/-- `log(1 + 1/a)` up to the first `n` terms, lower bound. -/
lemma log_one_add_inv_ge_sum {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∑ k ∈ range n, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) ≤
      log (1 + a⁻¹) :=
  sum_le_hasSum _ (fun k _ => by positivity) (hasSum_log_one_add_inv ha)

/-- Upper bound: first `n` terms plus the geometric tail `2 y^{2n+1}/(1 - y²)`. -/
lemma log_one_add_inv_le_sum {a : ℝ} (ha : 0 < a) (n : ℕ) :
    log (1 + a⁻¹) ≤ ∑ k ∈ range n, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1)
      + 2 * (1 / (2 * a + 1)) ^ (2 * n + 1) / (1 - (1 / (2 * a + 1)) ^ 2) := by
  set y := 1 / (2 * a + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hS := hasSum_log_one_add_inv ha
  have hT := (hasSum_nat_add_iff' n).mpr hS
  have hG : HasSum (fun k : ℕ => 2 * y ^ (2 * n + 1) * (y ^ 2) ^ k)
      (2 * y ^ (2 * n + 1) * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
  have hle : ∀ k : ℕ, (2 : ℝ) * (1 / (2 * ((k + n : ℕ) : ℝ) + 1)) * y ^ (2 * (k + n) + 1) ≤
      2 * y ^ (2 * n + 1) * (y ^ 2) ^ k := by
    intro k
    have h1 : (1 : ℝ) / (2 * ((k + n : ℕ) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ ((k + n : ℕ) : ℝ) := Nat.cast_nonneg _; linarith
    have e : y ^ (2 * (k + n) + 1) = y ^ (2 * n + 1) * (y ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    rw [e]
    have : 0 ≤ y ^ (2 * n + 1) * (y ^ 2) ^ k := by positivity
    nlinarith
  have := hasSum_le hle hT hG
  rw [div_eq_mul_inv]; linarith

/-- `u n = H_n - log n - 1/(2n)`. -/
def u (n : ℕ) : ℝ := harmonic n - log n - 1 / (2 * n)

lemma u_step (n : ℕ) (hn : 1 ≤ n) : u n ≤ u (n + 1) := by
  unfold u
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := log_one_add_inv_le hn0
  have e1 : log ((n + 1 : ℕ) : ℝ) = log n + log (1 + (n : ℝ)⁻¹) := by
    rw [← log_mul hn0.ne' (by positivity)]; congr 1; push_cast; field_simp
  rw [e1, harmonic_succ]; push_cast
  have hn' : (n : ℝ) ≠ 0 := hn0.ne'
  have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have e3 : 1 - (1 / (2 * (n : ℝ) + 1)) ^ 2 = 4 * n * (n + 1) / (2 * n + 1) ^ 2 := by
    field_simp; ring
  have e2 : 2 * (1 / (2 * (n : ℝ) + 1)) / (1 - (1 / (2 * n + 1)) ^ 2) =
      1 / (2 * n) + 1 / (2 * (n + 1)) := by
    rw [e3]; field_simp; ring
  rw [e2] at hl
  have : ((n : ℝ) + 1)⁻¹ = 1 / (n + 1) := by rw [one_div]
  rw [this]
  have : 1 / ((n : ℝ) + 1) = 1 / (2 * (n + 1)) + 1 / (2 * (n + 1)) := by field_simp; ring
  linarith

lemma u_mono : MonotoneOn u (Set.Ici 1) := by
  apply monotoneOn_of_le_succ (Set.ordConnected_Ici)
  intro n _ hn _; exact u_step n hn

lemma u_tendsto : Tendsto u atTop (𝓝 eulerMascheroniConstant) := by
  have h1 := tendsto_harmonic_sub_log
  have h2 : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)
    simp only [mul_zero] at this
    refine this.congr fun n => ?_; rw [one_div_mul_one_div]
  have := h1.sub h2
  rw [sub_zero] at this
  exact this

theorem u_le_gamma (n : ℕ) (hn : 1 ≤ n) : u n ≤ eulerMascheroniConstant := by
  apply ge_of_tendsto u_tendsto
  filter_upwards [eventually_ge_atTop n] with m hm
  exact u_mono (Set.mem_Ici.mpr hn) (Set.mem_Ici.mpr (hn.trans hm)) hm

/-- `w n = H_n - log(n + 1/2)`. -/
def w (n : ℕ) : ℝ := harmonic n - log (n + 1 / 2)

lemma w_step (n : ℕ) : w (n + 1) ≤ w n := by
  unfold w
  have ha : (0 : ℝ) < n + 1 / 2 := by positivity
  have hl := log_one_add_inv_ge ha
  have e1 : log (((n + 1 : ℕ) : ℝ) + 1 / 2) = log (n + 1 / 2) + log (1 + ((n : ℝ) + 1 / 2)⁻¹) := by
    rw [← log_mul ha.ne' (by positivity)]; congr 1; push_cast; field_simp; ring
  rw [e1, harmonic_succ]; push_cast
  have e2 : 2 * (1 / (2 * ((n : ℝ) + 1 / 2) + 1)) = ((n : ℝ) + 1)⁻¹ := by field_simp; ring
  rw [e2] at hl
  linarith

lemma w_tendsto : Tendsto w atTop (𝓝 eulerMascheroniConstant) := by
  have h1 := tendsto_harmonic_sub_log
  have h2 : Tendsto (fun n : ℕ => log ((n : ℝ) + 1 / 2) - log n) atTop (𝓝 0) := by
    have := tendsto_log_comp_add_sub_log (1 / 2 : ℝ)
    exact this.comp tendsto_natCast_atTop_atTop
  have := h1.sub h2
  simp only [sub_zero] at this
  refine this.congr fun n => ?_
  simp [w]

theorem gamma_le_w (n : ℕ) : eulerMascheroniConstant ≤ w n := by
  apply le_of_tendsto w_tendsto
  filter_upwards [eventually_ge_atTop n] with m hm
  exact (antitone_nat_of_succ_le w_step) hm

/-- `H_100`, exact. -/
theorem harmonic_100_bounds :
    (5187377 / 1000000 : ℚ) < harmonic 100 ∧ harmonic 100 < 5187378 / 1000000 := by
  constructor <;> decide +kernel

lemma log_five_four_bounds :
    0.2231435 ≤ log (5 / 4 : ℝ) ∧ log (5 / 4 : ℝ) ≤ 0.2231436 := by
  have e : (5 / 4 : ℝ) = 1 + (4 : ℝ)⁻¹ := by norm_num
  rw [e]
  have h1 := log_one_add_inv_ge_sum (a := (4 : ℝ)) (by norm_num) 4
  have h2 := log_one_add_inv_le_sum (a := (4 : ℝ)) (by norm_num) 4
  simp only [sum_range_succ, sum_range_zero] at h1 h2
  norm_num at h1 h2
  constructor <;> linarith

lemma log_100_eq : log (100 : ℝ) = 6 * log 2 + 2 * log (5 / 4) := by
  have : (100 : ℝ) = 2 ^ 6 * (5 / 4) ^ 2 := by norm_num
  rw [this, log_mul (by norm_num) (by norm_num), log_pow, log_pow]; push_cast; ring

/-- **`0.57720 < γ`, PROVED**, from `u 100 = H_100 - log 100 - 1/200 ≈ 0.5772074`. -/
theorem gamma_gt : (0.57720 : ℝ) < eulerMascheroniConstant := by
  have h := u_le_gamma 100 (by norm_num)
  unfold u at h
  have hH := harmonic_100_bounds.1
  have hH' : ((5187377 / 1000000 : ℚ) : ℝ) < (harmonic 100 : ℝ) := by exact_mod_cast hH
  have l2 := log_two_lt_d9
  have l54 := log_five_four_bounds.2
  have e := log_100_eq
  push_cast at h hH' ⊢
  rw [e] at h
  norm_num at h hH' l2 ⊢
  linarith

/-- **`γ < 0.57722`, PROVED**, from `w 100 = H_100 - log 100.5 ≈ 0.5772199`. -/
theorem gamma_lt : eulerMascheroniConstant < (0.57722 : ℝ) := by
  have h := gamma_le_w 100
  unfold w at h
  have hH := harmonic_100_bounds.2
  have hH' : (harmonic 100 : ℝ) < ((5187378 / 1000000 : ℚ) : ℝ) := by exact_mod_cast hH
  have l2 := log_two_gt_d9
  have l54 := log_five_four_bounds.1
  have e := log_100_eq
  have hs : log ((100 : ℕ) + 1 / 2 : ℝ) = log 100 + log (1 + (200 : ℝ)⁻¹) := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have hg := log_one_add_inv_ge (a := (200 : ℝ)) (by norm_num)
  rw [hs, e] at h
  norm_num at h hH' l2 hg ⊢
  linarith

end LeanLab.ChenExplicit.Gamma
