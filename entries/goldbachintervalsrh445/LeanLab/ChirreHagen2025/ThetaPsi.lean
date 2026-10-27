module

public import Mathlib
public import LeanLab.ChirreHagen2025.Schoenfeld

/-!
T2, unit U-5031. `J_θ` from `J_ψ`: Chirre-Hagen Theorem 2 has the constant 2.2258 for `J_ψ`,
Theorem 3 has 2.5571 for `J_θ`. With `D(y) = (ψ - θ)((1+δ)y) - (ψ - θ)(y) ≥ 0`, pointwise
`(u - D)² ≤ (1+η) u² + (1 + 1/η) D²`, so `J_θ ≤ (1+η) J_ψ + (1 + 1/η) ∫ D²`, and `∫ D²` is small:
`∫_1^X D ≤ δ X (ψ - θ)((1+δ)X)` and `D ≤ log² ((1+δ)y) / log 2` when every `k`-th root
interval `(y^{1/k}, ((1+δ)y)^{1/k}]` is shorter than 1, so holds at most one prime.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.ChirreHagen2025
open Real Chebyshev Finset

/-- `ψ - θ`, the prime powers `p^k`, `k ≥ 2`. -/
noncomputable def fpt (y : ℝ) : ℝ := ψ y - θ y

theorem fpt_nonneg (y : ℝ) : 0 ≤ fpt y := by unfold fpt; linarith [theta_le_psi y]

theorem fpt_mono : Monotone fpt := by
  intro a b hab
  unfold fpt
  rw [psi_sub_theta_eq_sum_not_prime, psi_sub_theta_eq_sum_not_prime]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨hn.1.1, le_trans hn.1.2 (Nat.floor_le_floor hab)⟩, hn.2⟩
  · intro n _ _; exact ArithmeticFunction.vonMangoldt_nonneg

/-- The increment `D(y)`. -/
noncomputable def Dpt (δ y : ℝ) : ℝ := fpt ((1 + δ) * y) - fpt y

theorem Dpt_nonneg {δ y : ℝ} (hδ : 0 ≤ δ) (hy : 0 ≤ y) : 0 ≤ Dpt δ y := by
  unfold Dpt; linarith [fpt_mono (show y ≤ (1 + δ) * y by nlinarith)]

/-- `J_ψ`'s integrand is interval integrable. -/
theorem psi_integrand_ii {δ c d : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hcd : c ≤ d) :
    IntervalIntegrable (fun y => (ψ ((1 + δ) * y) - ψ y - δ * y) ^ 2) MeasureTheory.volume c d := by
  set A : ℝ → ℝ := fun y => ψ ((1 + δ) * y) with hA
  set B : ℝ → ℝ := fun y => ψ y + δ * y with hB
  have hs : Set.uIcc c d = Set.Icc c d := Set.uIcc_of_le hcd
  have hAm : MonotoneOn A (Set.uIcc c d) := fun u _ v _ huv => psi_mono (by nlinarith)
  have hBm : MonotoneOn B (Set.uIcc c d) := fun u _ v _ huv => by
    simp only [hB]; have := psi_mono huv; nlinarith
  have hA0 : ∀ y ∈ Set.uIcc c d, 0 ≤ A y := fun y _ => psi_nonneg _
  have hB0 : ∀ y ∈ Set.uIcc c d, 0 ≤ B y := fun y hy => by
    rw [hs] at hy
    have := psi_nonneg y
    simp only [hB]; nlinarith [hy.1]
  have iAA := (hAm.mul hAm hA0 hA0).intervalIntegrable (μ := MeasureTheory.volume)
  have iAB := (hAm.mul hBm hA0 hB0).intervalIntegrable (μ := MeasureTheory.volume)
  have iBB := (hBm.mul hBm hB0 hB0).intervalIntegrable (μ := MeasureTheory.volume)
  have := (iAA.sub (iAB.const_mul 2)).add iBB
  refine this.congr ?_
  intro y _
  simp only [Pi.mul_apply, hA, hB]
  ring

theorem Dpt_ii {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    IntervalIntegrable (Dpt δ) MeasureTheory.volume a b := by
  have hm : Monotone fun t => fpt ((1 + δ) * t) := fun u v huv => fpt_mono (by nlinarith)
  exact (hm.intervalIntegrable).sub (fpt_mono.intervalIntegrable)

theorem Dpt_sq_ii {δ c d : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hcd : c ≤ d) :
    IntervalIntegrable (fun y => Dpt δ y ^ 2) MeasureTheory.volume c d := by
  set A : ℝ → ℝ := fun y => fpt ((1 + δ) * y) with hA
  set B : ℝ → ℝ := fun y => fpt y with hB
  have hAm : MonotoneOn A (Set.uIcc c d) := fun u _ v _ huv => fpt_mono (by nlinarith)
  have hBm : MonotoneOn B (Set.uIcc c d) := fun u _ v _ huv => fpt_mono huv
  have hA0 : ∀ y ∈ Set.uIcc c d, 0 ≤ A y := fun y _ => fpt_nonneg _
  have hB0 : ∀ y ∈ Set.uIcc c d, 0 ≤ B y := fun y _ => fpt_nonneg _
  have iAA := (hAm.mul hAm hA0 hA0).intervalIntegrable (μ := MeasureTheory.volume)
  have iAB := (hAm.mul hBm hA0 hB0).intervalIntegrable (μ := MeasureTheory.volume)
  have iBB := (hBm.mul hBm hB0 hB0).intervalIntegrable (μ := MeasureTheory.volume)
  have := (iAA.sub (iAB.const_mul 2)).add iBB
  refine this.congr ?_
  intro y _
  simp only [Pi.mul_apply, hA, hB, Dpt]
  ring

/-- Step 1: `J_θ ≤ (1+η) J_ψ + (1 + 1/η) ∫ D²`. -/
theorem Jtheta_le_Jpsi {X δ η : ℝ} (hX : 1 ≤ X) (hδ : 0 < δ) (hη : 0 < η) :
    Jtheta X δ ≤ (1 + η) * Jpsi X δ + (1 + 1 / η) * ∫ y in (1 : ℝ)..X, Dpt δ y ^ 2 := by
  unfold Jtheta Jpsi
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((psi_integrand_ii hδ zero_le_one hX).const_mul _)
      ((Dpt_sq_ii hδ zero_le_one hX).const_mul _)]
  apply intervalIntegral.integral_mono_on hX
  · exact integrand_intervalIntegrable hδ zero_le_one hX
  · exact ((psi_integrand_ii hδ zero_le_one hX).const_mul _).add
      ((Dpt_sq_ii hδ zero_le_one hX).const_mul _)
  · intro y _
    set u := ψ ((1 + δ) * y) - ψ y - δ * y
    set D := Dpt δ y
    have e : θ ((1 + δ) * y) - θ y - δ * y = u - D := by
      simp only [u, D, Dpt, fpt]; ring
    rw [e]
    have h : 0 ≤ (η * u + D) ^ 2 / η := by positivity
    have e2 : (1 + η) * u ^ 2 + (1 + 1 / η) * D ^ 2 - (u - D) ^ 2 = (η * u + D) ^ 2 / η := by
      field_simp; ring
    linarith

/-- Step 2: `∫_1^X D ≤ δ X (ψ - θ)((1+δ)X)`. -/
theorem intD_le {X δ : ℝ} (hX : 2 ≤ X) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ y in (1 : ℝ)..X, Dpt δ y ≤ δ * X * fpt ((1 + δ) * X) := by
  have hk : 0 < 1 + δ := by linarith
  have iF : ∀ a b, IntervalIntegrable fpt MeasureTheory.volume a b :=
    fun a b => fpt_mono.intervalIntegrable
  have iFk : IntervalIntegrable (fun t => fpt ((1 + δ) * t)) MeasureTheory.volume 1 X :=
    (show Monotone fun t => fpt ((1 + δ) * t) from fun u v huv => fpt_mono (by nlinarith)).intervalIntegrable
  have hsplit : (∫ y in (1 : ℝ)..X, Dpt δ y)
      = (∫ y in (1 : ℝ)..X, fpt ((1 + δ) * y)) - ∫ y in (1 : ℝ)..X, fpt y :=
    intervalIntegral.integral_sub iFk (iF 1 X)
  have hsub : (∫ y in (1 : ℝ)..X, fpt ((1 + δ) * y))
      = (1 + δ)⁻¹ * ∫ u in (1 + δ) * 1..(1 + δ) * X, fpt u := by
    rw [intervalIntegral.integral_comp_mul_left fpt (ne_of_gt hk), smul_eq_mul]
  have hI0 : 0 ≤ ∫ u in (1 + δ) * 1..(1 + δ) * X, fpt u :=
    intervalIntegral.integral_nonneg (by nlinarith) (fun u _ => fpt_nonneg u)
  have hinv : (1 + δ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h1 : (1 + δ)⁻¹ * (∫ u in (1 + δ) * 1..(1 + δ) * X, fpt u)
      ≤ ∫ u in (1 + δ) * 1..(1 + δ) * X, fpt u := by
    nlinarith
  have s1 : (∫ u in (1 + δ) * 1..X, fpt u) + (∫ u in X..(1 + δ) * X, fpt u)
      = ∫ u in (1 + δ) * 1..(1 + δ) * X, fpt u :=
    intervalIntegral.integral_add_adjacent_intervals (iF _ _) (iF _ _)
  have s2 : (∫ u in (1 : ℝ)..(1 + δ) * 1, fpt u) + (∫ u in (1 + δ) * 1..X, fpt u)
      = ∫ u in (1 : ℝ)..X, fpt u :=
    intervalIntegral.integral_add_adjacent_intervals (iF _ _) (iF _ _)
  have h0 : 0 ≤ ∫ u in (1 : ℝ)..(1 + δ) * 1, fpt u :=
    intervalIntegral.integral_nonneg (by nlinarith) (fun u _ => fpt_nonneg u)
  have htop : (∫ u in X..(1 + δ) * X, fpt u) ≤ ∫ u in X..(1 + δ) * X, fpt ((1 + δ) * X) := by
    apply intervalIntegral.integral_mono_on (by nlinarith) (iF _ _)
      (intervalIntegrable_const)
    intro u hu; exact fpt_mono hu.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at htop
  have e : ((1 + δ) * X - X) * fpt ((1 + δ) * X) = δ * X * fpt ((1 + δ) * X) := by ring
  rw [hsplit, hsub]
  linarith

/-- `θ` grows by at most `log b` over an interval `(a, b]` shorter than 1. -/
theorem theta_sub_le_log {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (h1 : b < a + 1) (hb : 1 ≤ b) :
    θ b - θ a ≤ Real.log b := by
  rw [theta_eq_theta_coe_floor b, theta_eq_theta_coe_floor a]
  set m := ⌊a⌋₊ with hm
  set n := ⌊b⌋₊ with hn
  have hmn : m ≤ n := Nat.floor_le_floor hab
  have hnm : n ≤ m + 1 := by
    have := Nat.floor_le_floor h1.le
    rwa [Nat.floor_add_one ha] at this
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb
  rcases Nat.eq_or_lt_of_le hmn with h | h
  · rw [h]; simp; exact hlb
  · have hn' : n = m + 1 := by omega
    rw [hn', theta_eq_sum_Icc, theta_eq_sum_Icc, Nat.floor_natCast, Nat.floor_natCast,
      Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega)]
    simp only [add_sub_cancel_left]
    split_ifs with hp
    · have hnb : ((m + 1 : ℕ) : ℝ) ≤ b := by
        rw [← hn']; exact Nat.floor_le (by linarith)
      exact Real.log_le_log (by positivity) hnb
    · exact hlb

/-- `ψ - θ` as the sum over `k ≥ 2` of `θ(y^{1/k})`, for `y ≥ 1`. -/
theorem fpt_eq_sum {y : ℝ} (hy : 1 ≤ y) {N : ℕ} (hN : ⌊Real.log y / Real.log 2⌋₊ ≤ N) :
    fpt y = ∑ k ∈ Icc 2 N, θ (y ^ ((1 : ℝ) / k)) := by
  unfold fpt
  rcases le_or_gt 2 y with h2 | h2
  · rw [psi_eq_theta_add_sum_theta' h2 hN]; ring
  · rw [psi_eq_zero_of_lt_two h2, theta_eq_zero_of_lt_two h2, sub_zero]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    apply theta_eq_zero_of_lt_two
    calc y ^ ((1 : ℝ) / k) ≤ y ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hy
          rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ k)
      _ = y := Real.rpow_one y
      _ < 2 := h2

/-- Step 3: if `δ √y < 1` then `D(y) ≤ log² ((1+δ) y) / log 2`. -/
theorem Dpt_le {y δ : ℝ} (hy : 1 ≤ y) (hδ : 0 < δ) (hs : δ * √y < 1) :
    Dpt δ y ≤ Real.log ((1 + δ) * y) ^ 2 / Real.log 2 := by
  set b := (1 + δ) * y with hb
  have hb1 : 1 ≤ b := by nlinarith
  have hyb : y ≤ b := by nlinarith
  set N := ⌊Real.log b / Real.log 2⌋₊ with hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNy : ⌊Real.log y / Real.log 2⌋₊ ≤ N :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hyb) hl2.le)
  unfold Dpt
  rw [← hb, fpt_eq_sum hb1 le_rfl, fpt_eq_sum hy hNy, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Icc 2 N, θ (b ^ ((1 : ℝ) / k)) - θ (y ^ ((1 : ℝ) / k)) ≤ Real.log b := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hr0 : (0 : ℝ) ≤ 1 / k := by positivity
    have hr1 : (1 : ℝ) / k ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hk0 (by norm_num)]; norm_num; exact_mod_cast hk2
    have hy0 : 0 ≤ y ^ ((1 : ℝ) / k) := by positivity
    have hyb' : y ^ ((1 : ℝ) / k) ≤ b ^ ((1 : ℝ) / k) :=
      Real.rpow_le_rpow (by linarith) hyb hr0
    have hbk : b ^ ((1 : ℝ) / k) = (1 + δ) ^ ((1 : ℝ) / k) * y ^ ((1 : ℝ) / k) :=
      Real.mul_rpow (by linarith) (by linarith)
    have hδk : (1 + δ) ^ ((1 : ℝ) / k) ≤ 1 + δ := by
      calc (1 + δ) ^ ((1 : ℝ) / k) ≤ (1 + δ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 1 + δ := Real.rpow_one _
    have hysq : y ^ ((1 : ℝ) / k) ≤ √y := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hy hr1
    have hlt : b ^ ((1 : ℝ) / k) < y ^ ((1 : ℝ) / k) + 1 := by
      rw [hbk]
      have : ((1 + δ) ^ ((1 : ℝ) / k) - 1) * y ^ ((1 : ℝ) / k) ≤ δ * √y :=
        mul_le_mul (by linarith) hysq hy0 hδ.le
      nlinarith
    have hb1k : 1 ≤ b ^ ((1 : ℝ) / k) := Real.one_le_rpow hb1 hr0
    refine (theta_sub_le_log hy0 hyb' hlt hb1k).trans ?_
    rw [Real.log_rpow (by linarith)]
    have : 0 ≤ Real.log b := Real.log_nonneg hb1
    calc 1 / (k : ℝ) * Real.log b ≤ 1 * Real.log b :=
          mul_le_mul_of_nonneg_right (by rw [div_le_one hk0]; exact_mod_cast (by omega : 1 ≤ k)) this
      _ = Real.log b := one_mul _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hNle : ((N + 1 - 2 : ℕ) : ℝ) ≤ Real.log b / Real.log 2 := by
    have h1 : ((N + 1 - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N + 1 - 2 ≤ N)
    exact h1.trans (Nat.floor_le (div_nonneg hlb hl2.le))
  calc ((N + 1 - 2 : ℕ) : ℝ) * Real.log b ≤ Real.log b / Real.log 2 * Real.log b :=
        mul_le_mul_of_nonneg_right hNle hlb
    _ = Real.log b ^ 2 / Real.log 2 := by ring

set_option maxHeartbeats 1000000 in
/-- The bilinear argument with any mean-square constant `c` at the scales `x/2 ≤ X ≤ x`. -/
theorem large_c_of {c H : ℝ} (hc0 : 0 ≤ c) (hH1 : 1 / 10 ≤ H) (hH : H ≤ 61.5)
    (hHc : c * 0.2380 < H * (20419 / 393216 - 123 / 400000)) (hT : ThetaRel)
    (x : ℝ) (hx : 1.1 * 10 ^ 18 ≤ x)
    (hJ : ∀ X : ℝ, x / 2 ≤ X → X ≤ x → Jtheta X (H * Real.log x ^ 2 / x)
      ≤ c * (H * Real.log x ^ 2 / x) * Real.log (2.0001 / (H * Real.log x ^ 2 / x)) ^ 2 * X ^ 2) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + H * Real.log x ^ 2 := by
  by_contra hno
  have hL : 41 ≤ Real.log x := log_ge_41 hx
  have hxpos : 0 < x := by linarith
  set h := H * Real.log x ^ 2 with hh
  have hδpos : 0 < h / x := div_pos (mul_pos (by linarith) (by positivity)) hxpos
  have hδle : h / x ≤ 1 / 10 ^ 13 := by
    have := threshold2 hx
    have : h / x ≤ 61.5 * Real.log x ^ 2 / x := by
      rw [hh]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
    linarith
  have hδx : h / x * x = h := by field_simp
  set δ := h / x with hδ
  have hint := bil_integrated (by linarith) hδpos hδx.le hno
  have hrhs := rhs_le_abel (x := x) (by linarith) hδpos
  -- Theorem 3 at the scales, Abel summation
  set K := c * δ * Real.log (2.0001 / δ) ^ 2 with hK
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hc0 hδpos.le) (sq_nonneg _)
  have hGB : ∀ j, Gs δ x s16 j ≤ x ^ 2 * K * s16 j ^ 2 := by
    intro j
    have hb := s16_bounds j
    have hX : 10 ^ 13 ≤ s16 j * x := by nlinarith
    have := hJ (s16 j * x) (by nlinarith) (by nlinarith)
    have e : Jtheta (s16 j * x) δ = Gs δ x s16 j := rfl
    rw [e] at this
    calc Gs δ x s16 j ≤ c * δ * Real.log (2.0001 / δ) ^ 2 * (s16 j * x) ^ 2 := this
      _ = x ^ 2 * K * s16 j ^ 2 := by rw [hK]; ring
  have hup := abelSum_mono wb (Gs δ x s16) (fun j => x ^ 2 * K * s16 j ^ 2)
    wb_antitone (fun j => by unfold wb; positivity) hGB 16
  have hfac : abelSum wb (fun j => x ^ 2 * K * s16 j ^ 2) 16
      = x ^ 2 * K * abelSum wb (fun j => s16 j ^ 2) 16 := by
    simp only [abelSum]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hfac] at hup
  have hxK : 0 ≤ x ^ 2 * K := mul_nonneg (by positivity) hK0
  have hup2 : abelSum wb (Gs δ x s16) 16 ≤ x ^ 2 * K * 0.2380 := by
    have := mul_le_mul_of_nonneg_left Ub_lt.le hxK
    linarith
  -- the cross terms
  have hδ1 : δ ≤ 1 / 16 := by linarith
  have hδxle : δ * x ≤ x / 16 := by nlinarith
  have hA1 : (1 + δ) * (x / 16) ≤ x / 2 := by nlinarith
  have hA2 : (1 + δ) * (x / 2) ≤ 15 * x / 16 := by nlinarith
  have hA3 : (1 + δ) * (15 * x / 16) ≤ 2 * x := by nlinarith
  have hρ : ∀ u, x / 16 ≤ u → u ≤ (1 + δ) * (15 * x / 16) → |Rθ u| ≤ 2 * x / 10 ^ 5 := by
    intro u h1 h2
    have := hT u (by linarith)
    have hu2 : u ≤ 2 * x := by linarith
    unfold Rθ
    linarith [div_le_div_of_nonneg_right hu2 (by norm_num : (0 : ℝ) ≤ 10 ^ 5)]
  have hδs : δ ≤ 1 / 10 ^ 13 := hδle
  have hc1 := cross_bound (g := g1f x) (by unfold g1f; fun_prop) hδpos
    (by positivity : (0 : ℝ) < x / 16) hA1
    (fun u h1 h2 => hρ u h1 (by linarith)) (D := 10 * δ * x) (Gm := 2 * x)
    (fun u h1 h2 => g1_D hxpos hδpos (by nlinarith) (by linarith))
    (fun u h1 h2 => g1_abs hxpos (by linarith) (by linarith))
    (fun u h1 h2 => gk_abs hxpos hδpos (by linarith) (by linarith) h2 (g1f x)
      (fun t ht0 ht1 => g1_abs hxpos ht0 ht1))
  have hc2 := cross_bound (g := g2f x) (by unfold g2f; fun_prop) hδpos
    (by positivity : (0 : ℝ) < x / 2) hA2
    (fun u h1 h2 => hρ u (by linarith) h2) (D := 16 * δ * x) (Gm := 2 * x)
    (fun u h1 h2 => g2_D hxpos hδpos (by nlinarith) (by linarith))
    (fun u h1 h2 => g2_abs hxpos (by linarith) (by linarith))
    (fun u h1 h2 => gk_abs hxpos hδpos (by linarith) (by linarith) h2 (g2f x)
      (fun t ht0 ht1 => g2_abs hxpos ht0 ht1))
  have a1' := neg_abs_le (∫ t in x / 16..x / 2, g1f x t * Eθ δ t)
  have a2' := neg_abs_le (∫ u in x / 2..15 * x / 16, g2f x u * Eθ δ u)
  have b1 := mul_le_mul_of_nonneg_left hc1 hδpos.le
  have b2 := mul_le_mul_of_nonneg_left hc2 hδpos.le
  have c1 := mul_le_mul_of_nonneg_left a1' hδpos.le
  have c2 := mul_le_mul_of_nonneg_left a2' hδpos.le
  -- numerics, everything divided by δ x²
  set L := Real.log x with hLdef
  set u := Real.log (2.0001 / δ) with hu
  have hu0 : 0 ≤ u := Real.log_nonneg (by rw [le_div_iff₀ hδpos]; nlinarith)
  have huL : u ≤ L := by
    apply Real.log_le_log (by positivity)
    rw [hδ, hh, div_div_eq_mul_div, div_le_iff₀ (mul_pos (by linarith) (by positivity))]
    have : (2.0001 : ℝ) ≤ H * L ^ 2 := by nlinarith
    nlinarith
  have hu2 : u ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hu0 huL 2
  have hdx : δ * x = H * L ^ 2 := by rw [hδ, hh]; field_simp
  have hD : 0 < δ * x ^ 2 := mul_pos hδpos (by positivity)
  have em : δ ^ 2 * (2 * ((x / 2) ^ 3 - (x / 16) ^ 3) / 3 - 2 / x * (((x / 2) ^ 4 - (x / 16) ^ 4) / 4))
      = (δ * x ^ 2) * (δ * x * (2 * ((1 / 2) ^ 3 - (1 / 16) ^ 3) / 3
        - 2 * (((1 / 2) ^ 4 - (1 / 16) ^ 4) / 4))) := by
    field_simp
  have ec : δ * (10 * δ * x * (2 * x / 10 ^ 5) * (x / 2 - x / 16)
        + 2 * x * (2 * x / 10 ^ 5) * (δ * (x / 2)) + 2 * x * (2 * x / 10 ^ 5) * (δ * (x / 16)))
      + δ * (16 * δ * x * (2 * x / 10 ^ 5) * (15 * x / 16 - x / 2)
        + 2 * x * (2 * x / 10 ^ 5) * (δ * (15 * x / 16)) + 2 * x * (2 * x / 10 ^ 5) * (δ * (x / 2)))
      = (δ * x ^ 2) * (δ * x * ((10 * 2 * (7 / 16) + 2 * 2 * (1 / 2) + 2 * 2 * (1 / 16)
        + 16 * 2 * (7 / 16) + 2 * 2 * (15 / 16) + 2 * 2 * (1 / 2)) / 10 ^ 5)) := by ring
  have hKx : x ^ 2 * K * 0.2380 = (δ * x ^ 2) * (c * 0.2380 * u ^ 2) := by rw [hK]; ring
  have key : (δ * x ^ 2) * (δ * x * (2 * ((1 / 2) ^ 3 - (1 / 16) ^ 3) / 3
        - 2 * (((1 / 2) ^ 4 - (1 / 16) ^ 4) / 4)))
      ≤ (δ * x ^ 2) * (c * 0.2380 * u ^ 2 + δ * x * ((10 * 2 * (7 / 16) + 2 * 2 * (1 / 2)
        + 2 * 2 * (1 / 16) + 16 * 2 * (7 / 16) + 2 * 2 * (15 / 16) + 2 * 2 * (1 / 2)) / 10 ^ 5)) := by
    rw [mul_add, ← em, ← hKx, ← ec]
    linarith only [hint, hrhs, hup2, b1, b2, c1, c2]
  have k2 := le_of_mul_le_mul_left key hD
  rw [hdx] at k2
  have hm : (2 * ((1 / 2 : ℝ) ^ 3 - (1 / 16) ^ 3) / 3 - 2 * (((1 / 2) ^ 4 - (1 / 16) ^ 4) / 4))
      = 20419 / 393216 := by norm_num
  have hc : ((10 * 2 * (7 / 16) + 2 * 2 * (1 / 2) + 2 * 2 * (1 / 16) + 16 * 2 * (7 / 16)
      + 2 * 2 * (15 / 16) + 2 * 2 * (1 / 2)) / 10 ^ 5 : ℝ) = 123 / 400000 := by norm_num
  rw [hm, hc] at k2
  have hL2 : 0 < L ^ 2 := by positivity
  have hfin : c * 0.2380 * u ^ 2 ≤ c * 0.2380 * L ^ 2 :=
    mul_le_mul_of_nonneg_left hu2 (mul_nonneg hc0 (by norm_num))
  nlinarith [k2, hfin, hL2, hHc]


theorem log_1e6_le : Real.log (10 ^ 6) ≤ 14 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : (2.7 : ℝ) ^ 14 ≤ Real.exp 1 ^ 14 :=
    pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) Real.exp_one_gt_d9.le) 14
  rw [← Real.exp_nat_mul] at h
  norm_num at h ⊢
  linarith

/-- `log³ y / √y ≤ 7.5 · 10^-5` for `y ≥ 10^18`, through `w = y^{1/3}`. -/
theorem log_cube_div_sqrt {y : ℝ} (hy : 10 ^ 18 ≤ y) : Real.log y ^ 3 / √y ≤ 7.5 / 10 ^ 5 := by
  have hy0 : 0 < y := by linarith
  set w := y ^ ((1 : ℝ) / 3) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hy0 _
  have hw3 : w ^ 3 = y := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
  have hw6 : (10 : ℝ) ^ 6 ≤ w := by
    by_contra h
    push_neg at h
    have := pow_lt_pow_left₀ h hw0.le (by norm_num : (3 : ℕ) ≠ 0)
    rw [hw3] at this; norm_num at this; linarith
  have hlog : Real.log y = 3 * Real.log w := by
    rw [← hw3, Real.log_pow]; push_cast; ring
  have hsq : √y = w * √w := by
    rw [← hw3, show w ^ 3 = w ^ 2 * w by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hw0.le]
  have he2 : Real.exp 2 ≤ (10 : ℝ) ^ 6 := by
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 := by gcongr; exact Real.exp_one_lt_d9.le
      _ ≤ 10 ^ 6 := by norm_num
  have hanti := Real.log_div_sqrt_antitoneOn (Set.mem_Ici.mpr he2)
    (Set.mem_Ici.mpr (le_trans he2 hw6)) hw6
  simp only at hanti
  have hs6 : √((10 : ℝ) ^ 6) = 10 ^ 3 := by
    rw [show (10 : ℝ) ^ 6 = (10 ^ 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs6] at hanti
  have hl0 : 0 ≤ Real.log w / √w :=
    div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hb : Real.log w / √w ≤ 14 / 10 ^ 3 :=
    le_trans hanti (div_le_div_of_nonneg_right log_1e6_le (by norm_num))
  have hcube := pow_le_pow_left₀ hl0 hb 3
  have hsw : 0 < √w := Real.sqrt_pos.mpr hw0
  have e : Real.log y ^ 3 / √y = 27 * (Real.log w / √w) ^ 3 := by
    rw [hlog, hsq, div_pow]
    have : √w ^ 3 = w * √w := by
      rw [show √w ^ 3 = √w ^ 2 * √w by ring, Real.sq_sqrt hw0.le]
    rw [this]; ring
  rw [e]
  have : (27 : ℝ) * (14 / 10 ^ 3) ^ 3 ≤ 7.5 / 10 ^ 5 := by norm_num
  nlinarith

/-- Step 4: from Theorem 2's `J_ψ` bound, `J_θ(X, δ) ≤ 2.23 δ log²(2.0001/δ) X²` for
`X ≥ 5 · 10^17`, `0 < δ ≤ 10^-13` and `δ √X < 1`. -/
theorem Jtheta_le_223 {X δ : ℝ}
    (h2 : Jpsi X δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2)
    (hX : 5 * 10 ^ 17 ≤ X) (hδ : 0 < δ) (hδ13 : δ ≤ 1 / 10 ^ 13) (hs : δ * √X < 1) :
    Jtheta X δ ≤ 2.23 * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2 := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hk : 1 + δ ≤ 2 := by linarith
  have hstep1 := Jtheta_le_Jpsi (η := 1 / 1000) hX1 hδ (by norm_num)
  set M := Real.log ((1 + δ) * X) ^ 2 / Real.log 2 with hM
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDle : ∀ y, 1 ≤ y → y ≤ X → Dpt δ y ≤ M := by
    intro y hy1 hyX
    have hsy : δ * √y < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hyX) hδ.le) hs
    refine (Dpt_le hy1 hδ hsy).trans ?_
    apply div_le_div_of_nonneg_right _ hl2.le
    apply pow_le_pow_left₀ (Real.log_nonneg (by nlinarith))
    exact Real.log_le_log (by nlinarith) (by nlinarith)
  have hD2 : ∫ y in (1 : ℝ)..X, Dpt δ y ^ 2 ≤ ∫ y in (1 : ℝ)..X, M * Dpt δ y := by
    apply intervalIntegral.integral_mono_on hX1 (Dpt_sq_ii hδ zero_le_one hX1)
      ((Dpt_ii hδ 1 X).const_mul M)
    intro y hy
    have h0 := Dpt_nonneg hδ.le (by linarith [hy.1] : (0 : ℝ) ≤ y)
    have h1 := hDle y hy.1 hy.2
    nlinarith
  rw [intervalIntegral.integral_const_mul] at hD2
  have hID := intD_le (by linarith : (2 : ℝ) ≤ X) hδ (by linarith)
  have hkX1 : 1 ≤ (1 + δ) * X := by nlinarith
  have hf := psi_sub_theta_le hkX1
  have hfpt : fpt ((1 + δ) * X) ≤ 2 * √((1 + δ) * X) * Real.log ((1 + δ) * X) := hf
  -- bound everything by y = 2X
  set y := 2 * X with hy
  have hkXy : (1 + δ) * X ≤ y := by nlinarith
  have hly : Real.log ((1 + δ) * X) ≤ Real.log y := Real.log_le_log (by linarith) hkXy
  have hl0 : 0 ≤ Real.log ((1 + δ) * X) := Real.log_nonneg hkX1
  have hsqy : √((1 + δ) * X) ≤ √y := Real.sqrt_le_sqrt hkXy
  have hM0 : 0 ≤ M := by positivity
  have hMy : M ≤ Real.log y ^ 2 / Real.log 2 :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hl0 hly 2) hl2.le
  have hfy : fpt ((1 + δ) * X) ≤ 2 * √y * Real.log y := by
    refine hfpt.trans ?_
    have : 0 ≤ √((1 + δ) * X) := Real.sqrt_nonneg _
    have hly0 : 0 ≤ Real.log y := le_trans hl0 hly
    nlinarith [mul_le_mul hsqy hly hl0 (Real.sqrt_nonneg _)]
  have hint0 : 0 ≤ ∫ y in (1 : ℝ)..X, Dpt δ y :=
    intervalIntegral.integral_nonneg hX1 (fun t ht => Dpt_nonneg hδ.le (by linarith [ht.1]))
  -- ∫ D² ≤ (log² y / log 2) · δ X · 2 √y log y
  have hD2' : ∫ y in (1 : ℝ)..X, Dpt δ y ^ 2
      ≤ Real.log y ^ 2 / Real.log 2 * (δ * X * (2 * √y * Real.log y)) := by
    have a1 : M * (∫ y in (1 : ℝ)..X, Dpt δ y) ≤ M * (δ * X * fpt ((1 + δ) * X)) :=
      mul_le_mul_of_nonneg_left hID hM0
    have a2 : δ * X * fpt ((1 + δ) * X) ≤ δ * X * (2 * √y * Real.log y) :=
      mul_le_mul_of_nonneg_left hfy (by positivity)
    have a3 : 0 ≤ δ * X * (2 * √y * Real.log y) := le_trans
      (mul_nonneg (by positivity) (fpt_nonneg _)) a2
    have a4 := mul_le_mul hMy a2 (mul_nonneg (by positivity) (fpt_nonneg _))
      (by positivity : (0 : ℝ) ≤ Real.log y ^ 2 / Real.log 2)
    linarith
  -- numerics: log³ y / √y ≤ 7.5e-5, log 2 ≥ 0.69, L ≥ 30
  have hcube := log_cube_div_sqrt (by rw [hy]; linarith : (10 : ℝ) ^ 18 ≤ y)
  have hy0 : 0 < y := by linarith
  have hsy0 : 0 < √y := Real.sqrt_pos.mpr hy0
  have hcube' : Real.log y ^ 3 ≤ 7.5 / 10 ^ 5 * √y := by rwa [div_le_iff₀ hsy0] at hcube
  have hsyy : √y * √y = y := Real.mul_self_sqrt hy0.le
  have hl2' : 0.69 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  set L := Real.log (2.0001 / δ) with hL
  have hL30 : 30 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 30 ≤ 2 * 10 ^ 13 := by
      have h1 : Real.exp 1 ^ 30 ≤ (2.7182818286 : ℝ) ^ 30 := by
        gcongr; exact Real.exp_one_lt_d9.le
      rw [← Real.exp_nat_mul] at h1; norm_num at h1 ⊢; linarith
    have : 2 * 10 ^ 13 ≤ 2.0001 / δ := by
      rw [le_div_iff₀ hδ]; nlinarith
    linarith
  -- the D² part is at most 0.0019 δ L² X²
  have hpart : (1 + 1 / (1 / 1000)) * (Real.log y ^ 2 / Real.log 2 * (δ * X * (2 * √y * Real.log y)))
      ≤ 0.0019 * δ * L ^ 2 * X ^ 2 := by
    have e : (1 + 1 / (1 / 1000)) * (Real.log y ^ 2 / Real.log 2 * (δ * X * (2 * √y * Real.log y)))
        = 2002 * δ * X * (Real.log y ^ 3 * √y) / Real.log 2 := by
      field_simp; ring
    rw [e, div_le_iff₀ hl2]
    have h1 : Real.log y ^ 3 * √y ≤ 7.5 / 10 ^ 5 * y := by
      have := mul_le_mul_of_nonneg_right hcube' hsy0.le
      rw [mul_assoc, hsyy] at this; exact this
    have h2' : 2002 * δ * X * (Real.log y ^ 3 * √y) ≤ 2002 * δ * X * (7.5 / 10 ^ 5 * y) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have hL2 : 900 ≤ L ^ 2 := by nlinarith
    have hdX0 : 0 ≤ δ * X ^ 2 := by positivity
    have h3a : 900 * 0.69 ≤ L ^ 2 * Real.log 2 :=
      mul_le_mul hL2 hl2' (by norm_num) (by positivity)
    have h5 := mul_le_mul_of_nonneg_left h3a (by positivity : (0 : ℝ) ≤ 0.0019 * (δ * X ^ 2))
    have h3 : 0.0019 * δ * L ^ 2 * X ^ 2 * Real.log 2 = 0.0019 * (δ * X ^ 2) * (L ^ 2 * Real.log 2) := by
      ring
    have h4 : 2002 * δ * X * (7.5 / 10 ^ 5 * (2 * X)) = 0.3003 * (δ * X ^ 2) := by ring
    rw [hy] at h2'
    rw [h3]
    linarith
  have hJ1 : (1 + 1 / 1000) * Jpsi X δ ≤ (1 + 1 / 1000) * (2.2258 * δ * L ^ 2 * X ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  have hD2'' := mul_le_mul_of_nonneg_left hD2' (by norm_num : (0 : ℝ) ≤ 1 + 1 / (1 / 1000))
  have hfin : (1 + 1 / 1000) * (2.2258 * δ * L ^ 2 * X ^ 2) + 0.0019 * δ * L ^ 2 * X ^ 2
      ≤ 2.23 * δ * L ^ 2 * X ^ 2 := by
    have : 0 ≤ δ * L ^ 2 * X ^ 2 := by positivity
    have e1 : (1 + 1 / 1000) * (2.2258 * δ * L ^ 2 * X ^ 2) + 0.0019 * δ * L ^ 2 * X ^ 2
        = 2.2299258 * (δ * L ^ 2 * X ^ 2) := by ring
    have e2 : 2.23 * δ * L ^ 2 * X ^ 2 = 2.23 * (δ * L ^ 2 * X ^ 2) := by ring
    rw [e1, e2]; linarith
  linarith

/-- U-5031: under RH, via Chirre-Hagen's Theorem 2, the `J_ψ` bound with 2.2258, Schoenfeld 1976
Corollary 1 and the `4 · 10^18` even check, a Goldbach number lies in `(x, x + 10.5 log² x)` for
every `x ≥ 2`. The paper has 123. -/
theorem goldbach_10_5
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 10.5 * Real.log x ^ 2 := by
  intro hRH x hx
  have hlog : 0.69 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  rcases le_or_gt x (2 * 10 ^ 18) with hs | hb
  · obtain ⟨n, hn, h1, h2'⟩ := small_of hE x hx hs
    exact ⟨n, hn, h1, by nlinarith⟩
  · have hx' : 1.1 * 10 ^ 18 ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hL : 41 ≤ Real.log x := log_ge_41 hx'
    set δ := 10.4 * Real.log x ^ 2 / x with hδ
    have hδpos : 0 < δ := by positivity
    have hδ13 : δ ≤ 1 / 10 ^ 13 := by
      have := threshold2 hx'
      have : δ ≤ 61.5 * Real.log x ^ 2 / x := by
        rw [hδ]; apply div_le_div_of_nonneg_right _ hxpos.le; nlinarith
      linarith
    have hsx : δ * √x < 1 := by
      have hc := log_cube_div_sqrt (by linarith : (10 : ℝ) ^ 18 ≤ x)
      have hsx0 : 0 < √x := Real.sqrt_pos.mpr hxpos
      have hss : √x * √x = x := Real.mul_self_sqrt hxpos.le
      have e0 : δ * √x * √x = 10.4 * Real.log x ^ 2 := by
        rw [mul_assoc, hss, hδ]; field_simp
      have e : δ * √x = 10.4 * (Real.log x ^ 2 / √x) := by
        rw [show 10.4 * (Real.log x ^ 2 / √x) = 10.4 * Real.log x ^ 2 / √x by ring,
          eq_div_iff hsx0.ne']
        exact e0
      have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith
      have : Real.log x ^ 2 / √x ≤ 7.5 / 10 ^ 5 :=
        le_trans (div_le_div_of_nonneg_right h23 hsx0.le) hc
      rw [e]; linarith
    obtain ⟨n, hn, h1, h2'⟩ := large_c_of (c := 2.23) (H := 10.4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (thetaRel_of_schoenfeld (hS hRH)) x hx'
      (fun X hX1 hX2 => by
        rw [← hδ]
        have hX : 5 * 10 ^ 17 ≤ X := by linarith
        have hsX : δ * √X < 1 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX2) hδpos.le) hsx
        exact Jtheta_le_223 (h2 hRH X δ (by linarith) hδpos hδ13) hX hδpos hδ13 hsX)
    exact ⟨n, hn, h1, by nlinarith⟩

end LeanLab.ChirreHagen2025

