module

public import Mathlib
public import LeanLab.HeathBrown1985.FromSiegelWalfisz
public import LeanLab.Ternary.Statements

/-!
P0096 Heath-Brown 1985, Corollary 2, Vinogradov's three primes theorem in its ineffective
form: every sufficiently large odd number is a sum of three primes, derived here from
Theorem 1, so from the Siegel-Walfisz theorem 1.1 alone, with zero sorry.
Route: for odd `n` take `x = 2n/7` and the primes `p` with `n/7 + 1 < p ≤ 3n/7 − 1`; then
`n − p` runs over distinct even `m` with `2x < m ≤ 3x`, so
`Σ_p log p · N₂(n − p) ≥ 2e⁻⁶ x Σ_p log p − log n · Σ_m |N₂(m) − x𝔖(m)|`, and the first term
wins by Theorem 1 with `C = 2` and the prime number theorem, which is 1.1 with `k = 1`,
plus Mathlib's `|ψ − θ| ≤ 2√x log x`.
AI-written Lean code, Claude, run 20261017T0603Z-10326. Checked only by the Lean kernel.
Ternary Goldbach for all odd n > 5 is Helfgott 2013; binary Goldbach is OPEN.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset Filter Real
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

/-- The lab's `psi y 1 0` is Mathlib's Chebyshev `ψ y`. -/
theorem psi_one_eq (y : ℝ) : psi y 1 0 = Chebyshev.psi y := by
  unfold psi Chebyshev.psi
  have : (Icc 1 ⌊y⌋₊).filter (fun n => n % 1 = 0 % 1) = Ioc 0 ⌊y⌋₊ := by
    ext n
    simp only [mem_filter, mem_Icc, mem_Ioc, Nat.mod_one, and_true]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [this]

/-- `θ(y₂) − θ(y₁)` is the sum of `log p` over primes in `(⌊y₁⌋, ⌊y₂⌋]`. -/
theorem theta_sub_eq (y₁ y₂ : ℝ) (h : ⌊y₁⌋₊ ≤ ⌊y₂⌋₊) :
    Chebyshev.theta y₂ - Chebyshev.theta y₁ =
      ∑ p ∈ (Ioc ⌊y₁⌋₊ ⌊y₂⌋₊).filter Nat.Prime, Real.log p := by
  unfold Chebyshev.theta
  rw [sum_filter, sum_filter, sum_filter, ← sum_Ioc_consecutive _ (Nat.zero_le _) h]
  ring

/-- The deterministic step: the bounds force `n` to be a sum of three primes. -/
theorem ternary_of_bounds (n : ℕ) (hodd : Odd n) (K1 : ℝ) (hn : (56 : ℝ) ≤ n)
    (hθ : (n : ℝ) / 7 ≤ ∑ p ∈ (Ioc ⌊(n : ℝ) / 7 + 1⌋₊ ⌊3 * (n : ℝ) / 7 - 1⌋₊).filter Nat.Prime,
      Real.log p)
    (hT1 : ∑ m ∈ (range (⌊3 * (2 * (n : ℝ) / 7)⌋₊ + 1)).filter
        (fun m : ℕ => 2 * (2 * (n : ℝ) / 7) < (m : ℝ)),
        |N2 (2 * (n : ℝ) / 7) m - 2 * (n : ℝ) / 7 * singular m| ≤
      K1 * (2 * (n : ℝ) / 7) ^ 2 * Real.log (2 * (n : ℝ) / 7) ^ (-(2 : ℝ)))
    (hwin : Real.log n * (K1 * (2 * (n : ℝ) / 7) ^ 2 * Real.log (2 * (n : ℝ) / 7) ^ (-(2 : ℝ))) <
      2 * Real.exp (-6) * (2 * (n : ℝ) / 7) * ((n : ℝ) / 7)) :
    IsTernarySum n := by
  set x : ℝ := 2 * (n : ℝ) / 7 with hxdef
  set P := (Ioc ⌊(n : ℝ) / 7 + 1⌋₊ ⌊3 * (n : ℝ) / 7 - 1⌋₊).filter Nat.Prime with hPdef
  set T := (range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ)) with hTdef
  have hn0 : (0 : ℝ) < n := by linarith
  have hx0 : 0 ≤ x := by positivity
  -- the members of P
  have hPmem : ∀ p ∈ P, p.Prime ∧ (n : ℝ) / 7 + 1 < p ∧ (p : ℝ) ≤ 3 * (n : ℝ) / 7 - 1 := by
    intro p hp
    obtain ⟨hI, hpr⟩ := mem_filter.mp hp
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hI
    refine ⟨hpr, ?_, ?_⟩
    · exact Nat.lt_of_floor_lt h1
    · exact (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
  have hpn : ∀ p ∈ P, p ≤ n := by
    intro p hp
    have := (hPmem p hp).2.2
    have : (p : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hmT : ∀ p ∈ P, n - p ∈ T := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := hPmem p hp
    have hc : ((n - p : ℕ) : ℝ) = n - p := Nat.cast_sub (hpn p hp)
    rw [hTdef, mem_filter, mem_range]
    constructor
    · have : ((n - p : ℕ) : ℝ) ≤ 3 * x := by rw [hc, hxdef]; linarith
      have := Nat.le_floor this
      omega
    · rw [hc, hxdef]; linarith
  have heven : ∀ p ∈ P, Even (n - p) := by
    intro p hp
    obtain ⟨hpr, h1, -⟩ := hPmem p hp
    have hp2 : p ≠ 2 := by
      intro h; rw [h] at h1; push_cast at h1; linarith
    have hpodd : Odd p := hpr.odd_of_ne_two hp2
    exact Nat.Odd.sub_odd hodd hpodd
  -- the weighted count
  set S := ∑ p ∈ P, Real.log p * N2 x (n - p) with hS
  have hlogp : ∀ p ∈ P, 0 ≤ Real.log p ∧ Real.log p ≤ Real.log n := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hPmem p hp).1.one_lt.le
    exact ⟨Real.log_nonneg hp1, Real.log_le_log (by linarith) (by exact_mod_cast hpn p hp)⟩
  have hterm : ∀ p ∈ P, Real.log p * (2 * Real.exp (-6) * x) -
      Real.log n * |N2 x (n - p) - x * singular (n - p)| ≤ Real.log p * N2 x (n - p) := by
    intro p hp
    obtain ⟨hl0, hln⟩ := hlogp p hp
    have hsg := singular_ge (heven p hp)
    have h1 : x * (2 * Real.exp (-6)) ≤ x * singular (n - p) :=
      mul_le_mul_of_nonneg_left hsg hx0
    have h2 : x * singular (n - p) - |N2 x (n - p) - x * singular (n - p)| ≤ N2 x (n - p) := by
      have := neg_abs_le (N2 x (n - p) - x * singular (n - p)); linarith
    have h3 : Real.log p * |N2 x (n - p) - x * singular (n - p)| ≤
        Real.log n * |N2 x (n - p) - x * singular (n - p)| :=
      mul_le_mul_of_nonneg_right hln (abs_nonneg _)
    have h4 : Real.log p * (x * (2 * Real.exp (-6))) ≤ Real.log p * (x * singular (n - p)) :=
      mul_le_mul_of_nonneg_left h1 hl0
    have h5 : Real.log p * (x * singular (n - p) - |N2 x (n - p) - x * singular (n - p)|) ≤
        Real.log p * N2 x (n - p) := mul_le_mul_of_nonneg_left h2 hl0
    nlinarith
  have hsumT : ∑ p ∈ P, |N2 x (n - p) - x * singular (n - p)| ≤
      ∑ m ∈ T, |N2 x m - x * singular m| := by
    have hinj : Set.InjOn (fun p => n - p) ↑P := by
      intro a ha b hb hab
      have := hpn a ha; have := hpn b hb
      simp only at hab; omega
    rw [← sum_image (f := fun m => |N2 x m - x * singular m|) hinj]
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
      exact hmT p hp
    · intro _ _ _; exact abs_nonneg _
  have hSlow : 2 * Real.exp (-6) * x * ∑ p ∈ P, Real.log p -
      Real.log n * ∑ m ∈ T, |N2 x m - x * singular m| ≤ S := by
    have := sum_le_sum hterm
    rw [sum_sub_distrib, ← sum_mul, ← mul_sum] at this
    have hln0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have := mul_le_mul_of_nonneg_left hsumT hln0
    nlinarith
  have hSpos : 0 < S := by
    have e1 : 2 * Real.exp (-6) * x * ((n : ℝ) / 7) ≤ 2 * Real.exp (-6) * x * ∑ p ∈ P, Real.log p :=
      mul_le_mul_of_nonneg_left hθ (by positivity)
    have hln0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have e2 := mul_le_mul_of_nonneg_left hT1 hln0
    linarith
  -- a positive term
  have h0lt : ∑ p ∈ P, (0 : ℝ) < ∑ p ∈ P, Real.log p * N2 x (n - p) := by
    rw [sum_const_zero]; exact hSpos
  obtain ⟨p, hp, hpos⟩ := exists_lt_of_sum_lt h0lt
  have hN2 : N2 x (n - p) ≠ 0 := by
    intro h; rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
  obtain ⟨q, hq, -⟩ := exists_ne_zero_of_sum_ne_zero hN2
  obtain ⟨hqr, hqp, hqm, -⟩ := mem_filter.mp hq
  have hqle : q ≤ n - p := Nat.lt_succ_iff.mp (mem_range.mp hqr)
  refine ⟨p, q, n - p - q, (hPmem p hp).1, hqp, hqm, ?_⟩
  have := hpn p hp
  omega


/-! ### The prime count on `(n/7 + 1, 3n/7 − 1]` from 1.1 with `k = 1` -/

theorem psi_bounds_of_SW {c K : ℝ}
    (hK : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ Real.log x ^ (1 : ℝ) →
      |psi x k l - x / (Nat.totient k : ℝ)| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (y : ℝ) (hy : 2 ≤ y) (hly : 1 ≤ Real.log y) :
    |Chebyshev.psi y - y| ≤ K * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
  have := hK y hy 1 0 le_rfl (Nat.coprime_zero_left 1 |>.mpr rfl) (by
    rw [Real.rpow_one]; exact_mod_cast hly)
  rwa [psi_one_eq, Nat.totient_one, Nat.cast_one, div_one] at this

theorem theta_window_ge {c K ε : ℝ} (hε : 0 ≤ ε) (hKε : |K| * ε ≤ 1 / 28)
    (hK : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ Real.log x ^ (1 : ℝ) →
      |psi x k l - x / (Nat.totient k : ℝ)| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (t : ℝ) (ht : 56 ≤ t) (hl1 : 1 ≤ Real.log (t / 7 + 1))
    (hE1 : Real.exp (-c * Real.sqrt (Real.log (t / 7 + 1))) ≤ ε)
    (hE2 : Real.exp (-c * Real.sqrt (Real.log (3 * t / 7 - 1))) ≤ ε)
    (hsq : 2 * Real.sqrt (3 * t / 7 - 1) * Real.log (3 * t / 7 - 1) ≤ t / 28) :
    t / 7 ≤ ∑ p ∈ (Ioc ⌊t / 7 + 1⌋₊ ⌊3 * t / 7 - 1⌋₊).filter Nat.Prime, Real.log p := by
  set y₁ := t / 7 + 1
  set y₂ := 3 * t / 7 - 1
  have hy12 : y₁ ≤ y₂ := by simp only [y₁, y₂]; linarith
  have hy1 : 2 ≤ y₁ := by simp only [y₁]; linarith
  have hl2 : 1 ≤ Real.log y₂ := hl1.trans (Real.log_le_log (by linarith) hy12)
  rw [← theta_sub_eq y₁ y₂ (Nat.floor_le_floor hy12)]
  have h1 := psi_bounds_of_SW hK y₁ hy1 hl1
  have h2 := psi_bounds_of_SW hK y₂ (by linarith) hl2
  have h3 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (show 1 ≤ y₂ by linarith)
  have h4 := Chebyshev.theta_le_psi y₁
  have e1 : K * y₁ * Real.exp (-c * Real.sqrt (Real.log y₁)) ≤ y₁ / 28 := by
    calc K * y₁ * Real.exp (-c * Real.sqrt (Real.log y₁))
        ≤ |K| * y₁ * ε := by
          have : 0 ≤ y₁ := by linarith
          have h0 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log y₁)) := (Real.exp_pos _).le
          calc K * y₁ * Real.exp (-c * Real.sqrt (Real.log y₁))
              ≤ |K| * y₁ * Real.exp (-c * Real.sqrt (Real.log y₁)) := by
                apply mul_le_mul_of_nonneg_right _ h0
                exact mul_le_mul_of_nonneg_right (le_abs_self K) this
            _ ≤ |K| * y₁ * ε := mul_le_mul_of_nonneg_left hE1 (by positivity)
      _ = (|K| * ε) * y₁ := by ring
      _ ≤ (1 / 28) * y₁ := mul_le_mul_of_nonneg_right hKε (by linarith)
      _ = y₁ / 28 := by ring
  have e2 : K * y₂ * Real.exp (-c * Real.sqrt (Real.log y₂)) ≤ y₂ / 28 := by
    calc K * y₂ * Real.exp (-c * Real.sqrt (Real.log y₂))
        ≤ |K| * y₂ * ε := by
          have : 0 ≤ y₂ := by linarith
          have h0 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log y₂)) := (Real.exp_pos _).le
          calc K * y₂ * Real.exp (-c * Real.sqrt (Real.log y₂))
              ≤ |K| * y₂ * Real.exp (-c * Real.sqrt (Real.log y₂)) := by
                apply mul_le_mul_of_nonneg_right _ h0
                exact mul_le_mul_of_nonneg_right (le_abs_self K) this
            _ ≤ |K| * y₂ * ε := mul_le_mul_of_nonneg_left hE2 (by positivity)
      _ = (|K| * ε) * y₂ := by ring
      _ ≤ (1 / 28) * y₂ := mul_le_mul_of_nonneg_right hKε (by linarith)
      _ = y₂ / 28 := by ring
  have a1 := (abs_le.mp h1).2
  have a2 := (abs_le.mp h2).1
  have a3 := (abs_le.mp h3).2
  simp only [y₁, y₂] at *
  linarith


/-! ### Corollary 2 from Siegel-Walfisz -/

theorem win_of_large (K1 t : ℝ) (ht : 56 ≤ t)
    (hL : 2 * |K1| * Real.exp 6 + 1 ≤ Real.log (2 * t / 7)) :
    Real.log t * (K1 * (2 * t / 7) ^ 2 * Real.log (2 * t / 7) ^ (-(2 : ℝ))) <
      2 * Real.exp (-6) * (2 * t / 7) * (t / 7) := by
  set x := 2 * t / 7 with hx
  set L' := Real.log x with hL'
  have hx0 : 0 < x := by rw [hx]; linarith
  have hL1 : 1 ≤ L' := by
    have : 0 ≤ 2 * |K1| * Real.exp 6 := by positivity
    linarith
  have hL0 : 0 < L' := by linarith
  have hlogt : Real.log t ≤ 2 * L' := by
    have h1 : t ≤ x ^ 2 := by rw [hx]; nlinarith
    have := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hrp : L' ^ (-(2 : ℝ)) = 1 / L' ^ 2 := by
    rw [Real.rpow_neg hL0.le, Real.rpow_two, one_div]
  rw [hrp]
  have hexp : Real.exp (-6) * Real.exp 6 = 1 := by rw [← Real.exp_add]; simp
  have hkey : 2 * |K1| < Real.exp (-6) * L' := by
    have h1 : Real.exp (-6) * (2 * |K1| * Real.exp 6 + 1) ≤ Real.exp (-6) * L' :=
      mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
    have h2 : Real.exp (-6) * (2 * |K1| * Real.exp 6 + 1) = 2 * |K1| + Real.exp (-6) := by
      have : Real.exp (-6) * (2 * |K1| * Real.exp 6) = 2 * |K1| * (Real.exp (-6) * Real.exp 6) := by
        ring
      rw [mul_add, this, hexp]; ring
    have := Real.exp_pos (-6)
    linarith
  have hx2 : 0 < x ^ 2 := by positivity
  calc Real.log t * (K1 * x ^ 2 * (1 / L' ^ 2))
      ≤ Real.log t * (|K1| * x ^ 2 * (1 / L' ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hlogt0
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_abs_self K1) hx2.le
    _ ≤ (2 * L') * (|K1| * x ^ 2 * (1 / L' ^ 2)) :=
        mul_le_mul_of_nonneg_right hlogt (by positivity)
    _ = (2 * |K1|) * x ^ 2 / L' := by field_simp
    _ < (Real.exp (-6) * L') * x ^ 2 / L' := by
        apply div_lt_div_of_pos_right _ hL0
        exact mul_lt_mul_of_pos_right hkey hx2
    _ = Real.exp (-6) * x ^ 2 := by field_simp
    _ = 2 * Real.exp (-6) * x * (t / 7) := by rw [hx]; ring

/-- **Heath-Brown 1985, Corollary 2, Vinogradov's theorem, from the Siegel-Walfisz theorem
alone**, zero sorry: every sufficiently large odd number is a sum of three primes. The bound
is ineffective, as Siegel-Walfisz is. -/
theorem corollary2_of_siegelWalfisz (hSW : SiegelWalfisz) : Corollary2 := by
  obtain ⟨c, hc, K, hK⟩ := hSW 1 one_pos
  obtain ⟨K1, hK1⟩ := theorem1_of_siegelWalfisz hSW 2 two_pos
  set ε : ℝ := 1 / (28 * (|K| + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hKε : |K| * ε ≤ 1 / 28 := by
    rw [hεdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg K]
  have G1 : ∀ᶠ y in atTop, Real.exp (-c * Real.sqrt (Real.log y)) ≤ ε := by
    have h : Tendsto (fun y => Real.exp (-(c * Real.sqrt (Real.log y)))) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hc)
    filter_upwards [h.eventually (Iic_mem_nhds hε)] with y hy
    simpa [neg_mul] using hy
  have G2 : ∀ᶠ y in atTop, 2 * Real.sqrt y * Real.log y ≤ y / 14 := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / 28 by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hy
    have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    nlinarith
  have G3 : ∀ᶠ y in atTop, 1 ≤ Real.log y := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hf1 : Tendsto (fun t : ℝ => t / 7 + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_id.atTop_div_const (by norm_num))
  have hf2 : Tendsto (fun t : ℝ => 3 * t / 7 - 1) atTop atTop := by
    have := tendsto_atTop_add_const_right _ (-1)
      ((tendsto_id.const_mul_atTop (show (0 : ℝ) < 3 by norm_num)).atTop_div_const
        (show (0 : ℝ) < 7 by norm_num))
    refine this.congr (fun t => ?_)
    simp only [id]; ring
  have hf3 : Tendsto (fun t : ℝ => 2 * t / 7) atTop atTop :=
    (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)).atTop_div_const
      (show (0 : ℝ) < 7 by norm_num)
  have G4 : ∀ᶠ t in atTop, 2 * |K1| * Real.exp 6 + 1 ≤ Real.log (2 * t / 7) :=
    (Real.tendsto_log_atTop.comp hf3).eventually_ge_atTop _
  have hev : ∀ᶠ t : ℝ in atTop, 56 ≤ t ∧ 1 ≤ Real.log (t / 7 + 1) ∧
      Real.exp (-c * Real.sqrt (Real.log (t / 7 + 1))) ≤ ε ∧
      Real.exp (-c * Real.sqrt (Real.log (3 * t / 7 - 1))) ≤ ε ∧
      2 * Real.sqrt (3 * t / 7 - 1) * Real.log (3 * t / 7 - 1) ≤ t / 28 ∧
      2 * |K1| * Real.exp 6 + 1 ≤ Real.log (2 * t / 7) := by
    filter_upwards [eventually_ge_atTop (56 : ℝ), hf1.eventually G3, hf1.eventually G1,
      hf2.eventually G1, hf2.eventually G2, G4] with t h1 h2 h3 h4 h5 h6
    refine ⟨h1, h2, h3, h4, ?_, h6⟩
    have : (3 * t / 7 - 1) / 14 ≤ t / 28 := by linarith
    exact h5.trans this
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨N0, fun n hodd hn => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hN0 n hn
  exact ternary_of_bounds n hodd K1 h1 (theta_window_ge hε.le hKε hK (n : ℝ) h1 h2 h3 h4 h5)
    (hK1 (2 * (n : ℝ) / 7) (by linarith)) (win_of_large K1 n h1 h6)


/-- The lab's cited P0003 Vinogradov 1937 statement, `∃ C, TernaryAbove C`, now follows from
Siegel-Walfisz with zero sorry. -/
theorem vinogradov_of_siegelWalfisz (hSW : SiegelWalfisz) : ∃ C : ℝ, Ternary.TernaryAbove C := by
  obtain ⟨N, hN⟩ := corollary2_of_siegelWalfisz hSW
  exact ⟨N, fun n hodd hn => hN n hodd (by exact_mod_cast hn)⟩

end LeanLab.HeathBrown1985
