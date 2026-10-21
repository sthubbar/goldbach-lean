module

public import Mathlib
public import LeanLab.HeathBrown1985.Vinogradov

/-!
P0096 Heath-Brown 1985, Corollary 3: there are infinitely many sets of three distinct primes
in arithmetic progression. Derived here from Theorem 1, so from the Siegel-Walfisz theorem 1.1
alone, with no gap.
Route: for large t take the primes q with t + 1 < q ≤ 3t/2 − 1, so m = 2q runs over distinct
even m with 2t < m ≤ 3t. If N₂(t, 2q) = 0 for all of them, then
2e⁻⁶ t Σ_q log q ≤ Σ_q log q · |N₂(t, 2q) − t𝔖(2q)| ≤ log(3t/2) · Σ_m |N₂(t, m) − t𝔖(m)|,
which Theorem 1 with C = 2 and the prime number theorem forbid. So some p ≤ t has
p + p' = 2q with p' prime, and p < q < p' is a three term progression with d = q − p > 0.
AI-written Lean code, Claude, run 20261017T0903Z-2557. Checked only by the Lean kernel.
Green-Tao 2008 gives progressions of every length; binary Goldbach is OPEN.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset Filter Real
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

/-- The prime weight on `(t + 1, 3t/2 − 1]` from 1.1 with `k = 1`. -/
theorem theta_window_ge' {c K ε : ℝ} (hε : 0 ≤ ε) (hKε : |K| * ε ≤ 1 / 28)
    (hK : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ Real.log x ^ (1 : ℝ) →
      |psi x k l - x / (Nat.totient k : ℝ)| ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (t : ℝ) (ht : 16 ≤ t) (hl1 : 1 ≤ Real.log (t + 1))
    (hE1 : Real.exp (-c * Real.sqrt (Real.log (t + 1))) ≤ ε)
    (hE2 : Real.exp (-c * Real.sqrt (Real.log (3 * t / 2 - 1))) ≤ ε)
    (hsq : 2 * Real.sqrt (3 * t / 2 - 1) * Real.log (3 * t / 2 - 1) ≤ t / 28) :
    t / 4 ≤ ∑ p ∈ (Ioc ⌊t + 1⌋₊ ⌊3 * t / 2 - 1⌋₊).filter Nat.Prime, Real.log p := by
  set y₁ := t + 1
  set y₂ := 3 * t / 2 - 1
  have hy12 : y₁ ≤ y₂ := by simp only [y₁, y₂]; linarith
  have hy1 : 2 ≤ y₁ := by simp only [y₁]; linarith
  have hl2 : 1 ≤ Real.log y₂ := hl1.trans (Real.log_le_log (by linarith) hy12)
  rw [← theta_sub_eq y₁ y₂ (Nat.floor_le_floor hy12)]
  have h1 := psi_bounds_of_SW hK y₁ hy1 hl1
  have h2 := psi_bounds_of_SW hK y₂ (by linarith) hl2
  have h3 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (show 1 ≤ y₂ by linarith)
  have h4 := Chebyshev.theta_le_psi y₁
  have e : ∀ y : ℝ, 0 ≤ y → Real.exp (-c * Real.sqrt (Real.log y)) ≤ ε →
      K * y * Real.exp (-c * Real.sqrt (Real.log y)) ≤ y / 28 := by
    intro y hy hE
    have h0 : 0 ≤ Real.exp (-c * Real.sqrt (Real.log y)) := (Real.exp_pos _).le
    calc K * y * Real.exp (-c * Real.sqrt (Real.log y))
        ≤ |K| * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
          apply mul_le_mul_of_nonneg_right _ h0
          exact mul_le_mul_of_nonneg_right (le_abs_self K) hy
      _ ≤ |K| * y * ε := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = (|K| * ε) * y := by ring
      _ ≤ (1 / 28) * y := mul_le_mul_of_nonneg_right hKε hy
      _ = y / 28 := by ring
  have e1 := e y₁ (by linarith) hE1
  have e2 := e y₂ (by linarith) hE2
  have a1 := (abs_le.mp h1).2
  have a2 := (abs_le.mp h2).1
  have a3 := (abs_le.mp h3).2
  simp only [y₁, y₂] at *
  linarith

/-- The deterministic step: the bounds force a three term progression of primes whose middle
term exceeds `t`. -/
theorem ap3_of_bounds (t : ℝ) (K1 : ℝ) (ht : 16 ≤ t)
    (hθ : t / 4 ≤ ∑ p ∈ (Ioc ⌊t + 1⌋₊ ⌊3 * t / 2 - 1⌋₊).filter Nat.Prime, Real.log p)
    (hT1 : ∑ m ∈ (range (⌊3 * t⌋₊ + 1)).filter (fun m : ℕ => 2 * t < (m : ℝ)),
        |N2 t m - t * singular m| ≤ K1 * t ^ 2 * Real.log t ^ (-(2 : ℝ)))
    (hwin : Real.log (3 * t / 2) * (K1 * t ^ 2 * Real.log t ^ (-(2 : ℝ))) <
      2 * Real.exp (-6) * t * (t / 4)) :
    ∃ p d : ℕ, p.Prime ∧ (p + d).Prime ∧ (p + 2 * d).Prime ∧ 0 < d ∧ t < (p + d : ℕ) := by
  set P := (Ioc ⌊t + 1⌋₊ ⌊3 * t / 2 - 1⌋₊).filter Nat.Prime with hPdef
  set T := (range (⌊3 * t⌋₊ + 1)).filter (fun m : ℕ => 2 * t < (m : ℝ)) with hTdef
  have ht0 : 0 ≤ t := by linarith
  have hPmem : ∀ q ∈ P, q.Prime ∧ t + 1 < q ∧ (q : ℝ) ≤ 3 * t / 2 - 1 := by
    intro q hq
    obtain ⟨hI, hpr⟩ := mem_filter.mp hq
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hI
    exact ⟨hpr, Nat.lt_of_floor_lt h1, (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))⟩
  have hmT : ∀ q ∈ P, 2 * q ∈ T := by
    intro q hq
    obtain ⟨-, h1, h2⟩ := hPmem q hq
    rw [hTdef, mem_filter, mem_range]
    push_cast
    constructor
    · have : ((2 * q : ℕ) : ℝ) ≤ 3 * t := by push_cast; linarith
      have := Nat.le_floor this
      omega
    · linarith
  by_contra hno
  push_neg at hno
  -- every N₂(t, 2q) vanishes
  have hzero : ∀ q ∈ P, N2 t (2 * q) = 0 := by
    intro q hq
    by_contra hne
    obtain ⟨p, hp, -⟩ := exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨hpr, hpp, hpm, hpt⟩ := mem_filter.mp hp
    have hple : p ≤ 2 * q := Nat.lt_succ_iff.mp (mem_range.mp hpr)
    obtain ⟨hq', hq1, -⟩ := hPmem q hq
    have hpq : p < q := by
      have : (p : ℝ) < q := by linarith
      exact_mod_cast this
    have := hno p (q - p) hpp (by rwa [Nat.add_sub_cancel' hpq.le])
      (by rwa [show p + 2 * (q - p) = 2 * q - p by omega]) (by omega)
    rw [Nat.add_sub_cancel' hpq.le] at this
    linarith
  have hlogq : ∀ q ∈ P, 0 ≤ Real.log q ∧ Real.log q ≤ Real.log (3 * t / 2) := by
    intro q hq
    obtain ⟨hq', -, h2⟩ := hPmem q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq'.one_lt.le
    exact ⟨Real.log_nonneg hq1, Real.log_le_log (by linarith) (by linarith)⟩
  have hterm : ∀ q ∈ P, Real.log q * (2 * Real.exp (-6) * t) ≤
      Real.log (3 * t / 2) * |N2 t (2 * q) - t * singular (2 * q)| := by
    intro q hq
    obtain ⟨hl0, hln⟩ := hlogq q hq
    have hsg := singular_ge (even_two_mul q)
    have hs0 : 0 ≤ t * singular (2 * q) :=
      mul_nonneg ht0 (le_trans (by positivity) hsg)
    rw [hzero q hq, zero_sub, abs_neg, abs_of_nonneg hs0]
    calc Real.log q * (2 * Real.exp (-6) * t) ≤ Real.log q * (t * singular (2 * q)) := by
          apply mul_le_mul_of_nonneg_left _ hl0; nlinarith
      _ ≤ Real.log (3 * t / 2) * (t * singular (2 * q)) :=
          mul_le_mul_of_nonneg_right hln (by have := Real.exp_pos (-6); nlinarith)
  have hsumT : ∑ q ∈ P, |N2 t (2 * q) - t * singular (2 * q)| ≤
      ∑ m ∈ T, |N2 t m - t * singular m| := by
    have hinj : Set.InjOn (fun q => 2 * q) ↑P := by
      intro a _ b _ hab; simp only at hab; omega
    rw [← sum_image (f := fun m => |N2 t m - t * singular m|) hinj]
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hm
      exact hmT q hq
    · intro _ _ _; exact abs_nonneg _
  have hL0 : 0 ≤ Real.log (3 * t / 2) := Real.log_nonneg (by linarith)
  have hA := sum_le_sum hterm
  rw [← sum_mul, ← mul_sum] at hA
  have hB := mul_le_mul_of_nonneg_left (hsumT.trans hT1) hL0
  have hC : 2 * Real.exp (-6) * t * (t / 4) ≤ (∑ q ∈ P, Real.log q) * (2 * Real.exp (-6) * t) := by
    have := mul_le_mul_of_nonneg_right hθ (show 0 ≤ 2 * Real.exp (-6) * t by positivity)
    linarith
  linarith

theorem win3_of_large (K1 t : ℝ) (ht : 16 ≤ t)
    (hL : 4 * |K1| * Real.exp 6 + 1 ≤ Real.log t) :
    Real.log (3 * t / 2) * (K1 * t ^ 2 * Real.log t ^ (-(2 : ℝ))) <
      2 * Real.exp (-6) * t * (t / 4) := by
  set L' := Real.log t with hL'
  have hL1 : 1 ≤ L' := by
    have : 0 ≤ 4 * |K1| * Real.exp 6 := by positivity
    linarith
  have hL0 : 0 < L' := by linarith
  have hlog : Real.log (3 * t / 2) ≤ 2 * L' := by
    have h1 : 3 * t / 2 ≤ t ^ 2 := by nlinarith
    have := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlog0 : 0 ≤ Real.log (3 * t / 2) := Real.log_nonneg (by linarith)
  have hrp : L' ^ (-(2 : ℝ)) = 1 / L' ^ 2 := by
    rw [Real.rpow_neg hL0.le, Real.rpow_two, one_div]
  rw [hrp]
  have hexp : Real.exp (-6) * Real.exp 6 = 1 := by rw [← Real.exp_add]; simp
  have hkey : 4 * |K1| < Real.exp (-6) * L' := by
    have h1 : Real.exp (-6) * (4 * |K1| * Real.exp 6 + 1) ≤ Real.exp (-6) * L' :=
      mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
    have h2 : Real.exp (-6) * (4 * |K1| * Real.exp 6 + 1) = 4 * |K1| + Real.exp (-6) := by
      have : Real.exp (-6) * (4 * |K1| * Real.exp 6) = 4 * |K1| * (Real.exp (-6) * Real.exp 6) := by
        ring
      rw [mul_add, this, hexp]; ring
    have := Real.exp_pos (-6)
    linarith
  have ht2 : 0 < t ^ 2 := by positivity
  calc Real.log (3 * t / 2) * (K1 * t ^ 2 * (1 / L' ^ 2))
      ≤ Real.log (3 * t / 2) * (|K1| * t ^ 2 * (1 / L' ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hlog0
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_abs_self K1) ht2.le
    _ ≤ (2 * L') * (|K1| * t ^ 2 * (1 / L' ^ 2)) :=
        mul_le_mul_of_nonneg_right hlog (by positivity)
    _ = (4 * |K1|) * t ^ 2 / L' / 2 := by field_simp; ring
    _ < (Real.exp (-6) * L') * t ^ 2 / L' / 2 := by
        apply div_lt_div_of_pos_right _ (by norm_num)
        apply div_lt_div_of_pos_right _ hL0
        exact mul_lt_mul_of_pos_right hkey ht2
    _ = 2 * Real.exp (-6) * t * (t / 4) := by field_simp; ring

/-- **Heath-Brown 1985, Corollary 3, from the Siegel-Walfisz theorem alone**, fully proved:
infinitely many three term progressions of primes. -/
theorem corollary3_of_siegelWalfisz (hSW : SiegelWalfisz) : Corollary3 := by
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
  have G2 : ∀ᶠ y in atTop, 2 * Real.sqrt y * Real.log y ≤ y / 42 := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / 84 by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hy
    have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    nlinarith
  have G3 : ∀ᶠ y in atTop, 1 ≤ Real.log y := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hf1 : Tendsto (fun t : ℝ => t + 1) atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_id
  have hf2 : Tendsto (fun t : ℝ => 3 * t / 2 - 1) atTop atTop := by
    have := tendsto_atTop_add_const_right _ (-1)
      ((tendsto_id.const_mul_atTop (show (0 : ℝ) < 3 by norm_num)).atTop_div_const
        (show (0 : ℝ) < 2 by norm_num))
    refine this.congr (fun t => ?_)
    simp only [id]; ring
  have G4 : ∀ᶠ t in atTop, 4 * |K1| * Real.exp 6 + 1 ≤ Real.log t :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have hev : ∀ᶠ t : ℝ in atTop, 16 ≤ t ∧ 1 ≤ Real.log (t + 1) ∧
      Real.exp (-c * Real.sqrt (Real.log (t + 1))) ≤ ε ∧
      Real.exp (-c * Real.sqrt (Real.log (3 * t / 2 - 1))) ≤ ε ∧
      2 * Real.sqrt (3 * t / 2 - 1) * Real.log (3 * t / 2 - 1) ≤ t / 28 ∧
      4 * |K1| * Real.exp 6 + 1 ≤ Real.log t := by
    filter_upwards [eventually_ge_atTop (16 : ℝ), hf1.eventually G3, hf1.eventually G1,
      hf2.eventually G1, hf2.eventually G2, G4] with t h1 h2 h3 h4 h5 h6
    refine ⟨h1, h2, h3, h4, ?_, h6⟩
    have : (3 * t / 2 - 1) / 42 ≤ t / 28 := by linarith
    exact h5.trans this
  obtain ⟨t0, ht0⟩ := eventually_atTop.mp hev
  -- the middle terms are unbounded
  have hunb : ∀ B : ℕ, ∃ p d : ℕ, p.Prime ∧ (p + d).Prime ∧ (p + 2 * d).Prime ∧ 0 < d ∧
      B < p + d := by
    intro B
    set t := max t0 (B : ℝ) + 16
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht0 t (by simp only [t]; linarith [le_max_left t0 (B : ℝ)])
    obtain ⟨p, d, hp, hpd, hp2d, hd, hlt⟩ := ap3_of_bounds t K1 h1
      (theta_window_ge' hε.le hKε hK t h1 h2 h3 h4 h5) (hK1 t (by linarith))
      (win3_of_large K1 t h1 h6)
    refine ⟨p, d, hp, hpd, hp2d, hd, ?_⟩
    have : (B : ℝ) < (p + d : ℕ) := by
      have : (B : ℝ) ≤ t := by simp only [t]; linarith [le_max_right t0 (B : ℝ)]
      linarith
    exact_mod_cast this
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image (fun s : ℕ × ℕ => s.1 + s.2)).bddAbove
  obtain ⟨p, d, hp, hpd, hp2d, hd, hlt⟩ := hunb B
  have : p + d ∈ (fun s : ℕ × ℕ => s.1 + s.2) ''
      {t : ℕ × ℕ | t.1.Prime ∧ (t.1 + t.2).Prime ∧ (t.1 + 2 * t.2).Prime ∧ 0 < t.2} :=
    ⟨(p, d), ⟨hp, hpd, hp2d, hd⟩, rfl⟩
  have := hB this
  omega

/-- All three corollaries of Heath-Brown 1985 from Siegel-Walfisz, fully proved. -/
theorem corollaries_of_siegelWalfisz (hSW : SiegelWalfisz) :
    Corollary1 ∧ Corollary2 ∧ Corollary3 :=
  ⟨corollary1_of_siegelWalfisz hSW, corollary2_of_siegelWalfisz hSW,
    corollary3_of_siegelWalfisz hSW⟩

end LeanLab.HeathBrown1985
