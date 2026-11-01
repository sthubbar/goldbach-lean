module

public import Mathlib
public import LeanLab.Dudek2014.Theorem1Small
public import LeanLab.Dudek2014.SigmaHSWDownstream

/-!
P0100 Dudek 2014, Theorem 1, Cramér's theorem, under RH, unit U-6722, CLOUD 20261020T2018Z-cloud50.

Dudek states Theorem 1 as Cramér's 1920 result and does not prove it; Section 2.4 sketches
`c = 3 + ε` for large `x`. The lab proves the stated form, with an explicit constant:
* `large_range`: under RH, CONDITIONAL ON `HSWN70 gZ`, for every `x ≥ 10^12` there are more
  than `√x` primes in `(x, x + 6 √x log x]`. Method of Section 2.2 with a wider window: Lemma 5
  from the PROVED Lemma 4, `lemma4_Zpatch`, at the centre `x + h`, `h = 3 √x log x`; the zero sum
  bound `sigma_gen`, the proof of `SigmaH.sigmaBd_of_hsw` for any `h` with `35 h ≤ x`; the prime
  powers bounded elementarily by `mass_gen`; then `Σ log p ≤ #primes · log(x + 2h)`.
* `Theorem1Small.small_range`: no RH, for `2 ≤ x < 10^12` with `c = 10^8`.
* `theorem1_of_RH_hsw`: Dudek's Theorem 1, the lab's `Statements.theorem1` conclusion with
  `c = 10^8`, for every `x ≥ 2`, under RH, CONDITIONAL ON `HSWN70 gZ` only.
KNOWN mathematics, Cramér 1920; the constant `10^8` is far from optimal and is not claimed new.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.Theorem1H
open Real Finset
open scoped ArithmeticFunction.vonMangoldt
open LeanLab.Dudek2014.Section22 (WS w lemma5_of)
open LeanLab.Dudek2014.SigmaT (rhoF fz Zr wgt wgt_le_inv_sq ne_of_large second_diff_small
  second_diff_large)
open LeanLab.Dudek2014.SigmaH (HSWN70 summable_fz summable_wgt split_bound weight_ratio)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ Zr_eq_Zreal Zpatch Zreal lemma4_Zpatch)

noncomputable section

variable {ι : Type*}

/-- **The page 5 zero sum bound for any `h` with `35 h ≤ x`**, CONDITIONAL ON `HSWN70`: the proof
of `SigmaH.sigmaBd_of_hsw` with `h = (2/π)√x log x` replaced by a general `h`. -/
theorem sigma_gen {γ : ι → ℝ} (hN : HSWN70 γ) {x h : ℝ} (hh0 : 0 < h) (h35 : 35 * h ≤ x) :
    |Zr γ (x + h) - 2 * Zr γ x + Zr γ (x - h)| ≤
      (2 * x * h / (π * √(x - h)) + 4 * h * (x + h) ^ (3 / 2 : ℝ) / (π * 2 * x)) *
        log (2 * x / h) := by
  have hx0 : 0 < x := by linarith
  have hhx : h < x := by linarith
  have hxh : 0 < x - h := by linarith
  set T := 2 * x / h with hTdef
  have hT : 70 ≤ T := by rw [hTdef, le_div_iff₀ hh0]; linarith
  set D : ι → ℂ := fun i =>
    fz (rhoF (γ i)) (x + h) - 2 * fz (rhoF (γ i)) x + fz (rhoF (γ i)) (x - h)
  have sa := summable_fz hN (by linarith : 0 < x + h)
  have sb := summable_fz hN hx0
  have sc := summable_fz hN hxh
  have eD : ∑' i, D i = (∑' i, fz (rhoF (γ i)) (x + h)) - 2 * (∑' i, fz (rhoF (γ i)) x)
      + ∑' i, fz (rhoF (γ i)) (x - h) := by
    rw [← tsum_mul_left, ← sa.tsum_sub (sb.mul_left 2), ← (sa.sub (sb.mul_left 2)).tsum_add sc]
  have e : Zr γ (x + h) - 2 * Zr γ x + Zr γ (x - h) = (∑' i, D i).re := by
    rw [eD]; unfold Zr; simp [Complex.add_re, Complex.sub_re]
  rw [e]
  set B := 4 * (x + h) ^ (3 / 2 : ℝ)
  have hB : 0 ≤ B := by positivity
  set a := h ^ 2 * (x - h) ^ (-1 / 2 : ℝ)
  have ha : 0 ≤ a := by positivity
  have hab : B ≤ 1.1 * a * T ^ 2 := weight_ratio hh0 h35
  have hDn : ∀ i, ‖D i‖ ≤ B * wgt γ i := fun i => by
    have := second_diff_large (γ i) hh0 hhx; unfold wgt; rw [mul_one_div]; exact this
  have hsumN : Summable (fun i => ‖D i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hDn ((summable_wgt hN).mul_left B)
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, ‖D i‖ ≤ T * log T / π * a + B * (log T / (π * T)) :=
    split_bound hN hT ha hB hab (fun i => ‖D i‖) (fun i _ => second_diff_small (γ i) hh0 hhx)
      (fun i hi => (hDn i).trans (by
        rw [← mul_one_div]; exact mul_le_mul_of_nonneg_left (wgt_le_inv_sq γ (ne_of_large hT hi)) hB))
  have htot := hsumN.tsum_le_of_sum_le hfin
  have hK : (x - h) ^ (-1 / 2 : ℝ) = 1 / √(x - h) := by
    rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hxh.le]
    exact (one_div _).symm
  have eq : T * log T / π * a + B * (log T / (π * T)) =
      (2 * x * h / (π * √(x - h)) + 4 * h * (x + h) ^ (3 / 2 : ℝ) / (π * 2 * x)) *
        log (2 * x / h) := by
    have hs : 0 < √(x - h) := Real.sqrt_pos.mpr hxh
    simp only [a, B, hK, hTdef]
    field_simp
  calc |(∑' i, D i).re| ≤ ‖∑' i, D i‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' i, ‖D i‖ := norm_tsum_le_tsum_norm hsumN
    _ ≤ _ := htot
    _ = _ := eq

/-- The weighted sum is at most the von Mangoldt sum over the window. -/
theorem WS_le {y h : ℝ} (hh0 : 0 < h) (hhy : h ≤ y) :
    WS y h ≤ ∑ n ∈ Ioc ⌊y - h⌋₊ ⌊y + h⌋₊, Λ n := by
  have hab : ⌊y - h⌋₊ ≤ ⌊y + h⌋₊ := Nat.floor_le_floor (by linarith)
  unfold WS
  rw [← Iic_union_Ioc_eq_Iic hab, sum_union (Iic_disjoint_Ioc le_rfl)]
  have hz : ∑ n ∈ Iic ⌊y - h⌋₊, Λ n * w y h n = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [mem_Iic] at hn
    have hnr : (n : ℝ) ≤ y - h := by
      have := Nat.floor_le (show 0 ≤ y - h by linarith)
      have : (n : ℝ) ≤ ⌊y - h⌋₊ := by exact_mod_cast hn
      linarith
    have hw : w y h n = 0 := by
      unfold w
      apply max_eq_left
      rw [sub_nonpos, le_div_iff₀ hh0, one_mul, abs_of_nonpos (by linarith)]
      linarith
    rw [hw, mul_zero]
  rw [hz, zero_add]
  apply sum_le_sum
  intro n _
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hw1 : w y h n ≤ 1 := by
    unfold w
    apply max_le (by norm_num)
    have : 0 ≤ |(n : ℝ) - y| / h := div_nonneg (abs_nonneg _) hh0.le
    linarith
  nlinarith [show 0 ≤ w y h n from le_max_left _ _]

/-- **The prime power mass in a window**, any length:
`Σ_{a < n ≤ b, n not prime} Λ(n) ≤ (log b / log 2)(log b / 2)(√b - √a + 1)`. PROVED. -/
theorem mass_gen {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun n => ¬ n.Prime), Λ n ≤
      Real.log b / Real.log 2 * (Real.log b / 2 * (√b - √a + 1)) := by
  classical
  have ha0 : 0 ≤ a := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hB1 : 1 ≤ ⌊b⌋₊ := Nat.le_floor (by exact_mod_cast hb1)
  have hBpos : (0 : ℝ) < ⌊b⌋₊ := by exact_mod_cast hB1
  have hlogB : Real.log ⌊b⌋₊ ≤ Real.log b := Real.log_le_log hBpos (Nat.floor_le (by linarith))
  have hlogB0 : 0 ≤ Real.log ⌊b⌋₊ := Real.log_nonneg (by exact_mod_cast hB1)
  have hlb0 : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hsq : √a ≤ √b := Real.sqrt_le_sqrt hab
  set K := Nat.log 2 ⌊b⌋₊ with hK
  set M := Real.log b / 2 * (√b - √a + 1) with hM
  have hM0 : 0 ≤ M := mul_nonneg (by linarith) (by linarith)
  have hmain := LeanLab.PrimePowerWindow.sum_nonprime_le ⌊a⌋₊ ⌊b⌋₊
  have hk : ∀ k ∈ Icc 2 K, Real.log ⌊b⌋₊ / k *
      (((Iic ⌊b⌋₊).filter (fun m => ⌊a⌋₊ < m ^ k ∧ m ^ k ≤ ⌊b⌋₊)).card : ℝ) ≤ M := by
    intro k hk
    rw [mem_Icc] at hk
    have hk1 : 1 ≤ k := by omega
    have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hc := LeanLab.PrimePowerWindow.count_le ha0 hab hk1
    have hm := LeanLab.PrimePowerWindow.rpow_sub_mono ha hab (r := 1 / (k : ℝ)) (s := 1 / 2)
      (by positivity) (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hm
    have hc2 : (((Iic ⌊b⌋₊).filter (fun m => ⌊a⌋₊ < m ^ k ∧ m ^ k ≤ ⌊b⌋₊)).card : ℝ) ≤
        √b - √a + 1 := by
      have : ((((Iic ⌊b⌋₊).filter (fun m => ⌊a⌋₊ < m ^ k ∧ m ^ k ≤ ⌊b⌋₊)).card : ℕ) : ℝ) ≤
          √b - √a + 1 := by linarith
      exact_mod_cast this
    have hc0 : (0 : ℝ) ≤ (((Iic ⌊b⌋₊).filter (fun m => ⌊a⌋₊ < m ^ k ∧ m ^ k ≤ ⌊b⌋₊)).card : ℝ) :=
      Nat.cast_nonneg _
    have hdiv : Real.log ⌊b⌋₊ / k ≤ Real.log b / 2 :=
      (div_le_div_of_nonneg_left hlogB0 (by norm_num) hkr).trans (by linarith)
    exact mul_le_mul hdiv hc2 hc0 (by linarith)
  have hKle : (K : ℝ) ≤ Real.log b / Real.log 2 := by
    have hpow : 2 ^ K ≤ ⌊b⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    rw [le_div_iff₀ hl2]
    have : Real.log ((2 : ℝ) ^ K) ≤ Real.log ⌊b⌋₊ :=
      Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    rw [Real.log_pow] at this
    linarith
  have hcard : ((Icc 2 K).card : ℝ) ≤ K := by
    have : (Icc 2 K).card ≤ K := by rw [Nat.card_Icc]; omega
    exact_mod_cast this
  calc _ ≤ _ := hmain
    _ ≤ ∑ k ∈ Icc 2 K, M := sum_le_sum hk
    _ = ((Icc 2 K).card : ℝ) * M := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (K : ℝ) * M := mul_le_mul_of_nonneg_right hcard hM0
    _ ≤ _ := mul_le_mul_of_nonneg_right hKle hM0

/-- The window sum splits into primes and the rest. -/
theorem split_sum (A B : ℕ) : ∑ n ∈ Ioc A B, Λ n =
    ∑ p ∈ (Ioc A B).filter Nat.Prime, Real.log p +
      ∑ n ∈ (Ioc A B).filter (fun n => ¬ n.Prime), Λ n := by
  rw [← sum_filter_add_sum_filter_not (Ioc A B) Nat.Prime (fun n => Λ n)]
  congr 1
  exact sum_congr rfl fun n hn => ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.1 hn).2

/-- `Σ_{x < p ≤ b} log p ≤ primesIn x (b - x) · log b`. -/
theorem prime_sum_le {x b : ℝ} (hx : 0 ≤ x) (hb : 1 ≤ b) :
    ∑ p ∈ (Ioc ⌊x⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p ≤
      (primesIn x (b - x) : ℝ) * Real.log b := by
  have hsub : (Ioc ⌊x⌋₊ ⌊b⌋₊).filter Nat.Prime ⊆
      (range (⌊x + (b - x)⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ x < (p : ℝ)) := by
    intro p hp
    rw [show x + (b - x) = b by ring]
    simp only [mem_filter, mem_Ioc, mem_range] at hp ⊢
    exact ⟨by omega, hp.2, (Nat.floor_lt hx).1 hp.1.1⟩
  calc _ ≤ ∑ p ∈ (Ioc ⌊x⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log b := by
        apply sum_le_sum
        intro p hp
        simp only [mem_filter, mem_Ioc] at hp
        apply Real.log_le_log (by exact_mod_cast hp.2.pos)
        exact (Nat.cast_le.2 hp.1.2).trans (Nat.floor_le (by linarith))
    _ = (((Ioc ⌊x⌋₊ ⌊b⌋₊).filter Nat.Prime).card : ℝ) * Real.log b := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hb)
        unfold primesIn
        exact_mod_cast card_le_card hsub

/-- `Zpatch = Zr gZ` above `1`, under RH. -/
theorem patch_eq (hRH : RiemannHypothesis) {z : ℝ} (hz : 1 < z) : Zpatch z = Zr gZ z := by
  unfold Zpatch
  rw [ite_eq_left hz, Zr_eq_Zreal hRH (by linarith)]

/-- Size facts for `x ≥ 10^12`: `s = √x ≥ 10^6`, `1 ≤ L = log x ≤ 0.00005 s`, `L² ≤ 0.0022 s`. -/
theorem sizes {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    10 ^ 6 ≤ √x ∧ 1 ≤ Real.log x ∧ Real.log x ≤ 0.00005 * √x ∧
      Real.log x ^ 2 ≤ 0.0022 * √x := by
  have hx0 : 0 < x := by linarith
  set s := √x with hs
  set L := Real.log x with hL
  have hs2 : s ^ 2 = x := sq_sqrt hx0.le
  have hs0 : 0 < s := sqrt_pos.2 hx0
  have hs6 : 10 ^ 6 ≤ s := by rw [hs, le_sqrt (by norm_num) hx0.le]; linarith
  set t := √s with ht
  have ht2 : t ^ 2 = s := sq_sqrt hs0.le
  have ht0 : 0 < t := sqrt_pos.2 hs0
  have ht3 : 1000 ≤ t := by rw [ht, le_sqrt (by norm_num) hs0.le]; linarith
  have hx4 : x = t ^ 4 := by rw [← hs2, ← ht2]; ring
  have hLt : L = 4 * Real.log t := by rw [hL, hx4, Real.log_pow]; push_cast; ring
  have hlt : Real.log t ≤ 0.0117 * t := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < t / 128 by positivity)
    rw [Real.log_div ht0.ne' (by norm_num)] at h1
    have h128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; push_cast; ring
    have := Real.log_two_lt_d9
    nlinarith
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hts : 1000 * t ≤ s := by rw [← ht2]; nlinarith
  have hLt' : L ≤ 0.0468 * t := by linarith
  refine ⟨hs6, hL1, by nlinarith, ?_⟩
  rw [← ht2]; nlinarith

/-- Arithmetic: `(x + 2h) r / (x + h) ≤ 1.0004 s` for `r ≤ s + 3L`, `x = s²`, `h = 3 s L`. -/
theorem arith_q2 {s L r : ℝ} (hs6 : 10 ^ 6 ≤ s) (hL1 : 1 ≤ L) (hLs : L ≤ 0.00005 * s)
    (hr0 : 0 ≤ r) (hr : r ≤ s + 3 * L) :
    (s ^ 2 + 2 * (3 * s * L)) * r / (s ^ 2 + 3 * s * L) ≤ 1.0004 * s := by
  have hs0 : 0 < s := by linarith
  have hd : 0 < s ^ 2 + 3 * s * L := by positivity
  rw [div_le_iff₀ hd]
  have h1 : (s ^ 2 + 2 * (3 * s * L)) * r ≤ (s ^ 2 + 2 * (3 * s * L)) * (s + 3 * L) :=
    mul_le_mul_of_nonneg_left hr (by positivity)
  have k1 : s ^ 2 * L ≤ s ^ 2 * (0.00005 * s) := mul_le_mul_of_nonneg_left hLs (by positivity)
  have k2 : s * L * L ≤ s * L * (0.00005 * s) := mul_le_mul_of_nonneg_left hLs (by positivity)
  nlinarith

/-- Arithmetic for the prime power mass: at most `0.0064 s L`. -/
theorem arith_mass {s L lb q m : ℝ} (hs6 : 10 ^ 6 ≤ s) (hL1 : 1 ≤ L)
    (hL2 : L ^ 2 ≤ 0.0022 * s) (hlb : lb ≤ 1.00001 * L) (hlb0 : 0 ≤ lb) (hq : q ≤ 4 * L)
    (hq0 : 0 ≤ q) (hm : m ≤ lb / Real.log 2 * (lb / 2 * q)) : m ≤ 0.0064 * s * L := by
  have hl2 := Real.log_two_gt_d9
  have hm1 : lb / Real.log 2 ≤ 1.4429 * L := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hm2 : lb / 2 * q ≤ 0.500005 * L * (4 * L) :=
    mul_le_mul (by linarith) hq hq0 (by positivity)
  have hm3 : lb / Real.log 2 * (lb / 2 * q) ≤ 1.4429 * L * (0.500005 * L * (4 * L)) :=
    mul_le_mul hm1 hm2 (by positivity) (by positivity)
  have hL3 : L ^ 2 * L ≤ 0.0022 * s * L := mul_le_mul_of_nonneg_right hL2 (by linarith)
  nlinarith

/-- **The window lower bound**: under RH, CONDITIONAL ON `HSWN70 gZ`, for `x ≥ 10^12` and
`h = 3 √x log x`, `Σ_{x < n ≤ x + 2h} Λ(n) > 3 s L - 0.6369 s L - 1`. -/
theorem window_lower (hRH : RiemannHypothesis) (hN : HSWN70 gZ) {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    3 * √x * Real.log x - 0.6369 * √x * Real.log x - 1 <
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + 2 * (3 * √x * Real.log x)⌋₊, Λ n := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hs6, hL1, hLs, -⟩ := sizes hx
  set s := √x with hs
  set L := Real.log x with hL
  have hs2 : s ^ 2 = x := sq_sqrt hx0.le
  have hs0 : 0 < s := by linarith
  set h := 3 * s * L with hh
  have hh0 : 0 < h := by positivity
  have hhx : h ≤ 0.00015 * x := by rw [← hs2, hh]; nlinarith
  have h35 : 35 * h ≤ x + h := by linarith
  have hhy : h < x + h := by linarith
  have e1 : x + h - h = x := by ring
  have e2 : x + h + h = x + 2 * h := by ring
  -- Lemma 5 at the centre x + h
  have h5 := lemma5_of lemma4_Zpatch (x + h) h hh0 hhy
  simp only at h5
  rw [e1, e2, patch_eq hRH (by linarith), patch_eq hRH (by linarith),
    patch_eq hRH (by linarith)] at h5
  have hS := sigma_gen hN hh0 h35
  rw [e1, e2, ← hs] at hS
  set S := Zr gZ (x + 2 * h) - 2 * Zr gZ (x + h) + Zr gZ x with hSdef
  have hsq2 : √(x + 2 * h) ≤ s + 3 * L := by
    rw [Real.sqrt_le_left (by positivity), ← hs2, hh]; nlinarith
  have hsq2' : 0 ≤ √(x + 2 * h) := Real.sqrt_nonneg _
  have h32 : (x + 2 * h) ^ (3 / 2 : ℝ) = (x + 2 * h) * √(x + 2 * h) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hlog2 : Real.log (2 * (x + h) / h) ≤ L / 2 := by
    have hsL : Real.log s = L / 2 := by rw [hs, Real.log_sqrt hx0.le]
    rw [← hsL]
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hh0, hh, ← hs2]; nlinarith
  have hlog20 : 0 ≤ Real.log (2 * (x + h) / h) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hh0]; linarith
  obtain ⟨-, hpi2⟩ := LeanLab.Dudek2014.Section22.pi_bounds
  have hpi0 := Real.pi_pos
  have eS : (2 * (x + h) * h / (π * s) + 4 * h * ((x + 2 * h) * √(x + 2 * h)) /
      (π * 2 * (x + h))) * Real.log (2 * (x + h) / h) =
      h * (2 / π * ((x + h) / s + (x + 2 * h) * √(x + 2 * h) / (x + h)) *
        Real.log (2 * (x + h) / h)) := by
    field_simp
    ring
  rw [h32, eS] at hS
  have hq1 : (x + h) / s = s + 3 * L := by
    rw [div_eq_iff hs0.ne', hh, ← hs2]; ring
  have hq2 : (x + 2 * h) * √(x + 2 * h) / (x + h) ≤ 1.0004 * s := by
    have := arith_q2 hs6 hL1 hLs hsq2' hsq2
    rw [hs2, ← hh] at this
    exact this
  have hbr : 2 / π * ((x + h) / s + (x + 2 * h) * √(x + 2 * h) / (x + h)) ≤ 1.2737 * s := by
    rw [hq1]
    have h0 : 0 ≤ (s + 3 * L) + (x + 2 * h) * √(x + 2 * h) / (x + h) := by positivity
    have : 2 / π * ((s + 3 * L) + (x + 2 * h) * √(x + 2 * h) / (x + h)) ≤
        0.63662 * ((s + 3 * L) + (x + 2 * h) * √(x + 2 * h) / (x + h)) :=
      mul_le_mul_of_nonneg_right hpi2 h0
    nlinarith
  have hSh : S / h ≤ 0.6369 * s * L := by
    have h1 : S / h ≤ |S| / h := div_le_div_of_nonneg_right (le_abs_self _) hh0.le
    have h2 : |S| / h ≤ 2 / π * ((x + h) / s + (x + 2 * h) * √(x + 2 * h) / (x + h)) *
        Real.log (2 * (x + h) / h) := by
      rw [div_le_iff₀ hh0]; linarith
    have h3 : 2 / π * ((x + h) / s + (x + 2 * h) * √(x + 2 * h) / (x + h)) *
        Real.log (2 * (x + h) / h) ≤ 1.2737 * s * (L / 2) :=
      mul_le_mul hbr hlog2 hlog20 (by positivity)
    nlinarith
  have h48 : 48 / (5 * h) ≤ 1 := by
    rw [div_le_iff₀ (by positivity), hh]; nlinarith
  have hWS : 3 * s * L - 0.6369 * s * L - 1 < WS (x + h) h := by
    have := (abs_lt.1 h5).1
    rw [hh] at hSh ⊢
    linarith
  have hWle := WS_le hh0 hhy.le
  rw [e1, e2] at hWle
  linarith

/-- **Cramér's theorem for `x ≥ 10^12`, with `c = 6`**: under RH, CONDITIONAL ON `HSWN70 gZ`,
more than `√x` primes in `(x, x + 6 √x log x]`. -/
theorem large_range (hRH : RiemannHypothesis) (hN : HSWN70 gZ) {x : ℝ} (hx : 10 ^ 12 ≤ x) :
    √x < primesIn x (6 * √x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hW := window_lower hRH hN hx
  obtain ⟨hs6, hL1, hLs, hL2⟩ := sizes hx
  set s := √x with hs
  set L := Real.log x with hL
  have hs2 : s ^ 2 = x := sq_sqrt hx0.le
  have hs0 : 0 < s := by linarith
  set h := 3 * s * L with hh
  have hh0 : 0 < h := by positivity
  have hb1 : x ≤ x + 2 * h := by linarith
  rw [split_sum] at hW
  have hmass := mass_gen (a := x) (b := x + 2 * h) (by linarith) hb1
  have hsq2 : √(x + 2 * h) ≤ s + 3 * L := by
    rw [Real.sqrt_le_left (by positivity), ← hs2, hh]; nlinarith
  have hlb : Real.log (x + 2 * h) ≤ 1.00001 * L := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (x + 2 * h) / x by positivity)
    rw [Real.log_div (by positivity) hx0.ne'] at h1
    have h2 : (x + 2 * h) / x - 1 = 6 * L / s := by
      rw [hh, ← hs2]; field_simp; ring
    have h3 : 6 * L / s ≤ 0.00001 * L := by
      rw [div_le_iff₀ hs0]; nlinarith
    linarith
  have hlb0 : 0 ≤ Real.log (x + 2 * h) := Real.log_nonneg (by linarith)
  have hdiff : √(x + 2 * h) - √x + 1 ≤ 4 * L := by rw [← hs]; linarith
  have hdiff0 : 0 ≤ √(x + 2 * h) - √x + 1 := by
    have := Real.sqrt_le_sqrt hb1; linarith
  have hmassB := arith_mass hs6 hL1 hL2 hlb hlb0 hdiff hdiff0 hmass
  have hpr := prime_sum_le (x := x) (b := x + 2 * h) hx0.le (by linarith)
  rw [show x + 2 * h - x = 6 * s * L by rw [hh]; ring] at hpr
  set P := (primesIn x (6 * s * L) : ℝ) with hP
  have hPL : 2.35 * s * L - 1 ≤ P * Real.log (x + 2 * h) := by linarith
  by_contra hc
  push Not at hc
  have : P * Real.log (x + 2 * h) ≤ s * (1.00001 * L) := mul_le_mul hc hlb hlb0 hs0.le
  nlinarith

/-- **Dudek 2014 Theorem 1, Cramér's theorem, with `c = 10^8`**: under RH, CONDITIONAL ON the
Hasanalizade-Shen-Wong `N(T)` bound `HSWN70 gZ` only, more than `√x` primes in
`(x, x + 10^8 √x log x]` for every `x ≥ 2`. -/
theorem theorem1_c (hRH : RiemannHypothesis) (hN : HSWN70 gZ) {x : ℝ} (hx : 2 ≤ x) :
    √x < primesIn x (10 ^ 8 * √x * Real.log x) := by
  rcases lt_or_ge x (10 ^ 12) with h | h
  · exact small_range hx h
  · have hL : 0 ≤ √x * Real.log x :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith))
    have e : ∀ c : ℝ, c * √x * Real.log x = c * (√x * Real.log x) := fun c => mul_assoc _ _ _
    have hle : 6 * √x * Real.log x ≤ 10 ^ 8 * √x * Real.log x := by
      rw [e, e]; exact mul_le_mul_of_nonneg_right (by norm_num) hL
    exact (large_range hRH hN h).trans_le (by exact_mod_cast primesIn_mono hle)

/-- **Dudek 2014 Theorem 1 in the form of `Statements.theorem1`**, under RH, CONDITIONAL ON
`HSWN70 gZ` only. -/
theorem theorem1_of_RH_hsw (hRH : RiemannHypothesis) (hN : HSWN70 gZ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → √x < primesIn x (c * √x * Real.log x) :=
  ⟨10 ^ 8, by norm_num, fun _ hx => theorem1_c hRH hN hx⟩

end

end LeanLab.Dudek2014.Theorem1H

