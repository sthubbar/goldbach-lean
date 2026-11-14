module

public import LeanLab.RieselVaughan1983.Section6
public import LeanLab.RieselVaughan1983.Numerics
public import LeanLab.ChenExplicit.TwinCUpper

/-!
P0032 Riesel-Vaughan 1983, Lemma 8, pages 58-60: `N(x) > x/18` for `24 ≤ log x ≤ 424`,
assembled from Section6.lean, Numerics.lean and the cited inputs: Lemma 5 for the four table
rows used, Lemma 6 (i), and the computed values (2.30), (2.31) of `T(u)` and `s`.
The twin prime constant is the lab's `ChenExplicit.twinC`, `C = 2·twinC ≤ 1.32034` PROVED by
`twinC_le_066017`, slightly above the paper's 1.320324; (6.8) still holds with it.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real
open scoped Classical

namespace LeanLab.RieselVaughan1983
open LeanLab.SchnirelmannConstant

/-- (2.3): `C = 2 Π_{p>2} p(p-2)/(p-1)²`, twice the lab's `twinC`. -/
noncomputable def Ctw : ℝ := 2 * LeanLab.ChenExplicit.twinC

lemma Ctw_le : Ctw ≤ 132034 / 100000 := by
  have := LeanLab.ChenExplicit.TwinCUpper.twinC_le_066017
  unfold Ctw; linarith

lemma Ctw_pos : 0 < Ctw := by
  have := LeanLab.ChenExplicit.twinC_pos
  unfold Ctw; linarith

/-- Lemma 5, p. 53, CITED, in the special case used in Lemma 8: `a = 1`, `b = h > 0`, the
interval `(0, x]`, and without the `-100 x^{1/2}` term, so weaker than the paper's lemma.
For `x ≥ e^L` the number of primes `p ≤ x` with `p + h` prime is at most
`8Cx/((log x)(A + log x)) Π_{p | h, p > 2} (p-1)/(p-2)`. -/
def Lemma5Used (L A : ℝ) : Prop :=
  ∀ x : ℝ, Real.exp L ≤ x → ∀ h : ℕ, 0 < h →
    (#((Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + h).Prime)) : ℝ) ≤
      8 * Ctw * x / (Real.log x * (A + Real.log x)) * wt h

/-- Lemma 6 (i), p. 55, CITED: `π(x) > x/log x + 0.9911 x/(log x)²` for `log x ≥ 17`;
`x > 0` is explicit because Mathlib's `log` is even. -/
def Lemma6i : Prop :=
  ∀ x : ℝ, 0 < x → 17 ≤ Real.log x →
    x / Real.log x + 9911 / 10000 * x / Real.log x ^ 2 < (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- (2.30) and (2.31), p. 48, the paper's computations, CITED; reproduced in Python by
`T_check.py`: `T(79) < 328.5614`, `T(99989) < 80096031`, `s(79) = 21`, `s(99989) = 9590`. -/
def Table230 : Prop :=
  Tu 79 ≤ 3285614 / 10000 ∧ Tu 99989 ≤ 80096031 ∧ #(oddPrimes 79) = 21 ∧
    #(oddPrimes 99989) = 9590

lemma wt_nonneg (h : ℕ) : 0 ≤ wt h := by
  unfold wt
  apply prod_nonneg
  intro p hp
  simp only [mem_filter] at hp
  have : (2 : ℝ) < p := by exact_mod_cast hp.2
  apply div_nonneg <;> linarith

lemma Tu_nonneg (u : ℕ) : 0 ≤ Tu u := by
  unfold Tu
  exact sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => wt_nonneg _))

/-- `π(n) ≤ #oddPrimes(n - u) + u + 1`: the primes up to `n` are 2, the odd primes up to
`n - u`, and at most `u` numbers in `(n - u, n]`. -/
lemma pi_le_oddPrimes_sub (n u : ℕ) (hn : 2 ≤ n) :
    Nat.primeCounting n ≤ #(oddPrimes (n - u)) + u + 1 := by
  rw [primeCounting_eq_oddPrimes n hn]
  have hsub : oddPrimes n ⊆ oddPrimes (n - u) ∪ Ioc (n - u) n := by
    intro p hp
    rw [mem_oddPrimes] at hp
    rw [mem_union, mem_oddPrimes, mem_Ioc]
    by_cases h : p ≤ n - u
    · exact Or.inl ⟨hp.1, h, hp.2.2⟩
    · exact Or.inr ⟨by omega, hp.2.1⟩
  have := (card_le_card hsub).trans (card_union_le _ _)
  rw [Nat.card_Ioc] at this
  omega

/-- The general form of Lemma 8's argument, pages 58-59: with Lemma 5 at `(L, A)`,
`s = π(u) - 1`, `T(u) ≤ t`, `α = x/l + Dx/l² ≤ π(x - u) - 1` and (6.8) at `l = log x`,
`N(x) > x/18`. -/
theorem lemma8_generic (x : ℝ) (u : ℕ) (L A D t : ℝ) (s : ℕ) (hxL : Real.exp L ≤ x)
    (hl0 : 0 < Real.log x) (hL5 : Lemma5Used L A) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hs : #(oddPrimes u) = s) (hT : Tu u ≤ t) (hu : u ≤ ⌊x⌋₊)
    (hα : x / Real.log x + D * x / Real.log x ^ 2 ≤ #(oddPrimes (⌊x⌋₊ - u)))
    (h68 : 0 < lhs68 s t A D Ctw (Real.log x)) : x / 18 < NCount x := by
  set n := ⌊x⌋₊ with hn
  set l := Real.log x with hl
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos L) hxL
  have hAl : 0 < A + l := by linarith
  set B := 8 * Ctw * x / (l * (A + l)) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]; have := Ctw_pos; positivity
  have h63 := eq63 u n hu B (fun h hh => hL5 x hxL h hh)
  have hN : (NCount x : ℝ) = #(Eset n) := by rfl
  set α := x / l + D * x / l ^ 2 with hαdef
  have hα0 : 0 ≤ α := by rw [hαdef]; positivity
  set a := α * s with hadef
  have hP : (#(Pset u n) : ℝ) = s * #(oddPrimes (n - u)) := by
    rw [Pset, card_product, hs]; push_cast; ring
  have ha0 : 0 ≤ a := by positivity
  have haP : a ≤ #(Pset u n) := by
    rw [hP, hadef, mul_comm]
    exact mul_le_mul_of_nonneg_left hα (Nat.cast_nonneg _)
  have hkey := key_ineq h63 ha0 haP (Nat.cast_nonneg _) hB0 (Tu_nonneg u) hT
  rw [← hN] at hkey
  have ht0 : 0 ≤ t := (Tu_nonneg u).trans hT
  -- (6.8) is `18 a² - x(a + 2Bt) > 0` up to the positive factor `x²/(l²(1 + A/l))`
  have hid : 18 * a ^ 2 - x * (a + 2 * B * t) =
      x ^ 2 / (l ^ 2 * (1 + A / l)) * lhs68 s t A D Ctw l := by
    rw [hadef, hαdef, hB, lhs68]
    field_simp
    ring
  have hpos : 0 < x ^ 2 / (l ^ 2 * (1 + A / l)) := by
    have : 0 < 1 + A / l := by positivity
    positivity
  have h18 : x * (a + 2 * B * t) < 18 * a ^ 2 := by
    have := mul_pos hpos h68
    linarith
  have hden : 0 < a + 2 * B * t := by
    by_contra hc
    push Not at hc
    have : 0 ≤ 2 * B * t := by positivity
    have ha : a = 0 := by linarith
    rw [ha] at h18
    have : 0 ≤ x * (0 + 2 * B * t) := by positivity
    linarith
  have : x / 18 * (a + 2 * B * t) < (NCount x : ℝ) * (a + 2 * B * t) := by
    nlinarith
  exact lt_of_mul_lt_mul_right this hden.le

/-- `e^l/l² ≥ l¹²/14!` for `l > 0`, from `e^l ≥ l¹⁴/14!`. -/
lemma exp_div_sq_ge (l : ℝ) (hl : 0 < l) (k : ℕ) :
    l ^ (k + 2) / (k + 2).factorial / l ^ 2 ≤ Real.exp l / l ^ 2 := by
  have := Real.pow_div_factorial_le_exp l hl.le (k + 2)
  exact div_le_div_of_nonneg_right this (by positivity)

/-- From Lemma 6 (i) to `α ≤ π(x - u) - 1` when `(0.9911 - D) x/l² ≥ u + 1`. -/
lemma alpha_le (h6 : Lemma6i) (x : ℝ) (u : ℕ) (D : ℝ) (hx0 : 0 < x) (hl : 17 ≤ Real.log x)
    (hmargin : (u : ℝ) + 1 ≤ (9911 / 10000 - D) * x / Real.log x ^ 2) :
    x / Real.log x + D * x / Real.log x ^ 2 ≤ #(oddPrimes (⌊x⌋₊ - u)) := by
  have hpi := h6 x hx0 hl
  have hx : Real.exp 17 ≤ x := by
    rw [← Real.exp_log hx0]; exact Real.exp_le_exp.mpr hl
  have hn2 : 2 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    have := Real.add_one_le_exp 17
    push_cast; linarith
  have hle := pi_le_oddPrimes_sub ⌊x⌋₊ u hn2
  have hle' : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ #(oddPrimes (⌊x⌋₊ - u)) + u + 1 := by
    exact_mod_cast hle
  have e : (9911 / 10000 - D) * x / Real.log x ^ 2 =
      9911 / 10000 * x / Real.log x ^ 2 - D * x / Real.log x ^ 2 := by ring
  linarith

/-- `x/l² ≥ l^k/(k+2)!` for `x = e^l`, `l > 0`. -/
lemma x_div_sq_ge (x : ℝ) (hx0 : 0 < x) (hl : 0 < Real.log x) (k : ℕ) :
    Real.log x ^ k / (k + 2).factorial ≤ x / Real.log x ^ 2 := by
  have h := exp_div_sq_ge (Real.log x) hl k
  rw [Real.exp_log hx0] at h
  refine le_trans (le_of_eq ?_) h
  field_simp
  ring

/-- (6.8) at the four right ends with the lab's proved `C ≤ 1.32034`. -/
theorem lhs68_ranges' (C l : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ 132034 / 100000) :
    (∀ t, 0 ≤ t → t ≤ 3285614 / 10000 → 24 ≤ l → l ≤ 42 → 0 < lhs68 21 t 0 0 C l) ∧
    (∀ t, 0 ≤ t → t ≤ 80096031 → 42 < l → l ≤ 300 →
      0 < lhs68 9590 t 8 (99 / 100) C l) ∧
    (∀ t, 0 ≤ t → t ≤ 80096031 → 300 < l → l ≤ 400 →
      0 < lhs68 9590 t (843 / 100) (99 / 100) C l) ∧
    (∀ t, 0 ≤ t → t ≤ 80096031 → 400 < l → l ≤ 424 →
      0 < lhs68 9590 t (844 / 100) (99 / 100) C l) := by
  have e42 : 0 < lhs68 21 (3285614 / 10000) 0 0 (132034 / 100000) 42 := by
    unfold lhs68; norm_num
  have e300 : 0 < lhs68 9590 80096031 8 (99 / 100) (132034 / 100000) 300 := by
    unfold lhs68; norm_num
  have e400 : 0 < lhs68 9590 80096031 (843 / 100) (99 / 100) (132034 / 100000) 400 := by
    unfold lhs68; norm_num
  have e424 : 0 < lhs68 9590 80096031 (844 / 100) (99 / 100) (132034 / 100000) 424 := by
    unfold lhs68; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht0 ht h1 h2
    exact lhs68_mono_Ct hC ht hC0 ht0
      (lhs68_pos_of_le (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by linarith) h2 e42)
  · intro t ht0 ht h1 h2
    exact lhs68_mono_Ct hC ht hC0 ht0 (lhs68_pos_of_le (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by linarith) h2 e300)
  · intro t ht0 ht h1 h2
    exact lhs68_mono_Ct hC ht hC0 ht0 (lhs68_pos_of_le (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by linarith) h2 e400)
  · intro t ht0 ht h1 h2
    exact lhs68_mono_Ct hC ht hC0 ht0 (lhs68_pos_of_le (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by linarith) h2 e424)

/-- **Lemma 8**, CONDITIONAL ON Lemma 5 at the four table rows `(L, A) = (24, 0)`, `(42, 8)`,
`(278, 8.43)`, `(396, 8.44)`, on Lemma 6 (i), and on the computed values (2.30), (2.31). -/
theorem lemma8_of (h24 : Lemma5Used 24 0) (h42 : Lemma5Used 42 8)
    (h278 : Lemma5Used 278 (843 / 100)) (h396 : Lemma5Used 396 (844 / 100))
    (h6 : Lemma6i) (hTab : Table230) : Lemma8 := by
  intro x hx0 hl24 hl424
  obtain ⟨hT79, hT99, hs79, hs99⟩ := hTab
  set l := Real.log x with hl
  have hl0 : 0 < l := by linarith
  have hxl : x = Real.exp l := (Real.exp_log hx0).symm
  have hC0 : 0 ≤ Ctw := Ctw_pos.le
  have hR := lhs68_ranges' Ctw l hC0 Ctw_le
  -- `x ≥ l⁶/720 ≥ 24⁶/720`, so `x ≥ 99989 + 1`
  have hxbig : (99990 : ℝ) ≤ x := by
    have h := Real.pow_div_factorial_le_exp l hl0.le 6
    rw [← hxl] at h
    have : (24 : ℝ) ^ 6 ≤ l ^ 6 := pow_le_pow_left₀ (by norm_num) hl24 6
    have hf : ((6 : ℕ).factorial : ℝ) = 720 := by norm_num [Nat.factorial]
    rw [hf] at h
    have h2 : (24 : ℝ) ^ 6 / 720 ≤ l ^ 6 / 720 := by gcongr
    have c : (99990 : ℝ) ≤ 24 ^ 6 / 720 := by norm_num
    linarith
  have hu : ∀ u : ℕ, u ≤ 99989 → u ≤ ⌊x⌋₊ := fun u hu => by
    apply Nat.le_floor; have : (u : ℝ) ≤ 99989 := by exact_mod_cast hu
    linarith
  by_cases hA : l ≤ 42
  · -- `A = 0`, `D = 0`, `u = 79`
    have hα := alpha_le h6 x 79 0 hx0 (by linarith) (by
      have h := x_div_sq_ge x hx0 hl0 4
      have : (24 : ℝ) ^ 4 ≤ l ^ 4 := pow_le_pow_left₀ (by norm_num) hl24 4
      have hf : (((4 + 2 : ℕ)).factorial : ℝ) = 720 := by norm_num [Nat.factorial]
      rw [hf] at h
      have : (24 : ℝ) ^ 4 / 720 ≤ x / l ^ 2 := le_trans (by gcongr) h
      rw [show (9911 / 10000 - 0) * x / l ^ 2 = 9911 / 10000 * (x / l ^ 2) by ring]
      have c : ((79 : ℕ) : ℝ) + 1 ≤ 9911 / 10000 * ((24 : ℝ) ^ 4 / 720) := by norm_num
      have c2 : 9911 / 10000 * ((24 : ℝ) ^ 4 / 720) ≤ 9911 / 10000 * (x / l ^ 2) := by gcongr
      linarith)
    refine lemma8_generic x 79 24 0 0 (3285614 / 10000) 21 ?_ hl0 h24 le_rfl le_rfl hs79 hT79
      (hu 79 (by norm_num)) (by simpa using hα) ?_
    · rw [hxl]; exact Real.exp_le_exp.mpr hl24
    · exact_mod_cast hR.1 _ (by norm_num) le_rfl hl24 hA
  push Not at hA
  -- `u = 99989`, `D = 0.99`; margin `0.0011 x/l² ≥ 0.0011 · 42¹²/14! ≥ 99990`
  have hα := alpha_le h6 x 99989 (99 / 100) hx0 (by linarith) (by
    have h := x_div_sq_ge x hx0 hl0 12
    have : (42 : ℝ) ^ 12 ≤ l ^ 12 := pow_le_pow_left₀ (by norm_num) hA.le 12
    have hf : (((12 + 2 : ℕ)).factorial : ℝ) = 87178291200 := by norm_num [Nat.factorial]
    rw [hf] at h
    have : (42 : ℝ) ^ 12 / 87178291200 ≤ x / l ^ 2 := le_trans (by gcongr) h
    rw [show (9911 / 10000 - 99 / 100) * x / l ^ 2 = 11 / 10000 * (x / l ^ 2) by ring]
    have c : ((99989 : ℕ) : ℝ) + 1 ≤ 11 / 10000 * ((42 : ℝ) ^ 12 / 87178291200) := by norm_num
    have c2 : 11 / 10000 * ((42 : ℝ) ^ 12 / 87178291200) ≤ 11 / 10000 * (x / l ^ 2) := by gcongr
    linarith)
  have hs99' : ((#(oddPrimes 99989) : ℕ) : ℝ) = 9590 := by rw [hs99]; norm_num
  by_cases hB : l ≤ 300
  · refine lemma8_generic x 99989 42 8 (99 / 100) 80096031 9590 ?_ hl0 h42 (by norm_num)
      (by norm_num) hs99 hT99 (hu 99989 le_rfl) hα ?_
    · rw [hxl]; exact Real.exp_le_exp.mpr hA.le
    · exact_mod_cast hR.2.1 _ (by norm_num) le_rfl hA hB
  push Not at hB
  by_cases hC : l ≤ 400
  · refine lemma8_generic x 99989 278 (843 / 100) (99 / 100) 80096031 9590 ?_ hl0 h278
      (by norm_num) (by norm_num) hs99 hT99 (hu 99989 le_rfl) hα ?_
    · rw [hxl]; exact Real.exp_le_exp.mpr (by linarith)
    · exact_mod_cast hR.2.2.1 _ (by norm_num) le_rfl hB hC
  push Not at hC
  refine lemma8_generic x 99989 396 (844 / 100) (99 / 100) 80096031 9590 ?_ hl0 h396
    (by norm_num) (by norm_num) hs99 hT99 (hu 99989 le_rfl) hα ?_
  · rw [hxl]; exact Real.exp_le_exp.mpr (by linarith)
  · exact_mod_cast hR.2.2.2 _ (by norm_num) le_rfl hC hl424

end LeanLab.RieselVaughan1983
