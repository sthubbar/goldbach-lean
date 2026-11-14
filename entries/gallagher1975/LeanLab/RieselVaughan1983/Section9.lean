module

public import LeanLab.RieselVaughan1983.Lemma15

/-!
P0032 Riesel-Vaughan 1983, Section 9, pages 69-70: (9.1) from Lemma 9, Lemma 14 and
Lemma 15, with Cauchy's inequality `Σ S_k² ≥ (Σ S_k)²/K`. Lemma 15 is PROVED conditional on
Lemma 6 in Lemma15.lean; Lemmas 9 and 14 enter as stated Props, with `Ψ_k`, `R_k`, `w(n)`
defined as in (7.3) to (7.5).
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset Real
open scoped Classical

namespace LeanLab.RieselVaughan1983

/-- (7.4): `w(n) = Π_{p | n, p > 2} (p - 2)/(p - 1)`. -/
noncomputable def wn (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (2 < ·), (((p : ℝ) - 2) / ((p : ℝ) - 1))

/-- (7.3): `R_k(n)`, the primes `p, p'` in `I_k = (ky/2, ky/2 + y]` with `p + p' = n`. -/
noncomputable def Rk (y : ℝ) (k n : ℕ) : ℕ :=
  #((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime ∧
    (k * y / 2 < p ∧ (p : ℝ) ≤ k * y / 2 + y) ∧
    (k * y / 2 < ((n - p : ℕ) : ℝ) ∧ ((n - p : ℕ) : ℝ) ≤ k * y / 2 + y)))

/-- (8.2): `Ψ_k = Σ_n R_k(n) w(n)`, the sum over `n ≤ x`, where all its terms lie for
`k ≤ K`. -/
noncomputable def PsiK (x y : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ range (⌊x⌋₊ + 1), (Rk y k n : ℝ) * wn n

/-- Lemma 9, page 60, as used, with `≤` where the paper has `<`, so weaker, and `x > 0`
explicit since Mathlib's `log` is even: with `K = 200`, `y = x/202` and `log y > 350`,
`Ψ < (N(x) - N(y)) 8Cy/((log(y/2))(8.3 + log(y/2)))`. -/
def Lemma9P : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) →
    ∑ k ∈ Icc 1 200, PsiK x (x / 202) k ≤
      ((NCount x : ℝ) - NCount (x / 202)) * (8 * Ctw * (x / 202) /
        (Real.log (x / 202 / 2) * (83 / 10 + Real.log (x / 202 / 2))))

/-- Lemma 14, page 67: for `x > 0` and `log y > 350`,
`Ψ_k ≥ (C/15)((8 + log 5/log y) S_k² - (y/log y)(1 + 2.9267/log y) S_k)`. -/
def Lemma14P : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200,
    Ctw / 15 * ((8 + Real.log 5 / Real.log (x / 202)) * Sk (x / 202) k ^ 2 -
      x / 202 / Real.log (x / 202) * (1 + 29267 / 10000 / Real.log (x / 202)) * Sk (x / 202) k)
      ≤ PsiK x (x / 202) k

lemma log_5_bounds : 160943 / 100000 ≤ Real.log 5 ∧ Real.log 5 ≤ 160944 / 100000 := by
  have e : (5 : ℝ) = 2 ^ 2 / (1 - 1 / 5) := by norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 5) (by norm_num) 10
  rw [abs_le] at h
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_two_gt_d9
  simp only [sum_range_succ, sum_range_zero] at h
  norm_num at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- Page 69, first display after (9.1): `(8 + log 5/L)(1 - 3.6581/L) - (1 + 2.9267/L) ≥ 7 - 30.5989/L`. -/
lemma sec9_step1 (L : ℝ) (hL : 350 ≤ L) :
    7 - 305989 / 10000 / L ≤
      (8 + Real.log 5 / L) * (1 - 36581 / 10000 / L) - (1 + 29267 / 10000 / L) := by
  obtain ⟨h1, h2⟩ := log_5_bounds
  have hL0 : 0 < L := by linarith
  have e : (8 + Real.log 5 / L) * (1 - 36581 / 10000 / L) - (1 + 29267 / 10000 / L) =
      7 + (Real.log 5 - 8 * (36581 / 10000) - 29267 / 10000) / L -
        Real.log 5 * (36581 / 10000) / L ^ 2 := by field_simp; ring
  rw [e]
  have hq : Real.log 5 * (36581 / 10000) / L ^ 2 ≤ 160944 / 100000 * (36581 / 10000) / 350 / L := by
    rw [div_div, pow_two]
    calc Real.log 5 * (36581 / 10000) / (L * L) ≤ 160944 / 100000 * (36581 / 10000) / (L * L) := by
          gcongr
      _ ≤ 160944 / 100000 * (36581 / 10000) / (350 * L) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
  have hl : (160943 / 100000 - 8 * (36581 / 10000) - 29267 / 10000) / L ≤
      (Real.log 5 - 8 * (36581 / 10000) - 29267 / 10000) / L :=
    div_le_div_of_nonneg_right (by linarith) hL0.le
  have hsum : -(160943 / 100000 - 8 * (36581 / 10000) - 29267 / 10000) / L +
      160944 / 100000 * (36581 / 10000) / 350 / L ≤ 305989 / 10000 / L := by
    rw [show -(160943 / 100000 - 8 * (36581 / 10000) - 29267 / 10000) / L +
      160944 / 100000 * (36581 / 10000) / 350 / L = (-(160943 / 100000 - 8 * (36581 / 10000) -
        29267 / 10000) + 160944 / 100000 * (36581 / 10000) / 350) / L by ring]
    apply div_le_div_of_nonneg_right _ hL0.le
    norm_num
  have : -(160943 / 100000 - 8 * (36581 / 10000) - 29267 / 10000) / L =
      -((160943 / 100000 - 8 * (36581 / 10000) - 29267 / 10000) / L) := by ring
  linarith

set_option maxHeartbeats 2000000 in
/-- **(9.1)** from Lemmas 9 and 14, CONDITIONAL ON those and on Lemma 6 (i) and (ii) through
Lemma 15. -/
theorem display91_of (h9 : Lemma9P) (h14 : Lemma14P) (h6 : Lemma6i) (h6' : Lemma6ii) :
    Display91 := by
  intro x hx
  rcases le_or_gt x 0 with hneg | hx0
  · -- for `x ≤ 0` both counts vanish and the left side is `≤ 0`; `x = 0` has `log x = 0`
    have h1 : NCount x = 0 := by
      unfold NCount; rw [Nat.floor_eq_zero.mpr (by linarith)]; rfl
    have h2 : NCount (x / 202) = 0 := by
      unfold NCount; rw [Nat.floor_eq_zero.mpr (by linarith)]; rfl
    rw [h1, h2]
    rcases hneg.lt_or_eq with h | h
    · simp; linarith
    · rw [h] at hx; simp at hx; linarith
  set y := x / 202 with hy
  have hy0 : 0 < y := by positivity
  have hlog202 : Real.log 202 < 6 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]; linarith [exp_six_gt]
  have hLy : Real.log y = Real.log x - Real.log 202 := Real.log_div hx0.ne' (by norm_num)
  set L := Real.log y with hLdef
  have hL350 : 350 < L := by rw [hLy]; linarith
  have hL0 : 0 < L := by linarith
  have hC := Ctw_pos
  -- Lemma 15 and Cauchy
  set σ := ∑ k ∈ Icc 1 200, Sk y k with hσ
  have h15 := lemma15 h6 h6' y hy0 hL350.le
  rw [← hσ] at h15
  set σ0 := 200 * y / L * (1 - 36581 / 10000 / L) with hσ0
  have hσ0pos : 0 < σ0 := by
    rw [hσ0]
    have : 36581 / 10000 / L < 1 := by rw [div_lt_one hL0]; linarith
    have : 0 < 1 - 36581 / 10000 / L := by linarith
    positivity
  have hCS : σ ^ 2 ≤ 200 * ∑ k ∈ Icc 1 200, Sk y k ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Icc 1 200) (f := fun k => Sk y k)
    simpa using this
  -- Lemma 14 summed
  set a8 := 8 + Real.log 5 / L with ha8
  set b := y / L * (1 + 29267 / 10000 / L) with hb
  have h14s : Ctw / 15 * (a8 * ∑ k ∈ Icc 1 200, Sk y k ^ 2 - b * σ) ≤
      ∑ k ∈ Icc 1 200, PsiK x y k := by
    have := sum_le_sum (fun k hk => h14 x hx0 hL350 k hk)
    rw [← hy] at this
    refine le_trans (le_of_eq ?_) this
    rw [hσ, mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
  have ha8pos : 0 < a8 := by
    have := (log_5_bounds).1; rw [ha8]; positivity
  -- the bracket `a8 σ/200 - b ≥ (y/L)(7 - 30.5989/L) > 0`
  have hstep1 := sec9_step1 L hL350.le
  have hbr : y / L * (7 - 305989 / 10000 / L) ≤ a8 * σ / 200 - b := by
    have e : a8 * σ0 / 200 - b = y / L * ((8 + Real.log 5 / L) * (1 - 36581 / 10000 / L) -
        (1 + 29267 / 10000 / L)) := by rw [hσ0, ha8, hb]; ring
    have : a8 * σ0 / 200 ≤ a8 * σ / 200 := by
      have := mul_le_mul_of_nonneg_left h15.le ha8pos.le; linarith
    have hyL : 0 < y / L := by positivity
    have := mul_le_mul_of_nonneg_left hstep1 hyL.le
    linarith
  have h7pos : 0 < 7 - 305989 / 10000 / L := by
    have : 305989 / 10000 / L < 7 := by rw [div_lt_iff₀ hL0]; linarith
    linarith
  have hbrpos : 0 < y / L * (7 - 305989 / 10000 / L) := by positivity
  have hσpos : 0 < σ := lt_trans hσ0pos h15
  have hPsi1 : Ctw / 15 * (σ * (y / L * (7 - 305989 / 10000 / L))) ≤
      ∑ k ∈ Icc 1 200, PsiK x y k := by
    refine le_trans ?_ h14s
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : σ * (a8 * σ / 200 - b) ≤ a8 * ∑ k ∈ Icc 1 200, Sk y k ^ 2 - b * σ := by
      have := mul_le_mul_of_nonneg_left hCS ha8pos.le
      nlinarith
    have := mul_le_mul_of_nonneg_left hbr hσpos.le
    linarith
  have hPsi2 : Ctw / 15 * (200 * y ^ 2 / L ^ 2 * (7 - 562056 / 10000 / L)) ≤
      ∑ k ∈ Icc 1 200, PsiK x y k := by
    refine le_trans ?_ hPsi1
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h2 := sec9_step2 L hL350.le
    have e : σ0 * (y / L * (7 - 305989 / 10000 / L)) = 200 * y ^ 2 / L ^ 2 *
        ((7 - 305989 / 10000 / L) * (1 - 36581 / 10000 / L)) := by rw [hσ0]; field_simp
    have h3 : σ0 * (y / L * (7 - 305989 / 10000 / L)) ≤ σ * (y / L * (7 - 305989 / 10000 / L)) :=
      mul_le_mul_of_nonneg_right h15.le hbrpos.le
    have h4 : 200 * y ^ 2 / L ^ 2 * (7 - 562056 / 10000 / L) ≤ 200 * y ^ 2 / L ^ 2 *
        ((7 - 305989 / 10000 / L) * (1 - 36581 / 10000 / L)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  -- Lemma 9
  have hy2 : Real.log (y / 2) = L - Real.log 2 := Real.log_div hy0.ne' (by norm_num)
  have hl2 := Real.log_two_lt_d9
  set D := Real.log (y / 2) * (83 / 10 + Real.log (y / 2)) with hD
  have hDpos : 0 < D := by
    rw [hD, hy2]; have : 0 < L - Real.log 2 := by linarith
    positivity
  have h9x := h9 x hx0 hL350
  rw [← hy, ← hD] at h9x
  have hDL := sec9_logy2 L hL350.le
  rw [← hy2, ← hD] at hDL
  have h3 := (sec9_step3 L hL350.le)
  -- `N(x) - N(y) > ΣΨ · D/(8Cy) ≥ (200y/120)(7 - 56.2056/L)(D/L²)`
  set Δ := (NCount x : ℝ) - NCount y with hΔ
  have hkey : Ctw / 15 * (200 * y ^ 2 / L ^ 2 * (7 - 562056 / 10000 / L)) ≤
      Δ * (8 * Ctw * y / D) := le_trans hPsi2 h9x
  have h7' : 0 < 7 - 562056 / 10000 / L := by
    have : 562056 / 10000 / L < 7 := by rw [div_lt_iff₀ hL0]; linarith
    linarith
  have hfin : 200 * y / 120 * ((7 - 562056 / 10000 / L) * (D / L ^ 2)) ≤ Δ := by
    have e : Δ * (8 * Ctw * y / D) = Δ * (8 * Ctw * y) / D := by ring
    rw [e, le_div_iff₀ hDpos] at hkey
    have e2 : 200 * y / 120 * ((7 - 562056 / 10000 / L) * (D / L ^ 2)) * (8 * Ctw * y) =
        Ctw / 15 * (200 * y ^ 2 / L ^ 2 * (7 - 562056 / 10000 / L)) * D := by
      field_simp; ring
    have hpos : 0 < 8 * Ctw * y := by positivity
    rw [← mul_le_mul_iff_of_pos_right hpos, e2]
    linarith
  have hge : 200 * y / 120 * (6974 / 1000) ≤
      200 * y / 120 * ((7 - 562056 / 10000 / L) * (D / L ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (7 - 562056 / 10000 / L) * (1 + 68986 / 10000 / L) ≤
        (7 - 562056 / 10000 / L) * (D / L ^ 2) := mul_le_mul_of_nonneg_left hDL.le h7'.le
    linarith [h3.1, h3.2]
  obtain ⟨f1, f2⟩ := sec9_final y hy0
  have hxy : x = 202 * y := by rw [hy]; ring
  rw [hxy]
  have : (202 * y - y) / 18 < (578 / 10000) * (202 * y - y) := by
    have : 0 < 202 * y - y := by linarith
    rw [div_lt_iff₀ (by norm_num)]; nlinarith
  have e3 : 6974 / 1000 * 200 * y / 120 = 200 * y / 120 * (6974 / 1000) := by ring
  linarith

end LeanLab.RieselVaughan1983
