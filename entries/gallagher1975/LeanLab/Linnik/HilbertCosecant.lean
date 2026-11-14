module

public import Mathlib
public import LeanLab.PNTPort.LargeSieve.Dual

/-!
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under the Apache 2.0 license.
Circular adaptation by Lean Lab contributors, 2026.
SPDX-License-Identifier: Apache-2.0
The matrix proof skeleton is adapted from anthropics/zeta-23-lean,
commit 16a5ce41304fcdaea4e0be7c132e1c361dc26da5,
zeta23/Zeta23/MV/Quadratic, EigenIdentity, Eigen and Duality.
Source author: Anthropic PBC. Source license: Apache 2.0.
https://github.com/anthropics/zeta-23-lean/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/zeta23/Zeta23/MV
Circular adaptation: Montgomery and Vaughan, Hilbert's inequality,
J. London Math. Soc. 1974, pp.73 to 82, Theorem 1 display 1.2.
https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

noncomputable section
open Finset Complex Matrix
open scoped ComplexConjugate
namespace LeanLab.Linnik.HilbertCosecant

/-- Polynomial upper bound used in Montgomery and Vaughan Lemma 1, p.76. -/
theorem cos_le_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f (t : ℝ) := 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hd (t : ℝ) : deriv f t = Real.sin t - t + t ^ 3 / 6 := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    have h := Real.sin_ge_sub_cube (show 0 ≤ t by simp only [interior_Ici, Set.mem_Ioi] at ht; exact ht.le)
    linarith
  have h := hm (by simp) hx hx
  dsimp [f] at h
  simp only [Real.cos_zero] at h
  linarith

/-- Montgomery and Vaughan Lemma 1 on the positive half period, p.76. -/
theorem cosecant_cotangent_bound {x : ℝ} (hx : 0 < x) (hxpi : x ≤ Real.pi / 2) :
    1 / Real.sin x ^ 2 + 2 * |Real.cos x / Real.sin x ^ 2| ≤ 3 / x ^ 2 := by
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hxpi⟩
  have hx2 : x ^ 2 < 6 := by
    have hp := Real.pi_lt_four
    have : x < 2 := by linarith
    nlinarith
  have hl : 0 ≤ x - x ^ 3 / 6 := by nlinarith
  have hsin := Real.sin_ge_sub_cube hx.le
  have hsq : (x - x ^ 3 / 6) ^ 2 ≤ Real.sin x ^ 2 := pow_le_pow_left₀ hl hsin 2
  have hcos := cos_le_quartic hx.le
  have hm := mul_le_mul_of_nonneg_left hcos (sq_nonneg x)
  have hmain : x ^ 2 * (1 + 2 * Real.cos x) ≤ 3 * Real.sin x ^ 2 := by
    nlinarith [hsq]
  rw [abs_of_nonneg (div_nonneg hc (sq_nonneg _))]
  apply (le_div_iff₀ (sq_pos_of_pos hx)).mpr
  have hsne := hs.ne'
  field_simp
  nlinarith [hmain]

/-- The circular partial fraction identity, Montgomery and Vaughan p.79 display 3.6. -/
theorem cosecant_product {a b c : ℝ}
    (hab : Real.sin (a - b) ≠ 0) (hac : Real.sin (a - c) ≠ 0)
    (hbc : Real.sin (b - c) ≠ 0) :
    (1 / Real.sin (a - b)) * (1 / Real.sin (a - c)) =
      (1 / Real.sin (b - c)) *
        (Real.cos (a - b) / Real.sin (a - b) -
          Real.cos (a - c) / Real.sin (a - c)) := by
  have hid : Real.sin (b - c) =
      Real.sin (a - c) * Real.cos (a - b) -
        Real.cos (a - c) * Real.sin (a - b) := by
    rw [← Real.sin_sub]
    congr 1
    ring
  field_simp
  nlinarith [hid]

open LeanLab.PNTPort.LargeSieve

/-- Sharp one sided inverse square spacing bound. Montgomery and Vaughan p.80. -/
theorem sum_inv_sq_sep_sharp {ι : Type*} (T : Finset ι) (t : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ i ∈ T, δ ≤ t i)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → δ ≤ |t i - t j|) :
    ∑ i ∈ T, 1 / t i ^ 2 ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  set k : ι → ℕ := fun i => ⌊t i / δ⌋₊ with hk
  have hk1 : ∀ i ∈ T, 1 ≤ k i := by
    intro i hi
    exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ, one_mul]; exact hpos i hi)
  have hkle : ∀ i ∈ T, (k i : ℝ) * δ ≤ t i := by
    intro i hi
    have := Nat.floor_le (div_nonneg (hδ.le.trans (hpos i hi)) hδ.le)
    exact (le_div_iff₀ hδ).1 this
  have hinj : Set.InjOn k T := by
    intro i hi j hj hij
    by_contra hne
    have hs := hsep i hi j hj hne
    have hi0 : 0 ≤ t i / δ := div_nonneg (hδ.le.trans (hpos i hi)) hδ.le
    have hj0 : 0 ≤ t j / δ := div_nonneg (hδ.le.trans (hpos j hj)) hδ.le
    have a1 := Nat.floor_le hi0
    have a2 := Nat.lt_floor_add_one (t i / δ)
    have b1 := Nat.floor_le hj0
    have b2 := Nat.lt_floor_add_one (t j / δ)
    have hij' : (⌊t i / δ⌋₊ : ℝ) = ⌊t j / δ⌋₊ := by exact_mod_cast hij
    have : |t i / δ - t j / δ| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at this
    linarith
  have step1 : ∑ i ∈ T, 1 / t i ^ 2 ≤ ∑ i ∈ T, (1 / δ ^ 2) * (((k i : ℕ) : ℝ) ^ 2)⁻¹ := by
    apply sum_le_sum
    intro i hi
    have hk0 : (0 : ℝ) < k i := by exact_mod_cast hk1 i hi
    rw [← one_div, one_div_mul_one_div, ← mul_pow, mul_comm δ]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (hkle i hi) 2
  have step2 : ∑ i ∈ T, (((k i : ℕ) : ℝ) ^ 2)⁻¹ = ∑ j ∈ T.image k, ((j : ℝ) ^ 2)⁻¹ :=
    (sum_image (f := fun j : ℕ => ((j : ℝ) ^ 2)⁻¹) hinj).symm
  have step3 : ∑ j ∈ T.image k, ((j : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
    simpa only [one_div] using
      sum_le_hasSum (T.image k) (fun n _ => by positivity)
        hasSum_zeta_two
  rw [← mul_sum, step2] at step1
  calc
    _ ≤ 1 / δ ^ 2 * ∑ j ∈ T.image k, ((j : ℝ) ^ 2)⁻¹ := step1
    _ ≤ 1 / δ ^ 2 * (Real.pi ^ 2 / 6) :=
      mul_le_mul_of_nonneg_left step3 (by positivity)
    _ = _ := by ring

/-- Sharp circular inverse square spacing bound. Montgomery and Vaughan p.80. -/
theorem sum_off_diag_sharp {ι : Type*} [DecidableEq ι] {s : Finset ι} {α : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hs : Spaced s α δ) {r : ι} (hr : r ∈ s) :
    ∑ r' ∈ s.erase r, 1 / dist0 (α r - α r') ^ 2 ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  set t : ι → ℝ := fun r' => α r' - α r - round (α r' - α r) with ht
  have hdt : ∀ r', dist0 (α r - α r') = |t r'| := by
    intro r'; rw [dist0_sub_comm]; rfl
  have hge : ∀ r' ∈ s.erase r, δ ≤ |t r'| := by
    intro r' hr'
    rw [← hdt]
    exact hs r hr r' (mem_of_mem_erase hr') (ne_of_mem_erase hr').symm
  have hsep : ∀ r1 ∈ s.erase r, ∀ r2 ∈ s.erase r, r1 ≠ r2 → δ ≤ |t r1 - t r2| := by
    intro r1 h1 r2 h2 hne
    have := hs r1 (mem_of_mem_erase h1) r2 (mem_of_mem_erase h2) hne
    refine this.trans ?_
    have h := dist0_le_abs_sub_int (α r1 - α r2)
      (round (α r1 - α r) - round (α r2 - α r))
    convert h using 2
    simp only [ht]
    push_cast
    ring
  rw [← sum_filter_add_sum_filter_not (s.erase r) (fun r' => 0 < t r')]
  have hP : ∑ r' ∈ (s.erase r).filter (fun r' => 0 < t r'), 1 / dist0 (α r - α r') ^ 2
      ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
    have := sum_inv_sq_sep_sharp ((s.erase r).filter (fun r' => 0 < t r')) t hδ
      (by
        intro i hi
        rw [mem_filter] at hi
        have := hge i hi.1
        rwa [abs_of_pos hi.2] at this)
      (by
        intro i hi j hj hne
        exact hsep i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hne)
    refine le_of_eq_of_le (sum_congr rfl ?_) this
    intro i hi
    rw [hdt, sq_abs]
  have hN : ∑ r' ∈ (s.erase r).filter (fun r' => ¬ 0 < t r'), 1 / dist0 (α r - α r') ^ 2
      ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
    have := sum_inv_sq_sep_sharp ((s.erase r).filter (fun r' => ¬ 0 < t r')) (fun r' => -t r') hδ
      (by
        intro i hi
        rw [mem_filter] at hi
        have h1 := hge i hi.1
        have h2 : t i ≤ 0 := not_lt.1 hi.2
        rw [abs_of_nonpos h2] at h1
        exact h1)
      (by
        intro i hi j hj hne
        have := hsep i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hne
        rwa [show -t i - -t j = -(t i - t j) by ring, abs_neg])
    refine le_of_eq_of_le (sum_congr rfl ?_) this
    intro i hi
    rw [hdt, sq_abs, neg_sq]
  calc _ ≤ Real.pi ^ 2 / (6 * δ ^ 2) + Real.pi ^ 2 / (6 * δ ^ 2) := add_le_add hP hN
    _ = Real.pi ^ 2 / (3 * δ ^ 2) := by ring


/-- Circular eigenvector identity. Montgomery and Vaughan p.79 displays 3.3 to 3.9.
The two real kernels satisfy the circular partial fraction identity. -/
theorem eigen_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K C : ι → ι → ℝ) (hK : ∀ m n, K n m = -K m n)
    (hprod : ∀ m n p, m ≠ n → m ≠ p → n ≠ p →
      K m n * K m p = K n p * (C m n - C m p))
    (u : ι → ℂ) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ univ.erase m, (K m n : ℂ) * u n = (μ : ℂ) * I * u m)
    (m : ι) :
    μ ^ 2 * ‖u m‖ ^ 2 =
      (∑ n ∈ univ.erase m, K m n ^ 2 * ‖u n‖ ^ 2) +
        2 * ∑ n ∈ univ.erase m, C m n * K m n * (u m * conj (u n)).re := by
  classical
  let S := univ.erase m
  let R (n p : ι) := (u n * conj (u p)).re
  have hRs (n p : ι) : R n p = R p n := by simp [R, mul_re]; ring
  have hRd (n : ι) : R n n = ‖u n‖ ^ 2 := by
    simp only [R, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hA : μ ^ 2 * ‖u m‖ ^ 2 = ∑ n ∈ S, ∑ p ∈ S, K m n * K m p * R n p := by
    have hn (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have h1 : μ ^ 2 * ‖u m‖ ^ 2 = ‖(μ : ℂ) * I * u m‖ ^ 2 := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        mul_pow, Real.norm_eq_abs, sq_abs]
    rw [h1, ← heig m, hn, map_sum, sum_mul_sum, Complex.re_sum]
    apply sum_congr rfl
    intro n _
    rw [Complex.re_sum]
    apply sum_congr rfl
    intro p _
    simp only [map_mul, Complex.conj_ofReal]
    have hh : (K m n : ℂ) * u n * ((K m p : ℂ) * conj (u p)) =
        ((K m n * K m p : ℝ) : ℂ) * (u n * conj (u p)) := by push_cast; ring
    rw [hh, Complex.re_ofReal_mul]
  have hB : (∑ n ∈ S, ∑ p ∈ S, K m n * K m p * R n p) =
      (∑ n ∈ S, K m n ^ 2 * ‖u n‖ ^ 2) +
        ∑ n ∈ S, ∑ p ∈ S.erase n, K m n * K m p * R n p := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    rw [← add_sum_erase S _ hn, hRd]
    ring
  let G (n p : ι) := C m n * K n p * R n p
  have hF (n : ι) (hn : n ∈ S) (p : ι) (hp : p ∈ S.erase n) :
      K m n * K m p * R n p = G n p + G p n := by
    have hn' : m ≠ n := (mem_erase.mp hn).1.symm
    have hp' : m ≠ p := (mem_erase.mp (mem_erase.mp hp).2).1.symm
    have hnp : n ≠ p := (mem_erase.mp hp).1.symm
    rw [hprod m n p hn' hp' hnp]
    dsimp [G]
    rw [hK p n, hRs p n]
    ring
  have hOff : (∑ n ∈ S, ∑ p ∈ S.erase n, K m n * K m p * R n p) =
      2 * ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
    have hswap : (∑ n ∈ S, ∑ p ∈ S.erase n, G p n) =
        ∑ n ∈ S, ∑ p ∈ S.erase n, G n p := by
      apply sum_comm'
      intro n p
      simp only [mem_erase]
      tauto
    calc
      _ = ∑ n ∈ S, ∑ p ∈ S.erase n, (G n p + G p n) := by
        apply sum_congr rfl
        intro n hn
        exact sum_congr rfl (fun p hp => hF n hn p hp)
      _ = (∑ n ∈ S, ∑ p ∈ S.erase n, G n p) +
          ∑ n ∈ S, ∑ p ∈ S.erase n, G p n := by simp only [sum_add_distrib]
      _ = _ := by rw [hswap]; ring
  have hInner (n : ι) (hn : n ∈ S) :
      (∑ p ∈ S.erase n, G n p) = C m n * K m n * R m n := by
    let W : ℂ := ∑ p ∈ S.erase n, (K n p : ℂ) * conj (u p)
    have hi : (∑ p ∈ S.erase n, G n p) = C m n * (u n * W).re := by
      simp only [W, mul_sum, Complex.re_sum]
      apply sum_congr rfl
      intro p _
      have hh : u n * ((K n p : ℂ) * conj (u p)) =
          (K n p : ℂ) * (u n * conj (u p)) := by ring
      rw [hh, Complex.re_ofReal_mul]
      dsimp [G, R]
      ring
    have hconj := congrArg conj (heig n)
    simp only [map_sum, map_mul, Complex.conj_ofReal, Complex.conj_I] at hconj
    have hmn : m ∈ univ.erase n := mem_erase.mpr ⟨(mem_erase.mp hn).1.symm, mem_univ _⟩
    have hsplit := add_sum_erase (univ.erase n)
      (fun p => (K n p : ℂ) * conj (u p)) hmn
    have hSS : (univ.erase n).erase m = S.erase n := by
      dsimp [S]
      rw [erase_right_comm]
    rw [hSS] at hsplit
    rw [← hsplit] at hconj
    have hW : W = -((μ : ℂ) * I * conj (u n)) - (K n m : ℂ) * conj (u m) := by
      dsimp [W]
      linear_combination hconj
    have hkill : (u n * (-((μ : ℂ) * I * conj (u n)))).re = 0 := by
      have hh : u n * (-((μ : ℂ) * I * conj (u n))) =
          -((μ : ℂ) * (u n * conj (u n))) * I := by ring
      rw [hh, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp [-Complex.ofReal_pow]
    rw [hi, hW, mul_sub, Complex.sub_re, hkill]
    have hh : u n * ((K n m : ℂ) * conj (u m)) =
        (K n m : ℂ) * (u n * conj (u m)) := by ring
    rw [hh, Complex.re_ofReal_mul, hK m n]
    change C m n * (0 - -K m n * R n m) = C m n * K m n * R m n
    rw [hRs n m]
    ring
  rw [hA, hB, hOff]
  congr 1
  congr 1
  apply sum_congr rfl
  intro n hn
  exact hInner n hn


/-- The eigenvalue estimate from symmetric row bounds. Montgomery and Vaughan pp.79 and 80. -/
theorem eigen_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K C : ι → ι → ℝ) (hK : ∀ m n, K n m = -K m n)
    (hC : ∀ m n, C n m = -C m n)
    (hprod : ∀ m n p, m ≠ n → m ≠ p → n ≠ p →
      K m n * K m p = K n p * (C m n - C m p))
    {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ m, ∑ n ∈ univ.erase m, (K m n ^ 2 + 2 * |C m n * K m n|) ≤ B ^ 2)
    (u : ι → ℂ) (hu : ∑ n, ‖u n‖ ^ 2 = 1) (μ : ℝ)
    (heig : ∀ m, ∑ n ∈ univ.erase m, (K m n : ℂ) * u n = (μ : ℂ) * I * u m) :
    |μ| ≤ B := by
  have hswap (F : ι → ι → ℝ) : (∑ m, ∑ n ∈ univ.erase m, F m n) =
      ∑ n, ∑ m ∈ univ.erase n, F m n := by
    apply sum_comm'
    intro m n
    simp only [mem_univ, mem_erase, true_and, and_true]
    exact ⟨Ne.symm, Ne.symm⟩
  let A (m n : ι) := |C m n * K m n|
  let L (m n : ι) := K m n ^ 2 + A m n
  have hAs (m n : ι) : A n m = A m n := by dsimp [A]; rw [hC m n, hK m n, neg_mul_neg]
  have hLs (m n : ι) : L n m = L m n := by dsimp [L]; rw [hK m n, neg_sq, hAs]
  have hp (m n : ι) :
      K m n ^ 2 * ‖u n‖ ^ 2 + 2 * (C m n * K m n * (u m * conj (u n)).re) ≤
        L m n * ‖u n‖ ^ 2 + A m n * ‖u m‖ ^ 2 := by
    have hre : |(u m * conj (u n)).re| ≤ ‖u m‖ * ‖u n‖ := by
      simpa [norm_mul] using Complex.abs_re_le_norm (u m * conj (u n))
    have hh : C m n * K m n * (u m * conj (u n)).re ≤ A m n * (‖u m‖ * ‖u n‖) :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hre (abs_nonneg _))
    have hnn : 0 ≤ A m n := abs_nonneg _
    have hsq := mul_nonneg hnn (sq_nonneg (‖u m‖ - ‖u n‖))
    dsimp [L]
    nlinarith
  have hid : μ ^ 2 = ∑ m, ∑ n ∈ univ.erase m,
      (K m n ^ 2 * ‖u n‖ ^ 2 + 2 * (C m n * K m n * (u m * conj (u n)).re)) := by
    calc
      μ ^ 2 = ∑ m, μ ^ 2 * ‖u m‖ ^ 2 := by rw [← mul_sum, hu, mul_one]
      _ = _ := by
        apply sum_congr rfl
        intro m _
        rw [eigen_identity K C hK hprod u μ heig m, sum_add_distrib, ← mul_sum]
  have hle : μ ^ 2 ≤ B ^ 2 := by
    calc
      _ ≤ ∑ m, ∑ n ∈ univ.erase m, (L m n * ‖u n‖ ^ 2 + A m n * ‖u m‖ ^ 2) := by
        rw [hid]
        exact sum_le_sum (fun m _ => sum_le_sum (fun n _ => hp m n))
      _ = (∑ m, ∑ n ∈ univ.erase m, L m n * ‖u n‖ ^ 2) +
          ∑ m, ∑ n ∈ univ.erase m, A m n * ‖u m‖ ^ 2 := by simp only [sum_add_distrib]
      _ = (∑ m, ∑ n ∈ univ.erase m, L m n * ‖u m‖ ^ 2) +
          ∑ m, ∑ n ∈ univ.erase m, A m n * ‖u m‖ ^ 2 := by
        congr 1
        rw [hswap]
        apply sum_congr rfl
        intro m _
        apply sum_congr rfl
        intro n _
        rw [hLs]
      _ = ∑ m, (∑ n ∈ univ.erase m, (K m n ^ 2 + 2 * |C m n * K m n|)) * ‖u m‖ ^ 2 := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro m _
        rw [sum_mul, ← sum_add_distrib]
        apply sum_congr rfl
        intro n _
        dsimp [L, A]
        ring
      _ ≤ ∑ m, B ^ 2 * ‖u m‖ ^ 2 :=
        sum_le_sum (fun m _ => mul_le_mul_of_nonneg_right (hrow m) (sq_nonneg _))
      _ = B ^ 2 := by rw [← mul_sum, hu, mul_one]
  nlinarith [sq_abs μ, abs_nonneg μ]

open Unitary
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `star v ⬝ᵥ v = Σ ‖v_i‖²` (as a complex number). -/
lemma star_dotProduct_self (v : ι → ℂ) : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

/-- Spectral expansion of the Hermitian form, complex-valued:
`x* A x = Σ_i ν_i ‖(U* x)_i‖²` with `U` the eigenvector unitary. -/
lemma star_dotProduct_mulVec_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    star x ⬝ᵥ (A *ᵥ x)
      = ((∑ i, hA.eigenvalues i *
          ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  conv_lhs => rw [hA.spectral_theorem]
  rw [conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) U, hsc, ← hc_def]
  simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, dotProduct, mulVec_diagonal, Pi.star_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.conj_mul', mul_left_comm]

/-- `Σ ‖(U* x)_i‖² = Σ ‖x_i‖²` for the eigenvector unitary `U`. -/
lemma sum_norm_sq_unitary {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℂ) :
    ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  set U : Matrix ι ι ℂ := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  have h : star c ⬝ᵥ c = star x ⬝ᵥ x := by
    have hU : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
    rw [← hsc, hc_def, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  rw [star_dotProduct_self, star_dotProduct_self] at h
  exact_mod_cast h



/-- Spectral reduction for a real antisymmetric kernel. Montgomery and Vaughan p.79.
Adapted from the Apache 2.0 MV Duality module of Anthropic PBC. -/
theorem form_bound_of_eigen_bound (K : ι → ι → ℝ)
    (hK : ∀ r s, K s r = -K r s) (hdiag : ∀ r, K r r = 0) {B : ℝ}
    (hb : ∀ (u : ι → ℂ), (∑ n, ‖u n‖ ^ 2 = 1) → ∀ μ : ℝ,
      (∀ m, ∑ n ∈ univ.erase m, (K m n : ℂ) * u n = (μ : ℂ) * I * u m) → |μ| ≤ B)
    (b : ι → ℂ) :
    ‖∑ r, ∑ s ∈ univ.erase r, b r * conj (b s) * (K r s : ℂ)‖ ≤
      B * ∑ r, ‖b r‖ ^ 2 := by
  let M : Matrix ι ι ℂ := fun r s => (K r s : ℂ) * I
  have hM : M.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro r s
    simp only [M, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I, hK r s]
    push_cast
    ring
  have hev (j : ι) : |hM.eigenvalues j| ≤ B := by
    let ν := hM.eigenvalues j
    let v : ι → ℂ := ⇑(hM.eigenvectorBasis j)
    have hv : M *ᵥ v = ν • v := hM.mulVec_eigenvectorBasis j
    have hunit : ∑ n, ‖v n‖ ^ 2 = 1 := by
      have h1 := hM.eigenvectorBasis.orthonormal.1 j
      rw [← EuclideanSpace.norm_sq_eq, h1, one_pow]
    have heig (m : ι) : ∑ n ∈ univ.erase m, (K m n : ℂ) * v n =
        ((-ν : ℝ) : ℂ) * I * v m := by
      have hm := congrFun hv m
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] at hm
      have hsplit : (∑ s, M m s * v s) =
          ∑ s ∈ univ.erase m, (K m s : ℂ) * I * v s := by
        rw [← add_sum_erase _ _ (mem_univ m)]
        simp [M, hdiag]
      rw [hsplit] at hm
      have hh : (∑ s ∈ univ.erase m, (K m s : ℂ) * I * v s) =
          I * ∑ s ∈ univ.erase m, (K m s : ℂ) * v s := by
        rw [mul_sum]
        exact sum_congr rfl (fun _ _ => by ring)
      rw [hh] at hm
      calc
        _ = -I * (I * ∑ s ∈ univ.erase m, (K m s : ℂ) * v s) := by
          rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
        _ = -I * ((ν : ℂ) * v m) := by rw [hm]
        _ = _ := by push_cast; ring
    simpa [ν] using hb v hunit (-ν) heig
  have hform : ‖star b ⬝ᵥ (M *ᵥ b)‖ ≤ B * ∑ r, ‖b r‖ ^ 2 := by
    rw [star_dotProduct_mulVec_eq hM, Complex.norm_real, Real.norm_eq_abs,
      ← sum_norm_sq_unitary hM b, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j _
    rw [abs_mul, abs_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right (hev j) (sq_nonneg _)
  have hsum : (∑ r, ∑ s ∈ univ.erase r, b r * conj (b s) * (K r s : ℂ)) =
      conj (star b ⬝ᵥ (M *ᵥ b)) * I := by
    have he (r : ι) : (∑ s ∈ univ.erase r, b r * conj (b s) * (K r s : ℂ)) =
        ∑ s, b r * conj (b s) * (K r s : ℂ) := by
      rw [← add_sum_erase _ _ (mem_univ r)]
      simp [hdiag]
    simp only [he, dotProduct, Matrix.mulVec, M, Pi.star_apply, Complex.star_def,
      map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, Complex.conj_I, sum_mul, mul_sum]
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro s _
    linear_combination (b r * conj (b s) * (K r s : ℂ)) * Complex.I_mul_I
  rw [hsum, norm_mul, Complex.norm_I, mul_one, Complex.norm_conj]
  exact hform


/-- Positive circular distance excludes a zero cosecant denominator. -/
theorem sin_ne_zero_of_dist0_pos {θ : ℝ} (hθ : 0 < dist0 θ) :
    Real.sin (Real.pi * θ) ≠ 0 := by
  intro hz
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hz
  have he : θ = (n : ℝ) := by nlinarith [Real.pi_pos]
  subst θ
  simp [dist0] at hθ

/-- Montgomery and Vaughan Lemma 1, p.76, in circular distance normalization. -/
theorem kernel_bound {θ : ℝ} (hθ : 0 < dist0 θ) :
    (1 / Real.sin (Real.pi * θ)) ^ 2 +
      2 * |(Real.cos (Real.pi * θ) / Real.sin (Real.pi * θ)) *
        (1 / Real.sin (Real.pi * θ))| ≤
      (3 / Real.pi ^ 2) * (1 / dist0 θ ^ 2) := by
  let t := θ - (round θ : ℝ)
  have ht : |t| ≤ 1 / 2 := abs_sub_round θ
  have habs : |Real.pi * t| = Real.pi * dist0 θ := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    rfl
  have hsin : |Real.sin (Real.pi * t)| = |Real.sin (Real.pi * θ)| := by
    dsimp [t]
    rw [mul_sub, mul_comm Real.pi (round θ : ℝ), Real.sin_sub_int_mul_pi, abs_mul]
    simp
  have hcos : |Real.cos (Real.pi * t)| = |Real.cos (Real.pi * θ)| := by
    dsimp [t]
    rw [mul_sub, mul_comm Real.pi (round θ : ℝ), Real.cos_sub_int_mul_pi, abs_mul]
    simp
  have hx : 0 < Real.pi * dist0 θ := mul_pos Real.pi_pos hθ
  have hxpi : Real.pi * dist0 θ ≤ Real.pi / 2 := by
    nlinarith [dist0_le_half θ, Real.pi_pos]
  have hc : 0 ≤ Real.cos (Real.pi * dist0 θ) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hxpi⟩
  have hs2 : Real.sin (Real.pi * θ) ^ 2 = Real.sin (Real.pi * dist0 θ) ^ 2 := by
    have he := Real.abs_sin_eq_sin_abs_of_abs_le_pi
      (show |Real.pi * t| ≤ Real.pi by rw [habs]; linarith [Real.pi_pos])
    rw [habs, hsin] at he
    rw [← he, sq_abs]
  have hcabs : |Real.cos (Real.pi * θ)| = Real.cos (Real.pi * dist0 θ) := by
    rw [← hcos, ← habs, Real.cos_abs, abs_of_nonneg]
    simpa [← Real.cos_abs, habs] using hc
  have hh := cosecant_cotangent_bound hx hxpi
  have he1 : (1 / Real.sin (Real.pi * θ)) ^ 2 =
      1 / Real.sin (Real.pi * dist0 θ) ^ 2 := by rw [div_pow, one_pow, hs2]
  have he2 : |(Real.cos (Real.pi * θ) / Real.sin (Real.pi * θ)) *
      (1 / Real.sin (Real.pi * θ))| =
      |Real.cos (Real.pi * dist0 θ) / Real.sin (Real.pi * dist0 θ) ^ 2| := by
    rw [div_mul_div_comm, mul_one, ← pow_two]
    simp only [abs_div, abs_pow, sq_abs, hcabs, abs_of_nonneg hc, hs2]
  rw [he1, he2]
  convert hh using 1
  ring

/-- Montgomery and Vaughan p.73 Theorem 1 display 1.2, for a finite index type. -/
theorem cosecant_hilbert_fintype (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : Spaced univ α δ) (b : ι → ℂ) :
    ‖∑ r, ∑ s ∈ univ.erase r,
      b r * conj (b s) / (Real.sin (Real.pi * (α r - α s)) : ℂ)‖ ≤
      (1 / δ) * ∑ r, ‖b r‖ ^ 2 := by
  let K (r s : ι) := 1 / Real.sin (Real.pi * (α r - α s))
  let C (r s : ι) := Real.cos (Real.pi * (α r - α s)) / Real.sin (Real.pi * (α r - α s))
  have hK (r s : ι) : K s r = -K r s := by
    dsimp [K]
    rw [show Real.pi * (α s - α r) = -(Real.pi * (α r - α s)) by ring, Real.sin_neg]
    simp
  have hC (r s : ι) : C s r = -C r s := by
    dsimp [C]
    rw [show Real.pi * (α s - α r) = -(Real.pi * (α r - α s)) by ring,
      Real.sin_neg, Real.cos_neg, div_neg]
  have hsin (r s : ι) (hne : r ≠ s) : Real.sin (Real.pi * (α r - α s)) ≠ 0 :=
    sin_ne_zero_of_dist0_pos (hδ.trans_le (hs r (mem_univ _) s (mem_univ _) hne))
  have hprod (m n p : ι) (hmn : m ≠ n) (hmp : m ≠ p) (hnp : n ≠ p) :
      K m n * K m p = K n p * (C m n - C m p) := by
    have hh := cosecant_product
      (a := Real.pi * α m) (b := Real.pi * α n) (c := Real.pi * α p)
      (by rw [← mul_sub]; exact hsin m n hmn)
      (by rw [← mul_sub]; exact hsin m p hmp)
      (by rw [← mul_sub]; exact hsin n p hnp)
    simpa only [← mul_sub] using hh
  have hrow (m : ι) : ∑ n ∈ univ.erase m, (K m n ^ 2 + 2 * |C m n * K m n|) ≤
      (1 / δ) ^ 2 := by
    calc
      _ ≤ ∑ n ∈ univ.erase m, (3 / Real.pi ^ 2) * (1 / dist0 (α m - α n) ^ 2) := by
        apply sum_le_sum
        intro n hn
        exact kernel_bound (hδ.trans_le (hs m (mem_univ _) n (mem_univ _) (ne_of_mem_erase hn).symm))
      _ = (3 / Real.pi ^ 2) * ∑ n ∈ univ.erase m, 1 / dist0 (α m - α n) ^ 2 := (mul_sum ..).symm
      _ ≤ (3 / Real.pi ^ 2) * (Real.pi ^ 2 / (3 * δ ^ 2)) :=
        mul_le_mul_of_nonneg_left (sum_off_diag_sharp hδ hs (mem_univ m)) (by positivity)
      _ = _ := by field_simp
  have hh := form_bound_of_eigen_bound K hK (by intro r; simp [K])
    (fun u hu μ heig => eigen_bound K C hK hC hprod (by positivity) hrow u hu μ heig) b
  convert hh using 1
  congr 1
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s _
  simp [K, div_eq_mul_inv]

/-- Montgomery and Vaughan p.73 Theorem 1 display 1.2, for any finite family. -/
theorem cosecant_hilbert {κ : Type*} [DecidableEq κ] (s : Finset κ) (α : κ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hs : Spaced s α δ) (b : κ → ℂ) :
    ‖∑ r ∈ s, ∑ t ∈ s.erase r,
      b r * conj (b t) / (Real.sin (Real.pi * (α r - α t)) : ℂ)‖ ≤
      (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  have hsp : Spaced (univ : Finset s) (fun r => α r) δ := by
    intro r _ t _ hne
    exact hs r r.property t t.property (fun h => hne (Subtype.ext h))
  have hh := cosecant_hilbert_fintype (fun r : s => α r) hδ hsp (fun r : s => b r)
  have he (r : κ) : b r * conj (b r) / (Real.sin (Real.pi * (α r - α r)) : ℂ) = 0 := by simp
  have her (r : s) : (∑ t ∈ (univ : Finset s).erase r,
      b r * conj (b t) / (Real.sin (Real.pi * (α r - α t)) : ℂ)) =
        ∑ t : s, b r * conj (b t) / (Real.sin (Real.pi * (α r - α t)) : ℂ) :=
    Finset.sum_erase _ (by simp)
  simp_rw [her] at hh
  have hex (r : κ) : (∑ t ∈ s.erase r,
      b r * conj (b t) / (Real.sin (Real.pi * (α r - α t)) : ℂ)) =
        ∑ t ∈ s, b r * conj (b t) / (Real.sin (Real.pi * (α r - α t)) : ℂ) :=
    Finset.sum_erase s (he r)
  simp_rw [hex]
  simpa only [← Finset.sum_coe_sort s] using hh

/-- Montgomery and Vaughan p.74 Corollary 1 display 1.4.
The cotangent form has the same circular spacing constant. -/
theorem cotangent_hilbert {κ : Type*} [DecidableEq κ] (s : Finset κ) (α : κ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hs : Spaced s α δ) (b : κ → ℂ) :
    ‖∑ r ∈ s, ∑ t ∈ s.erase r,
      b r * conj (b t) *
        ((Real.cos (Real.pi * (α r - α t)) / Real.sin (Real.pi * (α r - α t)) : ℝ) : ℂ)‖ ≤
      (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  let v (ε : ℝ) (r : κ) := b r * e (ε * α r / 2)
  let H (u : κ → ℂ) := ∑ r ∈ s, ∑ t ∈ s.erase r,
    u r * conj (u t) / (Real.sin (Real.pi * (α r - α t)) : ℂ)
  have hphase (ε : ℝ) (r t : κ) : v ε r * conj (v ε t) =
      b r * conj (b t) * e (ε * (α r - α t) / 2) := by
    have he : e (ε * α r / 2) * conj (e (ε * α t / 2)) = e (ε * (α r - α t) / 2) := by
      rw [← e_neg, ← e_add]
      congr 1
      ring
    simp only [v, map_mul]
    calc
      _ = (b r * conj (b t)) * (e (ε * α r / 2) * conj (e (ε * α t / 2))) := by ring
      _ = _ := by rw [he]
  have hcos (x : ℝ) : e (x / 2) + e (-x / 2) = 2 * (Real.cos (Real.pi * x) : ℂ) := by
    have he : e (x / 2) = (Real.cos (Real.pi * x) : ℂ) +
        (Real.sin (Real.pi * x) : ℂ) * I := by
      unfold e
      rw [show I * ((2 * Real.pi * (x / 2) : ℝ) : ℂ) =
        ((Real.pi * x : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [show -x / 2 = -(x / 2) by ring, e_neg, he]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have henergy (ε : ℝ) : ∑ r ∈ s, ‖v ε r‖ ^ 2 = ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simp only [v, norm_mul, norm_e, mul_one]
  have hH (ε : ℝ) : ‖H (v ε)‖ ≤ (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simpa only [H, henergy] using cosecant_hilbert s α hδ hs (v ε)
  have heq : (∑ r ∈ s, ∑ t ∈ s.erase r,
      b r * conj (b t) *
        ((Real.cos (Real.pi * (α r - α t)) / Real.sin (Real.pi * (α r - α t)) : ℝ) : ℂ)) =
      (1 / 2 : ℂ) * (H (v 1) + H (v (-1))) := by
    simp only [H, mul_add, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro t _
    rw [hphase, hphase]
    simp only [one_mul, neg_one_mul]
    have hc := hcos (α r - α t)
    rw [Complex.ofReal_div]
    simp only [div_eq_mul_inv] at hc ⊢
    linear_combination -(b r * conj (b t) * (Real.sin (Real.pi * (α r - α t)) : ℂ)⁻¹ / 2) * hc
  rw [heq, norm_mul]
  have hn : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num [norm_div]
  rw [hn]
  calc
    _ ≤ (1 / 2) * (‖H (v 1)‖ + ‖H (v (-1))‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1 / 2) * ((1 / δ) * (∑ r ∈ s, ‖b r‖ ^ 2) +
        (1 / δ) * ∑ r ∈ s, ‖b r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add (hH 1) (hH (-1))) (by norm_num)
    _ = _ := by ring

/-- Sharp inverse square packing on the real line. Auxiliary for p.74 display 1.6. -/
theorem sum_off_diag_real_sharp {ι : Type*} [DecidableEq ι] {s : Finset ι} {α : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hs : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → δ ≤ |α r - α t|) {r : ι} (hr : r ∈ s) :
    ∑ r' ∈ s.erase r, 1 / |α r - α r'| ^ 2 ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  set t : ι → ℝ := fun r' => α r' - α r with ht
  have hdt : ∀ r', |α r - α r'| = |t r'| := by
    intro r'; dsimp [t]; exact abs_sub_comm _ _
  have hge : ∀ r' ∈ s.erase r, δ ≤ |t r'| := by
    intro r' hr'
    rw [← hdt]
    exact hs r hr r' (mem_of_mem_erase hr') (ne_of_mem_erase hr').symm
  have hsep : ∀ r1 ∈ s.erase r, ∀ r2 ∈ s.erase r, r1 ≠ r2 → δ ≤ |t r1 - t r2| := by
    intro r1 h1 r2 h2 hne
    have hh := hs r1 (mem_of_mem_erase h1) r2 (mem_of_mem_erase h2) hne
    convert hh using 1
    congr 1
    dsimp [t]
    ring
  rw [← sum_filter_add_sum_filter_not (s.erase r) (fun r' => 0 < t r')]
  have hP : ∑ r' ∈ (s.erase r).filter (fun r' => 0 < t r'), 1 / |α r - α r'| ^ 2
      ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
    have := sum_inv_sq_sep_sharp ((s.erase r).filter (fun r' => 0 < t r')) t hδ
      (by
        intro i hi
        rw [mem_filter] at hi
        have := hge i hi.1
        rwa [abs_of_pos hi.2] at this)
      (by
        intro i hi j hj hne
        exact hsep i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hne)
    refine le_of_eq_of_le (sum_congr rfl ?_) this
    intro i hi
    rw [hdt, sq_abs]
  have hN : ∑ r' ∈ (s.erase r).filter (fun r' => ¬ 0 < t r'), 1 / |α r - α r'| ^ 2
      ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
    have := sum_inv_sq_sep_sharp ((s.erase r).filter (fun r' => ¬ 0 < t r')) (fun r' => -t r') hδ
      (by
        intro i hi
        rw [mem_filter] at hi
        have h1 := hge i hi.1
        have h2 : t i ≤ 0 := not_lt.1 hi.2
        rw [abs_of_nonpos h2] at h1
        exact h1)
      (by
        intro i hi j hj hne
        have := hsep i (mem_filter.1 hi).1 j (mem_filter.1 hj).1 hne
        rwa [show -t i - -t j = -(t i - t j) by ring, abs_neg])
    refine le_of_eq_of_le (sum_congr rfl ?_) this
    intro i hi
    rw [hdt, sq_abs, neg_sq]
  calc _ ≤ Real.pi ^ 2 / (6 * δ ^ 2) + Real.pi ^ 2 / (6 * δ ^ 2) := add_le_add hP hN
    _ = Real.pi ^ 2 / (3 * δ ^ 2) := by ring


/-- Montgomery and Vaughan p.74 Theorem 2 display 1.6, for a finite index type. -/
theorem hilbert_real_fintype (α : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ r t, r ≠ t → δ ≤ |α r - α t|) (b : ι → ℂ) :
    ‖∑ r, ∑ s ∈ univ.erase r,
      b r * conj (b s) / ((α r - α s : ℝ) : ℂ)‖ ≤
      (Real.pi / δ) * ∑ r, ‖b r‖ ^ 2 := by
  let K (r s : ι) := 1 / (α r - α s)
  have hK (r s : ι) : K s r = -K r s := by
    dsimp [K]
    rw [show α s - α r = -(α r - α s) by ring, div_neg]
  have hne (r s : ι) (hrs : r ≠ s) : α r - α s ≠ 0 := by
    have hh := hδ.trans_le (hs r s hrs)
    intro hz
    simp [hz] at hh
  have hprod (m n p : ι) (hmn : m ≠ n) (hmp : m ≠ p) (hnp : n ≠ p) :
      K m n * K m p = K n p * (K m n - K m p) := by
    dsimp [K]
    field_simp [hne m n hmn, hne m p hmp, hne n p hnp]
    ring
  have hrow (m : ι) : ∑ n ∈ univ.erase m, (K m n ^ 2 + 2 * |K m n * K m n|) ≤
      (Real.pi / δ) ^ 2 := by
    have hh := sum_off_diag_real_sharp (s := univ) (α := α) hδ
      (fun r _ t _ hrt => hs r t hrt) (mem_univ m)
    simp only [sq_abs] at hh
    calc
      _ = 3 * ∑ n ∈ univ.erase m, 1 / (α m - α n) ^ 2 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        rw [show K m n * K m n = K m n ^ 2 by ring, abs_sq]
        dsimp [K]
        rw [div_pow, one_pow]
        ring
      _ ≤ 3 * (Real.pi ^ 2 / (3 * δ ^ 2)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by field_simp
  have hh := form_bound_of_eigen_bound K hK (by intro r; simp [K])
    (fun u hu μ heig => eigen_bound K K hK hK hprod (by positivity) hrow u hu μ heig) b
  convert hh using 1
  congr 1
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s _
  simp [K, div_eq_mul_inv]

/-- Montgomery and Vaughan p.74 Theorem 2 display 1.6, for any finite family. -/
theorem hilbert_real {κ : Type*} [DecidableEq κ] (s : Finset κ) (α : κ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hs : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → δ ≤ |α r - α t|) (b : κ → ℂ) :
    ‖∑ r ∈ s, ∑ t ∈ s.erase r,
      b r * conj (b t) / ((α r - α t : ℝ) : ℂ)‖ ≤
      (Real.pi / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  have hsp : ∀ r t : s, r ≠ t → δ ≤ |α r - α t| := by
    intro r t hne
    exact hs r r.property t t.property (fun h => hne (Subtype.ext h))
  have hh := hilbert_real_fintype (fun r : s => α r) hδ hsp (fun r : s => b r)
  have he (r : κ) : b r * conj (b r) / ((α r - α r : ℝ) : ℂ) = 0 := by simp
  have her (r : s) : (∑ t ∈ (univ : Finset s).erase r,
      b r * conj (b t) / ((α r - α t : ℝ) : ℂ)) =
        ∑ t : s, b r * conj (b t) / ((α r - α t : ℝ) : ℂ) :=
    Finset.sum_erase _ (by simp)
  simp_rw [her] at hh
  have hex (r : κ) : (∑ t ∈ s.erase r,
      b r * conj (b t) / ((α r - α t : ℝ) : ℂ)) =
        ∑ t ∈ s, b r * conj (b t) / ((α r - α t : ℝ) : ℂ) :=
    Finset.sum_erase s (he r)
  simp_rw [hex]
  simpa only [← Finset.sum_coe_sort s] using hh

open MeasureTheory

/-- Montgomery and Vaughan p.74 Corollary 2 display 1.8, in absolute error form. -/
theorem exponential_mean_square {κ : Type*} [DecidableEq κ] (s : Finset κ) (α : κ → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → δ ≤ |α r - α t|) (b : κ → ℂ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖∑ r ∈ s,
        b r * Complex.exp (((α r * t : ℝ) : ℂ) * I)‖ ^ 2) - T * ∑ r ∈ s, ‖b r‖ ^ 2| ≤
      (2 * Real.pi / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
  have hex (x : ℝ) : e (x / (2 * Real.pi)) = Complex.exp ((x : ℂ) * I) := by
    unfold e
    have hh : 2 * Real.pi * (x / (2 * Real.pi)) = x := by field_simp
    rw [hh, mul_comm]
  let E (x : ℝ) := e (x / (2 * Real.pi))
  let v (t : ℝ) (r : κ) := b r * E (α r * t)
  let F (t : ℝ) := ∑ r ∈ s, v t r
  let A (r u : κ) (t : ℝ) := b r * conj (b u) * E ((α r - α u) * t)
  let H (u : κ → ℂ) := ∑ r ∈ s, ∑ t ∈ s.erase r,
    u r * conj (u t) / ((α r - α t : ℝ) : ℂ)
  have henergy (t : ℝ) : ∑ r ∈ s, ‖v t r‖ ^ 2 = ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simp only [v, E, norm_mul, norm_e, mul_one]
  have hphase (t : ℝ) (r u : κ) : v t r * conj (v t u) = A r u t := by
    have hh : E (α r * t) * conj (E (α u * t)) = E ((α r - α u) * t) := by
      dsimp [E]
      rw [← e_neg, ← e_add]
      congr 1
      ring
    dsimp [v, A]
    rw [map_mul]
    calc
      _ = (b r * conj (b u)) * (E (α r * t) * conj (E (α u * t))) := by ring
      _ = _ := by rw [hh]
  have he (t : ℝ) : ((‖F t‖ ^ 2 : ℝ) : ℂ) = ∑ r ∈ s, ∑ u ∈ s, A r u t := by
    simpa only [dualSum, Int.cast_one, one_mul, ← sub_div, ← sub_mul, F, v, A, E] using
      normSq_dualSum s (fun r => α r * t / (2 * Real.pi)) b 1
  have hA (r u : κ) : IntervalIntegrable (A r u) volume 0 T := by
    have hc : Continuous (A r u) := by dsimp [A, E, e]; fun_prop
    exact hc.intervalIntegrable _ _
  have hdiag (r : κ) : (∫ t in (0 : ℝ)..T, A r r t) =
      (T : ℂ) * ((‖b r‖ ^ 2 : ℝ) : ℂ) := by
    simp [A, E, e_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.real_smul]
  have hne (r u : κ) (hr : r ∈ s) (hu : u ∈ s) (hru : r ≠ u) : α r - α u ≠ 0 := by
    have hh := hδ.trans_le (hs r hr u hu hru)
    intro hz
    simp [hz] at hh
  have hoff (r : κ) (hr : r ∈ s) (u : κ) (hu : u ∈ s.erase r) :
      (∫ t in (0 : ℝ)..T, A r u t) =
        -I * ((v T r * conj (v T u) - b r * conj (b u)) / ((α r - α u : ℝ) : ℂ)) := by
    have hd : ((α r - α u : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hne r u hr (mem_erase.mp hu).2 (mem_erase.mp hu).1.symm
    have harg (t : ℝ) : E ((α r - α u) * t) =
        Complex.exp ((((α r - α u : ℝ) : ℂ) * I) * t) := by
      dsimp [E]
      rw [hex]
      congr 1
      push_cast
      ring
    dsimp [A]
    rw [intervalIntegral.integral_const_mul]
    simp_rw [harg]
    rw [integral_exp_mul_complex (mul_ne_zero hd Complex.I_ne_zero), ← harg T, hphase]
    rw [div_mul_eq_div_div, Complex.div_I]
    dsimp [A]
    ring_nf
    simp
  have hi : ((∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2 : ℝ) : ℂ) =
      (T : ℂ) * ((∑ r ∈ s, ‖b r‖ ^ 2 : ℝ) : ℂ) - I * (H (v T) - H b) := by
    have hrow (r : κ) (hr : r ∈ s) :
        (∑ u ∈ s, ∫ t in (0 : ℝ)..T, A r u t) =
          (T : ℂ) * ((‖b r‖ ^ 2 : ℝ) : ℂ) +
            -I * ∑ u ∈ s.erase r,
              (v T r * conj (v T u) - b r * conj (b u)) / ((α r - α u : ℝ) : ℂ) := by
      rw [← sum_erase_add _ _ hr, hdiag, add_comm]
      congr 1
      rw [mul_sum]
      exact sum_congr rfl (fun u hu => hoff r hr u hu)
    calc
      _ = ∑ r ∈ s, ∑ u ∈ s, ∫ t in (0 : ℝ)..T, A r u t := by
        rw [← intervalIntegral.integral_ofReal]
        simp_rw [he]
        rw [intervalIntegral.integral_finsetSum (fun r _ => by
          have hc : Continuous (fun x : ℝ => ∑ u ∈ s, A r u x) := by
            dsimp [A, E, e]
            fun_prop
          exact hc.intervalIntegrable _ _)]
        exact sum_congr rfl (fun r _ => intervalIntegral.integral_finsetSum (fun u _ => hA r u))
      _ = _ := by
        have hHs : (∑ r ∈ s, ∑ u ∈ s.erase r,
            (v T r * conj (v T u) - b r * conj (b u)) / ((α r - α u : ℝ) : ℂ)) =
              H (v T) - H b := by simp only [H, sub_div, sum_sub_distrib]
        rw [sum_congr rfl hrow, sum_add_distrib, ← mul_sum, ← mul_sum,
          ← Complex.ofReal_sum, hHs]
        ring
  have herr : (((∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) - T * ∑ r ∈ s, ‖b r‖ ^ 2 : ℝ) : ℂ) =
      -I * (H (v T) - H b) := by
    push_cast at hi ⊢
    linear_combination hi
  have hv : ‖H (v T)‖ ≤ (Real.pi / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    simpa only [H, henergy] using hilbert_real s α hδ hs (v T)
  have hb : ‖H b‖ ≤ (Real.pi / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := hilbert_real s α hδ hs b
  have hfinal : |(∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) - T * ∑ r ∈ s, ‖b r‖ ^ 2| ≤
      (2 * Real.pi / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := by
    calc
      _ = ‖(((∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) - T * ∑ r ∈ s, ‖b r‖ ^ 2 : ℝ) : ℂ)‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖H (v T) - H b‖ := by rw [herr, norm_mul, norm_neg, Complex.norm_I, one_mul]
      _ ≤ ‖H (v T)‖ + ‖H b‖ := norm_sub_le _ _
      _ ≤ (Real.pi / δ) * (∑ r ∈ s, ‖b r‖ ^ 2) +
          (Real.pi / δ) * ∑ r ∈ s, ‖b r‖ ^ 2 := add_le_add hv hb
      _ = _ := by ring
  simpa only [F, v, E, hex] using hfinal

/-- Reciprocal length spacing for the logarithms of the positive integers up to N.
Auxiliary for Montgomery and Vaughan p.75 display 1.12. -/
theorem log_nat_spacing {N : ℕ} (_hN : 0 < N) :
    ∀ r ∈ Icc 1 N, ∀ u ∈ Icc 1 N, r ≠ u →
      (1 / (N : ℝ)) ≤ |Real.log r - Real.log u| := by
  have hordered (r u : ℕ) (hr : 1 ≤ r) (hu : u ≤ N) (hru : r < u) :
      (1 / (N : ℝ)) ≤ Real.log u - Real.log r := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
    have huN : (u : ℝ) ≤ N := by exact_mod_cast hu
    have hdiff : (1 : ℝ) ≤ (u : ℝ) - r := by
      have hh : (r : ℝ) + 1 ≤ u := by exact_mod_cast Nat.succ_le_of_lt hru
      linarith
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hu0 hr0)
    rw [Real.log_div hu0.ne' hr0.ne', inv_div] at hl
    calc
      _ ≤ 1 / (u : ℝ) := one_div_le_one_div_of_le hu0 huN
      _ ≤ ((u : ℝ) - r) / u := div_le_div_of_nonneg_right hdiff hu0.le
      _ = 1 - (r : ℝ) / u := by field_simp
      _ ≤ _ := hl
  intro r hr u hu hne
  rcases lt_or_gt_of_ne hne with hru | hur
  · have hl : Real.log r ≤ Real.log u :=
      Real.log_le_log (by exact_mod_cast (by have := (mem_Icc.mp hr).1; omega : 0 < r))
        (by exact_mod_cast hru.le)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hl)]
    exact hordered r u (mem_Icc.mp hr).1 (mem_Icc.mp hu).2 hru
  · have hl : Real.log u ≤ Real.log r :=
      Real.log_le_log (by exact_mod_cast (by have := (mem_Icc.mp hu).1; omega : 0 < u))
        (by exact_mod_cast hur.le)
    rw [abs_of_nonneg (sub_nonneg.mpr hl)]
    exact hordered u r (mem_Icc.mp hu).1 (mem_Icc.mp hr).2 hur

/-- Montgomery and Vaughan p.75 display 1.12, with an explicit uniform constant.
This gives the unweighted finite Dirichlet polynomial estimate. -/
theorem dirichlet_polynomial_mean_square (N : ℕ) (hN : 0 < N) (b : ℕ → ℂ) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖∑ n ∈ Icc 1 N,
        b n * Complex.exp (-((Real.log n * t : ℝ) : ℂ) * I)‖ ^ 2) -
      T * ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2| ≤
      (2 * Real.pi * N) * ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2 := by
  have hs : ∀ r ∈ Icc 1 N, ∀ u ∈ Icc 1 N, r ≠ u →
      1 / (N : ℝ) ≤ |(-Real.log r) - (-Real.log u)| := by
    intro r hr u hu hne
    simpa only [neg_sub_neg, abs_sub_comm] using log_nat_spacing hN r hr u hu hne
  have hh := exponential_mean_square (Icc 1 N) (fun n => -Real.log n)
    (by positivity : (0 : ℝ) < 1 / N) hs b T
  simpa only [neg_mul, Complex.ofReal_neg, div_eq_mul_inv, one_mul, inv_inv] using hh

end LeanLab.Linnik.HilbertCosecant
