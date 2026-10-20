module

public import LeanLab.PNTPort.DirichletZF.SiegelBounds
import Mathlib

/-!
# Estermann's lemma

Lab proof, unit U-5111. AI wrote this file. Known mathematics, no cited input, Davenport
chapter 21, Estermann's form of the key lemma behind Siegel's theorem.

`estermann`: there is an absolute `C > 0` such that for every `N ≥ 1`, real non-principal
`χ₁, χ₂` mod `N` with `χ₁χ₂ ≠ χ₀`, real `7/8 ≤ σ < 1` and every `K ≥ 1`,

  `Re F(σ) ≥ 1/4 - ‖λ‖ (2 - σ)^K / (1 - σ) - 4 C N³ (3/4)^K`,

`F = ζ L(χ₁) L(χ₂) L(χ₁χ₂)`, `λ = L(1, χ₁) L(1, χ₂) L(1, χ₁χ₂)`. The proof expands
`G = F - λ/(s - 1)` in its Taylor series at `2`, uses the signs of `Fq_taylor_nonneg` on the
first `K` terms and Cauchy's estimate on the rest.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter Topology Metric Nat
open scoped ComplexOrder

theorem estermann : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
    (χ₁ χ₂ : DirichletCharacter ℂ N), χ₁ ≠ 1 → χ₂ ≠ 1 → χ₁ * χ₂ ≠ 1 → χ₁ ^ 2 = 1 →
      χ₂ ^ 2 = 1 → ∀ σ : ℝ, 7 / 8 ≤ σ → σ < 1 → ∀ K : ℕ, 1 ≤ K →
        1 / 4 - ‖Pq χ₁ χ₂ 1‖ * (2 - σ) ^ K / (1 - σ) - 4 * (C * (N : ℝ) ^ 3) * (3 / 4) ^ K ≤
          (Fq χ₁ χ₂ σ).re := by
  obtain ⟨C, hC, hCb⟩ := norm_Gq_sphere_le
  refine ⟨C, hC, fun N _ χ₁ χ₂ h1 h2 h12 r1 r2 σ hσ hσ1 K hK1 ↦ ?_⟩
  set B := C * (N : ℝ) ^ 3 with hB
  have hB0 : 0 ≤ B := by positivity
  set lam := Pq χ₁ χ₂ 1 with hlam
  set x : ℝ := 2 - σ with hx
  have hx1 : 1 < x := by rw [hx]; linarith
  have hx98 : x ≤ 9 / 8 := by rw [hx]; linarith
  have hGd := Gq_differentiable h1 h2 h12
  have hT := Complex.hasSum_taylorSeries_of_entire hGd 2 (σ : ℂ)
  set g : ℕ → ℂ := fun n ↦ (n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n (Gq χ₁ χ₂) 2
    with hg
  -- the coefficients
  set b : ℕ → ℂ := fun n ↦ (n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (Fq χ₁ χ₂) 2) with hb
  have hbn : ∀ n, 0 ≤ b n := fun n ↦
    mul_nonneg (by
      have : (0 : ℂ) ≤ (n ! : ℂ) := by exact_mod_cast Nat.zero_le _
      exact inv_nonneg.mpr this) (Fq_taylor_nonneg r1 r2 n)
  have hgform : ∀ n, g n = (x : ℂ) ^ n * b n - lam * (x : ℂ) ^ n := by
    intro n
    simp only [hg, hb, smul_eq_mul]
    rw [iteratedDeriv_Gq_two h1 h2 h12 n]
    have hs : (σ : ℂ) - 2 = -(x : ℂ) := by rw [hx]; push_cast; ring
    rw [hs, neg_pow]
    have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    have h11 : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
    have hinv : (n ! : ℂ)⁻¹ * (n ! : ℂ) = 1 := inv_mul_cancel₀ hf
    linear_combination (-lam * (x : ℂ) ^ n) * h11 +
      (-lam * (x : ℂ) ^ n * ((-1) ^ n * (-1) ^ n)) * hinv
  -- tail estimate
  have hgn : ∀ n, ‖g n‖ ≤ B * (3 / 4) ^ n := by
    intro n
    have hc := norm_iteratedDeriv_Gq_le h1 h2 h12 (hCb N χ₁ χ₂ h1 h2 h12) n
    simp only [hg, smul_eq_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    have hs : ‖(σ : ℂ) - 2‖ = x := by
      rw [show (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_neg (by linarith), hx]; ring
    rw [hs]
    have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    calc (n ! : ℝ)⁻¹ * (x ^ n * ‖iteratedDeriv n (Gq χ₁ χ₂) 2‖)
        ≤ (n ! : ℝ)⁻¹ * (x ^ n * (n ! * B / (3 / 2) ^ n)) := by gcongr
      _ = B * (x * (2 / 3)) ^ n := by
          have h32 : ((3 : ℝ) / 2) ^ n * (2 / 3) ^ n = 1 := by rw [← mul_pow]; norm_num
          have h32' : ((3 : ℝ) / 2) ^ n ≠ 0 := by positivity
          rw [mul_pow]
          field_simp
          linear_combination (-B) * h32
      _ ≤ B * (3 / 4) ^ n := by
          gcongr
          linarith
  have hsum_norm : Summable fun n ↦ ‖g n‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hgn
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left B)
  have hsum : Summable g := hsum_norm.of_norm
  have hsplit := (hsum.sum_add_tsum_nat_add K).symm
  rw [hT.tsum_eq] at hsplit
  -- the tail
  have htail : ‖∑' n, g (n + K)‖ ≤ 4 * B * (3 / 4) ^ K := by
    have hs2 : Summable fun n ↦ ‖g (n + K)‖ := (summable_nat_add_iff K).mpr hsum_norm
    calc ‖∑' n, g (n + K)‖ ≤ ∑' n, ‖g (n + K)‖ := norm_tsum_le_tsum_norm hs2
      _ ≤ ∑' n, B * (3 / 4) ^ K * (3 / 4) ^ n := by
          refine hs2.tsum_le_tsum (fun n ↦ ?_) ?_
          · have := hgn (n + K); rw [pow_add] at this; linarith
          · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      _ = 4 * B * (3 / 4) ^ K := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  -- the head
  have hhead : ∑ n ∈ Finset.range K, g n =
      ∑ n ∈ Finset.range K, (x : ℂ) ^ n * b n - lam * ∑ n ∈ Finset.range K, (x : ℂ) ^ n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ hgform n
  have hgeom : ∑ n ∈ Finset.range K, (x : ℂ) ^ n = ((x : ℂ) ^ K - 1) / ((x : ℂ) - 1) :=
    geom_sum_eq (by exact_mod_cast hx1.ne') K
  have hF : Fq χ₁ χ₂ σ = Gq χ₁ χ₂ σ + lam / ((σ : ℂ) - 1) := by
    rw [Gq_eq χ₁ χ₂ (by intro h; have := congrArg Complex.re h; simp at this; linarith)]
    ring
  have hx1c : (x : ℂ) - 1 = -((σ : ℂ) - 1) := by rw [hx]; push_cast; ring
  have hσc : (σ : ℂ) - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hkey : Fq χ₁ χ₂ σ = ∑ n ∈ Finset.range K, (x : ℂ) ^ n * b n -
      lam * (x : ℂ) ^ K / (1 - σ) + ∑' n, g (n + K) := by
    rw [hF, hsplit, hhead, hgeom, hx1c]
    have h1σ : (1 : ℂ) - σ ≠ 0 := by
      intro h; apply hσc; linear_combination -h
    field_simp
    ring
  -- real parts
  have hpos : 0 < 1 - σ := by linarith
  have hb0 : 1 / 4 ≤ (b 0).re := by
    have h0 := hbn 0
    have hn := Fq_two_ge χ₁ χ₂
    simp only [hb, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul] at h0 ⊢
    have hre : (iteratedDeriv 0 (Fq χ₁ χ₂) 2).im = 0 := by
      have := (Complex.nonneg_iff.mp h0).2; simp at this ⊢; linarith
    rw [iteratedDeriv_zero] at hre ⊢
    have hzr : Fq χ₁ χ₂ 2 = ((Fq χ₁ χ₂ 2).re : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rw [hzr, Complex.norm_real, Real.norm_eq_abs] at hn
    have hre0 : 0 ≤ (Fq χ₁ χ₂ 2).re := by
      have := (Complex.nonneg_iff.mp h0).1; simpa using this
    rwa [abs_of_nonneg hre0] at hn
  have hheadre : 1 / 4 ≤ (∑ n ∈ Finset.range K, (x : ℂ) ^ n * b n).re := by
    have hK : 0 < K := hK1
    rw [Complex.re_sum]
    have hterm : ∀ n ∈ Finset.range K, 0 ≤ ((x : ℂ) ^ n * b n).re := by
      intro n _
      have : (0 : ℂ) ≤ (x : ℂ) ^ n * b n :=
        mul_nonneg (pow_nonneg (by exact_mod_cast (by linarith : (0 : ℝ) ≤ x)) n) (hbn n)
      exact (Complex.nonneg_iff.mp this).1
    have h0 : 0 ∈ Finset.range K := Finset.mem_range.mpr hK
    calc 1 / 4 ≤ ((x : ℂ) ^ 0 * b 0).re := by simpa using hb0
      _ ≤ _ := Finset.single_le_sum hterm h0
  have hmid : -(‖lam‖ * x ^ K / (1 - σ)) ≤ (-(lam * (x : ℂ) ^ K / (1 - σ))).re := by
    have := Complex.re_le_norm (lam * (x : ℂ) ^ K / (1 - σ))
    have hn : ‖lam * (x : ℂ) ^ K / (1 - σ)‖ = ‖lam‖ * x ^ K / (1 - σ) := by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < x)]
      rw [show ((1 : ℂ) - σ) = ((1 - σ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hpos]
    rw [neg_re]; linarith
  have htailre : -(4 * B * (3 / 4) ^ K) ≤ (∑' n, g (n + K)).re := by
    have := (abs_le.mp ((Complex.abs_re_le_norm (∑' n, g (n + K))).trans htail)).1
    linarith
  rw [neg_re] at hmid
  rw [hkey, add_re, sub_re]
  linarith

end LeanLab.PNTPort.DirichletZF

