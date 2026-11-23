module

public import Mathlib
public import LeanLab.Routes.Decomp1551c

/-!
Unit U-1551, track T1, DECOMPOSE, run 20261026T1219Z-15327, 2026-10-26. PALOMAR line I5171.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Decomposition of the input `SmoothT2.HadamardK gZ` of
`LeanLab.Routes.U1508.goldbach_445_hsw_gZ` under RH:
`Σ_{j ∈ s} 4/(4 + (γ_i - γ_j)²) ≤ log |γ_i|` for every finite set `s` of zeros.

The textbook route, Davenport, Multiplicative Number Theory, chapter 12, equations (17) and (18):
the Hadamard product of `ξ(s) = s(s-1)/2 · π^{-s/2} Γ(s/2) ζ(s)` gives
`Re ζ'/ζ(s) = -Re 1/(s-1) + (1/2) log π - (1/2) Re ψ(s/2 + 1) + Σ_ρ Re 1/(s - ρ)`, with
multiplicity and absolutely convergent, LEAF `hadamard_re_sum_of` from the LEAVES `xi_growth`,
`xi_zero_iff`, `logDeriv_xi` and the cited Hadamard theorem `hadamard_logDeriv_order_one`;
`ξ(1-s) = ξ(s)` is PROVED here as `xi_one_sub`.
At `s = 5/2 + iγ` and under RH, `Re 1/(s - ρ_j) = 2/(4 + (γ - γ_j)²)`, the terms are positive,
so any finite partial sum of the kernel is at most twice the full sum. Then
`|ζ'/ζ(5/2 + it)| ≤ 3/10`, LEAF `logDeriv_bound_5half`, true value `0.28874` at `t = 0`;
`Re ψ(9/4 + iu) ≤ log|9/4 + iu| + 1/10`, LEAF `digamma_re_le`; and the real inequality LEAF
`final_numeric` for `|γ| ≥ 14`, which comes from `Ordinates14` under RH, the assembly
`Decomp1551c.ordinates14_gZ_of_RH`.

A float check: at `s = 5/2 + 20i` the identity of `hadamard_re_sum_of` reads `0.617322` against
`0.617312` from the first 150 zeros with an integral tail.

ASSEMBLY `hadamardK_gZ_of_RH`, CONDITIONAL ON the leaves here and in `Decomp1551c`.
-/

@[expose] public section

namespace LeanLab.Routes.Decomp1551b

open Complex Filter Topology
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx re_half_of_RH)
open LeanLab.ChirreHagen2025.SmoothKernel (K)

local notation "ζ" => riemannZeta

/-- Riemann's `ξ(s) = s(s-1)/2 · Λ(s)`, written with Mathlib's entire `completedRiemannZeta₀`:
`s(s-1)Λ(s) = s(s-1)Λ₀(s) + 1`, so `ξ(s) = (s(s-1)Λ₀(s) + 1)/2`. -/
noncomputable def xi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- `ξ(1-s) = ξ(s)`, from Mathlib's `completedRiemannZeta₀_one_sub`. Proved. -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Davenport chapter 12 page 80 evaluates xi at 1 and then at 0.
Both values are one half. AI wrote the Lean code. Goldbach is open. -/
theorem xi_at_zero_and_one : xi 0 = 1 / 2 ∧ xi 1 = 1 / 2 := by
  constructor <;> norm_num [xi]

/-
Independent lab growth estimates for the existing Davenport chapter 12 page 80 leaf.
Gamma recurrence is DLMF equation 5.5.1.
The fixed strip bound and Euler Maclaurin remainder are already proved in PNTPort.
These coarse bounds suffice for the exact sealed order one upper bound.
AI wrote this Lean code. Goldbach is open.
-/
private lemma norm_cpow_nat_neg (n : ℕ) (s : ℂ) (hn : 0 < n) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  simp

private lemma zeta_sum_le (N : ℕ) (s : ℂ) (hσ : 0 ≤ s.re) :
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ ≤ (N : ℝ) + 1 := by
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ n ∈ Finset.range (N + 1), ‖1 / (n : ℂ) ^ s‖ ≤ 1 := by
    intro n _
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, Nat.cast_zero, norm_div, norm_one]
      by_cases hs : s = 0
      · simp [hs]
      · rw [Complex.zero_cpow hs]
        simp
    · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos h]
      simpa [one_div] using
        inv_le_one_of_one_le₀ (Real.one_le_rpow (x := (n : ℝ)) (by exact_mod_cast h) hσ)
  calc ∑ n ∈ Finset.range (N + 1), ‖1 / (n : ℂ) ^ s‖ ≤ ∑ n ∈ Finset.range (N + 1), (1 : ℝ) :=
        Finset.sum_le_sum h1
    _ = (N : ℝ) + 1 := by simp

/-- `‖ζ(σ + it)‖ ≤ 5 |t|` for `σ ≥ 1/2` and `|t| > 3`, from the Euler–Maclaurin
decomposition `riemannZeta0`. -/
private lemma zeta_bound_im (σ t : ℝ) (hσ : 1 / 2 ≤ σ) (ht : 3 < |t|) :
    ‖ζ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 5 * |t| := by
  have hσpos : 0 < σ := by linarith
  set N : ℕ := ⌊|t|⌋₊ with hN
  have hN1 : 1 ≤ N := by
    rw [hN]; exact Nat.le_floor (by push_cast; linarith)
  have hNle : (N : ℝ) ≤ |t| := by rw [hN]; exact Nat.floor_le (abs_nonneg t)
  have htne : t ≠ 0 := by
    intro h; rw [h] at ht; simp only [abs_zero] at ht; linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  have hsim : s.im = t := by simp [hsdef]
  have hsre : s.re = σ := by simp [hsdef]
  have him1 : (1 - s).im = -t := by simp [hsim]
  have hne1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    rw [hsim] at him
    simp at him
    exact htne him
  have hre : 0 < s.re := by rw [hsre]; exact hσpos
  rw [← Zeta0EqZeta (N := N) (by omega) hre hne1, riemannZeta0]
  have hI : ‖∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤ (N : ℝ) ^ (-σ) / σ :=
    ZetaBnd_aux1b N hN1 (σ := σ) (t := t) hσpos
  have hsum : ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ ≤ (N : ℝ) + 1 :=
    zeta_sum_le N s (by rw [hsre]; linarith)
  have hnum2 : ‖(N : ℂ) ^ (1 - s)‖ = (N : ℝ) ^ (1 - σ) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp [hsre]
  have hden2 : |t| ≤ ‖1 - s‖ := by
    have h := Complex.abs_im_le_norm (1 - s)
    rw [him1, abs_neg] at h
    exact h
  have hNpos : (0 : ℝ) < ‖1 - s‖ := by
    rw [norm_pos_iff]
    intro h
    have him := congrArg Complex.im h
    rw [him1] at him
    simp at him
    exact htne him
  have hterm2 : ‖(-(N : ℂ) ^ (1 - s)) / (1 - s)‖ ≤ 1 := by
    rw [norm_div, norm_neg, hnum2, div_le_one hNpos]
    have h1 : (N : ℝ) ^ (1 - σ) ≤ (N : ℝ) ^ ((1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
    have h2a : (N : ℝ) ^ ((1 / 2 : ℝ)) ≤ |t| ^ ((1 / 2 : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hNle (by norm_num)
    have h2b : |t| ^ ((1 / 2 : ℝ)) ≤ |t| := by
      simpa using Real.rpow_le_rpow_of_exponent_le (x := |t|) (by linarith)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
    linarith
  have hterm3 : ‖(-(N : ℂ) ^ (-s)) / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_neg, norm_cpow_nat_neg N s (by omega), hsre]
    rw [show ‖(2 : ℂ)‖ = 2 from by norm_num, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
    calc (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
      _ = 1 := Real.rpow_zero _
  have hterm4 : ‖s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ 1 + 2 * |t| := by
    rw [norm_mul]
    have h1 : ‖s‖ ≤ σ + |t| := by
      calc ‖s‖ = ‖(σ : ℂ) + (t : ℂ) * I‖ := by rw [hsdef]
        _ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = σ + |t| := by simp [abs_of_pos hσpos]
    have h2 : (N : ℝ) ^ (-σ) ≤ 1 := by
      calc (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
        _ = 1 := Real.rpow_zero _
    have h4 : ‖s‖ * ((N : ℝ) ^ (-σ) / σ) ≤ (σ + |t|) * (1 / σ) := by
      exact mul_le_mul h1 ((div_le_div_iff_of_pos_right hσpos).mpr h2) (by positivity)
        (by linarith [abs_nonneg t])
    have h5 : (σ + |t|) * (1 / σ) = 1 + |t| / σ := by field_simp
    have h6 : |t| / σ ≤ 2 * |t| := by
      rw [div_le_iff₀ hσpos]
      nlinarith [abs_nonneg t]
    calc ‖s‖ * ‖∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
        ≤ ‖s‖ * ((N : ℝ) ^ (-σ) / σ) := mul_le_mul_of_nonneg_left hI (norm_nonneg _)
      _ ≤ (σ + |t|) * (1 / σ) := h4
      _ = 1 + |t| / σ := h5
      _ ≤ 1 + 2 * |t| := by linarith
  have hsum4 : ‖(∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s)
      + ((-(N : ℂ) ^ (1 - s)) / (1 - s)) + ((-(N : ℂ) ^ (-s)) / 2)
      + (s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1))‖
      ≤ ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖
        + ‖(-(N : ℂ) ^ (1 - s)) / (1 - s)‖ + ‖(-(N : ℂ) ^ (-s)) / 2‖
        + ‖s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ :=
    norm_add₄_le
  have hfin : ((N : ℝ) + 1) + 1 + 1 / 2 + (1 + 2 * |t|) ≤ 5 * |t| := by
    nlinarith [hNle, abs_nonneg t, ht]
  have h1 : ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖
      + ‖(-(N : ℂ) ^ (1 - s)) / (1 - s)‖ + ‖(-(N : ℂ) ^ (-s)) / 2‖
      + ‖s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ ((N : ℝ) + 1) + 1 + 1 / 2 + (1 + 2 * |t|) := by linarith
  exact hsum4.trans (h1.trans hfin)

/-- `‖ζ(σ + it)‖ ≤ 6 (1 + |t|)` for `σ ≥ 2`, from the Euler–Maclaurin decomposition with
`N = 3`. -/
private lemma zeta_bound_re (σ t : ℝ) (hσ : 2 ≤ σ) :
    ‖ζ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 6 * (1 + |t|) := by
  have hσpos : 0 < σ := by linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  have hsim : s.im = t := by simp [hsdef]
  have hsre : s.re = σ := by simp [hsdef]
  have hne1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    simp at this
    linarith
  have hre : 0 < s.re := by rw [hsre]; exact hσpos
  rw [← Zeta0EqZeta (N := 3) (by norm_num) hre hne1, riemannZeta0]
  have hI : ‖∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤ (3 : ℝ) ^ (-σ) / σ :=
    ZetaBnd_aux1b 3 (by norm_num) (σ := σ) (t := t) hσpos
  have hsum : ‖∑ n ∈ Finset.range (3 + 1), 1 / (n : ℂ) ^ s‖ ≤ (3 : ℝ) + 1 :=
    zeta_sum_le 3 s (by rw [hsre]; linarith)
  have hnum2 : ‖((3 : ℝ) : ℂ) ^ (1 - s)‖ = (3 : ℝ) ^ (1 - σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simp [hsre]
  have hden2 : (1 : ℝ) ≤ ‖1 - s‖ := by
    have h := Complex.abs_re_le_norm (1 - s)
    rw [show (1 - s).re = 1 - σ by simp [hsre], abs_of_neg (by linarith)] at h
    linarith
  have hNpos : (0 : ℝ) < ‖1 - s‖ := by linarith
  have hterm2 : ‖(-((3 : ℝ) : ℂ) ^ (1 - s)) / (1 - s)‖ ≤ 1 / 3 := by
    rw [norm_div, norm_neg, hnum2, div_le_iff₀ hNpos]
    have h1 : (3 : ℝ) ^ (1 - σ) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h0 : (3 : ℝ) ^ (-1 : ℝ) = 1 / 3 := by
      rw [Real.rpow_neg_one]; norm_num
    rw [h0] at h1
    nlinarith [h1, hden2]
  have hterm3 : ‖(-((3 : ℝ) : ℂ) ^ (-s)) / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num),
      show (-s).re = -σ from by simp [hsre]]
    rw [show ‖(2 : ℂ)‖ = 2 from by norm_num, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
    calc (3 : ℝ) ^ (-σ) ≤ (3 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 := Real.rpow_zero _
  have hterm4 : ‖s * ∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ (1 + |t|) / 3 := by
    rw [norm_mul]
    have h1 : ‖s‖ ≤ σ + |t| := by
      calc ‖s‖ = ‖(σ : ℂ) + (t : ℂ) * I‖ := by rw [hsdef]
        _ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = σ + |t| := by simp [abs_of_pos hσpos]
    have h2 : (3 : ℝ) ^ (-σ) ≤ 1 / 3 := by
      calc (3 : ℝ) ^ (-σ) ≤ (3 : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 3 := by rw [Real.rpow_neg_one]; norm_num
    have h4 : ‖s‖ * ((3 : ℝ) ^ (-σ) / σ) ≤ (σ + |t|) * ((1 / 3) / σ) := by
      exact mul_le_mul h1 ((div_le_div_iff_of_pos_right hσpos).mpr h2) (by positivity)
        (by linarith [abs_nonneg t])
    have h5 : (σ + |t|) * ((1 / 3) / σ) = (1 + |t| / σ) / 3 := by field_simp
    have h6 : |t| / σ ≤ |t| := by
      rw [div_le_iff₀ hσpos]
      nlinarith [abs_nonneg t]
    calc ‖s‖ * ‖∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
        ≤ ‖s‖ * ((3 : ℝ) ^ (-σ) / σ) := mul_le_mul_of_nonneg_left hI (norm_nonneg _)
      _ ≤ (σ + |t|) * ((1 / 3) / σ) := h4
      _ = (1 + |t| / σ) / 3 := h5
      _ ≤ (1 + |t|) / 3 := by linarith
  have hsum4 : ‖(∑ n ∈ Finset.range (3 + 1), 1 / (n : ℂ) ^ s)
      + ((-((3 : ℝ) : ℂ) ^ (1 - s)) / (1 - s)) + ((-((3 : ℝ) : ℂ) ^ (-s)) / 2)
      + (s * ∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1))‖
      ≤ ‖∑ n ∈ Finset.range (3 + 1), 1 / (n : ℂ) ^ s‖
        + ‖(-((3 : ℝ) : ℂ) ^ (1 - s)) / (1 - s)‖ + ‖(-((3 : ℝ) : ℂ) ^ (-s)) / 2‖
        + ‖s * ∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ :=
    norm_add₄_le
  have h1 : ‖∑ n ∈ Finset.range (3 + 1), 1 / (n : ℂ) ^ s‖
      + ‖(-((3 : ℝ) : ℂ) ^ (1 - s)) / (1 - s)‖ + ‖(-((3 : ℝ) : ℂ) ^ (-s)) / 2‖
      + ‖s * ∫ x in Set.Ioi (3 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ ((3 : ℝ) + 1) + 1 / 3 + 1 / 2 + (1 + |t|) / 3 := by linarith
  have hfin : ((3 : ℝ) + 1) + 1 / 3 + 1 / 2 + (1 + |t|) / 3 ≤ 6 * (1 + |t|) := by
    nlinarith [abs_nonneg t]
  exact hsum4.trans (h1.trans hfin)

/-- `‖ζ s‖ ≤ 6 (1 + ‖s‖)` for `Re s ≥ 1/2` and `‖s‖ ≥ 4`. -/
private lemma zeta_bound (s : ℂ) (hre : 1 / 2 ≤ s.re) (hn : 4 ≤ ‖s‖) :
    ‖ζ s‖ ≤ 6 * (1 + ‖s‖) := by
  have hrw : ((s.re : ℂ) + (s.im : ℂ) * I) = s := Complex.re_add_im s
  have hsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rcases le_or_gt |s.im| 3 with ht | ht
  · have hσ2 : 2 ≤ s.re := by
      have h1 : (16 : ℝ) ≤ ‖s‖ ^ 2 := by nlinarith [norm_nonneg s]
      have h2 : s.im ^ 2 ≤ 9 := by nlinarith [abs_le.mp ht]
      have h3 : 0 < s.re := by linarith
      nlinarith
    have := zeta_bound_re s.re s.im hσ2
    rw [hrw] at this
    have h2 : 6 * (1 + |s.im|) ≤ 6 * (1 + ‖s‖) := by
      linarith [Complex.abs_im_le_norm s]
    linarith
  · have := zeta_bound_im s.re s.im hre ht
    rw [hrw] at this
    have h2 : 5 * |s.im| ≤ 6 * (1 + ‖s‖) := by linarith [Complex.abs_im_le_norm s]
    linarith

/-! ### Auxiliary numeric facts -/

private lemma one_le_log_add_two {x : ℝ} (hx : 2 ≤ x) : 1 ≤ Real.log (x + 2) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_three.le]

private lemma sqrt_two_pi_le : Real.sqrt (2 * Real.pi) ≤ 3 := by
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith [Real.pi_lt_four]

private lemma inv_le_four {x : ℝ} (hx : 1 / 4 ≤ x) : x⁻¹ ≤ 4 := by
  rw [← one_div, div_le_iff₀ (by linarith : (0:ℝ) < x)]
  linarith

private lemma twelve_sq_le_exp (x : ℝ) (hx : 2 ≤ x) :
    12 * (x + 2) ^ 2 ≤ Real.exp (100 * x * Real.log (x + 2)) := by
  have h1 : 12 * (x + 2) ^ 2 ≤ 48 * x ^ 2 := by nlinarith
  have h2 : 48 * x ^ 2 ≤ Real.exp (100 * x) := by
    have h := Real.pow_div_factorial_le_exp (100 * x) (by linarith) 3
    have hfac : (((3 : ℕ).factorial : ℝ)) = 6 := by norm_num
    rw [hfac] at h
    nlinarith [h, sq_nonneg x, hx]
  have h3 : Real.exp (100 * x) ≤ Real.exp (100 * x * Real.log (x + 2)) := by
    apply Real.exp_le_exp.mpr
    have hL := one_le_log_add_two hx
    nlinarith
  linarith

private lemma three_mul_pow_le_exp (x : ℝ) (hx : 2 ≤ x) (k : ℕ) (hk : (k : ℝ) ≤ x) :
    3 * (2 * x + 1) ^ (k + 2) ≤ Real.exp (100 * x * Real.log (x + 2)) := by
  have hL := one_le_log_add_two hx
  have hpos : 0 < 3 * (2 * x + 1) ^ (k + 2) := by positivity
  rw [← Real.log_le_iff_le_exp hpos]
  have hbase : 0 < 2 * x + 1 := by linarith
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  push_cast
  have hlog2 : Real.log (2 * x + 1) ≤ 2 * Real.log (x + 2) := by
    have h1 : 2 * x + 1 ≤ (x + 2) ^ 2 := by nlinarith
    have h2 := Real.log_le_log hbase h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    nlinarith [Real.exp_one_gt_two, Real.exp_pos 1,
      show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
  have hLnn : (0:ℝ) ≤ Real.log (x + 2) := by linarith
  have hstep1 : ((k : ℝ) + 2) * Real.log (2 * x + 1) ≤ (x + 3) * (2 * Real.log (x + 2)) := by
    apply mul_le_mul _ hlog2 (Real.log_nonneg (by linarith)) (by linarith)
    linarith
  nlinarith [hstep1, hlog3, hL, hx, hLnn]

/-! ### Growth of `Γ` -/

private lemma Gamma_shift (k : ℕ) (w : ℂ) (h : (k : ℝ) < w.re) :
    Gamma w = Gamma (w - k) * ∏ j ∈ Finset.range k, (w - 1 - (j : ℂ)) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    have hk : (k : ℝ) < w.re := by
      have h' : ((k : ℕ) : ℝ) + 1 < w.re := by
        have := h; push_cast at this; exact this
      linarith
    rw [ih w hk, Finset.prod_range_succ]
    have hne : w - (k : ℂ) - 1 ≠ 0 := by
      intro h0
      have hre0 : w.re = (k : ℝ) + 1 := by
        have h1 := congrArg Complex.re h0
        have h2 : w.re - (k : ℝ) - 1 = 0 := by simpa using h1
        linarith
      have h' : ((k : ℕ) : ℝ) + 1 < w.re := by have := h; push_cast at this; exact this
      linarith
    have hadd : Gamma (w - (k : ℂ)) = (w - (k : ℂ) - 1) * Gamma (w - (k : ℂ) - 1) := by
      have := Complex.Gamma_add_one (w - (k : ℂ) - 1) hne
      rwa [show w - (k : ℂ) - 1 + 1 = w - (k : ℂ) by ring] at this
    have hcast : w - (((k + 1 : ℕ)) : ℂ) = w - (k : ℂ) - 1 := by push_cast; ring
    rw [hadd, hcast]
    ring

private lemma fac_bound (w : ℂ) (m : ℕ) (hm : (m : ℝ) ≤ ‖w‖) :
    ‖w - 1 - (m : ℂ)‖ ≤ 2 * ‖w‖ + 1 := by
  have h2 : ‖-1 - (m : ℂ)‖ ≤ ‖(-1 : ℂ)‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
  have h3 : ‖(-1 : ℂ)‖ = 1 := by norm_num
  have h4 : ‖(m : ℂ)‖ = (m : ℝ) := by simp
  have h5 : ‖w - 1 - (m : ℂ)‖ ≤ ‖w‖ + ‖-1 - (m : ℂ)‖ := by
    have := norm_add_le w (-1 - (m : ℂ))
    rwa [show w + (-1 - (m : ℂ)) = w - 1 - (m : ℂ) by ring] at this
  rw [h3, h4] at h2
  linarith

private lemma prod_bound (w : ℂ) (m : ℕ) (hm : (m : ℝ) ≤ ‖w‖) :
    ‖∏ j ∈ Finset.range m, (w - 1 - (j : ℂ))‖ ≤ (2 * ‖w‖ + 1) ^ m := by
  rw [norm_prod]
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : (m : ℝ) ≤ ‖w‖ := by
      have : ((m : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
      linarith
    rw [Finset.prod_range_succ, pow_succ]
    exact mul_le_mul (ih hm') (fac_bound w m hm') (norm_nonneg _) (by positivity)

private lemma Gamma_bound_of_im (w : ℂ) (hre : 1 / 4 ≤ w.re) (hn : 2 ≤ ‖w‖) (him : 0 ≤ w.im) :
    ‖Gamma w‖ ≤ Real.exp (100 * ‖w‖ * Real.log (‖w‖ + 2)) := by
  have hx : (2:ℝ) ≤ ‖w‖ := hn
  rcases lt_or_ge w.re (1 / 2) with hlt | hge
  · have hwne : w ≠ 0 := by
      intro h; rw [h] at hre; simp at hre; linarith
    have hsplit : Gamma w = Gamma (w + 1) / w := by
      rw [Complex.Gamma_add_one w hwne]; field_simp
    have hPL := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL2 (s := w + 1)
      (by simp; linarith) (by simp; linarith)
    have him1 : (w + 1).im = w.im := by simp
    have hexp : Real.exp (-(Real.pi * (w + 1).im / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff, him1]
      nlinarith [Real.pi_pos]
    have h2 : ‖(w + 1) + 1‖ ≤ ‖w‖ + 2 := by
      calc ‖(w + 1) + 1‖ = ‖w + 2‖ := by ring_nf
        _ ≤ ‖w‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
        _ = ‖w‖ + 2 := by norm_num
    have hs : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have hnum : ‖Gamma (w + 1)‖ ≤ Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2 := by
      have hstep : Real.sqrt (2 * Real.pi) * ‖(w + 1) + 1‖ ^ 2 *
          Real.exp (-(Real.pi * (w + 1).im / 2)) ≤ Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2 * 1 := by
        apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
        apply mul_le_mul_of_nonneg_left _ hs
        exact pow_le_pow_left₀ (norm_nonneg _) h2 2
      calc ‖Gamma (w + 1)‖
          ≤ Real.sqrt (2 * Real.pi) * ‖(w + 1) + 1‖ ^ 2 *
              Real.exp (-(Real.pi * (w + 1).im / 2)) := hPL
        _ ≤ Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2 * 1 := hstep
        _ = Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2 := by ring
    have hinv : ‖w‖⁻¹ ≤ 4 := inv_le_four (le_trans hre (le_trans (le_abs_self _)
      (Complex.abs_re_le_norm w)))
    have hmain : ‖Gamma w‖ ≤ 12 * (‖w‖ + 2) ^ 2 := by
      rw [hsplit, norm_div, div_eq_mul_inv]
      have hstep : ‖Gamma (w + 1)‖ * ‖w‖⁻¹ ≤ (Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2) * 4 :=
        mul_le_mul hnum hinv (by positivity) (by positivity)
      have hstep2 : (Real.sqrt (2 * Real.pi) * (‖w‖ + 2) ^ 2) * 4 ≤ 12 * (‖w‖ + 2) ^ 2 := by
        nlinarith [sqrt_two_pi_le, sq_nonneg (‖w‖ + 2)]
      linarith
    have hfin : 12 * (‖w‖ + 2) ^ 2 ≤ Real.exp (100 * ‖w‖ * Real.log (‖w‖ + 2)) :=
      twelve_sq_le_exp ‖w‖ hx
    linarith
  · set k : ℕ := ⌊w.re - 1 / 2⌋₊ with hkdef
    have hk_le : (k : ℝ) ≤ w.re - 1 / 2 := by
      rw [hkdef]; exact Nat.floor_le (by linarith)
    have hk_lt : w.re - 1 / 2 < (k : ℝ) + 1 := by
      rw [hkdef]; exact Nat.lt_floor_add_one _
    have hkre : 1 / 2 ≤ (w - (k : ℂ)).re := by simp; linarith
    have hkre' : (w - (k : ℂ)).re ≤ 3 / 2 := by simp; linarith
    have hPL := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL2 (s := w - (k : ℂ))
      (by linarith) (by linarith)
    have himk : (w - (k : ℂ)).im = w.im := by simp
    have hkx : (k : ℝ) ≤ ‖w‖ := by
      have h1 : w.re ≤ ‖w‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm w)
      linarith
    have hs : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have hstep2 : ‖(w - (k : ℂ)) + 1‖ ≤ 2 * ‖w‖ + 1 := by
      have ha : ‖(w - (k : ℂ)) + 1‖ ≤ ‖w - (k : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      have hb : ‖w - (k : ℂ)‖ ≤ ‖w‖ + ‖(k : ℂ)‖ := norm_sub_le _ _
      have hc : ‖(k : ℂ)‖ = (k : ℝ) := by simp
      have hd : ‖(1 : ℂ)‖ = 1 := by norm_num
      rw [hc] at hb
      rw [hd] at ha
      linarith
    have hGk : ‖Gamma (w - (k : ℂ))‖ ≤ Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2 := by
      have hexp : Real.exp (-(Real.pi * (w - (k : ℂ)).im / 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff, himk]
        nlinarith [Real.pi_pos]
      have hstep : Real.sqrt (2 * Real.pi) * ‖(w - (k : ℂ)) + 1‖ ^ 2 *
          Real.exp (-(Real.pi * (w - (k : ℂ)).im / 2)) ≤
          Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2 * 1 := by
        apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
        apply mul_le_mul_of_nonneg_left _ hs
        exact pow_le_pow_left₀ (norm_nonneg _) hstep2 2
      calc ‖Gamma (w - (k : ℂ))‖
          ≤ Real.sqrt (2 * Real.pi) * ‖(w - (k : ℂ)) + 1‖ ^ 2 *
              Real.exp (-(Real.pi * (w - (k : ℂ)).im / 2)) := hPL
        _ ≤ Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2 * 1 := hstep
        _ = Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2 := by ring
    have hP : ‖∏ j ∈ Finset.range k, (w - 1 - (j : ℂ))‖ ≤ (2 * ‖w‖ + 1) ^ k :=
      prod_bound w k hkx
    have hshift := Gamma_shift k w (by linarith)
    have hfinal : ‖Gamma w‖ ≤ Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ (k + 2) := by
      rw [hshift, norm_mul]
      have hstep : ‖Gamma (w - (k : ℂ))‖ * ‖∏ j ∈ Finset.range k, (w - 1 - (j : ℂ))‖
          ≤ (Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2) * (2 * ‖w‖ + 1) ^ k :=
        mul_le_mul hGk hP (norm_nonneg _) (by positivity)
      calc ‖Gamma (w - (k : ℂ))‖ * ‖∏ j ∈ Finset.range k, (w - 1 - (j : ℂ))‖
          ≤ (Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ 2) * (2 * ‖w‖ + 1) ^ k := hstep
        _ = Real.sqrt (2 * Real.pi) * ((2 * ‖w‖ + 1) ^ 2 * (2 * ‖w‖ + 1) ^ k) := by ring
        _ = Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ (k + 2) := by
            rw [← pow_add]; ring_nf
    have h3 : Real.sqrt (2 * Real.pi) * (2 * ‖w‖ + 1) ^ (k + 2) ≤ 3 * (2 * ‖w‖ + 1) ^ (k + 2) := by
      have h0 : (0:ℝ) ≤ (2 * ‖w‖ + 1) ^ (k + 2) := by positivity
      nlinarith [sqrt_two_pi_le]
    exact hfinal.trans (h3.trans (three_mul_pow_le_exp ‖w‖ hx k hkx))

private lemma Gamma_growth (w : ℂ) (hre : 1 / 4 ≤ w.re) (hn : 2 ≤ ‖w‖) :
    ‖Gamma w‖ ≤ Real.exp (100 * ‖w‖ * Real.log (‖w‖ + 2)) := by
  rcases le_or_gt 0 w.im with him | him
  · exact Gamma_bound_of_im w hre hn him
  · have h1 : ‖Gamma ((starRingEnd ℂ) w)‖ ≤
        Real.exp (100 * ‖(starRingEnd ℂ) w‖ * Real.log (‖(starRingEnd ℂ) w‖ + 2)) :=
      Gamma_bound_of_im ((starRingEnd ℂ) w) (by simpa using hre) (by simpa using hn)
        (by simpa using him.le)
    rwa [Complex.Gamma_conj, Complex.norm_conj, Complex.norm_conj] at h1

/-! ### Bounds for `Λ₀` -/

private lemma norm_pi_cpow_le_one (s : ℂ) (hre : 0 ≤ s.re) :
    ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  rw [show (-s / 2).re = -s.re / 2 from by simp]
  calc (Real.pi : ℝ) ^ (-s.re / 2) ≤ Real.pi ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
          (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi) (by linarith)
    _ = 1 := Real.rpow_zero _

/-- `‖Λ₀ s‖` bound for `Re s ≥ 1/2` and `‖s‖ ≥ 4`. -/
private lemma completedZeta_bound_half (s : ℂ) (hre : 1 / 2 ≤ s.re) (hn : 4 ≤ ‖s‖) :
    ‖completedRiemannZeta₀ s‖ ≤ Real.exp (1000 * ‖s‖ * Real.log (‖s‖ + 2)) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hn; simp at hn; linarith
  have hx : (2:ℝ) ≤ ‖s‖ := by linarith
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hG : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hid : completedRiemannZeta₀ s
      = (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s + 1 / s + 1 / (1 - s) := by
    have h := riemannZeta_eq_completedRiemannZeta₀ hs0
    rw [eq_div_iff (mul_ne_zero hpi hG)] at h
    linear_combination -h
  -- bounds for the three pieces
  have hpi1 := norm_pi_cpow_le_one s (by linarith)
  have hGn : ‖s / 2‖ = ‖s‖ / 2 := by
    rw [Complex.norm_div]; norm_num
  have hGbd : ‖Gamma (s / 2)‖ ≤ Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) := by
    have h1 : (1 / 4 : ℝ) ≤ (s / 2).re := by simp; linarith
    have h2 : (2 : ℝ) ≤ ‖s / 2‖ := by rw [hGn]; linarith
    have h3 := Gamma_growth (s / 2) h1 h2
    rwa [hGn] at h3
  have hzbd := zeta_bound s hre hn
  have hsix : 6 * (1 + ‖s‖) ≤ Real.exp (100 * ‖s‖) := by
    have h := Real.pow_div_factorial_le_exp (100 * ‖s‖) (by positivity) 2
    have hfac : (((2 : ℕ).factorial : ℝ)) = 2 := by norm_num
    rw [hfac] at h
    have hx0 : (0:ℝ) ≤ ‖s‖ := norm_nonneg _
    nlinarith [h, hx0]
  have hinv1 : ‖(1:ℂ) / s‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]
    linarith
  have hden : (1:ℝ) ≤ ‖1 - s‖ := by
    rcases le_or_gt 2 s.re with h2 | h2
    · have h := Complex.abs_re_le_norm (1 - s)
      rw [show (1 - s).re = 1 - s.re by simp, abs_of_neg (by linarith)] at h
      linarith
    · have h := Complex.abs_im_le_norm (1 - s)
      rw [show (1 - s).im = -s.im by simp, abs_neg] at h
      have hsq : s.re ^ 2 + s.im ^ 2 = ‖s‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have hsq' : (12:ℝ) ≤ s.im ^ 2 := by nlinarith
      have : (3:ℝ) ≤ |s.im| := by nlinarith [abs_nonneg s.im, sq_abs s.im]
      linarith
  have hinv2 : ‖(1:ℂ) / (1 - s)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]
    exact hden
  -- assemble
  have hbd : ‖completedRiemannZeta₀ s‖ ≤
      Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) * Real.exp (100 * ‖s‖) + 2 := by
    rw [hid]
    have h1 : ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s + 1 / s + 1 / (1 - s)‖
        ≤ ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s‖ + ‖1 / s‖ + ‖1 / (1 - s)‖ := by
      have h2 : ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s + 1 / s + 1 / (1 - s)‖
          ≤ ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s + 1 / s‖ + ‖1 / (1 - s)‖ :=
        norm_add_le _ _
      have h3 : ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s + 1 / s‖
          ≤ ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s‖ + ‖1 / s‖ := norm_add_le _ _
      linarith
    have h1' : ‖1 / s‖ ≤ 1 := by simpa [one_div] using hinv1
    have h1'' : ‖1 / (1 - s)‖ ≤ 1 := by simpa [one_div] using hinv2
    have h4 : ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) * ζ s‖
        ≤ Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) * Real.exp (100 * ‖s‖) := by
      rw [norm_mul, norm_mul]
      have hA : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Gamma (s / 2)‖
          ≤ 1 * Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) :=
        mul_le_mul hpi1 hGbd (norm_nonneg _) (by norm_num)
      have hz2 : ‖ζ s‖ ≤ Real.exp (100 * ‖s‖) := le_trans hzbd hsix
      have h5 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Gamma (s / 2)‖ * ‖ζ s‖
          ≤ 1 * Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) * Real.exp (100 * ‖s‖) :=
        mul_le_mul hA hz2 (norm_nonneg _) (by positivity)
      linarith
    linarith
  have hcomb : Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) * Real.exp (100 * ‖s‖)
      ≤ Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hL := one_le_log_add_two hx
    have hlog : Real.log (‖s‖ / 2 + 2) ≤ Real.log (‖s‖ + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hx0 : (0:ℝ) ≤ ‖s‖ := norm_nonneg _
    nlinarith [hL, hlog, hx0, mul_nonneg hx0 (by linarith : (0:ℝ) ≤ Real.log (‖s‖ + 2))]
  have htwo : (2:ℝ) ≤ Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := by
    have hL := one_le_log_add_two hx
    have hx0 : (0:ℝ) ≤ ‖s‖ := norm_nonneg _
    have h1 : 500 * ‖s‖ * Real.log (‖s‖ + 2) + 1 ≤
        Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) :=
      Real.add_one_le_exp (500 * ‖s‖ * Real.log (‖s‖ + 2))
    have h2 : (1:ℝ) ≤ 500 * ‖s‖ * Real.log (‖s‖ + 2) := by nlinarith
    linarith
  calc ‖completedRiemannZeta₀ s‖
      ≤ Real.exp (100 * (‖s‖ / 2) * Real.log (‖s‖ / 2 + 2)) * Real.exp (100 * ‖s‖) + 2 := hbd
    _ ≤ Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) +
        Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := by linarith
    _ = 2 * Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := by ring
    _ ≤ Real.exp (1000 * ‖s‖ * Real.log (‖s‖ + 2)) := by
        have hL := one_le_log_add_two hx
        have hx0 : (0:ℝ) ≤ ‖s‖ := norm_nonneg _
        have h1 : Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) * Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2))
            = Real.exp (1000 * ‖s‖ * Real.log (‖s‖ + 2)) := by
          rw [← Real.exp_add]; ring_nf
        have h2 : (2:ℝ) ≤ Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := htwo
        have h0 : (0:ℝ) < Real.exp (500 * ‖s‖ * Real.log (‖s‖ + 2)) := Real.exp_pos _
        nlinarith [h1, h2, h0]

namespace Growth210
open Complex Real Set MeasureTheory
lemma zeta_regularized_bound (s : ℂ) (hs : 1/2 ≤ s.re) :
    ‖(s-1) * riemannZeta s‖ ≤ 4 * (‖s‖+1)^2 := by
  by_cases hs1 : s=1
  · subst s; simp
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hsre : 0 < s.re := by linarith
  let J : ℂ := ∫ x in Ioi (1:ℝ), (⌊x⌋+1/2-x) * (x:ℂ)^(-(s+1))
  have hj : ‖J‖ ≤ 2 := by
    have h := ZetaBnd_aux1b 1 (by norm_num) (σ := s.re) (t := s.im) hsre
    rw [Complex.re_add_im] at h
    norm_num only [Nat.cast_one, Real.one_rpow] at h
    have he : J = ∫ x in Ioi (1:ℝ), (⌊x⌋+1/2-x) / (x:ℂ)^(s+1) := by
      dsimp [J]
      congr 1
      funext x
      simp only [div_eq_mul_inv, Complex.cpow_neg]
    rw [he]
    apply h.trans
    apply (div_le_iff₀ hsre).2
    linarith
  have he : riemannZeta s = 1/2 + 1/(s-1) + s*J := by
    have h := Zeta0EqZeta (N := 1) (by norm_num) hsre hs1
    rw [riemannZeta0_apply] at h
    have hsum : (∑ n ∈ Finset.range (1+1), 1 / (n:ℂ)^s) = 1 := by
      norm_num [Finset.sum_range_succ, Complex.zero_cpow hs0]
    rw [hsum] at h
    simp only [Nat.cast_one, Complex.one_cpow] at h
    change 1 + (-1 / (1-s) + (-1)/2 + s*J) = riemannZeta s at h
    rw [← h]
    have hn : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    field_simp
    ring
  have hid : (s-1)*riemannZeta s = 1 + (s-1)/2 + s*(s-1)*J := by
    rw [he]
    field_simp [sub_ne_zero.mpr hs1]
    ring
  have hsm : ‖s-1‖ ≤ ‖s‖+1 := by simpa using norm_sub_le s 1
  rw [hid]
  calc ‖1 + (s-1)/2 + s*(s-1)*J‖ ≤ ‖(1:ℂ)‖ + ‖(s-1)/2‖ + ‖s*(s-1)*J‖ := norm_add₃_le
    _ ≤ 1 + (‖s‖+1)/2 + ‖s‖*(‖s‖+1)*2 := by
      simp only [norm_one, norm_div, norm_mul, Complex.norm_ofNat]
      gcongr
    _ ≤ 4*(‖s‖+1)^2 := by nlinarith [norm_nonneg s]
end Growth210
namespace Growth210
open Complex Real Set MeasureTheory
lemma norm_sub_one_le {z : ℂ} (hz : 1/2 ≤ z.re) : ‖z-1‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, one_re, sub_im, one_im,
    sub_zero]
  nlinarith

lemma gamma_power_bound (n : ℕ) (z : ℂ) (hz : 1/2 ≤ z.re) (hn : z.re ≤ n+3/2) :
    ‖Complex.Gamma z‖ ≤ (Real.Gamma (1/2)+Real.Gamma (3/2)) * (‖z‖+1)^n := by
  have hM : 0 ≤ Real.Gamma (1/2)+Real.Gamma (3/2) := by
    exact add_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le
      (Real.Gamma_pos_of_pos (by norm_num)).le
  induction n generalizing z with
  | zero => simpa using LeanLab.PNTPort.ZetaZeros.norm_Gamma_strip_le hz (by simpa using hn)
  | succ n ih =>
    by_cases hsmall : z.re ≤ 3/2
    · have hb := LeanLab.PNTPort.ZetaZeros.norm_Gamma_strip_le hz hsmall
      have hp : (1:ℝ) ≤ (‖z‖+1)^(n+1) := one_le_pow₀ (by linarith [norm_nonneg z])
      exact hb.trans (by nlinarith)
    · have hz1 : 1/2 ≤ (z-1).re := by simp; linarith
      have hnn : (z-1).re ≤ (n:ℝ)+3/2 := by
        simp only [sub_re, one_re]
        push_cast at hn
        linarith
      have hb := ih (z-1) hz1 hnn
      have hnorm := norm_sub_one_le hz
      have he : Complex.Gamma z = (z-1)*Complex.Gamma (z-1) := by
        convert Complex.Gamma_add_one (z-1) (by
          intro he
          have := congrArg Complex.re he
          simp at this
          linarith) using 1 <;> ring
      rw [he, norm_mul]
      calc ‖z-1‖ * ‖Complex.Gamma (z-1)‖ ≤ (‖z‖+1) *
          ((Real.Gamma (1/2)+Real.Gamma (3/2)) * (‖z‖+1)^n) := by
            gcongr
            · linarith
            · exact hb.trans (by gcongr)
        _ = (Real.Gamma (1/2)+Real.Gamma (3/2)) * (‖z‖+1)^(n+1) := by ring

lemma gamma_exp_bound (z : ℂ) (hz : 1/2 ≤ z.re) :
    ‖Complex.Gamma z‖ ≤ (Real.Gamma (1/2)+Real.Gamma (3/2)) *
      Real.exp ((‖z‖+1) * Real.log (‖z‖+1)) := by
  have hz0 : 0 ≤ z.re := by linarith
  have hn : z.re ≤ (⌈z.re⌉₊:ℝ)+3/2 := by linarith [Nat.le_ceil z.re]
  have hb := gamma_power_bound ⌈z.re⌉₊ z hz hn
  have hc : (⌈z.re⌉₊:ℝ) ≤ ‖z‖+1 := by
    have hceil := Nat.ceil_lt_add_one hz0
    have := Complex.re_le_norm z
    linarith
  have hl : 0 ≤ Real.log (‖z‖+1) := Real.log_nonneg (by linarith [norm_nonneg z])
  apply hb.trans
  gcongr
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
  apply Real.exp_le_exp.mpr
  nlinarith
end Growth210
namespace Growth210
open Complex Real Set MeasureTheory
lemma xi_half_bound (s : ℂ) (hs : 1/2 ≤ s.re) :
    ‖xi s‖ ≤ 4 * (Real.Gamma (1/2)+Real.Gamma (3/2)) *
      Real.exp ((‖s‖+4)*Real.log (‖s‖+2)) := by
  let M : ℝ := Real.Gamma (1/2)+Real.Gamma (3/2)
  have hM : 1 ≤ M := by
    have h := LeanLab.PNTPort.ZetaZeros.norm_Gamma_strip_le (s := 1) (by norm_num) (by norm_num)
    simpa [M] using h
  have hr0 := norm_nonneg s
  have hlog : 0 ≤ Real.log (‖s‖+2) := Real.log_nonneg (by linarith)
  by_cases hs1 : s=1
  · subst s
    norm_num [xi]
    have hexp : 1 ≤ Real.exp (5*Real.log 3) := Real.one_le_exp_iff.mpr (by positivity)
    change 1 ≤ Real.Gamma (1/2)+Real.Gamma (3/2) at hM
    nlinarith
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hG : Gamma (s/2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hpi : (Real.pi:ℂ)^(-s/2) ≠ 0 :=
    (Complex.cpow_ne_zero_iff).mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have he : xi s = ((s-1)*riemannZeta s) * (Real.pi:ℂ)^(-s/2) * Gamma (s/2+1) := by
    rw [Gamma_add_one (s/2) (div_ne_zero hs0 (by norm_num)), riemannZeta_eq_completedRiemannZeta₀ hs0]
    unfold xi
    have hn : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    field_simp
    ring
  have hp : ‖(Real.pi:ℂ)^(-s/2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · linarith [Real.pi_gt_three]
    · simp; linarith
  have hnorm : ‖s/2+1‖+1 ≤ ‖s‖+2 := by
    have h := norm_add_le (s/2) (1:ℂ)
    norm_num only [norm_div, Complex.norm_ofNat, norm_one] at h
    linarith
  have hGexp := gamma_exp_bound (s/2+1) (by simp; linarith)
  have hlogw : 0 ≤ Real.log (‖s/2+1‖+1) := Real.log_nonneg (by linarith [norm_nonneg (s/2+1)])
  have hGe : ‖Gamma (s/2+1)‖ ≤ M * Real.exp ((‖s‖+2)*Real.log (‖s‖+2)) := by
    apply hGexp.trans
    change M * _ ≤ M * _
    gcongr
  have hze := zeta_regularized_bound s hs
  have hpoly : (‖s‖+1)^2 ≤ Real.exp (2*Real.log (‖s‖+2)) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log (by positivity)]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  rw [he, norm_mul, norm_mul]
  calc ‖(s-1)*riemannZeta s‖ * ‖(Real.pi:ℂ)^(-s/2)‖ * ‖Gamma (s/2+1)‖ ≤
      (4*(‖s‖+1)^2) * 1 * (M*Real.exp ((‖s‖+2)*Real.log (‖s‖+2))) := by gcongr
    _ ≤ (4*Real.exp (2*Real.log (‖s‖+2))) * 1 *
      (M*Real.exp ((‖s‖+2)*Real.log (‖s‖+2))) := by gcongr
    _ = 4*M*Real.exp ((‖s‖+4)*Real.log (‖s‖+2)) := by
      rw [mul_one]
      rw [show (4*Real.exp (2*Real.log (‖s‖+2)))*(M*Real.exp ((‖s‖+2)*Real.log (‖s‖+2))) =
        4*M*(Real.exp (2*Real.log (‖s‖+2))*Real.exp ((‖s‖+2)*Real.log (‖s‖+2))) by ring,
        ← Real.exp_add]
      congr 2
      ring

lemma growth_radial_normalize (r : ℝ) (hr : 0 ≤ r) :
    (r+5)*Real.log (r+3) ≤ 12*r*Real.log (r+2)+20 := by
  have hl : 0 ≤ Real.log (r+2) := Real.log_nonneg (by linarith)
  by_cases h : r ≤ 1
  · have hlog : Real.log (r+3) ≤ 3 := by
      have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < r+3)
      linarith
    nlinarith
  · have hl2 : Real.log (r+3) ≤ 2*Real.log (r+2) := by
      calc Real.log (r+3) ≤ Real.log ((r+2)^2) :=
          Real.log_le_log (by linarith) (by nlinarith)
        _ = 2*Real.log (r+2) := by rw [Real.log_pow]; norm_num
    have hr1 : 1 ≤ r := by linarith
    have hlog0 : 0 ≤ Real.log (r+3) := Real.log_nonneg (by linarith)
    calc (r+5)*Real.log (r+3) ≤ (6*r)*(2*Real.log (r+2)) := by gcongr <;> linarith
      _ ≤ 12*r*Real.log (r+2)+20 := by nlinarith

end Growth210

/-- LEAF. Unit U-1551. Davenport chapter 12, page 80, first displays: `ξ` has order one,
`|ξ(s)| ≤ C exp(C |s| log(|s| + 2))` for all `s`, from Stirling for `Γ(s/2)` and
`ζ(s) ≪ |s|` on `Re s ≥ 1/2`, with `ξ(1-s) = ξ(s)` for the other half plane. -/
theorem xi_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖xi s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  let K : ℝ := 4*(Real.Gamma (1/2)+Real.Gamma (3/2))
  have hK : 0 ≤ K := by
    dsimp [K]
    have h := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<1/2)
    have h' := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<3/2)
    positivity
  let C := max 12 (K*Real.exp 20)
  have hC12 : 12 ≤ C := le_max_left _ _
  have hCK : K*Real.exp 20 ≤ C := le_max_right _ _
  refine ⟨C, by linarith, fun s => ?_⟩
  have hr := norm_nonneg s
  have hl : 0 ≤ Real.log (‖s‖+2) := Real.log_nonneg (by linarith)
  have hb : ‖xi s‖ ≤ K*Real.exp ((‖s‖+5)*Real.log (‖s‖+3)) := by
    by_cases hs : 1/2 ≤ s.re
    · apply (Growth210.xi_half_bound s hs).trans
      change K*_ ≤ K*_
      gcongr <;> linarith
    · have hs' : 1/2 ≤ (1-s).re := by simp; linarith
      have he : xi (1-s) = xi s := by
        unfold xi
        rw [completedRiemannZeta₀_one_sub]
        ring
      rw [← he]
      apply (Growth210.xi_half_bound (1-s) hs').trans
      change K*_ ≤ K*_
      have hn : ‖1-s‖ ≤ ‖s‖+1 := by simpa [add_comm] using norm_sub_le (1:ℂ) s
      have hlw : 0 ≤ Real.log (‖1-s‖+2) := Real.log_nonneg (by linarith [norm_nonneg (1-s)])
      apply mul_le_mul_of_nonneg_left _ hK
      apply Real.exp_le_exp.mpr
      exact mul_le_mul (by linarith) (Real.log_le_log (by positivity) (by linarith)) hlw (by positivity)
  calc ‖xi s‖ ≤ K*Real.exp ((‖s‖+5)*Real.log (‖s‖+3)) := hb
    _ ≤ K*Real.exp (12*‖s‖*Real.log (‖s‖+2)+20) := by
      gcongr
      exact Growth210.growth_radial_normalize ‖s‖ hr
    _ = (K*Real.exp 20)*Real.exp (12*‖s‖*Real.log (‖s‖+2)) := by rw [Real.exp_add]; ring
    _ ≤ C*Real.exp (C*‖s‖*Real.log (‖s‖+2)) := by gcongr

/-- LEAF. Unit U-1551. Davenport chapter 12, page 79: the zeros of `ξ` are exactly the zeros
of `ζ` in the critical strip, with the same multiplicity, since `s(s-1)/2 · π^{-s/2} Γ(s/2)`
is analytic and nonzero on `0 < Re s < 1`, and `ξ ≠ 0` off the strip. -/
theorem xi_zero_iff :
    (∀ ρ : ℂ, xi ρ = 0 ↔ (ζ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)) ∧
    (∀ ρ : ℂ, ζ ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      analyticOrderNatAt xi ρ = analyticOrderNatAt ζ ρ) := by
  have heq : ∀ z : ℂ, 0 < z.re → z ≠ 1 → xi z =
      (z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) / 2) * riemannZeta z := by
    intro z hz hz1
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1' : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    have hG : Gamma (z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    rw [riemannZeta_eq_completedRiemannZeta₀ hz0]
    unfold xi
    field_simp
    ring
  have hfac : ∀ z : ℂ, 0 < z.re → z ≠ 1 →
      z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) / 2 ≠ 0 := by
    intro z hz hz1
    apply div_ne_zero _ (by norm_num)
    apply mul_ne_zero _ (Gamma_ne_zero_of_re_pos (by simp; linarith))
    apply mul_ne_zero _ ((Complex.cpow_ne_zero_iff).mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))
    exact mul_ne_zero (by intro h; norm_num [h] at hz) (sub_ne_zero.mpr hz1)
  have hp : ∀ z : ℂ, 0 < z.re → z ≠ 1 → (xi z = 0 ↔ riemannZeta z = 0) := by
    intro z hz hz1
    rw [heq z hz hz1, mul_eq_zero, or_iff_right (hfac z hz hz1)]
  constructor
  · intro z
    constructor
    · intro hz
      have hz0 : z ≠ 0 := by intro h; subst z; norm_num [xi] at hz
      have hz1 : z ≠ 1 := by intro h; subst z; norm_num [xi] at hz
      have hre : 0 < z.re := by
        by_contra hn
        have hwr : 1 ≤ (1 - z).re := by simp; linarith
        have hw1 : 1 - z ≠ 1 := by intro h; apply hz0; linear_combination -h
        have hw0 := riemannZeta_ne_zero_of_one_le_re hwr
        have hsym : xi (1 - z) = xi z := by
          unfold xi
          rw [completedRiemannZeta₀_one_sub]
          ring
        exact hw0 ((hp (1 - z) (by linarith) hw1).mp (hsym.trans hz))
      have hzero := (hp z hre hz1).mp hz
      refine ⟨hzero, hre, ?_⟩
      by_contra hn
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hn) hzero
    · rintro ⟨hz, h0, h1⟩
      exact (hp z h0 (by intro h; norm_num [h] at h1)).mpr hz
  · intro z hz h0 h1
    let a : ℂ → ℂ := fun w => w * (w - 1) * (Real.pi : ℂ) ^ (-w / 2) * Gamma (w / 2) / 2
    have hza : z ≠ 1 := by intro h; norm_num [h] at h1
    have ha0 : a z ≠ 0 := hfac z h0 hza
    have ha : AnalyticAt ℂ a z := by
      apply DifferentiableOn.analyticAt _ ((isOpen_re_gt 0).mem_nhds h0)
      intro w hw
      change 0 < w.re at hw
      apply DifferentiableAt.differentiableWithinAt
      unfold a
      have hdG : DifferentiableAt ℂ (fun v : ℂ => Gamma (v / 2)) w :=
        (hasDerivAt_Gamma_of_re_pos (by simp; linarith)).differentiableAt.comp w (by fun_prop)
      have hdpi : DifferentiableAt ℂ (fun v : ℂ => (Real.pi : ℂ) ^ (-v / 2)) w :=
        (show DifferentiableAt ℂ (fun v : ℂ => -v / 2) w by fun_prop).const_cpow
          (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
      fun_prop
    have he : xi =ᶠ[𝓝 z] a * riemannZeta := by
      filter_upwards [(isOpen_re_gt 0).mem_nhds h0, isOpen_ne.mem_nhds hza] with w hw hw1
      exact heq w hw hw1
    have hζ : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hza
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr he, analyticOrderAt_mul ha hζ,
      analyticOrderAt_eq_zero.mpr (Or.inr ha0), zero_add]

/-- LEAF. Unit U-1551. Davenport chapter 12, logarithmic differentiation of
`ξ(s) = s(s-1)/2 · π^{-s/2} Γ(s/2) ζ(s)`: for `Re s > 1`,
`ξ'/ξ(s) = 1/s + 1/(s-1) - (1/2) log π + (1/2) ψ(s/2) + ζ'/ζ(s)`. -/
theorem logDeriv_xi (s : ℂ) (hs : 1 < s.re) :
    logDeriv xi s = 1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2
      + logDeriv ζ s := by
  have heq : ∀ z : ℂ, 1 < z.re → xi z =
      z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) * riemannZeta z * (2 : ℂ)⁻¹ := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1 : 1 - z ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
    have hG : Gamma (z / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hpi : (Real.pi : ℂ) ^ (-z / 2) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
    rw [riemannZeta_eq_completedRiemannZeta₀ hz0]
    unfold xi
    field_simp
    ring
  have heq' : xi =ᶠ[𝓝 s] (fun z =>
      z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) * riemannZeta z * (2 : ℂ)⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact heq z hz
  rw [(logDeriv_congr_nhds heq').self_of_nhds, logDeriv_mul_const _ _ (by norm_num)]
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s - 1 ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
  have hG : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hdG : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s := by
    apply DifferentiableAt.comp s ((hasDerivAt_Gamma_of_re_pos (by simp; linarith)).differentiableAt)
    fun_prop
  have hdpi : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    exact (show DifferentiableAt ℂ (fun z : ℂ => -z / 2) s by fun_prop).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [logDeriv_fun_mul s (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1) hpi) hG)
    (riemannZeta_ne_zero_of_one_lt_re hs) (by fun_prop) (differentiableAt_riemannZeta (by intro h; norm_num [h] at hs))]
  rw [logDeriv_fun_mul (f := fun z : ℂ => z * (z - 1) * (Real.pi : ℂ) ^ (-z / 2))
    (g := fun z : ℂ => Gamma (z / 2)) s (mul_ne_zero (mul_ne_zero hs0 hs1) hpi) hG
    ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hdpi) hdG]
  rw [logDeriv_fun_mul (f := fun z : ℂ => z * (z - 1))
    (g := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s (mul_ne_zero hs0 hs1) hpi (by fun_prop) hdpi]
  rw [logDeriv_fun_mul s hs0 hs1 (by fun_prop) (by fun_prop)]
  have hp : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
    rw [logDeriv_fun_comp (f := fun z : ℂ => (Real.pi : ℂ) ^ z)
      (g := fun z : ℂ => -z / 2) (by fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))) (by fun_prop)]
    simp only [Complex.logDeriv_const_cpow (ofReal_ne_zero.mpr Real.pi_ne_zero)]
    simp [← Complex.ofReal_log Real.pi_pos.le]
    ring
  have hgamma : logDeriv (fun z : ℂ => Gamma (z / 2)) s = digamma (s / 2) / 2 := by
    rw [logDeriv_fun_comp (f := Gamma) (g := fun z : ℂ => z / 2)
      (hasDerivAt_Gamma_of_re_pos (by simp; linarith)).differentiableAt (by fun_prop)]
    simp [← digamma_def, div_eq_mul_inv]
  rw [hp, hgamma]
  simp [logDeriv_apply]
  ring

namespace Hadamard210
open Complex Filter Topology

/-- Real part cancellation for a symmetric entire function.
CONDITIONAL ON the explicit canonical logarithmic derivative expansion.
This is the algebraic step in Davenport chapter 12 equations 17 and 18.
AI wrote the Lean code. Goldbach is open. -/
lemma real_sum_of_symmetric_hadamard (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (hreflect : ∀ z : ℂ, f (1-z) = f z)
    (hstrip : ∀ z : ℂ, f z = 0 → 0 < z.re ∧ z.re < 1)
    (hH : ∃ B : ℂ, ∀ s : ℂ, f s ≠ 0 →
      Summable (fun i : (Σ ρ : {ρ : ℂ // f ρ = 0}, Fin (analyticOrderNatAt f (ρ : ℂ))) =>
        1 / (s - (i.1 : ℂ)) + 1 / (i.1 : ℂ)) ∧
      logDeriv f s = B + ∑' i : (Σ ρ : {ρ : ℂ // f ρ = 0}, Fin (analyticOrderNatAt f (ρ : ℂ))),
        (1 / (s - (i.1 : ℂ)) + 1 / (i.1 : ℂ)))
    (s : ℂ) (hs : f s ≠ 0) :
    HasSum (fun i : (Σ ρ : {ρ : ℂ // f ρ = 0}, Fin (analyticOrderNatAt f (ρ : ℂ))) =>
      (1 / (s - (i.1 : ℂ))).re) (logDeriv f s).re := by
  classical
  let Z := Σ ρ : {ρ : ℂ // f ρ = 0}, Fin (analyticOrderNatAt f (ρ : ℂ))
  obtain ⟨B, hB⟩ := hH
  have hpair (w : ℂ) (hw : f w ≠ 0) :
      HasSum (fun i : Z => 1/(w-(i.1:ℂ))+1/(i.1:ℂ)) (logDeriv f w-B) := by
    convert (hB w hw).1.hasSum using 1
    rw [(hB w hw).2]
    ring
  have hB0 : logDeriv f 0 = B := by
    have h := (hB 0 h0).2
    simpa using h
  have h1 : f 1 ≠ 0 := by simpa only [sub_zero] using (hreflect 0).trans_ne h0
  have hld (w : ℂ) : logDeriv f (1-w) = -logDeriv f w := by
    have he : (fun z : ℂ => f (1-z)) = f := funext hreflect
    have hc := logDeriv_fun_comp (f := f) (g := fun z : ℂ => 1-z) (hf (1-w))
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1-z) w)
    rw [he] at hc
    have hd : deriv (fun z : ℂ => 1-z) w = -1 := by simp
    rw [hd] at hc
    linear_combination hc
  have hld1 : logDeriv f 1 = -B := by simpa [hB0] using hld 0
  have hp1 := Complex.hasSum_re (hpair 1 h1)
  simp only [Complex.add_re] at hp1
  have hnn0 (i : Z) : 0 ≤ (1/(i.1:ℂ)).re := by
    rw [one_div, Complex.inv_re]
    exact div_nonneg (hstrip i.1 i.1.2).1.le (Complex.normSq_nonneg _)
  have hnn1 (i : Z) : 0 ≤ (1/(1-(i.1:ℂ))).re := by
    rw [one_div, Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re, Complex.one_re]
    linarith [(hstrip i.1 i.1.2).2]
  have hb : Summable (fun i : Z => (1/(i.1:ℂ)).re) :=
    Summable.of_nonneg_of_le hnn0 (fun i => le_add_of_nonneg_left (hnn1 i)) hp1.summable
  have ha : Summable (fun i : Z => (1/(1-(i.1:ℂ))).re) :=
    Summable.of_nonneg_of_le hnn1 (fun i => le_add_of_nonneg_right (hnn0 i)) hp1.summable
  have hord (z : ℂ) : analyticOrderNatAt f (1-z) = analyticOrderNatAt f z := by
    have he : f ∘ (fun w : ℂ => 1-w) = f := funext hreflect
    have hg : AnalyticAt ℂ (fun w : ℂ => 1-w) z := by fun_prop
    have hg' : deriv (fun w : ℂ => 1-w) z ≠ 0 := by simp
    unfold analyticOrderNatAt
    rw [← analyticOrderAt_comp_of_deriv_ne_zero (f := f) hg hg', he]
  let er : {ρ : ℂ // f ρ = 0} ≃ {ρ : ℂ // f ρ = 0} := {
    toFun := fun ρ => ⟨1-(ρ:ℂ), by rw [hreflect]; exact ρ.2⟩
    invFun := fun ρ => ⟨1-(ρ:ℂ), by rw [hreflect]; exact ρ.2⟩
    left_inv := fun ρ => by apply Subtype.ext; simp
    right_inv := fun ρ => by apply Subtype.ext; simp }
  let e : Z ≃ Z := Equiv.sigmaCongr er (fun ρ => finCongr (hord ρ).symm)
  have he (i : Z) : ((e i).1:ℂ) = 1-(i.1:ℂ) := rfl
  have hab : (∑' i : Z, (1/(1-(i.1:ℂ))).re) = ∑' i : Z, (1/(i.1:ℂ)).re := by
    simpa only [he] using e.tsum_eq (fun i : Z => (1/(i.1:ℂ)).re)
  have hcancel : B.re + ∑' i : Z, (1/(i.1:ℂ)).re = 0 := by
    have h := hp1.tsum_eq
    rw [ha.tsum_add hb, hab, hld1] at h
    simp only [Complex.sub_re, Complex.neg_re] at h
    linarith
  have hps := Complex.hasSum_re (hpair s hs)
  have hsub := hps.sub hb.hasSum
  convert hsub using 1
  · funext i
    simp
  · simp only [Complex.sub_re]
    linarith
end Hadamard210
namespace Hadamard210
open Complex Filter Topology
/-- The symmetric zero free entire function exp of z minus one half squared has
nonconstant logarithmic derivative. The growth assumption cannot be discarded.
This is a lab obstruction, not a paper error. -/
lemma hadamard_requires_growth :
    let f : ℂ → ℂ := fun z => Complex.exp ((z-1/2)^2)
    Differentiable ℂ f ∧ (∀ z : ℂ, f (1-z) = f z) ∧
      (∀ z : ℂ, f z ≠ 0) ∧ ¬ ∃ B : ℂ, ∀ z : ℂ, logDeriv f z = B := by
  dsimp only
  refine ⟨by fun_prop, ?_, fun z => Complex.exp_ne_zero _, ?_⟩
  · intro z
    congr 1
    ring
  · have hd (z : ℂ) : logDeriv (fun w : ℂ => Complex.exp ((w-1/2)^2)) z = 2*(z-1/2) := by
      have h : HasDerivAt (fun w : ℂ => Complex.exp ((w-1/2)^2))
          (Complex.exp ((z-1/2)^2) * (2*(z-1/2))) z := by
        simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
          (((hasDerivAt_id z).sub_const (1/2)).pow 2).cexp
      rw [logDeriv_apply, h.deriv]
      exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
    rintro ⟨B,hB⟩
    have h0 := hB 0
    have h1 := hB 1
    rw [hd] at h0 h1
    have he : (2*(0-1/2):ℂ) = 2*(1-1/2) := h0.trans h1.symm
    norm_num at he
end Hadamard210

set_option maxHeartbeats 3200000
set_option maxRecDepth 2000

/-- LEAF. Unit U-1551. `|ζ'/ζ(5/2 + it)| ≤ Σ Λ(n) n^{-5/2} = -ζ'/ζ(5/2) = 0.28874 ≤ 3/10`,
from Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` and a finite sum with a tail
bound. -/
theorem logDeriv_bound_5half (t : ℝ) : ‖logDeriv ζ ((5 / 2 : ℂ) + t * I)‖ ≤ 3 / 10 := by
  -- Exact prime powers below 64, followed by a telescoped logarithmic tail.
  -- Rational logarithm bounds use twenty positive terms of the exponential series.
  let f : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n)
  have hf0 : ∀ n, 0 ≤ f n := by intro n; exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hprefix : ∑ n ∈ Finset.range 64, f n ≤ (288/1000 : ℝ) := by
    change ∑ n ∈ Finset.range 64, ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n) ≤ (288/1000 : ℝ)
    have l2 : Real.log 2 ≤ (6932/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (2 : ℝ) ≤ ∑ i ∈ Finset.range 20, (6932/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l3 : Real.log 3 ≤ (10987/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (3 : ℝ) ≤ ∑ i ∈ Finset.range 20, (10987/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l5 : Real.log 5 ≤ (16095/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (5 : ℝ) ≤ ∑ i ∈ Finset.range 20, (16095/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l7 : Real.log 7 ≤ (19460/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (7 : ℝ) ≤ ∑ i ∈ Finset.range 20, (19460/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l11 : Real.log 11 ≤ (23979/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (11 : ℝ) ≤ ∑ i ∈ Finset.range 20, (23979/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l13 : Real.log 13 ≤ (25650/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (13 : ℝ) ≤ ∑ i ∈ Finset.range 20, (25650/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l17 : Real.log 17 ≤ (28333/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (17 : ℝ) ≤ ∑ i ∈ Finset.range 20, (28333/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l19 : Real.log 19 ≤ (29445/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (19 : ℝ) ≤ ∑ i ∈ Finset.range 20, (29445/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l23 : Real.log 23 ≤ (31355/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (23 : ℝ) ≤ ∑ i ∈ Finset.range 20, (31355/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l29 : Real.log 29 ≤ (33673/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (29 : ℝ) ≤ ∑ i ∈ Finset.range 20, (33673/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l31 : Real.log 31 ≤ (34340/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (31 : ℝ) ≤ ∑ i ∈ Finset.range 20, (34340/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l37 : Real.log 37 ≤ (36110/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (37 : ℝ) ≤ ∑ i ∈ Finset.range 20, (36110/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l41 : Real.log 41 ≤ (37136/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (41 : ℝ) ≤ ∑ i ∈ Finset.range 20, (37136/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l43 : Real.log 43 ≤ (37613/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (43 : ℝ) ≤ ∑ i ∈ Finset.range 20, (37613/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l47 : Real.log 47 ≤ (38502/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (47 : ℝ) ≤ ∑ i ∈ Finset.range 20, (38502/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l53 : Real.log 53 ≤ (39703/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (53 : ℝ) ≤ ∑ i ∈ Finset.range 20, (39703/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l59 : Real.log 59 ≤ (40776/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (59 : ℝ) ≤ ∑ i ∈ Finset.range 20, (40776/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    have l61 : Real.log 61 ≤ (41109/10000 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (61 : ℝ) ≤ ∑ i ∈ Finset.range 20, (41109/10000 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    let b : ℕ → ℝ := fun n => ([(0/100000000 : ℝ),(0/100000000 : ℝ),(12254279/100000000 : ℝ),(7048371/100000000 : ℝ),(2166250/100000000 : ℝ),(2879249/100000000 : ℝ),(0/100000000 : ℝ),(1501089/100000000 : ℝ),(382947/100000000 : ℝ),(452140/100000000 : ℝ),(0/100000000 : ℝ),(597521/100000000 : ℝ),(0/100000000 : ℝ),(420955/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(67696/100000000 : ℝ),(237778/100000000 : ℝ),(0/100000000 : ℝ),(187128/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(123592/100000000 : ℝ),(0/100000000 : ℝ),(51504/100000000 : ℝ),(0/100000000 : ℝ),(29006/100000000 : ℝ),(0/100000000 : ℝ),(74352/100000000 : ℝ),(0/100000000 : ℝ),(64181/100000000 : ℝ),(11968/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(43364/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(34502/100000000 : ℝ),(0/100000000 : ℝ),(31022/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(25424/100000000 : ℝ),(0/100000000 : ℝ),(11579/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(19415/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ),(15251/100000000 : ℝ),(0/100000000 : ℝ),(14146/100000000 : ℝ),(0/100000000 : ℝ),(0/100000000 : ℝ)].getD n 0)
    have hb : ∀ n ∈ Finset.range 64, ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n) ≤ b n := by
      intro n hn
      have hn64 : n < 64 := Finset.mem_range.mp hn
      interval_cases n
      · norm_num [b, ArithmeticFunction.vonMangoldt_apply]
      · norm_num [b, ArithmeticFunction.vonMangoldt_apply]
      · have hv : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (14142/10000 : ℝ) ≤ Real.sqrt 2 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (17320/10000 : ℝ) ≤ Real.sqrt 3 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l3]
      · have hv : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (20000/10000 : ℝ) ≤ Real.sqrt 4 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 5 = Real.log 5 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (22360/10000 : ℝ) ≤ Real.sqrt 5 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l5]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 6 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 7 = Real.log 7 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (26457/10000 : ℝ) ≤ Real.sqrt 7 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l7]
      · have hv : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (28284/10000 : ℝ) ≤ Real.sqrt 8 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (30000/10000 : ℝ) ≤ Real.sqrt 9 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l3]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 10 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 11 = Real.log 11 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (33166/10000 : ℝ) ≤ Real.sqrt 11 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l11]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 12 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 13 = Real.log 13 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (36055/10000 : ℝ) ≤ Real.sqrt 13 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l13]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 14 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 15 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 16 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (40000/10000 : ℝ) ≤ Real.sqrt 16 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · have hv : ArithmeticFunction.vonMangoldt 17 = Real.log 17 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (41231/10000 : ℝ) ≤ Real.sqrt 17 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l17]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 18 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 19 = Real.log 19 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (43588/10000 : ℝ) ≤ Real.sqrt 19 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l19]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 20 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 21 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 22 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 23 = Real.log 23 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (47958/10000 : ℝ) ≤ Real.sqrt 23 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l23]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 24 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 25 = Real.log 5 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (50000/10000 : ℝ) ≤ Real.sqrt 25 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l5]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 26 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 27 = Real.log 3 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (51961/10000 : ℝ) ≤ Real.sqrt 27 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l3]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 28 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 29 = Real.log 29 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (53851/10000 : ℝ) ≤ Real.sqrt 29 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l29]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 30 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 31 = Real.log 31 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (55677/10000 : ℝ) ≤ Real.sqrt 31 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l31]
      · have hv : ArithmeticFunction.vonMangoldt 32 = Real.log 2 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (56568/10000 : ℝ) ≤ Real.sqrt 32 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l2]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 33 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 34 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 35 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 36 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 37 = Real.log 37 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (60827/10000 : ℝ) ≤ Real.sqrt 37 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l37]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 38 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 39 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 40 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 41 = Real.log 41 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (64031/10000 : ℝ) ≤ Real.sqrt 41 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l41]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 42 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 43 = Real.log 43 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (65574/10000 : ℝ) ≤ Real.sqrt 43 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l43]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 44 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 45 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 46 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 47 = Real.log 47 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (68556/10000 : ℝ) ≤ Real.sqrt 47 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l47]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 48 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 49 = Real.log 7 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (70000/10000 : ℝ) ≤ Real.sqrt 49 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l7]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 50 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 51 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 52 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 53 = Real.log 53 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (72801/10000 : ℝ) ≤ Real.sqrt 53 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l53]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 54 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 55 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 56 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 57 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 58 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 59 = Real.log 59 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (76811/10000 : ℝ) ≤ Real.sqrt 59 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l59]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 60 by decide +kernel)]
        norm_num [b]
      · have hv : ArithmeticFunction.vonMangoldt 61 = Real.log 61 := by
          rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (by decide +kernel)]
          norm_num
        have hs : (78102/10000 : ℝ) ≤ Real.sqrt 61 := by
          apply (Real.le_sqrt (by norm_num) (by norm_num)).2
          norm_num
        rw [hv]
        norm_num only [b, List.getD_cons_zero, List.getD_cons_succ, Nat.cast_ofNat]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [l61]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 62 by decide +kernel)]
        norm_num [b]
      · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right (show ¬IsPrimePow 63 by decide +kernel)]
        norm_num [b]
    calc _ ≤ ∑ n ∈ Finset.range 64, b n := Finset.sum_le_sum hb
         _ ≤ (288/1000 : ℝ) := by norm_num [b, Finset.sum_range_succ]
  have htail (n : ℕ) (hn : 64 ≤ n) : f n ≤ LeanLab.PNTPort.ExplicitPsi1.Trivial.fl n / 8 := by
    change ArithmeticFunction.vonMangoldt n / ((n : ℝ)^2 * Real.sqrt n) ≤ LeanLab.PNTPort.ExplicitPsi1.Trivial.fl n / 8
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hs : (8 : ℝ) ≤ Real.sqrt n := by
      apply (Real.le_sqrt (by norm_num) hn0.le).2
      norm_num; exact_mod_cast hn
    have hp : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    unfold LeanLab.PNTPort.ExplicitPsi1.Trivial.fl
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hn0) hp)).2
    have hv : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hh : Real.log n ≤ Real.log n * (Real.sqrt n / 8) := by nlinarith
    calc ArithmeticFunction.vonMangoldt n ≤ Real.log n := hv
         _ ≤ Real.log n * (Real.sqrt n / 8) := hh
         _ = Real.log n / (n : ℝ)^2 / 8 * ((n : ℝ)^2 * Real.sqrt n) := by field_simp
  have hgt : LeanLab.PNTPort.ExplicitPsi1.Trivial.gt 63 / 8 ≤ (11/1000 : ℝ) := by
    have hlog : Real.log 63 ≤ (21/5 : ℝ) := by
      apply (Real.log_le_iff_le_exp (by norm_num)).2
      calc (63 : ℝ) ≤ ∑ i ∈ Finset.range 20, (21/5 : ℝ)^i / (i.factorial : ℝ) := by norm_num [Finset.sum_range_succ, Nat.factorial]
           _ ≤ Real.exp _ := Real.sum_le_exp_of_nonneg (by norm_num) _
    unfold LeanLab.PNTPort.ExplicitPsi1.Trivial.gt
    norm_num
    linarith
  have haux (M : ℕ) (hM : 64 ≤ M) :
      ∑ n ∈ Finset.range M, f n ≤ ∑ n ∈ Finset.range 64, f n + LeanLab.PNTPort.ExplicitPsi1.Trivial.gt 63 / 8 - LeanLab.PNTPort.ExplicitPsi1.Trivial.gt ((M : ℝ) - 1) / 8 := by
    induction M, hM using Nat.le_induction with
    | base => norm_num
    | succ M hM ih =>
      rw [Finset.sum_range_succ]
      have hn : (4 : ℝ) ≤ M := by exact_mod_cast (by omega : 4 ≤ M)
      have htele := LeanLab.PNTPort.ExplicitPsi1.Trivial.tele_step hn
      have ht := htail M hM
      unfold LeanLab.PNTPort.ExplicitPsi1.Trivial.fl at ht
      rw [show ((M + 1 : ℕ) : ℝ) - 1 = M by push_cast; ring]
      linarith
  have hpartial (M : ℕ) : ∑ n ∈ Finset.range M, f n ≤ (3/10 : ℝ) := by
    by_cases hM : 64 ≤ M
    · have h1 := haux M hM
      have h2 : 0 ≤ LeanLab.PNTPort.ExplicitPsi1.Trivial.gt ((M : ℝ) - 1) := LeanLab.PNTPort.ExplicitPsi1.Trivial.gt_nonneg (by
        have hMr : (64 : ℝ) ≤ M := by exact_mod_cast hM
        linarith)
      linarith
    · have hsub := Finset.sum_le_sum_of_subset_of_nonneg (f := f)
        (Finset.range_subset_range.mpr (by omega : M ≤ 64)) (fun n _ _ => hf0 n)
      linarith
  have hsum : Summable f := summable_of_sum_range_le hf0 hpartial
  have hn (n : ℕ) : ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) n‖ = f n := by
    rw [LSeries.norm_term_eq]
    split_ifs with hz
    · subst n; simp [f]
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      norm_num
      change ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5/2 : ℝ) = f n
      rw [show (5/2 : ℝ) = 2 + 1/2 by norm_num, Real.rpow_add_of_nonneg (by positivity) (by norm_num) (by norm_num), Real.rpow_two, ← Real.sqrt_eq_rpow]
  have hsn : Summable (fun n => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) n‖) := hsum.congr (fun n => (hn n).symm)
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (5/2 : ℂ) + t * I) (by simp; norm_num)
  have he : logDeriv riemannZeta ((5/2 : ℂ) + t * I) = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) := by
    rw [hL, logDeriv_apply]; ring
  rw [he, norm_neg]
  calc _ ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((5/2 : ℂ) + t * I) n‖ := norm_tsum_le_tsum_norm hsn
       _ = ∑' n, f n := tsum_congr hn
       _ ≤ 3/10 := Real.tsum_le_of_sum_range_le hf0 hpartial

set_option maxHeartbeats 200000
set_option maxRecDepth 1000

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
Ported from https://github.com/anthropics/formal-math
Commit e1a4e6508154ea59f030480661590a9fe3018011
Source zeta23/Zeta23/GammaFacts/Series.lean
The full license is in the LICENSE file at the root of this repository.
Only the digamma series dependency closure is retained.
The namespace and imports are adapted to this lab.
AI wrote the integration code. Goldbach is open.
-/
namespace Digamma210
namespace DigammaSeries

open Complex Filter Topology

/-- Offset Weierstrass factor: `1 + wTerm n z = (1 + z/(n+1))·e^{−z/(n+1)}`. -/
noncomputable def wTerm (n : ℕ) (z : ℂ) : ℂ := (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) - 1

lemma one_add_wTerm (n : ℕ) (z : ℂ) :
    1 + wTerm n z = (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) := by
  unfold wTerm
  ring

lemma norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- The quadratic tail bound for the Weierstrass factor. -/
lemma norm_wTerm_le {z : ℂ} {n : ℕ} (h : ‖z‖ ≤ (n : ℝ) + 1) :
    ‖wTerm n z‖ ≤ 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by
  set w : ℂ := z / ((n : ℂ) + 1) with hwdef
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hwnorm : ‖w‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [hwdef, norm_div, norm_natCast_add_one]
  have hwn : ‖w‖ ≤ 1 := by
    rw [hwnorm, div_le_one hn1]
    exact h
  have hr : ‖Complex.exp (-w) - 1 + w‖ ≤ ‖w‖ ^ 2 := by
    have hx : ‖(-w : ℂ)‖ ≤ 1 := by rwa [norm_neg]
    have h2 := norm_exp_sub_one_sub_id_le hx
    rw [norm_neg] at h2
    calc ‖Complex.exp (-w) - 1 + w‖ = ‖Complex.exp (-w) - 1 - (-w)‖ := by ring_nf
      _ ≤ ‖w‖ ^ 2 := h2
  have hident : wTerm n z = (Complex.exp (-w) - 1 + w) - w ^ 2
      + w * (Complex.exp (-w) - 1 + w) := by
    unfold wTerm
    ring
  have hnw2 : ‖(w : ℂ) ^ 2‖ = ‖w‖ ^ 2 := norm_pow _ _
  calc ‖wTerm n z‖
      ≤ ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ + ‖w * (Complex.exp (-w) - 1 + w)‖ := by
        rw [hident]
        exact norm_add_le _ _
    _ ≤ (‖w‖ ^ 2 + ‖w‖ ^ 2) + ‖w‖ * ‖w‖ ^ 2 := by
        have h1 : ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
          calc ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖
              ≤ ‖Complex.exp (-w) - 1 + w‖ + ‖(w : ℂ) ^ 2‖ := norm_sub_le _ _
            _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
                rw [hnw2]
                exact add_le_add hr le_rfl

        have h2 : ‖w * (Complex.exp (-w) - 1 + w)‖ ≤ ‖w‖ * ‖w‖ ^ 2 := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)
        linarith
    _ ≤ 3 * ‖w‖ ^ 2 := by nlinarith [norm_nonneg w, hwn, sq_nonneg ‖w‖]
    _ = 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by rw [hwnorm]

lemma summable_wBound (R : ℝ) : Summable (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2) := by
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
      have := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at this
    have := (summable_nat_add_iff 1).mpr h2
    simpa [add_comm] using this
  have h3 : (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2)
      = fun n : ℕ => (3 * R ^ 2) * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
    funext n
    rw [div_pow]
    ring
  rw [h3]
  exact h1.mul_left _

lemma summable_norm_wTerm (z : ℂ) : Summable (fun n => ‖wTerm n z‖) := by
  refine (summable_wBound ‖z‖).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine norm_wTerm_le ?_
  calc ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by linarith

lemma multipliable_one_add_wTerm (z : ℂ) : Multipliable fun n => 1 + wTerm n z :=
  Complex.multipliable_one_add_of_summable ((summable_norm_wTerm z).of_norm)

/-! ### The finite identity and the Weierstrass product -/

lemma harmonic_cast_eq (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1) := by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_div]

/-- The finite identity: (GammaSeq z N)⁻¹ = z·e^{(H_N − log N)z}·∏_{n<N}(1 + wTerm n z). -/
lemma inv_gammaSeq_eq {z : ℂ} (_hz : z ∈ Complex.integerComplement) {N : ℕ} (hN : 1 ≤ N) :
    (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1))
            - Real.log N : ℝ) : ℂ) * z)
          * ∏ n ∈ Finset.range N, (1 + wTerm n z) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the product of the Weierstrass factors
  have hprod : ∏ n ∈ Finset.range N, (1 + wTerm n z)
      = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
          * Complex.exp (-(∑ m ∈ Finset.range N, z / ((m : ℂ) + 1))) := by
    calc ∏ n ∈ Finset.range N, (1 + wTerm n z)
        = ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
            * Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_congr rfl fun n _ => one_add_wTerm n z
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * ∏ n ∈ Finset.range N, Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_mul_distrib
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * Complex.exp (∑ n ∈ Finset.range N, -(z / ((n : ℂ) + 1))) := by
          rw [Complex.exp_sum]
      _ = _ := by rw [← Finset.sum_neg_distrib]
  -- numeric ingredients
  have hfact_ne : ((N.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hNz : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcpow : (N : ℂ) ^ z = Complex.exp (((Real.log N : ℝ) : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero hNz]
    congr 2
    rw [show ((N : ℂ)) = (((N : ℝ) : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log hNR.le).symm
  have hdenom : ∏ j ∈ Finset.range (N + 1), (z + (j : ℂ))
      = z * ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) := by
    rw [Finset.prod_range_succ']
    rw [Nat.cast_zero, add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun n _ => ?_
    push_cast
    ring
  have hfactprod : ((N.factorial : ℕ) : ℂ) = ∏ n ∈ Finset.range N, ((n : ℂ) + 1) := by
    rw [show N.factorial = ∏ n ∈ Finset.range N, (n + 1) from
      (Finset.prod_range_add_one_eq_factorial N).symm]
    push_cast
    rfl
  have hfrac : ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
      = (∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1))) / ((N.factorial : ℕ) : ℂ) := by
    have h1 : ∀ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
        = (z + ((n : ℂ) + 1)) / ((n : ℂ) + 1) := by
      intro n _
      have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp
      ring
    rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib, hfactprod]
  have hsumcast : (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    push_cast
    rfl
  have hzsum : ∑ m ∈ Finset.range N, z / ((m : ℂ) + 1)
      = z * ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  -- assemble
  rw [Complex.GammaSeq, hprod, hfrac, hdenom, hcpow, hzsum, ← hsumcast]
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
  set A : ℂ := ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) with hA
  set E1 : ℂ := Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ) * z)
    with hE1
  set E2 : ℂ := Complex.exp (((Real.log N : ℝ) : ℂ) * z) with hE2
  have hE1ne : E1 ≠ 0 := Complex.exp_ne_zero _
  have hE2ne : E2 ≠ 0 := Complex.exp_ne_zero _
  have hexpneg : Complex.exp (-(z * (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)))
      = E1⁻¹ := by
    rw [hE1, ← Complex.exp_neg]
    congr 1
    ring
  rw [hexpneg]
  field_simp

/-- **The Weierstrass product for 1/Γ** on the integer complement:
Γ(z)⁻¹ = z·e^{γz}·∏'ₙ (1 + z/(n+1))e^{−z/(n+1)}. -/
theorem inv_gamma_eq_prod {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (Complex.Gamma z)⁻¹
      = z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
          * ∏' n : ℕ, (1 + wTerm n z) := by
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hL : Tendsto (fun N => (Complex.GammaSeq z N)⁻¹) atTop (𝓝 ((Complex.Gamma z)⁻¹)) :=
    (Complex.GammaSeq_tendsto_Gamma z).inv₀ (Complex.Gamma_ne_zero hzero)
  have hhar : Tendsto (fun N : ℕ =>
      ((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine Real.tendsto_harmonic_sub_log.congr fun n => ?_
    rw [harmonic_cast_eq]
  have hexp : Tendsto (fun N : ℕ => Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z))
      atTop (𝓝 (Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z))) := by
    have h2 : Tendsto (fun N : ℕ =>
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ)))
        atTop (𝓝 ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hhar
    exact (Complex.continuous_exp.tendsto _).comp (h2.mul_const z)
  have hP : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (∏' n : ℕ, (1 + wTerm n z))) :=
    (multipliable_one_add_wTerm z).hasProd.tendsto_prod_nat
  have hRHS : Tendsto (fun N : ℕ => z * Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
        * ∏' n : ℕ, (1 + wTerm n z))) :=
    (tendsto_const_nhds.mul hexp).mul hP
  have heq : ∀ᶠ N in atTop, (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + wTerm n z) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact inv_gammaSeq_eq hz hN
  exact tendsto_nhds_unique (hL.congr' heq) hRHS

/-- The logarithmic derivative of a single Weierstrass factor. -/
lemma logDeriv_one_add_wTerm {z : ℂ} (hz : z ∈ Complex.integerComplement) (n : ℕ) :
    logDeriv (fun s => 1 + wTerm n s) z = 1 / (z + n + 1) - 1 / ((n : ℂ) + 1) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
    have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
    push_cast at this ⊢
    convert this using 2
  have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
    rw [add_assoc]
    exact hzn
  have hfun : (fun s => 1 + wTerm n s)
      = fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) := by
    funext s
    exact one_add_wTerm n s
  rw [hfun]
  have h1z : (1 + z / ((n : ℂ) + 1)) ≠ 0 := by
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hd1 : HasDerivAt (fun s : ℂ => 1 + s / ((n : ℂ) + 1)) (1 / ((n : ℂ) + 1)) z := by
    have h3 := ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).const_add 1
    simpa [one_div] using h3
  have hd2 : HasDerivAt (fun s : ℂ => Complex.exp (-(s / ((n : ℂ) + 1))))
      (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1)))) z := by
    have hlin : HasDerivAt (fun s : ℂ => -(s / ((n : ℂ) + 1))) (-(1 / ((n : ℂ) + 1))) z := by
      exact ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).neg
    have h5 := hlin.cexp
    simpa [mul_comm] using h5
  have hprod : HasDerivAt
      (fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))))
      (1 / ((n : ℂ) + 1) * Complex.exp (-(z / ((n : ℂ) + 1)))
        + (1 + z / ((n : ℂ) + 1)) * (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))))) z :=
    hd1.mul hd2
  unfold logDeriv
  rw [Pi.div_apply, hprod.deriv]
  have hexpne : Complex.exp (-(z / ((n : ℂ) + 1))) ≠ 0 := Complex.exp_ne_zero _
  have h3 : (1 : ℂ) + (n : ℂ) + z ≠ 0 := by
    intro h
    apply hzn'
    linear_combination h
  field_simp [h3]
  have h4 : ((1 : ℂ) + (n : ℂ) + z) * ((1 + (n : ℂ) + z)⁻¹) = 1 := mul_inv_cancel₀ h3
  linear_combination (-z) * h4

/-- Summability of the digamma partial-fraction series. -/
theorem summable_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  refine Summable.of_norm ?_
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹)) ?_ ?_
  · have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
      have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
        have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
        have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
          funext n
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rwa [heq] at h3
      have h4 := (summable_nat_add_iff 1).mpr h2
      simpa [add_comm] using h4
    exact h1.mul_left _
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with n hn
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hzn
    have hident : 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)
        = z / (((n : ℂ) + 1) * (z + n + 1)) := by
      field_simp
      ring
    have h2n : 2 * ‖z‖ ≤ (n : ℝ) := by
      calc 2 * ‖z‖ ≤ (⌈2 * ‖z‖⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast hn
    have hlow : ((n : ℝ) + 1) / 2 ≤ ‖z + (n : ℂ) + 1‖ := by
      have h1 : ‖((n : ℂ) + 1)‖ - ‖z‖ ≤ ‖z + (n : ℂ) + 1‖ := by
        have h2 := norm_sub_le (z + (n : ℂ) + 1) z
        have h3 : (z + (n : ℂ) + 1) - z = ((n : ℂ) + 1) := by ring
        rw [h3] at h2
        linarith
      rw [norm_natCast_add_one] at h1
      linarith [norm_nonneg z]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hident, norm_div, norm_mul,
      norm_natCast_add_one]
    calc ‖z‖ / (((n : ℝ) + 1) * ‖z + (n : ℂ) + 1‖)
        ≤ ‖z‖ / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by
          gcongr
      _ = 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
          field_simp

/-- **The digamma partial-fraction series, HasSum form**:
Σₙ (1/(n+1) − 1/(z+n+1)) converges to ψ(z) + γ + 1/z on the integer complement. -/
theorem hasSum_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
  set γc : ℂ := ((Real.eulerMascheroniConstant : ℝ) : ℂ) with hγc
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have hopenZ : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  set U : Set ℂ := Metric.ball (0 : ℂ) (‖z‖ + 1) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by
    rw [hU, Metric.mem_ball, dist_zero_right]
    linarith [norm_nonneg z]
  have htend : MultipliableLocallyUniformlyOn (fun n (s : ℂ) => 1 + wTerm n s) U := by
    refine Summable.multipliableLocallyUniformlyOn_nat_one_add hUopen
      (summable_wBound (‖z‖ + 1)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖ + 1⌉₊] with n hn x hx
      have hx1 : ‖x‖ ≤ ‖z‖ + 1 := by
        rw [hU, Metric.mem_ball, dist_zero_right] at hx
        linarith
      have hn1 : ‖z‖ + 1 ≤ (n : ℝ) + 1 := by
        calc ‖z‖ + 1 ≤ (⌈‖z‖ + 1⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
          _ ≤ (n : ℝ) + 1 := by linarith
      calc ‖wTerm n x‖ ≤ 3 * (‖x‖ / ((n : ℝ) + 1)) ^ 2 :=
            norm_wTerm_le (le_trans hx1 hn1)
        _ ≤ 3 * ((‖z‖ + 1) / ((n : ℝ) + 1)) ^ 2 := by
            gcongr
    · intro n
      have hc : Continuous (wTerm n) := by
        unfold wTerm
        fun_prop
      exact hc.continuousOn
  have hfne : ∀ n : ℕ, (fun s : ℂ => 1 + wTerm n s) z ≠ 0 := by
    intro n
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    simp only [one_add_wTerm]
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hgne : z * Complex.exp (γc * z) ≠ 0 := mul_ne_zero hz0 (Complex.exp_ne_zero _)
  have hPne : (∏' n : ℕ, (1 + wTerm n z)) ≠ 0 := by
    intro h
    have h2 := inv_gamma_eq_prod hz
    rw [← hγc, h, mul_zero] at h2
    exact inv_ne_zero hΓne h2
  have hsummable : Summable fun n : ℕ => logDeriv (fun s => 1 + wTerm n s) z := by
    have hcongr : (fun n : ℕ => logDeriv (fun s => 1 + wTerm n s) z)
        = fun n : ℕ => -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      funext n
      rw [logDeriv_one_add_wTerm hz n]
      ring
    rw [hcongr]
    exact (summable_digamma_series hz).neg
  have hlogP : logDeriv (fun s => ∏' n : ℕ, (1 + wTerm n s)) z
      = ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z := by
    refine logDeriv_tprod_eq_tsum hUopen hzU hfne ?_ hsummable htend hPne
    intro n
    have hd : Differentiable ℂ fun s : ℂ => 1 + wTerm n s := by
      unfold wTerm
      fun_prop
    exact hd.differentiableOn
  have hgdiff : Differentiable ℂ fun s : ℂ => s * Complex.exp (γc * s) := by
    fun_prop
  have hPdiff : DifferentiableAt ℂ (fun s => ∏' n : ℕ, (1 + wTerm n s)) z := by
    have hev : (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s)))
        =ᶠ[nhds z] (fun s => ∏' n : ℕ, (1 + wTerm n s)) := by
      filter_upwards [hopenZ.mem_nhds hz] with s hs
      have h2 := inv_gamma_eq_prod hs
      rw [← hγc] at h2
      have hsne : s * Complex.exp (γc * s) ≠ 0 :=
        mul_ne_zero (Complex.integerComplement.ne_zero hs) (Complex.exp_ne_zero _)
      rw [h2]
      exact mul_div_cancel_left₀ _ hsne
    have hd : DifferentiableAt ℂ
        (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s))) z := by
      refine DifferentiableAt.div ?_ (hgdiff z) hgne
      exact Complex.differentiable_one_div_Gamma z
    exact hd.congr_of_eventuallyEq hev.symm
  have hldinv : logDeriv (fun s => (Complex.Gamma s)⁻¹) z = -Complex.digamma z := by
    have h1 : logDeriv ((·⁻¹) ∘ Complex.Gamma) z
        = logDeriv (·⁻¹) (Complex.Gamma z) * deriv Complex.Gamma z := by
      refine logDeriv_comp ?_ (Complex.differentiableAt_Gamma z hzero)
      exact differentiableAt_inv hΓne
    rw [show (fun s => (Complex.Gamma s)⁻¹) = (·⁻¹) ∘ Complex.Gamma from rfl, h1, logDeriv_inv]
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp
  have hev2 : (fun s => (Complex.Gamma s)⁻¹)
      =ᶠ[nhds z] fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s) := by
    filter_upwards [hopenZ.mem_nhds hz] with s hs
    have h2 := inv_gamma_eq_prod hs
    rw [← hγc] at h2
    rw [h2]
  have hlogeq : logDeriv (fun s => (Complex.Gamma s)⁻¹) z
      = logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s)) z := by
    unfold logDeriv
    rw [Pi.div_apply, Pi.div_apply, hev2.deriv_eq, hev2.eq_of_nhds]
  have hmul : logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s)) z
      = logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z
        + logDeriv (fun s => ∏' n : ℕ, (1 + wTerm n s)) z :=
    logDeriv_mul z hgne hPne (hgdiff z) hPdiff
  have hldg : logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z = 1 / z + γc := by
    have hder : HasDerivAt (fun s : ℂ => s * Complex.exp (γc * s))
        (1 * Complex.exp (γc * z) + z * (γc * Complex.exp (γc * z))) z := by
      have h1 : HasDerivAt (fun s : ℂ => Complex.exp (γc * s)) (γc * Complex.exp (γc * z)) z := by
        have hlin : HasDerivAt (fun s : ℂ => γc * s) γc z := by
          simpa using (hasDerivAt_id z).const_mul γc
        have h5 := hlin.cexp
        simpa [mul_comm] using h5
      exact (hasDerivAt_id z).mul h1
    unfold logDeriv
    rw [Pi.div_apply, hder.deriv]
    have he : Complex.exp (γc * z) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hmain : -Complex.digamma z
      = (1 / z + γc) + ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z := by
    rw [← hldinv, hlogeq, hmul, hldg, hlogP]
  have htsum : ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      = Complex.digamma z + γc + 1 / z := by
    have h1 : ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z
        = ∑' n : ℕ, -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      congr 1
      funext n
      rw [logDeriv_one_add_wTerm hz n]
      ring
    rw [h1, tsum_neg] at hmain
    linear_combination hmain
  have h := (summable_digamma_series hz).hasSum
  rwa [htsum] at h

end DigammaSeries
end Digamma210

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
The harmonic logarithm limit is adapted from zeta23/Zeta23/GammaFacts/StirlingVert.lean
at e1a4e6508154ea59f030480661590a9fe3018011 in anthropics/formal-math.
The full license is in the LICENSE file at the root of this repository.
The real reciprocal and integral comparisons are lab derivations.
AI wrote the integration code and these comparisons. Goldbach is open.
-/

namespace Digamma210
open Complex Filter Topology
variable {w : ℂ}
lemma natp1_ne_zero (hw : 0 < w.re) (n : ℕ) : (n : ℂ) + 1 + w ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp at he
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith
theorem tendsto_harmonic_sub_clog (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)) atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  -- split:  [H_N − Real.log(N+1)] − log(1 + w/(N+1))
  have hdecomp : ∀ N : ℕ, (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)
      = (((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ)
        - Complex.log (1 + w / ((N : ℂ) + 1)) := by
    intro N
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN1 : (N : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero N
    have hq' : 1 + w / ((N : ℂ) + 1) = ((N : ℂ) + 1 + w) / ((N : ℂ) + 1) := by
      field_simp
    have hq : 1 + w / ((N : ℂ) + 1) ≠ 0 := by
      rw [hq']; exact div_ne_zero (natp1_ne_zero hw N) hN1
    have hlog : Complex.log ((N : ℂ) + 1 + w)
        = Real.log ((N : ℝ) + 1) + Complex.log (1 + w / ((N : ℂ) + 1)) := by
      rw [← Complex.log_ofReal_mul hN hq, hq']
      congr 1
      push_cast
      field_simp
    rw [hlog, Digamma210.DigammaSeries.harmonic_cast_eq]
    push_cast
    ring
  simp_rw [hdecomp]
  have h1 : Tendsto (fun N : ℕ => ((((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log_add_one
  have h2 : Tendsto (fun N : ℕ => Complex.log (1 + w / ((N : ℂ) + 1))) atTop (𝓝 0) := by
    have hq : Tendsto (fun N : ℕ => w / ((N : ℂ) + 1)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun N : ℕ => ‖w / ((N : ℂ) + 1)‖) = fun N : ℕ => ‖w‖ * (1 / ((N : ℝ) + 1)) := by
        funext N
        rw [norm_div, show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        ring
      rw [this]
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖w‖
    have hcont : ContinuousAt Complex.log 1 := continuousAt_clog (by simp)
    have := hcont.tendsto.comp (by simpa using hq.const_add 1)
    simpa [Function.comp_def] using this
  simpa using h1.sub h2

end Digamma210

namespace Digamma210
open Complex Filter Topology
lemma tendsto_log_sub_sum {z : ℂ} (hz : z ∈ Complex.integerComplement) (hre : 0 < z.re) :
    Tendsto (fun N : ℕ => Complex.log ((N : ℂ) + 1 + z) -
      ∑ n ∈ Finset.range N, 1 / (z + n + 1)) atTop (𝓝 (digamma (z+1))) := by
  have hs := (DigammaSeries.hasSum_digamma_series hz).tendsto_sum_nat
  have hl := tendsto_harmonic_sub_clog hre
  have heq (N : ℕ) : Complex.log ((N : ℂ) + 1 + z) -
      ∑ n ∈ Finset.range N, 1 / (z + n + 1) =
      (∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1))) -
        ((∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1)) - Complex.log ((N : ℂ) + 1 + z)) := by
    rw [Finset.sum_sub_distrib]
    ring
  simp_rw [heq]
  convert hs.sub hl using 1
  rw [digamma_apply_add_one z (by
    intro m hm
    apply hz
    exact ⟨-(m : ℤ), by simpa using hm.symm⟩)]
  ring
end Digamma210

open Complex Filter Topology MeasureTheory intervalIntegral Set

namespace Digamma210

lemma inv_re_vertical (a u : ℝ) :
    (((a : ℂ) + u * I)⁻¹).re = a / (a ^ 2 + u ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp
  ring

lemma reciprocal_step (v u t : ℝ) (hv : 0 < v) (ht : 0 ≤ t) :
    (v + t) / ((v + t) ^ 2 + u ^ 2) - v / (v ^ 2 + u ^ 2) ≤ t / (8 * v ^ 2) := by
  have h0 : 0 < v ^ 2 + u ^ 2 := by positivity
  have h1 : 0 < (v + t) ^ 2 + u ^ 2 := by positivity
  rw [sub_le_iff_le_add]
  apply (div_le_iff₀ h1).2
  rw [← sub_nonneg]
  have he : (t / (8 * v^2) + v / (v^2 + u^2)) * ((v+t)^2 + u^2) - (v+t) =
      t * ((u^2 - 3*v^2)^2 + (2*v*t+t^2)*(v^2+u^2) + 8*v^3*t) /
        (8*v^2*(v^2+u^2)) := by
    field_simp
    ring
  rw [he]
  positivity

lemma hasDerivAt_log_norm_vertical (a u x : ℝ) (hx : 0 < a + x) :
    HasDerivAt (fun y : ℝ => Real.log ‖((a + y : ℝ) : ℂ) + u * I‖)
      ((a + x) / ((a + x) ^ 2 + u ^ 2)) x := by
  have heq : (fun y : ℝ => Real.log ‖((a + y : ℝ) : ℂ) + u * I‖) =
      fun y => Real.log ((a + y)^2 + u^2) / 2 := by
    funext y
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add]
    rw [Real.log_sqrt (by positivity)]
  rw [heq]
  have hd : HasDerivAt (fun y : ℝ => (a + y)^2 + u^2) (2 * (a + x)) x := by
    convert (((hasDerivAt_id x).const_add a).pow 2).add_const (u^2) using 1 <;> simp only [id_eq, Pi.pow_apply] <;> ring
  convert (hd.log (by positivity)).div_const 2 using 1 <;> field_simp <;> ring

lemma log_norm_step (a u : ℝ) (ha : 0 < a) :
    Real.log ‖((a + 1 : ℝ) : ℂ) + u * I‖ - Real.log ‖(a : ℂ) + u * I‖ ≤
      a / (a^2 + u^2) + 1 / (8 * a^2) := by
  let f : ℝ → ℝ := fun x => (a + x) / ((a + x)^2 + u^2)
  have hc : ContinuousOn f (Icc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    have : 0 < a + x := by linarith [hx.1]
    positivity
  have hi : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have he : ∫ x in (0 : ℝ)..1, f x =
      Real.log ‖((a + 1 : ℝ) : ℂ) + u * I‖ - Real.log ‖(a : ℂ) + u * I‖ := by
    convert integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_log_norm_vertical a u x (by
        have : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
        linarith [this.1])) hi using 1 <;> simp
  rw [← he]
  calc
    (∫ x in (0 : ℝ)..1, f x) ≤ (∫ x in (0 : ℝ)..1, (a / (a^2 + u^2) + 1 / (8 * a^2))) := by
      apply integral_mono_on (by norm_num) hi (continuous_const.intervalIntegrable _ _)
      intro x hx
      have hs := reciprocal_step a u x ha hx.1
      have ht : x / (8 * a^2) ≤ 1 / (8 * a^2) := by gcongr; exact hx.2
      dsimp [f]
      linarith
    _ = a / (a^2 + u^2) + 1 / (8 * a^2) := by simp

lemma reciprocal_square_telescope (v : ℝ) (hv : 1 < v) :
    1 / (8 * v^2) ≤ 1 / (8*(v-1)) - 1 / (8*v) := by
  have hv0 : 0 < v := by linarith
  have hv1 : 0 < v-1 := by linarith
  apply (le_sub_iff_add_le).2
  field_simp
  nlinarith

lemma log_norm_partial_sum_le (a u : ℝ) (ha : 1 < a) (N : ℕ) :
    Real.log ‖((a + N : ℝ) : ℂ) + u*I‖ -
      (∑ n ∈ Finset.range N, (a+n) / ((a+n)^2 + u^2)) ≤
      Real.log ‖(a : ℂ) + u*I‖ + 1/(8*(a-1)) - 1/(8*(a+N-1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hs := log_norm_step (a+N) u (by linarith)
    have ht := reciprocal_square_telescope (a+N) (by linarith)
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show a + ((N : ℝ) + 1) = a + N + 1 by ring]
    have he : a + (N : ℝ) + 1 - 1 = a + N := by ring
    rw [he]
    linarith

end Digamma210
/-- LEAF. Unit U-1551. Stirling for the digamma function: `Re ψ(9/4 + iu) ≤ log|9/4 + iu| + 1/10`
for every real `u`; the float maximum of `Re ψ(9/4 + iu) - log|9/4 + iu|` over `|u| ≤ 200` is
negative, `-2.6·10⁻⁵`, and `Re ψ(z) = log|z| - Re z/(2|z|²) + O(|z|⁻²)`. -/
theorem digamma_re_le (u : ℝ) :
    (digamma ((9 / 4 : ℂ) + u * I)).re ≤ Real.log ‖(9 / 4 : ℂ) + u * I‖ + 1 / 10 := by
  let z : ℂ := (5/4 : ℂ) + u*I
  have hz : z ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have he := congrArg Complex.re hn
    norm_num [z] at he
    have h1 : (1 : ℝ) < n := by linarith
    have h2 : (n : ℝ) < 2 := by linarith
    have hn1 : (1 : ℤ) < n := by exact_mod_cast h1
    have hn2 : n < (2 : ℤ) := by exact_mod_cast h2
    omega
  have hre : 0 < z.re := by norm_num [z]
  have hw : z+1 = (9/4 : ℂ) + u*I := by dsimp [z]; ring
  have hl := (Complex.continuous_re.tendsto _).comp (Digamma210.tendsto_log_sub_sum hz hre)
  rw [hw] at hl
  apply le_of_tendsto hl
  apply Filter.Eventually.of_forall
  intro N
  have hb := Digamma210.log_norm_partial_sum_le (9/4) u (by norm_num) N
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hp : 0 ≤ 1 / (8 * ((9/4 : ℝ)+N-1)) := by
    have : 0 < (9/4 : ℝ)+N-1 := by linarith
    positivity
  have he : (N : ℂ)+1+z = (((9/4 : ℝ)+N : ℝ) : ℂ) + u*I := by
    dsimp [z]
    push_cast
    ring
  dsimp only [Function.comp_def]
  rw [he]
  simp only [Complex.sub_re, Complex.log_re]
  have hsum : (∑ n ∈ Finset.range N, 1 / (z+n+1)).re =
      ∑ n ∈ Finset.range N, ((9/4 : ℝ)+n) / (((9/4 : ℝ)+n)^2+u^2) := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [show z+(n:ℂ)+1 = ((((9/4 : ℝ)+n) : ℝ) : ℂ)+u*I by dsimp [z]; push_cast; ring,
      one_div, Digamma210.inv_re_vertical]
  rw [hsum]
  norm_num at hb ⊢
  have hinv : 0 ≤ ((9/4 : ℝ)+N-1)⁻¹ := inv_nonneg.mpr (by linarith)
  linarith

/-- LEAF. Unit U-1551. The real inequality closing the bound: for `|g| ≥ 14`,
`2 (3/10 + Re 1/(3/2 + ig) - (1/2) log π + (log|9/4 + ig/2| + 1/10)/2) ≤ log |g|`; the left
side is at most `log |g| - 1.07`. -/
theorem final_numeric (g : ℝ) (hg : 14 ≤ |g|) :
    2 * (3 / 10 + (1 / ((3 / 2 : ℂ) + g * I)).re - Real.log Real.pi / 2
      + (Real.log ‖(9 / 4 : ℂ) + (g / 2 : ℝ) * I‖ + 1 / 10) / 2) ≤ Real.log |g| := by
  have hg0 : 0 < |g| := by linarith
  have hsq : 196 ≤ g ^ 2 := by nlinarith [sq_abs g, sq_nonneg (|g| - 14)]
  have hn : ‖(9 / 4 : ℂ) + (g / 2 : ℝ) * I‖ ≤ |g| := by
    apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num
    nlinarith
  have hn0 : 0 < ‖(9 / 4 : ℂ) + (g / 2 : ℝ) * I‖ := by
    apply norm_pos_iff.mpr
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hl := Real.log_le_log hn0 hn
  have hpi : 1 ≤ Real.log Real.pi := by
    exact (Real.le_log_iff_exp_le Real.pi_pos).mpr
      (Real.exp_one_lt_three.le.trans Real.pi_gt_three.le)
  have hi : (1 / ((3 / 2 : ℂ) + g * I)).re ≤ 1 / 10 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    norm_num
    apply (div_le_iff₀ (by nlinarith [sq_nonneg g] : (0 : ℝ) < 9 / 4 + g * g)).mpr
    nlinarith
  linarith

lemma re_inv_two (d : ℝ) : (1 / ((2 : ℂ) + d * I)).re = 2 / (4 + d ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp
  ring

end LeanLab.Routes.Decomp1551b
