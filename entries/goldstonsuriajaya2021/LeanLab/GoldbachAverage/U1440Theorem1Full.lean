module

public import LeanLab.GoldbachAverage.GSTheorem1
public import LeanLab.PNTPort.ExplicitPsi1.TrivialTerms
public import LeanLab.PNTPort.StrongPNT.ZetaConj
public import LeanLab.PNTPort.ExplicitPsi1.Log2Pi

/-!
# Goldston and Suriajaya, Theorem 1, the full exact formula, eq. (11), proved

Lab unit U-1440, run 20261021T1603Z-28836. AI wrote this Lean code, Claude by Anthropic. Known
mathematics, no cited input.

D. A. Goldston and A. I. Suriajaya, *On an average Goldbach representation formula of Fujii*,
arXiv 2110.14250v2, Theorem 1, eq. (11): for `N ≥ 2`,

`Σ_{n ≤ N} ψ₂(n) = N²/2 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) - (2 log 2π - 1/2) N + 2 (ζ'/ζ)(-1)
   - Σ_{k ≥ 1} N^{1-2k}/(k(2k-1)) + E(N)`,

an exact identity, with `E(N)` of eq. (12), `ψ₂(n) = Σ_{m + m' = n} Λ(m) Λ(m')`, here `G n`.
The lab's `gs_theorem1_proved` is the "in particular" form eq. (13), with the three explicit lower
terms put into `O(N)`; `gs_theorem1_of_full` derives it from the full form.

Two points of presentation. The paper writes `E(N)`; the Lean `EGS N r` carries the radius
`0 < r < 1` of the power series as an argument, and `EGS_indep_r` proves that its value does not
depend on `r`. The paper's identity is between real numbers; `gs_theorem1_full` is stated in `ℂ`,
where `Z1 N` and `EGS N r` live, and `EGS_im_eq_zero`, `logDeriv_zeta_neg_one_im` and
`Z1_im_eq_zero` prove that every term is real, so `gs_theorem1_full_real` is the same identity
in `ℝ` with real parts.

Route: the identity `Σ G = E(N) + 2ψ₁(N) - N(N - 1)/2` of GSTheorem1.lean, `EGS_eq` and `sum_dc`,
and the exact explicit formula for `ψ₁` with the trivial zeros, Davenport chapter 17, the lab's
`PNTPort.ExplicitPsi1.Trivial.explicit_formula_psi1_trivial`, with `ζ'(0)/ζ(0) = log 2π`.
Binary Goldbach is open; this is an average over n.
-/

@[expose] public section


open Finset Complex
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section
namespace LeanLab.GoldbachAverage.U1440


/-- The trivial zero sum of eq. (11), `Σ_{k ≥ 1} N^{1-2k}/(k(2k-1))`, written with `k + 1`
for `k ≥ 0`. -/
def trivSum (N : ℝ) : ℝ :=
  ∑' k : ℕ, N ^ (1 - 2 * ((k : ℝ) + 1)) / (((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) - 1))

open LeanLab.GoldbachAverage LeanLab.PNTPort.ExplicitPsi1 LeanLab.PNTPort.ExplicitPsi1.Trivial

lemma trivSum_eq {N : ℝ} (hN : 0 < N) : trivSum N = 2 * N * ∑' n, tb N n := by
  rw [trivSum, ← tsum_mul_left]
  apply tsum_congr; intro k
  unfold tb
  have e : N ^ (1 - 2 * ((k : ℝ) + 1)) = N * N ^ (-2 * ((k : ℝ) + 1)) := by
    rw [show (1 - 2 * ((k : ℝ) + 1)) = 1 + (-2 * ((k : ℝ) + 1)) by ring,
      Real.rpow_add hN, Real.rpow_one]
  rw [e, show (2 * ((k : ℝ) + 1) - 1) = 2 * k + 1 by ring]
  have h1 : ((k : ℝ) + 1) * (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (2 * (k : ℝ) + 2) * (2 * k + 1) ≠ 0 := by positivity
  field_simp

/-- **Derived result of this entry**: `0 ≤ Σ_{k ≥ 1} N^{1-2k}/(k(2k-1)) ≤ π²/3` for `N ≥ 1`, so the
trivial zero sum is a genuine convergent sum and is `O(1)`. -/
theorem trivSum_bounds {N : ℝ} (hN : 1 ≤ N) : 0 ≤ trivSum N ∧ trivSum N ≤ π ^ 2 / 3 := by
  rw [trivSum_eq (by linarith)]
  obtain ⟨h0, h1⟩ := y_tsum_tb_bounds hN
  constructor <;> nlinarith

/-- **Goldston-Suriajaya Theorem 1, eq. (11), the full printed statement**, unconditional:
for every integer `N ≥ 2` and every `0 < r < 1`,
`Σ_{n ≤ N} ψ₂(n) = N²/2 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) - (2 log 2π - 1/2) N + 2 (ζ'/ζ)(-1)
   - Σ_{k ≥ 1} N^{1-2k}/(k(2k-1)) + E(N)`. -/
theorem gs_theorem1_full (N : ℕ) (hN : 2 ≤ N) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    ((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) =
      (N : ℂ) ^ 2 / 2 - 2 * Z1 N - ((2 * Real.log (2 * π) - 1 / 2 : ℝ) : ℂ) * N
        + 2 * (deriv riemannZeta (-1) / riemannZeta (-1)) - ((trivSum N : ℝ) : ℂ)
        + EGS N r := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN0 : (0 : ℝ) < N := by linarith
  set P := ∑ a ∈ range (N + 1), Λ a * ((N : ℝ) - a) with hPdef
  have hRg : LZCesaroShort.Rg N (N : ℝ) = P := by
    rw [LZCesaroShort.Rg]; apply sum_congr rfl; intro a ha; rw [mem_range] at ha
    have : (a : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp ha
    rw [max_eq_right (by linarith)]
  -- `ψ₁(N) = N Σ Λ(n) w₁(n/N)`
  have hP : ((P : ℝ) : ℂ) = ((N : ℝ) : ℂ) *
      ∑' n : ℕ, (Λ n : ℂ) * PNTPort.ZetaZeros.w1 (n / (N : ℝ)) := by
    rw [← hRg]; exact LZCesaroShort.Rg_eq hN0 le_rfl
  -- the exact explicit formula with the trivial zeros
  have hS := explicit_formula_psi1_trivial hN1
  rw [logDeriv_zeta_zero, Complex.cpow_neg_one] at hS
  -- the nontrivial zero sum is `Z1`
  have hZ : ((N : ℝ) : ℂ) * ∑' ρ : Zall, zterm (N : ℝ) ρ = Z1 N := by
    rw [LZCesaroShort.uZ_eq hN0, LZCesaroShort.Wf, Z1, zeroSum]
    have e : (∑' ρ : Zall, LZCesaroShort.wterm (N : ℝ) ρ.1) =
        ∑' ρ : NontrivialZero, LZCesaroShort.wterm (N : ℝ) ρ.1 := by
      rw [Zall_eq]; rfl
    rw [e]; rfl
  -- the trivial zero sum
  have hT : ∑' n : ℕ, tterm (N : ℝ) n = ((∑' n, tb (N : ℝ) n : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; exact tsum_congr (tterm_eq hN0)
  have hTr : ((trivSum N : ℝ) : ℂ) = 2 * ((N : ℝ) : ℂ) * ((∑' n, tb (N : ℝ) n : ℝ) : ℂ) := by
    rw [trivSum_eq hN0]; push_cast; ring
  have hinv : ((N : ℝ) : ℂ) * ((N : ℝ) : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast hN0.ne')
  -- orthogonality and the expansion
  have hE : EGS N r = ((∑ n ∈ range (N + 1), G n - 2 * P + (N : ℝ) * (N - 1) / 2 : ℝ) : ℂ) := by
    rw [EGS_eq N hr0 hr, sum_dc]
  rw [hE]
  push_cast at hP hS hZ hT hTr hinv ⊢
  set d1 := deriv riemannZeta (-1) / riemannZeta (-1)
  linear_combination 2 * hP + 2 * (N : ℂ) * hS - 2 * hZ +
    2 * d1 * hinv - 2 * (N : ℂ) * hT + hTr

/-- **Goldston-Suriajaya Theorem 1, eq. (13)**, deduced here from eq. (11): the simplified form, with the
three explicit lower terms bounded by `K N`; this is the statement of the lab's
`gs_theorem1_proved`. -/
theorem gs_theorem1_of_full : ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ r : ℝ, 0 < r → r < 1 →
    ‖((∑ n ∈ range (N + 1), G n : ℝ) : ℂ) - (N : ℂ) ^ 2 / 2 + 2 * Z1 N - EGS N r‖ ≤ K * N := by
  set L := Real.log (2 * π)
  set d1 := deriv riemannZeta (-1) / riemannZeta (-1)
  refine ⟨2 * |L| + 1 + 2 * ‖d1‖ + 4, fun N hN r hr0 hr => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  rw [gs_theorem1_full N hN r hr0 hr]
  have e : (N : ℂ) ^ 2 / 2 - 2 * Z1 N - ((2 * L - 1 / 2 : ℝ) : ℂ) * N + 2 * d1 -
      ((trivSum N : ℝ) : ℂ) + EGS N r - (N : ℂ) ^ 2 / 2 + 2 * Z1 N - EGS N r =
      -(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ)) + 2 * d1 - ((trivSum N : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  obtain ⟨t0, t1⟩ := trivSum_bounds hN1
  have hpi : π ^ 2 / 3 ≤ 4 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have n1 : ‖-(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ))‖ ≤ (2 * |L| + 1) * N := by
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < N)]
    have : |2 * L - 1 / 2| ≤ 2 * |L| + 1 := by
      have := abs_sub (2 * L) (1 / 2)
      rw [abs_mul, abs_two] at this
      norm_num at this ⊢; linarith
    nlinarith
  have n2 : ‖2 * d1‖ ≤ 2 * ‖d1‖ * N := by
    rw [norm_mul, Complex.norm_two]; nlinarith [norm_nonneg d1]
  have n3 : ‖((trivSum N : ℝ) : ℂ)‖ ≤ 4 * N := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t0]; nlinarith
  calc ‖-(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ)) + 2 * d1 - ((trivSum N : ℝ) : ℂ)‖
      ≤ ‖-(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ))‖ + ‖2 * d1‖ +
          ‖((trivSum N : ℝ) : ℂ)‖ := by
        have a1 := norm_sub_le (-(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ)) + 2 * d1)
          ((trivSum N : ℝ) : ℂ)
        have a2 := norm_add_le (-(((2 * L - 1 / 2 : ℝ) : ℂ) * ((N : ℝ) : ℂ))) (2 * d1)
        linarith
    _ ≤ (2 * |L| + 1) * N + 2 * ‖d1‖ * N + 4 * N := by linarith
    _ = (2 * |L| + 1 + 2 * ‖d1‖ + 4) * N := by ring

/-- The derived form has exactly the type of `gs_theorem1_proved`, eq. (13). -/
example : type_of% gs_theorem1_proved := gs_theorem1_of_full

/-- **Derived result of this entry, a non-vacuity check**: the hypotheses of `gs_theorem1_full`
hold at `N = 2`, `r = 1/2`, and the identity there reads
`0 = 2 - 2 Σ_ρ 2^{ρ+1}/(ρ(ρ+1)) - (2 log 2π - 1/2)·2 + 2 (ζ'/ζ)(-1) - Σ_k 2^{1-2k}/(k(2k-1)) + E(2)`,
since `Σ_{n ≤ 2} ψ₂(n) = 0`. -/
theorem gs_theorem1_full_at_two :
    (0 : ℂ) = (2 : ℂ) ^ 2 / 2 - 2 * Z1 2 - ((2 * Real.log (2 * π) - 1 / 2 : ℝ) : ℂ) * 2
        + 2 * (deriv riemannZeta (-1) / riemannZeta (-1)) - ((trivSum 2 : ℝ) : ℂ)
        + EGS 2 (1 / 2) := by
  have h := gs_theorem1_full 2 le_rfl (1 / 2) (by norm_num) (by norm_num)
  have hG : ∑ n ∈ range (2 + 1), G n = 0 := by
    simp [Finset.sum_range_succ, G, Finset.Nat.antidiagonal_succ,
      ArithmeticFunction.vonMangoldt_apply_one]
  rw [hG] at h
  push_cast at h ⊢
  exact h

/-- **Derived result of this entry**: `E(N)` does not depend on the radius `r`. For `0 < r < 1` and
`0 < r' < 1`, `EGS N r = EGS N r'`, both equal to `Σ_{m=1}^{N} Σ_{a+b=m} (Λ(a) - 1)(Λ(b) - 1)`
with `a, b ≥ 1`, by orthogonality, `EGS_eq`. The paper writes `E(N)` without `r`. -/
theorem EGS_indep_r (N : ℕ) {r r' : ℝ} (hr0 : 0 < r) (hr : r < 1) (hr0' : 0 < r') (hr' : r' < 1) :
    EGS N r = EGS N r' := by
  rw [EGS_eq N hr0 hr, EGS_eq N hr0' hr']

/-- **Derived result of this entry**: `E(N)` is real, `Im EGS N r = 0` for `0 < r < 1`. -/
theorem EGS_im_eq_zero (N : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r < 1) : (EGS N r).im = 0 := by
  rw [EGS_eq N hr0 hr, Complex.im_sum]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  rw [dc_eq_real]; exact Complex.ofReal_im _

/-- **Derived result of this entry**: the constant `(ζ'/ζ)(-1)` is real. -/
theorem logDeriv_zeta_neg_one_im : (deriv riemannZeta (-1) / riemannZeta (-1)).im = 0 := by
  have h := logDerivZeta_conj (-1)
  have hc : (starRingEnd ℂ) (-1 : ℂ) = -1 := by simp
  rw [hc] at h
  simp only [Pi.div_apply] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- **Derived result of this entry**: the zero sum `Σ_ρ N^{ρ+1}/(ρ(ρ+1))` is real for `N ≥ 2`,
read off the imaginary part of `gs_theorem1_full`. -/
theorem Z1_im_eq_zero (N : ℕ) (hN : 2 ≤ N) : (Z1 N).im = 0 := by
  have h := gs_theorem1_full N hN (1 / 2) (by norm_num) (by norm_num)
  have hE := EGS_im_eq_zero N (r := 1 / 2) (by norm_num) (by norm_num)
  have hdi := logDeriv_zeta_neg_one_im
  set d := deriv riemannZeta (-1) / riemannZeta (-1) with hdd
  set E := EGS N (1 / 2) with hEE
  have hd : ((d.re : ℝ) : ℂ) = d := Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, hdi])
  have he : ((E.re : ℝ) : ℂ) = E := Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, hE])
  have hz : Z1 N = ((((N : ℝ) ^ 2 / 2 - (2 * Real.log (2 * π) - 1 / 2) * N + 2 * d.re - trivSum N
      + E.re - ∑ n ∈ range (N + 1), G n) / 2 : ℝ) : ℂ) := by
    push_cast
    rw [hd, he]
    push_cast at h
    linear_combination (1 / 2 : ℂ) * h
  rw [hz, Complex.ofReal_im]

/-- **Goldston-Suriajaya Theorem 1, eq. (11), as an identity of real numbers**: the real parts of
the terms of `gs_theorem1_full`, which are all real by `Z1_im_eq_zero`,
`logDeriv_zeta_neg_one_im` and `EGS_im_eq_zero`. For every integer `N ≥ 2` and `0 < r < 1`,
`Σ_{n ≤ N} ψ₂(n) = N²/2 - 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) - (2 log 2π - 1/2) N + 2 (ζ'/ζ)(-1)
   - Σ_{k ≥ 1} N^{1-2k}/(k(2k-1)) + E(N)`. -/
theorem gs_theorem1_full_real (N : ℕ) (hN : 2 ≤ N) (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    ∑ n ∈ range (N + 1), G n =
      (N : ℝ) ^ 2 / 2 - 2 * (Z1 N).re - (2 * Real.log (2 * π) - 1 / 2) * N
        + 2 * (deriv riemannZeta (-1) / riemannZeta (-1)).re - trivSum N
        + (EGS N r).re := by
  have h := gs_theorem1_full N hN r hr0 hr
  have hz : (((Z1 N).re : ℝ) : ℂ) = Z1 N :=
    Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, Z1_im_eq_zero N hN])
  have hd : (((deriv riemannZeta (-1) / riemannZeta (-1)).re : ℝ) : ℂ) =
      deriv riemannZeta (-1) / riemannZeta (-1) :=
    Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, logDeriv_zeta_neg_one_im])
  have he : (((EGS N r).re : ℝ) : ℂ) = EGS N r :=
    Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, EGS_im_eq_zero N hr0 hr])
  apply Complex.ofReal_injective
  push_cast
  rw [hz, hd, he]
  push_cast at h
  linear_combination h

/-- **Derived result of this entry**: the zero sum in `Z1 x` converges absolutely: for every real
`x > 0` the family `ρ ↦ m(ρ) x^{ρ+1}/(ρ(ρ+1))` over the nontrivial zeros is summable, so `Z1 x` is its
genuine unordered sum, not the junk value `0`. The paper uses this absolute convergence. -/
theorem zeroSum_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun ρ : NontrivialZero => (analyticOrderNatAt riemannZeta ρ.1 : ℂ) *
      ((x : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1)))) := by
  have hs := (PNTPort.ExplicitPsi1.summable_zterm hx).mul_left (x : ℂ)
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e : ∀ ρ : PNTPort.ExplicitPsi1.Zall, (x : ℂ) * PNTPort.ExplicitPsi1.zterm x ρ =
      (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * ((x : ℂ) ^ (ρ.1 + 1) / (ρ.1 * (ρ.1 + 1))) := by
    intro ρ
    simp only [PNTPort.ExplicitPsi1.zterm]
    rw [cpow_add _ _ hx0, cpow_one]
    ring
  simp_rw [e] at hs
  rw [PNTPort.ExplicitPsi1.Zall_eq] at hs
  exact hs

end LeanLab.GoldbachAverage.U1440
