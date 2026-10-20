module

public import LeanLab.PNTPort.DirichletZF.SiegelSign
public import LeanLab.PNTPort.DirichletZF.Exceptional
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.Linearity

/-!
# The Taylor coefficients of `ζ L(χ₁) L(χ₂) L(χ₁χ₂)` at `2` have the right sign

Lab proof, unit U-5111. AI wrote this file. Known mathematics, no cited input, a step of the
Estermann-Goldfeld proof of Siegel's theorem, Davenport chapter 21.

For real characters `χ₁, χ₂` mod `N`, `χᵢ² = χ₀`, and `F(s) = ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁χ₂)`:
* `LFunction_real_nonneg`: `L(σ, χ) ≥ 0` for real `σ > 1`, from the Euler product;
* `Fq_taylor_nonneg`: `(-1)^m F^{(m)}(2) ≥ 0` for every `m`, nonnegative real.
So `F(s) = ∑ b_m (2 - s)^m` near `2` with `b_m ≥ 0`.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter Topology LSeries
open scoped LSeries.notation ComplexOrder

variable {N : ℕ} [NeZero N]

/-- `F = ζ L(χ₁) L(χ₂) L(χ₁χ₂)`. -/
noncomputable def Fq (χ₁ χ₂ : DirichletCharacter ℂ N) : ℂ → ℂ := fun s ↦
  riemannZeta s * DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
    DirichletCharacter.LFunction (χ₁ * χ₂) s

lemma real_char_eq {M : ℕ} {χ : DirichletCharacter ℂ M} (h : χ ^ 2 = 1) (n : ℕ) :
    χ n = ((χ n).re : ℂ) := by
  apply Complex.ext <;> simp [im_eq_zero_of_sq h n]

lemma real_char_bound {M : ℕ} (χ : DirichletCharacter ℂ M) (n : ℕ) :
    -1 ≤ (χ n).re ∧ (χ n).re ≤ 1 := by
  have := (Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n)
  exact abs_le.mp this

/-- `L(σ, χ) ≥ 0` for a real character and real `σ > 1`. -/
lemma LFunction_real_nonneg {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M} (h : χ ^ 2 = 1)
    {σ : ℝ} (hσ : 1 < σ) : 0 ≤ DirichletCharacter.LFunction χ σ := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  refine (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).nonneg fun p ↦ ?_
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (p.prop).pos
  have e1 : ((p : ℕ) : ℂ) ^ (-(σ : ℂ)) = (((p : ℕ) : ℝ) ^ (-σ) : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow hp0.le]
  have hx : ((p : ℕ) : ℝ) ^ (-σ) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast (p.prop).two_le
    calc ((p : ℕ) : ℝ) ^ (-σ) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / (p : ℕ) := by rw [Real.rpow_neg_one]; ring
      _ ≤ 1 / 2 := by gcongr
  have hx0 : 0 ≤ ((p : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg hp0.le _
  obtain ⟨hb1, hb2⟩ := real_char_bound χ p
  have e : (1 - χ ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ =
      (((1 - (χ (p : ℕ)).re * ((p : ℕ) : ℝ) ^ (-σ))⁻¹ : ℝ) : ℂ) := by
    rw [e1, real_char_eq h (p : ℕ)]; push_cast; rfl
  rw [e]
  refine Complex.zero_le_real.mpr (inv_nonneg.mpr ?_)
  nlinarith

lemma riemannZeta_real_nonneg {σ : ℝ} (hσ : 1 < σ) : 0 ≤ riemannZeta σ := by
  have := LFunction_real_nonneg (M := 1) (χ := 1) (by norm_num) hσ
  rwa [DirichletCharacter.LFunction_modOne_eq] at this

/-- The coefficients `c(n) = Λ(n)(1 + χ₁(n))(1 + χ₂(n))` of `-F'/F`. -/
noncomputable def cq (χ₁ χ₂ : DirichletCharacter ℂ N) : ℕ → ℂ :=
  ↗ArithmeticFunction.vonMangoldt + ↗χ₁ * ↗ArithmeticFunction.vonMangoldt +
    ↗χ₂ * ↗ArithmeticFunction.vonMangoldt + ↗(χ₁ * χ₂) * ↗ArithmeticFunction.vonMangoldt

omit [NeZero N] in
lemma cq_eq_real {χ₁ χ₂ : DirichletCharacter ℂ N} (h1 : χ₁ ^ 2 = 1) (h2 : χ₂ ^ 2 = 1) (n : ℕ) :
    cq χ₁ χ₂ n = ((ArithmeticFunction.vonMangoldt n * ((1 + (χ₁ n).re) * (1 + (χ₂ n).re)) : ℝ) :
      ℂ) := by
  simp only [cq, Pi.add_apply, Pi.mul_apply, MulChar.mul_apply]
  apply Complex.ext <;>
    simp [im_eq_zero_of_sq h1 n, im_eq_zero_of_sq h2 n, Complex.mul_re, Complex.mul_im]
  ring

omit [NeZero N] in
lemma cq_real_nonneg (χ₁ χ₂ : DirichletCharacter ℂ N) (n : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt n * ((1 + (χ₁ n).re) * (1 + (χ₂ n).re)) := by
  obtain ⟨a1, -⟩ := real_char_bound χ₁ n
  obtain ⟨a2, -⟩ := real_char_bound χ₂ n
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (mul_nonneg (by linarith) (by linarith))

lemma logMul_iter_apply (f : ℕ → ℂ) (j n : ℕ) :
    (LSeries.logMul)^[j] f n = (Complex.log n) ^ j * f n := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [LSeries.logMul]; ring

omit [NeZero N] in
lemma summable_cq {χ₁ χ₂ : DirichletCharacter ℂ N} {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (cq χ₁ χ₂) s := by
  unfold cq
  exact LSeriesSummable.add (LSeriesSummable.add (LSeriesSummable.add
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ₁ hs))
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ₂ hs))
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ₁ * χ₂) hs)

lemma abscissa_cq_le (χ₁ χ₂ : DirichletCharacter ℂ N) : abscissaOfAbsConv (cq χ₁ χ₂) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
    summable_cq (by simpa using hy)

lemma Q_signs {χ₁ χ₂ : DirichletCharacter ℂ N} (h1 : χ₁ ^ 2 = 1) (h2 : χ₂ ^ 2 = 1) (j : ℕ) :
    0 ≤ (-1) ^ j * iteratedDeriv j (LSeries (cq χ₁ χ₂)) 2 := by
  have hab : abscissaOfAbsConv (cq χ₁ χ₂) < (2 : ℂ).re :=
    lt_of_le_of_lt (abscissa_cq_le χ₁ χ₂) (by simp only [Complex.re_ofNat]; exact_mod_cast (show (1 : ℝ) < 2 by norm_num))
  rw [LSeries_iteratedDeriv j hab, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  unfold LSeries
  refine tsum_nonneg fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, logMul_iter_apply, cq_eq_real h1 h2]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e1 : (n : ℂ) ^ (2 : ℂ) = (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, Complex.ofReal_cpow hn0.le]
  have e2 : Complex.log n = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [e1, e2]
  have : 0 ≤ Real.log n ^ j * (ArithmeticFunction.vonMangoldt n *
      ((1 + (χ₁ n).re) * (1 + (χ₂ n).re))) / (n : ℝ) ^ (2 : ℝ) :=
    div_nonneg (mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) _) (cq_real_nonneg χ₁ χ₂ n))
      (Real.rpow_nonneg hn0.le _)
  have h := Complex.zero_le_real.mpr this
  push_cast at h ⊢
  exact h

/-- `(-1)^m F^{(m)}(2) ≥ 0`. -/
theorem Fq_taylor_nonneg {χ₁ χ₂ : DirichletCharacter ℂ N} (h1 : χ₁ ^ 2 = 1) (h2 : χ₂ ^ 2 = 1)
    (m : ℕ) : 0 ≤ (-1) ^ m * iteratedDeriv m (Fq χ₁ χ₂) 2 := by
  set U : Set ℂ := {z | 1 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h2U : (2 : ℂ) ∈ U := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  have hne : ∀ z ∈ U, z ≠ 1 := by intro z hz h; simp [U, h] at hz
  have hdL : ∀ (ψ : DirichletCharacter ℂ N), ∀ z ∈ U,
      DifferentiableAt ℂ (DirichletCharacter.LFunction ψ) z :=
    fun ψ z hz ↦ DirichletCharacter.differentiableAt_LFunction ψ z (Or.inl (hne z hz))
  have hdZ : ∀ z ∈ U, DifferentiableAt ℂ riemannZeta z :=
    fun z hz ↦ differentiableAt_riemannZeta (hne z hz)
  have hdF : DifferentiableOn ℂ (Fq χ₁ χ₂) U := fun z hz ↦
    ((((hdZ z hz).mul (hdL χ₁ z hz)).mul (hdL χ₂ z hz)).mul (hdL (χ₁ * χ₂) z hz)).differentiableWithinAt
  have hFan : AnalyticAt ℂ (Fq χ₁ χ₂) 2 := hdF.analyticAt (hUo.mem_nhds h2U)
  have hQan : AnalyticAt ℂ (LSeries (cq χ₁ χ₂)) 2 :=
    LSeries_analyticOnNhd _ 2 (lt_of_le_of_lt (abscissa_cq_le χ₁ χ₂)
      (by simp only [Complex.re_ofNat]; exact_mod_cast (show (1 : ℝ) < 2 by norm_num)))
  refine sign_of_logDeriv hFan hQan ?_ ?_ (Q_signs h1 h2) m
  · filter_upwards [hUo.mem_nhds h2U] with z hz
    have hz1 : 1 < z.re := hz
    have nZ : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz1
    have nL : ∀ ψ : DirichletCharacter ℂ N, DirichletCharacter.LFunction ψ z ≠ 0 :=
      fun ψ ↦ DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inr (hne z hz)) hz1.le
    have hlog : logDeriv (Fq χ₁ χ₂) z = -LSeries (cq χ₁ χ₂) z := by
      have e : Fq χ₁ χ₂ = riemannZeta * DirichletCharacter.LFunction χ₁ *
          DirichletCharacter.LFunction χ₂ * DirichletCharacter.LFunction (χ₁ * χ₂) := rfl
      have a1 : (riemannZeta * DirichletCharacter.LFunction χ₁) z ≠ 0 := by
        simp only [Pi.mul_apply]; exact mul_ne_zero nZ (nL _)
      have a2 : (riemannZeta * DirichletCharacter.LFunction χ₁ *
          DirichletCharacter.LFunction χ₂) z ≠ 0 := by
        simp only [Pi.mul_apply]; exact mul_ne_zero (mul_ne_zero nZ (nL _)) (nL _)
      rw [e, logDeriv_mul z a2 (nL _)
          (((hdZ z hz).mul (hdL χ₁ z hz)).mul (hdL χ₂ z hz)) (hdL (χ₁ * χ₂) z hz),
        logDeriv_mul z a1 (nL _) ((hdZ z hz).mul (hdL χ₁ z hz)) (hdL χ₂ z hz),
        logDeriv_mul z nZ (nL _) (hdZ z hz) (hdL χ₁ z hz)]
      simp only [logDeriv_apply]
      have eZ : deriv riemannZeta z / riemannZeta z =
          -LSeries ↗ArithmeticFunction.vonMangoldt z := by
        rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz1]; ring
      have eL : ∀ ψ : DirichletCharacter ℂ N,
          deriv (DirichletCharacter.LFunction ψ) z / DirichletCharacter.LFunction ψ z =
          -LSeries (↗ψ * ↗ArithmeticFunction.vonMangoldt) z := by
        intro ψ; rw [← neg_logDeriv_eq_LSeries ψ hz1]; ring
      rw [eZ, eL, eL, eL]
      have s1 := ArithmeticFunction.LSeriesSummable_vonMangoldt hz1
      have s2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ₁ hz1
      have s3 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ₂ hz1
      have s4 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ₁ * χ₂) hz1
      have eQ : LSeries (cq χ₁ χ₂) z = LSeries ↗ArithmeticFunction.vonMangoldt z +
          LSeries (↗χ₁ * ↗ArithmeticFunction.vonMangoldt) z +
          LSeries (↗χ₂ * ↗ArithmeticFunction.vonMangoldt) z +
          LSeries (↗(χ₁ * χ₂) * ↗ArithmeticFunction.vonMangoldt) z := by
        unfold cq
        rw [LSeries_add ((s1.add s2).add s3) s4, LSeries_add (s1.add s2) s3, LSeries_add s1 s2]
      rw [eQ]; ring
    have hFz : Fq χ₁ χ₂ z ≠ 0 := by
      simp only [Fq]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero nZ (nL _)) (nL _)) (nL _)
    rw [logDeriv_apply] at hlog
    rw [show deriv (Fq χ₁ χ₂) z = Fq χ₁ χ₂ z * (deriv (Fq χ₁ χ₂) z / Fq χ₁ χ₂ z) by
      field_simp, hlog]
    ring
  · have e2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
    simp only [Fq]
    rw [e2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (riemannZeta_real_nonneg (by norm_num))
      (LFunction_real_nonneg h1 (by norm_num))) (LFunction_real_nonneg h2 (by norm_num)))
      (LFunction_real_nonneg (by rw [mul_pow, h1, h2, one_mul]) (by norm_num))

end LeanLab.PNTPort.DirichletZF

