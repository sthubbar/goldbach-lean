module

public import LeanLab.PNTPort.DirichletZF.SiegelG
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.Liouville

/-!
# Two bounds for the Estermann-Goldfeld lemma

Lab proof, unit U-5111. AI wrote this file. Known mathematics, no cited input.

* `norm_LFunction_two_ge`: `‖L(2, χ)‖ ≥ 6/π²` for every Dirichlet character;
* `Fq_two_ge`: `‖F(2)‖ ≥ 1/4` for `F = ζ L(χ₁) L(χ₂) L(χ₁χ₂)`;
* `norm_Gq_sphere_le`: an absolute `C` with `‖G(s)‖ ≤ C N³` on `|s - 2| = 3/2`, for
  non-principal `χ₁, χ₂` mod `N` with `χ₁χ₂ ≠ χ₀`, `G = F - λ/(s - 1)`;
* `norm_iteratedDeriv_Gq_le`: `‖G^{(m)}(2)‖ ≤ m! C N³ (2/3)^m`, by Cauchy's estimate.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter Topology Metric Nat
open scoped LSeries.notation ArithmeticFunction.Moebius Real

variable {N : ℕ} [NeZero N]

lemma tsum_norm_term_one_two :
    ∑' n : ℕ, ‖LSeries.term 1 (2 : ℂ) n‖ = π ^ 2 / 6 := by
  refine (HasSum.tsum_eq ?_)
  convert hasSum_zeta_two using 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.norm_term_eq]
  simp only [hn, ite_false, Pi.one_apply, norm_one]
  simp

lemma norm_LSeries_le_zeta_two {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖LSeries f 2‖ ≤ π ^ 2 / 6 := by
  have hs1 : Summable fun n : ℕ ↦ ‖LSeries.term 1 (2 : ℂ) n‖ :=
    (LSeriesSummable_one_iff.mpr (by norm_num)).norm
  have hb : ∀ n, ‖LSeries.term f 2 n‖ ≤ ‖LSeries.term 1 (2 : ℂ) n‖ := fun n ↦
    LSeries.norm_term_le 2 (g := 1) (by simpa using hf n)
  have hs : Summable fun n ↦ ‖LSeries.term f 2 n‖ :=
    hs1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  calc ‖LSeries f 2‖ = ‖∑' n, LSeries.term f 2 n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term f 2 n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, ‖LSeries.term 1 (2 : ℂ) n‖ := hs.tsum_le_tsum hb hs1
    _ = π ^ 2 / 6 := tsum_norm_term_one_two

lemma pi_sq_div_six_lt_two : π ^ 2 / 6 < 2 := by
  have := Real.pi_lt_d2
  have := Real.pi_pos
  nlinarith

/-- `‖L(2, χ)‖ ≥ 6/π²`. -/
lemma norm_LFunction_two_ge {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    6 / π ^ 2 ≤ ‖DirichletCharacter.LFunction χ 2‖ := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have h := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hb : ‖LSeries (↗χ * ↗μ) 2‖ ≤ π ^ 2 / 6 := by
    refine norm_LSeries_le_zeta_two (fun n ↦ ?_)
    simp only [Pi.mul_apply, norm_mul]
    have h1 := χ.norm_le_one n
    have h2 : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    nlinarith [norm_nonneg (χ n), norm_nonneg ((μ n : ℤ) : ℂ)]
  have hprod : ‖LSeries ↗χ 2‖ * ‖LSeries (↗χ * ↗μ) 2‖ = 1 := by
    rw [← norm_mul, h, norm_one]
  have hpi : 0 < π ^ 2 := by positivity
  rw [div_le_iff₀ hpi]
  nlinarith [norm_nonneg (LSeries ↗χ 2)]

lemma Fq_two_ge (χ₁ χ₂ : DirichletCharacter ℂ N) : 1 / 4 ≤ ‖Fq χ₁ χ₂ 2‖ := by
  have hz : ‖riemannZeta 2‖ = π ^ 2 / 6 := by
    rw [riemannZeta_two, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    simp
  have a1 := norm_LFunction_two_ge χ₁
  have a2 := norm_LFunction_two_ge χ₂
  have a3 := norm_LFunction_two_ge (χ₁ * χ₂)
  simp only [Fq, norm_mul, hz]
  have hpi : 0 < π ^ 2 := by positivity
  have hlt := pi_sq_div_six_lt_two
  set x := 6 / π ^ 2 with hx
  have hx0 : 0 < x := by positivity
  have hxy : π ^ 2 / 6 = 1 / x := by rw [hx]; field_simp
  rw [hxy]
  have hx2 : 1 / 2 ≤ x := by
    rw [hx, le_div_iff₀ hpi]; linarith
  calc 1 / 4 ≤ 1 / x * x ^ 3 := by
        rw [show 1 / x * x ^ 3 = x ^ 2 by field_simp]
        nlinarith
    _ ≤ 1 / x * ‖DirichletCharacter.LFunction χ₁ 2‖ * ‖DirichletCharacter.LFunction χ₂ 2‖ *
          ‖DirichletCharacter.LFunction (χ₁ * χ₂) 2‖ := by
        have h3 : x * x * x ≤ ‖DirichletCharacter.LFunction χ₁ 2‖ *
            ‖DirichletCharacter.LFunction χ₂ 2‖ * ‖DirichletCharacter.LFunction (χ₁ * χ₂) 2‖ :=
          mul_le_mul (mul_le_mul a1 a2 hx0.le (norm_nonneg _)) a3 hx0.le
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        rw [pow_three, mul_assoc (1 / x), mul_assoc (1 / x), ← mul_assoc x x x]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)

lemma sphere_facts {s : ℂ} (hs : s ∈ sphere (2 : ℂ) (3 / 2)) :
    s ≠ 1 ∧ 1 / 2 ≤ ‖s - 1‖ ∧ 1 / 2 ≤ s.re ∧ ‖s‖ ≤ 7 / 2 := by
  rw [mem_sphere, dist_eq_norm] at hs
  have h1 : 1 / 2 ≤ ‖s - 1‖ := by
    have := norm_sub_norm_le (s - 2) (s - 1)
    rw [show s - 2 - (s - 1) = -1 by ring, norm_neg, norm_one, hs] at this
    linarith
  refine ⟨fun h ↦ ?_, h1, ?_, ?_⟩
  · rw [h] at h1; simp at h1; linarith
  · have := (Complex.abs_re_le_norm (s - 2)).trans hs.le
    rw [sub_re] at this
    have h2 : (2 : ℂ).re = 2 := by norm_num
    rw [h2] at this
    linarith [(abs_le.mp this).1]
  · calc ‖s‖ = ‖(s - 2) + 2‖ := by ring_nf
      _ ≤ ‖s - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ = 7 / 2 := by rw [hs]; norm_num

/-- `‖G‖ ≤ C N³` on the circle `|s - 2| = 3/2`. -/
theorem norm_Gq_sphere_le : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
    (χ₁ χ₂ : DirichletCharacter ℂ N), χ₁ ≠ 1 → χ₂ ≠ 1 → χ₁ * χ₂ ≠ 1 →
      ∀ s ∈ sphere (2 : ℂ) (3 / 2), ‖Gq χ₁ χ₂ s‖ ≤ C * (N : ℝ) ^ 3 := by
  have hcont : ContinuousOn riemannZeta (sphere (2 : ℂ) (3 / 2)) := fun s hs ↦
    (differentiableAt_riemannZeta (sphere_facts hs).1).continuousAt.continuousWithinAt
  obtain ⟨Cz, hCz⟩ := (isCompact_sphere (2 : ℂ) (3 / 2)).exists_bound_of_continuousOn hcont
  refine ⟨343 * max Cz 0 + 2, by positivity, fun N _ χ₁ χ₂ h1 h2 h12 s hs ↦ ?_⟩
  obtain ⟨hs1, hsd, hsre, hsn⟩ := sphere_facts hs
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hL : ∀ ψ : DirichletCharacter ℂ N, ψ ≠ 1 →
      ‖DirichletCharacter.LFunction ψ s‖ ≤ 7 * N := by
    intro ψ hψ
    have := norm_LFunction_le hψ (s := s) (by linarith)
    calc _ ≤ N * ‖s‖ / s.re := this
      _ ≤ N * (7 / 2) / (1 / 2) := by
          apply div_le_div₀ (by positivity) (by gcongr) (by norm_num) hsre
      _ = 7 * N := by ring
  have hL1 : ∀ ψ : DirichletCharacter ℂ N, ψ ≠ 1 →
      ‖DirichletCharacter.LFunction ψ 1‖ ≤ N := by
    intro ψ hψ
    have := norm_LFunction_le hψ (s := 1) (by norm_num)
    simpa using this
  rw [Gq_eq χ₁ χ₂ hs1]
  have hF : ‖Fq χ₁ χ₂ s‖ ≤ max Cz 0 * (7 * N) ^ 3 := by
    simp only [Fq, norm_mul]
    have hz := (hCz s hs).trans (le_max_left Cz 0)
    calc ‖riemannZeta s‖ * ‖DirichletCharacter.LFunction χ₁ s‖ *
          ‖DirichletCharacter.LFunction χ₂ s‖ * ‖DirichletCharacter.LFunction (χ₁ * χ₂) s‖
        ≤ max Cz 0 * (7 * N) * (7 * N) * (7 * N) := by
          gcongr
          · exact hL χ₁ h1
          · exact hL χ₂ h2
          · exact hL _ h12
      _ = _ := by ring
  have hP : ‖Pq χ₁ χ₂ 1‖ ≤ (N : ℝ) ^ 3 := by
    simp only [Pq, norm_mul]
    calc _ ≤ (N : ℝ) * N * N := by
          gcongr
          · exact hL1 χ₁ h1
          · exact hL1 χ₂ h2
          · exact hL1 _ h12
      _ = _ := by ring
  have hpos : 0 < ‖s - 1‖ := by linarith
  have hQ : ‖Pq χ₁ χ₂ 1 / (s - 1)‖ ≤ 2 * (N : ℝ) ^ 3 := by
    rw [norm_div, div_le_iff₀ hpos]
    nlinarith [norm_nonneg (Pq χ₁ χ₂ 1)]
  calc ‖Fq χ₁ χ₂ s - Pq χ₁ χ₂ 1 / (s - 1)‖
      ≤ ‖Fq χ₁ χ₂ s‖ + ‖Pq χ₁ χ₂ 1 / (s - 1)‖ := norm_sub_le _ _
    _ ≤ max Cz 0 * (7 * N) ^ 3 + 2 * (N : ℝ) ^ 3 := add_le_add hF hQ
    _ = (343 * max Cz 0 + 2) * (N : ℝ) ^ 3 := by ring

/-- Cauchy's estimate for the Taylor coefficients of `G` at `2`. -/
lemma norm_iteratedDeriv_Gq_le {C : ℝ} {χ₁ χ₂ : DirichletCharacter ℂ N} (h1 : χ₁ ≠ 1)
    (h2 : χ₂ ≠ 1) (h12 : χ₁ * χ₂ ≠ 1)
    (hC : ∀ s ∈ sphere (2 : ℂ) (3 / 2), ‖Gq χ₁ χ₂ s‖ ≤ C * (N : ℝ) ^ 3) (m : ℕ) :
    ‖iteratedDeriv m (Gq χ₁ χ₂) 2‖ ≤ m ! * (C * (N : ℝ) ^ 3) / (3 / 2) ^ m :=
  Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m (by norm_num)
    (Gq_differentiable h1 h2 h12).diffContOnCl hC

end LeanLab.PNTPort.DirichletZF

