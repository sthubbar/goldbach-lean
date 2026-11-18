module

public import LeanLab.PNTPort.DirichletZF.ThreeFourOne
public import LeanLab.PNTPort.DirichletZF.LogDeriv

/-!
# A zero-free region for `L(s, χ)`, `χ` not real, uniform in the modulus

Lab proof, unit U-5110. AI wrote this file. Known mathematics, the classical
de la Vallee Poussin region for complex characters, no cited input. It uses
`ShiftZeroBound`, `-ζ'/ζ(1 + d) ≤ 1/d + C`, from the ported StrongPNT file, Apache-2.0,
the PrimeNumberTheoremAnd contributors.

* `principal_bound`: `-Re L'/L(1 + d, χ₀) ≤ 1/d + A` for `0 < d < 1`, every modulus `N`;
* `zero_free_complex`: there is an absolute `c > 0` such that for every `N ≥ 1`, every
  Dirichlet character `χ` mod `N` with `χ² ≠ 1`, and every zero `β + iγ` of `L(s, χ)`,
  `β ≤ 1 - c / log(2NZ(|γ| + 3))`, `Z = ∑ n^{-3/2}`.
Real characters, the exceptional zero and Siegel's theorem are not covered here.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter
open scoped LSeries.notation

lemma neg_logDeriv_eq_LSeries {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction ψ) s / DirichletCharacter.LFunction ψ s =
      LSeries (↗ψ * ↗ArithmeticFunction.vonMangoldt) s := by
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq ψ hs,
    DirichletCharacter.LFunction_eq_LSeries ψ hs]
  congr 2
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  exact DirichletCharacter.LFunction_eq_LSeries ψ hz

/-- Termwise, twisting by the principal character only drops nonnegative terms. -/
lemma term_principal_le {N : ℕ} (σ : ℝ) (n : ℕ) :
    (LSeries.term (↗(1 : DirichletCharacter ℂ N) * ↗ArithmeticFunction.vonMangoldt) σ n).re ≤
      (LSeries.term ↗ArithmeticFunction.vonMangoldt σ n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [LSeries.term_of_ne_zero hn, Pi.mul_apply]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e1 : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
  rw [e1]
  have ha : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn0 σ
  have hL : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have r2 : ((ArithmeticFunction.vonMangoldt n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)).re =
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
    rw [← Complex.ofReal_div, Complex.ofReal_re]
  rw [r2]
  by_cases hu : IsUnit (n : ZMod N)
  · have h1 : (1 : DirichletCharacter ℂ N) n = 1 := by simp [MulChar.one_apply hu]
    rw [h1, one_mul, r2]
  · have h0 : (1 : DirichletCharacter ℂ N) n = 0 := MulChar.map_nonunit _ hu
    rw [h0, zero_mul, zero_div, zero_re]
    exact div_nonneg hL ha.le

/-- `-Re L'/L(1 + d, χ₀) ≤ 1/d + A`, uniformly in the modulus. -/
theorem principal_bound : ∃ A : ℝ, 1 ≤ A ∧ ∀ (N : ℕ) [NeZero N] (d : ℝ), d ∈ Ioo 0 1 →
    (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) (1 + d) /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) (1 + d)).re ≤ 1 / d + A := by
  obtain ⟨C, hC, h⟩ := ShiftZeroBound
  refine ⟨C, hC, fun N _ d hd ↦ ?_⟩
  have hs : 1 < ((1 + d : ℝ) : ℂ).re := by simp; linarith [hd.1]
  have hcast : ((1 + d : ℝ) : ℂ) = 1 + d := by push_cast; ring
  have e := neg_logDeriv_eq_LSeries (1 : DirichletCharacter ℂ N) hs
  rw [hcast] at e
  rw [e]
  have hz := h d hd
  have hζ : LSeries ↗ArithmeticFunction.vonMangoldt ((1 + d : ℝ) : ℂ) =
      -deriv riemannZeta (1 + d) / riemannZeta (1 + d) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, hcast]
  have s1 : LSeriesSummable (↗(1 : DirichletCharacter ℂ N) * ↗ArithmeticFunction.vonMangoldt)
      ((1 + d : ℝ) : ℂ) := DirichletCharacter.LSeriesSummable_twist_vonMangoldt _ hs
  have s2 : LSeriesSummable ↗ArithmeticFunction.vonMangoldt ((1 + d : ℝ) : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hle : (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗ArithmeticFunction.vonMangoldt)
      ((1 + d : ℝ) : ℂ)).re ≤ (LSeries ↗ArithmeticFunction.vonMangoldt ((1 + d : ℝ) : ℂ)).re := by
    simp only [LSeries]
    rw [Complex.re_tsum s1, Complex.re_tsum s2]
    exact (Complex.reCLM.summable s1).tsum_le_tsum (fun n ↦ term_principal_le (1 + d) n)
      (Complex.reCLM.summable s2)
  rw [hζ, hcast] at hle
  rw [neg_div, neg_re] at hle
  linarith

lemma neg_div_re_eq (a b : ℂ) : (-a / b).re = -(a / b).re := by rw [neg_div, neg_re]

lemma log_Bt_two_mul_le {N : ℕ} [NeZero N] (t : ℝ) :
    Real.log (Bt N (2 * t)) ≤ 2 * Real.log (Bt N t) := by
  have h1 := one_lt_Bt (N := N) t
  have hB2 : Bt N (2 * t) ≤ 2 * Bt N t := by
    unfold Bt
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hZ := Z_pos
    rw [abs_mul, abs_two]
    have : 2 * |t| + 3 ≤ 2 * (|t| + 3) := by linarith
    have hNZ : 0 ≤ 2 * (N : ℝ) * Z := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hNZ]
  have h6 : 2 ≤ Bt N t := by
    unfold Bt
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    have hZ := one_le_Z
    have ht := abs_nonneg t
    have : (6 : ℝ) ≤ 2 * N * (|t| + 3) := by nlinarith
    nlinarith
  calc Real.log (Bt N (2 * t)) ≤ Real.log (2 * Bt N t) :=
        Real.log_le_log (by linarith [one_lt_Bt (N := N) (2 * t)]) hB2
    _ = Real.log 2 + Real.log (Bt N t) := Real.log_mul (by norm_num) (by linarith)
    _ ≤ Real.log (Bt N t) + Real.log (Bt N t) := by
        gcongr
    _ = 2 * Real.log (Bt N t) := by ring

lemma one_le_log_Bt {N : ℕ} [NeZero N] (t : ℝ) : 1 ≤ Real.log (Bt N t) := by
  have h6 : Real.exp 1 ≤ Bt N t := by
    unfold Bt
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    have hZ := one_le_Z
    have ht := abs_nonneg t
    have : (6 : ℝ) ≤ 2 * N * (|t| + 3) := by nlinarith
    have he := Real.exp_one_lt_d9
    nlinarith
  rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])]
  exact h6

/-- The zero-free region for Dirichlet characters with `χ² ≠ 1`, uniform in the modulus. -/
theorem zero_free_complex : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ^ 2 ≠ 1 → ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
      ρ.re ≤ 1 - c / Real.log (Bt N ρ.im) := by
  obtain ⟨A, hA, hprin⟩ := principal_bound
  set M : ℝ := 6 * K0 + 3 * A + 16 with hM
  have hK := K0_pos
  have hMpos : 1 < M := by rw [hM]; linarith
  refine ⟨3 / (52 * M), by positivity, fun N _ χ hχ2 ρ hρ ↦ ?_⟩
  have hχ : χ ≠ 1 := by rintro rfl; exact hχ2 (one_pow 2)
  set t := ρ.im with ht
  set Lg := Real.log (Bt N t) with hLg
  have hL1 : 1 ≤ Lg := one_le_log_Bt t
  set D := M * Lg with hD
  have hD1 : 1 < D := by rw [hD]; nlinarith
  set d : ℝ := 1 / (4 * D) with hd
  have hd0 : d ∈ Ioo 0 1 := by
    rw [hd]; constructor
    · positivity
    · rw [div_lt_one (by linarith)]; linarith
  have hβ1 : ρ.re < 1 := by
    by_contra hc; push Not at hc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hc hρ
  have hpos : 0 < 1 + d - ρ.re := by linarith [hd0.1]
  -- the three bounds
  have b0 := hprin N d hd0
  have b1 := shiftOne_bound hχ hd0 hρ
  have b2 := shiftAny_bound (by exact hχ2 : χ ^ 2 ≠ 1) (2 * t) hd0
  have hlog2 := log_Bt_two_mul_le (N := N) t
  have key := three_four_one χ (show 1 < 1 + d by linarith [hd0.1]) t
  simp only [Complex.ofReal_add, Complex.ofReal_one] at key
  have c1 : (1 : ℂ) + d + t * I = 1 + d + I * t := by ring
  have c2 : (1 : ℂ) + d + 2 * t * I = 1 + d + I * ((2 * t : ℝ) : ℂ) := by push_cast; ring
  rw [c1, c2] at key
  simp only [neg_div_re_eq] at key b0
  rw [← ht] at b1
  rw [← hLg] at b1 hlog2
  -- combine: `4/(1 + d - β) ≤ 3/d + M Lg`
  have hcomb : 4 / (1 + d - ρ.re) ≤ 3 / d + D := by
    have hKL : 0 ≤ K0 * Lg := mul_nonneg hK.le (by linarith)
    have e4 : 4 / (1 + d - ρ.re) = 4 * (1 / (1 + d - ρ.re)) := by ring
    have e3 : 3 / d = 3 * (1 / d) := by ring
    have hA' : A ≤ A * Lg := le_mul_of_one_le_right (by linarith) hL1
    have h2 := mul_le_mul_of_nonneg_left hlog2 hK.le
    rw [e4, e3, hD, hM]
    nlinarith
  have h3d : 3 / d = 12 * D := by rw [hd]; field_simp; ring
  rw [h3d] at hcomb
  have h13 : 4 ≤ 13 * D * (1 + d - ρ.re) := by
    rw [div_le_iff₀ hpos] at hcomb; linarith
  -- so `β ≤ 1 + d - 4/(13 D) = 1 - (3/52)/D`
  have hfinal : ρ.re ≤ 1 - 3 / (52 * D) := by
    have hDpos : 0 < D := by linarith
    have : 4 / (13 * D) ≤ 1 + d - ρ.re := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have e : 1 + d - 4 / (13 * D) = 1 - 3 / (52 * D) := by
      rw [hd]; field_simp; ring
    linarith
  have e : 3 / (52 * M) / Lg = 3 / (52 * D) := by
    rw [hD]; field_simp
  rw [e]; exact hfinal

end LeanLab.PNTPort.DirichletZF

