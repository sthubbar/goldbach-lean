module

public import LeanLab.HardyLittlewood1923.U1503Contour
public import LeanLab.HardyLittlewood1923.U1503LogDeriv
public import LeanLab.HardyLittlewood1923.U1473Explicit
public import LeanLab.PNTPort.PsiChi.Unsmooth
public import LeanLab.PNTPort.PsiChi.Assembly

/-!
AI-written Lean code, Claude, 2026-10-23, CLOUD run 20261023T1343Z-19109, unit U-1503, paper P0004.

# `ψ(x, χ)` from a zero-free half plane, without a cited explicit formula

Known mathematics, Davenport ch. 17 to 20, no cited input. The route avoids the truncated
explicit formula with a sum over zeros: on Hypothesis R at level `Θ`, the contour of the smoothed
`ψ(x, χ)` is moved to `Re s = Θ + 1/log x`, where no zero lies, and `L'/L` is bounded there by
the local Borel-Caratheodory bound of U1503LogDeriv, since every zero is at distance at least
`1/log x`. The cost is one more `log x` than the printed `(log x)²`.

* `logDeriv_region`: on `NoZerosRightPrim Θ`, for primitive `χ` mod `q`, `σ ≥ Θ + η`,
  `1/2 ≤ σ ≤ 2`, `s = σ + it ≠ 1`:
  `‖L'/L(s, χ)‖ ≤ (K + 1/(l η)) log (60 q (|t| + 4)² Z) + ‖s - 1‖⁻¹`.
* `psi_sub_le`: `ψ(b) - ψ(a) ≤ (b - a + 1) log b`.
* `PsiChiPrimBound3 Θ`: U-1473's `PsiChiPrimBound Θ` with `(log x)³` in place of `(log x)²`.
* `psiChiPrimBound3_of_noZeros`: for `1/2 ≤ Θ < 1`, `NoZerosRightPrim Θ → PsiChiPrimBound3 Θ`.
* `psiChiPrimBound_of_noZeros`: for `1/2 ≤ Θ < 1` and every `Θ' > Θ`,
  `NoZerosRightPrim Θ → PsiChiPrimBound Θ'`.
-/

@[expose] public section

set_option lang.lemmaCmd true

open Set Function Filter Complex Real MeasureTheory

open ArithmeticFunction (vonMangoldt)

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

namespace LeanLab.HardyLittlewood1923.U1503

open LeanLab.HardyLittlewood1923.U1473 (NoZerosRightPrim PsiChiPrimBound)
open LeanLab.PNTPort.DirichletZF (Z Z_pos one_le_Z)
open LeanLab.PNTPort.DirichletZF.U1482 (gZ gZ_of_ne gZ_one cen)
open LeanLab.PNTPort.BV (psiChi)

lemma ne_one_of_primitive {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) : χ ≠ 1 := by
  rintro rfl
  apply hq
  have h1 : (1 : DirichletCharacter ℂ q).conductor = 1 := DirichletCharacter.conductor_one
  unfold DirichletCharacter.IsPrimitive at hχ
  rw [h1] at hχ
  exact hχ.symm

/-- **`L'/L` right of the zeros.** -/
theorem logDeriv_region {Θ : ℝ} (hZ : NoZerosRightPrim Θ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {η σ t : ℝ} (hη : 0 < η)
    (hσ : Θ + η ≤ σ) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (hs1 : (σ : ℂ) + t * I ≠ 1) :
    ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ ≤
      (KW + 1 / (lZ * η)) * Real.log (60 * q * (|t| + 4) ^ 2 * Z) +
        ‖(σ : ℂ) + t * I - 1‖⁻¹ := by
  have hsre : ((σ : ℂ) + t * I).re = σ := by simp
  have hsc : ‖((σ : ℂ) + t * I) - cen t‖ ≤ 29 / 20 * (7 / 10) := by
    have e : ((σ : ℂ) + t * I) - cen t = ((σ - 3 / 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [cen]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have hdist : ∀ ρ : ℂ, ρ.re ≤ Θ → η ≤ ‖((σ : ℂ) + t * I) - ρ‖ := by
    intro ρ hρ
    have h1 : (((σ : ℂ) + t * I) - ρ).re ≤ ‖((σ : ℂ) + t * I) - ρ‖ := Complex.re_le_norm _
    have h2 : (((σ : ℂ) + t * I) - ρ).re = σ - ρ.re := by simp
    linarith
  have hZχ : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ ≠ 1 → ρ.re ≤ Θ := by
    intro ρ hρ h1
    by_contra hc
    push Not at hc
    exact hZ q χ hχ ρ hc h1 hρ
  have hLs : DirichletCharacter.LFunction χ ((σ : ℂ) + t * I) ≠ 0 :=
    hZ q χ hχ _ (by rw [hsre]; linarith) hs1
  have hinv0 : 0 ≤ ‖(σ : ℂ) + t * I - 1‖⁻¹ := by positivity
  have hK0 : 0 ≤ KW + 1 / (lZ * η) := by
    have := KW_pos; have := lZ_pos; positivity
  by_cases hq : q = 1
  · subst hq
    have hL : DirichletCharacter.LFunction χ = riemannZeta :=
      DirichletCharacter.LFunction_modOne_eq
    rw [hL] at hLs ⊢
    have hgs : gZ ((σ : ℂ) + t * I) ≠ 0 := by
      rw [gZ_of_ne hs1]; exact mul_ne_zero (sub_ne_zero.mpr hs1) hLs
    have hd : ∀ ρ : ℂ, gZ ρ = 0 → ‖ρ - cen t‖ ≤ 29 / 20 * (4 / 5) →
        η ≤ ‖((σ : ℂ) + t * I) - ρ‖ := by
      intro ρ hρ _
      have hρ1 : ρ ≠ 1 := by
        rintro rfl; rw [gZ_one] at hρ; exact one_ne_zero hρ
      rw [gZ_of_ne hρ1] at hρ
      have hz : riemannZeta ρ = 0 := (mul_eq_zero.mp hρ).resolve_left (sub_ne_zero.mpr hρ1)
      exact hdist ρ (hZχ ρ (by rw [hL]; exact hz) hρ1)
    have hb := logDeriv_gZ_wide t hsc hgs hη hd
    rw [U1503.logDeriv_zeta_eq hs1 hLs]
    have e1 : ‖(1 : ℂ) / ((σ : ℂ) + t * I - 1)‖ = ‖(σ : ℂ) + t * I - 1‖⁻¹ := by
      rw [norm_div, norm_one, one_div]
    have e2 : (60 : ℝ) * ((1 : ℕ) : ℝ) * (|t| + 4) ^ 2 * Z = 60 * (|t| + 4) ^ 2 * Z := by
      push_cast; ring
    rw [e2]
    calc ‖deriv gZ ((σ : ℂ) + t * I) / gZ ((σ : ℂ) + t * I) - 1 / ((σ : ℂ) + t * I - 1)‖
        ≤ ‖deriv gZ ((σ : ℂ) + t * I) / gZ ((σ : ℂ) + t * I)‖ +
            ‖(1 : ℂ) / ((σ : ℂ) + t * I - 1)‖ := norm_sub_le _ _
      _ ≤ _ := by rw [e1]; linarith
  · have hχ1 := ne_one_of_primitive hχ hq
    have hd : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖ρ - cen t‖ ≤ 29 / 20 * (4 / 5) →
        η ≤ ‖((σ : ℂ) + t * I) - ρ‖ := by
      intro ρ hρ _
      have hρ1 : ρ ≠ 1 := by
        rintro rfl; exact DirichletCharacter.LFunction_apply_one_ne_zero hχ1 hρ
      exact hdist ρ (hZχ ρ hρ hρ1)
    have hb := logDeriv_L_wide hχ1 t hsc hLs hη hd
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hZ1 := one_le_Z
    have ht := abs_nonneg t
    have hmono : Real.log (20 * q * (|t| + 3) * Z) ≤ Real.log (60 * q * (|t| + 4) ^ 2 * Z) := by
      apply Real.log_le_log (by positivity)
      have h1 : (|t| + 3) ≤ (|t| + 4) ^ 2 := by nlinarith
      have hqZ : 0 ≤ (q : ℝ) * Z := by positivity
      have := mul_le_mul_of_nonneg_left h1 hqZ
      nlinarith
    calc _ ≤ (KW + 1 / (lZ * η)) * Real.log (20 * q * (|t| + 3) * Z) := hb
      _ ≤ (KW + 1 / (lZ * η)) * Real.log (60 * q * (|t| + 4) ^ 2 * Z) :=
          mul_le_mul_of_nonneg_left hmono hK0
      _ ≤ _ := le_add_of_nonneg_right hinv0

/-- `ψ(b) - ψ(a) ≤ (b - a + 1) log b` for `a ≤ b`, `1 ≤ b`. -/
lemma psi_sub_le {a b : ℝ} (hab : a ≤ b) (hb : 1 ≤ b) :
    Chebyshev.psi b - Chebyshev.psi a ≤ (b - a + 1) * Real.log b := by
  rw [LeanLab.PNTPort.PsiChi.psi_sub_eq hab]
  have hterm : ∀ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, Λ n ≤ Real.log b := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hnb : (n : ℝ) ≤ b := (Nat.le_floor_iff (by linarith)).mp hn'.2
    exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by linarith) hnb)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hb)
  have h1 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (by linarith)
  have h2 : a < ⌊a⌋₊ + 1 := Nat.lt_floor_add_one a
  have h3 : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  rw [Nat.cast_sub h3]; linarith

lemma one_lt_log_four_le {x : ℝ} (hx : 4 ≤ x) : 1 < Real.log x := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma log_le_two_log {x y : ℝ} (hx : 3 ≤ x) (hy0 : 0 < y) (hy : y ≤ 3 * x) :
    Real.log y ≤ 2 * Real.log x := by
  rw [← Real.log_rpow (by linarith)]
  apply Real.log_le_log hy0
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  nlinarith

/-- The arithmetic of the contour bound at `T = x`, `ε = x^{Θ-1}`, `σ₁ = Θ + 1/log x`. -/
lemma rhs_le {x Θ A KM : ℝ} (hx : 4 ≤ x) (hΘ : 1 / 2 ≤ Θ) (hA : 0 ≤ A) (hKM : 0 ≤ KM) :
    (Real.log x + A) * x / (x ^ (Θ - 1) * x) +
        KM * Real.log x ^ 2 * x ^ (Θ + (Real.log x)⁻¹) * Real.log (1 + x) +
        KM * Real.log x ^ 2 * x / x ≤
      ((1 + A) + 2 * Real.exp 1 * KM + KM) * (x ^ Θ * Real.log x ^ 3) := by
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := (one_lt_log_four_le hx).le
  set L := Real.log x with hLdef
  set u := x ^ Θ with hudef
  have hu1 : 1 ≤ u := Real.one_le_rpow (by linarith) (by linarith)
  have e1 : x ^ (Θ - 1) * x = u := by
    rw [Real.rpow_sub_one hx0.ne', hudef]; field_simp
  have hxu : x ≤ u * u := by
    have : u * u = x ^ (2 * Θ) := by rw [hudef, ← Real.rpow_add hx0]; ring_nf
    rw [this]
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (2 * Θ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hu0 : 0 < u := by linarith
  have t1 : (L + A) * x / (x ^ (Θ - 1) * x) ≤ (1 + A) * (u * L ^ 3) := by
    rw [e1, div_le_iff₀ hu0]
    have hL3 : L ≤ L ^ 3 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
    have hL31 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
    have hA3 : A ≤ A * L ^ 3 := le_mul_of_one_le_right hA hL31
    have hLA : L + A ≤ (1 + A) * L ^ 3 := by
      calc L + A ≤ L ^ 3 + A * L ^ 3 := add_le_add hL3 hA3
        _ = (1 + A) * L ^ 3 := by ring
    have hLA0 : 0 ≤ L + A := by linarith
    calc (L + A) * x ≤ (L + A) * (u * u) := mul_le_mul_of_nonneg_left hxu hLA0
      _ ≤ (1 + A) * L ^ 3 * (u * u) := mul_le_mul_of_nonneg_right hLA (by positivity)
      _ = (1 + A) * (u * L ^ 3) * u := by ring
  have eL : x ^ L⁻¹ = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hx0, ← hLdef, mul_inv_cancel₀ (by linarith : L ≠ 0)]
  have e2 : x ^ (Θ + L⁻¹) = u * Real.exp 1 := by
    rw [Real.rpow_add hx0, eL, hudef]
  have hl2 : Real.log (1 + x) ≤ 2 * L := log_le_two_log (by linarith) (by linarith) (by linarith)
  have t2 : KM * L ^ 2 * x ^ (Θ + L⁻¹) * Real.log (1 + x) ≤ 2 * Real.exp 1 * KM * (u * L ^ 3) := by
    rw [e2]
    have h0 : 0 ≤ KM * L ^ 2 * (u * Real.exp 1) := by positivity
    calc KM * L ^ 2 * (u * Real.exp 1) * Real.log (1 + x) ≤
          KM * L ^ 2 * (u * Real.exp 1) * (2 * L) := mul_le_mul_of_nonneg_left hl2 h0
      _ = 2 * Real.exp 1 * KM * (u * L ^ 3) := by ring
  have t3 : KM * L ^ 2 * x / x ≤ KM * (u * L ^ 3) := by
    rw [mul_div_assoc, div_self hx0.ne', mul_one]
    have h23 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
    have : L ^ 2 ≤ u * L ^ 3 := h23.trans (le_mul_of_one_le_left (by positivity) hu1)
    exact mul_le_mul_of_nonneg_left this hKM
  have := add_le_add (add_le_add t1 t2) t3
  calc _ ≤ (1 + A) * (u * L ^ 3) + 2 * Real.exp 1 * KM * (u * L ^ 3) + KM * (u * L ^ 3) := this
    _ = _ := by ring

/-- The unsmoothing error at `ε = x^{Θ-1}`. -/
lemma unsmooth_arith {x Θ : ℝ} (hx : 4 ≤ x) (hΘ : Θ < 1) (hΘ0 : 0 ≤ Θ) :
    Chebyshev.psi (x * (1 + 2 * x ^ (Θ - 1))) - Chebyshev.psi (x * (1 - x ^ (Θ - 1))) ≤
      8 * (x ^ Θ * Real.log x ^ 3) := by
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := (one_lt_log_four_le hx).le
  set u := x ^ Θ with hudef
  have hu1 : 1 ≤ u := Real.one_le_rpow (by linarith) hΘ0
  have hux : u ≤ x := by
    calc u = x ^ Θ := rfl
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hΘ.le
      _ = x := Real.rpow_one x
  have eε : x * x ^ (Θ - 1) = u := by
    rw [Real.rpow_sub_one hx0.ne', hudef]; field_simp
  have ha : x * (1 - x ^ (Θ - 1)) = x - u := by rw [mul_sub, mul_one, eε]
  have hb : x * (1 + 2 * x ^ (Θ - 1)) = x + 2 * u := by
    rw [mul_add, mul_one, ← mul_assoc, mul_comm x 2, mul_assoc, eε]
  rw [ha, hb]
  refine (psi_sub_le (by linarith) (by linarith)).trans ?_
  have hl : Real.log (x + 2 * u) ≤ 2 * Real.log x :=
    log_le_two_log (by linarith) (by linarith) (by linarith)
  have hL3 : Real.log x ≤ Real.log x ^ 3 := by
    calc Real.log x = Real.log x ^ 1 := (pow_one _).symm
      _ ≤ Real.log x ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL0 : 0 ≤ Real.log x := by linarith
  calc (x + 2 * u - (x - u) + 1) * Real.log (x + 2 * u) ≤ (3 * u + 1) * (2 * Real.log x) := by
        have : x + 2 * u - (x - u) + 1 = 3 * u + 1 := by ring
        rw [this]; exact mul_le_mul_of_nonneg_left hl (by linarith)
    _ ≤ 8 * (u * Real.log x) := by
        have := mul_le_mul_of_nonneg_right hu1 hL0
        nlinarith
    _ ≤ 8 * (u * Real.log x ^ 3) := by
        have := mul_le_mul_of_nonneg_left hL3 (by linarith : (0 : ℝ) ≤ u); linarith

/-- `ψ(x, χ)` with error `C x^Θ (log x)³`. -/
def PsiChiPrimBound3 (Θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → χ.IsPrimitive →
    ∀ x : ℝ, 2 ≤ x → (q : ℝ) ≤ x →
      ‖psiChi x χ - (if q = 1 then (x : ℂ) else 0)‖ ≤ C * x ^ Θ * Real.log x ^ 3

/-- The edge bound for `L'/L` at `T = x`, `σ₁ = Θ + 1/log x`, used on the left edge and the two
horizontal edges. -/
lemma edge_M {Θ : ℝ} (hZ : NoZerosRightPrim Θ) (h0 : 1 / 2 ≤ Θ) (h1 : Θ < 1) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {x : ℝ} (hx : 4 ≤ x) (hqx : (q : ℝ) ≤ x)
    (σ t : ℝ) (hσ1 : Θ + (Real.log x)⁻¹ ≤ σ)
    (hσ2 : σ ≤ 1 + (Real.log x)⁻¹) (ht : |t| ≤ x) (hd : (1 - Θ) / 2 ≤ ‖(σ : ℂ) + t * I - 1‖) :
    ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ ≤
      ((KW + 1 / lZ) * (Real.log (240 * Z) + 3) + 2 / (1 - Θ)) * Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hL1 : 1 < Real.log x := one_lt_log_four_le hx
  have hη : 0 < (Real.log x)⁻¹ := by positivity
  have hη1 : (Real.log x)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL1
  have hdpos : 0 < (1 - Θ) / 2 := by linarith
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hd; linarith
  have hb := logDeriv_region hZ hχ hη hσ1 (by linarith) (by linarith) hs1
  set L := Real.log x with hLdef
  have hlZ := lZ_pos
  have hKW := KW_pos
  have hZ1 := one_le_Z
  have e1 : KW + 1 / (lZ * L⁻¹) = KW + L / lZ := by field_simp
  rw [e1] at hb
  have hL0 : 0 ≤ L := by linarith
  have hcoef : KW + L / lZ ≤ (KW + 1 / lZ) * L := by
    have h1 : KW ≤ KW * L := le_mul_of_one_le_right hKW.le hL1.le
    have h2 : L / lZ = 1 / lZ * L := by ring
    calc KW + L / lZ ≤ KW * L + 1 / lZ * L := by rw [h2]; linarith
      _ = (KW + 1 / lZ) * L := by ring
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog : Real.log (60 * q * (|t| + 4) ^ 2 * Z) ≤ (Real.log (240 * Z) + 3) * L := by
    have h4 : |t| + 4 ≤ 2 * x := by linarith
    have hpos : 0 < 60 * (q : ℝ) * (|t| + 4) ^ 2 * Z := by positivity
    have hle : 60 * (q : ℝ) * (|t| + 4) ^ 2 * Z ≤ 240 * Z * x ^ 3 := by
      have hsq : (|t| + 4) ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
      have hZ0 : 0 ≤ Z := by linarith
      have : 60 * (q : ℝ) * (|t| + 4) ^ 2 ≤ 60 * x * (2 * x) ^ 2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hqx (by norm_num)) hsq (by positivity)
          (by positivity)
      calc 60 * (q : ℝ) * (|t| + 4) ^ 2 * Z ≤ 60 * x * (2 * x) ^ 2 * Z :=
            mul_le_mul_of_nonneg_right this hZ0
        _ = 240 * Z * x ^ 3 := by ring
    have hl240 : 0 ≤ Real.log (240 * Z) := Real.log_nonneg (by linarith)
    calc Real.log (60 * q * (|t| + 4) ^ 2 * Z) ≤ Real.log (240 * Z * x ^ 3) :=
          Real.log_le_log hpos hle
      _ = Real.log (240 * Z) + 3 * L := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ (Real.log (240 * Z) + 3) * L := by
          have := mul_le_mul_of_nonneg_left hL1.le hl240
          nlinarith
  have hinv : ‖(σ : ℂ) + t * I - 1‖⁻¹ ≤ 2 / (1 - Θ) := by
    rw [inv_le_comm₀ (by linarith) (by positivity)]
    calc (2 / (1 - Θ))⁻¹ = (1 - Θ) / 2 := by rw [inv_div]
      _ ≤ _ := hd
  have hlog0 : 0 ≤ Real.log (60 * q * (|t| + 4) ^ 2 * Z) := by
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ (|t| + 4) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg t])
    have h2 : (1 : ℝ) ≤ 60 * q := by linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h2 h1) hZ1
  have hc0 : 0 ≤ KW + L / lZ := by positivity
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1.le
  calc _ ≤ (KW + L / lZ) * Real.log (60 * q * (|t| + 4) ^ 2 * Z) + ‖(σ : ℂ) + t * I - 1‖⁻¹ := hb
    _ ≤ ((KW + 1 / lZ) * L) * ((Real.log (240 * Z) + 3) * L) + 2 / (1 - Θ) := by
        gcongr
    _ ≤ ((KW + 1 / lZ) * (Real.log (240 * Z) + 3) + 2 / (1 - Θ)) * L ^ 2 := by
        have h2 : 0 ≤ 2 / (1 - Θ) := div_nonneg (by norm_num) (by linarith)
        have := mul_le_mul_of_nonneg_left hL2 h2
        nlinarith

set_option maxHeartbeats 4000000 in
/-- **Hypothesis R at level `Θ ∈ [1/2, 1)` gives `ψ(x, χ) - [q = 1] x ≪ x^Θ (log x)³`**, for
every primitive `χ` mod `q ≤ x`, uniformly. -/
theorem psiChiPrimBound3_of_noZeros {Θ : ℝ} (h0 : 1 / 2 ≤ Θ) (h1 : Θ < 1)
    (hZ : NoZerosRightPrim Θ) : PsiChiPrimBound3 Θ := by
  obtain ⟨ν, hν, hν0, hνs, hνm⟩ := SmoothExistence
  have hν1 : ContDiff ℝ 1 ν := hν.of_le (by simp)
  have hνpos : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ hν0 x
  have hνm' : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← MeasureTheory.integral_Ici_eq_integral_Ioi]
  obtain ⟨Ci, hCi, hcont⟩ := contour_bound_inv hν1 hνpos hνs hνm'
  obtain ⟨Cz, hCz, hcontz⟩ := contour_bound_zeta hν1 hνpos hνs hνm'
  obtain ⟨A, hA, hright⟩ := LeanLab.PNTPort.PsiChi.logDeriv_right_le
  obtain ⟨ε₀, cM, hε₀, hcM, hmel⟩ := MellinOfSmooth1cExplicit hν1 hνs hνm'
  obtain ⟨C1, hC1, hone⟩ := U1473.psiChiPrimBound_one
  have hlZ := lZ_pos
  have hKW := KW_pos
  have hZ1 := one_le_Z
  have hAnn : 0 ≤ A := by linarith
  have hΘ1 : 0 < 1 - Θ := by linarith
  set KM := (KW + 1 / lZ) * (Real.log (240 * Z) + 3) + 2 / (1 - Θ) with hKMdef
  have hKM : 0 ≤ KM := by
    have : 0 ≤ Real.log (240 * Z) := Real.log_nonneg (by linarith)
    positivity
  set K' := (1 + A) + 2 * Real.exp 1 * KM + KM with hK'def
  have hK' : 0 ≤ K' := by positivity
  set Cbig := max Ci Cz * K' + 8 + cM with hCbig
  have hCbig0 : 0 ≤ Cbig := by positivity
  -- the threshold
  have hev : ∀ᶠ x : ℝ in atTop,
      4 ≤ x ∧ 2 / (1 - Θ) ≤ Real.log x ∧ x ^ (Θ - 1) < min ε₀ 1 := by
    refine (eventually_ge_atTop 4).and ((Real.tendsto_log_atTop.eventually_ge_atTop _).and ?_)
    have ht := tendsto_rpow_neg_atTop (y := 1 - Θ) hΘ1
    have hlt := ht.eventually (gt_mem_nhds (lt_min hε₀ one_pos))
    filter_upwards [hlt] with x hx
    rwa [neg_sub] at hx
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hev
  set X₁ := max X₀ 4 with hX₁
  have hX₁4 : 4 ≤ X₁ := le_max_right _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Csmall := C1 * X₁ ^ (1 - Θ) / Real.log 2 with hCsmall
  have hCsmall0 : 0 ≤ Csmall := by
    have : 0 ≤ X₁ ^ (1 - Θ) := by positivity
    positivity
  refine ⟨Cbig + Csmall, by positivity, fun q χ hq hχ x hx hqx ↦ ?_⟩
  have : NeZero q := ⟨by omega⟩
  have hx0 : 0 < x := by linarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx0 : 0 ≤ Real.log x := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hW0 : 0 ≤ x ^ Θ * Real.log x ^ 3 := by positivity
  by_cases hsmall : x < X₁
  · -- small `x`: Chebyshev
    have hb := hone q χ hq hχ x hx hqx
    have hpow : x ^ (1 : ℝ) ≤ X₁ ^ (1 - Θ) * x ^ Θ := by
      have e : x ^ (1 : ℝ) = x ^ (1 - Θ) * x ^ Θ := by
        rw [← Real.rpow_add hx0]; ring_nf
      rw [e]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hx0.le hsmall.le (by linarith)) (by positivity)
    have hlog : Real.log x ^ 2 ≤ Real.log x ^ 3 / Real.log 2 := by
      rw [le_div_iff₀ hl2]
      have : 0 ≤ Real.log x ^ 2 := sq_nonneg _
      nlinarith
    have hS : C1 * x ^ (1 : ℝ) * Real.log x ^ 2 ≤ Csmall * x ^ Θ * Real.log x ^ 3 := by
      rw [hCsmall]
      have hL2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
      calc C1 * x ^ (1 : ℝ) * Real.log x ^ 2 ≤ C1 * (X₁ ^ (1 - Θ) * x ^ Θ) *
            (Real.log x ^ 3 / Real.log 2) := by gcongr
        _ = C1 * X₁ ^ (1 - Θ) / Real.log 2 * x ^ Θ * Real.log x ^ 3 := by ring
    have : 0 ≤ Cbig * x ^ Θ * Real.log x ^ 3 := by positivity
    calc _ ≤ _ := hb.trans hS
      _ ≤ (Cbig + Csmall) * x ^ Θ * Real.log x ^ 3 := by nlinarith
  -- large `x`
  push Not at hsmall
  obtain ⟨hx4, hxΘ, hxε⟩ := hX₀ x (le_trans (le_max_left _ _) hsmall)
  have hL1 : 1 < Real.log x := one_lt_log_four_le hx4
  have hη : 0 < (Real.log x)⁻¹ := by positivity
  have hη1 : (Real.log x)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL1
  have hηΘ : (Real.log x)⁻¹ ≤ (1 - Θ) / 2 := by
    rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]; exact hxΘ
  have hεpos : 0 < x ^ (Θ - 1) := by positivity
  have hε1 : x ^ (Θ - 1) < 1 := lt_of_lt_of_le hxε (min_le_right _ _)
  have hεε₀ : x ^ (Θ - 1) < ε₀ := lt_of_lt_of_le hxε (min_le_left _ _)
  have hσ₁1 : Θ + (Real.log x)⁻¹ < 1 := by linarith
  have hσ₁h : 1 / 2 ≤ Θ + (Real.log x)⁻¹ := by linarith
  have hM₀ : ∀ t : ℝ, ‖deriv (DirichletCharacter.LFunction χ)
      (((1 + (Real.log x)⁻¹ : ℝ) : ℂ) + t * I) /
        DirichletCharacter.LFunction χ (((1 + (Real.log x)⁻¹ : ℝ) : ℂ) + t * I)‖ ≤
        Real.log x + A := by
    intro t
    have := hright q χ (Real.log x)⁻¹ t ⟨hη, hη1⟩
    rwa [one_div, inv_inv] at this
  have hM0 : 0 ≤ KM * Real.log x ^ 2 := by positivity
  have hleft : ∀ t : ℝ, |t| ≤ x →
      ‖deriv (DirichletCharacter.LFunction χ) (((Θ + (Real.log x)⁻¹ : ℝ) : ℂ) + t * I) /
        DirichletCharacter.LFunction χ (((Θ + (Real.log x)⁻¹ : ℝ) : ℂ) + t * I)‖ ≤
        KM * Real.log x ^ 2 := by
    intro t ht
    refine edge_M hZ h0 h1 hχ hx4 hqx _ t le_rfl (by linarith) ht ?_
    have h := Complex.abs_re_le_norm (((Θ + (Real.log x)⁻¹ : ℝ) : ℂ) + t * I - 1)
    have e : (((Θ + (Real.log x)⁻¹ : ℝ) : ℂ) + t * I - 1).re = Θ + (Real.log x)⁻¹ - 1 := by simp
    rw [e, abs_of_neg (by linarith)] at h
    linarith
  have hhor : ∀ σ : ℝ, Θ + (Real.log x)⁻¹ ≤ σ → σ ≤ 1 + (Real.log x)⁻¹ →
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + x * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + x * I)‖ ≤ KM * Real.log x ^ 2 ∧
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + ((-x : ℝ) : ℂ) * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + ((-x : ℝ) : ℂ) * I)‖ ≤ KM * Real.log x ^ 2 := by
    intro σ hσa hσb
    constructor
    · refine edge_M hZ h0 h1 hχ hx4 hqx σ x hσa hσb (by rw [abs_of_pos hx0]) ?_
      have h := Complex.abs_im_le_norm ((σ : ℂ) + x * I - 1)
      have e : ((σ : ℂ) + x * I - 1).im = x := by simp
      rw [e, abs_of_pos hx0] at h
      linarith
    · refine edge_M hZ h0 h1 hχ hx4 hqx σ (-x) hσa hσb (by rw [abs_neg, abs_of_pos hx0]) ?_
      have h := Complex.abs_im_le_norm ((σ : ℂ) + ((-x : ℝ) : ℂ) * I - 1)
      have e : ((σ : ℂ) + ((-x : ℝ) : ℂ) * I - 1).im = -x := by simp
      rw [e, abs_neg, abs_of_pos hx0] at h
      linarith
  have hrhs := rhs_le hx4 h0 hA0 hKM
  -- unsmoothing
  have hun := LeanLab.PNTPort.PsiChi.unsmooth_le hνpos hνs hνm' χ hx0 hεpos hε1
  have hun2 := unsmooth_arith hx4 h1 (by linarith)
  have hun3 : ‖psiChi x χ - ∑' n : ℕ, χ (n : ZMod q) * Λ n * Smooth1 ν (x ^ (Θ - 1)) (n / x)‖ ≤
      8 * (x ^ Θ * Real.log x ^ 3) := hun.trans hun2
  have hmax : 0 ≤ max Ci Cz := le_trans hCi.le (le_max_left _ _)
  by_cases hq1 : q = 1
  · subst hq1
    have hL : DirichletCharacter.LFunction χ = riemannZeta :=
      DirichletCharacter.LFunction_modOne_eq
    rw [hL] at hM₀ hleft hhor
    have hzero : ∀ s : ℂ, Θ + (Real.log x)⁻¹ ≤ s.re → s.re ≤ 2 → |s.im| ≤ x → s ≠ 1 →
        riemannZeta s ≠ 0 := by
      intro s hs _ _ hs1
      have := hZ 1 χ hχ s (by linarith) hs1
      rwa [hL] at this
    have hc := hcontz x (x ^ (Θ - 1)) (Θ + (Real.log x)⁻¹) x (Real.log x + A)
      (KM * Real.log x ^ 2) (by linarith) hεpos hε1 hσ₁h hσ₁1 (by linarith) (by positivity) hM0
      hzero hM₀ hleft hhor
    have hSC : SmoothedChebyshev ν (x ^ (Θ - 1)) x =
        ∑' n : ℕ, χ (n : ZMod 1) * Λ n * Smooth1 ν (x ^ (Θ - 1)) (n / x) := by
      rw [← LeanLab.PNTPort.PsiChi.smoothedChebyshevChi_eq χ hν1 hνpos hνs hνm' (by linarith)
        hεpos hε1]
      unfold SmoothedChebyshev
      congr 1
      ext s
      simp only [LeanLab.PNTPort.PsiChi.SmoothedChiIntegrand, SmoothedChebyshevIntegrand, hL]
    rw [hSC] at hc
    have hmel1 := hmel (x ^ (Θ - 1)) ⟨hεpos, hεε₀⟩
    have hmain : ‖𝓜 (fun t ↦ (Smooth1 ν (x ^ (Θ - 1)) t : ℂ)) 1 * x - x‖ ≤
        cM * (x ^ Θ * Real.log x ^ 3) := by
      have e : 𝓜 (fun t ↦ (Smooth1 ν (x ^ (Θ - 1)) t : ℂ)) 1 * x - x =
          (𝓜 (fun t ↦ (Smooth1 ν (x ^ (Θ - 1)) t : ℂ)) 1 - 1) * x := by ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      have e2 : x ^ (Θ - 1) * x = x ^ Θ := by
        rw [Real.rpow_sub_one hx0.ne']; field_simp
      have hL3 : 1 ≤ Real.log x ^ 3 := one_le_pow₀ hL1.le
      calc ‖𝓜 (fun t ↦ (Smooth1 ν (x ^ (Θ - 1)) t : ℂ)) 1 - 1‖ * x ≤ cM * x ^ (Θ - 1) * x :=
            mul_le_mul_of_nonneg_right hmel1 hx0.le
        _ = cM * x ^ Θ := by rw [mul_assoc, e2]
        _ ≤ cM * (x ^ Θ * Real.log x ^ 3) := by
            apply mul_le_mul_of_nonneg_left _ hcM.le
            exact le_mul_of_one_le_right (by positivity) hL3
    have hcz : Cz * ((Real.log x + A) * x / (x ^ (Θ - 1) * x) +
        KM * Real.log x ^ 2 * x ^ (Θ + (Real.log x)⁻¹) * Real.log (1 + x) +
        KM * Real.log x ^ 2 * x / x) ≤ max Ci Cz * K' * (x ^ Θ * Real.log x ^ 3) := by
      calc _ ≤ Cz * (K' * (x ^ Θ * Real.log x ^ 3)) := mul_le_mul_of_nonneg_left hrhs hCz.le
        _ ≤ max Ci Cz * (K' * (x ^ Θ * Real.log x ^ 3)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ = _ := by ring
    rw [if_pos rfl]
    set Sm := ∑' n : ℕ, χ (n : ZMod 1) * Λ n * Smooth1 ν (x ^ (Θ - 1)) (n / x)
    set Mx := 𝓜 (fun t ↦ (Smooth1 ν (x ^ (Θ - 1)) t : ℂ)) 1 * x
    have htri : ‖psiChi x χ - (x : ℂ)‖ ≤ ‖psiChi x χ - Sm‖ + ‖Sm - Mx‖ + ‖Mx - x‖ := by
      have e : psiChi x χ - (x : ℂ) = (psiChi x χ - Sm) + (Sm - Mx) + (Mx - x) := by ring
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hfin : ‖psiChi x χ - (x : ℂ)‖ ≤ Cbig * (x ^ Θ * Real.log x ^ 3) := by
      have := htri.trans (add_le_add (add_le_add hun3 (hc.trans hcz)) hmain)
      calc _ ≤ _ := this
        _ = (max Ci Cz * K' + 8 + cM) * (x ^ Θ * Real.log x ^ 3) := by ring
        _ = _ := by rw [hCbig]
    have : 0 ≤ Csmall * (x ^ Θ * Real.log x ^ 3) := by positivity
    calc _ ≤ Cbig * (x ^ Θ * Real.log x ^ 3) := hfin
      _ ≤ (Cbig + Csmall) * x ^ Θ * Real.log x ^ 3 := by nlinarith
  · have hχ1 := ne_one_of_primitive hχ hq1
    have hrect : ∀ s ∈ Rectangle (((Θ + (Real.log x)⁻¹ : ℝ) : ℂ) - I * x)
        (((1 + (Real.log x)⁻¹ : ℝ) : ℂ) + I * x), DirichletCharacter.LFunction χ s ≠ 0 := by
      intro s hs
      have hs' := hs
      simp only [Rectangle, Complex.mem_reProdIm] at hs'
      have hre : Θ + (Real.log x)⁻¹ ≤ s.re := by
        have h1 := hs'.1
        simp only [sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul, mul_zero, sub_zero,
          add_re, sub_self, add_zero] at h1
        rw [Set.uIcc_of_le (by linarith)] at h1
        exact h1.1
      rcases eq_or_ne s 1 with rfl | hs1
      · exact DirichletCharacter.LFunction_apply_one_ne_zero hχ1
      · exact hZ q χ hχ s (by linarith) hs1
    have hc := hcont q χ hχ1 x (x ^ (Θ - 1)) (Θ + (Real.log x)⁻¹) x (Real.log x + A)
      (KM * Real.log x ^ 2) (by linarith) hεpos hε1 hσ₁h hσ₁1 (by linarith) (by positivity) hM0
      hrect hM₀ hleft hhor
    have hci : Ci * ((Real.log x + A) * x / (x ^ (Θ - 1) * x) +
        KM * Real.log x ^ 2 * x ^ (Θ + (Real.log x)⁻¹) * Real.log (1 + x) +
        KM * Real.log x ^ 2 * x / x) ≤ max Ci Cz * K' * (x ^ Θ * Real.log x ^ 3) := by
      calc _ ≤ Ci * (K' * (x ^ Θ * Real.log x ^ 3)) := mul_le_mul_of_nonneg_left hrhs hCi.le
        _ ≤ max Ci Cz * (K' * (x ^ Θ * Real.log x ^ 3)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ = _ := by ring
    rw [if_neg hq1, sub_zero]
    set Sm := ∑' n : ℕ, χ (n : ZMod q) * Λ n * Smooth1 ν (x ^ (Θ - 1)) (n / x)
    have htri : ‖psiChi x χ‖ ≤ ‖psiChi x χ - Sm‖ + ‖Sm‖ := by
      have e : psiChi x χ = (psiChi x χ - Sm) + Sm := by ring
      calc ‖psiChi x χ‖ = ‖(psiChi x χ - Sm) + Sm‖ := by rw [← e]
        _ ≤ _ := norm_add_le _ _
    have hfin : ‖psiChi x χ‖ ≤ Cbig * (x ^ Θ * Real.log x ^ 3) := by
      have := htri.trans (add_le_add hun3 (hc.trans hci))
      have hcM0 : 0 ≤ cM * (x ^ Θ * Real.log x ^ 3) := by positivity
      calc _ ≤ _ := this
        _ ≤ (max Ci Cz * K' + 8 + cM) * (x ^ Θ * Real.log x ^ 3) := by nlinarith
        _ = _ := by rw [hCbig]
    have : 0 ≤ Csmall * (x ^ Θ * Real.log x ^ 3) := by positivity
    calc _ ≤ Cbig * (x ^ Θ * Real.log x ^ 3) := hfin
      _ ≤ (Cbig + Csmall) * x ^ Θ * Real.log x ^ 3 := by nlinarith

/-- **The log power traded for any power of `x`**: `NoZerosRightPrim Θ`, `1/2 ≤ Θ < 1`, gives
U-1473's `PsiChiPrimBound Θ'` for every `Θ' > Θ`. -/
theorem psiChiPrimBound_of_noZeros {Θ : ℝ} (h0 : 1 / 2 ≤ Θ) (h1 : Θ < 1)
    (hZ : NoZerosRightPrim Θ) {Θ' : ℝ} (hΘ' : Θ < Θ') : PsiChiPrimBound Θ' := by
  obtain ⟨C, hC, hb⟩ := psiChiPrimBound3_of_noZeros h0 h1 hZ
  set δ := Θ' - Θ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  refine ⟨C / δ, by positivity, fun q χ hq hχ x hx hqx ↦ (hb q χ hq hχ x hx hqx).trans ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have e : x ^ Θ' = x ^ Θ * x ^ δ := by rw [← Real.rpow_add hx0, hδ]; ring_nf
  have hxΘ : 0 ≤ x ^ Θ := by positivity
  calc C * x ^ Θ * Real.log x ^ 3 = C * x ^ Θ * Real.log x ^ 2 * Real.log x := by ring
    _ ≤ C * x ^ Θ * Real.log x ^ 2 * (x ^ δ / δ) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = C / δ * x ^ Θ' * Real.log x ^ 2 := by rw [e]; field_simp

end LeanLab.HardyLittlewood1923.U1503
