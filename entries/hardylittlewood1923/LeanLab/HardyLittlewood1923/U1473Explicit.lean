module

public import LeanLab.HardyLittlewood1923.U1468SingR
public import LeanLab.PNTPort.BV.Characters
public import LeanLab.PNTPort.BV.Helpers

/-!
AI-written Lean code, Claude, 2026-10-22, PC run 20261022T0804Z-19316, unit U-1473, paper P0004.

# Hardy-Littlewood 1923, splitting the cited input `ExplicitFormulaLog`

U-1453's cited `ExplicitFormulaLog` says: if no `L(s, χ)` vanishes in `Re s > Θ`, then
`|ψ(x; k, l) - x/φ(k)| ≤ C x^Θ (log x)²` uniformly for `2 ≤ x`, `1 ≤ k ≤ x`, `(l, k) = 1`.
Here it is split into elementary parts, all PROVED, and ONE named analytic input:

* `NoZerosRightPrim Θ`: no zero of `L(s, χ)` with `Re s > Θ`, `s ≠ 1`, for PRIMITIVE `χ` only;
  implied by U-1438's `NoZerosRight Θ`, the paper's Hypothesis R at level `Θ`, p. 4.
* `PsiChiPrimBound Θ`: `|ψ(x, χ) - [q = 1] x| ≤ C x^Θ (log x)²` for every primitive `χ` mod `q`,
  `1 ≤ q ≤ x`, `x ≥ 2`.
* `ExplicitFormulaPrim`, the ONLY cited input: `NoZerosRightPrim Θ → PsiChiPrimBound Θ`.
  Mathematically this is the truncated explicit formula for a primitive character with the zero
  count per unit height, Davenport, Multiplicative Number Theory, ch. 16, 19, 20, where the case
  `Θ = 1/2` is Davenport ch. 20, `ψ(x, χ) ≪ x^{1/2} (log qx)²`; for `Θ < 1/2` the hypothesis is
  false by the functional equation, so the statement is true as a whole. NOT proved here.

PROVED, no cited input:
* `perChar_bound`: imprimitive to primitive, with the principal character against `ψ(x)`,
  loss `Σ_{n ≤ x, (n, k) > 1} Λ(n) ≤ (log x)²/log 2`.
* `psiPowerLog_of_prim`: `0 ≤ Θ` and `PsiChiPrimBound Θ` give `PsiPowerLog Θ`, by orthogonality.
* `not_noZerosRight_neg`: `NoZerosRight Θ` is FALSE for `Θ < 0`: the principal character mod 2 has
  `L(s, χ₀) = (1 - 2^{-s}) ζ(s)`, which vanishes at `s = 2πi/log 2`.
* `explicitFormulaLog_of_prim`: `ExplicitFormulaPrim → ExplicitFormulaLog`.
* `printedA_form_all_U1473`: printed Theorem A, eq. 3.113 p. 21, every `r ≥ 3`,
  `Θ ∈ [47/64, 3/4)`, CONDITIONAL ON `ExplicitFormulaPrim` only.
* Vacuity: `noZerosRightPrim_one`, `psiChiPrimBound_one`, the cited implication at `Θ = 1` is a
  theorem, `explicitFormulaPrim_at_one`.

Every proof is complete, no axiom. Binary Goldbach is OPEN.

Packaging note: in this copy the cited Props of this file and the theorems that take them as
hypotheses were removed, as no compared theorem uses them; see PORTING.md.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1473

open Real Finset
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1438 (NoZerosRight)
open LeanLab.HardyLittlewood1923.U1444 (singR)
open LeanLab.HardyLittlewood1923.U1453 (PsiPowerLog)
open LeanLab.PNTPort.BV (psiChi psiBad psiBad_nonneg psiBad_le abs_psi_sub_le
  norm_psiChi_sub_primitive)

/-! ### The named analytic input -/

/-- Hypothesis R at level `Θ` for primitive characters: no zero of `L(s, χ)`, `χ` primitive, with
`Re s > Θ`, the pole `s = 1` excluded. -/
def NoZerosRightPrim (Θ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ s : ℂ, Θ < s.re → s ≠ 1 →
    DirichletCharacter.LFunction χ s ≠ 0

theorem noZerosRightPrim_of {Θ : ℝ} (h : NoZerosRight Θ) : NoZerosRightPrim Θ :=
  fun q _ χ _ s hs hs1 => h q χ s hs hs1

/-- `|ψ(x, χ) - [q = 1] x| ≤ C x^Θ (log x)²` for every primitive `χ` mod `q`, `1 ≤ q ≤ x`, `x ≥ 2`. -/
def PsiChiPrimBound (Θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → χ.IsPrimitive →
    ∀ x : ℝ, 2 ≤ x → (q : ℝ) ≤ x →
      ‖psiChi x χ - (if q = 1 then (x : ℂ) else 0)‖ ≤ C * x ^ Θ * Real.log x ^ 2

/-! ### Elementary part 1: one character -/

lemma log_sq_div_le {x Θ : ℝ} (hx : 2 ≤ x) (hΘ : 0 ≤ Θ) :
    Real.log x ^ 2 / Real.log 2 ≤ 1 / Real.log 2 * x ^ Θ * Real.log x ^ 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx1 : 1 ≤ x ^ Θ := Real.one_le_rpow (by linarith) hΘ
  have hL : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  rw [div_le_iff₀ h2]
  have : 1 / Real.log 2 * x ^ Θ * Real.log x ^ 2 * Real.log 2 = x ^ Θ * Real.log x ^ 2 := by
    field_simp
  rw [this]
  nlinarith

/-- **One character**: for `χ` mod `k`, `1 ≤ k ≤ x`,
`‖ψ(x, χ) - [χ = 1] x‖ ≤ (1/log 2 + C) x^Θ (log x)²` from `PsiChiPrimBound Θ` with constant `C`. -/
theorem perChar_bound {Θ C : ℝ} (hΘ : 0 ≤ Θ)
    (hP : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → χ.IsPrimitive →
      ∀ x : ℝ, 2 ≤ x → (q : ℝ) ≤ x →
        ‖psiChi x χ - (if q = 1 then (x : ℂ) else 0)‖ ≤ C * x ^ Θ * Real.log x ^ 2)
    {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) {x : ℝ} (hx : 2 ≤ x) (hkx : (k : ℝ) ≤ x) :
    ‖psiChi x χ - (if χ = 1 then (x : ℂ) else 0)‖ ≤
      (1 / Real.log 2 + C) * x ^ Θ * Real.log x ^ 2 := by
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hc0 : χ.conductor ≠ 0 := DirichletCharacter.conductor_ne_zero χ
  have hc1 : 1 ≤ χ.conductor := Nat.one_le_iff_ne_zero.mpr hc0
  have hck : χ.conductor ≤ k := Nat.le_of_dvd (by omega) (DirichletCharacter.conductor_dvd_level χ)
  have hcx : (χ.conductor : ℝ) ≤ x := le_trans (by exact_mod_cast hck) hkx
  have hprim := hP χ.conductor χ.primitiveCharacter hc1
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) x hx hcx
  have hif : (if χ = 1 then (x : ℂ) else 0) = (if χ.conductor = 1 then (x : ℂ) else 0) := by
    by_cases h1 : χ = 1
    · rw [if_pos h1, if_pos ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).1 h1)]
    · rw [if_neg h1, if_neg (fun h' => h1 ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).2 h'))]
  have hbad : psiBad x k ≤ Real.log x ^ 2 / Real.log 2 := by
    refine (psiBad_le (by linarith) hk1).trans ?_
    have hlk : Real.log k ≤ Real.log x := Real.log_le_log (by exact_mod_cast hk1) hkx
    have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [div_mul_eq_mul_div, sq]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlk hlx) h2.le
  have hsub := norm_psiChi_sub_primitive (q := k) x χ
  have hsub' : ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ ≤ psiBad x k := hsub
  rw [hif]
  calc ‖psiChi x χ - (if χ.conductor = 1 then (x : ℂ) else 0)‖
      = ‖(psiChi x χ - psiChi x χ.primitiveCharacter) +
          (psiChi x χ.primitiveCharacter - (if χ.conductor = 1 then (x : ℂ) else 0))‖ := by
        congr 1; ring
    _ ≤ ‖psiChi x χ - psiChi x χ.primitiveCharacter‖ +
          ‖psiChi x χ.primitiveCharacter - (if χ.conductor = 1 then (x : ℂ) else 0)‖ :=
        norm_add_le _ _
    _ ≤ Real.log x ^ 2 / Real.log 2 + C * x ^ Θ * Real.log x ^ 2 :=
        add_le_add (hsub'.trans hbad) hprim
    _ ≤ 1 / Real.log 2 * x ^ Θ * Real.log x ^ 2 + C * x ^ Θ * Real.log x ^ 2 :=
        add_le_add (log_sq_div_le hx hΘ) le_rfl
    _ = (1 / Real.log 2 + C) * x ^ Θ * Real.log x ^ 2 := by ring

/-! ### Elementary part 2: orthogonality -/

/-- **From primitive characters to progressions**: `0 ≤ Θ` and `PsiChiPrimBound Θ` give
`PsiPowerLog Θ`, with constant `1/log 2 + C`. -/
theorem psiPowerLog_of_prim {Θ : ℝ} (hΘ : 0 ≤ Θ) (h : PsiChiPrimBound Θ) : PsiPowerLog Θ := by
  obtain ⟨C, hC, hP⟩ := h
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log 2 + C, by positivity, fun x hx k l hk hcop hkx => ?_⟩
  haveI : NeZero k := ⟨by omega⟩
  set B := (1 / Real.log 2 + C) * x ^ Θ * Real.log x ^ 2 with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ x ^ Θ := Real.rpow_nonneg (by linarith) _
    positivity
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ k)).card = k.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ k]
  have h1 : ‖psiChi x (1 : DirichletCharacter ℂ k) - x‖ ≤ B := by
    have := perChar_bound hΘ hP (1 : DirichletCharacter ℂ k) hx hkx
    rwa [if_pos rfl] at this
  have hother : ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ k)).erase 1, ‖psiChi x χ‖ ≤ B := by
    intro χ hχ
    have hne : χ ≠ 1 := (mem_erase.1 hχ).1
    have := perChar_bound hΘ hP χ hx hkx
    rwa [if_neg hne, sub_zero] at this
  have hsum : ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ k)).erase 1, ‖psiChi x χ‖ ≤
      ((univ : Finset (DirichletCharacter ℂ k)).erase 1).card • B :=
    sum_le_card_nsmul _ _ _ hother
  rw [nsmul_eq_mul, card_erase_of_mem (mem_univ _), hcard] at hsum
  have htot1 : 1 ≤ k.totient := Nat.totient_pos.2 (by omega)
  have hcast : ((k.totient - 1 : ℕ) : ℝ) = (k.totient : ℝ) - 1 := by
    rw [Nat.cast_sub htot1, Nat.cast_one]
  rw [hcast] at hsum
  refine (abs_psi_sub_le x hcop).trans ?_
  rw [div_le_iff₀ hφ]
  calc ‖psiChi x (1 : DirichletCharacter ℂ k) - x‖ +
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ k)).erase 1, ‖psiChi x χ‖
      ≤ B + ((k.totient : ℝ) - 1) * B := add_le_add h1 hsum
    _ = B * k.totient := by ring

/-! ### Elementary part 3: `Θ < 0` is impossible -/

/-- `L(s, χ₀)` for the principal character mod 2 vanishes at `s = 2πi / log 2`, `Re s = 0`. -/
theorem LFunction_trivChar_two_zero :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 2)
      (2 * Real.pi * Complex.I / (Real.log 2 : ℂ)) = 0 := by
  set s : ℂ := 2 * Real.pi * Complex.I / (Real.log 2 : ℂ) with hs
  have hl2 : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hre : s.re = 0 := by
    rw [hs, Complex.div_ofReal_re]
    simp
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hre; simp at hre
  have hpow : (2 : ℂ) ^ (-s) = 1 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]
    have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.ofReal_log (by norm_num)]
    rw [hlog, hs, show (Real.log 2 : ℂ) * -(2 * Real.pi * Complex.I / (Real.log 2 : ℂ)) =
      -(2 * Real.pi * Complex.I) by field_simp]
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  have := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 2) hs1
  rw [show DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 2) s =
    DirichletCharacter.LFunctionTrivChar 2 s from rfl, this,
    Nat.Prime.primeFactors Nat.prime_two, prod_singleton]
  push_cast
  rw [hpow, sub_self, zero_mul]

/-- **`NoZerosRight Θ` is false for `Θ < 0`.** Hardy and Littlewood remark that `Θ ≥ 1/2` in any
case, p. 4; the lab's predicate counts every zero, so the imprimitive zeros on `Re s = 0` already
force `Θ ≥ 0`. -/
theorem not_noZerosRight_neg {Θ : ℝ} (hΘ : Θ < 0) : ¬ NoZerosRight Θ := by
  intro h
  have hre : (2 * Real.pi * Complex.I / (Real.log 2 : ℂ)).re = 0 := by
    rw [Complex.div_ofReal_re]; simp
  refine h 2 (1 : DirichletCharacter ℂ 2) _ (by rw [hre]; exact hΘ) ?_ LFunction_trivChar_two_zero
  intro h1; rw [h1] at hre; simp at hre

/-! ### The split -/

/-! ### Vacuity -/

/-- The hypothesis of the cited implication holds at `Θ = 1`. -/
theorem noZerosRightPrim_one : NoZerosRightPrim 1 :=
  noZerosRightPrim_of U1438.noZerosRight_one

/-- The conclusion of the cited implication holds at `Θ = 1`, from Chebyshev. -/
theorem psiChiPrimBound_one : PsiChiPrimBound 1 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 4 + 5) / Real.log 2 ^ 2, by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity, fun q χ hq _ x hx _ => ?_⟩
  haveI : NeZero q := ⟨by omega⟩
  have hx0 : 0 ≤ x := by linarith
  have hψ : ‖psiChi x χ‖ ≤ Chebyshev.psi x := by
    unfold psiChi Chebyshev.psi
    have e : Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ := by ext n; simp; omega
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)
  have hψ2 := Chebyshev.psi_le_const_mul_self hx0
  have hδ : ‖(if q = 1 then (x : ℂ) else 0)‖ ≤ x := by
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    · simp [hx0]
  have hl : Real.log 2 ^ 2 ≤ Real.log x ^ 2 :=
    pow_le_pow_left₀ h2.le (Real.log_le_log (by norm_num) hx) 2
  have hl4 : 0 < Real.log 4 + 5 := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  rw [Real.rpow_one]
  calc ‖psiChi x χ - (if q = 1 then (x : ℂ) else 0)‖
      ≤ ‖psiChi x χ‖ + ‖(if q = 1 then (x : ℂ) else 0)‖ := norm_sub_le _ _
    _ ≤ (Real.log 4 + 4) * x + x := add_le_add (hψ.trans hψ2) hδ
    _ = (Real.log 4 + 5) / Real.log 2 ^ 2 * x * Real.log 2 ^ 2 := by field_simp; ring
    _ ≤ (Real.log 4 + 5) / Real.log 2 ^ 2 * x * Real.log x ^ 2 := by gcongr

/-- **The cited implication is a theorem at `Θ = 1`**, so it is not vacuous in form. -/
theorem explicitFormulaPrim_at_one : NoZerosRightPrim 1 → PsiChiPrimBound 1 :=
  fun _ => psiChiPrimBound_one

/-- Vacuity of the headline's range: `Θ = 47/64` is in `[47/64, 3/4)`, and `NoZerosRight Θ` there
is implied by GRH, open; it is not refuted by `not_noZerosRight_neg`, which needs `Θ < 0`. -/
theorem headline_range_nonempty : (47 : ℝ) / 64 < 3 / 4 ∧ ¬ ((47 : ℝ) / 64 < 0) := by
  constructor <;> norm_num

end LeanLab.HardyLittlewood1923.U1473

