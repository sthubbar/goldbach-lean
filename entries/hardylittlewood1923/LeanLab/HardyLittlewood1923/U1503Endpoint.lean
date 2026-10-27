module

public import LeanLab.HardyLittlewood1923.U1503ThmA

/-!
AI-written Lean code, Claude, 2026-10-23, CLOUD run 20261023T1343Z-19109, unit U-1503, paper P0004.

# Theorem A at the closed endpoint `Θ = 47/64`, with no cited input

U1503Explicit gives `ψ(x, χ) - [q = 1] x ≪ x^Θ (log x)³`, one log more than U-1453's
`PsiPowerLog`. At `Θ > 47/64` U1503ThmA absorbs it into a power of `x`; at `Θ = 47/64` there is no
slack, so this file carries `(log x)³` through U-1453's circle method instead. In U-1453's rate the
`ψ` bound enters only through the major arcs at points `y ≤ n`, with its constant linearly, so
`C y^θ (log y)³ ≤ (C log n) y^θ (log y)²` on `y ≤ n` costs one factor `1 + log n` at the end.

* `PsiPowerLog3 θ`: U-1453's `PsiPowerLog θ` with `(log x)³`.
* `perChar_bound3`, `psiPowerLog3_of_prim`: U-1473's reduction to primitive characters, with `³`.
* `psiPowerLog3_of_noZeros`: `1/2 ≤ Θ < 1` and `NoZerosRight Θ` give `PsiPowerLog3 Θ`.
* `major_of_psiPowerLog3`, `r3_rate3`, `nur3_rate3`: copies of U-1453's major arc bound and rates,
  with final `(1 + log n)⁶` in place of `(1 + log n)⁵`.
* `printedA3_U1503_closed`: printed Theorem A for `r = 3` on `47/64 ≤ Θ < 3/4`, `B = 6`.
* `printedA_form_all_U1503_closed`: eq. 3.113 p. 21 for every `r ≥ 3` on `47/64 ≤ Θ < 3/4`,
  the exact statement of U-1489's `printedA_form_all_U1489`, now with NO cited input.
Binary Goldbach is OPEN.

Packaging note: in this copy the cited Props of this file and the theorems that take them as
hypotheses were removed, as no compared theorem uses them; see PORTING.md.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1503

open Real Finset Filter
open scoped ArithmeticFunction.Moebius
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.U1444
open LeanLab.HardyLittlewood1923.U1453 (PsiPowerLog err_total17)
open LeanLab.HardyLittlewood1923.U1463
open LeanLab.HardyLittlewood1923.U1468
open LeanLab.PNTPort.Vinogradov (S V Aq r3 J singP singP_eq_fS norm_Aq_sub_le norm_Aq_le
  major_of_bound ternary_explicit lp_bound sum_vonMangoldt_sq_le fS)
open LeanLab.PNTPort.BV (psiChi psiBad psiBad_le abs_psi_sub_le norm_psiChi_sub_primitive)

/-- Primes in progressions with error `C x^θ (log x)³`, uniform in `k ≤ x`. -/
def PsiPowerLog3 (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ x →
    |LeanLab.HeathBrown1985.psi x k l - x / (Nat.totient k : ℝ)| ≤ C * x ^ θ * Real.log x ^ 3

lemma log_cube_div_le {x Θ : ℝ} (hx : 2 ≤ x) (hΘ : 0 ≤ Θ) :
    Real.log x ^ 2 / Real.log 2 ≤ 1 / Real.log 2 ^ 2 * x ^ Θ * Real.log x ^ 3 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hx1 : 1 ≤ x ^ Θ := Real.one_le_rpow (by linarith) hΘ
  have hL : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  rw [div_le_iff₀ h2]
  have e : 1 / Real.log 2 ^ 2 * x ^ Θ * Real.log x ^ 3 * Real.log 2 =
      x ^ Θ * Real.log x ^ 2 * (Real.log x / Real.log 2) := by
    field_simp
  rw [e]
  have h1 : 1 ≤ Real.log x / Real.log 2 := by rw [le_div_iff₀ h2]; linarith
  have : Real.log x ^ 2 ≤ x ^ Θ * Real.log x ^ 2 := le_mul_of_one_le_left hL hx1
  calc Real.log x ^ 2 ≤ x ^ Θ * Real.log x ^ 2 := this
    _ ≤ x ^ Θ * Real.log x ^ 2 * (Real.log x / Real.log 2) :=
        le_mul_of_one_le_right (by positivity) h1

/-- **One character**, U-1473's `perChar_bound` with `(log x)³`. -/
theorem perChar_bound3 {Θ C : ℝ} (hΘ : 0 ≤ Θ)
    (hP : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → χ.IsPrimitive →
      ∀ x : ℝ, 2 ≤ x → (q : ℝ) ≤ x →
        ‖psiChi x χ - (if q = 1 then (x : ℂ) else 0)‖ ≤ C * x ^ Θ * Real.log x ^ 3)
    {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) {x : ℝ} (hx : 2 ≤ x) (hkx : (k : ℝ) ≤ x) :
    ‖psiChi x χ - (if χ = 1 then (x : ℂ) else 0)‖ ≤
      (1 / Real.log 2 ^ 2 + C) * x ^ Θ * Real.log x ^ 3 := by
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
    · rw [if_neg h1,
        if_neg (fun h' => h1 ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).2 h'))]
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
    _ ≤ Real.log x ^ 2 / Real.log 2 + C * x ^ Θ * Real.log x ^ 3 :=
        add_le_add (hsub'.trans hbad) hprim
    _ ≤ 1 / Real.log 2 ^ 2 * x ^ Θ * Real.log x ^ 3 + C * x ^ Θ * Real.log x ^ 3 :=
        add_le_add (log_cube_div_le hx hΘ) le_rfl
    _ = (1 / Real.log 2 ^ 2 + C) * x ^ Θ * Real.log x ^ 3 := by ring

/-- **From primitive characters to progressions**, U-1473's `psiPowerLog_of_prim` with `³`. -/
theorem psiPowerLog3_of_prim {Θ : ℝ} (hΘ : 0 ≤ Θ) (h : PsiChiPrimBound3 Θ) : PsiPowerLog3 Θ := by
  obtain ⟨C, hC, hP⟩ := h
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log 2 ^ 2 + C, by positivity, fun x hx k l hk hcop hkx => ?_⟩
  have : NeZero k := ⟨by omega⟩
  set B := (1 / Real.log 2 ^ 2 + C) * x ^ Θ * Real.log x ^ 3 with hB
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ k)).card = k.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ k]
  have h1 : ‖psiChi x (1 : DirichletCharacter ℂ k) - x‖ ≤ B := by
    have := perChar_bound3 hΘ hP (1 : DirichletCharacter ℂ k) hx hkx
    rwa [if_pos rfl] at this
  have hother : ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ k)).erase 1, ‖psiChi x χ‖ ≤ B := by
    intro χ hχ
    have hne : χ ≠ 1 := (mem_erase.1 hχ).1
    have := perChar_bound3 hΘ hP χ hx hkx
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

/-- **Hypothesis R at level `Θ ∈ [1/2, 1)` gives `PsiPowerLog3 Θ`**, at `Θ` itself. -/
theorem psiPowerLog3_of_noZeros {Θ : ℝ} (h0 : 1 / 2 ≤ Θ) (h1 : Θ < 1) (hZ : NoZerosRight Θ) :
    PsiPowerLog3 Θ :=
  psiPowerLog3_of_prim (by linarith)
    (psiChiPrimBound3_of_noZeros h0 h1 (U1473.noZerosRightPrim_of hZ))

/-- The major arc approximation from `PsiPowerLog3 θ`, U-1453's `major_of_psiPowerLog` with
`(log x)³`. -/
theorem major_of_psiPowerLog3 {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (h : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → Nat.Coprime l k → (k : ℝ) ≤ x →
      |LeanLab.HeathBrown1985.psi x k l - x / (Nat.totient k : ℝ)| ≤ C * x ^ θ * Real.log x ^ 3)
    {N : ℕ} (hN : 1 ≤ N) {q : ℕ} (hq : 1 ≤ q) (a : ℤ) (hcop : IsCoprime a (q : ℤ)) (β : ℝ) :
    ‖S N (a / q + β) - (μ q : ℂ) / q.totient * V N β‖ ≤
      q * (7 + C * (N : ℝ) ^ θ * Real.log N ^ 3 + 2 * Real.log N) * (1 + 2 * π * |β| * N) := by
  apply major_of_bound hq a N β
  intro n hn
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hNθ : 0 ≤ C * (N : ℝ) ^ θ * Real.log N ^ 3 := by positivity
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  have htot : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  by_cases hsmall : n < 2 ∨ (n : ℝ) < q
  · have hnq : (n : ℝ) ≤ q := by
      rcases hsmall with h1 | h1
      · have : (n : ℝ) ≤ 1 := by exact_mod_cast (by omega : n ≤ 1)
        linarith
      · exact h1.le
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 := norm_Aq_le q a n
    have h2 : ‖(μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖ ≤ n := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hμ : ‖(μ q : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc ‖(μ q : ℂ)‖ * ((n : ℝ) / q.totient) ≤ 1 * n :=
            mul_le_mul hμ (div_le_self hn0 htot) (by positivity) zero_le_one
        _ = n := one_mul _
    have h4 : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    calc ‖Aq q a n - (μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖
        ≤ ‖Aq q a n‖ + ‖(μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖ := norm_sub_le _ _
      _ ≤ (Real.log 4 + 4) * n + n := add_le_add h1 h2
      _ ≤ 7 * q := by nlinarith
      _ ≤ q * (7 + C * (N : ℝ) ^ θ * Real.log N ^ 3 + 2 * Real.log N) := by nlinarith
  · push_neg at hsmall
    obtain ⟨hn2, hqn⟩ := hsmall
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hlogn : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hterm : ∀ r ∈ (range q).filter (fun r => Nat.Coprime r q),
        |LeanLab.HeathBrown1985.psi n q r - (n : ℝ) / q.totient| ≤
          C * (N : ℝ) ^ θ * Real.log N ^ 3 := by
      intro r hr
      have hcr : Nat.Coprime r q := (mem_filter.1 hr).2
      refine (h n hn2' q r hq hcr hqn).trans ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hnN hθ) hC)
        (pow_le_pow_left₀ hlogn0 hlogn 3) (by positivity) (by positivity)
    have hsum := sum_le_sum hterm
    rw [sum_const, nsmul_eq_mul] at hsum
    have hcard : (((range q).filter (fun r => Nat.Coprime r q)).card : ℝ) ≤ q := by
      have := (card_filter_le (range q) (fun r => Nat.Coprime r q)).trans (card_range q).le
      exact_mod_cast this
    have hbad := LeanLab.PNTPort.BV.psiBad_le (x := (n : ℝ)) (by linarith) hq
    have hlp := lp_bound hqr
    have hbad' : LeanLab.PNTPort.BV.psiBad n q ≤ 2 * q * Real.log N := by
      calc LeanLab.PNTPort.BV.psiBad n q ≤ Real.log q / Real.log 2 * Real.log n := hbad
        _ ≤ 2 * q * Real.log N := mul_le_mul hlp hlogn hlogn0 (by positivity)
    calc ‖Aq q a n - (μ q : ℂ) * ((n : ℝ) / q.totient : ℝ)‖
        ≤ ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q),
            |LeanLab.HeathBrown1985.psi n q r - (n : ℝ) / q.totient|
          + LeanLab.PNTPort.BV.psiBad n q := norm_Aq_sub_le q hq hcop n
      _ ≤ q * (C * (N : ℝ) ^ θ * Real.log N ^ 3) + 2 * q * Real.log N := by
          have := mul_le_mul_of_nonneg_right hcard hNθ
          linarith
      _ ≤ q * (7 + C * (N : ℝ) ^ θ * Real.log N ^ 3 + 2 * Real.log N) := by nlinarith

set_option maxHeartbeats 4000000 in
/-- **The rate from `PsiPowerLog3`**, U-1453's `r3_rate_of_psiPowerLog` with `C log x` in place
of `C` for the fixed `x = n`: `|r₃(n) - n²/2 · 𝔖₃(n)| ≤ K n^{2 - (1-θ)/17} (1 + log n)⁶`. -/
theorem r3_rate3 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hψ : PsiPowerLog3 θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |r3 n n - sing3 n * (n : ℝ) ^ 2 / 2| ≤
        K * ((n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 6) := by
  obtain ⟨C, hC, h⟩ := hψ
  set η := 2 * (1 - θ) / 17 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hη1 : η ≤ 2 / 17 := by rw [hηdef]; linarith
  set C0 := 1800 * (Real.sqrt 2 + 2) + 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) * (9 + C) + 1
    with hC0
  have hC00 : 0 ≤ C0 := by have := Real.pi_pos; rw [hC0]; positivity
  refine ⟨C0 + 3 * Real.exp 8, by positivity, max 3 ⌈(2 : ℝ) ^ (1 / η)⌉₊, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_left _ _) hn
  set x := (n : ℝ) with hxdef
  have hx3 : (3 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hn3
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set s := x ^ (η / 4) with hsdef
  have hs1 : 1 ≤ s := Real.one_le_rpow hx1 (by positivity)
  have hs0 : 0 < s := by linarith
  have hsk : ∀ k : ℕ, s ^ k = x ^ (η / 4 * k) := fun k => pow_rpow_eq hx0.le _ k
  have hs4 : s ^ 4 = x ^ η := by rw [hsk]; congr 1; push_cast; ring
  have hs4_2 : 2 ≤ s ^ 4 := by
    rw [hs4]
    have hc : (2 : ℝ) ^ (1 / η) ≤ x := by
      have : ⌈(2 : ℝ) ^ (1 / η)⌉₊ ≤ n := le_trans (le_max_right _ _) hn
      exact (Nat.le_ceil _).trans (by rw [hxdef]; exact_mod_cast this)
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / η)) ^ η := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hη.ne', Real.rpow_one]
      _ ≤ x ^ η := Real.rpow_le_rpow (by positivity) hc hη.le
  have hs34 : s ^ 34 ≤ x := by
    rw [hsk]
    calc x ^ (η / 4 * ((34 : ℕ) : ℝ)) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; rw [hηdef]; nlinarith)
      _ = x := Real.rpow_one x
  have hx45 : x ^ ((4 : ℝ) / 5) * s ^ 2 ≤ x := by
    rw [hsk, ← Real.rpow_add hx0]
    calc x ^ ((4 : ℝ) / 5 + η / 4 * ((2 : ℕ) : ℝ)) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; nlinarith)
      _ = x := Real.rpow_one x
  have hθs : x ^ θ = x / s ^ 34 := by
    rw [hsk, show η / 4 * ((34 : ℕ) : ℝ) = 1 - θ by rw [hηdef]; push_cast; ring]
    rw [eq_div_iff (by positivity), ← Real.rpow_add hx0, show θ + (1 - θ) = 1 by ring,
      Real.rpow_one]
  -- the parameters
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = ⌊s ^ 4⌋₊ := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = ⌊x / s ^ 10⌋₊ := ⟨_, rfl⟩
  have hp : (P : ℝ) ≤ s ^ 4 := by rw [hPdef]; exact Nat.floor_le (by positivity)
  have hp2 : s ^ 4 / 2 ≤ (P : ℝ) := by
    have : s ^ 4 < (P : ℝ) + 1 := by rw [hPdef]; exact Nat.lt_floor_add_one _
    linarith
  have hp1 : (1 : ℝ) ≤ P := by linarith
  have hP1 : 1 ≤ P := by exact_mod_cast hp1
  have hs10 : s ^ 10 ≤ x := le_trans (pow_le_pow_right₀ hs1 (by norm_num)) hs34
  have hs10p : (0 : ℝ) < s ^ 10 := by positivity
  have hq : (Q : ℝ) ≤ x / s ^ 10 := by rw [hQdef]; exact Nat.floor_le (by positivity)
  have hq1 : x / s ^ 10 ≤ Q + 1 := by
    have : x / s ^ 10 < (Q : ℝ) + 1 := by rw [hQdef]; exact Nat.lt_floor_add_one _
    linarith
  have hQ1 : 1 ≤ Q := by
    rw [hQdef]
    exact Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hs10p, one_mul]; exact hs10)
  have hQN : Q ≤ n := by
    have : (Q : ℝ) ≤ n := hq.trans (div_le_self hx0.le (one_le_pow₀ hs1))
    exact_mod_cast this
  have hs_gt : 1 < s := by
    by_contra hle
    push_neg at hle
    have : s ^ 4 ≤ 1 := pow_le_one₀ hs0.le hle
    linarith
  have h18 : 2 * s ^ 18 < x := by
    have a1 : 2 * s ^ 18 ≤ s ^ 4 * s ^ 18 := mul_le_mul_of_nonneg_right hs4_2 (by positivity)
    have a2 : s ^ 4 * s ^ 18 = s ^ 22 := by ring
    have a3 : s ^ 22 < s ^ 34 := pow_lt_pow_right₀ hs_gt (by norm_num)
    linarith
  have hPQ : 2 / ((Q : ℝ) + 1) < 1 / (P : ℝ) ^ 2 := by
    have hxs : 0 < x / s ^ 10 := by positivity
    have c1 : 2 / ((Q : ℝ) + 1) ≤ 2 * s ^ 10 / x := by
      calc 2 / ((Q : ℝ) + 1) ≤ 2 / (x / s ^ 10) := div_le_div_of_nonneg_left (by norm_num) hxs hq1
        _ = 2 * s ^ 10 / x := by field_simp
    have c2 : 2 * s ^ 10 / x < 1 / s ^ 8 := by
      rw [div_lt_div_iff₀ hx0 (by positivity)]
      calc 2 * s ^ 10 * s ^ 8 = 2 * s ^ 18 := by ring
        _ < x := h18
        _ = 1 * x := (one_mul x).symm
    have c3 : 1 / s ^ 8 ≤ 1 / (P : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      calc (P : ℝ) ^ 2 ≤ (s ^ 4) ^ 2 := pow_le_pow_left₀ (by linarith) hp 2
        _ = s ^ 8 := by ring
    linarith
  have : NeZero (3 * n + 1) := ⟨by omega⟩
  set E := (P : ℝ) * (7 + C * x ^ θ * Real.log x ^ 3 + 2 * Real.log x) with hEdef
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hE0 : 0 ≤ E := by positivity
  have hmaj : ∀ q ∈ Icc 1 P, ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S n (a' / q + β) - (μ q : ℂ) / q.totient * V n β‖ ≤ E * (1 + 2 * π * |β| * n) := by
    intro q hq a' hcop β
    rw [mem_Icc] at hq
    refine (major_of_psiPowerLog3 hθ0 hC h (by omega) hq.1 a' hcop β).trans ?_
    apply mul_le_mul_of_nonneg_right _ (by have := Real.pi_pos; positivity)
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hq.2) (by positivity)
  have hTE := ternary_explicit (N := n) (M := 3 * n + 1) (P := P) (Q := Q) (n := n)
    (by omega) (by omega) hP1 hQ1 hQN hPQ hE0 hmaj
  have hsP : s ^ 2 / Real.sqrt 2 ≤ Real.sqrt P := by
    apply le_sqrt_of_sq (by positivity)
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    calc (s ^ 2) ^ 2 / 2 = s ^ 4 / 2 := by ring
      _ ≤ (P : ℝ) := hp2
  have hE : E ≤ s ^ 4 * (7 + (C * Real.log x) * (x / s ^ 34) * Real.log x ^ 2 +
      2 * Real.log x) := by
    rw [hEdef, ← hθs, show C * x ^ θ * Real.log x ^ 3 = (C * Real.log x) * x ^ θ * Real.log x ^ 2
      by ring]
    exact mul_le_mul_of_nonneg_right hp (by positivity)
  have hM : x ≤ ((3 * n + 1 : ℕ) : ℝ) := by rw [hxdef]; exact_mod_cast (by omega : n ≤ 3 * n + 1)
  have herr := err_total17 (x := x) (s := s) (u := 1 + Real.log x) (L := Real.log x) (p := P)
    (q := Q) (M := ((3 * n + 1 : ℕ) : ℝ)) (C := C * Real.log x)
    (Λ2 := ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m ^ 2)
    (E := E) hx1 hs1 hlog0 rfl (mul_nonneg hC hlog0) hs34 hx45 hp1 hp hp2 (Nat.cast_nonneg Q) hq hq1 hM
    (sum_vonMangoldt_sq_le n) (sum_nonneg fun _ _ => sq_nonneg _) hE0 hE
  set C0' := 1800 * (Real.sqrt 2 + 2) + 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) *
    (9 + C * Real.log x) + 1 with hC0'
  have hC0le : C0' ≤ C0 * (1 + Real.log x) := by
    have hk : 0 ≤ 9 * (Real.log 4 + 4) ^ 2 * (1 + 2 * π) := by
      have := Real.pi_pos; have : 0 ≤ Real.log 4 + 4 := by
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
      positivity
    have hs2 : 0 ≤ 1800 * (Real.sqrt 2 + 2) := by positivity
    rw [hC0', hC0]
    have h9 : 9 + C * Real.log x ≤ (9 + C) * (1 + Real.log x) := by nlinarith
    have := mul_le_mul_of_nonneg_left h9 hk
    nlinarith [mul_nonneg hs2 hlog0, hlog0]
  have hreal : (r3 n n : ℂ) - (J n n : ℂ) * singP P n =
      ((r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q : ℝ) : ℂ) := by
    rw [singP_eq_fS]; push_cast; ring
  rw [hreal, Complex.norm_real, Real.norm_eq_abs] at hTE
  have h1 : |r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q| ≤
      C0' * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) := hTE.trans herr
  have hs2x : s ^ 2 ≤ x := le_trans (pow_le_pow_right₀ hs1 (by norm_num)) hs34
  have h2 := main_term_err hn3 hP1 hs1 hsP hs2x
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hu1 : (1 : ℝ) ≤ (1 + Real.log x) ^ 5 := one_le_pow₀ (by linarith)
  have hB : x ^ 2 / s ^ 2 ≤ x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2 := by
    apply div_le_div_of_nonneg_right _ hs2.le
    have := mul_le_mul_of_nonneg_left hu1 (sq_nonneg x)
    linarith
  have hfin : x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2 =
      x ^ (2 - (1 - θ) / 17) * (1 + Real.log x) ^ 5 := by
    have e2 : s ^ 2 = x ^ ((1 - θ) / 17) := by
      rw [hsk]; congr 1; rw [hηdef]; push_cast; ring
    rw [e2, Real.rpow_sub hx0, show (x : ℝ) ^ (2 : ℝ) = x ^ 2 from Real.rpow_two x]
    ring
  calc |r3 n n - sing3 n * x ^ 2 / 2|
      = |(r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q) +
          (J n n * ∑ q ∈ Icc 1 P, fS n q - sing3 n * x ^ 2 / 2)| := by congr 1; ring
    _ ≤ |r3 n n - J n n * ∑ q ∈ Icc 1 P, fS n q| +
          |J n n * ∑ q ∈ Icc 1 P, fS n q - sing3 n * x ^ 2 / 2| := abs_add_le _ _
    _ ≤ C0' * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) +
          3 * Real.exp 8 * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) := by
        apply add_le_add h1
        exact h2.trans (mul_le_mul_of_nonneg_left hB (by positivity))
    _ ≤ (C0 + 3 * Real.exp 8) * (1 + Real.log x) * (x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2) := by
        have hB0 : 0 ≤ x ^ 2 * (1 + Real.log x) ^ 5 / s ^ 2 := by positivity
        have he8 : 0 ≤ 3 * Real.exp 8 := by positivity
        have h3 : 3 * Real.exp 8 ≤ 3 * Real.exp 8 * (1 + Real.log x) := by nlinarith
        have := mul_le_mul_of_nonneg_right hC0le hB0
        have := mul_le_mul_of_nonneg_right h3 hB0
        nlinarith
    _ = (C0 + 3 * Real.exp 8) * (x ^ (2 - (1 - θ) / 17) * (1 + Real.log x) ^ 6) := by
        rw [show (1 + Real.log x) ^ 6 = (1 + Real.log x) ^ 5 * (1 + Real.log x) by ring,
          ← mul_assoc (x ^ (2 - (1 - θ) / 17)), ← hfin]
        ring

/-- The rate for prime weights `ν₃`, via `r3_sub_nur3_power`. -/
theorem nur3_rate3 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hψ : PsiPowerLog3 θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n| ≤
        K * ((n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 6) := by
  obtain ⟨K, hK, n₀, h⟩ := r3_rate3 hθ0 hθ1 hψ
  obtain ⟨C₁, hC₁, hpp⟩ := r3_sub_nur3_power
  refine ⟨K + C₁, by positivity, max n₀ 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have e1 := h n (le_trans (le_max_left _ _) hn)
  have e2 := hpp n hn2
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hu1 : (1 : ℝ) ≤ (1 + Real.log n) ^ 6 := one_le_pow₀ (by linarith)
  have k1 : (n : ℝ) ^ ((7 : ℝ) / 4) ≤ (n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 6 := by
    have : (n : ℝ) ^ ((7 : ℝ) / 4) ≤ (n : ℝ) ^ (2 - (1 - θ) / 17) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have h0 : 0 ≤ (n : ℝ) ^ (2 - (1 - θ) / 17) := by positivity
    nlinarith
  calc |nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n|
      = |(r3 n n - sing3 n * (n : ℝ) ^ 2 / 2) - (r3 n n - nur 3 n)| := by congr 1; ring
    _ ≤ |r3 n n - sing3 n * (n : ℝ) ^ 2 / 2| + |r3 n n - nur 3 n| := abs_sub _ _
    _ ≤ K * ((n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 6) +
          C₁ * ((n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 6) := by
        have := mul_le_mul_of_nonneg_left k1 hC₁
        linarith
    _ = (K + C₁) * ((n : ℝ) ^ (2 - (1 - θ) / 17) * (1 + Real.log n) ^ 6) := by ring


/-- **The printed bound for `47/64 ≤ Θ < 3/4`** from `PsiPowerLog3 Θ`, with `B = 6`. -/
theorem printedA3Bound_of_psiPowerLog3 {Θ : ℝ} (hΘ0 : 47 / 64 ≤ Θ) (hΘ1 : Θ < 3 / 4)
    (hψ : PsiPowerLog3 Θ) : printedA3Bound Θ := by
  obtain ⟨K, hK, n₀, h⟩ := nur3_rate3 (by linarith) (by linarith) hψ
  refine ⟨6, by norm_num, 64 * K, max n₀ 3, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hn3'
  have hm := h n (le_trans (le_max_left _ _) hn)
  have hexp : (n : ℝ) ^ (2 - (1 - Θ) / 17) ≤ (n : ℝ) ^ (2 + (Θ - 3 / 4)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hl6 : (1 + Real.log n) ^ 6 ≤ 64 * Real.log n ^ (6 : ℝ) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (1 + Real.log n) ^ 6 ≤ (2 * Real.log n) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
      _ = 64 * Real.log n ^ 6 := by ring
  calc |nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n|
      ≤ K * ((n : ℝ) ^ (2 - (1 - Θ) / 17) * (1 + Real.log n) ^ 6) := hm
    _ ≤ K * ((n : ℝ) ^ (2 + (Θ - 3 / 4)) * (64 * Real.log n ^ (6 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact mul_le_mul hexp hl6 (by positivity) (by positivity)
    _ = 64 * K * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ (6 : ℝ) := by ring

/-- **Printed Theorem A for `r = 3`, eq. 3.113 p. 21, on `47/64 ≤ Θ < 3/4`, no cited input.** -/
theorem printedA3_U1503_closed :
    ∀ Θ : ℝ, 47 / 64 ≤ Θ → Θ < 3 / 4 → NoZerosRight Θ → printedA3Bound Θ :=
  fun Θ h0 h1 hZ => printedA3Bound_of_psiPowerLog3 h0 h1
    (psiPowerLog3_of_noZeros (by linarith) (by linarith) hZ)

/-- **Printed Theorem A, eq. 3.113 p. 21, every `r ≥ 3`, every large `n`, `47/64 ≤ Θ < 3/4`, on
the paper's Hypothesis R at level `Θ`, with NO cited input.** Same statement as U-1489's
`printedA_form_all_U1489`, whose cited `TruncExplicitPrimB` is not used. -/
theorem printedA_form_all_U1503_closed :
    ∀ r : ℕ, 3 ≤ r → ∀ Θ : ℝ, 47 / 64 ≤ Θ → Θ < 3 / 4 → NoZerosRight Θ →
      ∃ B : ℕ, ∃ K : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        |nur r n - (n : ℝ) ^ (r - 1) / ((r - 1).factorial : ℝ) * singR r n| ≤
          K * (n : ℝ) ^ ((r : ℝ) - 1 + (Θ - 3 / 4)) * Real.log n ^ B := by
  intro r hr Θ h0 h1 hZ
  set θ := Θ + 1 / 128 with hθ
  have hψ := psiPowerLog_of_noZeros (by linarith) (by linarith) hZ (θ := θ) (by rw [hθ]; linarith)
  obtain ⟨B₀, hA⟩ : ∃ B : ℕ, APow r (Θ - 3 / 4) B :=
    apow_all (θ := θ) (by rw [hθ]; linarith) (by rw [hθ]; linarith) hψ
      (apow_three_of_bound (printedA3_U1503_closed Θ h0 h1 hZ)) r hr
  obtain ⟨K, hK, n₀, hn⟩ := apow_mono (le_max_left B₀ r) hA
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  refine ⟨max B₀ (s + 2), K + 3 * (s + 2) * 2 ^ s, max n₀ 3, fun n hn' => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL1 := one_le_log_of_three hn3
  have hY : (0 : ℝ) ≤ (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) := by positivity
  have hZ0 : 0 ≤ Real.log n ^ max B₀ (s + 2) := by positivity
  by_cases hpar : n % 2 = (s + 2) % 2
  · rw [← Mr_eq_printed_pos hr (by omega) hpar]
    refine (hn n hpar (le_trans (le_max_left _ _) hn')).trans ?_
    have : 0 ≤ 3 * (s + 2 : ℝ) * 2 ^ s * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
        Real.log n ^ max B₀ (s + 2) := by positivity
    nlinarith
  · rw [(singRProductPos (s + 2) hr n (by omega)).2 hpar, mul_zero, sub_zero,
      abs_of_nonneg (nur_nonneg _ _)]
    refine (nur_unlike_le s n hpar).trans ?_
    have q1 : ((n : ℝ) + 1) ^ s ≤ 2 ^ s * (n : ℝ) ^ s := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) s
    have q2 : (n : ℝ) ^ s ≤ (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) :=
      npow_le_rpow (by omega) (by push_cast; linarith)
    have q3 : Real.log n ^ (s + 2) ≤ Real.log n ^ max B₀ (s + 2) :=
      log_pow_mono hn3 (le_max_right _ _)
    have hKY : 0 ≤ K * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
        Real.log n ^ max B₀ (s + 2) := by positivity
    calc 3 * ((s : ℝ) + 2) * ((n : ℝ) + 1) ^ s * Real.log n ^ (s + 2)
        ≤ 3 * ((s : ℝ) + 2) * (2 ^ s * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4))) *
            Real.log n ^ max B₀ (s + 2) := by
          gcongr
          exact q1.trans (mul_le_mul_of_nonneg_left q2 (by positivity))
      _ ≤ (K + 3 * (s + 2) * 2 ^ s) * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
            Real.log n ^ max B₀ (s + 2) := by
          linarith only [hKY]

end LeanLab.HardyLittlewood1923.U1503
