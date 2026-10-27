module

public import LeanLab.HardyLittlewood1923.U1473Explicit

/-!
AI-written Lean code, Claude, 2026-10-22, PC run 20261022T1302Z-31860, unit U-1479, paper P0004.

# Hardy-Littlewood 1923, splitting the cited input `ExplicitFormulaPrim` of U-1473

U-1473's only cited input is `ExplicitFormulaPrim`: no zero of a primitive `L(s, χ)` right of `Θ`
gives `|ψ(x, χ) - [q = 1] x| ≤ C x^Θ (log x)²` for primitive `χ` mod `q ≤ x`.
Here it is reduced, for every `Θ ≥ 0`, which is all that the Theorem A chain uses, to TWO
standard named inputs, both textbook theorems, Davenport, Multiplicative Number Theory:

* `ZeroCountUnit`, Davenport ch. 16: for primitive `χ` mod `q` and `t ≥ 0` the nontrivial zeros
  with `t ≤ |γ| ≤ t + 1` are finitely many and number, with multiplicity `analyticOrderNatAt`,
  at most `A log (q (t + 2))`. Hardy and Littlewood's Lemma 6, eq 2.611 p. 14, is the weaker
  `M(T) < A (log (q + 1))^A log (T + 2)`.
* `TruncExplicitPrim`, Davenport ch. 17 and 19: the truncated explicit formula for primitive `χ`,
  `ψ(x, χ) = [q = 1] x - Σ_{|γ| ≤ T} m(ρ) x^ρ/ρ + R`, `2 ≤ T ≤ x`, `q ≤ x`, with
  `|R| ≤ A (x log²(qx)/T + log²(qx) + Σ_{|γ| ≤ 1} m(ρ)/|ρ|)`; the last sum absorbs the constant
  `b(χ)` and the terms `1/ρ` of the low zeros, Davenport ch. 19 eq for `b(χ)`.

PROVED, no cited input:
* `reflect_zero`: for primitive `χ`, a zero `ρ` of `L(s, χ)` in `0 < Re s < 1` gives a zero
  `1 - ρ` of `L(s, χ⁻¹)`, from Mathlib's functional equation `completedLFunction_one_sub`; this
  is Hardy and Littlewood's remark (c) p. 15.
* `zero_re_bounds`: on `NoZerosRightPrim Θ`, every such zero has `1 - Θ ≤ β ≤ Θ`.
* `sum_inv_norm_le`, the summation step: from a zero count per unit height `A L` and `δ ≤ β`,
  `Σ_{|γ| ≤ T} m(ρ)/|ρ| ≤ A L (1/δ + 1 + log (T + 1))`.
* `psiChiPrimBound_of_split`, `explicitFormulaPrimNN_of_split`, `explicitFormulaLog_of_split`,
  and the headline `printedA_form_all_U1479`, CONDITIONAL ON `ZeroCountUnit` and
  `TruncExplicitPrim`.

Every proof is complete, no axiom. Binary Goldbach is OPEN.

Packaging note: in this copy the cited Props of this file and the theorems that take them as
hypotheses were removed, as no compared theorem uses them; see PORTING.md.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923.U1479

open Real Finset
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1438 (NoZerosRight)
open LeanLab.HardyLittlewood1923.U1444 (singR)
open LeanLab.HardyLittlewood1923.U1453 (PsiPowerLog)
open LeanLab.HardyLittlewood1923.U1473 (NoZerosRightPrim PsiChiPrimBound)
open LeanLab.PNTPort.BV (psiChi)

/-! ### Zeros and multiplicities -/

/-- `ρ` is a nontrivial zero of `L(s, χ)`: `L(ρ, χ) = 0` and `0 < Re ρ < 1`. -/
def IsNTZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop :=
  DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- The multiplicity of `ρ` as a zero of `L(s, χ)`, Mathlib's `analyticOrderNatAt`. -/
noncomputable def mult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℝ :=
  (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)

lemma mult_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : 0 ≤ mult χ ρ := by
  unfold mult; positivity

/-! ### The two named analytic inputs -/

/-! ### Reflection of zeros, PROVED -/

/-- **Reflection**: for primitive `χ`, a zero `ρ` of `L(s, χ)` with `0 < Re ρ < 1` gives the zero
`1 - ρ` of `L(s, χ⁻¹)`, by the functional equation. -/
theorem reflect_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h : IsNTZero χ ρ) : IsNTZero χ⁻¹ (1 - ρ) := by
  obtain ⟨hz, h0, h1⟩ := h
  have hρ0 : ρ ≠ 0 := by intro e; rw [e] at h0; simp at h0
  have hg : DirichletCharacter.gammaFactor χ ρ ≠ 0 := by
    rcases χ.even_or_odd with he | ho
    · rw [he.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos h0
    · rw [ho.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hc : DirichletCharacter.completedLFunction χ ρ = 0 := by
    have := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ρ (Or.inl hρ0)
    rw [hz] at this
    exact (div_eq_zero_iff.1 this.symm).resolve_right hg
  have hinv : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have hfe := DirichletCharacter.IsPrimitive.completedLFunction_one_sub hinv ρ
  rw [inv_inv, hc, mul_zero] at hfe
  have h1ρ : (1 - ρ) ≠ 0 := by
    intro e
    have : (1 - ρ).re = 0 := by rw [e]; simp
    simp at this; linarith
  refine ⟨?_, by simp; linarith, by simp; linarith⟩
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - ρ) (Or.inl h1ρ), hfe,
    zero_div]

/-- On Hypothesis R for primitive characters at level `Θ`, every nontrivial zero of a primitive
`L(s, χ)` has `1 - Θ ≤ β ≤ Θ`. -/
theorem zero_re_bounds {Θ : ℝ} (hZ : NoZerosRightPrim Θ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {ρ : ℂ} (h : IsNTZero χ ρ) :
    ρ.re ≤ Θ ∧ 1 - Θ ≤ ρ.re := by
  have key : ∀ (ψ : DirichletCharacter ℂ q), ψ.IsPrimitive → ∀ σ : ℂ, IsNTZero ψ σ → σ.re ≤ Θ := by
    intro ψ hψ σ hσ
    by_contra hlt
    push_neg at hlt
    have hσ1 : σ ≠ 1 := by intro e; have := hσ.2.2; rw [e] at this; simp at this
    exact hZ q ψ hψ σ hlt hσ1 hσ.1
  refine ⟨key χ hχ ρ h, ?_⟩
  have hinv : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have := key χ⁻¹ hinv (1 - ρ) (reflect_zero hχ h)
  simp at this; linarith

/-! ### The summation step, PROVED -/

/-- Weight of the unit window `n ≤ |γ| < n + 1`: `1/δ` for `n = 0`, `1/n` otherwise. -/
noncomputable def wt (δ : ℝ) (n : ℕ) : ℝ := if n = 0 then 1 / δ else 1 / n

lemma wt_nonneg {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 ≤ wt δ n := by
  unfold wt; split_ifs <;> positivity

lemma sum_wt (δ : ℝ) (N : ℕ) : ∑ n ∈ range (N + 1), wt δ n = 1 / δ + (harmonic N : ℝ) := by
  rw [sum_range_succ', harmonic, Rat.cast_sum, add_comm]
  congr 1 <;> simp [wt]

/-- **Summation step**, abstract form: zeros `Z` with multiplicities `m ≥ 0`, real parts at least
`δ > 0`, and at most `A L` of them, with multiplicity, in each window `n ≤ |γ| ≤ n + 1`, `n ≤ T`:
then `Σ_{|γ| ≤ T} m(ρ)/|ρ| ≤ A L (1/δ + 1 + log (T + 1))`. -/
theorem sum_inv_norm_le {Z : ℂ → Prop} {m : ℂ → ℝ} (hm : ∀ ρ, 0 ≤ m ρ) {A L δ T : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hδ : 0 < δ) (hT : 0 ≤ T)
    (hcount : ∀ n : ℕ, (n : ℝ) ≤ T → ∀ s : Finset ℂ,
      (∀ ρ ∈ s, Z ρ ∧ (n : ℝ) ≤ |ρ.im| ∧ |ρ.im| ≤ n + 1) → ∑ ρ ∈ s, m ρ ≤ A * L)
    (hre : ∀ ρ, Z ρ → δ ≤ ρ.re)
    (s : Finset ℂ) (hs : ∀ ρ ∈ s, Z ρ ∧ |ρ.im| ≤ T) :
    ∑ ρ ∈ s, m ρ / ‖ρ‖ ≤ A * L * (1 / δ + 1 + Real.log (T + 1)) := by
  set N := ⌊T⌋₊ with hN
  have hmaps : ∀ ρ ∈ s, ⌊|ρ.im|⌋₊ ∈ range (N + 1) := by
    intro ρ hρ
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (hs ρ hρ).2
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ n ∈ range (N + 1),
      ∑ ρ ∈ s with ⌊|ρ.im|⌋₊ = n, m ρ / ‖ρ‖ ≤ wt δ n * (A * L) := by
    intro n hn
    have hnT : (n : ℝ) ≤ T := by
      have : n ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hn)
      exact le_trans (by exact_mod_cast this) (Nat.floor_le hT)
    have hmem : ∀ ρ ∈ s.filter (fun ρ => ⌊|ρ.im|⌋₊ = n),
        Z ρ ∧ (n : ℝ) ≤ |ρ.im| ∧ |ρ.im| ≤ n + 1 := by
      intro ρ hρ
      rw [mem_filter] at hρ
      obtain ⟨hρs, hfl⟩ := hρ
      refine ⟨(hs ρ hρs).1, ?_, ?_⟩
      · rw [← hfl]; exact Nat.floor_le (abs_nonneg _)
      · have := Nat.lt_floor_add_one (|ρ.im|)
        rw [hfl] at this; linarith
    have hpt : ∀ ρ ∈ s.filter (fun ρ => ⌊|ρ.im|⌋₊ = n), m ρ / ‖ρ‖ ≤ wt δ n * m ρ := by
      intro ρ hρ
      obtain ⟨hZρ, hlo, _⟩ := hmem ρ hρ
      have hinv : 1 / ‖ρ‖ ≤ wt δ n := by
        unfold wt
        split_ifs with h0
        · have : δ ≤ ‖ρ‖ :=
            (hre ρ hZρ).trans ((le_abs_self _).trans (Complex.abs_re_le_norm ρ))
          exact one_div_le_one_div_of_le hδ this
        · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h0
          exact one_div_le_one_div_of_le hn0 (hlo.trans (Complex.abs_im_le_norm ρ))
      rw [div_eq_mul_one_div, mul_comm (wt δ n)]
      exact mul_le_mul_of_nonneg_left hinv (hm ρ)
    calc ∑ ρ ∈ s with ⌊|ρ.im|⌋₊ = n, m ρ / ‖ρ‖
        ≤ ∑ ρ ∈ s with ⌊|ρ.im|⌋₊ = n, wt δ n * m ρ := sum_le_sum hpt
      _ = wt δ n * ∑ ρ ∈ s with ⌊|ρ.im|⌋₊ = n, m ρ := by rw [mul_sum]
      _ ≤ wt δ n * (A * L) :=
          mul_le_mul_of_nonneg_left (hcount n hnT _ hmem) (wt_nonneg hδ n)
  have hharm : (harmonic N : ℝ) ≤ 1 + Real.log (T + 1) := by
    refine (harmonic_le_one_add_log N).trans ?_
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 1)]
    · have : (N : ℝ) ≤ T + 1 := by linarith [Nat.floor_le hT]
      have := Real.log_le_log (by exact_mod_cast hpos) this
      linarith
  calc ∑ n ∈ range (N + 1), ∑ ρ ∈ s with ⌊|ρ.im|⌋₊ = n, m ρ / ‖ρ‖
      ≤ ∑ n ∈ range (N + 1), wt δ n * (A * L) := sum_le_sum hfib
    _ = (A * L) * (1 / δ + (harmonic N : ℝ)) := by rw [← sum_mul, sum_wt, mul_comm]
    _ ≤ A * L * (1 / δ + 1 + Real.log (T + 1)) := by
        have : 0 ≤ A * L := mul_nonneg hA hL
        nlinarith

/-! ### Assembly -/

/-- `PsiChiPrimBound` is monotone in `Θ`. -/
theorem psiChiPrimBound_mono {Θ Θ' : ℝ} (hle : Θ ≤ Θ') (h : PsiChiPrimBound Θ) :
    PsiChiPrimBound Θ' := by
  obtain ⟨C, hC, hP⟩ := h
  refine ⟨C, hC, fun q χ hq hp x hx hqx => (hP q χ hq hp x hx hqx).trans ?_⟩
  have : x ^ Θ ≤ x ^ Θ' := Real.rpow_le_rpow_of_exponent_le (by linarith) hle
  have hL : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  gcongr

/-! ### Vacuity -/

/-- The hypotheses of the summation step are satisfiable with a NONEMPTY zero set: one zero at
`1/2` of multiplicity 1, `A = L = 1`, `δ = 1/2`, `T = 0`. -/
theorem sum_inv_norm_le_nonvacuous :
    (∀ n : ℕ, (n : ℝ) ≤ 0 → ∀ s : Finset ℂ,
      (∀ ρ ∈ s, ρ = (1 / 2 : ℂ) ∧ (n : ℝ) ≤ |ρ.im| ∧ |ρ.im| ≤ n + 1) →
        ∑ ρ ∈ s, (fun _ => (1 : ℝ)) ρ ≤ 1 * 1) ∧
    (∀ ρ : ℂ, ρ = (1 / 2 : ℂ) → (1 / 2 : ℝ) ≤ ρ.re) ∧
    (∀ ρ ∈ ({(1 / 2 : ℂ)} : Finset ℂ), ρ = (1 / 2 : ℂ) ∧ |ρ.im| ≤ 0) ∧
    ({(1 / 2 : ℂ)} : Finset ℂ).Nonempty := by
  refine ⟨fun n _ s hs => ?_, fun ρ h => by rw [h]; norm_num, fun ρ h => ?_, singleton_nonempty _⟩
  · have hsub : s ⊆ {(1 / 2 : ℂ)} := fun ρ hρ => mem_singleton.2 (hs ρ hρ).1
    simp only [sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast card_le_card hsub
  · rw [mem_singleton] at h; subst h; simp

/-- The Θ range of the headline meets the hypothesis of the reduction: `47/64 ≥ 0` and `< 1`, so
`psiChiPrimBound_of_split` applies there, its premise `NoZerosRightPrim Θ` being implied by GRH. -/
theorem split_range_ok : (0 : ℝ) ≤ 47 / 64 ∧ (47 : ℝ) / 64 < 1 := by
  constructor <;> norm_num

end LeanLab.HardyLittlewood1923.U1479
