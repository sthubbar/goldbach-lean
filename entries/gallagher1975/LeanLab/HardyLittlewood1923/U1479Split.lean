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

No placeholder proof, no axiom. Binary Goldbach is OPEN.
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

/-- **Cited**, Davenport ch. 16: zero count per unit height for primitive characters,
`N(t + 1, χ) - N(t, χ) ≪ log q (t + 2)` in symmetric form, with finiteness of the window. -/
def ZeroCountUnit : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ t : ℝ, 0 ≤ t →
      {ρ : ℂ | IsNTZero χ ρ ∧ t ≤ |ρ.im| ∧ |ρ.im| ≤ t + 1}.Finite ∧
      ∀ s : Finset ℂ, (∀ ρ ∈ s, IsNTZero χ ρ ∧ t ≤ |ρ.im| ∧ |ρ.im| ≤ t + 1) →
        ∑ ρ ∈ s, mult χ ρ ≤ A * Real.log (q * (t + 2))

/-- **Cited**, Davenport ch. 17 and 19: the truncated explicit formula for primitive `χ`, the sum
over the nontrivial zeros with `|γ| ≤ T`, with multiplicity, given as any finset `s` equal to that
zero set. -/
def TruncExplicitPrim : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ x T : ℝ, 2 ≤ x → 2 ≤ T → T ≤ x → (q : ℝ) ≤ x →
    ∀ s : Finset ℂ, (∀ ρ, ρ ∈ s ↔ IsNTZero χ ρ ∧ |ρ.im| ≤ T) →
      ‖psiChi x χ - (if q = 1 then (x : ℂ) else 0) +
          ∑ ρ ∈ s, (mult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        A * (x * Real.log (q * x) ^ 2 / T + Real.log (q * x) ^ 2 +
          ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 1), mult χ ρ / ‖ρ‖)

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

/-- The zero set up to height `x` is finite, from `ZeroCountUnit`; a finset with exactly these
members exists, so the premise of `TruncExplicitPrim` is satisfiable. -/
theorem exists_zero_finset (hN : ZeroCountUnit) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    ∃ s : Finset ℂ, ∀ ρ, ρ ∈ s ↔ IsNTZero χ ρ ∧ |ρ.im| ≤ T := by
  obtain ⟨A, _, hA⟩ := hN
  have hsub : {ρ : ℂ | IsNTZero χ ρ ∧ |ρ.im| ≤ T} ⊆
      ⋃ n ∈ range (⌊T⌋₊ + 1), {ρ : ℂ | IsNTZero χ ρ ∧ (n : ℝ) ≤ |ρ.im| ∧ |ρ.im| ≤ n + 1} := by
    intro ρ ⟨hz, hle⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, mem_range]
    refine ⟨⌊|ρ.im|⌋₊, Nat.lt_succ_iff.2 (Nat.floor_le_floor hle), hz,
      Nat.floor_le (abs_nonneg _), (Nat.lt_floor_add_one _).le⟩
  have hfin : {ρ : ℂ | IsNTZero χ ρ ∧ |ρ.im| ≤ T}.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion (finite_toSet _) fun n _ => ?_) hsub
    exact (hA q χ hχ n (Nat.cast_nonneg n)).1
  exact ⟨hfin.toFinset, fun ρ => by simp⟩

/-- **`PsiChiPrimBound Θ` for `0 ≤ Θ < 1` from the two named inputs**, with the summation step
and the reflection PROVED. -/
theorem psiChiPrimBound_of_split (hN : ZeroCountUnit) (hE : TruncExplicitPrim) {Θ : ℝ}
    (hΘ0 : 0 ≤ Θ) (hΘ1 : Θ < 1) (hZ : NoZerosRightPrim Θ) : PsiChiPrimBound Θ := by
  obtain ⟨A1, hA1, hcnt⟩ := id hN
  obtain ⟨A2, hA2, hexp⟩ := hE
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set δ : ℝ := 1 - Θ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set c1 : ℝ := (1 / δ + 1) / Real.log 2 + 2 with hc1
  have hc1n : 0 ≤ c1 := by rw [hc1]; positivity
  set Sb : ℝ := 3 * A1 * c1 with hSb
  have hSbn : 0 ≤ Sb := by rw [hSb]; positivity
  refine ⟨Sb + A2 * (8 + Sb), by positivity, fun q χ hq hprim x hx hqx => ?_⟩
  haveI : NeZero q := ⟨by omega⟩
  have hx0 : 0 < x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx0 : 0 ≤ Real.log x := hl2.le.trans hlx
  obtain ⟨s, hs⟩ := exists_zero_finset hN hprim hx0.le
  -- the summation step at `T = x`
  set S : ℝ := ∑ ρ ∈ s, mult χ ρ / ‖ρ‖ with hSdef
  have hLq : 0 ≤ Real.log (q * (x + 2)) := Real.log_nonneg (by nlinarith)
  have hS1 : S ≤ A1 * Real.log (q * (x + 2)) * (1 / δ + 1 + Real.log (x + 1)) := by
    refine sum_inv_norm_le (Z := IsNTZero χ) (mult_nonneg χ) hA1 hLq hδ hx0.le ?_ ?_ s
      (fun ρ hρ => (hs ρ).1 hρ)
    · intro n hn s' hs'
      refine ((hcnt q χ hprim n (Nat.cast_nonneg n)).2 s' hs').trans ?_
      refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hA1
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    · intro ρ hρ
      have := (zero_re_bounds hZ hprim hρ).2
      rw [hδdef]; exact this
  have hlog3 : Real.log (q * (x + 2)) ≤ 3 * Real.log x := by
    rw [← Real.log_rpow hx0]
    refine Real.log_le_log (by positivity) ?_
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h1 : (q : ℝ) * (x + 2) ≤ x * (x + 2) := mul_le_mul_of_nonneg_right hqx (by linarith)
    have h2 : x * (x + 2) ≤ x ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ x - 2))
        (by linarith : (0 : ℝ) ≤ x + 1)]
    linarith
  have hlog1 : Real.log (x + 1) ≤ 2 * Real.log x := by
    rw [← Real.log_rpow hx0]
    refine Real.log_le_log (by positivity) ?_
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ x + 1)]
  have hfac : 1 / δ + 1 + Real.log (x + 1) ≤ c1 * Real.log x := by
    have h1 : 1 / δ + 1 ≤ (1 / δ + 1) / Real.log 2 * Real.log x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlx (by positivity)
    rw [hc1]; nlinarith
  have hS : S ≤ Sb * Real.log x ^ 2 := by
    refine hS1.trans ?_
    calc A1 * Real.log (q * (x + 2)) * (1 / δ + 1 + Real.log (x + 1))
        ≤ A1 * (3 * Real.log x) * (c1 * Real.log x) := by
          have hF0 : 0 ≤ 1 / δ + 1 + Real.log (x + 1) := by
            have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ x + 1)
            have := one_div_pos.2 hδ
            linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left hlog3 hA1) hfac hF0
            (mul_nonneg hA1 (by linarith))
      _ = Sb * Real.log x ^ 2 := by rw [hSb]; ring
  have hS0 : 0 ≤ S := sum_nonneg fun ρ _ => div_nonneg (mult_nonneg χ ρ) (norm_nonneg _)
  -- the explicit formula at `T = x`
  have hE1 := hexp q χ hprim x x hx hx le_rfl hqx s hs
  have hsmall : ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 1), mult χ ρ / ‖ρ‖ ≤ S :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun ρ _ _ => div_nonneg (mult_nonneg χ ρ) (norm_nonneg _)
  have hlqx : Real.log (q * x) ^ 2 ≤ 4 * Real.log x ^ 2 := by
    have h0 : 0 ≤ Real.log (q * x) := Real.log_nonneg (by nlinarith)
    have h1 : Real.log (q * x) ≤ 2 * Real.log x := by
      rw [← Real.log_rpow hx0]
      refine Real.log_le_log (by positivity) ?_
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      nlinarith
    nlinarith
  have hxx : x * Real.log (q * x) ^ 2 / x = Real.log (q * x) ^ 2 := by field_simp
  have hR : ‖psiChi x χ - (if q = 1 then (x : ℂ) else 0) +
      ∑ ρ ∈ s, (mult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤ A2 * (8 * Real.log x ^ 2 + S) := by
    refine hE1.trans ?_
    rw [hxx]
    exact mul_le_mul_of_nonneg_left (by linarith) hA2
  -- the zero sum
  have hxΘ : 1 ≤ x ^ Θ := Real.one_le_rpow (by linarith) hΘ0
  have hZs : ‖∑ ρ ∈ s, (mult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤ x ^ Θ * S := by
    refine (norm_sum_le _ _).trans ?_
    rw [hSdef, mul_sum]
    refine sum_le_sum fun ρ hρ => ?_
    have hre := (zero_re_bounds hZ hprim ((hs ρ).1 hρ).1).1
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mult_nonneg χ ρ),
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hp : x ^ ρ.re ≤ x ^ Θ := Real.rpow_le_rpow_of_exponent_le (by linarith) hre
    rw [mul_div_assoc]
    have h1 : 0 ≤ mult χ ρ / ‖ρ‖ := div_nonneg (mult_nonneg χ ρ) (norm_nonneg _)
    calc mult χ ρ * (x ^ ρ.re / ‖ρ‖) = x ^ ρ.re * (mult χ ρ / ‖ρ‖) := by ring
      _ ≤ x ^ Θ * (mult χ ρ / ‖ρ‖) := mul_le_mul_of_nonneg_right hp h1
  have hL2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  calc ‖psiChi x χ - (if q = 1 then (x : ℂ) else 0)‖
      = ‖(psiChi x χ - (if q = 1 then (x : ℂ) else 0) +
          ∑ ρ ∈ s, (mult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
          ∑ ρ ∈ s, (mult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ := by ring_nf
    _ ≤ A2 * (8 * Real.log x ^ 2 + S) + x ^ Θ * S := (norm_sub_le _ _).trans (add_le_add hR hZs)
    _ ≤ A2 * (8 * Real.log x ^ 2 + Sb * Real.log x ^ 2) + x ^ Θ * (Sb * Real.log x ^ 2) := by
        gcongr
    _ = (A2 * (8 + Sb)) * Real.log x ^ 2 + Sb * x ^ Θ * Real.log x ^ 2 := by ring
    _ ≤ (A2 * (8 + Sb)) * (x ^ Θ * Real.log x ^ 2) + Sb * x ^ Θ * Real.log x ^ 2 := by
        have h := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hL2 hxΘ)
          (mul_nonneg hA2 (by linarith : (0 : ℝ) ≤ 8 + Sb))
        linarith
    _ = (Sb + A2 * (8 + Sb)) * x ^ Θ * Real.log x ^ 2 := by ring

/-- `PsiChiPrimBound` is monotone in `Θ`. -/
theorem psiChiPrimBound_mono {Θ Θ' : ℝ} (hle : Θ ≤ Θ') (h : PsiChiPrimBound Θ) :
    PsiChiPrimBound Θ' := by
  obtain ⟨C, hC, hP⟩ := h
  refine ⟨C, hC, fun q χ hq hp x hx hqx => (hP q χ hq hp x hx hqx).trans ?_⟩
  have : x ^ Θ ≤ x ^ Θ' := Real.rpow_le_rpow_of_exponent_le (by linarith) hle
  have hL : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  gcongr

/-- **U-1473's `ExplicitFormulaPrim` for every `Θ ≥ 0`, CONDITIONAL ON `ZeroCountUnit` and
`TruncExplicitPrim`**. For `Θ ≥ 1` it is U-1473's unconditional `psiChiPrimBound_one`. -/
theorem explicitFormulaPrimNN_of_split (hN : ZeroCountUnit) (hE : TruncExplicitPrim) :
    ∀ Θ : ℝ, 0 ≤ Θ → NoZerosRightPrim Θ → PsiChiPrimBound Θ := by
  intro Θ hΘ0 hZ
  rcases lt_or_ge Θ 1 with h1 | h1
  · exact psiChiPrimBound_of_split hN hE hΘ0 h1 hZ
  · exact psiChiPrimBound_mono h1 U1473.psiChiPrimBound_one

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
