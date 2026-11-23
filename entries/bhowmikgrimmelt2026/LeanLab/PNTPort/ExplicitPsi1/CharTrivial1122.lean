module

public import LeanLab.Linnik.ExplicitFormula.LeftHalf
public import LeanLab.PNTPort.ExplicitPsi1.Residues
public import LeanLab.PNTPort.StrongPNT.StrongPNT

/-!
# Trivial zeros of a primitive `L(s, χ)` and their residues in the sharp kernel

Unit P1122-0016, ROUTE BURST burst-20261122 session S2, port step 5 of the half weighted
truncated explicit formula for primitive nonprincipal `χ`, Davenport, Multiplicative Number
Theory, second edition, chapter 19, pages 115 to 118. AI wrote the Lean code. Binary Goldbach
is OPEN; nothing here bears on it directly.

Let `χ` be primitive modulo `q`, `χ ≠ 1`, with parity `a`, `χ(-1) = (-1)^a`, `a ∈ {0, 1}`.
The sharp kernel integrand is `-(L'/L)(s, χ) xˢ/s`, written inline.

* `LFunction_eq_mul_trivial`: for every `k ≥ 0`, `L(s, χ) = (s + a + 2k) v(s)` with `v` entire
  and `v(-a - 2k) ≠ 0`; Davenport ch. 9, `Λ(s, χ) = (q/π)^{(s+a)/2} Γ((s+a)/2) L(s, χ)` with
  `Λ` nonvanishing on `Re s ≤ 0` by the functional equation.
* `LFunction_eq_zero_iff_of_re_nonpos`: on `Re s ≤ 0` the zeros are exactly `-a - 2k`,
  `k ≥ 0`; for `a = 0` this includes `s = 0`. `analyticOrderAt_trivial`: all are simple.
* `tendsto_mul_logDeriv_trivial`: `(s + m) L'/L(s) → 1` at `s = -m`, `m = a + 2k`.
* `residue_trivial_char`: the residue of the integrand at a trivial zero `-m`, `m > 0`, is
  `x^{-m}/m`, Davenport p. 115 display (2) and p. 116 display (3).
* `residue_zero_odd`: for `a = 1` the residue at `0` is `-L'(0, χ)/L(0, χ)`, p. 115 (2).
* `laurent_zero_even`: for `a = 0`, with `b(χ)` the constant term of `L'/L` at `0`, the
  coefficient of `1/s` of the integrand at `0` is `-(log x + b(χ))`, p. 116.
* `hasSum_trivial_even`, `hasSum_trivial_odd`, `trivial_sum_le`: the sums over the trivial zeros
  are `-(1/2) log(1 - x⁻²)` and `(1/2) log((1 + x⁻¹)/(1 - x⁻¹))`, both at most `1/(x - 1)`.
* LEAF `b_regroup_leaf`, HARD, see its doc for a cheaper route: Davenport p. 118, `b(χ) = -Σ_{|γ|<1} 1/ρ + O(log q)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122

open Complex Filter Topology Set
open scoped Real

/-- The gamma factor of `χ` with parity `a` is `Γℝ(s + a)`. Davenport ch. 9, p. 71. -/
theorem gammaFactor_eq_parity {q : ℕ} {χ : DirichletCharacter ℂ q} {a : ℕ}
    (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1)) (s : ℂ) :
    DirichletCharacter.gammaFactor χ s = Gammaℝ (s + a) := by
  rcases ha with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · rw [h.gammaFactor_def]; simp
  · rw [h.gammaFactor_def]; simp

/-- The Gamma recurrence iterated, valid at the poles as well:
`1/Γ(w) = w (w + 1) ... (w + k) / Γ(w + k + 1)`. -/
theorem inv_Gamma_eq_prod (k : ℕ) (w : ℂ) :
    (Gamma w)⁻¹ = (∏ j ∈ Finset.range (k + 1), (w + j)) * (Gamma (w + ((k : ℂ) + 1)))⁻¹ := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.prod_singleton, Nat.cast_zero, add_zero]
    exact one_div_Gamma_eq_self_mul_one_div_Gamma_add_one w
  | succ k ih =>
    rw [ih, one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (w + ((k : ℂ) + 1)),
      Finset.prod_range_succ _ (k + 1)]
    have e : w + ((k : ℂ) + 1) + 1 = w + (((k + 1 : ℕ) : ℂ) + 1) := by push_cast; ring
    rw [e]
    push_cast
    ring

/-- `χ ≠ 1` forces the modulus to differ from `1`. -/
lemma modulus_ne_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) : q ≠ 1 :=
  hχ ∘ DirichletCharacter.level_one' χ

/-- Davenport ch. 9: `L(s, χ) = Λ(s, χ) / Γℝ(s + a)`, with Mathlib's convention that
`1/Γℝ` vanishes at the poles, valid for every `s`. -/
theorem LFunction_eq_completed_mul_inv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1)) (s : ℂ) :
    DirichletCharacter.LFunction χ s =
      DirichletCharacter.completedLFunction χ s * (Gammaℝ (s + a))⁻¹ := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr (modulus_ne_one hχ)),
    gammaFactor_eq_parity ha, div_eq_mul_inv]

/-- **The trivial zeros, factored.** Davenport ch. 9 and ch. 19 p. 115: for primitive
`χ ≠ 1` of parity `a` and every `k ≥ 0`, `L(s, χ) = (s + a + 2k) v(s)` with `v` entire and
`v(-a - 2k) ≠ 0`. For `a = 0`, `k = 0` this is the simple zero at `s = 0`. -/
theorem LFunction_eq_mul_trivial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    (k : ℕ) :
    ∃ v : ℂ → ℂ, Differentiable ℂ v ∧ v (-((a : ℂ) + 2 * k)) ≠ 0 ∧
      ∀ s, DirichletCharacter.LFunction χ s = (s + ((a : ℂ) + 2 * k)) * v s := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨fun s => DirichletCharacter.completedLFunction χ s *
      ((π : ℂ) ^ ((s + a) / 2) * ((∏ j ∈ Finset.range k, ((s + a) / 2 + j)) *
        ((1 / 2) * (Gamma ((s + a) / 2 + ((k : ℂ) + 1)))⁻¹))), ?_, ?_, ?_⟩
  · have hΛ := DirichletCharacter.differentiable_completedLFunction hχ
    have h1 : Differentiable ℂ fun s : ℂ => (s + a) / 2 :=
      (differentiable_id.add_const _).div_const _
    have hp : Differentiable ℂ fun s : ℂ => (π : ℂ) ^ ((s + a) / 2) :=
      fun s => (h1 s).const_cpow (Or.inl hπ)
    have hprod : Differentiable ℂ fun s : ℂ => ∏ j ∈ Finset.range k, ((s + a) / 2 + j) := by
      fun_prop
    have hg : Differentiable ℂ fun s : ℂ => (Gamma ((s + a) / 2 + ((k : ℂ) + 1)))⁻¹ :=
      differentiable_one_div_Gamma.comp (h1.add_const _)
    exact hΛ.mul (hp.mul (hprod.mul (hg.const_mul _)))
  · have hre : (-((a : ℂ) + 2 * k)).re ≤ 0 := by
      rw [show (-((a : ℂ) + 2 * k)) = ((-((a : ℝ) + 2 * k) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
      have := (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    have hΛ := LeanLab.Linnik.ExplicitFormula.completed_ne_zero_of_re_nonpos hprim hre (Or.inr hχ)
    have hw : (-((a : ℂ) + 2 * k) + a) / 2 = -(k : ℂ) := by ring
    simp only [hw]
    refine mul_ne_zero hΛ (mul_ne_zero ?_ (mul_ne_zero ?_ (mul_ne_zero (by norm_num) ?_)))
    · exact cpow_ne_zero_iff.mpr (Or.inl hπ)
    · rw [Finset.prod_ne_zero_iff]
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      intro h
      have : ((j : ℤ) : ℂ) = ((k : ℤ) : ℂ) := by push_cast; linear_combination h
      have := Int.cast_injective this
      omega
    · rw [show -(k : ℂ) + ((k : ℂ) + 1) = 1 by ring, Gamma_one, inv_one]
      exact one_ne_zero
  · intro s
    rw [LFunction_eq_completed_mul_inv hχ ha, Gammaℝ_def, mul_inv, ← cpow_neg,
      show -(-(s + a) / 2) = (s + a) / 2 by ring, inv_Gamma_eq_prod k ((s + a) / 2),
      Finset.prod_range_succ]
    ring

/-- **The zeros on `Re s ≤ 0`.** Davenport ch. 19 p. 115 and ch. 9: for primitive `χ ≠ 1` of
parity `a`, a point with `Re s ≤ 0` is a zero of `L(s, χ)` exactly when `s = -a - 2k`,
`k ≥ 0`. For `a = 0` this includes `s = 0`. -/
theorem LFunction_eq_zero_iff_of_re_nonpos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    {s : ℂ} (hs : s.re ≤ 0) :
    DirichletCharacter.LFunction χ s = 0 ↔ ∃ k : ℕ, s = -((a : ℂ) + 2 * k) := by
  constructor
  · intro h0
    rw [LFunction_eq_completed_mul_inv hχ ha] at h0
    have hΛ := LeanLab.Linnik.ExplicitFormula.completed_ne_zero_of_re_nonpos hprim hs (Or.inr hχ)
    have hg : Gammaℝ (s + a) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hΛ
      · exact inv_eq_zero.mp h
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hg
    exact ⟨n, by linear_combination hn⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨v, -, -, hv⟩ := LFunction_eq_mul_trivial hprim hχ ha k
    rw [hv]; simp

/-- **The trivial zeros are simple.** Davenport ch. 19 p. 115: `L(s, χ)` has analytic order
exactly one at `s = -a - 2k` for every `k ≥ 0`. -/
theorem analyticOrderAt_trivial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    (k : ℕ) :
    analyticOrderAt (DirichletCharacter.LFunction χ) (-((a : ℂ) + 2 * k)) = 1 ∧
      analyticOrderNatAt (DirichletCharacter.LFunction χ) (-((a : ℂ) + 2 * k)) = 1 := by
  obtain ⟨v, hvd, hv0, hv⟩ := LFunction_eq_mul_trivial hprim hχ ha k
  set p : ℂ := -((a : ℂ) + 2 * k) with hp
  have hL : DirichletCharacter.LFunction χ = fun s => (s + ((a : ℂ) + 2 * k)) * v s := funext hv
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) p :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt p
  have hz : DirichletCharacter.LFunction χ p = 0 := by rw [hv, hp]; ring
  have hd : HasDerivAt (DirichletCharacter.LFunction χ) (1 * v p + (p + ((a : ℂ) + 2 * k)) *
      deriv v p) p := by
    rw [hL]
    exact ((hasDerivAt_id p).add_const _).mul (hvd p).hasDerivAt
  have hd' : deriv (DirichletCharacter.LFunction χ) p ≠ 0 := by
    have hp' : p + ((a : ℂ) + 2 * k) = 0 := by rw [hp]; ring
    rw [hd.deriv, hp']; simpa using hv0
  have ho := hA.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hd'
  exact ⟨ho, by simp [analyticOrderNatAt, ho]⟩

/-- Davenport ch. 19 p. 115: near a trivial zero `-m`, `m = a + 2k`,
`L'/L(s) = 1/(s + m) + v'/v(s)` with `v` from `LFunction_eq_mul_trivial`, so
`L'/L(s) - 1/(s + m)` has a finite limit. For `m = 0`, `a = 0`, the limit is the constant
`b(χ)` of p. 116. -/
theorem tendsto_logDeriv_sub_trivial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    (k : ℕ) :
    ∃ c : ℂ, Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s - 1 / (s + ((a : ℂ) + 2 * k)))
      (𝓝[≠] (-((a : ℂ) + 2 * k))) (𝓝 c) := by
  obtain ⟨v, hvd, hv0, hv⟩ := LFunction_eq_mul_trivial hprim hχ ha k
  set p : ℂ := -((a : ℂ) + 2 * k) with hp
  have hL : DirichletCharacter.LFunction χ = fun s => (s + ((a : ℂ) + 2 * k)) * v s := funext hv
  have hva : AnalyticAt ℂ v p := hvd.analyticAt p
  refine ⟨deriv v p / v p, ?_⟩
  have hc : ContinuousAt (fun s => deriv v s / v s) p :=
    hva.deriv.continuousAt.div hva.continuousAt hv0
  have hne : ∀ᶠ s in 𝓝 p, v s ≠ 0 := hva.continuousAt.eventually_ne hv0
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds hne, self_mem_nhdsWithin] with s hs hsp
  have hsm : s + ((a : ℂ) + 2 * k) ≠ 0 := by
    intro h; apply hsp; show s = p; rw [hp]; linear_combination h
  have hd : deriv (DirichletCharacter.LFunction χ) s =
      1 * v s + (s + ((a : ℂ) + 2 * k)) * deriv v s := by
    rw [hL]; exact (((hasDerivAt_id s).add_const _).mul (hvd s).hasDerivAt).deriv
  rw [hd, hL]
  field_simp
  ring

/-- **Residue of `L'/L` at a trivial zero.** Davenport ch. 19 p. 115:
`(s + m) L'/L(s) → 1` as `s → -m`, `m = a + 2k`, the trivial zeros being simple. -/
theorem tendsto_mul_logDeriv_trivial {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    (k : ℕ) :
    Tendsto (fun s => (s + ((a : ℂ) + 2 * k)) * (deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s)) (𝓝[≠] (-((a : ℂ) + 2 * k))) (𝓝 1) := by
  obtain ⟨c, hc⟩ := tendsto_logDeriv_sub_trivial hprim hχ ha k
  set p : ℂ := -((a : ℂ) + 2 * k) with hp
  have h0 : Tendsto (fun s : ℂ => s + ((a : ℂ) + 2 * k)) (𝓝[≠] p) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s + ((a : ℂ) + 2 * k)) (𝓝 p) (𝓝 (p + ((a : ℂ) + 2 * k))) :=
      (continuous_id.add continuous_const).tendsto p
    rw [hp, neg_add_cancel] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := (h0.mul hc).const_add 1
  rw [zero_mul, add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hsp
  have hsm : s + ((a : ℂ) + 2 * k) ≠ 0 := by
    intro h; apply hsp; show s = p; rw [hp]; linear_combination h
  field_simp
  ring

/-- **Residue at a trivial zero.** Davenport ch. 19 p. 115 display (2) and p. 116 display (3):
for `x > 0` and a trivial zero `-m`, `m = a + 2k > 0`, the residue of the sharp kernel integrand
`-(L'/L)(s, χ) xˢ/s` is `x^{-m}/m`. -/
theorem residue_trivial_char {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1))
    (k : ℕ) (hm : a + 2 * k ≠ 0) {x : ℝ} (hx : 0 < x) :
    residue (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) (-((a : ℂ) + 2 * k)) =
      (x : ℂ) ^ (-((a : ℂ) + 2 * k)) / ((a : ℂ) + 2 * k) := by
  set p : ℂ := -((a : ℂ) + 2 * k) with hp
  have hp0 : p ≠ 0 := by
    rw [hp, neg_ne_zero]
    have : ((a + 2 * k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    simpa using this
  apply residue_eq_of_tendsto
  have hk : Tendsto (fun s : ℂ => (x : ℂ) ^ s / s) (𝓝[≠] p) (𝓝 ((x : ℂ) ^ p / p)) :=
    (((analyticAt_xpow hx p).div analyticAt_id hp0).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  have h := ((tendsto_mul_logDeriv_trivial hprim hχ ha k).mul hk).neg
  have hv : -(1 * ((x : ℂ) ^ p / p)) = (x : ℂ) ^ p / ((a : ℂ) + 2 * k) := by
    rw [hp]; field_simp
  rw [hv] at h
  refine h.congr' (Eventually.of_forall fun s => ?_)
  ring

/-- **Residue at `0`, odd case.** Davenport ch. 19 p. 115 display (2): for `a = 1`,
`L(0, χ) ≠ 0` and the residue of `-(L'/L)(s, χ) xˢ/s` at `0` is `-L'(0, χ)/L(0, χ)`. -/
theorem residue_zero_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (hodd : χ.Odd) {x : ℝ} (hx : 0 < x) :
    DirichletCharacter.LFunction χ 0 ≠ 0 ∧
    residue (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) 0 =
      -(deriv (DirichletCharacter.LFunction χ) 0 / DirichletCharacter.LFunction χ 0) := by
  have ha : (χ.Even ∧ (1 : ℕ) = 0) ∨ (χ.Odd ∧ (1 : ℕ) = 1) := Or.inr ⟨hodd, rfl⟩
  have hL0 : DirichletCharacter.LFunction χ 0 ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := (LFunction_eq_zero_iff_of_re_nonpos hprim hχ ha (by simp)).mp h
    have := congr_arg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  refine ⟨hL0, ?_⟩
  apply residue_eq_of_tendsto
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) 0 :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt 0
  have hH : ContinuousAt (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s) 0 :=
    ((hA.deriv.continuousAt.div hA.continuousAt hL0).neg).mul
      (analyticAt_xpow hx 0).continuousAt
  have ht := hH.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  simp only [cpow_zero, mul_one] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  rw [sub_zero]
  field_simp

/-- **The constant `b(χ)` exists, even case.** Davenport ch. 19 p. 116: for `a = 0` the zero
at `0` is simple, so `L'/L(s) = 1/s + b(χ) + O(s)`; here `b(χ)` is the limit of
`L'/L(s) - 1/s`. -/
theorem exists_b_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (heven : χ.Even) :
    ∃ b : ℂ, Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b) := by
  obtain ⟨c, hc⟩ := tendsto_logDeriv_sub_trivial hprim hχ
    (a := 0) (Or.inl ⟨heven, rfl⟩) 0
  refine ⟨c, ?_⟩
  simpa using hc

/-- **The double pole at `0`, even case.** Davenport ch. 19 p. 116: for `a = 0` and `x > 0`,
with `b(χ)` the constant term of `L'/L` at `0`, `s · (-(L'/L)(s, χ) xˢ/s) + 1/s →
-(log x + b(χ))`: the coefficient of `1/s` in the Laurent expansion of the integrand at `0` is
`-(log x + b(χ))`, from `xˢ/s = 1/s + log x + ...`. -/
theorem laurent_zero_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {b : ℂ} (hb : Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b)) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s => s * (-(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s) + 1 / s) (𝓝[≠] 0)
      (𝓝 (-((Real.log x : ℂ) + b))) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hD : HasDerivAt (fun s : ℂ => (x : ℂ) ^ s) ((x : ℂ) ^ (0 : ℂ) * Complex.log x * 1) 0 :=
    (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl hx0)
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (ofReal_log hx.le).symm
  rw [cpow_zero, one_mul, mul_one, hlog] at hD
  have hslope := hD.tendsto_slope_zero
  simp only [zero_add, cpow_zero, smul_eq_mul] at hslope
  have hxs : Tendsto (fun s : ℂ => (x : ℂ) ^ s) (𝓝[≠] 0) (𝓝 1) := by
    have := ((analyticAt_xpow hx 0).continuousAt.tendsto).mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    simpa using this
  have h := ((hb.mul hxs).neg).sub hslope
  rw [mul_one, show -b - (Real.log x : ℂ) = -((Real.log x : ℂ) + b) by ring] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  field_simp
  ring

/-- The same statement with the lab's `residue`: after removing the principal part `-1/s²`,
the residue of the sharp kernel integrand at `0` is `-(log x + b(χ))`, Davenport ch. 19
p. 116. -/
theorem residue_zero_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {b : ℂ} (hb : Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b)) {x : ℝ} (hx : 0 < x) :
    residue (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s / s + 1 / s ^ 2) 0 =
      -((Real.log x : ℂ) + b) := by
  apply residue_eq_of_tendsto
  refine (laurent_zero_even hb hx).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  rw [sub_zero]
  field_simp

/-! ### The sums over the trivial zeros, Davenport ch. 19 p. 115 (2) and p. 116 (3) -/

/-- The residue `x^{-n}/n` is the real number `x⁻ⁿ/n`. -/
lemma trivial_term_eq (x : ℝ) (n : ℕ) :
    (x : ℂ) ^ (-(n : ℂ)) / (n : ℂ) = (((x⁻¹) ^ n / n : ℝ) : ℂ) := by
  rw [cpow_neg, cpow_natCast]
  push_cast
  rw [inv_pow]

/-- The even case: `Σ_{k ≥ 0} x^{-(2k+2)}/(2k+2) = -(1/2) log(1 - x⁻²)` for `x > 1`. -/
theorem hasSum_trivial_even_real {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (x⁻¹) ^ (2 * k + 2) / ((2 * k + 2 : ℕ) : ℝ))
      (-(1 / 2) * Real.log (1 - (x⁻¹) ^ 2)) := by
  have hu0 : 0 < x⁻¹ := inv_pos.mpr (by linarith)
  have hu1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hy : |(x⁻¹) ^ 2| < 1 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hy).mul_left (1 / 2)
  rw [show (1 / 2 : ℝ) * -Real.log (1 - (x⁻¹) ^ 2) = -(1 / 2) * Real.log (1 - (x⁻¹) ^ 2) by
    ring] at h
  convert h using 1
  funext k
  rw [← pow_mul, show 2 * (k + 1) = 2 * k + 2 by ring]
  push_cast
  field_simp

/-- The odd case: `Σ_{k ≥ 0} x^{-(2k+1)}/(2k+1) = (1/2)(log(1 + x⁻¹) - log(1 - x⁻¹))` for
`x > 1`. -/
theorem hasSum_trivial_odd_real {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (x⁻¹) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))
      ((1 / 2) * (Real.log (1 + x⁻¹) - Real.log (1 - x⁻¹))) := by
  have hu0 : 0 < x⁻¹ := inv_pos.mpr (by linarith)
  have hu1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hy : |x⁻¹| < 1 := by rw [abs_of_pos hu0]; exact hu1
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hy).mul_left (1 / 2)
  convert h using 1
  funext k
  push_cast
  field_simp

/-- **The trivial zero series, even character.** Davenport ch. 19 p. 116 display (3):
for `x > 1`, `Σ_{k ≥ 0} x^{-(2k+2)}/(2k+2) = -(1/2) log(1 - x⁻²)`, the sum of the residues
`residue_trivial_char` at the trivial zeros `-2(k+1)` for `a = 0`. -/
theorem hasSum_trivial_even {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (x : ℂ) ^ (-((0 : ℕ) + 2 * ((k + 1 : ℕ) : ℂ))) /
        ((0 : ℕ) + 2 * ((k + 1 : ℕ) : ℂ)))
      ((-(1 / 2) * Real.log (1 - (x⁻¹) ^ 2) : ℝ) : ℂ) := by
  refine (Complex.hasSum_ofReal.mpr (hasSum_trivial_even_real hx)).congr_fun ?_
  intro k
  have e : ((0 : ℕ) : ℂ) + 2 * ((k + 1 : ℕ) : ℂ) = ((2 * k + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [e, trivial_term_eq x]

/-- **The trivial zero series, odd character.** Davenport ch. 19 p. 115 display (2):
for `x > 1`, `Σ_{k ≥ 0} x^{-(2k+1)}/(2k+1) = (1/2)(log(1 + x⁻¹) - log(1 - x⁻¹))`, the sum of the
residues `residue_trivial_char` at the trivial zeros `-(1 + 2k)` for `a = 1`. -/
theorem hasSum_trivial_odd {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (x : ℂ) ^ (-((1 : ℕ) + 2 * (k : ℂ))) / ((1 : ℕ) + 2 * (k : ℂ)))
      (((1 / 2) * (Real.log (1 + x⁻¹) - Real.log (1 - x⁻¹)) : ℝ) : ℂ) := by
  refine (Complex.hasSum_ofReal.mpr (hasSum_trivial_odd_real hx)).congr_fun ?_
  intro k
  have e : ((1 : ℕ) : ℂ) + 2 * (k : ℂ) = ((2 * k + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [e, trivial_term_eq x]

/-- Geometric majorant: `Σ_{k ≥ 0} x^{-(k+1)} = 1/(x - 1)` for `x > 1`. -/
lemma hasSum_geom_shift {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (x⁻¹) ^ (k + 1)) (1 / (x - 1)) := by
  have hu0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (by linarith)
  have hu1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have h := (hasSum_geometric_of_lt_one hu0 hu1).mul_left x⁻¹
  have hx0 : x ≠ 0 := by positivity
  have hx1 : x - 1 ≠ 0 := by linarith
  have hv : x⁻¹ * (1 - x⁻¹)⁻¹ = 1 / (x - 1) := by
    field_simp
  rw [hv] at h
  refine h.congr_fun (fun k => ?_)
  ring

/-- **The trivial zero sums are `O(1)`.** Davenport ch. 19 p. 117, the sum over `m` absorbed
into the error term: for `x > 1` both trivial zero sums lie in `[0, 1/(x - 1)]`, so in
`[0, 1]` for `x ≥ 2`. -/
theorem trivial_sum_le {x : ℝ} (hx : 1 < x) :
    (0 ≤ -(1 / 2) * Real.log (1 - (x⁻¹) ^ 2) ∧
      -(1 / 2) * Real.log (1 - (x⁻¹) ^ 2) ≤ 1 / (x - 1)) ∧
    (0 ≤ (1 / 2) * (Real.log (1 + x⁻¹) - Real.log (1 - x⁻¹)) ∧
      (1 / 2) * (Real.log (1 + x⁻¹) - Real.log (1 - x⁻¹)) ≤ 1 / (x - 1)) := by
  have hu0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (by linarith)
  have hu1 : x⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hx).le
  have hg := hasSum_geom_shift hx
  have hterm : ∀ n j : ℕ, j + 1 ≤ n → 1 ≤ n → (x⁻¹) ^ n / (n : ℝ) ≤ (x⁻¹) ^ (j + 1) := by
    intro n j hjn hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc (x⁻¹) ^ n / (n : ℝ) ≤ (x⁻¹) ^ n := div_le_self (by positivity) hn'
      _ ≤ (x⁻¹) ^ (j + 1) := pow_le_pow_of_le_one hu0 hu1 hjn
  have hE := hasSum_trivial_even_real hx
  have hO := hasSum_trivial_odd_real hx
  refine ⟨⟨hasSum_le (fun k => by positivity) hasSum_zero hE, hasSum_le (fun k => ?_) hE hg⟩,
    ⟨hasSum_le (fun k => by positivity) hasSum_zero hO, hasSum_le (fun k => ?_) hO hg⟩⟩
  · exact hterm _ k (by omega) (by omega)
  · exact hterm _ k (by omega) (by omega)

/-! ### The constant `b(χ)`, Davenport ch. 19 p. 118 -/

/- Route notes for `b_regroup_leaf`. Davenport's route needs the Hadamard partial fraction (17)
of ch. 12 for `L'/L` at `s` and at `2`, the regularity of `Γ'/Γ` at `0` for `a = 1` and its
expansion `-1/s + const` for `a = 0`, and the zero count (3) of ch. 16 at `t = 0`, namely
`N(t + 1, χ) - N(t, χ) = O(log q(|t| + 2))`, which bounds the number of terms of the sum.
Alternative route: for even `χ` the lab already has `b` in closed form, from the functional
equation, as `log(2π/q) + γ - conj(L'/L(1, χ))`, in `PNTPort/LeftHalf` and
`HelfgottMajor/LogResidue669`; a local expansion of `L'/L` near `s = 1` together with the zero
count above may then suffice in place of the full Hadamard product, and similarly for odd `χ`
via the functional equation at `s = 0` and `s = 1`. -/

/-! ### Growth of `L(s, χ)` in `Re s > 0`, for the local partial fraction below -/

/-- A function on `ℕ` of period `N` has the same sum over every block of `N` consecutive
integers. -/
private lemma sum_range_shift_periodic {N : ℕ} {M : Type*} [AddCommGroup M] (f : ℕ → M)
    (hf : ∀ n, f (n + N) = f n) (m : ℕ) :
    ∑ k ∈ Finset.range N, f (m + k) = ∑ k ∈ Finset.range N, f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    obtain ⟨M', rfl⟩ : ∃ M', N = M' + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun k => f (m + k))]
    have : f (m + 1 + M') = f (m + (M' + 1)) := by ring_nf
    rw [this]
    have hp : f (m + (M' + 1)) = f m := hf m
    rw [hp]
    simp only [add_zero]
    have : ∀ k, f (m + 1 + k) = f (m + (k + 1)) := fun k => by ring_nf
    simp only [this]

/-- A full period of a non-principal character sums to zero. -/
lemma sum_range_eq_zero' {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∑ k ∈ Finset.range N, χ k = 0 := by
  rw [← MulChar.sum_eq_zero_of_ne_one hχ]
  refine Finset.sum_nbij' (fun i : ℕ => (i : ZMod N)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
  · intro i _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro i hi; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hi)
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro i _; rfl

/-- Partial sums of a non-principal character are at most `N` in norm. -/
lemma norm_sum_range_le' {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (n : ℕ) : ‖∑ k ∈ Finset.range n, χ k‖ ≤ N := by
  have hper : ∀ m, ∑ k ∈ Finset.range (m + N), χ k = ∑ k ∈ Finset.range m, χ k := by
    intro m
    rw [Finset.sum_range_add, sum_range_shift_periodic (fun k => χ k) (fun k => by simp) m,
      sum_range_eq_zero' hχ, add_zero]
  have hmod : ∀ n, ∑ k ∈ Finset.range n, χ k = ∑ k ∈ Finset.range (n % N), χ k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < N
      · rw [Nat.mod_eq_of_lt hn]
      · push Not at hn
        have hN := Nat.pos_of_ne_zero (NeZero.ne N)
        have e : n = (n - N) + N := by omega
        rw [e, hper, ih _ (by omega), Nat.add_mod_right]
  rw [hmod]
  calc ‖∑ k ∈ Finset.range (n % N), χ k‖ ≤ ∑ k ∈ Finset.range (n % N), ‖χ k‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (n % N), (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => DirichletCharacter.norm_le_one χ k
    _ = (n % N : ℕ) := by simp
    _ ≤ N := by exact_mod_cast (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))).le

/-- The same over `Icc 1 n`. -/
lemma norm_sum_Icc_le' {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (n : ℕ) : ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ N := by
  have h0 : ∑ k ∈ Finset.range (n + 1), χ k = χ 0 + ∑ k ∈ Finset.Icc 1 n, χ k := by
    rw [Finset.sum_range_succ', ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.cast_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [add_comm 1 k]
  have hz : χ (0 : ZMod N) = 0 ∨ N = 1 := by
    rcases eq_or_ne N 1 with h | h
    · exact Or.inr h
    · left
      have : ¬ IsUnit (0 : ZMod N) := by
        have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr h
        exact not_isUnit_zero
      exact χ.map_nonunit this
  rcases hz with hz | hN
  · have := norm_sum_range_le' hχ (n + 1)
    rwa [h0, hz, zero_add] at this
  · subst hN
    exact absurd (Subsingleton.elim χ 1) hχ

open Finset MeasureTheory

/-- The step function `A(t) = ∑_{1 ≤ k ≤ t} χ(k)`. -/
lemma integral_eq_mellin' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)) =
      mellin ((Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k)) (-s) := by
  rw [mellin]
  have : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • ((Set.Ioi (1 : ℝ)).indicator
      (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k)) t =
      (Set.Ioi (1 : ℝ)).indicator (fun t =>
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · simp only [Set.indicator_of_mem ht, smul_eq_mul]
      rw [mul_comm]; congr 2; ring
    · simp [Set.indicator_of_notMem ht]
  simp_rw [this]
  rw [setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi]
  simp

lemma measurable_A' {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Measurable (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) :=
  (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ k)).comp Nat.measurable_floor

private lemma norm_A'_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) :
    ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k‖ ≤ N := norm_sum_Icc_le' hχ _

private lemma norm_indicator_A'_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖(Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) t‖ ≤ N := by
  by_cases ht : t ∈ Set.Ioi (1 : ℝ)
  · rw [Set.indicator_of_mem ht]; exact norm_A'_le hχ t
  · rw [Set.indicator_of_notMem ht]; simp [Nat.cast_nonneg]

private lemma differentiableAt_mellin_indicator {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin ((Set.Ioi (1 : ℝ)).indicator
      (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k))) (-s) := by
  have hmeas : Measurable ((Set.Ioi (1 : ℝ)).indicator
      (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k)) :=
    (measurable_A' χ).indicator measurableSet_Ioi
  have hbdd : ∀ t, ‖(Set.Ioi (1 : ℝ)).indicator
      (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) t‖ ≤ N := fun t =>
    norm_indicator_A'_le hχ t
  refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    refine ⟨Set.Ioi 0 ∩ Set.Iio (x + 1), inter_mem_nhdsWithin _ (Iio_mem_nhds (by linarith)),
      ?_⟩
    refine Measure.integrableOn_of_bounded (M := N) ?_ hmeas.aestronglyMeasurable
      (Eventually.of_forall hbdd)
    rw [Set.Ioi_inter_Iio, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  · refine Asymptotics.IsBigO.of_bound N (Eventually.of_forall fun t => ?_)
    simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]; exact hbdd t
  · simpa using hs
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have : t ∉ Set.Ioi (1 : ℝ) := fun h => by
      rw [Set.mem_Ioi] at h; linarith [ht.2]
    simp only [Set.indicator_of_notMem this]
  · simp

lemma LSeries_eq_integral' {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun x : ℕ => χ ↑x) s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)) := by
  have hS : LSeriesSummable (fun x : ℕ => χ ↑x) s :=
    (DirichletCharacter.LSeriesSummable_iff (NeZero.ne N) χ).mpr hs
  have hO : (fun n => ∑ k ∈ Finset.Icc 1 n, (fun x : ℕ => χ ↑x) k) =O[Filter.atTop]
      fun n => (n : ℝ) ^ (0 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound N (Eventually.of_forall fun n => ?_)
    simp only [Real.rpow_zero, norm_one, mul_one]
    exact norm_sum_Icc_le' hχ n
  rw [LSeries_eq_mul_integral _ le_rfl (by linarith) hS hO]

theorem LFunction_eq_integral' {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)) := by
  set U : Set ℂ := {z | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ (fun z => z * mellin ((Set.Ioi (1 : ℝ)).indicator
      (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k)) (-z)) U := by
    intro z hz
    refine (differentiableAt_id.mul ?_).differentiableWithinAt
    exact (differentiableAt_mellin_indicator hχ hz).comp z differentiableAt_id.neg
  have hL : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have hconv : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by simp [hU]
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds 2] fun z => z * mellin ((Set.Ioi (1 : ℝ)).indicator
      (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k)) (-z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz, LSeries_eq_integral' hχ hz,
      integral_eq_mellin']
  have := (hL.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hF.analyticOnNhd hUo)
    hconv h2 hev hs
  rw [this, integral_eq_mellin']

/-- `‖L(s, χ)‖ ≤ N ‖s‖ / Re s` for `Re s > 0`, `χ` non-principal. -/
theorem norm_LFunction_le' {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ N * ‖s‖ / s.re := by
  rw [LFunction_eq_integral' hχ hs, norm_mul]
  have hint : IntegrableOn (fun t : ℝ => (N : ℝ) * t ^ (-(s.re + 1))) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have hle : ‖∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Set.Ioi (1 : ℝ), (N : ℝ) * t ^ (-(s.re + 1)) := by
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have : (-(s + 1)).re = -(s.re + 1) := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (norm_A'_le hχ t) (Real.rpow_nonneg ht0.le _)
  have hval : ∫ t in Set.Ioi (1 : ℝ), (N : ℝ) * t ^ (-(s.re + 1)) = N / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    simp only [Real.one_rpow]
    have : s.re ≠ 0 := hs.ne'
    rw [show -(s.re + 1) + 1 = -s.re by ring]
    field_simp
  calc ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖s‖ * (N / s.re) := by rw [← hval]; exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = N * ‖s‖ / s.re := by ring

/-! ### `|L(2, χ)| ≥ 1/4`, the lower bound at the centre of the local disc -/

private lemma summable_inv_sq_shift2 : Summable fun n : ℕ => (1 : ℝ) / ((n + 2 : ℝ) ^ 2) := by
  have h2 : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h3 : Summable fun n : ℕ => (1 : ℝ) / (((n + 2 : ℕ)) : ℝ) ^ 2 := by
    have := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 2).mpr h2
    simpa using this
  refine h3.congr (fun n => ?_)
  push_cast
  ring

private lemma sum_inv_sq_tail_le : ∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℝ) ^ 2) ≤ 3 / 4 := by
  have hsum := summable_inv_sq_shift2
  refine le_of_tendsto_of_tendsto hsum.hasSum.tendsto_sum_nat tendsto_const_nhds ?_
  filter_upwards with N
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
    norm_num
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have h0 : (1 : ℝ) / ((↑(0 : ℕ) + 2) ^ 2) = 1 / 4 := by norm_num
  rw [h0]
  have hstep : ∑ i ∈ Finset.range M, (1 : ℝ) / ((↑(i + 1) + 2) ^ 2) ≤
      ∑ i ∈ Finset.range M, ((1 : ℝ) / ((i : ℝ) + 2) - 1 / ((i : ℝ) + 3)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hi2 : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have hi3 : (0 : ℝ) < (i : ℝ) + 3 := by positivity
    have e1 : (↑(i + 1) + 2 : ℝ) = (i : ℝ) + 3 := by push_cast; ring
    rw [e1, div_sub_div _ _ hi2.ne' hi3.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have htel : ∑ i ∈ Finset.range M, ((1 : ℝ) / ((i : ℝ) + 2) - 1 / ((i : ℝ) + 3)) =
      1 / 2 - 1 / ((M : ℝ) + 2) := by
    have h := Finset.sum_range_sub' (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 2)) M
    rw [show ∑ i ∈ Finset.range M, ((1 : ℝ) / ((i : ℝ) + 2) - 1 / ((i : ℝ) + 3)) =
        ∑ i ∈ Finset.range M,
          ((1 : ℝ) / ((i : ℝ) + 2) - 1 / (((i + 1 : ℕ) : ℝ) + 2)) from
      Finset.sum_congr rfl (fun i _ => by congr 2; push_cast; ring)]
    simpa using h
  rw [htel] at hstep
  have hpos : (0 : ℝ) < (M : ℝ) + 2 := by positivity
  have hle : (0 : ℝ) < 1 / ((M : ℝ) + 2) := by positivity
  linarith

/-- `1/4 ≤ |L(2, χ)|` for non-principal `χ`: the first term of the series is `1` and the
remaining terms sum to at most `∑_{n ≥ 2} 1/n² ≤ 3/4`. -/
private lemma norm_LFunction_two_ge {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) : (1 : ℝ) / 4 ≤ ‖DirichletCharacter.LFunction χ 2‖ := by
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  rw [DirichletCharacter.LFunction_eq_LSeries χ h2]
  unfold LSeries
  have hsumm : Summable (LSeries.term (fun n : ℕ => χ n) (2 : ℂ)) :=
    (DirichletCharacter.LSeriesSummable_iff (NeZero.ne N) χ).mpr h2
  have hshift : Summable fun n : ℕ => LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 2) :=
    (summable_nat_add_iff 2).mpr hsumm
  have hs1 : Summable fun n : ℕ => LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 1) :=
    (summable_nat_add_iff 1).mpr hsumm
  have e1 : ∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (2 : ℂ) n =
      LSeries.term (fun n : ℕ => χ n) (2 : ℂ) 0 +
        ∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 1) :=
    hsumm.tsum_eq_zero_add
  have e2 : ∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 1) =
      LSeries.term (fun n : ℕ => χ n) (2 : ℂ) 1 +
        ∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 2) := by
    have := hs1.tsum_eq_zero_add
    simpa [Nat.add_assoc] using this
  have ht0 : LSeries.term (fun n : ℕ => χ n) (2 : ℂ) 0 = 0 := by simp [LSeries.term_def]
  have ht1 : LSeries.term (fun n : ℕ => χ n) (2 : ℂ) 1 = 1 := by
    rw [LSeries.term_def]; norm_num
  have hnorm : ∀ n : ℕ,
      ‖LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 2)‖ ≤ 1 / ((n + 2 : ℝ) ^ 2) := by
    intro n
    rw [LSeries.norm_term_eq, if_neg (by omega : ¬ (n + 2 = 0))]
    have hnum : ‖χ ((n + 2 : ℕ) : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hsq : ((n : ℝ) + 2) ^ ((2 : ℂ).re) = ((n : ℝ) + 2) ^ 2 := by
      norm_num [Real.rpow_two]
    rw [hcast, hsq, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hnum, show (0:ℝ) < ((n : ℝ) + 2) ^ 2 by positivity]
  have htail : ‖∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 2)‖ ≤ 3 / 4 := by
    calc ‖∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 2)‖
        ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 2)‖ :=
          norm_tsum_le_tsum_norm hshift.norm
      _ ≤ ∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℝ) ^ 2) := by
          apply Summable.tsum_le_tsum hnorm hshift.norm summable_inv_sq_shift2
      _ ≤ 3 / 4 := sum_inv_sq_tail_le
  rw [e1, e2, ht0, ht1, zero_add]
  have hgoal : (1 : ℂ) + ∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 2) =
      1 - (-∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 2)) := by ring
  rw [hgoal]
  have hneg : ‖-∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 2)‖ ≤ 3 / 4 := by
    rw [norm_neg]; exact htail
  have hkey : ‖(1 : ℂ) - (-∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 2))‖ ≥
      (1 : ℝ) - 3 / 4 := by
    have hle := norm_sub_norm_le (1 : ℂ)
      (-∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) (2 : ℂ) (n + 2))
    simp only [norm_one] at hle
    linarith
  calc (1 : ℝ) / 4 = 1 - 3 / 4 := by norm_num
    _ ≤ _ := hkey

/-! ### Gamma bounds on a compact region, and the functional equation for `L` -/

private theorem GammaR_compact_bounds :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ u : ℂ, ‖u‖ ≤ 8 → -1 ≤ u.re → 1 / 100 ≤ ‖u‖ →
      m ≤ ‖Complex.Gammaℝ u‖ ∧ ‖Complex.Gammaℝ u‖ ≤ M := by
  set K : Set ℂ := {u : ℂ | ‖u‖ ≤ 8} ∩ {u : ℂ | -1 ≤ u.re} ∩ {u : ℂ | (1 : ℝ) / 100 ≤ ‖u‖}
    with hK
  have hcl : {u : ℂ | ‖u‖ ≤ 8} = Metric.closedBall (0 : ℂ) 8 := by
    ext u
    simp [Metric.mem_closedBall, dist_zero_right]
  have hsub : K ⊆ Metric.closedBall (0 : ℂ) 8 := by
    rw [hK, hcl]
    intro u hu
    exact hu.1.1
  have hclosed : IsClosed K := by
    rw [hK, hcl]
    exact (Metric.isClosed_closedBall.inter
      (isClosed_le continuous_const Complex.continuous_re)).inter
      (isClosed_le continuous_const continuous_norm)
  have hKc : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) 8).of_isClosed_subset hclosed hsub
  have hmem1 : (1 : ℂ) ∈ K := by
    rw [hK]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> norm_num
  have hne : ∀ u ∈ K, Complex.Gammaℝ u ≠ 0 := by
    rintro u hu h0
    rw [hK] at hu
    obtain ⟨⟨hu8, hure⟩, hunorm⟩ := hu
    simp only [Set.mem_setOf_eq] at hu8 hure hunorm
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
    have hre : u.re = -(2 * (n : ℝ)) := by rw [hn]; simp
    have hn0 : n = 0 := by
      have h1 : (n : ℝ) < 1 := by rw [hre] at hure; linarith
      have h2 : n < 1 := by exact_mod_cast h1
      omega
    subst hn0
    rw [hn] at hunorm
    simp at hunorm
    linarith
  have hcont : ContinuousOn (fun u : ℂ => ‖u.Gammaℝ‖) K := by
    have hinv : Continuous fun u : ℂ => (u.Gammaℝ)⁻¹ := differentiable_Gammaℝ_inv.continuous
    have hc : ContinuousOn (fun u : ℂ => u.Gammaℝ) K := by
      have hEq : (fun u : ℂ => u.Gammaℝ) = fun u : ℂ => ((u.Gammaℝ)⁻¹)⁻¹ := by
        funext u
        exact (inv_inv _).symm
      rw [hEq]
      exact ContinuousOn.inv₀ hinv.continuousOn (fun u hu => inv_ne_zero (hne u hu))
    exact hc.norm
  obtain ⟨umin, humin, hmin⟩ := hKc.exists_isMinOn ⟨1, hmem1⟩ hcont
  obtain ⟨umax, humax, hmax⟩ := hKc.exists_isMaxOn ⟨1, hmem1⟩ hcont
  exact ⟨‖Complex.Gammaℝ umin‖, ‖Complex.Gammaℝ umax‖, norm_pos_iff.mpr (hne umin humin),
    norm_pos_iff.mpr (hne umax humax), fun u hu hre hnorm =>
      ⟨hmin (by rw [hK]; exact ⟨⟨hu, hre⟩, hnorm⟩),
        hmax (by rw [hK]; exact ⟨⟨hu, hre⟩, hnorm⟩)⟩⟩

private lemma norm_rootNumber_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ‖DirichletCharacter.rootNumber χ‖ ≤ (N : ℝ) := by
  classical
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hg : ‖gaussSum χ ZMod.stdAddChar‖ ≤ (N : ℝ) := by
    unfold gaussSum
    calc ‖∑ a : ZMod N, χ a * ZMod.stdAddChar a‖ ≤ ∑ a : ZMod N, ‖χ a * ZMod.stdAddChar a‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _a : ZMod N, (1 : ℝ) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul]
          have h1 : ‖χ a‖ ≤ 1 := DirichletCharacter.norm_le_one χ a
          have h2 : ‖ZMod.stdAddChar a‖ = 1 := (ZMod.toCircle a).norm_coe
          rw [h2, mul_one]
          exact h1
      _ = (N : ℝ) := by simp
  have hq : ‖((N : ℂ)) ^ ((1 / 2 : ℂ))‖ = (N : ℝ) ^ ((1 / 2 : ℝ)) := by
    have hcast : ((N : ℂ)) = (((N : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    norm_num
  have hI : ‖(Complex.I) ^ (if χ.Even then 0 else 1)‖ = 1 := by
    split_ifs <;> simp
  rw [DirichletCharacter.rootNumber, norm_div, norm_div, hI, hq, div_one]
  rw [div_le_iff₀ (by positivity)]
  have hr1 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 / 2 : ℝ)) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 / 2 : ℝ)) := by simp
      _ ≤ (N : ℝ) ^ ((1 / 2 : ℝ)) := Real.rpow_le_rpow (by norm_num) hN1 (by norm_num)
  have hNN : (N : ℝ) ≤ (N : ℝ) * (N : ℝ) ^ ((1 / 2 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hr1 (Nat.cast_nonneg N)
    simpa using this
  linarith [hg, hNN]

/-- The parity exponent is the same for `χ⁻¹`. -/
private lemma parity_inv {N : ℕ} {χ : DirichletCharacter ℂ N} {a : ℕ}
    (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1)) :
    ((χ⁻¹).Even ∧ a = 0) ∨ ((χ⁻¹).Odd ∧ a = 1) := by
  rcases ha with ⟨he, rfl⟩ | ⟨ho, rfl⟩
  · refine Or.inl ⟨?_, rfl⟩
    show χ⁻¹ (-1) = 1
    rw [MulChar.inv_apply_eq_inv, he, Ring.inverse_one]
  · refine Or.inr ⟨?_, rfl⟩
    show χ⁻¹ (-1) = -1
    rw [MulChar.inv_apply_eq_inv, ho]
    have h1 : Ring.inverse (-1 : ℂ) = -1 := by
      have := Ring.inverse_unit (-1 : ℂˣ)
      simpa using this
    rw [h1]

/-- The functional equation for `L(s, χ)` with the gamma factors separated. -/
private lemma LFunction_fe_parity {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {a : ℕ}
    (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1)) {s : ℂ}
    (hg1 : Complex.Gammaℝ (1 - s + a) ≠ 0) :
    DirichletCharacter.LFunction χ s =
      (N : ℂ) ^ ((1 / 2 : ℂ) - s) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.LFunction χ⁻¹ (1 - s) * Complex.Gammaℝ (1 - s + a) *
          (Complex.Gammaℝ (s + a))⁻¹ := by
  have ha' := parity_inv ha
  have h1 := LFunction_eq_completed_mul_inv (χ := χ) hχ ha s
  have h2 := LFunction_eq_completed_mul_inv (χ := χ⁻¹) (inv_ne_one.mpr hχ) ha' (1 - s)
  have hfe := hprim.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hfe
  rw [h1, hfe]
  have hΛ : DirichletCharacter.completedLFunction χ⁻¹ (1 - s) =
      DirichletCharacter.LFunction χ⁻¹ (1 - s) * Complex.Gammaℝ (1 - s + a) := by
    rw [h2]
    field_simp
  rw [hΛ]
  have hexp : ((1 : ℂ) - s) - 1 / 2 = 1 / 2 - s := by ring
  rw [hexp]
  ring

/-- **The growth of `L` on the disc of radius `2.97` about `2`.** `‖L‖ ≤ K N⁴`, by the maximum
modulus principle, `‖L(s)‖ ≤ N‖s‖/Re s` for `Re s ≥ 1/4` and the functional equation with bounded
gamma factors for `Re s < 1/4`. -/
private theorem LFunction_ball_bound {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hgam : ∀ u : ℂ, ‖u‖ ≤ 8 → -1 ≤ u.re → 1 / 100 ≤ ‖u‖ →
      m ≤ ‖Complex.Gammaℝ u‖ ∧ ‖Complex.Gammaℝ u‖ ≤ M)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1)) :
    ∀ s : ℂ, ‖s - 2‖ ≤ 2.97 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ (100 + 100 * (M / m)) * (N : ℝ) ^ 4 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hK0 : (0 : ℝ) < 100 + 100 * (M / m) := by positivity
  have hN4 : (N : ℝ) ≤ (N : ℝ) ^ 4 := by
    have h3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hN1 3
      simpa using h
    calc (N : ℝ) = (N : ℝ) * 1 := by ring
      _ ≤ (N : ℝ) * (N : ℝ) ^ 3 := by
          apply mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = (N : ℝ) ^ 4 := by ring
  have han : (a : ℝ) ≤ 1 := by
    rcases ha with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num
  have hfront : ∀ z ∈ Metric.sphere (2 : ℂ) 2.97,
      ‖DirichletCharacter.LFunction χ z‖ ≤ (100 + 100 * (M / m)) * (N : ℝ) ^ 4 := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hzn : ‖z‖ ≤ 4.97 := by
      have h1 : ‖z‖ = ‖(z - 2) + 2‖ := by ring_nf
      rw [h1]
      refine (norm_add_le (z - 2) (2 : ℂ)).trans ?_
      rw [hz]
      norm_num
    have hzn2 : (0.97 : ℝ) ≤ ‖z‖ := by
      have h := norm_sub_le z (2 : ℂ)
      rw [hz] at h
      norm_num at h
      linarith
    have hz1 : (0.03 : ℝ) ≤ ‖z + 1‖ := by
      have h := abs_norm_sub_norm_le (3 : ℂ) (z + 1)
      have e : (3 : ℂ) - (z + 1) = -(z - 2) := by ring
      rw [e, norm_neg, hz] at h
      have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
      have h2 := (abs_le.mp h).2
      rw [h3] at h2
      linarith
    have hzre_lo : (-1 : ℝ) ≤ z.re := by
      have h := Complex.abs_re_le_norm (z - 2)
      rw [hz] at h
      have e : (z - 2).re = z.re - 2 := by simp
      rw [e, abs_le] at h
      linarith [h.1]
    have h1z : ‖1 - z‖ ≤ 6 := by
      have h := norm_sub_le 1 z
      norm_num at h
      linarith
    rcases le_or_gt (1 / 4 : ℝ) z.re with hre | hre
    · have h := norm_LFunction_le' hχ (s := z) (by linarith)
      have hzre : (0 : ℝ) < z.re := by linarith
      have hNz : (0 : ℝ) ≤ (N : ℝ) := by linarith
      have step1 : (N : ℝ) * ‖z‖ / z.re ≤ (N : ℝ) * 4.97 / (1 / 4) := by
        rw [div_le_div_iff₀ hzre (by norm_num)]
        have ha1 : (N : ℝ) * ‖z‖ * (1 / 4) ≤ (N : ℝ) * 4.97 * (1 / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hzn hNz
        have ha2 : (N : ℝ) * 4.97 * (1 / 4) ≤ (N : ℝ) * 4.97 * z.re := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
        linarith
      have step2 : (N : ℝ) * 4.97 / (1 / 4) ≤ (100 + 100 * (M / m)) * (N : ℝ) ^ 4 := by
        have h19 : (N : ℝ) * 4.97 / (1 / 4) = (19.88 : ℝ) * (N : ℝ) := by ring
        rw [h19]
        have hle : (19.88 : ℝ) * (N : ℝ) ≤ (19.88 : ℝ) * (N : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left hN4 (by norm_num)
        have hK : (19.88 : ℝ) ≤ 100 + 100 * (M / m) := by
          have h2 : (0 : ℝ) < M / m := by positivity
          linarith
        exact hle.trans (mul_le_mul_of_nonneg_right hK (by positivity))
      exact h.trans (step1.trans step2)
    · have hzre0 : z.re < 1 / 4 := hre
      have ha01 : a = 0 ∨ a = 1 := by
        rcases ha with ⟨_, h⟩ | ⟨_, h⟩
        · exact Or.inl h
        · exact Or.inr h
      have hmem1 : ‖z + a‖ ≤ 8 ∧ -1 ≤ (z + a).re ∧ (1 : ℝ) / 100 ≤ ‖z + a‖ := by
        have hre1 : (z + a).re = z.re + a := by simp
        refine ⟨?_, ?_, ?_⟩
        · calc ‖z + a‖ ≤ ‖z‖ + ‖(a : ℂ)‖ := norm_add_le _ _
            _ ≤ 4.97 + 1 := by
                have : ‖(a : ℂ)‖ = (a : ℝ) := by simp
                rw [this]
                linarith
            _ ≤ 8 := by norm_num
        · rw [hre1]; push_cast; linarith
        · rcases ha01 with rfl | rfl
          · have hz0 : ‖z + ((0 : ℕ) : ℂ)‖ = ‖z‖ := by simp
            rw [hz0]
            linarith
          · have hz0 : ‖z + ((1 : ℕ) : ℂ)‖ = ‖z + 1‖ := by norm_num
            rw [hz0]
            linarith
      have hmem2 : ‖1 - z + a‖ ≤ 8 ∧ -1 ≤ (1 - z + a).re ∧ (1 : ℝ) / 100 ≤ ‖1 - z + a‖ := by
        have hre2 : (1 - z + a).re = 1 - z.re + a := by simp
        refine ⟨?_, ?_, ?_⟩
        · calc ‖1 - z + a‖ ≤ ‖1 - z‖ + ‖(a : ℂ)‖ := norm_add_le _ _
            _ ≤ 6 + 1 := by
                have : ‖(a : ℂ)‖ = (a : ℝ) := by simp
                rw [this]
                linarith
            _ ≤ 8 := by norm_num
        · rw [hre2]; push_cast; linarith
        · have := Complex.re_le_norm (1 - z + a)
          rw [hre2] at this
          push_cast at this
          linarith
      have hg1 : Complex.Gammaℝ (1 - z + a) ≠ 0 := by
        have h := (hgam _ hmem2.1 hmem2.2.1 hmem2.2.2).1
        intro h0
        rw [h0, norm_zero] at h
        linarith
      have hu := (hgam _ hmem1.1 hmem1.2.1 hmem1.2.2).1
      have hv := (hgam _ hmem2.1 hmem2.2.1 hmem2.2.2).2
      have hratio : ‖Complex.Gammaℝ (1 - z + a) * (Complex.Gammaℝ (z + a))⁻¹‖ ≤ M / m := by
        rw [norm_mul, norm_inv, ← div_eq_mul_inv]
        have hu0 : (0 : ℝ) < ‖Complex.Gammaℝ (z + a)‖ := by linarith
        rw [div_le_div_iff₀ hu0 hm]
        nlinarith [hv, hu]
      have hcpow : ‖((N : ℂ)) ^ ((1 / 2 : ℂ) - z)‖ ≤ (N : ℝ) ^ 2 := by
        have hcast : ((N : ℂ)) = (((N : ℝ)) : ℂ) := by push_cast; ring
        rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
        have hexp : ((1 / 2 : ℂ) - z).re = 1 / 2 - z.re := by simp
        rw [hexp]
        have hle : (1 : ℝ) / 2 - z.re ≤ 2 := by linarith
        calc (N : ℝ) ^ (1 / 2 - z.re) ≤ (N : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hN1 hle
          _ = (N : ℝ) ^ 2 := Real.rpow_two (N : ℝ)
      have hW : ‖DirichletCharacter.rootNumber χ‖ ≤ (N : ℝ) := norm_rootNumber_le χ
      have hL1 : ‖DirichletCharacter.LFunction χ⁻¹ (1 - z)‖ ≤ 8 * (N : ℝ) := by
        have hre1z : (1 - z).re = 1 - z.re := by simp
        have h := norm_LFunction_le' (χ := χ⁻¹) (inv_ne_one.mpr hχ) (s := 1 - z) (by rw [hre1z]; linarith)
        have hNz : (0 : ℝ) ≤ (N : ℝ) := by linarith
        calc ‖DirichletCharacter.LFunction χ⁻¹ (1 - z)‖ ≤ (N : ℝ) * ‖1 - z‖ / (1 - z).re := h
          _ ≤ (N : ℝ) * 6 / (3 / 4) := by
              rw [hre1z]
              rw [div_le_div_iff₀ (by linarith) (by norm_num)]
              have h1 : (N : ℝ) * ‖1 - z‖ ≤ (N : ℝ) * 6 :=
                mul_le_mul_of_nonneg_left h1z hNz
              have h34 : (3 / 4 : ℝ) ≤ 1 - z.re := by linarith
              calc (N : ℝ) * ‖1 - z‖ * (3 / 4) ≤ (N : ℝ) * 6 * (3 / 4) :=
                    mul_le_mul_of_nonneg_right h1 (by norm_num)
                _ ≤ (N : ℝ) * 6 * (1 - z.re) :=
                    mul_le_mul_of_nonneg_left h34 (by positivity)
          _ ≤ 8 * (N : ℝ) := by
              have : (N : ℝ) * 6 / (3 / 4) = 8 * (N : ℝ) := by norm_num; ring
              rw [this]
      rw [LFunction_fe_parity hχ hprim ha hg1]
      set A := ((N : ℂ)) ^ ((1 / 2 : ℂ) - z) with hAdef
      set B := DirichletCharacter.rootNumber χ with hBdef
      set C := DirichletCharacter.LFunction χ⁻¹ (1 - z) with hCdef
      set D := Complex.Gammaℝ (1 - z + a) with hDdef
      set E := Complex.Gammaℝ (z + a) with hEdef
      have hb1 : ‖A‖ ≤ (N : ℝ) ^ 2 := hcpow
      have hb2 : ‖B‖ ≤ (N : ℝ) := hW
      have hb3 : ‖C‖ ≤ 8 * (N : ℝ) := hL1
      have hb4 : ‖D‖ ≤ M := hv
      have hb6 : m ≤ ‖E‖ := hu
      have hE0 : (0 : ℝ) < ‖E‖ := lt_of_lt_of_le hm hb6
      have hEinv : ‖E⁻¹‖ ≤ m⁻¹ := by
        rw [norm_inv]
        exact (inv_le_inv₀ hE0 hm).mpr hb6
      have e : ‖A * B * C * D * E⁻¹‖ = ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E⁻¹‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_inv]
      rw [e]
      have hAB : ‖A‖ * ‖B‖ ≤ (N : ℝ) ^ 2 * (N : ℝ) :=
        mul_le_mul hb1 hb2 (norm_nonneg B) (by positivity)
      have hABC : ‖A‖ * ‖B‖ * ‖C‖ ≤ (N : ℝ) ^ 2 * (N : ℝ) * (8 * (N : ℝ)) :=
        mul_le_mul hAB hb3 (norm_nonneg C) (by positivity)
      have hABCD : ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ ≤
          (N : ℝ) ^ 2 * (N : ℝ) * (8 * (N : ℝ)) * M :=
        mul_le_mul hABC hb4 (norm_nonneg D) (by positivity)
      have hABCDE : ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E⁻¹‖ ≤
          (N : ℝ) ^ 2 * (N : ℝ) * (8 * (N : ℝ)) * M * m⁻¹ :=
        mul_le_mul hABCD hEinv (norm_nonneg E⁻¹) (by positivity)
      refine hABCDE.trans ?_
      have hMm : (0 : ℝ) < M / m := by positivity
      have heq : (N : ℝ) ^ 2 * (N : ℝ) * (8 * (N : ℝ)) * M * m⁻¹ =
          8 * (M / m) * (N : ℝ) ^ 4 := by
        field_simp
      rw [heq]
      have h8 : 8 * (M / m) ≤ 100 + 100 * (M / m) := by linarith
      exact mul_le_mul_of_nonneg_right h8 (by positivity)
  have hdiff : DiffContOnCl ℂ (DirichletCharacter.LFunction χ) (Metric.ball (2 : ℂ) 2.97) :=
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
  intro s hs
  have hcl : s ∈ closure (Metric.ball (2 : ℂ) 2.97) := by
    rw [closure_ball (2 : ℂ) (by norm_num), Metric.mem_closedBall, dist_eq_norm]
    exact hs
  exact norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdiff
    (fun z hz => by rw [frontier_ball (2 : ℂ) (by norm_num)] at hz; exact hfront z hz) hcl


/-! ### The local partial fraction at the centre `2` and the constant term at `0` -/

/-- Dividing by a nonzero constant and precomposing with the affine map `z ↦ 2 + 3z` does not
change the order of vanishing. -/
private lemma orderNat_affine {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (ρ : ℂ) :
    analyticOrderNatAt (fun z : ℂ => DirichletCharacter.LFunction χ (2 + 3 * z) /
        DirichletCharacter.LFunction χ 2) ρ =
      analyticOrderNatAt (DirichletCharacter.LFunction χ) (2 + 3 * ρ) := by
  have hL2 : DirichletCharacter.LFunction χ 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  have hdiff : Differentiable ℂ (fun z : ℂ => DirichletCharacter.LFunction χ (2 + 3 * z)) :=
    (DirichletCharacter.differentiable_LFunction hχ).comp
      ((differentiable_const 2).add ((differentiable_id).const_mul 3))
  have hderiv : deriv (fun z : ℂ => 2 + 3 * z) ρ = 3 := by
    have h : HasDerivAt (fun z : ℂ => 2 + 3 * z) 3 ρ := by
      simpa using ((hasDerivAt_id ρ).const_mul (3 : ℂ)).const_add 2
    exact h.deriv
  have hcomp : analyticOrderAt (fun z : ℂ => DirichletCharacter.LFunction χ (2 + 3 * z)) ρ =
      analyticOrderAt (DirichletCharacter.LFunction χ) (2 + 3 * ρ) :=
    analyticOrderAt_comp_of_deriv_ne_zero
      (f := DirichletCharacter.LFunction χ) (g := fun z : ℂ => 2 + 3 * z)
      (differentiable_const 2 |>.add (differentiable_id.const_mul 3) |>.analyticAt ρ)
      (by rw [hderiv]; norm_num)
  set F : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ (2 + 3 * z) with hF
  have hFd : AnalyticAt ℂ F ρ := hdiff.analyticAt ρ
  have hmul : analyticOrderAt (F * fun _ : ℂ => (DirichletCharacter.LFunction χ 2)⁻¹) ρ =
      analyticOrderAt F ρ := by
    have h1 := analyticOrderAt_mul (f := F) (g := fun _ : ℂ => (DirichletCharacter.LFunction χ 2)⁻¹)
      hFd analyticAt_const
    have hconst : analyticOrderAt (fun _ : ℂ => (DirichletCharacter.LFunction χ 2)⁻¹) ρ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (inv_ne_zero hL2))
    rw [h1, hconst, add_zero]
  have hcomp' : analyticOrderAt F ρ = analyticOrderAt (DirichletCharacter.LFunction χ) (2 + 3 * ρ) :=
    hcomp
  have heq : (fun z : ℂ => DirichletCharacter.LFunction χ (2 + 3 * z) /
      DirichletCharacter.LFunction χ 2) =
      F * fun _ : ℂ => (DirichletCharacter.LFunction χ 2)⁻¹ := by
    funext z
    simp [hF, Pi.mul_apply, div_eq_mul_inv]
  rw [heq]
  simp only [analyticOrderNatAt]
  rw [hmul, hcomp']

/-! ### The local partial fraction and the zero count for the scaled function -/

private theorem local_pf_and_count {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hgam : ∀ u : ℂ, ‖u‖ ≤ 8 → -1 ≤ u.re → 1 / 100 ≤ ‖u‖ →
      m ≤ ‖Complex.Gammaℝ u‖ ∧ ‖Complex.Gammaℝ u‖ ≤ M)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1)) :
    ∃ Zg : Finset ℂ,
    (∀ ρ : ℂ, ρ ∈ Zg ↔ (DirichletCharacter.LFunction χ (2 + 3 * ρ) = 0 ∧ ‖ρ‖ ≤ 4 / 5)) ∧
    (∑ ρ ∈ Zg, (analyticOrderNatAt (DirichletCharacter.LFunction χ) (2 + 3 * ρ) : ℝ) ≤
        1 / Real.log ((99 / 100 : ℝ) / (4 / 5)) *
          Real.log (4 * (100 + 100 * (M / m)) * (N : ℝ) ^ 4)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 7 / 10 → DirichletCharacter.LFunction χ (2 + 3 * z) ≠ 0 →
      ‖deriv (fun w : ℂ => DirichletCharacter.LFunction χ (2 + 3 * w) /
          DirichletCharacter.LFunction χ 2) z /
        (fun w : ℂ => DirichletCharacter.LFunction χ (2 + 3 * w) /
          DirichletCharacter.LFunction χ 2) z -
        ∑ ρ ∈ Zg, (analyticOrderNatAt (fun w : ℂ => DirichletCharacter.LFunction χ (2 + 3 * w) /
          DirichletCharacter.LFunction χ 2) ρ : ℂ) / (z - ρ)‖ ≤
      (16 * (4 / 5 : ℝ) ^ 2 / (4 / 5 - 7 / 10) ^ 3 +
          1 / (((99 / 100 : ℝ) ^ 2 / (9 / 10) - 9 / 10) * Real.log ((99 / 100) / (9 / 10)))) *
        Real.log (4 * (100 + 100 * (M / m)) * (N : ℝ) ^ 4)) := by
  classical
  set LF := DirichletCharacter.LFunction χ with hLF
  set G : ℂ → ℂ := fun z => LF (2 + 3 * z) / LF 2 with hG
  set B : ℝ := 4 * (100 + 100 * (M / m)) * (N : ℝ) ^ 4 with hB
  have hL2 : LF 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  have hL2ge : (1 : ℝ) / 4 ≤ ‖LF 2‖ := norm_LFunction_two_ge hχ
  have hL2pos : (0 : ℝ) < ‖LF 2‖ := by linarith
  have hGd : Differentiable ℂ G :=
    ((DirichletCharacter.differentiable_LFunction hχ).comp
      ((differentiable_const 2).add (differentiable_id.const_mul 3))).div_const _
  have hG0 : G 0 = 1 := by
    rw [hG]
    simp only [mul_zero, add_zero]
    exact div_self hL2
  have hB1 : 1 < B := by
    rw [hB]
    have h1 : (0 : ℝ) < M / m := by positivity
    have h3 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := by
      calc (1 : ℝ) = (1 : ℝ) ^ 4 := by norm_num
        _ ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) h3 4
    nlinarith
  have hball := LFunction_ball_bound hm hM hgam χ hχ hprim ha
  have hgb : ∀ z : ℂ, ‖z‖ ≤ 99 / 100 → ‖G z‖ ≤ B := by
    intro z hz
    have hzn : ‖2 + 3 * z - 2‖ ≤ 2.97 := by
      rw [show 2 + 3 * z - 2 = 3 * z by ring, norm_mul]
      have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
      rw [h3]
      nlinarith
    have h1 : ‖LF (2 + 3 * z)‖ ≤ (100 + 100 * (M / m)) * (N : ℝ) ^ 4 := hball _ hzn
    have hkb : (0 : ℝ) ≤ (100 + 100 * (M / m)) * (N : ℝ) ^ 4 := by positivity
    rw [hG, hB, norm_div, div_le_iff₀ hL2pos]
    nlinarith [h1, hL2ge, hkb]
  have hfin : (SetOfZeros 1 G).Finite := by
    have hK : IsCompact (Metric.closedBall (0 : ℂ) 1) := isCompact_closedBall _ _
    have hAn : AnalyticOnNhd ℂ G Set.univ := fun w _ => hGd.analyticAt w
    have hn : G 0 ≠ 0 := by rw [hG0]; exact one_ne_zero
    have hd := hAn.preimage_zero_mem_codiscrete hn
    have h1 := hK.finite_sdiff_of_mem_codiscreteWithin
      (Filter.codiscreteWithin_mono (Set.subset_univ _) hd)
    have heq : (Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | G z = 0}) =
        (Metric.closedBall (0 : ℂ) 1 \ (fun z : ℂ => G z) ⁻¹' ({0}ᶜ)) := by
      ext z
      simp [Set.mem_sdiff, Metric.mem_closedBall, dist_zero_right, eq_comm]
    have h2 : (Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | G z = 0}).Finite := by
      rw [heq]; exact h1
    rw [show SetOfZeros 1 G = Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | G z = 0} from by
      ext z
      simp [SetOfZeros, Metric.mem_closedBall, dist_zero_right, and_comm]]
    exact h2
  -- identify the abstract finset `Zg` with the zero set of `G` in the disc of radius `4/5`
  have horderG : ∀ ρ : ℂ, analyticOrderNatAt G ρ =
      analyticOrderNatAt LF (2 + 3 * ρ) := fun ρ => orderNat_affine hχ ρ
  have hZg : ∀ ρ : ℂ, ρ ∈ (finiteSetOfZeros_mono (by norm_num : (4 / 5 : ℝ) < 1) hfin).toFinset ↔
      (DirichletCharacter.LFunction χ (2 + 3 * ρ) = 0 ∧ ‖ρ‖ ≤ 4 / 5) := by
    intro ρ
    rw [Set.Finite.mem_toFinset]
    simp only [SetOfZeros, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hnorm, hz⟩
      refine ⟨?_, hnorm⟩
      have h1 : LF (2 + 3 * ρ) / LF 2 = 0 := hz
      exact (div_eq_zero_iff.mp h1).resolve_right hL2
    · rintro ⟨h1, hnorm⟩
      refine ⟨hnorm, ?_⟩
      exact div_eq_zero_iff.mpr (Or.inl h1)
  refine ⟨_, hZg, ?_, ?_⟩
  · have hzb := ZerosBound (B := B) (r := 4 / 5) (R := 99 / 100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (fun w _ => hGd.analyticAt w) hG0 hfin hgb
    have hcast : (∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (4 / 5 : ℝ) < 1) hfin).toFinset,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) (2 + 3 * ρ) : ℝ)) =
        ((∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (4 / 5 : ℝ) < 1) hfin).toFinset,
          analyticOrderNatAt G ρ : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun ρ _ => by rw [horderG ρ])
    rw [hcast]
    exact hzb
  · intro z hz hgz
    have hmem : z ∈ Metric.closedBall (0 : ℂ) (7 / 10) \ SetOfZeros (9 / 10) G := by
      refine ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hz, ?_⟩
      rintro ⟨-, h0⟩
      have h1 : LF (2 + 3 * z) / LF 2 = 0 := h0
      exact hgz ((div_eq_zero_iff.mp h1).resolve_right hL2)
    have hFB := FinalBound (B := B) hB1 (r' := 7 / 10) (r := 4 / 5) (R' := 9 / 10) (R := 99 / 100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun w _ => hGd.analyticAt w) hG0 hfin hgb hmem
    exact hFB

/-- **The constant term at `0`.** With the trivial zero at `0` of an even character (of order one)
   removed from the sum, `L'/L(s) - Σ_ρ m(ρ)/(s - 2 - 3ρ)` tends to `b + Σ_{ρ ≠ -2/3} m(ρ)/(2+3ρ)`
   as `s → 0`. -/
private theorem bracket_tendsto {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {Zg : Finset ℂ}
    (hZg : ∀ ρ : ℂ, ρ ∈ Zg ↔ (DirichletCharacter.LFunction χ (2 + 3 * ρ) = 0 ∧ ‖ρ‖ ≤ 4 / 5))
    {b : ℂ}
    (hb : (χ.Odd ∧ b = deriv (DirichletCharacter.LFunction χ) 0 /
              DirichletCharacter.LFunction χ 0) ∨
          (χ.Even ∧ Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b))) :
    Tendsto (fun s : ℂ => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Zg, (analyticOrderNatAt (DirichletCharacter.LFunction χ) (2 + 3 * ρ) : ℂ) /
          (s - (2 + 3 * ρ)))
      (𝓝[≠] 0)
      (𝓝 (b + ∑ ρ ∈ Zg.erase (-2 / 3),
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ))) := by
  classical
  set LF := DirichletCharacter.LFunction χ with hLF
  have hAn : AnalyticAt ℂ LF 0 := (DirichletCharacter.differentiable_LFunction hχ).analyticAt 0
  rcases hb with ⟨hodd, hbe⟩ | ⟨heven, hbe⟩
  · -- the odd case: `L(0) ≠ 0`, no term to remove
    have hL0 : LF 0 ≠ 0 := (residue_zero_odd hprim hχ hodd (x := 1) (by norm_num)).1
    have hρ0 : (-2 / 3 : ℂ) ∉ Zg := by
      intro h
      have h1 : LF (2 + 3 * (-2 / 3)) = 0 := ((hZg _).mp h).1
      apply hL0
      convert h1 using 2
      ring
    rw [Finset.erase_eq_of_notMem hρ0]
    have hne : ∀ ρ ∈ Zg, (2 : ℂ) + 3 * ρ ≠ 0 := by
      intro ρ hρ h0
      have h1 : ρ = -2 / 3 := by linear_combination h0 / 3
      exact hρ0 (h1 ▸ hρ)
    have hsub : ContinuousAt (fun s : ℂ => deriv LF s / LF s -
        ∑ ρ ∈ Zg, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (s - (2 + 3 * ρ))) 0 := by
      have hA : ContinuousAt (fun s : ℂ => deriv LF s / LF s) 0 :=
        hAn.deriv.continuousAt.div hAn.continuousAt hL0
      have hB : ContinuousAt (fun s : ℂ =>
          ∑ ρ ∈ Zg, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (s - (2 + 3 * ρ))) 0 := by
        refine tendsto_finset_sum _ (fun ρ hρ => ?_)
        have hx : (0 : ℂ) - (2 + 3 * ρ) ≠ 0 := by
          intro h
          exact hne ρ hρ (by linear_combination -h)
        exact continuousAt_const.div (continuousAt_id.sub continuousAt_const) hx
      exact hA.sub hB
    have hmain := hsub.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    have hsum : (∑ ρ ∈ Zg, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (0 - (2 + 3 * ρ))) =
        - ∑ ρ ∈ Zg, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun ρ _ => by rw [zero_sub, div_neg]
    rw [← hbe, hsum, sub_neg_eq_add] at hmain
    exact hmain
  · -- the even case: the zero at `0` is simple
    have ha0 : (χ.Even ∧ (0 : ℕ) = 0) ∨ (χ.Odd ∧ (0 : ℕ) = 1) := Or.inl ⟨heven, rfl⟩
    have hL0 : LF 0 = 0 := by
      rw [LFunction_eq_zero_iff_of_re_nonpos hprim hχ ha0 (le_refl 0)]
      exact ⟨0, by push_cast; ring⟩
    have hm0 : analyticOrderNatAt LF 0 = 1 := by
      have h := (analyticOrderAt_trivial hprim hχ ha0 0).2
      simpa using h
    have hρ0 : (-2 / 3 : ℂ) ∈ Zg := by
      rw [hZg]
      refine ⟨?_, by norm_num⟩
      convert hL0 using 2
      ring
    have hmρ0 : (analyticOrderNatAt LF (2 + 3 * (-2 / 3)) : ℂ) = 1 := by
      rw [show 2 + 3 * (-2 / 3 : ℂ) = 0 by ring, hm0]
      norm_num
    have hsplit : ∀ s : ℂ, (∑ ρ ∈ Zg, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (s - (2 + 3 * ρ))) =
        1 / s + ∑ ρ ∈ Zg.erase (-2 / 3),
          (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (s - (2 + 3 * ρ)) := by
      intro s
      rw [← Finset.sum_erase_add _ _ hρ0, hmρ0]
      rw [show (2 : ℂ) + 3 * (-2 / 3) = 0 by ring]
      ring
    have hne : ∀ ρ ∈ Zg.erase (-2 / 3), (2 : ℂ) + 3 * ρ ≠ 0 := by
      intro ρ hρ h0
      have h1 : ρ = -2 / 3 := by linear_combination h0 / 3
      exact (Finset.ne_of_mem_erase hρ) h1
    have h2 : Tendsto (fun s : ℂ => ∑ ρ ∈ Zg.erase (-2 / 3),
        (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (s - (2 + 3 * ρ))) (𝓝[≠] 0)
        (𝓝 (∑ ρ ∈ Zg.erase (-2 / 3),
          (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (0 - (2 + 3 * ρ)))) := by
      refine tendsto_finset_sum _ (fun ρ hρ => ?_)
      have hx : (0 : ℂ) - (2 + 3 * ρ) ≠ 0 := by
        intro h
        exact hne ρ hρ (by linear_combination -h)
      exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hx).tendsto.mono_left
        nhdsWithin_le_nhds
    have hmain := hbe.sub h2
    have hsum : (∑ ρ ∈ Zg.erase (-2 / 3), (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (0 - (2 + 3 * ρ))) =
        - ∑ ρ ∈ Zg.erase (-2 / 3), (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun ρ _ => by rw [zero_sub, div_neg]
    rw [hsum, sub_neg_eq_add] at hmain
    refine hmain.congr' (Eventually.of_forall fun s => ?_)
    show deriv LF s / LF s - 1 / s -
        ∑ ρ ∈ Zg.erase (-2 / 3), (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (s - (2 + 3 * ρ)) =
        deriv LF s / LF s - ∑ ρ ∈ Zg, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (s - (2 + 3 * ρ))
    rw [hsplit s]
    ring


set_option maxHeartbeats 2000000 in
/-- **`b(χ) + Σ_{|γ|<1} m(ρ)/ρ = O(log q)`.** The sum over the zeros of `L(s, χ)` in the box
`0 < Re ρ < 1`, `|Im ρ| < 1`, plus the constant term of `L'/L` at `0`, is bounded by an absolute
constant times `log q`. -/
private theorem leaf_core {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hgam : ∀ u : ℂ, ‖u‖ ≤ 8 → -1 ≤ u.re → 1 / 100 ≤ ‖u‖ →
      m ≤ ‖Complex.Gammaℝ u‖ ∧ ‖Complex.Gammaℝ u‖ ≤ M)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {a : ℕ} (ha : (χ.Even ∧ a = 0) ∨ (χ.Odd ∧ a = 1)) {b : ℂ}
    (hb : (χ.Odd ∧ b = deriv (DirichletCharacter.LFunction χ) 0 /
              DirichletCharacter.LFunction χ 0) ∨
          (χ.Even ∧ Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b)))
    (Z : Finset ℂ)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| < 1)) :
    ‖b + ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / ρ‖ ≤
      ((16 * (4 / 5 : ℝ) ^ 2 / (4 / 5 - 7 / 10) ^ 3 +
            1 / (((99 / 100 : ℝ) ^ 2 / (9 / 10) - 9 / 10) * Real.log ((99 / 100) / (9 / 10)))) / 3 +
        1 / Real.log ((99 / 100 : ℝ) / (4 / 5))) *
        Real.log (4 * (100 + 100 * (M / m)) * (N : ℝ) ^ 4) := by
  classical
  set LF := DirichletCharacter.LFunction χ with hLF
  set Kf : ℝ := 16 * (4 / 5 : ℝ) ^ 2 / (4 / 5 - 7 / 10) ^ 3 +
    1 / (((99 / 100 : ℝ) ^ 2 / (9 / 10) - 9 / 10) * Real.log ((99 / 100) / (9 / 10))) with hKf
  set B : ℝ := 4 * (100 + 100 * (M / m)) * (N : ℝ) ^ 4 with hB
  set met : ℝ := Real.log ((99 / 100 : ℝ) / (4 / 5)) with hmet
  set ρ0 : ℂ := -2 / 3 with hρ0def
  have hL2 : LF 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  obtain ⟨Zg, hZg, hcount, hFB⟩ := local_pf_and_count hm hM hgam χ hprim hχ ha
  have hbr := bracket_tendsto hprim hχ hZg hb
  -- the test sequence `sₙ = 1/(n+1) → 0`
  set sn : ℕ → ℂ := fun n => (((1 : ℝ) / ((n : ℝ) + 1)) : ℂ) with hsn
  have hsn0 : Tendsto sn atTop (𝓝 0) := by
    rw [hsn, tendsto_zero_iff_norm_tendsto_zero]
    have hfun : (fun n : ℕ => ‖(((1 : ℝ) / ((n : ℝ) + 1)) : ℂ)‖) =
        fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) := by
      funext n
      have key : (((1 : ℝ) / ((n : ℝ) + 1)) : ℂ) = (1 : ℂ) / ((n : ℂ) + 1) := by
        push_cast
        ring
      rw [key, norm_div]
      have hden : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
        rw [show ((n : ℂ) + 1) = ((((n : ℝ) + 1) : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hden, norm_one]
    rw [hfun]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hsn_ne : ∀ᶠ n : ℕ in atTop, sn n ≠ 0 := by
    filter_upwards with n
    rw [hsn]
    intro h0
    have h1 : ((n : ℂ) + 1) = 0 := by simpa using h0
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : ((n : ℂ) + 1) ≠ 0 := by
      rw [show ((n : ℂ) + 1) = ((((n : ℝ) + 1) : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast (ne_of_gt hpos)
    exact h2 h1
  have hsn0' : Tendsto sn atTop (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hsn0, ?_⟩
    filter_upwards [hsn_ne] with n hn
    simpa using hn
  have hzn_ev : ∀ᶠ n : ℕ in atTop,
      ‖sn n - 2‖ / 3 ≤ 7 / 10 := by
    have ht : Tendsto (fun n : ℕ => ‖sn n - 2‖ / 3) atTop
        (𝓝 (‖((0 : ℂ) - 2)‖ / 3)) := by
      refine Tendsto.div_const ?_ 3
      exact continuous_norm.continuousAt.tendsto.comp (hsn0.sub tendsto_const_nhds)
    have h2 : ‖((0 : ℂ) - 2)‖ / 3 < 7 / 10 := by norm_num
    exact ht.eventually (eventually_le_nhds h2)
  have hLne_ev : ∀ᶠ n : ℕ in atTop, LF (sn n) ≠ 0 := by
    rcases ha with ⟨he, rfl⟩ | ⟨ho, rfl⟩
    · obtain ⟨v, hv, hv0, hvf⟩ := LFunction_eq_mul_trivial hprim hχ (Or.inl ⟨he, rfl⟩) (a := 0) 0
      have hvc : ContinuousAt v 0 := hv.differentiableAt.continuousAt
      have hv0' : v 0 ≠ 0 := by simpa using hv0
      have h1 : ∀ᶠ n : ℕ in atTop, v (sn n) ≠ 0 :=
        hsn0.eventually (hvc.eventually_ne hv0')
      filter_upwards [h1, hsn_ne] with n h1n h2n
      rw [hLF, hvf (sn n)]
      have h2n' : sn n + (((0 : ℕ) : ℂ) + 2 * ((0 : ℕ) : ℂ)) ≠ 0 := by simpa using h2n
      exact mul_ne_zero h2n' h1n
    · have hL0 : LF 0 ≠ 0 := (residue_zero_odd hprim hχ ho (x := 1) (by norm_num)).1
      have hcont : ContinuousAt LF 0 :=
        (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt
      exact hsn0.eventually (hcont.eventually_ne hL0)
  -- the local partial fraction along the sequence, in the `s` variable
  have hFBev : ∀ᶠ n : ℕ in atTop,
      3 * ‖deriv LF (sn n) / LF (sn n) -
        ∑ ρ ∈ Zg, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (sn n - (2 + 3 * ρ))‖ ≤
          Kf * Real.log B := by
    filter_upwards [hzn_ev, hLne_ev] with n hzn hLne
    have hmem : ‖(sn n - 2) / 3‖ ≤ 7 / 10 := by
      rw [norm_div]
      have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
      rw [h3]
      exact hzn
    have hLne' : DirichletCharacter.LFunction χ (2 + 3 * ((sn n - 2) / 3)) ≠ 0 := by
      rw [show 2 + 3 * ((sn n - 2) / 3) = sn n by ring]
      exact hLne
    have h1 := hFB ((sn n - 2) / 3) hmem hLne'
    rw [← hKf, ← hB] at h1
    have hd1 : deriv (fun w : ℂ => LF (2 + 3 * w)) ((sn n - 2) / 3) = 3 * deriv LF (sn n) := by
      have h1 : (fun w : ℂ => LF (2 + 3 * w)) = LF ∘ (fun w : ℂ => 2 + 3 * w) := rfl
      rw [h1, deriv_comp]
      · have h2 : deriv (fun w : ℂ => 2 + 3 * w) ((sn n - 2) / 3) = 3 := by
          have h3 : HasDerivAt (fun w : ℂ => 2 + 3 * w) 3 ((sn n - 2) / 3) := by
            simpa using ((hasDerivAt_id ((sn n - 2) / 3)).const_mul (3 : ℂ)).const_add 2
          exact h3.deriv
        rw [h2, show 2 + 3 * ((sn n - 2) / 3) = sn n by ring]
        ring
      · have he : 2 + 3 * ((sn n - 2) / 3) = sn n := by ring
        rw [he]
        exact (DirichletCharacter.differentiable_LFunction hχ) _
      · exact ((differentiable_id.const_mul 3).const_add 2) ((sn n - 2) / 3)
    have hderiv : deriv (fun w : ℂ => LF (2 + 3 * w) / LF 2) ((sn n - 2) / 3) =
        3 * deriv LF (sn n) / LF 2 := by
      rw [deriv_div_const, hd1]
    have hGval : (fun w : ℂ => LF (2 + 3 * w) / LF 2) ((sn n - 2) / 3) = LF (sn n) / LF 2 := by
      show LF (2 + 3 * ((sn n - 2) / 3)) / LF 2 = _
      rw [show 2 + 3 * ((sn n - 2) / 3) = sn n by ring]
    have hratio : deriv (fun w : ℂ => LF (2 + 3 * w) / LF 2) ((sn n - 2) / 3) /
        (fun w : ℂ => LF (2 + 3 * w) / LF 2) ((sn n - 2) / 3) =
        3 * (deriv LF (sn n) / LF (sn n)) := by
      rw [hderiv, hGval, div_eq_iff (div_ne_zero hLne hL2)]
      field_simp
    have hterm : ∀ ρ : ℂ,
        (analyticOrderNatAt (fun w : ℂ => LF (2 + 3 * w) / LF 2) ρ : ℂ) / ((sn n - 2) / 3 - ρ) =
          3 * ((analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (sn n - (2 + 3 * ρ))) := by
      intro ρ
      rw [orderNat_affine hχ ρ]
      rw [show (sn n - 2) / 3 - ρ = (sn n - (2 + 3 * ρ)) / 3 by ring]
      by_cases hzero : sn n - (2 + 3 * ρ) = 0
      · rw [hzero]
        simp
      · field_simp
        ring
    have hsum : (∑ ρ ∈ Zg, (analyticOrderNatAt (fun w : ℂ => LF (2 + 3 * w) / LF 2) ρ : ℂ) /
        ((sn n - 2) / 3 - ρ)) =
        3 * ∑ ρ ∈ Zg, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (sn n - (2 + 3 * ρ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ρ _ => hterm ρ
    rw [hratio, hsum, ← mul_sub, norm_mul] at h1
    simpa using h1
  -- pass to the limit
  have hlim : Tendsto (fun n : ℕ => deriv LF (sn n) / LF (sn n) -
        ∑ ρ ∈ Zg, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (sn n - (2 + 3 * ρ))) atTop
      (𝓝 (b + ∑ ρ ∈ Zg.erase ρ0, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ))) :=
    hbr.comp hsn0'
  have hlim3 : Tendsto (fun n : ℕ => 3 * ‖deriv LF (sn n) / LF (sn n) -
        ∑ ρ ∈ Zg, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (sn n - (2 + 3 * ρ))‖) atTop
      (𝓝 (3 * ‖b + ∑ ρ ∈ Zg.erase ρ0,
        (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ)‖)) :=
    hlim.norm.const_mul 3
  have hkey := le_of_tendsto hlim3 hFBev
  have hhalf : ‖b + ∑ ρ ∈ Zg.erase ρ0,
      (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ)‖ ≤ Kf / 3 * Real.log B := by
    rw [show Kf / 3 * Real.log B = Kf * Real.log B / 3 by ring,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    linarith
  -- relate the sum over the box to the sum over the disc
  have hφinj : Set.InjOn (fun s : ℂ => (s - 2) / 3) (Z : Set ℂ) := by
    intro a _ b _ h
    have := congrArg (fun z : ℂ => 2 + 3 * z) h
    simpa [mul_comm] using this
  have hφZ : Z.image (fun s : ℂ => (s - 2) / 3) ⊆ Zg.erase ρ0 := by
    intro ρ hρ
    rw [Finset.mem_image] at hρ
    obtain ⟨s, hs, rfl⟩ := hρ
    rw [Finset.mem_erase]
    have hsz := (hZ s).mp hs
    refine ⟨?_, ?_⟩
    · intro h
      have h0 : s = 0 := by
        have h1 : (s - 2) / 3 = -2 / 3 := by
          rw [hρ0def] at h
          exact h
        linear_combination 3 * h1
      rw [h0] at hsz
      have hc := hsz.2.1
      simp at hc
    · rw [hZg]
      refine ⟨?_, ?_⟩
      · rw [show 2 + 3 * ((s - 2) / 3) = s by ring]
        exact hsz.1
      · have h1 : ‖s - 2‖ < 2.4 := by
          have hsq : ‖s - 2‖ ^ 2 = (s.re - 2) ^ 2 + s.im ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]
            simp
            ring
          have him := abs_lt.mp hsz.2.2.2
          nlinarith [hsz.2.1, hsz.2.2.1, hsq, norm_nonneg (s - 2), him.1, him.2]
        rw [norm_div]
        have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
        rw [h3, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
        linarith
  have himage : (∑ s ∈ Z, (analyticOrderNatAt LF s : ℂ) / s) =
      ∑ ρ ∈ Z.image (fun s : ℂ => (s - 2) / 3), (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ) := by
    rw [Finset.sum_image hφinj]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show 2 + 3 * ((s - 2) / 3) = s by ring]
  have hsdiff := Finset.sum_sdiff (f := fun ρ => (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ))
    (s₁ := Z.image (fun s : ℂ => (s - 2) / 3)) (s₂ := Zg.erase ρ0) hφZ
  -- the difference of the two sums, termwise bounded
  have hdiff : ‖(∑ ρ ∈ Zg.erase ρ0, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ)) -
      ∑ s ∈ Z, (analyticOrderNatAt LF s : ℂ) / s‖ ≤ 1 / met * Real.log B := by
    rw [himage]
    have hkey2 : (∑ ρ ∈ Zg.erase ρ0, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ)) -
        ∑ ρ ∈ Z.image (fun s : ℂ => (s - 2) / 3), (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ) =
        ∑ ρ ∈ Zg.erase ρ0 \ Z.image (fun s : ℂ => (s - 2) / 3),
          (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ) := by
      rw [sub_eq_iff_eq_add]
      exact hsdiff.symm
    rw [hkey2]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ ρ ∈ Zg.erase ρ0 \ Z.image (fun s : ℂ => (s - 2) / 3),
        ‖(analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ)‖ ≤
          (analyticOrderNatAt LF (2 + 3 * ρ) : ℝ) := by
      intro ρ hρ
      obtain ⟨hρe, hρs⟩ := Finset.mem_sdiff.mp hρ
      have hρZg : ρ ∈ Zg := Finset.mem_of_mem_erase hρe
      have hρ0' : ρ ≠ ρ0 := Finset.ne_of_mem_erase hρe
      have hzL : LF (2 + 3 * ρ) = 0 := ((hZg ρ).mp hρZg).1
      have hnorm : ‖ρ‖ ≤ 4 / 5 := ((hZg ρ).mp hρZg).2
      have hre_lo : (-1 / 2 : ℝ) ≤ (2 + 3 * ρ).re := by
        have h1 : (2 + 3 * ρ).re = 2 + 3 * ρ.re := by simp
        have h2 : |ρ.re| ≤ ‖ρ‖ := Complex.abs_re_le_norm ρ
        rw [h1]
        rw [abs_le] at h2
        linarith [h2.1]
      have hne0 : 2 + 3 * ρ ≠ 0 := by
        intro h0
        have h1 : ρ = -2 / 3 := by linear_combination h0 / 3
        exact hρ0' (by rw [hρ0def]; exact h1)
      have hre_pos : 0 < (2 + 3 * ρ).re := by
        rcases le_or_gt (2 + 3 * ρ).re 0 with h | h
        · exact absurd (LeanLab.Linnik.ExplicitFormula.zero_left_strip hprim hzL hre_lo h) hne0
        · exact h
      have hre_lt1 : (2 + 3 * ρ).re < 1 := by
        rcases lt_or_ge (2 + 3 * ρ).re 1 with h | h
        · exact h
        · exact absurd hzL (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h)
      have hnotZ : 2 + 3 * ρ ∉ Z := by
        intro hmem
        have hρmem : ρ ∈ Z.image (fun s : ℂ => (s - 2) / 3) := by
          refine Finset.mem_image.mpr ⟨2 + 3 * ρ, hmem, ?_⟩
          ring
        exact hρs hρmem
      have him : (1 : ℝ) ≤ |(2 + 3 * ρ).im| := by
        by_contra h
        push Not at h
        exact hnotZ ((hZ (2 + 3 * ρ)).mpr ⟨hzL, hre_pos, hre_lt1, h⟩)
      have hnorm1 : (1 : ℝ) ≤ ‖2 + 3 * ρ‖ :=
        le_trans him (Complex.abs_im_le_norm (2 + 3 * ρ))
      rw [norm_div]
      have hcast : ‖(analyticOrderNatAt LF (2 + 3 * ρ) : ℂ)‖ =
          (analyticOrderNatAt LF (2 + 3 * ρ) : ℝ) := by simp
      rw [hcast]
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖2 + 3 * ρ‖)]
      have hm0 : (0 : ℝ) ≤ (analyticOrderNatAt LF (2 + 3 * ρ) : ℝ) := by positivity
      nlinarith [hnorm1, hm0]
    have hstep1 : (∑ ρ ∈ Zg.erase ρ0 \ Z.image (fun s : ℂ => (s - 2) / 3),
        ‖(analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ)‖) ≤
        ∑ ρ ∈ Zg.erase ρ0 \ Z.image (fun s : ℂ => (s - 2) / 3),
          (analyticOrderNatAt LF (2 + 3 * ρ) : ℝ) :=
      Finset.sum_le_sum hterm
    have hstep2 : (∑ ρ ∈ Zg.erase ρ0 \ Z.image (fun s : ℂ => (s - 2) / 3),
        (analyticOrderNatAt LF (2 + 3 * ρ) : ℝ)) ≤
        ∑ ρ ∈ Zg, (analyticOrderNatAt LF (2 + 3 * ρ) : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · exact (Finset.sdiff_subset).trans (Finset.erase_subset _ _)
      · intro ρ _ _
        exact Nat.cast_nonneg _
    exact hstep1.trans (hstep2.trans hcount)
  -- assemble
  have hfinal : b + ∑ ρ ∈ Z, (analyticOrderNatAt LF ρ : ℂ) / ρ =
      (b + ∑ ρ ∈ Zg.erase ρ0, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ)) -
        ((∑ ρ ∈ Zg.erase ρ0, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ)) -
          ∑ s ∈ Z, (analyticOrderNatAt LF s : ℂ) / s) := by
    ring
  rw [hfinal]
  refine (norm_sub_le _ _).trans ?_
  have hlogB : 0 ≤ Real.log B := by
    rw [hB]
    apply Real.log_nonneg
    have h1 : (0 : ℝ) < M / m := by positivity
    have h2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    have h4 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := by
      calc (1 : ℝ) = (1 : ℝ) ^ 4 := by norm_num
        _ ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 4
    nlinarith [h1, h4]
  calc ‖b + ∑ ρ ∈ Zg.erase ρ0, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ)‖ +
        ‖(∑ ρ ∈ Zg.erase ρ0, (analyticOrderNatAt LF (2 + 3 * ρ) : ℂ) / (2 + 3 * ρ)) -
          ∑ s ∈ Z, (analyticOrderNatAt LF s : ℂ) / s‖
      ≤ Kf / 3 * Real.log B + 1 / met * Real.log B := add_le_add hhalf hdiff
    _ = (Kf / 3 + 1 / met) * Real.log B := by ring
    _ = (Kf / 3 + 1 / Real.log ((99 / 100 : ℝ) / (4 / 5))) *
        Real.log (4 * (100 + 100 * (M / m)) * (N : ℝ) ^ 4) := by rw [hKf, hmet, hB]

set_option maxHeartbeats 2000000 in
/-- The coefficient in front of `log B` is nonnegative. -/
private lemma coef_pos {m M : ℝ} (hm : 0 < m) (hM : 0 < M) :
    (0 : ℝ) < (16 * (4 / 5 : ℝ) ^ 2 / (4 / 5 - 7 / 10) ^ 3 +
        1 / (((99 / 100 : ℝ) ^ 2 / (9 / 10) - 9 / 10) * Real.log ((99 / 100) / (9 / 10)))) / 3 +
      1 / Real.log ((99 / 100 : ℝ) / (4 / 5)) := by
  have h1 : (0 : ℝ) < 4 / 5 - 7 / 10 := by norm_num
  have h2 : (0 : ℝ) < (99 / 100 : ℝ) ^ 2 / (9 / 10) - 9 / 10 := by norm_num
  have h3 : (0 : ℝ) < Real.log ((99 / 100 : ℝ) / (9 / 10)) := Real.log_pos (by norm_num)
  have h4 : (0 : ℝ) < Real.log ((99 / 100 : ℝ) / (4 / 5)) := Real.log_pos (by norm_num)
  positivity

set_option maxHeartbeats 2000000 in
/-- `log(4·k·q⁴) ≤ (log(4k)/log 2 + 4)·log q` for `q ≥ 2`. -/
private lemma log_bound {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Real.log (4 * (100 + 100 * (M / m)) * (N : ℝ) ^ 4) ≤
      (Real.log (4 * (100 + 100 * (M / m))) / Real.log 2 + 4) * Real.log (N : ℝ) := by
  have hN1 : N ≠ 1 := modulus_ne_one hχ
  have hN0 : N ≠ 0 := NeZero.ne N
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by
    have : 2 ≤ N := by omega
    exact_mod_cast this
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hN2
  have hMb : (0 : ℝ) < M / m := by positivity
  have hkb : (0 : ℝ) < 4 * (100 + 100 * (M / m)) := by nlinarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN4pos : (0 : ℝ) < (N : ℝ) ^ 4 := pow_pos hNpos 4
  rw [Real.log_mul (ne_of_gt hkb) (ne_of_gt hN4pos), Real.log_pow]
  push_cast
  have h0 : 0 ≤ Real.log (4 * (100 + 100 * (M / m))) := by
    apply Real.log_nonneg
    have : (0 : ℝ) < 100 + 100 * (M / m) := by nlinarith
    nlinarith
  have h1 : Real.log (4 * (100 + 100 * (M / m))) ≤
      Real.log (4 * (100 + 100 * (M / m))) / Real.log 2 * Real.log (N : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left hlogN h0
  nlinarith


/-- LEAF: Davenport, Multiplicative Number Theory, second edition, ch. 19 p. 118, the display
`b(χ) = O(log q) - Σ_{|γ|<1} 1/ρ` following display (8). Class HARD, possibly cheaper by the
alternative route in the comment above. For primitive `χ ≠ 1`, `b(χ)` is `L'(0, χ)/L(0, χ)`
when `χ` is odd and the constant term of `L'/L` at `0` when `χ` is even, and
`b(χ) + Σ_{|γ|<1} m(ρ)/ρ = O(log q)` uniformly, the sum over the zeros with `0 < Re ρ < 1`,
`m(ρ)` the multiplicity. Note `q ≥ 3` here, so `log q > 1`. -/
theorem b_regroup_leaf : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ b : ℂ,
      ((χ.Odd ∧ b = deriv (DirichletCharacter.LFunction χ) 0 /
          DirichletCharacter.LFunction χ 0) ∨
        (χ.Even ∧ Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b))) →
      ∀ Z : Finset ℂ, (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1) →
      ‖b + ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / ρ‖ ≤
        C * Real.log q := by
  obtain ⟨m, M, hm, hM, hgam⟩ := GammaR_compact_bounds
  refine ⟨((16 * (4 / 5 : ℝ) ^ 2 / (4 / 5 - 7 / 10) ^ 3 +
        1 / (((99 / 100 : ℝ) ^ 2 / (9 / 10) - 9 / 10) * Real.log ((99 / 100) / (9 / 10)))) / 3 +
      1 / Real.log ((99 / 100 : ℝ) / (4 / 5))) *
        (Real.log (4 * (100 + 100 * (M / m))) / Real.log 2 + 4), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 4 / 5 - 7 / 10 := by norm_num
    have h2 : (0 : ℝ) < (99 / 100 : ℝ) ^ 2 / (9 / 10) - 9 / 10 := by norm_num
    have h3 : (0 : ℝ) < Real.log ((99 / 100 : ℝ) / (9 / 10)) := Real.log_pos (by norm_num)
    have hKb : (0 : ℝ) < M / m := by positivity
    have hkb : (0 : ℝ) < 4 * (100 + 100 * (M / m)) := by nlinarith
    have h5 : (0 : ℝ) < Real.log (4 * (100 + 100 * (M / m))) := Real.log_pos (by
      have : (0 : ℝ) < 100 + 100 * (M / m) := by nlinarith
      nlinarith)
    have h6 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h4 : (0 : ℝ) < Real.log ((99 / 100 : ℝ) / (4 / 5)) := Real.log_pos (by norm_num)
    positivity
  · intro q _ χ hprim hχ b hb Z hZ
    rcases χ.even_or_odd with he | ho
    · have ha : (χ.Even ∧ (0 : ℕ) = 0) ∨ (χ.Odd ∧ (0 : ℕ) = 1) := Or.inl ⟨he, rfl⟩
      have hcore := leaf_core hm hM hgam χ hprim hχ (a := 0) ha hb Z hZ
      refine hcore.trans ?_
      have h := mul_le_mul_of_nonneg_left (log_bound hm hM hχ) (le_of_lt (coef_pos hm hM))
      exact h.trans (le_of_eq (by ring))
    · have ha : (χ.Even ∧ (1 : ℕ) = 0) ∨ (χ.Odd ∧ (1 : ℕ) = 1) := Or.inr ⟨ho, rfl⟩
      have hcore := leaf_core hm hM hgam χ hprim hχ (a := 1) ha hb Z hZ
      refine hcore.trans ?_
      have h := mul_le_mul_of_nonneg_left (log_bound hm hM hχ) (le_of_lt (coef_pos hm hM))
      exact h.trans (le_of_eq (by ring))


end LeanLab.PNTPort.ExplicitPsi1.CharTrivial1122
