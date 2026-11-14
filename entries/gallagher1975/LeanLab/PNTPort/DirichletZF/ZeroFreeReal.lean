module

public import LeanLab.PNTPort.DirichletZF.ZeroFree

/-!
# The zero-free region for every non-principal `χ`, away from the real axis

Lab proof, unit U-5110. AI wrote this file. Known mathematics, no cited input. It uses
`ShiftTwoBound` and `ZeroWindowFinite` from the ported StrongPNT file, Apache-2.0, the
PrimeNumberTheoremAnd contributors.

* `norm_logDeriv_euler_le`: `‖logDeriv(1 - p^{-s})‖ ≤ log p` for a prime `p` and `Re s ≥ 1`;
* `logDeriv_trivChar_sub_zeta`: `‖L'/L(s, χ₀) - ζ'/ζ(s)‖ ≤ log N` for `Re s > 1`, from
  `L(s, χ₀) = ζ(s) ∏_{p | N} (1 - p^{-s})`;
* `trivChar_shiftTwo_bound`: `-Re L'/L(1 + d + 2it, χ₀) ≤ C log |t| + log N`, `|t| ≥ 2`;
* `zero_free_real`: an absolute `c > 0` with `β ≤ 1 - c / log B(γ)` for every zero `β + iγ`,
  `|γ| ≥ 2`, of `L(s, χ)`, `χ` real non-principal;
* `zero_free_nonprincipal`: the same for every non-principal `χ`, `|γ| ≥ 2`.
The range `|γ| < 2` for real `χ`, where an exceptional zero may sit, is not covered.
-/

@[expose] public section


namespace LeanLab.PNTPort.DirichletZF

open Complex Set Filter

/-- One Euler factor of the principal character. -/
noncomputable def Ef (p : ℕ) (s : ℂ) : ℂ := 1 - (p : ℂ) ^ (-s)

lemma hasDerivAt_Ef {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    HasDerivAt (Ef p) ((p : ℂ) ^ (-s) * Complex.log p) s := by
  have h := ((hasDerivAt_id s).neg).const_cpow (c := (p : ℂ)) (Or.inl (by exact_mod_cast hp))
  have h2 := h.const_sub 1
  show HasDerivAt (fun x ↦ 1 - (p : ℂ) ^ (-x)) _ s
  convert h2 using 1
  · rfl
  · show _ = -((p : ℂ) ^ (-s) * Complex.log p * -1); ring

lemma norm_cpow_neg {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0, neg_re]

lemma rpow_neg_le_half {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 ≤ σ) :
    (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1 / p := by rw [Real.rpow_neg_one]; ring
    _ ≤ 1 / 2 := by gcongr

lemma Ef_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) : Ef p s ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := by unfold Ef at h; linear_combination -h
  have := norm_cpow_neg hp.ne_zero s
  rw [h1, norm_one] at this
  have := rpow_neg_le_half hp hs
  linarith

lemma norm_logDeriv_euler_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (Ef p) s‖ ≤ Real.log p := by
  rw [logDeriv_apply, (hasDerivAt_Ef hp.ne_zero s).deriv]
  set x : ℝ := (p : ℝ) ^ (-s.re)
  have hx : ‖(p : ℂ) ^ (-s)‖ = x := norm_cpow_neg hp.ne_zero s
  have hxh : x ≤ 1 / 2 := rpow_neg_le_half hp hs
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg p)]
  have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hden : 1 - x ≤ ‖Ef p s‖ := by
    unfold Ef
    have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one, hx] at this
    linarith
  have hpos : 0 < 1 - x := by linarith
  rw [norm_div, norm_mul, hx, hlog, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlp,
    div_le_iff₀ (lt_of_lt_of_le hpos hden)]
  nlinarith

/-- `P(s) = ∏_{p | N} (1 - p^{-s})`. -/
noncomputable def Pfac (N : ℕ) : ℂ → ℂ := ∏ p ∈ N.primeFactors, Ef p

lemma Pfac_apply (N : ℕ) (s : ℂ) : Pfac N s = ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s)) := by
  simp [Pfac, Finset.prod_apply, Ef]

lemma norm_logDeriv_Pfac_le {N : ℕ} [NeZero N] {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (Pfac N) s‖ ≤ Real.log N := by
  have hpr : ∀ p ∈ N.primeFactors, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  rw [Pfac, logDeriv_prod (fun p hp ↦ Ef_ne_zero (hpr p hp) hs)
    (fun p hp ↦ (hasDerivAt_Ef (hpr p hp).ne_zero s).differentiableAt)]
  calc ‖∑ p ∈ N.primeFactors, logDeriv (Ef p) s‖
      ≤ ∑ p ∈ N.primeFactors, ‖logDeriv (Ef p) s‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ N.primeFactors, Real.log p :=
        Finset.sum_le_sum fun p hp ↦ norm_logDeriv_euler_le (hpr p hp) hs
    _ = Real.log (∏ p ∈ N.primeFactors, (p : ℝ)) := by
        rw [Real.log_prod]
        intro p hp; exact_mod_cast (hpr p hp).ne_zero
    _ ≤ Real.log N := by
        have hd := Nat.prod_primeFactors_dvd N
        have hle : ∏ p ∈ N.primeFactors, p ≤ N := Nat.le_of_dvd
          (Nat.pos_of_ne_zero (NeZero.ne N)) hd
        apply Real.log_le_log
        · apply Finset.prod_pos; intro p hp; exact_mod_cast (hpr p hp).pos
        · rw [← Nat.cast_prod]; exact_mod_cast hle

lemma diffAt_prod {ι : Type*} (u : Finset ι) (f : ι → ℂ → ℂ) (s : ℂ)
    (h : ∀ i ∈ u, DifferentiableAt ℂ (f i) s) : DifferentiableAt ℂ (∏ i ∈ u, f i) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

lemma Pfac_differentiableAt (N : ℕ) (s : ℂ) : DifferentiableAt ℂ (Pfac N) s := by
  rw [Pfac]
  refine diffAt_prod _ _ _ ?_
  intro p hp
  exact (hasDerivAt_Ef (Nat.prime_of_mem_primeFactors hp).ne_zero s).differentiableAt

lemma Pfac_ne_zero (N : ℕ) {s : ℂ} (hs : 1 ≤ s.re) : Pfac N s ≠ 0 := by
  rw [Pfac, Finset.prod_apply]
  exact Finset.prod_ne_zero_iff.mpr fun p hp ↦
    Ef_ne_zero (Nat.prime_of_mem_primeFactors hp) hs

/-- `‖L'/L(s, χ₀) - ζ'/ζ(s)‖ ≤ log N` on `Re s > 1`. -/
theorem logDeriv_trivChar_sub_zeta {N : ℕ} [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) s /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) s -
      deriv riemannZeta s / riemannZeta s‖ ≤ Real.log N := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hev : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) =ᶠ[nhds s]
      Pfac N * riemannZeta := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    rw [Pi.mul_apply, Pfac_apply]
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz
  have hval := hev.eq_of_nhds
  have hld : deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) s /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) s =
      logDeriv (Pfac N * riemannZeta) s := by
    rw [logDeriv_apply, hev.deriv_eq, hval]
  rw [hld, logDeriv_mul s (Pfac_ne_zero N hs.le) (riemannZeta_ne_zero_of_one_lt_re hs)
    (Pfac_differentiableAt N s) (differentiableAt_riemannZeta hs1),
    show logDeriv riemannZeta s = deriv riemannZeta s / riemannZeta s from logDeriv_apply _ _,
    add_sub_cancel_right]
  exact norm_logDeriv_Pfac_le hs.le

/-- The principal character at `1 + d + 2it`, `|t| ≥ 2`. -/
theorem trivChar_shiftTwo_bound : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (d : ℝ),
    d ∈ Ioo 0 1 → ∀ t : ℝ, 2 ≤ |t| →
      -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) (1 + d + 2 * I * t) /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) (1 + d + 2 * I * t)).re ≤
        C * Real.log |t| + Real.log N := by
  obtain ⟨C, hC, h⟩ := ShiftTwoBound
  refine ⟨C, hC, fun N _ d hd t ht ↦ ?_⟩
  have hfin : (ZeroWindow (2 * t)).Finite :=
    ZeroWindowFinite (by rw [abs_mul, abs_two]; linarith)
  have hz := h d hd t ht hfin
  have hs : 1 < (1 + d + 2 * I * t : ℂ).re := by simp; linarith [hd.1]
  have hdiff := logDeriv_trivChar_sub_zeta (N := N) hs
  have h1 := Complex.re_le_norm (-(deriv (DirichletCharacter.LFunction
    (1 : DirichletCharacter ℂ N)) (1 + d + 2 * I * t) / DirichletCharacter.LFunction
    (1 : DirichletCharacter ℂ N) (1 + d + 2 * I * t) - deriv riemannZeta (1 + d + 2 * I * t) /
    riemannZeta (1 + d + 2 * I * t)))
  rw [norm_neg, neg_re, sub_re] at h1
  have h2 : -(deriv riemannZeta (1 + d + 2 * I * t) / riemannZeta (1 + d + 2 * I * t)).re ≤
      C * Real.log |t| := hz
  linarith

/-- The closing algebra of the de la Vallee Poussin argument. -/
lemma beta_le_of_comb {D β : ℝ} (hD : 1 < D)
    (h : 4 / (1 + 1 / (4 * D) - β) ≤ 3 / (1 / (4 * D)) + D) (hpos : 0 < 1 + 1 / (4 * D) - β) :
    β ≤ 1 - 3 / (52 * D) := by
  have hDpos : 0 < D := by linarith
  have h3d : 3 / (1 / (4 * D)) = 12 * D := by field_simp; ring
  rw [h3d] at h
  have h13 : 4 ≤ 13 * D * (1 + 1 / (4 * D) - β) := by
    rw [div_le_iff₀ hpos] at h; linarith
  have : 4 / (13 * D) ≤ 1 + 1 / (4 * D) - β := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have e : 1 + 1 / (4 * D) - 4 / (13 * D) = 1 - 3 / (52 * D) := by
    field_simp; ring
  linarith

lemma log_le_log_Bt {N : ℕ} [NeZero N] (t : ℝ) (ht : 2 ≤ |t|) :
    Real.log |t| + Real.log N ≤ 2 * Real.log (Bt N t) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hZ := one_le_Z
  have ht0 := abs_nonneg t
  have a : |t| + 3 ≤ N * (|t| + 3) := le_mul_of_one_le_left (by positivity) hN
  have a' : (N : ℝ) ≤ N * (|t| + 3) := le_mul_of_one_le_right (by positivity) (by linarith)
  have b : N * (|t| + 3) ≤ N * (|t| + 3) * Z := le_mul_of_one_le_right (by positivity) hZ
  have e : Bt N t = 2 * (N * (|t| + 3) * Z) := by unfold Bt; ring
  have hB1 : |t| ≤ Bt N t := by rw [e]; linarith
  have hB2 : (N : ℝ) ≤ Bt N t := by rw [e]; linarith
  have := Real.log_le_log (by linarith) hB1
  have := Real.log_le_log (by linarith) hB2
  linarith

/-- The zero-free region for real non-principal characters, `|γ| ≥ 2`. -/
theorem zero_free_real : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 → ∀ ρ : ℂ,
      DirichletCharacter.LFunction χ ρ = 0 → 2 ≤ |ρ.im| →
        ρ.re ≤ 1 - c / Real.log (Bt N ρ.im) := by
  obtain ⟨A, hA, hprin⟩ := principal_bound
  obtain ⟨C, hC, htwo⟩ := trivChar_shiftTwo_bound
  set M : ℝ := 4 * K0 + 2 * C + 2 + 3 * A + 16 with hM
  have hK := K0_pos
  have hMpos : 1 < M := by rw [hM]; linarith
  refine ⟨3 / (52 * M), by positivity, fun N _ χ hχ hχ2 ρ hρ hγ ↦ ?_⟩
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
  have b0 := hprin N d hd0
  have b1 := shiftOne_bound hχ hd0 hρ
  have b2 := htwo N d hd0 t hγ
  have hlogs := log_le_log_Bt (N := N) t hγ
  have key := three_four_one χ (show 1 < 1 + d by linarith [hd0.1]) t
  rw [hχ2] at key
  simp only [Complex.ofReal_add, Complex.ofReal_one] at key
  have c1 : (1 : ℂ) + d + t * I = 1 + d + I * t := by ring
  have c2 : (1 : ℂ) + d + 2 * t * I = 1 + d + 2 * I * t := by ring
  rw [c1, c2] at key
  simp only [neg_div_re_eq] at key b0
  rw [← ht] at b1
  rw [← hLg] at b1 hlogs
  have hcomb : 4 / (1 + d - ρ.re) ≤ 3 / d + D := by
    have e4 : 4 / (1 + d - ρ.re) = 4 * (1 / (1 + d - ρ.re)) := by ring
    have e3 : 3 / d = 3 * (1 / d) := by ring
    have hA' : A ≤ A * Lg := le_mul_of_one_le_right (by linarith) hL1
    have hlt : Real.log |t| ≤ 2 * Lg := by
      have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
      linarith
    have h2 := mul_le_mul_of_nonneg_left hlt hC.le
    have hlt0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
    have hlN : Real.log N ≤ 2 * Lg := by linarith
    rw [e4, e3, hD, hM]
    linarith
  have e : 3 / (52 * M) / Lg = 3 / (52 * D) := by rw [hD]; field_simp
  rw [e]
  exact beta_le_of_comb hD1 hcomb hpos

/-- Every non-principal character, `|γ| ≥ 2`. -/
theorem zero_free_nonprincipal : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ ρ : ℂ,
      DirichletCharacter.LFunction χ ρ = 0 → 2 ≤ |ρ.im| →
        ρ.re ≤ 1 - c / Real.log (Bt N ρ.im) := by
  obtain ⟨c1, hc1, h1⟩ := zero_free_complex
  obtain ⟨c2, hc2, h2⟩ := zero_free_real
  refine ⟨min c1 c2, lt_min hc1 hc2, fun N _ χ hχ ρ hρ hγ ↦ ?_⟩
  have hL := one_le_log_Bt (N := N) ρ.im
  have hLpos : 0 < Real.log (Bt N ρ.im) := by linarith
  by_cases hsq : χ ^ 2 = 1
  · have := h2 N χ hχ hsq ρ hρ hγ
    have : min c1 c2 / Real.log (Bt N ρ.im) ≤ c2 / Real.log (Bt N ρ.im) :=
      div_le_div_of_nonneg_right (min_le_right _ _) hLpos.le
    linarith
  · have := h1 N χ hsq ρ hρ
    have : min c1 c2 / Real.log (Bt N ρ.im) ≤ c1 / Real.log (Bt N ρ.im) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
    linarith

end LeanLab.PNTPort.DirichletZF

