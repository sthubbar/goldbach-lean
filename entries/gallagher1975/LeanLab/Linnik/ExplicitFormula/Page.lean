module

public import LeanLab.Linnik.ExplicitFormula.Defs
public import LeanLab.PNTPort.DirichletZF.RealZero

/-!
# The exceptional zero is the only zero near 1, Davenport ch. 14

AI wrote the Lean code. Binary Goldbach is OPEN.
Davenport, Multiplicative Number Theory, ch. 14: there is an absolute `c > 0` such that for a
primitive `χ` of conductor `q ≤ T`, `L(s, χ)` has at most one zero, counted with multiplicity,
in `σ ≥ 1 - c/log T`, `|t| ≤ T`; Gallagher 1975 p.127 uses this. Lab inputs:
`LeanLab.PNTPort.DirichletZF.Page`, `Exceptional.zero_free_region_all`,
`LeanLab.Linnik.Decomp1532b.page_real`, `primitive_local_zero_order_sum`.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex Finset

open LeanLab.PNTPort.DirichletZF in
/-- Elementary: `log B(t) ≤ K log T` when `q ≤ T` and `|t| ≤ T`; a copy of
`Decomp1532b.log_Bt_le_log_height`, restated so this file does not import Decomp1532b. -/
theorem page_log_Bt_le : ∃ K : ℝ, 0 < K ∧ ∀ {q : ℕ} [NeZero q] {T t : ℝ},
    2 ≤ T → (q : ℝ) ≤ T → |t| ≤ T → Real.log (Bt q t) ≤ K * Real.log T := by
  let A := Real.log (6 * Z)
  let K := A / Real.log 2 + 2
  have hZ := one_le_Z
  have hA : 0 ≤ A := Real.log_nonneg (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro q _ T t hT hq ht
  have hT0 : 0 < T := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hBt : Bt q t ≤ (6 * Z) * T ^ 2 := by
    unfold Bt
    have h1 := mul_le_mul hq (show |t| + 3 ≤ 3 * T by linarith) (by positivity) hT0.le
    nlinarith [mul_le_mul_of_nonneg_right h1 (show 0 ≤ Z by linarith)]
  calc
    Real.log (Bt q t) ≤ Real.log ((6 * Z) * T ^ 2) :=
      Real.log_le_log (by unfold Bt; positivity) hBt
    _ = A + 2 * Real.log T := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; norm_num [A]
    _ ≤ K * Real.log T := by
      have hmul : A ≤ A / Real.log 2 * Real.log T := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
        exact mul_le_mul_of_nonneg_left hlog hA
      dsimp [K]
      nlinarith

/-- Elementary: a zero-free box for `ζ` near `1` up to height `T`; a copy of
`Decomp1532b.zeta_height_box_nonzero`, de la Vallee Poussin, Davenport ch. 13. -/
theorem page_zeta_box : ∃ b : ℝ, 0 < b ∧ ∀ {T : ℝ}, 2 ≤ T →
    ∀ ρ : ℂ, 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T → riemannZeta ρ ≠ 0 := by
  obtain ⟨A, hA, hlarge⟩ := ZetaZeroFree1
  obtain ⟨σ, hσ, hsmall⟩ := ZetaNoZerosInBox 3
  let b := min A ((1 - σ) * Real.log 2)
  have hb : 0 < b := lt_min hA.1 (mul_pos (by linarith) (Real.log_pos (by norm_num)))
  refine ⟨b, hb, ?_⟩
  intro T hT ρ hβ ht
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hrep : (ρ.re : ℂ) + ρ.im * Complex.I = ρ := by simp
  by_cases h1 : 1 ≤ ρ.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  by_cases ht3 : |ρ.im| ≤ 3
  · have hcmp : b / Real.log T ≤ 1 - σ := by
      apply (div_le_iff₀ hlT).mpr
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
      have hmin : b ≤ (1 - σ) * Real.log 2 := min_le_right _ _
      nlinarith
    simpa only [hrep] using hsmall ρ.im ht3 ρ.re (by linarith)
  · have ht3' : 3 < |ρ.im| := lt_of_not_ge ht3
    have hlogt : 0 < Real.log |ρ.im| := Real.log_pos (by linarith)
    have hcomp : b / Real.log T ≤ A / Real.log |ρ.im| := by
      exact (div_le_div_of_nonneg_right (min_le_left _ _) hlT.le).trans
        (div_le_div_of_nonneg_left hA.1.le hlogt (Real.log_le_log (by positivity) ht))
    have hh := hlarge ρ.re ρ.im ht3' ⟨by simpa only [Real.rpow_one] using
      (show 1 - A / Real.log |ρ.im| ≤ ρ.re by linarith), lt_of_not_ge h1⟩
    simpa only [hrep] using hh

open LeanLab.PNTPort.DirichletZF in
/-- Elementary: the order of `L(s, χ)` at `ρ` equals the order of its translate `fShift χ t`
at `ρ - (3/2 + i t)`. -/
theorem page_order_shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (ρ : ℂ) :
    analyticOrderNatAt (fShift χ t) (ρ - ((3 : ℂ) / 2 + I * t)) =
      analyticOrderNatAt χ.LFunction ρ := by
  have hfun : fShift χ t = χ.LFunction ∘ (fun z : ℂ ↦ z + ((3 : ℂ) / 2 + I * t)) := rfl
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ z + ((3 : ℂ) / 2 + I * t)) (ρ - ((3 : ℂ) / 2 + I * t)) := by
    fun_prop
  have hg' : deriv (fun z : ℂ ↦ z + ((3 : ℂ) / 2 + I * t)) (ρ - ((3 : ℂ) / 2 + I * t)) ≠ 0 := by
    rw [deriv_add_const, deriv_id'']; exact one_ne_zero
  unfold analyticOrderNatAt
  rw [hfun, analyticOrderAt_comp_of_deriv_ne_zero hg hg', sub_add_cancel]

open LeanLab.PNTPort.DirichletZF in
/-- Davenport ch. 14, Page's step for non-principal `χ`: zeros near `1` up to height `T`
are real by the zero-free region, and there is at most one, with multiplicity, by `page_count`. -/
theorem page_one_zero_nonprincipal : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → (q : ℝ) ≤ T → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ 1 - b / Real.log T ≤ ρ.re ∧ |ρ.im| ≤ T) →
        (∑ ρ ∈ S, mult χ ρ) ≤ 1 := by
  obtain ⟨K, hK, hlog⟩ := page_log_Bt_le
  obtain ⟨c, c', hc, hc', hreg⟩ := zero_free_region_real
  obtain ⟨cp, hcp, hcp31, hpc⟩ := page_count
  refine ⟨min (c / (2 * K)) (cp / K), lt_min (by positivity) (by positivity), ?_⟩
  intro T hT q _ χ hχ hq S hS
  set b := min (c / (2 * K)) (cp / K) with hbdef
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  -- every zero of `S` is real
  have hreal : ∀ ρ ∈ S, ρ.im = 0 := by
    intro ρ hρ
    obtain ⟨hz, hβ, ht⟩ := hS ρ hρ
    rcases (hreg q χ hχ).1 ρ hz with hleft | hright
    · exfalso
      have hlB : 0 < Real.log (Bt q ρ.im) := by linarith [one_le_log_Bt (N := q) ρ.im]
      have hd : c / (K * Real.log T) ≤ c / Real.log (Bt q ρ.im) :=
        div_le_div_of_nonneg_left hc.le hlB (hlog hT hq ht)
      have hpos : 0 < c / (2 * K) / Real.log T := by positivity
      have heq : c / (K * Real.log T) = 2 * (c / (2 * K) / Real.log T) := by field_simp
      have hb1 : b / Real.log T ≤ c / (2 * K) / Real.log T :=
        div_le_div_of_nonneg_right (min_le_left _ _) hlT.le
      rw [heq] at hd
      linarith
    · exact hright.2.2.2
  -- the box of `page_count`
  set Lg := Real.log (Bt q 0) with hLg
  have hLg1 : 1 ≤ Lg := one_le_log_Bt 0
  have hLgT : Lg ≤ K * Real.log T := hlog hT hq (by simp; linarith)
  have hbox : ∀ ρ ∈ S, 1 - cp / Lg ≤ ρ.re := by
    intro ρ hρ
    obtain ⟨-, hβ, -⟩ := hS ρ hρ
    have h1 : b / Real.log T ≤ cp / K / Real.log T :=
      div_le_div_of_nonneg_right (min_le_right _ _) hlT.le
    have h2 : cp / K / Real.log T ≤ cp / Lg := by
      rw [div_div]
      exact div_le_div_of_nonneg_left hcp.le (by linarith) hLgT
    linarith
  set F := (Tset hχ 0).filter (fun ρ ↦ 1 - cp / Real.log (Bt q 0) ≤ ρ.re + 3 / 2 ∧
      |ρ.im| ≤ cp / Real.log (Bt q 0))
  have hmapF : ∀ ρ ∈ S, ρ - 3 / 2 ∈ F := by
    intro ρ hρ
    obtain ⟨hz, -, -⟩ := hS ρ hρ
    have hb := hbox ρ hρ
    have him := hreal ρ hρ
    have hβ1 : ρ.re < 1 := by
      by_contra hcc; push Not at hcc
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcc hz
    have hη : cp / Lg ≤ 1 / 31 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    rw [Finset.mem_filter, mem_Tset]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have e : ρ - 3 / 2 = ((ρ.re - 3 / 2 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [him]
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    · show χ.LFunction (ρ - 3 / 2 + ((3 : ℂ) / 2 + I * ((0 : ℝ) : ℂ))) = 0
      simp only [Complex.ofReal_zero, mul_zero, add_zero, sub_add_cancel]; exact hz
    · simp only [sub_re]; norm_num; linarith
    · simp [him]; positivity
  have hinj : Set.InjOn (fun ρ : ℂ ↦ ρ - 3 / 2) (S : Set ℂ) :=
    fun x _ y _ h ↦ sub_left_injective h
  have hord : ∀ ρ, mult χ ρ = analyticOrderNatAt (fShift χ 0) (ρ - 3 / 2) := by
    intro ρ
    have := page_order_shift χ 0 ρ
    simp only [Complex.ofReal_zero, mul_zero, add_zero] at this
    rw [mult, this]
  calc (∑ ρ ∈ S, mult χ ρ)
      = ∑ ρ ∈ S.image (fun ρ : ℂ ↦ ρ - 3 / 2), analyticOrderNatAt (fShift χ 0) ρ := by
        rw [Finset.sum_image hinj]; exact Finset.sum_congr rfl (fun ρ _ ↦ hord ρ)
    _ ≤ ∑ ρ ∈ F, analyticOrderNatAt (fShift χ 0) ρ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hx
          exact hmapF ρ hρ
        · intros; exact Nat.zero_le _
    _ ≤ 1 := hpc q χ hχ


/-- Davenport ch. 14: at most one zero with multiplicity near `1`, per primitive character. -/
theorem page_one_zero : ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → (q : ℝ) ≤ T → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ 1 - c / Real.log T ≤ ρ.re ∧ |ρ.im| ≤ T ∧ ρ ≠ 1) →
        (∑ ρ ∈ S, mult χ ρ) ≤ 1 := by
  obtain ⟨bn, hbn, hn⟩ := page_one_zero_nonprincipal
  obtain ⟨bz, hbz, hz⟩ := page_zeta_box
  refine ⟨min bn bz, lt_min hbn hbz, ?_⟩
  intro T hT q _ χ hprim hq S hS
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  by_cases hχ : χ = 1
  · -- the principal primitive character has modulus `1`, so `L(s, χ) = ζ(s)`
    subst hχ
    have hq1 : q = 1 := by
      have h := hprim
      rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hq1
    have hS0 : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ρ hρ
      obtain ⟨h0, hβ, ht, -⟩ := hS ρ hρ
      rw [DirichletCharacter.LFunction_modOne_eq] at h0
      have hb : min bn bz / Real.log T ≤ bz / Real.log T :=
        div_le_div_of_nonneg_right (min_le_right _ _) hlT.le
      exact hz hT ρ (by linarith) ht h0
    simp [hS0]
  · refine hn T hT q χ hχ hq S (fun ρ hρ ↦ ?_)
    obtain ⟨h0, hβ, ht, -⟩ := hS ρ hρ
    have hb : min bn bz / Real.log T ≤ bn / Real.log T :=
      div_le_div_of_nonneg_right (min_le_left _ _) hlT.le
    exact ⟨h0, by linarith, ht⟩

end LeanLab.Linnik.ExplicitFormula
