module

public import LeanLab.BhowmikGrimmelt2026.TotientRatio247

/-!
Supply for the coefficient majorant in Decomp247a.
Source: Pintz Part I page 20 display 7.13.
The residue fiber proof is Montgomery Vaughan 1975 pages 359 and 360.
Existing statements remain sealed.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- The integer frequency twisted sum is a shifted standard Gauss sum.
Source: Montgomery Vaughan page 359 display 5.3, before grouping residue fibers. -/
theorem cChi_int_gauss436 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (N : ℤ) :
    cChi χ N = gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift (N : ZMod q)) := by
  unfold cChi gaussSum
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  rw [AddChar.mulShift_apply]
  have he : (N : ZMod q) * a = ((N * (a.val : ℤ) : ℤ) : ZMod q) := by simp
  rw [he, ZMod.stdAddChar_coe]
  unfold ee
  congr 1
  push_cast
  ring

/-- LEAF. Montgomery Vaughan 1975 page 359, Case 1 after display 5.3.
Pintz Part I page 11 Lemma 4.4 gives the same vanishing alternative.
Residue fiber cancellation when the primitive conductor does not divide q1.
This concerns one finite character sum and no coefficient denominator or series. -/
theorem twisted_fiber_vanish436 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hd : r ∣ q)
    (N : ℤ) (hbad : ¬ r ∣ q / Nat.gcd q N.natAbs) :
    cChi (DirichletCharacter.changeLevel hd χ) N = 0 := by
  by_contra hn
  rw [cChi_int_gauss436] at hn
  let d := q / Nat.gcd q N.natAbs
  have hdq : d ∣ q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q N.natAbs)
  have hmul : q ∣ N.natAbs * d := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_right q N.natAbs
    refine ⟨k, ?_⟩
    calc
      N.natAbs * d = (Nat.gcd q N.natAbs * k) * d := by conv_lhs => rw [hk]
      _ = (d * Nat.gcd q N.natAbs) * k := by ring
      _ = q * k := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left q N.natAbs)]
  have hmulInt : (q : ℤ) ∣ N * (d : ℤ) := Int.natCast_dvd.mpr (by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hmul)
  have hz : (N : ZMod q) * (d : ZMod q) = 0 := by
    rw [← Int.cast_natCast d, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hmulInt
  have hp : ((ZMod.stdAddChar (N := q)).mulShift (N : ZMod q)).mulShift (d : ZMod q) = 1 := by
    ext a
    simp only [AddChar.mulShift_apply, ← mul_assoc, hz, zero_mul, AddChar.map_zero_eq_one,
      AddChar.one_apply]
  have hf := factorsThrough_of_gaussSum_ne_zero
    ((ZMod.stdAddChar (N := q)).mulShift (N : ZMod q)) hdq hp hn
  have hc := DirichletCharacter.conductor_dvd_of_mem_conductorSet
    (DirichletCharacter.changeLevel hd χ) hf
  rw [DirichletCharacter.conductor_changeLevel, hχ] at hc
  exact hbad hc

/-! ### Unit residue fibers  (inlined from `LeanLab.BhowmikGrimmelt2026.UnitFibers436`) -/

/-- Each unit fiber has cardinality the source totient divided by the target totient. -/
private theorem ufiber_card_mul {m q : ℕ} [NeZero m] [NeZero q]
    (hd : m ∣ q) (u : (ZMod m)ˣ) :
    ((Finset.univ.filter (fun a : (ZMod q)ˣ => ZMod.unitsMap hd a = u)).card) *
      Nat.totient m = Nat.totient q := by
  classical
  have hk := Subgroup.card_ker_mul_card_of_surjective (ZMod.unitsMap_surjective hd)
  have hcard :
      ((Finset.univ.filter (fun a : (ZMod q)ˣ => ZMod.unitsMap hd a = 1)).card) *
        Nat.totient m = Nat.totient q := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, MonoidHom.mem_ker,
      ZMod.card_units_eq_totient] using hk
  have hu := MonoidHom.card_fiber_eq_of_mem_range (ZMod.unitsMap hd)
    (ZMod.unitsMap_surjective hd u) (ZMod.unitsMap_surjective hd 1)
  rw [hu]
  exact hcard

/-- The real unit fiber count is the totient quotient in the twisted sum formula. -/
private theorem ufiber_card {m q : ℕ} [NeZero m] [NeZero q]
    (hd : m ∣ q) (u : (ZMod m)ˣ) :
    (((Finset.univ.filter (fun a : (ZMod q)ˣ => ZMod.unitsMap hd a = u)).card) : ℝ) =
      (Nat.totient q : ℝ) / (Nat.totient m : ℝ) := by
  have hm : (Nat.totient m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))).ne'
  apply (eq_div_iff hm).mpr
  exact_mod_cast ufiber_card_mul hd u

/-- Summing a function pulled back along unit reduction multiplies its sum by the fiber count. -/
private theorem ufiber_sum {m q : ℕ} [NeZero m] [NeZero q]
    (hd : m ∣ q) (F : (ZMod m)ˣ → ℂ) :
    (∑ a : (ZMod q)ˣ, F (ZMod.unitsMap hd a)) =
      ((Nat.totient q : ℂ) / (Nat.totient m : ℂ)) * ∑ u : (ZMod m)ˣ, F u := by
  classical
  have hc (u : (ZMod m)ˣ) :
      (((Finset.univ.filter (fun a : (ZMod q)ˣ => ZMod.unitsMap hd a = u)).card) : ℂ) =
        (Nat.totient q : ℂ) / (Nat.totient m : ℂ) := by
    have h := congrArg Complex.ofReal (ufiber_card hd u)
    push_cast at h
    exact h
  rw [← Finset.sum_fiberwise' Finset.univ (ZMod.unitsMap hd) F]
  simp_rw [Finset.sum_const, nsmul_eq_mul, hc]
  rw [Finset.mul_sum]

/-! ### Residue fiber reductions of the twisted sum
(inlined from `LeanLab.BhowmikGrimmelt2026.GaussReduction443` and
`LeanLab.BhowmikGrimmelt2026.ReducedFrequency443`) -/

/-- Restrict a twisted character sum to units since every nonunit term vanishes. -/
private theorem cChi_units_p {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (N : ℤ) :
    cChi χ N = ∑ a : (ZMod q)ˣ,
      χ a * ee ((N : ℝ) * ((a : ZMod q).val : ℝ) / q) := by
  classical
  unfold cChi
  simp only [mul_comm (N : ℝ)]
  symm
  apply Fintype.sum_of_injective (fun a : (ZMod q)ˣ => (a : ZMod q))
    Units.val_injective
    (fun a => χ a * ee (((a : ZMod q).val : ℝ) * N / q))
    (fun a => χ a * ee ((a.val : ℝ) * N / q)) ?_ (fun _ => rfl)
  intro a ha
  rw [MulChar.map_nonunit χ (fun hu => ha ⟨hu.unit, hu.unit_spec⟩), zero_mul]

/-- The additive phase descends when the modulus and frequency share the same factor. -/
private theorem stdAddChar_factor_p {m q : ℕ} [NeZero m] [NeZero q]
    (hd : m ∣ q) (g : ℕ) (hq : q = m * g) (M : ℤ) (a : ZMod q) :
    ZMod.stdAddChar ((((g : ℤ) * M * (a.val : ℤ)) : ℤ) : ZMod q) =
      ZMod.stdAddChar ((M * (a.val : ℤ) : ℤ) : ZMod m) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hg : (g : ℂ) ≠ 0 := by
    have hg' : g ≠ 0 := by intro hg; simp [hg] at hq; exact NeZero.ne q hq
    exact_mod_cast hg'
  have hcq : (q : ℂ) = (m : ℂ) * (g : ℂ) := by exact_mod_cast hq
  rw [hcq]
  field_simp
  <;> ring

/-- Exact frequency reduction along unit residue fibers. -/
private theorem cChi_factor_p {m q : ℕ} [NeZero m] [NeZero q]
    (χ : DirichletCharacter ℂ m) (hd : m ∣ q)
    (g : ℕ) (hq : q = m * g) (M : ℤ) :
    cChi (DirichletCharacter.changeLevel hd χ) ((g : ℤ) * M) =
      ((Nat.totient q : ℂ) / (Nat.totient m : ℂ)) * cChi χ M := by
  rw [cChi_units_p, cChi_units_p]
  have hterm (a : (ZMod q)ˣ) :
      DirichletCharacter.changeLevel hd χ a *
          ee ((((g : ℤ) * M : ℤ) : ℝ) * ((a : ZMod q).val : ℝ) / q) =
        χ (ZMod.unitsMap hd a) *
          ee ((M : ℝ) * ((ZMod.unitsMap hd a : ZMod m).val : ℝ) / m) := by
    have hc : DirichletCharacter.changeLevel hd χ a = χ (ZMod.unitsMap hd a) := by
      simp [DirichletCharacter.changeLevel_def]
    rw [hc]
    congr 1
    have he := stdAddChar_factor_p hd g hq M (a : ZMod q)
    have hleft :
        ZMod.stdAddChar ((((g : ℤ) * M) * ((a : ZMod q).val : ℤ) : ℤ) : ZMod q) =
          ee (((((g : ℤ) * M : ℤ) : ℝ) * ((a : ZMod q).val : ℝ)) / q) := by
      rw [ZMod.stdAddChar_coe]
      unfold ee
      congr 1
      push_cast
      ring
    rw [hleft] at he
    have hcast : (((a : ZMod q).val : ℕ) : ZMod m) = (ZMod.unitsMap hd a : ZMod m) := by
      simp [ZMod.unitsMap_val]
    have hr : ZMod.stdAddChar ((M * ((a : ZMod q).val : ℤ) : ℤ) : ZMod m) =
        ee ((M : ℝ) * ((ZMod.unitsMap hd a : ZMod m).val : ℝ) / m) := by
      have hz : ((M * ((a : ZMod q).val : ℤ) : ℤ) : ZMod m) =
          ((M * ((ZMod.unitsMap hd a : ZMod m).val : ℤ) : ℤ) : ZMod m) := by
        push_cast
        rw [hcast, ZMod.natCast_zmod_val]
      rw [hz, ZMod.stdAddChar_coe]
      unfold ee
      congr 1
      push_cast
      ring
    exact he.trans hr
  simp_rw [hterm]
  exact ufiber_sum hd (fun a : (ZMod m)ˣ =>
    χ a * ee ((M : ℝ) * ((a : ZMod m).val : ℝ) / m))

/-- Dividing the modulus and integer frequency by their gcd produces a unit frequency. -/
private theorem gcd_freq_unit_p {q : ℕ} [NeZero q] (N : ℤ) :
    IsUnit ((N / (Nat.gcd q N.natAbs : ℤ) : ℤ) : ZMod (q / Nat.gcd q N.natAbs)) := by
  have hg : 0 < Nat.gcd q N.natAbs := Nat.gcd_pos_of_pos_left _
    (Nat.pos_of_ne_zero (NeZero.ne q))
  have h := Int.gcd_ediv_gcd_ediv_gcd (i := (q : ℤ)) (j := N) (by
    simpa only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast] using hg)
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one]
  simpa only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast, ← Int.natCast_ediv] using h

/-- A unit frequency does not change the modulus of a twisted sum. -/
private theorem cChi_unit_norm_p {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (M : ℤ) (hM : IsUnit (M : ZMod q)) :
    ‖cChi χ M‖ = ‖cChi χ 1‖ := by
  rw [cChi_int_gauss436, ← hM.unit_spec, gaussSum_mulShift_eq, norm_mul,
    DirichletCharacter.unit_norm_eq_one, one_mul, cChi_int_gauss436]
  simp

/-- Exact gcd frequency reduction for a lifted character. -/
private theorem cChi_gcd_factor_p {m q : ℕ} [NeZero m] [NeZero q]
    (χ : DirichletCharacter ℂ m) (N : ℤ)
    (hm : m = q / Nat.gcd q N.natAbs) :
    cChi (DirichletCharacter.changeLevel
        (hm ▸ Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q N.natAbs)) χ) N =
      ((Nat.totient q : ℂ) / (Nat.totient m : ℂ)) *
        cChi χ (N / (Nat.gcd q N.natAbs : ℤ)) := by
  have hg : (Nat.gcd q N.natAbs : ℤ) ∣ N :=
    Int.natCast_dvd.mpr (Nat.gcd_dvd_right q N.natAbs)
  have hq : q = m * Nat.gcd q N.natAbs := by
    rw [hm, Nat.div_mul_cancel (Nat.gcd_dvd_left q N.natAbs)]
  have hN : (Nat.gcd q N.natAbs : ℤ) * (N / (Nat.gcd q N.natAbs : ℤ)) = N :=
    Int.mul_ediv_cancel' hg
  convert cChi_factor_p χ
    (hm ▸ Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q N.natAbs))
    (Nat.gcd q N.natAbs) hq (N / (Nat.gcd q N.natAbs : ℤ)) using 1
  rw [hN]

/-! ### The modulus of a primitive Gauss sum over `ZMod n`
(ingredient not in Mathlib 4.35, which has `gaussSum_mul_gaussSum_eq_card` only over a field;
from the earlier numerical pass on this unit, re-checked here by compilation) -/

section PrimitiveGauss

variable {N : ℕ} [NeZero N]

/-- Summation over `ZMod N` is invariant under `k ↦ -k`. -/
private lemma sum_neg_index (f : ZMod N → ℂ) : ∑ k : ZMod N, f (-k) = ∑ k : ZMod N, f k :=
  Fintype.sum_equiv (Equiv.neg _) _ _ fun _ => rfl

/-- The double DFT of a function on `ZMod N`, at a point `j`. -/
private lemma dft_dft_apply (Φ : ZMod N → ℂ) (j : ZMod N) :
    ZMod.dft (ZMod.dft Φ) j = (N : ℂ) * Φ (-j) := by
  have h := congrFun (ZMod.dft_dft Φ) j
  simpa [smul_eq_mul] using h

/-- For primitive `χ`, the double DFT of `χ` at `j` is `gaussSum χ ψ` times the Gauss sum of
`χ⁻¹` at frequency `j`. -/
private theorem mul_gaussSum_mulShift {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (j : ZMod N) :
    (N : ℂ) * χ (-j) = gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
      gaussSum χ⁻¹ ((ZMod.stdAddChar : AddChar (ZMod N) ℂ).mulShift j) := by
  classical
  rw [← dft_dft_apply, ZMod.dft_apply]
  have hterm : ∀ k : ZMod N,
      ZMod.stdAddChar (-(k * j)) * ZMod.dft (χ : ZMod N → ℂ) k =
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
          (χ⁻¹ (-k) * ZMod.stdAddChar (-(k * j))) := by
    intro k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum]
    ring
  have hstep : ∑ k : ZMod N, (χ⁻¹ (-k) * ZMod.stdAddChar (-(k * j)))
      = ∑ k : ZMod N, (χ⁻¹ k * ZMod.stdAddChar (k * j)) := by
    have e1 : ∑ k : ZMod N, (χ⁻¹ (-k) * ZMod.stdAddChar (-(k * j)))
        = ∑ k : ZMod N, (χ⁻¹ (-k) * ZMod.stdAddChar ((-k) * j)) :=
      Finset.sum_congr rfl fun k _ => by rw [neg_mul]
    rw [e1, sum_neg_index (fun k : ZMod N => χ⁻¹ k * ZMod.stdAddChar (k * j))]
  calc ∑ k : ZMod N, ZMod.stdAddChar (-(k * j)) * ZMod.dft (χ : ZMod N → ℂ) k
      = ∑ k : ZMod N, gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
          (χ⁻¹ (-k) * ZMod.stdAddChar (-(k * j))) := Finset.sum_congr rfl fun k _ => hterm k
    _ = gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
          ∑ k : ZMod N, (χ⁻¹ (-k) * ZMod.stdAddChar (-(k * j))) := by
        rw [Finset.mul_sum]
    _ = gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
          ∑ k : ZMod N, (χ⁻¹ k * ZMod.stdAddChar (k * j)) := by rw [hstep]
    _ = gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
          gaussSum χ⁻¹ ((ZMod.stdAddChar : AddChar (ZMod N) ℂ).mulShift j) := by
        rw [gaussSum]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by rw [AddChar.mulShift_apply, mul_comm j k]

/-- **A primitive Gauss sum over the composite modulus `ZMod n` has modulus `√n`.** -/
private theorem gaussSum_norm_sq_primitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ)‖ ^ 2 = (N : ℝ) := by
  set τ := gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) with hτ
  have h := mul_gaussSum_mulShift (N := N) hχ (-1 : ZMod N)
  rw [neg_neg, map_one, mul_one] at h
  have hconj : (starRingEnd ℂ) τ = gaussSum χ⁻¹
      ((ZMod.stdAddChar : AddChar (ZMod N) ℂ).mulShift (-1)) := by
    rw [hτ]
    exact (star_gaussSum_eq χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ)).trans (by
      rw [AddChar.inv_mulShift])
  have hN : τ * (starRingEnd ℂ) τ = (N : ℂ) := by
    rw [hconj]
    exact h.symm
  have h1 : (‖τ‖ : ℂ) ^ 2 = (N : ℂ) := (Complex.mul_conj' τ).symm.trans hN
  have h2 : ‖τ‖ ^ 2 = (N : ℝ) := by
    have hpoly : ((‖τ‖ : ℂ) ^ 2).re = ‖τ‖ ^ 2 := by
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hthis := congrArg Complex.re h1
    rw [hpoly] at hthis
    simpa using hthis
  exact h2

end PrimitiveGauss

/-- The twisted sum at frequency one is the Gauss sum against the standard additive character. -/
private theorem cChi_one_eq_std {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    cChi χ 1 = ∑ a : ZMod q, χ a * ZMod.stdAddChar a := by
  unfold cChi
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  have ha : a = (((a.val : ℤ)) : ZMod q) := by
    push_cast
    exact (ZMod.natCast_zmod_val a).symm
  conv_rhs => rw [ha]
  rw [ZMod.stdAddChar_coe]
  unfold ee
  congr 1
  push_cast
  ring

/-- The norm of a primitive twisted sum at unit frequency is the square root of the conductor. -/
private theorem cChi_primitive_norm_le {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) : ‖cChi χ 1‖ ≤ Real.sqrt r := by
  rw [cChi_int_gauss436]
  simp only [Int.cast_one, AddChar.mulShift_one]
  have h := gaussSum_norm_sq_primitive (N := r) hχ
  have hnn : (0 : ℝ) ≤ ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod r) ℂ)‖ := norm_nonneg _
  rw [← Real.sqrt_sq hnn, h]

/-! ### The Möbius collapse of the residue fiber sum -/

/-- A residue class is a unit exactly when its representative is coprime to the modulus. -/
private theorem isUnit_of_gcd_eq_one {d : ℕ} [NeZero d] {c : ZMod d}
    (h : Nat.gcd c.val d = 1) : IsUnit c := by
  rw [show c = ((c.val : ℕ) : ZMod d) from (ZMod.natCast_zmod_val c).symm, ZMod.isUnit_iff_coprime]
  exact Nat.coprime_iff_gcd_eq_one.mpr h

/-- The gcd of a unit residue with the modulus is one. -/
private theorem gcd_eq_one_of_isUnit {d : ℕ} [NeZero d] {c : ZMod d}
    (h : IsUnit c) : Nat.gcd c.val d = 1 := by
  have h2 : IsUnit ((c.val : ℕ) : ZMod d) := by rwa [ZMod.natCast_zmod_val]
  rw [ZMod.isUnit_iff_coprime] at h2
  exact Nat.coprime_iff_gcd_eq_one.mp h2

/-- The unit indicator on `ZMod d` as a Möbius sum over the divisors of the modulus. -/
private theorem mobius_unit_indicator {d : ℕ} [NeZero d] (c : ZMod d) :
    (if IsUnit c then (1 : ℂ) else 0) =
      ∑ k ∈ d.divisors, if k ∣ c.val then (ArithmeticFunction.moebius k : ℂ) else 0 := by
  classical
  have hdne : d ≠ 0 := NeZero.ne d
  have hfil : d.divisors.filter (fun k => k ∣ c.val) = (Nat.gcd c.val d).divisors := by
    ext k
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hkd, _⟩, hkc⟩
      exact ⟨Nat.dvd_gcd hkc hkd, (Nat.gcd_pos_of_pos_right c.val (Nat.pos_of_ne_zero hdne)).ne'⟩
    · rintro ⟨hkg, _⟩
      exact ⟨⟨hkg.trans (Nat.gcd_dvd_right c.val d), hdne⟩,
        hkg.trans (Nat.gcd_dvd_left c.val d)⟩
  have hcoe : ∀ k : ℕ, (ArithmeticFunction.moebius k : ℂ)
      = (ArithmeticFunction.moebius : ArithmeticFunction ℂ) k := fun k => rfl
  have hmu : (∑ k ∈ (Nat.gcd c.val d).divisors, (ArithmeticFunction.moebius k : ℂ)) =
      if Nat.gcd c.val d = 1 then 1 else 0 := by
    simp only [hcoe]
    rw [← ArithmeticFunction.coe_mul_zeta_apply (R := ℂ)
      (f := (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) (x := Nat.gcd c.val d),
      ArithmeticFunction.coe_moebius_mul_coe_zeta]
    exact ArithmeticFunction.one_apply
  rw [← Finset.sum_filter, hfil, hmu]
  by_cases h : Nat.gcd c.val d = 1
  · rw [if_pos h, if_pos (isUnit_of_gcd_eq_one h)]
  · rw [if_neg h, if_neg (fun hc => h (gcd_eq_one_of_isUnit hc))]

/-- Fibers over a divisor sharing a prime with the conductor vanish. -/
private theorem fiber_noncoprime_zero {r d : ℕ} [NeZero r] [NeZero d]
    (χ : DirichletCharacter ℂ r) {k : ℕ} (hk : ¬ Nat.Coprime k r) :
    (∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
      χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c) = 0 := by
  classical
  refine Finset.sum_eq_zero (fun c hc => ?_)
  obtain ⟨_, hdiv⟩ := Finset.mem_filter.mp hc
  have hpos : 0 < Nat.gcd k r := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne r))
  have hne1 : Nat.gcd k r ≠ 1 := fun h => hk (Nat.coprime_iff_gcd_eq_one.mpr h)
  have hdvd : Nat.gcd k r ∣ Nat.gcd c.val r :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left k r).trans hdiv) (Nat.gcd_dvd_right k r)
  have hnu : ¬ IsUnit ((c.val : ℕ) : ZMod r) := by
    intro hu
    rw [ZMod.isUnit_iff_coprime] at hu
    rw [Nat.coprime_iff_gcd_eq_one.mp hu] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    omega
  rw [MulChar.map_nonunit _ hnu, zero_mul]

/-- Fibers over a divisor larger than the conductor, but coprime to it, vanish by a translation. -/
private theorem fiber_shift_zero {r d : ℕ} [NeZero r] [NeZero d]
    (hrd : r ∣ d) (χ : DirichletCharacter ℂ r) {k : ℕ} (hkd : k ∣ d)
    (hcop : Nat.Coprime k r) (hgt : r < d / k) :
    (∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
      χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c) = 0 := by
  classical
  set x : ZMod d := ((k * r : ℕ) : ZMod d) with hx
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hkd hdpos
  have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hkr : k * (d / k) = d := Nat.mul_div_cancel' hkd
  have hkrlt : k * r < d := by
    rw [← hkr]
    exact (Nat.mul_lt_mul_left hkpos).mpr hgt
  have hxval : x.val = k * r := by
    rw [hx, ZMod.val_natCast, Nat.mod_eq_of_lt hkrlt]
  have hxne : x ≠ 0 := by
    intro h
    have h0 : x.val = 0 := by rw [h]; exact ZMod.val_zero
    rw [hxval] at h0
    exact (Nat.mul_pos hkpos hrpos).ne' h0
  have hz : ZMod.stdAddChar x ≠ 1 := by
    intro h
    apply hxne
    refine ZMod.injective_stdAddChar ?_
    rw [h, AddChar.map_zero_eq_one]
  have hz1 : (1 : ℂ) - ZMod.stdAddChar x ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  -- the translated index set is again a set of multiples of `k`
  have hmem : ∀ c : ZMod d, k ∣ c.val → k ∣ (c + x).val := by
    intro c hc
    obtain ⟨s, hs⟩ := hc
    rw [ZMod.val_add, hxval, hs, ← Nat.mul_add, ← hkr, Nat.mul_mod_mul_left]
    exact ⟨_, rfl⟩
  -- the character factor is unchanged by the translation
  have hcast : ∀ c : ZMod d, (((c + x).val : ℕ) : ZMod r) = ((c.val : ℕ) : ZMod r) := by
    intro c
    have h1 : (((c + x).val : ℕ) : ZMod r) = ZMod.castHom hrd (ZMod r) (c + x) := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    have hx0 : ((k * r : ℕ) : ZMod r) = 0 := by
      rw [Nat.mul_comm]
      simp
    rw [h1, map_add, ZMod.castHom_apply, ZMod.castHom_apply, ZMod.cast_eq_val,
      ZMod.cast_eq_val, hxval, hx0, add_zero]
  -- the translation is a bijection of the index set
  have hinj : Set.InjOn (fun c : ZMod d => c + x)
      ↑(Finset.univ.filter (fun c : ZMod d => k ∣ c.val)) :=
    fun a _ b _ h => add_right_cancel h
  have hsub : Finset.image (fun c : ZMod d => c + x)
      (Finset.univ.filter (fun c : ZMod d => k ∣ c.val))
      ⊆ Finset.univ.filter (fun c : ZMod d => k ∣ c.val) := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem a (Finset.mem_filter.mp ha).2⟩
  have himg : Finset.image (fun c : ZMod d => c + x)
      (Finset.univ.filter (fun c : ZMod d => k ∣ c.val))
      = Finset.univ.filter (fun c : ZMod d => k ∣ c.val) :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq (Finset.card_image_of_injOn hinj).symm)
  -- consequently the sum is invariant under the translation
  have hA : (∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
        χ (((c + x).val : ℕ) : ZMod r) * ZMod.stdAddChar (c + x))
      = ∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
          χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image hinj]
  have hB : ∀ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
      χ (((c + x).val : ℕ) : ZMod r) * ZMod.stdAddChar (c + x)
        = (χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c) * ZMod.stdAddChar x := by
    intro c _
    rw [hcast c, AddChar.map_add_eq_mul]
    ring
  have hshift : (∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
        χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c)
      = (∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
          χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c) * ZMod.stdAddChar x := by
    calc (∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
          χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c)
        = ∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
            χ (((c + x).val : ℕ) : ZMod r) * ZMod.stdAddChar (c + x) := hA.symm
      _ = ∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
            (χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c) * ZMod.stdAddChar x :=
          Finset.sum_congr rfl hB
      _ = (∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
            χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c) * ZMod.stdAddChar x :=
          (Finset.sum_mul ..).symm
  have hzero : (∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
      χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c) *
        ((1 : ℂ) - ZMod.stdAddChar x) = 0 := by
    rw [mul_sub, mul_one, ← hshift]
    ring
  exact (mul_eq_zero.mp hzero).resolve_right hz1

/-- Scaling the modulus by `k` rescales the standard additive character. -/
private lemma stdAddChar_scale {r d k : ℕ} [NeZero r] [NeZero d] (hk : k * r = d) (j : ℕ) :
    ZMod.stdAddChar (((k * j : ℕ)) : ZMod d) = ZMod.stdAddChar ((j : ℕ) : ZMod r) := by
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne r)
  have hkne : (k : ℂ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.zero_mul] at hk
      exact absurd hk.symm (NeZero.ne d)
    · exact_mod_cast h.ne'
  have e1 : (((k * j : ℕ)) : ZMod d) = ((↑(k * j) : ℤ) : ZMod d) := by push_cast; ring
  have e2 : (((j : ℕ)) : ZMod r) = ((↑j : ℤ) : ZMod r) := by push_cast; ring
  rw [e1, e2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  have hdc : (d : ℂ) = (k : ℂ) * (r : ℂ) := by
    rw [← hk]
    push_cast
    ring
  rw [hdc]
  push_cast
  field_simp

/-- The surviving fiber is a primitive Gauss sum, up to one character value. -/
private theorem fiber_main_term {r d : ℕ} [NeZero r] [NeZero d]
    (χ : DirichletCharacter ℂ r) {k : ℕ} (hk : k * r = d) :
    (∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
      χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c)
      = χ ((k : ℕ) : ZMod r) * cChi χ 1 := by
  classical
  have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.zero_mul] at hk
      exact absurd hk.symm (NeZero.ne d)
    · exact h
  have hlt : ∀ s : ZMod r, k * s.val < d := by
    intro s
    rw [← hk]
    exact (Nat.mul_lt_mul_left hkpos).mpr (ZMod.val_lt s)
  have hval : ∀ s : ZMod r, (((k * s.val : ℕ) : ZMod d)).val = k * s.val := by
    intro s
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt s)]
  have hinj : Set.InjOn (fun s : ZMod r => ((k * s.val : ℕ) : ZMod d))
      ↑(Finset.univ : Finset (ZMod r)) := by
    intro a _ b _ h
    have h2 : k * a.val = k * b.val := by
      have hv := congrArg ZMod.val h
      simpa only [hval a, hval b] using hv
    exact ZMod.val_injective r (Nat.eq_of_mul_eq_mul_left hkpos h2)
  have himage : Finset.univ.filter (fun c : ZMod d => k ∣ c.val)
      = Finset.univ.image (fun s : ZMod r => ((k * s.val : ℕ) : ZMod d)) := by
    ext c
    constructor
    · intro hc
      rw [Finset.mem_filter] at hc
      obtain ⟨j, hj⟩ := hc.2
      have hjlt : j < r := by
        have hlt' : c.val < d := ZMod.val_lt c
        rw [hj, ← hk] at hlt'
        exact (Nat.mul_lt_mul_left hkpos).mp hlt'
      refine Finset.mem_image.mpr ⟨(j : ZMod r), Finset.mem_univ _, ?_⟩
      have hv : (j : ZMod r).val = j := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hjlt]
      show ((k * (j : ZMod r).val : ℕ) : ZMod d) = c
      rw [hv, ← hj, ZMod.natCast_zmod_val]
    · intro hc
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hval j]
      exact ⟨j.val, rfl⟩
  rw [himage, Finset.sum_image hinj, cChi_one_eq_std, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have hchi : χ ((k * s.val : ℕ) : ZMod r) = χ ((k : ℕ) : ZMod r) * χ s := by
    rw [show ((k * s.val : ℕ) : ZMod r)
        = ((k : ℕ) : ZMod r) * ((s.val : ℕ) : ZMod r) by push_cast; ring]
    rw [ZMod.natCast_zmod_val s, map_mul]
  have hstd : ZMod.stdAddChar (((k * s.val : ℕ) : ZMod d)) = ZMod.stdAddChar s := by
    rw [stdAddChar_scale hk s.val, ZMod.natCast_zmod_val]
  rw [hval s, hchi, hstd]
  ring

/-- The Möbius collapse at a modulus that is a multiple of the conductor. -/
private theorem cChi_lift_one_le {r d : ℕ} [NeZero r] [NeZero d]
    (hrd : r ∣ d) (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) :
    ‖cChi (DirichletCharacter.changeLevel hrd χ) 1‖ ≤ Real.sqrt r := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hmain : cChi (DirichletCharacter.changeLevel hrd χ) 1
      = ∑ c : ZMod d, (if IsUnit c then (1 : ℂ) else 0) *
          (χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c) := by
    rw [cChi_one_eq_std]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    by_cases hc : IsUnit c
    · obtain ⟨u, rfl⟩ := hc
      rw [if_pos (show IsUnit (↑u : ZMod d) from ⟨u, rfl⟩), one_mul]
      have hcl : (DirichletCharacter.changeLevel hrd χ) (↑u : ZMod d)
          = χ (((↑u : ZMod d)).cast) :=
        DirichletCharacter.changeLevel_eq_cast_of_dvd χ hrd u
      rw [hcl, ZMod.cast_eq_val]
    · rw [if_neg hc, zero_mul, MulChar.map_nonunit _ hc, zero_mul]
  have hexp : (∑ c : ZMod d, (if IsUnit c then (1 : ℂ) else 0) *
        (χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c))
      = ∑ k ∈ d.divisors, (ArithmeticFunction.moebius k : ℂ) *
          ∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
            (χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c) := by
    have h1 : ∀ c : ZMod d, (if IsUnit c then (1 : ℂ) else 0) *
        (χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c)
        = ∑ k ∈ d.divisors, if k ∣ c.val then
            (ArithmeticFunction.moebius k : ℂ) *
              (χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c) else 0 := by
      intro c
      rw [mobius_unit_indicator c, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : i ∣ c.val <;> simp [h]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_filter]
  have hcollapse : (∑ k ∈ d.divisors, (ArithmeticFunction.moebius k : ℂ) *
        ∑ c ∈ Finset.univ.filter (fun c : ZMod d => k ∣ c.val),
          (χ ((c.val : ℕ) : ZMod r) * ZMod.stdAddChar c))
      = (ArithmeticFunction.moebius (d / r) : ℂ) *
          (χ ((d / r : ℕ) : ZMod r) * cChi χ 1) := by
    rw [Finset.sum_eq_single (d / r) ?_ ?_]
    · rw [fiber_main_term χ (k := d / r)
        (by rw [Nat.mul_comm]; exact Nat.mul_div_cancel' hrd)]
    · intro k hk hne
      have hkd : k ∣ d := (Nat.mem_divisors.mp hk).1
      by_cases hcop : Nat.Coprime k r
      · have hdkdvd : r ∣ d / k := by
          refine Nat.Coprime.dvd_of_dvd_mul_left hcop.symm ?_
          rw [Nat.mul_div_cancel' hkd]
          exact hrd
        have hdkpos : 0 < d / k :=
          Nat.div_pos (Nat.le_of_dvd hdpos hkd) (Nat.pos_of_dvd_of_pos hkd hdpos)
        have hle : r ≤ d / k := Nat.le_of_dvd hdkpos hdkdvd
        have hne2 : d / k ≠ r := by
          intro h
          apply hne
          have hkr : k * r = d := by rw [← h, Nat.mul_div_cancel' hkd]
          rw [← hkr, Nat.mul_comm k r, Nat.mul_div_right k hrpos]
        rw [fiber_shift_zero hrd χ hkd hcop (lt_of_le_of_ne hle (Ne.symm hne2))]
        ring
      · rw [fiber_noncoprime_zero χ hcop]
        ring
    · intro hnot
      exact absurd (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hrd, NeZero.ne d⟩) hnot
  rw [hmain, hexp, hcollapse, norm_mul, norm_mul]
  have hmu : ‖(ArithmeticFunction.moebius (d / r) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d / r)
  have hchi : ‖χ ((d / r : ℕ) : ZMod r)‖ ≤ 1 := by
    by_cases hu : IsUnit (((d / r : ℕ) : ZMod r))
    · rw [← hu.unit_spec, DirichletCharacter.unit_norm_eq_one]
    · rw [MulChar.map_nonunit _ hu, norm_zero]
      exact zero_le_one
  have hcore : ‖cChi χ 1‖ ≤ Real.sqrt r := cChi_primitive_norm_le χ hχ
  have hn : (0 : ℝ) ≤ ‖cChi χ 1‖ := norm_nonneg _
  have hnn : (0 : ℝ) ≤ ‖χ ((d / r : ℕ) : ZMod r)‖ := norm_nonneg _
  have hstep : ‖χ ((d / r : ℕ) : ZMod r)‖ * ‖cChi χ 1‖ ≤ 1 * Real.sqrt r :=
    mul_le_mul hchi hcore hn (by norm_num)
  calc ‖(ArithmeticFunction.moebius (d / r) : ℂ)‖ *
        (‖χ ((d / r : ℕ) : ZMod r)‖ * ‖cChi χ 1‖)
      ≤ 1 * (1 * Real.sqrt r) :=
        mul_le_mul hmu hstep (mul_nonneg hnn hn) (by norm_num)
    _ = Real.sqrt r := by ring

/-- LEAF. Montgomery Vaughan 1975 pages 359 and 360, Case 2 and display 5.1.
Pintz Part I page 11 display 4.3 and page 20 display 7.13.
OPEN norm consequence of the residue fiber formula and the primitive Gauss norm.
Only the nonvanishing conductor alternative is required.
The totient quotient and one primitive conductor remain explicit. -/
theorem twisted_fiber_bound436 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hd : r ∣ q)
    (N : ℤ) (hgood : r ∣ q / Nat.gcd q N.natAbs) :
    ‖cChi (DirichletCharacter.changeLevel hd χ) N‖ ≤
      (Nat.totient q : ℝ) / (Nat.totient (q / Nat.gcd q N.natAbs) : ℝ) *
        Real.sqrt r := by
  classical
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hgpos : 0 < Nat.gcd q N.natAbs := Nat.gcd_pos_of_pos_left _ hqpos
  have hdpos : 0 < q / Nat.gcd q N.natAbs :=
    Nat.div_pos (Nat.le_of_dvd hqpos (Nat.gcd_dvd_left q N.natAbs)) hgpos
  haveI : NeZero (q / Nat.gcd q N.natAbs) := ⟨hdpos.ne'⟩
  have hfac : cChi (DirichletCharacter.changeLevel hd χ) N =
      ((Nat.totient q : ℂ) / (Nat.totient (q / Nat.gcd q N.natAbs) : ℂ)) *
        cChi (DirichletCharacter.changeLevel hgood χ) (N / (Nat.gcd q N.natAbs : ℤ)) := by
    have h1 : DirichletCharacter.changeLevel hd χ
        = DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q N.natAbs))
            (DirichletCharacter.changeLevel hgood χ) :=
      DirichletCharacter.changeLevel_trans χ hgood
        (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q N.natAbs))
    rw [h1]
    exact cChi_gcd_factor_p (DirichletCharacter.changeLevel hgood χ) N rfl
  rw [hfac, norm_mul, Complex.norm_div, Complex.norm_natCast, Complex.norm_natCast]
  rw [cChi_unit_norm_p _ _ (gcd_freq_unit_p N)]
  exact mul_le_mul_of_nonneg_left (cChi_lift_one_le hgood χ hχ) (by positivity)

/-- The positive frequency bound follows by the two residue fiber alternatives.
Source: Pintz page 20 display 7.13 and the totient quotient in display 4.3.
CONDITIONAL ON twisted_fiber_bound436. -/
theorem twisted_primitive_bound436 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hd : r ∣ q)
    (N : ℤ) (hN : 1 ≤ N) :
    ‖cChi (DirichletCharacter.changeLevel hd χ) N‖ ≤
      (N.natAbs : ℝ) * Real.sqrt r := by
  by_cases hgood : r ∣ q / Nat.gcd q N.natAbs
  · exact (twisted_fiber_bound436 χ hχ hd N hgood).trans
      (mul_le_mul_of_nonneg_right (totient_gcd_ratio247 q N.natAbs
        (Nat.pos_of_ne_zero (NeZero.ne q))
        (Int.natAbs_pos.mpr (by omega))) (Real.sqrt_nonneg _))
  · rw [twisted_fiber_vanish436 χ hχ hd N hgood, norm_zero]
    positivity

/-- Passing to the primitive character gives the same bound at any fixed source level.
Source: the primitive inducing character in Pintz page 11 Lemma 4.4.
CONDITIONAL ON twisted_fiber_bound436. -/
theorem twisted_lift_bound436 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hd : r ∣ q) (N : ℤ) (hN : 1 ≤ N) :
    ‖cChi (DirichletCharacter.changeLevel hd χ) N‖ ≤
      (N.natAbs : ℝ) * Real.sqrt r := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := twisted_primitive_bound436 χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
    (χ.conductor_dvd_level.trans hd) N hN
  rw [DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level hd,
    DirichletCharacter.changeLevel_primitiveCharacter] at h
  have hcr : (χ.conductor : ℝ) ≤ r := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne r)) χ.conductor_dvd_level
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcr) (by positivity))

/-- A conjugate Gauss sum is the inverse character twisted sum at frequency one.
Source: Pintz page 11 displays 4.1 and 4.2, with the local conjugation convention. -/
theorem tauConj_eq_cChi_inv436 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    tauConj χ = cChi χ⁻¹ 1 := by
  unfold tauConj cChi
  apply Finset.sum_congr rfl
  intro a ha
  rw [show (starRingEnd ℂ) (χ a) = star (χ a) from rfl, MulChar.star_apply']
  simp

/-- The lifted conjugate Gauss norm is bounded by the square root of its source level.
Source: Pintz page 11 Lemmas 4.1 to 4.4, frequency one specialization.
CONDITIONAL ON twisted_fiber_bound436. -/
theorem tau_lift_bound436 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hd : r ∣ q) :
    ‖tauConj (DirichletCharacter.changeLevel hd χ)‖ ≤ Real.sqrt r := by
  rw [tauConj_eq_cChi_inv436, ← map_inv]
  simpa using twisted_lift_bound436 χ⁻¹ hd 1 (by norm_num)

/-- Lifting the product at the least common multiple agrees with multiplying the two lifts.
Source: Pintz page 20 display 7.13, the primitive character inducing the product. -/
theorem lifted_product436 {r₁ r₂ q : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (h₁ : r₁ ∣ q) (h₂ : r₂ ∣ q) :
    DirichletCharacter.changeLevel (Nat.lcm_dvd h₁ h₂) (χ₁.mul χ₂) =
      DirichletCharacter.changeLevel h₁ χ₁ * DirichletCharacter.changeLevel h₂ χ₂ := by
  rw [DirichletCharacter.mul, map_mul, ← DirichletCharacter.changeLevel_trans,
    ← DirichletCharacter.changeLevel_trans]

/-- Exact aqZero247_totient_bound statement assembled from the smaller residue fiber leaves.
CONDITIONAL ON twisted_fiber_bound436.
Source: Pintz page 20 display 7.13. No original coefficient leaf is used. -/
theorem aqZero247_totient_supply436 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (N : ℤ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 0 < q →
      ‖aqZero247 χ₁ χ₂ N q‖ ≤ C * (1 / (Nat.totient q : ℝ) ^ 2) := by
  refine ⟨Real.sqrt r₁ * Real.sqrt r₂ * ((N.natAbs : ℝ) * Real.sqrt (Nat.lcm r₁ r₂)),
    by positivity, ?_⟩
  intro q hq
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero (Nat.lcm r₁ r₂) := ⟨Nat.lcm_ne_zero (NeZero.ne r₁) (NeZero.ne r₂)⟩
  by_cases hd : r₁ ∣ q ∧ r₂ ∣ q
  · have h₁ := tau_lift_bound436 χ₁ hd.1
    have h₂ := tau_lift_bound436 χ₂ hd.2
    have h₃ := twisted_lift_bound436 (χ₁.mul χ₂) (Nat.lcm_dvd hd.1 hd.2) N hN
    rw [lifted_product436 χ₁ χ₂ hd.1 hd.2] at h₃
    have hn := mul_le_mul h₁ h₂ (norm_nonneg _) (Real.sqrt_nonneg _)
    have hn' := mul_le_mul hn h₃ (norm_nonneg _) (by positivity)
    simp only [aqZero247, dif_neg (Nat.ne_of_gt hq), Aq, dif_pos hd, norm_div, norm_mul,
      norm_pow, Complex.norm_natCast]
    calc
      _ ≤ (Real.sqrt r₁ * Real.sqrt r₂ * ((N.natAbs : ℝ) * Real.sqrt (Nat.lcm r₁ r₂))) /
          (Nat.totient q : ℝ) ^ 2 := div_le_div_of_nonneg_right hn' (by positivity)
      _ = _ := by ring
  · simp [aqZero247, Nat.ne_of_gt hq, Aq, hd]
    positivity

end LeanLab.BhowmikGrimmelt2026

