module

public import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a
public import LeanLab.PNTPort.DirichletZF.RealZero
public import LeanLab.PNTPort.DirichletZF.Siegel

/-!
The real and nonreal character cases of P0045 preprint page 6.
External results stay cited. Their consequences proved in P0045 stay open.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- P0045 page 6: Davenport Chapter 5, the real primitive conductor classification. -/
def RealPrimitiveStatement481 : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    χ.IsPrimitive → (∀ a, (χ a).im = 0) →
      r = oddRad131 r ∨ r = 4 * oddRad131 r ∨ r = 8 * oddRad131 r

/-- P0045 page 5: Pintz and Goldfeld and Schinzel, the real zero lower bound. -/
def RealZeroStatement481 : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    (∀ b, (χ b).im = 0) → ∀ δ : ℝ, 0 < δ →
      Lfun481 χ (1 - (δ : ℂ)) = 0 → a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ

/-- P0045 page 6: the denominator in the quoted Iwaniec region.
Corrected 20261121 U-1702 to |t| + 3 per Iwaniec 1974 page 97; the paper P0045 page 6 prints |t| + 2. -/
def iwaniecDenom481 (r : ℕ) (t : ℝ) : ℝ :=
  let ℓ := Real.log ((r : ℝ) * (|t| + 3))
  4 * 10 ^ 4 * (Real.log (2 * (oddRad131 r : ℝ)) +
    (ℓ * Real.log (2 * ℓ)) ^ (3 / 4 : ℝ))

/-- P0045 page 6: Iwaniec's zero free region for nonreal primitive characters. -/
def IwaniecStatement481 : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    χ.IsPrimitive → (∃ a, (χ a).im ≠ 0) → ∀ s : ℂ,
      1 - 1 / iwaniecDenom481 r s.im < s.re → Lfun481 χ s ≠ 0

/-- Standard: if `x ^ 2 = 0` then `(1 + x) ^ n = 1 + n * x`. -/
private theorem dav481_one_add_pow {R : Type*} [CommRing R] {x : R} (hx : x ^ 2 = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + (n : R) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast; linear_combination (n : R) * hx

/-- Davenport Chapter 5, standard: a character factors through `d ∣ r` as soon as it is
trivial on every unit `1 + k d` of `ZMod r`. -/
private theorem dav481_factors {r d : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hd : d ∣ r)
    (h : ∀ k : ℕ, IsUnit ((1 : ZMod r) + (k : ZMod r) * (d : ZMod r)) →
      χ (1 + (k : ZMod r) * (d : ZMod r)) = 1) : χ.FactorsThrough d := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have hcast : (ZMod.castHom hd (ZMod d)) ((u : ZMod r) - 1) = 0 := by
    have := congrArg Units.val hu
    rw [ZMod.unitsMap_val] at this
    rw [map_sub, map_one, ZMod.castHom_apply, this, Units.val_one, sub_self]
  set x : ZMod r := (u : ZMod r) - 1 with hxdef
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hcast
  obtain ⟨k, hk⟩ := hcast
  have hu' : (u : ZMod r) = 1 + (k : ZMod r) * (d : ZMod r) := by
    have : x = ((d * k : ℕ) : ZMod r) := by rw [← hk, ZMod.natCast_zmod_val]
    rw [Nat.cast_mul] at this
    linear_combination this
  apply Units.ext
  rw [MulChar.coe_toUnitHom, Units.val_one, hu']
  exact h k (hu' ▸ u.isUnit)

/-- A real value of a character on a unit has `y ^ φ r = 1`. -/
private theorem dav481_pow_totient {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) {y : ZMod r}
    (hy : IsUnit y) : χ y ^ Nat.totient r = 1 := by
  obtain ⟨v, rfl⟩ := hy
  rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]

private theorem dav481_real {r : ℕ} {χ : DirichletCharacter ℂ r}
    (hreal : ∀ a, (χ a).im = 0) (a : ZMod r) : χ a = ((χ a).re : ℂ) :=
  Complex.ext (by simp) (by simp [hreal a])

/-- Case of an odd prime square: a real character factors through `r / p`. -/
private theorem dav481_odd_sq {p t : ℕ} (hp : p.Prime) (hodd : Odd p) (ht : 1 ≤ t)
    (χ : DirichletCharacter ℂ (p * p * t)) (hreal : ∀ a, (χ a).im = 0) :
    χ.FactorsThrough (p * t) := by
  have : NeZero (p * p * t) := ⟨by positivity [hp.pos]⟩
  refine dav481_factors χ ⟨p, by ring⟩ fun k hk => ?_
  set x : ZMod (p * p * t) := (k : ZMod (p * p * t)) * ((p * t : ℕ) : ZMod (p * p * t))
  have h0 : ((p * p * t : ℕ) : ZMod (p * p * t)) = 0 := ZMod.natCast_self _
  have hx2 : x ^ 2 = 0 := by
    have : x ^ 2 = (k : ZMod (p * p * t)) ^ 2 * (t : ZMod (p * p * t)) *
        ((p * p * t : ℕ) : ZMod (p * p * t)) := by simp only [x]; push_cast; ring
    rw [this, h0, mul_zero]
  have hpx : (p : ZMod (p * p * t)) * x = 0 := by
    have : (p : ZMod (p * p * t)) * x = (k : ZMod (p * p * t)) *
        ((p * p * t : ℕ) : ZMod (p * p * t)) := by simp only [x]; push_cast; ring
    rw [this, h0, mul_zero]
  have hpow : (1 + x) ^ p = 1 := by rw [dav481_one_add_pow hx2, hpx, add_zero]
  have hy : (χ (1 + x)) ^ p = 1 := by rw [← map_pow, hpow, map_one]
  rw [dav481_real hreal] at hy ⊢
  have hre : (χ (1 + x)).re ^ p = 1 := by exact_mod_cast hy
  have habs : |(χ (1 + x)).re| = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (abs_nonneg _) hp.ne_zero, pow_abs, hre, abs_one]
  rcases abs_eq (zero_le_one) |>.mp habs with h | h
  · rw [h]; simp
  · rw [h, hodd.neg_one_pow] at hre; norm_num at hre

/-- Case `16 ∣ r`: a real character factors through `r / 2`. -/
private theorem dav481_sixteen {t : ℕ} (ht : 1 ≤ t)
    (χ : DirichletCharacter ℂ (16 * t)) (hreal : ∀ a, (χ a).im = 0) :
    χ.FactorsThrough (8 * t) := by
  have : NeZero (16 * t) := ⟨by omega⟩
  refine dav481_factors χ ⟨2, by ring⟩ fun k hk => ?_
  have h0 : ((16 * t : ℕ) : ZMod (16 * t)) = 0 := ZMod.natCast_self _
  set w : ZMod (16 * t) := 1 + (k : ZMod (16 * t)) * ((4 * t : ℕ) : ZMod (16 * t))
  have hsq : (1 : ZMod (16 * t)) + (k : ZMod (16 * t)) * ((8 * t : ℕ) : ZMod (16 * t)) = w ^ 2 := by
    have : w ^ 2 = 1 + (k : ZMod (16 * t)) * ((8 * t : ℕ) : ZMod (16 * t)) +
        (k : ZMod (16 * t)) ^ 2 * (t : ZMod (16 * t)) * ((16 * t : ℕ) : ZMod (16 * t)) := by
      simp only [w]; push_cast; ring
    rw [this, h0, mul_zero, add_zero]
  have htot := dav481_pow_totient χ hk
  rw [hsq, map_pow, dav481_real hreal w] at htot ⊢
  have hn : Nat.totient (16 * t) ≠ 0 := by
    rw [Ne, Nat.totient_eq_zero]; omega
  have hre : ((χ w).re ^ 2) ^ Nat.totient (16 * t) = 1 := by exact_mod_cast htot
  rw [pow_eq_one_iff_of_nonneg (sq_nonneg _) hn] at hre
  rw [← Complex.ofReal_pow, hre, Complex.ofReal_one]

/-- Case `r = 2 m` with `m` odd: every character factors through `m`. -/
private theorem dav481_two_odd {m : ℕ} (hm : Odd m) (χ : DirichletCharacter ℂ (2 * m)) :
    χ.FactorsThrough m := by
  have : NeZero (2 * m) := ⟨by obtain ⟨j, rfl⟩ := hm; omega⟩
  refine dav481_factors χ ⟨2, by ring⟩ fun k hk => ?_
  have h2 : (2 : ℕ) ∣ 2 * m := ⟨m, rfl⟩
  have hk2 := hk.map (ZMod.castHom h2 (ZMod 2))
  rw [map_add, map_one, map_mul, map_natCast, map_natCast] at hk2
  have hm1 : ((m : ℕ) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, Nat.odd_iff.mp hm, Nat.cast_one]
  rw [hm1, mul_one] at hk2
  have hkz : ((k : ℕ) : ZMod 2) = 0 := by
    revert hk2; generalize ((k : ℕ) : ZMod 2) = z; revert z; decide
  rw [ZMod.natCast_eq_zero_iff] at hkz
  obtain ⟨j, rfl⟩ := hkz
  have : ((2 * j : ℕ) : ZMod (2 * m)) * (m : ZMod (2 * m)) =
      (j : ZMod (2 * m)) * ((2 * m : ℕ) : ZMod (2 * m)) := by push_cast; ring
  rw [this, ZMod.natCast_self, mul_zero, add_zero, map_one]


private theorem dav481_two_odd' {r m : ℕ} (hm : Odd m) (hr : r = 2 * m)
    (χ : DirichletCharacter ℂ r) : χ.FactorsThrough m := by
  subst hr; exact dav481_two_odd hm χ

/-- LEAF. CITED. P0045 page 6, first proof paragraph following display 10.
Davenport Chapter 5 supplies the classification of real primitive conductors.
Proved here from Mathlib's factor through criterion, by the three standard cases. -/
theorem davenport_classification481 : RealPrimitiveStatement481 := by
  intro r hr χ hprim hreal
  have : NeZero r := ⟨by omega⟩
  have hr0 : r ≠ 0 := by omega
  have hle : ∀ d, χ.FactorsThrough d → r ≤ d := fun d hd => by
    have h := Nat.sInf_le (show d ∈ χ.conductorSet from hd)
    rwa [← DirichletCharacter.conductor, hprim] at h
  have hodd : ∀ p, p.Prime → 2 < p → ¬ p * p ∣ r := by
    rintro p hp h2 ⟨t, rfl⟩
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp at hr
      · exact h
    have := hle _ (dav481_odd_sq hp (hp.eq_two_or_odd'.resolve_left (by omega)) ht1 χ hreal)
    nlinarith [hp.two_le]
  have h16 : ¬ 16 ∣ r := by
    rintro ⟨t, rfl⟩
    have := hle _ (dav481_sixteen (by omega) χ hreal)
    omega
  have hoodd : ¬ 2 ∣ oddRad131 r := by
    intro h
    obtain ⟨p, hp, h2p⟩ := (Nat.prime_two.prime.dvd_finset_prod_iff _).mp h
    rw [Finset.mem_filter] at hp
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Nat.prime_of_mem_primeFactors hp.1)).mp h2p
    omega
  have hdecomp : r = 2 ^ r.factorization 2 * oddRad131 r := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hr0]
    rw [← Finset.prod_filter_mul_prod_filter_not r.primeFactors (fun p => 2 < p), mul_comm]
    congr 1
    · rw [Finset.prod_subset (s₁ := r.primeFactors.filter (fun p => ¬ 2 < p)) (s₂ := {2})]
      · simp
      · intro p hp
        rw [Finset.mem_filter] at hp
        have := (Nat.prime_of_mem_primeFactors hp.1).two_le
        simp only [Finset.mem_singleton]; omega
      · intro p hp hnot
        rw [Finset.mem_singleton] at hp
        subst hp
        have hn : (2 : ℕ) ∉ r.primeFactors := fun h => hnot (Finset.mem_filter.mpr ⟨h, by omega⟩)
        rw [← Nat.support_factorization] at hn
        rw [Finsupp.notMem_support_iff.mp hn, pow_zero]
    · unfold oddRad131
      apply Finset.prod_congr rfl
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp.1
      have h1 : 1 ≤ r.factorization p :=
        (hpp.dvd_iff_one_le_factorization hr0).mp (Nat.dvd_of_mem_primeFactors hp.1)
      have h2 : r.factorization p < 2 := by
        by_contra hc
        push Not at hc
        exact hodd p hpp hp.2 (by rw [← pow_two]; exact (hpp.pow_dvd_iff_le_factorization hr0).mpr hc)
      rw [show r.factorization p = 1 by omega, pow_one]
  have hf3 : r.factorization 2 ≤ 3 := by
    by_contra hc
    push Not at hc
    exact h16 (by
      have := (Nat.prime_two.pow_dvd_iff_le_factorization hr0 (k := 4)).mpr hc
      simpa using this)
  have hf1 : r.factorization 2 ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hdecomp
    have := hle _ (dav481_two_odd' (Nat.odd_iff.mpr (by omega)) hdecomp χ)
    omega
  interval_cases h : r.factorization 2
  · left; simpa using hdecomp
  · exact absurd rfl hf1
  · right; left; simpa using hdecomp
  · right; right; simpa using hdecomp

/-! Auxiliary lemmas for the modulus one leaf: the alternating ("eta") series
`∑ k, ((2k+1)^(-s) - (2k+2)^(-s))` converges for `0 < re s`, is termwise a positive
real for real `s ∈ (0,1)`, and equals `(1 - 2^(1-s)) * ζ s` there, so `ζ σ ≠ 0` for
real `σ ∈ (0,1)`. -/

namespace RZB481

open Complex Filter
open scoped Topology

/-- A nonnegative real base: the complex power is the coercion of the real power. -/
private theorem ofReal_rpow_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) :=
  Complex.ofReal_cpow hx y

/-- `((n : ℝ) : ℂ) ^ (-(σ : ℂ))` is the coercion of the real power. -/
private theorem nat_cpow_neg_eq {n : ℕ} {σ : ℝ} :
    (((n : ℂ)) ^ (-(σ : ℂ))) = ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ) := by
  have hcoe : (((-σ : ℝ)) : ℂ) = -(σ : ℂ) := by push_cast; ring
  rw [← hcoe, ← Complex.ofReal_natCast n,
    ← ofReal_rpow_cpow (x := (n : ℝ)) (by positivity) (-σ)]

/-- Mean value bound for `t ↦ t ^ (-s)` between two positive reals. -/
private theorem norm_cpow_neg_sub_le {s : ℂ} (hs : -1 ≤ s.re) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  have hbound : ∀ x ∈ Set.Ico a b, ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    have hnorm : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp
    have hmono : x ^ (-s.re - 1) ≤ a ^ (-s.re - 1) :=
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) (Set.mem_Ioi.mpr ha)
        (Set.mem_Ioi.mpr hx0) hx.1
    rw [norm_mul, hnorm, norm_neg]
    gcongr
  have hmain : ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => (t : ℂ) ^ (-s)) (f' := fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1))
      (C := ‖s‖ * a ^ (-s.re - 1))
      (fun x hx =>
        (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le ha hx.1)) (neg_ne_zero.mpr hs0)
          ).hasDerivWithinAt)
      hbound b (Set.right_mem_Icc.mpr hab)
  simpa only [norm_sub_rev] using hmain

/-- `t ↦ ((2k+1)^(-t) - (2k+2)^(-t))` is complex differentiable. -/
private theorem differentiableAt_pair_term (k : ℕ) (w : ℂ) :
    DifferentiableAt ℂ
      (fun t : ℂ => ((2 * k + 1 : ℕ) : ℂ) ^ (-t) - ((2 * k + 2 : ℕ) : ℂ) ^ (-t)) w := by
  have h1 : ((2 * k + 1 : ℕ) : ℂ) ≠ 0 := by
    have : (2 * k + 1 : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have h2 : ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := by
    have : (2 * k + 2 : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  exact ((differentiableAt_id.neg).const_cpow (Or.inl h1)).sub
    ((differentiableAt_id.neg).const_cpow (Or.inl h2))

/-- The alternating series is summable in the half plane `0 < re s`. -/
private theorem summable_pair_series {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ =>
      (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s))) := by
  have hmaj : Summable (fun k : ℕ => ‖s‖ * (((k : ℝ) + 1) ^ (-s.re - 1))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re - 1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-s.re - 1)) :=
      (summable_nat_add_iff 1).mpr hbase
    refine Summable.mul_left ‖s‖ ?_
    exact hshift.congr (fun n => by norm_num)
  refine Summable.of_norm_bounded hmaj (fun k => ?_)
  have ha : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hab : ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := by
    have h : 2 * k + 1 ≤ 2 * k + 2 := by omega
    exact_mod_cast h
  have hb := norm_cpow_neg_sub_le (s := s) (by linarith) ha hab
  have hdiff1 : ((2 * k + 2 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) = 1 := by
    have h : ((2 * k + 1 : ℕ) : ℝ) + 1 = ((2 * k + 2 : ℕ) : ℝ) := by
      have h' : (2 * k + 1 : ℕ) + 1 = 2 * k + 2 := by omega
      rw [← h']
      push_cast
      ring
    linarith
  rw [hdiff1, mul_one] at hb
  have hmono : ((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1) ≤ ((k : ℝ) + 1) ^ (-s.re - 1) := by
    refine Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) ?_ ?_ ?_
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · have h : (k : ℝ) + 1 ≤ ((2 * k + 1 : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
      exact h
  exact hb.trans (by gcongr)

/-- The alternating series is complex differentiable in the half plane `0 < re s`. -/
private theorem differentiableAt_pair_series (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∑' k : ℕ,
        (((2 * k + 1 : ℕ) : ℂ) ^ (-w) - ((2 * k + 2 : ℕ) : ℂ) ^ (-w))) s := by
  have hr0 : 0 < s.re / 2 := by positivity
  have hmaj : Summable (fun k : ℕ => (‖s‖ + s.re / 2) * (((k : ℝ) + 1) ^ (-s.re / 2 - 1))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re / 2 - 1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-s.re / 2 - 1)) :=
      (summable_nat_add_iff 1).mpr hbase
    refine Summable.mul_left (‖s‖ + s.re / 2) ?_
    exact hshift.congr (fun n => by norm_num)
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ
      (fun t : ℂ => ((2 * k + 1 : ℕ) : ℂ) ^ (-t) - ((2 * k + 2 : ℕ) : ℂ) ^ (-t))
      (Metric.ball s (s.re / 2)) :=
    fun k x _ => (differentiableAt_pair_term k x).differentiableWithinAt
  have hle : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball s (s.re / 2) →
      ‖((2 * k + 1 : ℕ) : ℂ) ^ (-w) - ((2 * k + 2 : ℕ) : ℂ) ^ (-w)‖
        ≤ (‖s‖ + s.re / 2) * (((k : ℝ) + 1) ^ (-s.re / 2 - 1)) := by
    intro k w hw
    have h2 : ‖w - s‖ < s.re / 2 := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hw
    have hwr : s.re / 2 < w.re := by
      have h1 : |(w - s).re| ≤ ‖w - s‖ := Complex.abs_re_le_norm _
      have h3 : w.re - s.re = (w - s).re := by simp
      have h4 : -(w.re - s.re) ≤ ‖w - s‖ := by
        rw [h3]
        exact (neg_le_abs _).trans h1
      linarith
    have hnorm : ‖w‖ ≤ ‖s‖ + s.re / 2 := by
      calc ‖w‖ = ‖s + (w - s)‖ := by rw [add_sub_cancel]
        _ ≤ ‖s‖ + ‖w - s‖ := norm_add_le _ _
        _ ≤ ‖s‖ + s.re / 2 := by linarith
    have ha : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
    have hab : ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := by
      have h : 2 * k + 1 ≤ 2 * k + 2 := by omega
      exact_mod_cast h
    have hb := norm_cpow_neg_sub_le (s := w) (by linarith) ha hab
    have hdiff1 : ((2 * k + 2 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) = 1 := by
      have h : ((2 * k + 1 : ℕ) : ℝ) + 1 = ((2 * k + 2 : ℕ) : ℝ) := by
        have h' : (2 * k + 1 : ℕ) + 1 = 2 * k + 2 := by omega
        rw [← h']
        push_cast
        ring
      linarith
    have hstep1 : ((2 * k + 1 : ℕ) : ℝ) ^ (-w.re - 1) ≤ ((k : ℝ) + 1) ^ (-w.re - 1) := by
      refine Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) ?_ ?_ ?_
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact Set.mem_Ioi.mpr (by positivity)
      · have h : (k : ℝ) + 1 ≤ ((2 * k + 1 : ℕ) : ℝ) := by
          push_cast
          linarith [Nat.cast_nonneg (α := ℝ) k]
        exact h
    have hstep2 : ((k : ℝ) + 1) ^ (-w.re - 1) ≤ ((k : ℝ) + 1) ^ (-s.re / 2 - 1) := by
      refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [hdiff1, mul_one] at hb
    refine hb.trans ?_
    exact mul_le_mul hnorm (hstep1.trans hstep2) (by positivity) (by positivity)
  have hall := differentiableOn_tsum_of_summable_norm
    (F := fun k : ℕ => fun t : ℂ =>
      ((2 * k + 1 : ℕ) : ℂ) ^ (-t) - ((2 * k + 2 : ℕ) : ℂ) ^ (-t))
    (U := Metric.ball s (s.re / 2)) hmaj hdiff Metric.isOpen_ball hle
  exact hall.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0))

/-- `∑' n, n ^ (-s) = ζ s` in the half plane of absolute convergence. -/
private theorem tsum_nat_cpow_neg_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (n : ℂ) ^ (-s)) = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr (fun n => ?_)
  rw [Complex.cpow_neg, one_div]

/-- The series `∑' n, n ^ (-s)` is summable for `1 < re s`. -/
private theorem summable_nat_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
  have hsne : -s ≠ 0 := by
    intro h
    have h0 : s = 0 := by linear_combination -h
    have hre : s.re = 0 := by rw [h0]; simp
    rw [hre] at hs
    linarith
  refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-s.re))
    (Real.summable_nat_rpow.mpr (by linarith)) (fun n => ?_)
  rcases eq_or_ne n 0 with h | h
  · subst h
    simp [Complex.zero_cpow, hsne, Real.zero_rpow (by linarith : -s.re ≠ 0)]
  · rw [← Complex.ofReal_natCast n,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero h)]
    simp

/-- The alternating ("eta") series equals `(1 - 2^(1-s)) * ζ s` for `1 < re s`. -/
private theorem pair_series_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)))
      = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hsne : -s ≠ 0 := by
    intro h
    have h0 : s = 0 := by linear_combination -h
    have hre : s.re = 0 := by rw [h0]; simp
    rw [hre] at hs
    linarith
  have hsum := summable_nat_cpow_neg (s := s) hs
  have hodd : Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) :=
    hsum.comp_injective (i := fun k : ℕ => 2 * k + 1) (by
      intro a b hab
      simp only at hab
      omega)
  have heven : Summable (fun k : ℕ => ((2 * k : ℕ) : ℂ) ^ (-s)) :=
    hsum.comp_injective (i := fun k : ℕ => 2 * k) (by
      intro a b hab
      simp only at hab
      omega)
  have hshift : Summable (fun k : ℕ => ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) :=
    hsum.comp_injective (i := fun k : ℕ => 2 * k + 2) (by
      intro a b hab
      simp only at hab
      omega)
  have hz : ((0 : ℕ) : ℂ) ^ (-s) = 0 := by
    simp [Complex.zero_cpow, hsne]
  have hstep : (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)))
      = (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s))
        - (∑' k : ℕ, ((2 * k : ℕ) : ℂ) ^ (-s)) := by
    rw [(hodd.hasSum.sub hshift.hasSum).tsum_eq]
    congr 1
    rw [heven.tsum_eq_zero_add, hz, zero_add]
    exact tsum_congr (fun k => by simp only [Nat.mul_succ])
  have hzetz : (∑' n : ℕ, (n : ℂ) ^ (-s)) = riemannZeta s :=
    tsum_nat_cpow_neg_eq_riemannZeta hs
  have hsplit : (∑' k : ℕ, ((2 * k : ℕ) : ℂ) ^ (-s))
      + (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) = riemannZeta s := by
    have hcomb := HasSum.even_add_odd (f := fun n : ℕ => (n : ℂ) ^ (-s))
      heven.hasSum hodd.hasSum
    rw [← hcomb.tsum_eq]
    exact hzetz
  have heven_eq : (∑' k : ℕ, ((2 * k : ℕ) : ℂ) ^ (-s))
      = (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [← hzetz, ← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    have h := Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ)) (b := (k : ℝ)) (by norm_num)
      (Nat.cast_nonneg k) (-s)
    rw [show ((2 * k : ℕ) : ℂ) = (((2 : ℝ)) : ℂ) * (((k : ℝ)) : ℂ) by push_cast; ring,
      show (2 : ℂ) = (((2 : ℝ)) : ℂ) by norm_num,
      show ((k : ℕ) : ℂ) = (((k : ℝ)) : ℂ) from (Complex.ofReal_natCast k).symm]
    exact h
  have hpow : (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    have h2 : (2 : ℂ) ^ (1 - s) = (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-s) := by
      rw [← Complex.cpow_add (y := (1 : ℂ)) (z := -s) (by norm_num : (2 : ℂ) ≠ 0)]
      congr 1
    rw [h2, Complex.cpow_one]
  have hA : (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s))
      = riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    have h := hsplit
    rw [heven_eq] at h
    rw [eq_sub_iff_add_eq, add_comm]
    exact h
  rw [hstep, hA, heven_eq]
  rw [hpow.symm]
  ring

/-- The alternating series equals `(1 - 2^(1-s)) * ζ s` on the half plane `0 < re s`. -/
private theorem pair_series_eq_of_pos_re {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)))
      = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hpc : IsPreconnected {w : ℂ | 0 < w.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hG : AnalyticOnNhd ℂ
      (fun w : ℂ => (w - 1) * (∑' k : ℕ,
          (((2 * k + 1 : ℕ) : ℂ) ^ (-w) - ((2 * k + 2 : ℕ) : ℂ) ^ (-w)))
        - (1 - (2 : ℂ) ^ (1 - w)) * riemannZeta₁ w) {w : ℂ | 0 < w.re} := by
    refine DifferentiableOn.analyticOnNhd ?_ hU
    exact DifferentiableOn.sub
      (DifferentiableOn.mul (fun w _ => (differentiableAt_id.sub
        (differentiableAt_const (c := (1 : ℂ)))).differentiableWithinAt)
        (fun w hw => (differentiableAt_pair_series w hw).differentiableWithinAt))
      (DifferentiableOn.mul (fun w _ =>
        ((differentiableAt_const (c := (1 : ℂ))).sub
          (((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id).const_cpow
            (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))).differentiableWithinAt)
        differentiable_riemannZeta₁.differentiableOn)
  have hz0 : (fun w : ℂ => (w - 1) * (∑' k : ℕ,
          (((2 * k + 1 : ℕ) : ℂ) ^ (-w) - ((2 * k + 2 : ℕ) : ℂ) ^ (-w)))
        - (1 - (2 : ℂ) ^ (1 - w)) * riemannZeta₁ w) =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have haux : Continuous fun _ : ℂ => (1 : ℝ) := continuous_const
    have hset : {w : ℂ | 1 < w.re} = {w : ℂ | (fun _ : ℂ => (1 : ℝ)) w < w.re} := rfl
    have hopen : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) := by
      rw [hset]
      exact (isOpen_lt haux continuous_re).mem_nhds (by simp)
    filter_upwards [hopen] with w hw
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hw
      simp at hw
    rw [pair_series_eq_of_one_lt_re hw, riemannZeta_eq_inv_sub_mul hw1]
    simp only [Pi.zero_apply]
    field_simp
    ring
  have hres := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hG hpc
    (z₀ := (2 : ℂ)) (by simp) hz0 hs
  beta_reduce at hres
  simp only [Pi.zero_apply] at hres
  rw [riemannZeta_eq_inv_sub_mul hs1]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hmul : (s - 1) * (∑' k : ℕ,
        (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)))
      = (s - 1) * ((1 - (2 : ℂ) ^ (1 - s)) * ((s - 1)⁻¹ * riemannZeta₁ s)) := by
    have h := hres
    field_simp at h ⊢
    linear_combination h
  exact mul_left_cancel₀ hs1' hmul

/-- For real `σ > 0` each term of the alternating series is a positive real. -/
private theorem pair_term_pos {σ : ℝ} (h0 : 0 < σ) (k : ℕ) :
    ((2 * k + 2 : ℕ) : ℝ) ^ (-σ) < ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) := by
  refine Real.rpow_lt_rpow_of_neg (by positivity : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ)) ?_
    (by linarith : -σ < 0)
  have h : 2 * k + 1 < 2 * k + 2 := by omega
  exact_mod_cast h

/-- The real alternating series is summable for `σ > 0`. -/
private theorem summable_pair_series_real {σ : ℝ} (h0 : 0 < σ) :
    Summable (fun k : ℕ =>
      (((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ))) := by
  have hmaj : Summable (fun k : ℕ => σ * (((k : ℝ) + 1) ^ (-σ - 1))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-σ - 1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-σ - 1)) :=
      (summable_nat_add_iff 1).mpr hbase
    refine Summable.mul_left σ ?_
    exact hshift.congr (fun n => by norm_num)
  refine Summable.of_norm_bounded hmaj (fun k => ?_)
  have hab : ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := by
    have h : 2 * k + 1 ≤ 2 * k + 2 := by omega
    exact_mod_cast h
  have hcomplex := norm_cpow_neg_sub_le (s := (σ : ℂ))
    (by rw [Complex.ofReal_re]; linarith)
    (a := ((2 * k + 1 : ℕ) : ℝ)) (b := ((2 * k + 2 : ℕ) : ℝ)) (by positivity) hab
  have hkey : ‖(((2 * k + 1 : ℕ) : ℂ) ^ (-(σ : ℂ)) - (((2 * k + 2 : ℕ) : ℂ) ^ (-(σ : ℂ))))‖
      = ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ) := by
    rw [nat_cpow_neg_eq (n := 2 * k + 1) (σ := σ),
      nat_cpow_neg_eq (n := 2 * k + 2) (σ := σ), ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr (pair_term_pos h0 k))]
  simp only [Complex.ofReal_natCast] at hcomplex
  rw [hkey, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0,
    Complex.ofReal_re] at hcomplex
  have hdiff1 : ((2 * k + 2 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) = 1 := by
    have h : ((2 * k + 1 : ℕ) : ℝ) + 1 = ((2 * k + 2 : ℕ) : ℝ) := by
      have h' : (2 * k + 1 : ℕ) + 1 = 2 * k + 2 := by omega
      rw [← h']
      push_cast
      ring
    linarith
  rw [hdiff1, mul_one] at hcomplex
  have hmono : ((2 * k + 1 : ℕ) : ℝ) ^ (-σ - 1) ≤ ((k : ℝ) + 1) ^ (-σ - 1) := by
    refine Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) ?_ ?_ ?_
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · have h : (k : ℝ) + 1 ≤ ((2 * k + 1 : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
      exact h
  rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (pair_term_pos h0 k))]
  exact hcomplex.trans (mul_le_mul_of_nonneg_left hmono h0.le)

/-- The alternating series is positive at real arguments in `(0,1)`. -/
private theorem pair_series_pos_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (_h1 : σ < 1) :
    0 < (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ))) :=
  Summable.tsum_pos (summable_pair_series_real h0)
    (fun k => le_of_lt (sub_pos.mpr (pair_term_pos h0 k))) 0
    (sub_pos.mpr (pair_term_pos h0 0))

/-- At a real argument, the complex alternating series is the coercion of the real one. -/
private theorem pair_series_ofReal {σ : ℝ} :
    (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℂ) ^ (-(σ : ℂ)) - ((2 * k + 2 : ℕ) : ℂ) ^ (-(σ : ℂ))))
      = ((∑' k : ℕ,
          (((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr (fun k => ?_)
  rw [nat_cpow_neg_eq (n := 2 * k + 1) (σ := σ), nat_cpow_neg_eq (n := 2 * k + 2) (σ := σ),
    ← Complex.ofReal_sub]

/-- **The Riemann zeta function has no real zero in `(0,1)`.** -/
private theorem riemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  have hcast := pair_series_ofReal (σ := σ)
  have hpos := pair_series_pos_of_mem_Ioo h0 h1
  have hne : (1 - (2 : ℂ) ^ (1 - (σ : ℂ))) ≠ 0 := by
    have hgt : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith)
    have hbase : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    have hval : (2 : ℂ) ^ (1 - (σ : ℂ)) = (((2 : ℝ) ^ (1 - σ) : ℝ) : ℂ) := by
      have h2 : (1 : ℂ) - ((σ : ℂ)) = (((1 : ℝ) - σ : ℝ) : ℂ) := by push_cast; ring
      rw [hbase, h2, ← ofReal_rpow_cpow (x := (2 : ℝ)) (by norm_num) (1 - σ)]
    intro h
    rw [hval, sub_eq_zero] at h
    have hh : ((2 : ℝ) ^ (1 - σ) : ℝ) = 1 := by exact_mod_cast h.symm
    linarith
  have hid := pair_series_eq_of_pos_re (s := (σ : ℂ)) (by simpa using h0) (by
    intro h
    have hre : (σ : ℂ).re = 1 := by rw [h]; simp
    rw [show (σ : ℂ).re = σ from rfl] at hre
    linarith)
  have hEne : (∑' k : ℕ,
      (((2 * k + 1 : ℕ) : ℂ) ^ (-(σ : ℂ)) - ((2 * k + 2 : ℕ) : ℂ) ^ (-(σ : ℂ)))) ≠ 0 := by
    rw [hcast]
    intro h
    exact (ne_of_gt hpos) (Complex.ofReal_eq_zero.mp h)
  intro hzero
  have hprod : (1 - (2 : ℂ) ^ (1 - (σ : ℂ))) * riemannZeta (σ : ℂ) ≠ 0 := by
    rw [← hid]
    exact hEne
  exact hprod (by rw [hzero, mul_zero])

end RZB481

namespace RZB481

open Complex Filter
open scoped Topology

/-- A character with real values has square one. -/
private theorem sq_of_real481 {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hreal : ∀ a, (χ a).im = 0) : χ ^ 2 = 1 := by
  have hstar : star χ = χ := by
    ext a
    change star (χ a) = χ a
    apply Complex.ext <;> simp [hreal a]
  rw [MulChar.star_eq_inv] at hstar
  calc χ ^ 2 = χ⁻¹ * χ := by rw [hstar, pow_two]
    _ = 1 := inv_mul_cancel _

/-- One Euler factor of the principal character does not vanish at a real point of `(0,1)`. -/
private theorem one_sub_cpow_neg_ne_zero481 {p : ℕ} (hp : p.Prime) {β : ℝ} (h0 : 0 < β) :
    (1 : ℂ) - (p : ℂ) ^ (-(β : ℂ)) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-(β : ℂ)) = 1 := by linear_combination -h
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hcast : (((p : ℝ)) : ℂ) = (p : ℂ) := by push_cast; ring
  have hn := Complex.norm_cpow_eq_rpow_re_of_pos (x := (p : ℝ)) hp0 (-(β : ℂ))
  rw [hcast, h1, norm_one] at hn
  simp only [Complex.neg_re, Complex.ofReal_re] at hn
  have hlt : (p : ℝ) ^ (-β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  linarith

/-- The principal character has no real zero in `(0,1)`. -/
private theorem principal_ne_zero481 {r : ℕ} [NeZero r] {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ r) (β : ℂ) ≠ 0 := by
  have hne : (β : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    linarith
  change DirichletCharacter.LFunctionTrivChar r (β : ℂ) ≠ 0
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hne]
  refine mul_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    exact one_sub_cpow_neg_ne_zero481 (Nat.prime_of_mem_primeFactors hp) hβ0
  · exact riemannZeta_ne_zero_of_mem_Ioo hβ0 hβ1

/-- **The real zero lower bound for every real character**, from Siegel's theorem at exponent
one half. This is strictly stronger than either of the two remaining leaves: no case
distinction on primitivity, and no restriction on the size of `δ`. -/
private theorem real_zero_bound_all481 :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      (∀ b, (χ b).im = 0) → ∀ δ : ℝ, 0 < δ →
        Lfun481 χ (1 - (δ : ℂ)) = 0 → a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ := by
  obtain ⟨c, hc, H⟩ := LeanLab.PNTPort.DirichletZF.siegel_zero (1 / 2) (by norm_num)
  let C := min (c * (8 : ℝ) ^ (-(1 / 2 : ℝ))) (1 / 2)
  have hC : 0 < C := lt_min (by positivity) (by norm_num)
  refine ⟨C, hC, fun r hr χ hreal δ hδ hz => ?_⟩
  have hr0 : 0 < r := by omega
  have hrne : r ≠ 0 := by omega
  haveI : NeZero r := ⟨hrne⟩
  have hrreal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpow : (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hrreal (by norm_num)
  by_cases hfar : (1 / 2 : ℝ) ≤ δ
  · have hC1 : C ≤ 1 / 2 := min_le_right _ _
    calc C * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ C * 1 := mul_le_mul_of_nonneg_left hrpow hC.le
      _ = C := mul_one C
      _ ≤ δ := by linarith
  have hβ0 : 0 < 1 - δ := by linarith
  have hβ1 : 1 - δ < 1 := by linarith
  have hL : Lfun481 χ (1 - (δ : ℂ)) = DirichletCharacter.LFunction χ (1 - (δ : ℂ)) := by
    unfold Lfun481
    rw [dif_neg hrne]
  have hz' : DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) = 0 := by
    rw [hL] at hz
    rwa [show (1 : ℂ) - (δ : ℂ) = ((1 - δ : ℝ) : ℂ) by push_cast; ring] at hz
  have hχ : χ ≠ 1 := by
    rintro rfl
    exact principal_ne_zero481 hβ0 hβ1 hz'
  have hχ2 : χ ^ 2 = 1 := sq_of_real481 χ hreal
  let M := 8 * r
  haveI : NeZero M := ⟨Nat.mul_ne_zero (by decide) hrne⟩
  have hd : r ∣ M := Dvd.intro_left 8 rfl
  have hM : 8 ≤ M := by dsimp only [M]; omega
  have hzlift : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hd χ)
      ((1 - δ : ℝ) : ℂ) = 0 := by
    rw [LeanLab.PNTPort.DirichletZF.L_lift hd hχ, hz', zero_mul]
  have hb := H M hM (DirichletCharacter.changeLevel hd χ)
    (LeanLab.PNTPort.DirichletZF.lift_ne_one hd hχ)
    (LeanLab.PNTPort.DirichletZF.lift_sq hd hχ2) (1 - δ) hβ1.le hzlift
  have hMr : (M : ℝ) = 8 * r := by simp [M]
  rw [hMr, Real.mul_rpow (by norm_num) (Nat.cast_nonneg r)] at hb
  have hcoeff : C ≤ c * (8 : ℝ) ^ (-(1 / 2 : ℝ)) := min_le_left _ _
  have hmul := mul_le_mul_of_nonneg_right hcoeff
    (Real.rpow_nonneg (Nat.cast_nonneg r) (-(1 / 2 : ℝ)))
  nlinarith

end RZB481
/-- P0045 page 5, the paragraph before Lemma 4.1: the real zero bound that the paper cites
from Pintz 1976 and Goldfeld and Schinzel 1975, proved here from Siegel's theorem. -/
theorem real_zero_bound481 : RealZeroStatement481 :=
  RZB481.real_zero_bound_all481


/-! Inlined proof of `real_exceptional_conductor481`. These private lemmas are copies of the
proved lemmas of `Decomp484a` and `SPLIT_real_exceptional_conductor481`, which import this file and
so cannot be called from here. No statement is changed and nothing is assumed. -/

section RealInline481b

open Complex LeanLab.PNTPort.DirichletZF

/-- P0045 page 5, display 8, change of logarithmic scale in the classical region.
The auxiliary factor in Bt is absorbed in one absolute positive constant. -/
private theorem log_Bt_comparison484_inl481b :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℕ, 1 ≤ r → ∀ t : ℝ,
      Real.log (Bt r t) ≤ K * Real.log ((r : ℝ) * (|t| + 2)) := by
  have hZ : 0 < Z := Z_pos
  let B : ℝ := 3 * Z
  have hB : 1 ≤ B := by dsimp [B]; linarith [one_le_Z]
  have hB0 : 0 < B := by linarith
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + Real.log B / Real.log 2, by positivity, ?_⟩
  intro r hr t
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  let A : ℝ := (r : ℝ) * (|t| + 2)
  have hA2 : 2 ≤ A := by
    dsimp [A]
    nlinarith [mul_nonneg hr0.le (abs_nonneg t)]
  have hA0 : 0 < A := by linarith
  have hlogA : Real.log 2 ≤ Real.log A := Real.log_le_log (by norm_num) hA2
  have hBt : Bt r t ≤ B * A := by
    dsimp [Bt, B, A]
    nlinarith [show 0 ≤ (r : ℝ) * |t| * Z by positivity]
  have hBt0 : 0 < Bt r t := by dsimp [Bt]; positivity
  have hscale : Real.log B ≤ Real.log B / Real.log 2 * Real.log A := by
    have hm := mul_le_mul_of_nonneg_left hlogA (div_nonneg hlB hl2.le)
    simpa [div_mul_cancel₀ _ hl2.ne'] using hm
  calc Real.log (Bt r t) ≤ Real.log (B * A) := Real.log_le_log hBt0 hBt
    _ = Real.log B + Real.log A := Real.log_mul hB0.ne' hA0.ne'
    _ ≤ (1 + Real.log B / Real.log 2) * Real.log A := by nlinarith

/-- P0045 page 5 before Lemma 4.1, nonreal zeros of nonprincipal characters.
The only exceptional zero in the proved classical region is real. -/
private theorem nonprincipal_nonreal_gap484_inl481b :
    ∃ b : ℝ, 0 < b ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      χ ≠ 1 → ∀ ρ : ℂ, Lfun481 χ ρ = 0 → ρ.im ≠ 0 →
        b / Real.log ((r : ℝ) * (|ρ.im| + 2)) ≤ 1 - ρ.re := by
  obtain ⟨c, c', hc, _, hreg⟩ := zero_free_region_real
  obtain ⟨K, hK, hcomp⟩ := log_Bt_comparison484_inl481b
  refine ⟨c / K, div_pos hc hK, ?_⟩
  intro r hr χ hχ ρ hρ him
  have hr0 : r ≠ 0 := by omega
  letI : NeZero r := ⟨hr0⟩
  have hzero : DirichletCharacter.LFunction χ ρ = 0 := by simpa [Lfun481, hr0] using hρ
  have hgap : c / Real.log (Bt r ρ.im) ≤ 1 - ρ.re := by
    rcases (hreg r χ hχ).1 ρ hzero with h | h
    · linarith
    · exact (him h.2.2.2).elim
  have hlogBt : 0 < Real.log (Bt r ρ.im) := by linarith [one_le_log_Bt (N := r) ρ.im]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hA : 1 < (r : ℝ) * (|ρ.im| + 2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r) (abs_nonneg ρ.im)]
  have hlogA : 0 < Real.log ((r : ℝ) * (|ρ.im| + 2)) := Real.log_pos hA
  apply le_trans _ hgap
  rw [div_div, div_le_div_iff₀ (mul_pos hK hlogA) hlogBt]
  exact mul_le_mul_of_nonneg_left (hcomp r hr ρ.im) hc.le

/-- P0045 page 5, the primitive principal case of the nonreal zero region.
The compact low height strip and the classical zeta region cover all heights. -/
private theorem zeta_gap484_inl481b :
    ∃ b : ℝ, 0 < b ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      b / Real.log (|ρ.im| + 2) ≤ 1 - ρ.re := by
  obtain ⟨σ, hσ, hbox⟩ := ZetaNoZerosInBox 3
  obtain ⟨A, hA, hlarge⟩ := ZetaZeroFree1
  have hσgap : 0 < 1 - σ := sub_pos.mpr hσ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min ((1 - σ) * Real.log 2) A, lt_min (by positivity) hA.1, ?_⟩
  intro ρ hρ
  have hre : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hρ
  have hrepr : (ρ.re : ℂ) + (ρ.im : ℂ) * I = ρ := by
    simpa [mul_comm] using ρ.re_add_im
  have hlog : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith [abs_nonneg ρ.im])
  by_cases ht : |ρ.im| ≤ 3
  · have hs : ρ.re < σ := by
      by_contra h
      exact hbox ρ.im ht ρ.re (le_of_not_gt h) (by rwa [hrepr])
    have hlogs : Real.log 2 ≤ Real.log (|ρ.im| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg ρ.im])
    rw [div_le_iff₀ hlog]
    calc min ((1 - σ) * Real.log 2) A ≤ (1 - σ) * Real.log 2 := min_le_left _ _
      _ ≤ (1 - σ) * Real.log (|ρ.im| + 2) := mul_le_mul_of_nonneg_left hlogs (by linarith)
      _ ≤ (1 - ρ.re) * Real.log (|ρ.im| + 2) := by nlinarith
  · have ht3 : 3 < |ρ.im| := lt_of_not_ge ht
    have hzero : riemannZeta ((ρ.re : ℂ) + (ρ.im : ℂ) * I) = 0 := by rwa [hrepr]
    have hleft : ρ.re < 1 - A / Real.log |ρ.im| := by
      by_contra hn
      have he := hlarge ρ.re ρ.im ht3 ⟨by simpa using le_of_not_gt hn, hre⟩
      exact he hzero
    have hlogt : 0 < Real.log |ρ.im| := Real.log_pos (by linarith)
    have hlogs : Real.log |ρ.im| ≤ Real.log (|ρ.im| + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    calc min ((1 - σ) * Real.log 2) A / Real.log (|ρ.im| + 2)
        ≤ A / Real.log (|ρ.im| + 2) := div_le_div_of_nonneg_right (min_le_right _ _) hlog.le
      _ ≤ A / Real.log |ρ.im| := div_le_div_of_nonneg_left hA.1.le hlogt hlogs
      _ ≤ 1 - ρ.re := by linarith

/-- P0045 pages 5 and 6, the classical gap for primitive characters at nonreal zeros.
Primitivity reduces the principal case to zeta at modulus one. -/
private theorem primitive_nonreal_gap484_inl481b :
    ∃ b : ℝ, 0 < b ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      χ.IsPrimitive → ∀ ρ : ℂ, Lfun481 χ ρ = 0 → ρ.im ≠ 0 →
        b / Real.log ((r : ℝ) * (|ρ.im| + 2)) ≤ 1 - ρ.re := by
  obtain ⟨b₁, hb₁, hnon⟩ := nonprincipal_nonreal_gap484_inl481b
  obtain ⟨b₂, hb₂, hzeta⟩ := zeta_gap484_inl481b
  refine ⟨min b₁ b₂, lt_min hb₁ hb₂, ?_⟩
  intro r hr χ hprim ρ hρ him
  have hr0 : r ≠ 0 := by omega
  letI : NeZero r := ⟨hr0⟩
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog : 0 ≤ Real.log ((r : ℝ) * (|ρ.im| + 2)) :=
    Real.log_nonneg (by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r) (abs_nonneg ρ.im)])
  by_cases hχ : χ = 1
  · have hrone : r = 1 := by
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hprim
      exact hprim.symm
    subst r
    have hζ : riemannZeta ρ = 0 := by
      simpa [Lfun481, hχ, DirichletCharacter.LFunction_modOne_eq] using hρ
    have he := hzeta ρ hζ
    simp only [Nat.cast_one, one_mul] at hlog ⊢
    exact (div_le_div_of_nonneg_right (min_le_right _ _) hlog).trans he
  · exact (div_le_div_of_nonneg_right (min_le_left _ _) hlog).trans (hnon r hr χ hχ ρ hρ him)

end RealInline481b

/-- The real zero case, from the real zero lower bound alone: for a modulus `r ≥ 1`, a
character with real values, and a genuine zero of the L function at the real point `1 - δ` with
`0 < δ ≤ H / log X`, the modulus is at least `c * Lg X ^ 2`, with one constant `c` for all `X`.
This is the lower bound `a * r ^ (-1/2) ≤ δ` rearranged, with `Lg X = log X / log 2`. -/
private theorem leaf_real_zero_conductor481_inl481b (hzero : RealZeroStatement481)
    (H : ℝ) (hH : 1 ≤ H) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : ℕ, ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      (∀ a, (χ a).im = 0) → ∀ δ : ℝ, 0 < δ → δ ≤ H / Real.log X →
        Lfun481 χ (1 - (δ : ℂ)) = 0 → c * Lg X ^ 2 ≤ (r : ℝ) := by
  obtain ⟨a, ha, hbound⟩ := hzero
  have hH0 : 0 < H := by linarith
  refine ⟨(a / H) ^ 2 * (Real.log 2) ^ 2, by positivity, ?_⟩
  intro X r hr χ hreal δ hδ hδle hpt
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hR : (0 : ℝ) < (r : ℝ) := by linarith
  rcases eq_or_lt_of_le (Real.log_natCast_nonneg X) with h0 | hpos
  · have hLg : Lg X = 0 := by rw [Lg, Real.logb, ← h0]; simp
    rw [hLg]
    simp
  · have hstep : a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ H / Real.log X :=
      le_trans (hbound r hr χ hreal δ hδ hpt) hδle
    rw [Real.rpow_neg hR.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv] at hstep
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 hR) hpos] at hstep
    have hsq : (a * Real.log X) ^ 2 ≤ H ^ 2 * (r : ℝ) := by
      have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ a * Real.log X) hstep 2
      simp only [mul_pow, Real.sq_sqrt hR.le] at hp
      simpa [mul_pow] using hp
    have hgoal : (a / H) ^ 2 * (Real.log 2) ^ 2 * Lg X ^ 2 = (a * Real.log X) ^ 2 / H ^ 2 := by
      rw [Lg, Real.logb]
      field_simp
    rw [hgoal, div_le_iff₀ (by positivity : (0:ℝ) < H ^ 2)]
    linarith

/-- The zero free region for real characters off the real axis, in the form the box uses:
some `b > 0` has `b / log (r (|t| + 2)) ≤ H / log X` for every zero of the box with real character
and nonzero imaginary part. Such a zero cannot sit inside `re ≥ 1 - b / log (r (|t| + 2))`, where
the L function does not vanish, and the box puts it at `re ≥ 1 - H / log X`, so the two radii are
ordered. -/
private theorem leaf_real_nonreal_threshold481_inl481b :
    ∃ b : ℝ, 0 < b ∧ ∀ X : ℕ, 1 < X → ∀ H T P : ℝ,
      ∀ z ∈ zeroBox481 X H T P, (∀ a, (z.2.1 a).im = 0) → z.2.2.im ≠ 0 →
        b / Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤ H / Real.log X := by
  obtain ⟨b, hb, hregion⟩ := primitive_nonreal_gap484_inl481b
  refine ⟨b, hb, ?_⟩
  intro X hX H T P z hz hreal him
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
  -- The region places the nonreal zero at least `b / log (r (|t| + 2))` to the left of one.
  have hzreg : b / Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤ 1 - z.2.2.re :=
    hregion z.1 h1 z.2.1 h3 z.2.2 h4 him
  -- The box puts the zero at real part at least `1 - H / log X`, so the gap to one is at most
  -- `H / log X`. The two radii are therefore ordered.
  have hgap : 1 - z.2.2.re ≤ H / Real.log X := by
    linarith [h5]
  exact le_trans hzreg hgap

/-- From that radius to the conductor bound: for a fixed `H ≥ 1` and `T ≥ 1`, if every
nonreal zero of the box satisfies the radius inequality at every height, then the modulus of such
a zero is at least `c * Lg X ^ 2` for all large `X`, uniformly in the major arc parameter `P`.
The box gives `|im| ≤ T`, so `r ≥ X ^ (b / H) / (T + 2)`, and an exponential in `X` beats
`Lg X ^ 2` for large `X`. -/
private theorem leaf_real_nonreal_conductor481_inl481b (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∀ b : ℝ, 0 < b →
      (∀ X : ℕ, 1 < X → ∀ P : ℝ, ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → z.2.2.im ≠ 0 →
          b / Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤ H / Real.log X) →
      ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
        AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
          (∀ a, (z.2.1 a).im = 0) → z.2.2.im ≠ 0 → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  intro b hb hhyp
  have hH0 : 0 < H := by linarith
  have hT0 : (0 : ℝ) < T + 2 := by linarith
  set q := b / H with hqval
  have hq : 0 < q := by rw [hqval]; exact div_pos hb hH0
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  have key : ∀ X : ℕ, 2 ≤ X → (Real.log X) ^ 2 ≤ 4 / q ^ 2 * (X : ℝ) ^ q := by
    intro X hX2
    have hX1' : (1 : ℝ) < (X : ℝ) := by
      have h : 1 < X := by omega
      exact_mod_cast h
    have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
    have hlogX : 0 ≤ Real.log X := le_of_lt (Real.log_pos hX1')
    have hypos : 0 < (X : ℝ) ^ (q / 2) := Real.rpow_pos_of_pos hXpos _
    have hlogXeq : Real.log X = (2 / q) * Real.log ((X : ℝ) ^ (q / 2)) := by
      rw [Real.log_rpow hXpos]
      field_simp
    have hb1 : Real.log ((X : ℝ) ^ (q / 2)) ≤ (X : ℝ) ^ (q / 2) := by
      have h := Real.log_le_sub_one_of_pos hypos
      linarith
    have hbound : Real.log X ≤ (2 / q) * (X : ℝ) ^ (q / 2) := by
      rw [hlogXeq]
      exact mul_le_mul_of_nonneg_left hb1 (by positivity)
    have hsq := pow_le_pow_left₀ hlogX hbound 2
    have hpow : ((X : ℝ) ^ (q / 2)) ^ 2 = (X : ℝ) ^ q := by
      rw [← Real.rpow_natCast ((X : ℝ) ^ (q / 2)) 2, ← Real.rpow_mul hXpos.le]
      congr 1
      ring
    calc (Real.log X) ^ 2 ≤ ((2 / q) * (X : ℝ) ^ (q / 2)) ^ 2 := hsq
      _ = 4 / q ^ 2 * (X : ℝ) ^ q := by
            rw [mul_pow, hpow]
            field_simp
            ring
  refine ⟨(Real.log 2) ^ 2 * q ^ 2 / (4 * (T + 2)), by positivity, 2, ?_⟩
  intro X hX P hP z hz hreal him
  have hz' : z ∈ zeroBox481 X H T P := hz
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz'
  have hX2 : 2 ≤ X := hX
  have hX1' : (1 : ℝ) < (X : ℝ) := by
    have h : 1 < X := by omega
    exact_mod_cast h
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX1'
  have hr1 : (1 : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast h1
  have hrpos : (0 : ℝ) < (z.1 : ℝ) := by linarith
  have hCpos : (0 : ℝ) < (z.1 : ℝ) * (|z.2.2.im| + 2) :=
    mul_pos hrpos (by positivity)
  have hC1 : (1 : ℝ) < (z.1 : ℝ) * (|z.2.2.im| + 2) := by
    have h2' : (2 : ℝ) ≤ |z.2.2.im| + 2 := by
      have hnn := abs_nonneg z.2.2.im
      linarith
    have hm := mul_le_mul hr1 h2' (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hrpos)
    linarith
  have hlogC : 0 < Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) := Real.log_pos hC1
  have hDpos : (0 : ℝ) < (z.1 : ℝ) * (T + 2) := mul_pos hrpos hT0
  have hle : (z.1 : ℝ) * (|z.2.2.im| + 2) ≤ (z.1 : ℝ) * (T + 2) :=
    mul_le_mul_of_nonneg_left (by have := h7; linarith) (le_of_lt hrpos)
  have hlogle : Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤
      Real.log ((z.1 : ℝ) * (T + 2)) := Real.log_le_log hCpos hle
  have hstep : b * Real.log X ≤ H * Real.log ((z.1 : ℝ) * (T + 2)) := by
    have hd := hhyp X (by omega) P z hz hreal him
    rw [div_le_div_iff₀ hlogC hlogX] at hd
    have hm := mul_le_mul_of_nonneg_left hlogle (le_of_lt hH0)
    linarith
  have hqle : q * Real.log X ≤ Real.log ((z.1 : ℝ) * (T + 2)) := by
    rw [hqval, div_mul_eq_mul_div, div_le_iff₀ hH0]
    linarith
  have hexp : (X : ℝ) ^ q ≤ (z.1 : ℝ) * (T + 2) := by
    have e1 : (X : ℝ) ^ q = Real.exp (Real.log X * q) := by
      rw [mul_comm, ← Real.log_rpow hXpos, Real.exp_log (Real.rpow_pos_of_pos hXpos q)]
    rw [e1]
    have h1 : Real.exp (Real.log X * q) ≤ Real.exp (Real.log ((z.1 : ℝ) * (T + 2))) :=
      Real.exp_le_exp.2 (by rw [mul_comm]; exact hqle)
    rwa [Real.exp_log hDpos] at h1
  have hk := key X hX2
  have hm : q ^ 2 / 4 * (Real.log X) ^ 2 ≤ q ^ 2 / 4 * (4 / q ^ 2 * (X : ℝ) ^ q) :=
    mul_le_mul_of_nonneg_left hk (by positivity)
  have hsimp : q ^ 2 / 4 * (4 / q ^ 2 * (X : ℝ) ^ q) = (X : ℝ) ^ q := by
    field_simp
  rw [hsimp] at hm
  have hm4 := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4)
  have heq : 4 * (q ^ 2 / 4 * (Real.log X) ^ 2) = q ^ 2 * (Real.log X) ^ 2 := by ring
  rw [heq] at hm4
  have hcval : (Real.log 2) ^ 2 * q ^ 2 / (4 * (T + 2)) * Lg X ^ 2 =
      q ^ 2 * (Real.log X) ^ 2 / (4 * (T + 2)) := by
    rw [Lg, Real.logb]
    field_simp
  rw [hcval, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (T + 2))]
  have hfin : q ^ 2 * (Real.log X) ^ 2 ≤ 4 * (X : ℝ) ^ q := by linarith
  nlinarith [hfin, hexp, hDpos]

/-- The real zero case inside the box: a zero of the box whose imaginary part vanishes is the
real point `1 - δ` with `δ = 1 - re`, `0 < δ` and `δ ≤ H / log X`, so the real zero case applies to
it with one constant and with a threshold that does not depend on the character, the height, the
major arc parameter or the modulus. -/
private theorem leaf_real_zero_box481_inl481b (hzero : RealZeroStatement481) (H T : ℝ) (hH : 1 ≤ H) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → z.2.2.im = 0 → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  obtain ⟨c, hc, h⟩ := leaf_real_zero_conductor481_inl481b hzero H hH
  refine ⟨c, hc, 0, ?_⟩
  intro X _ P _ z hz hreal him
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
  set d : ℝ := 1 - z.2.2.re with hdval
  have hdpos : 0 < d := by rw [hdval]; linarith
  have hdle : d ≤ H / Real.log X := by rw [hdval]; linarith
  have hzz : z.2.2 = ((z.2.2.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hcast : (1 : ℂ) - (d : ℂ) = ((z.2.2.re : ℝ) : ℂ) := by
    rw [hdval]; push_cast; ring
  have hzpt : Lfun481 z.2.1 (1 - (d : ℂ)) = 0 := by
    rw [hcast, ← hzz]
    exact h4
  exact h X z.1 h1 z.2.1 hreal d hdpos hdle hzpt

/-- The split target: the statement of `real_exceptional_conductor481`, proved from the four leaves
by the case distinction `im = 0` or `im ≠ 0`, with the smaller constant and the larger threshold. -/
private theorem real_exceptional_conductor481_split_inl481b (hzero : RealZeroStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  obtain ⟨c₁, hc₁, X₁, hreal⟩ := leaf_real_zero_box481_inl481b hzero H T hH
  obtain ⟨b, hb, hthr⟩ := leaf_real_nonreal_threshold481_inl481b
  obtain ⟨c₂, hc₂, X₂, hnonreal⟩ := leaf_real_nonreal_conductor481_inl481b H T hH hT b hb
    (fun X hX P z hz him hIm => hthr X hX H T P z hz him hIm)
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max X₁ X₂, ?_⟩
  intro X hX P hAdm z hz him
  have hle₁ : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hle₂ : X₂ ≤ X := le_trans (le_max_right _ _) hX
  have hsq : (0 : ℝ) ≤ Lg X ^ 2 := sq_nonneg (Lg X)
  by_cases hIm : z.2.2.im = 0
  · have h := hreal X hle₁ P hAdm z hz him hIm
    have hmin : min c₁ c₂ * Lg X ^ 2 ≤ c₁ * Lg X ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hsq
    linarith
  · have h := hnonreal X hle₂ P hAdm z hz him hIm
    have hmin : min c₁ c₂ * Lg X ^ 2 ≤ c₂ * Lg X ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hsq
    linarith

/-- PROVED. P0045 page 5 before Lemma 4.1 and page 6, first proof paragraph.
The real zero bound gives the quadratic conductor bound.
Nonreal zeros of real characters also require the classical zero free region.
The primitive principal character is excluded for large X at bounded height. -/
theorem real_exceptional_conductor481 (hzero : RealZeroStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → c * Lg X ^ 2 ≤ (z.1 : ℝ) :=
  real_exceptional_conductor481_split_inl481b hzero H T hH hT

/-! Inlined proof of `nonreal_exceptional_radical481`. These private lemmas are copies of the
proved lemmas of `SPLIT_nonreal_exceptional_radical481`, which imports this file and so cannot be
called from here. No statement is changed and nothing is assumed. -/

private theorem lpz481_oddRad_pos (r : ℕ) : 0 < oddRad131 r := by
  rw [oddRad131]
  refine Finset.prod_pos ?_
  intro p hp
  have h2 : 2 < p := (Finset.mem_filter.mp hp).2
  omega

/-- The Iwaniec denominator is positive at conductor at least one. -/
private theorem lpz481_denom_pos {r : ℕ} {t : ℝ} (hr : 1 ≤ r) :
    0 < iwaniecDenom481 r t := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by linarith
  have habs : (2 : ℝ) ≤ |t| + 3 := by linarith [abs_nonneg t]
  have hprod : (2 : ℝ) ≤ (r : ℝ) * (|t| + 3) := by
    have h := mul_le_mul hr1 habs (by norm_num : (0 : ℝ) ≤ 2) hr0
    simpa using h
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLpos : 0 < Real.log ((r : ℝ) * (|t| + 3)) := Real.log_pos (by linarith)
  have hLge : Real.log 2 ≤ Real.log ((r : ℝ) * (|t| + 3)) :=
    Real.log_le_log (by norm_num) hprod
  have h2L : 0 < Real.log (2 * Real.log ((r : ℝ) * (|t| + 3))) := by
    apply Real.log_pos
    linarith
  have hterm : 0 ≤ (Real.log ((r : ℝ) * (|t| + 3)) *
      Real.log (2 * Real.log ((r : ℝ) * (|t| + 3)))) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (le_of_lt (mul_pos hLpos h2L)) _
  have hodd1 : (1 : ℝ) ≤ (oddRad131 r : ℝ) := by
    have h1 : 1 ≤ oddRad131 r := by have := lpz481_oddRad_pos r; omega
    exact_mod_cast h1
  have hodd : 0 < Real.log (2 * (oddRad131 r : ℝ)) := by
    apply Real.log_pos
    linarith
  have hrw : iwaniecDenom481 r t
      = 4 * 10 ^ 4 * (Real.log (2 * (oddRad131 r : ℝ)) +
          (Real.log ((r : ℝ) * (|t| + 3)) *
            Real.log (2 * Real.log ((r : ℝ) * (|t| + 3)))) ^ ((3 : ℝ) / 4)) := rfl
  rw [hrw]
  exact mul_pos (by norm_num) (by linarith)

/-- The zero free region in the shape the box uses. -/
private theorem leaf_iwaniec_bound481_inl481b (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∀ X : ℕ, 2 ≤ X → ∀ P : ℝ, ∀ z ∈ zeroBox481 X H T P,
      (∃ a, (z.2.1 a).im ≠ 0) →
        Real.log X / H ≤ iwaniecDenom481 z.1 z.2.2.im := by
  intro X hX P z hz him
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
  have hHpos : 0 < H := by linarith
  have hX2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hD : 0 < iwaniecDenom481 z.1 z.2.2.im := lpz481_denom_pos h1
  have hnot : ¬ (1 - 1 / iwaniecDenom481 z.1 z.2.2.im < z.2.2.re) := by
    intro hlt
    exact (hiw z.1 h1 z.2.1 h3 him z.2.2 hlt) h4
  have hle : z.2.2.re ≤ 1 - 1 / iwaniecDenom481 z.1 z.2.2.im := not_lt.mp hnot
  have hstep : (1 : ℝ) / iwaniecDenom481 z.1 z.2.2.im ≤ H / Real.log X := by linarith
  have hmul : Real.log X ≤ H * iwaniecDenom481 z.1 z.2.2.im := by
    have h := (div_le_div_iff₀ hD hlogX).mp hstep
    linarith
  rw [div_le_iff₀ hHpos]
  linarith [mul_comm H (iwaniecDenom481 z.1 z.2.2.im)]

/-- `log y ≤ 6 * y ^ (1/6)` for `y ≥ 0`. -/
private theorem lpz481_log_le_six_rpow {y : ℝ} (hy : 0 ≤ y) :
    Real.log y ≤ 6 * y ^ ((1 : ℝ) / 6) := by
  have h := Real.log_le_rpow_div hy (show (0 : ℝ) < 1 / 6 by norm_num)
  have h6 : y ^ ((1 : ℝ) / 6) / ((1 : ℝ) / 6) = 6 * y ^ ((1 : ℝ) / 6) := by
    rw [div_eq_mul_inv, show ((1 : ℝ) / 6)⁻¹ = 6 by norm_num]
    ring
  linarith [h, h6]

/-- The size of the second summand of the denominator only. -/
private theorem leaf_denom_upper_bound481_inl481b (T : ℝ) (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → ∀ P H : ℝ, AdmissibleP131 X P →
      ∀ z ∈ zeroBox481 X H T P,
        (Real.log ((z.1 : ℝ) * (|z.2.2.im| + 3)) *
          Real.log (2 * Real.log ((z.1 : ℝ) * (|z.2.2.im| + 3)))) ^ (3 / 4 : ℝ)
          ≤ C * (Real.log X) ^ (7 / 8 : ℝ) := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hT2 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  set A : ℝ := (41 : ℝ) / 100 + Real.log (T + 3) / Real.log 2 with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    have h : 0 ≤ Real.log (T + 3) / Real.log 2 := div_nonneg hT2 hlog2pos.le
    linarith
  have hDpos : 0 < 6 * (2 : ℝ) ^ ((1 : ℝ) / 6) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) ((1 : ℝ) / 6))
  refine ⟨(6 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ ((3 : ℝ) / 4) * A ^ ((7 : ℝ) / 8), ?_, ?_⟩
  · exact mul_pos (Real.rpow_pos_of_pos hDpos ((3 : ℝ) / 4))
      (Real.rpow_pos_of_pos hApos ((7 : ℝ) / 8))
  · intro X hX P H hP z hz
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
    obtain ⟨hPa, hPb⟩ := hP
    have hX2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hlogXge : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
    have hR1 : (1 : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast h1
    have hR0 : (0 : ℝ) < (z.1 : ℝ) := by linarith
    have ha2 : (2 : ℝ) ≤ |z.2.2.im| + 3 := by linarith [abs_nonneg z.2.2.im]
    have hapos : (0 : ℝ) < |z.2.2.im| + 3 := by linarith
    have hra : 0 < (z.1 : ℝ) * (|z.2.2.im| + 3) := mul_pos hR0 hapos
    have hge2 : (2 : ℝ) ≤ (z.1 : ℝ) * (|z.2.2.im| + 3) := by
      have h := mul_le_mul hR1 ha2 (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ (z.1 : ℝ))
      simpa using h
    have hPle : (z.1 : ℝ) ≤ (X : ℝ) ^ ((41 : ℝ) / 100) := h2.trans hPb
    have him : |z.2.2.im| + 3 ≤ T + 3 := by linarith
    have hmul : (z.1 : ℝ) * (|z.2.2.im| + 3) ≤ (X : ℝ) ^ ((41 : ℝ) / 100) * (T + 3) :=
      mul_le_mul hPle him (by linarith) (Real.rpow_pos_of_pos hXpos _).le
    have hlogmul : Real.log ((z.1 : ℝ) * (|z.2.2.im| + 3))
        ≤ Real.log ((X : ℝ) ^ ((41 : ℝ) / 100) * (T + 3)) := Real.log_le_log hra hmul
    have hlogsplit : Real.log ((X : ℝ) ^ ((41 : ℝ) / 100) * (T + 3))
        = (41 : ℝ) / 100 * Real.log X + Real.log (T + 3) := by
      rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hXpos _)) (by linarith : (T + 3 : ℝ) ≠ 0),
        Real.log_rpow hXpos]
    have hl : Real.log ((z.1 : ℝ) * (|z.2.2.im| + 3)) ≤ A * Real.log X := by
      have hge1 : (1 : ℝ) ≤ Real.log X / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]
        linarith
      have hTstep : Real.log (T + 3) ≤ Real.log (T + 3) / Real.log 2 * Real.log X := by
        have h := mul_le_mul_of_nonneg_left hge1 hT2
        rw [mul_one] at h
        calc Real.log (T + 3) ≤ Real.log (T + 3) * (Real.log X / Real.log 2) := h
          _ = Real.log (T + 3) / Real.log 2 * Real.log X := by ring
      have hAexp : A * Real.log X
          = (41 : ℝ) / 100 * Real.log X + Real.log (T + 3) / Real.log 2 * Real.log X := by
        rw [hAdef]
        ring
      linarith
    have hlpos : 0 < Real.log ((z.1 : ℝ) * (|z.2.2.im| + 3)) := Real.log_pos (by linarith)
    set l : ℝ := Real.log ((z.1 : ℝ) * (|z.2.2.im| + 3)) with hldef
    have hl0 : 0 < l := hlpos
    have hlog2le : Real.log 2 ≤ l := Real.log_le_log (by norm_num) hge2
    have h2l1 : 1 < 2 * l := by linarith [Real.log_two_gt_d9]
    have hlog2l : 0 < Real.log (2 * l) := Real.log_pos h2l1
    have hbasepos : 0 ≤ l * Real.log (2 * l) := (mul_pos hl0 hlog2l).le
    have hbase : l * Real.log (2 * l) ≤ 6 * (2 : ℝ) ^ ((1 : ℝ) / 6) * l ^ ((7 : ℝ) / 6) := by
      have hlog : Real.log (2 * l) ≤ 6 * (2 * l) ^ ((1 : ℝ) / 6) :=
        lpz481_log_le_six_rpow (by linarith)
      have hmr : (2 * l) ^ ((1 : ℝ) / 6) = (2 : ℝ) ^ ((1 : ℝ) / 6) * l ^ ((1 : ℝ) / 6) :=
        Real.mul_rpow (by norm_num) hl0.le
      have hl76 : l ^ ((7 : ℝ) / 6) = l * l ^ ((1 : ℝ) / 6) := by
        have h : (7 : ℝ) / 6 = 1 + 1 / 6 := by norm_num
        rw [h, Real.rpow_add hl0, Real.rpow_one]
      have hstep : l * Real.log (2 * l) ≤ l * (6 * ((2 : ℝ) ^ ((1 : ℝ) / 6) * l ^ ((1 : ℝ) / 6))) := by
        have h := mul_le_mul_of_nonneg_left hlog hl0.le
        rwa [hmr] at h
      rw [hl76]
      nlinarith [hstep, Real.rpow_pos_of_pos hl0 ((1 : ℝ) / 6)]
    have hpow : (l * Real.log (2 * l)) ^ ((3 : ℝ) / 4)
        ≤ (6 * (2 : ℝ) ^ ((1 : ℝ) / 6) * l ^ ((7 : ℝ) / 6)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hbasepos hbase (by norm_num)
    have hpow2 : (6 * (2 : ℝ) ^ ((1 : ℝ) / 6) * l ^ ((7 : ℝ) / 6)) ^ ((3 : ℝ) / 4)
        = (6 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ ((3 : ℝ) / 4) * l ^ ((7 : ℝ) / 8) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hl0.le _),
        ← Real.rpow_mul hl0.le]
      norm_num
    have hlA : l ^ ((7 : ℝ) / 8) ≤ A ^ ((7 : ℝ) / 8) * (Real.log X) ^ ((7 : ℝ) / 8) := by
      have h1' : l ^ ((7 : ℝ) / 8) ≤ (A * Real.log X) ^ ((7 : ℝ) / 8) :=
        Real.rpow_le_rpow hl0.le hl (by norm_num)
      rwa [Real.mul_rpow hApos.le hlogX.le] at h1'
    calc (l * Real.log (2 * l)) ^ ((3 : ℝ) / 4)
        ≤ (6 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ ((3 : ℝ) / 4) * l ^ ((7 : ℝ) / 8) := hpow.trans_eq hpow2
      _ ≤ (6 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ ((3 : ℝ) / 4) *
            (A ^ ((7 : ℝ) / 8) * (Real.log X) ^ ((7 : ℝ) / 8)) :=
          mul_le_mul_of_nonneg_left hlA (le_of_lt (Real.rpow_pos_of_pos hDpos _))
      _ = ((6 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ ((3 : ℝ) / 4) * A ^ ((7 : ℝ) / 8)) *
            (Real.log X) ^ ((7 : ℝ) / 8) := by ring

private theorem lpz481_rpow_eighth_pow {x : ℝ} (hx : 0 < x) :
    (x ^ ((1 : ℝ) / 8)) ^ 8 = x := by
  have h1 : (x ^ ((1 : ℝ) / 8)) ^ 8 = (x ^ ((1 : ℝ) / 8)) ^ (8 : ℝ) :=
    (Real.rpow_natCast _ 8).symm
  rw [h1, ← Real.rpow_mul hx.le]
  norm_num

/-- Helper: `C * H < L ^ (1/8)` once `(C H) ^ 8 + 1 ≤ L`. -/
private theorem lpz481_ch_lt_eighth {C H L : ℝ} (hCH : 0 < C * H)
    (hL : (C * H) ^ 8 + 1 ≤ L) : C * H < L ^ ((1 : ℝ) / 8) := by
  have hLpos : 0 < L := by
    have h0 : (0 : ℝ) ≤ (C * H) ^ 8 := by positivity
    linarith
  have hDpos : 0 < L ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hLpos _
  have hD8 : (L ^ ((1 : ℝ) / 8)) ^ 8 = L := lpz481_rpow_eighth_pow hLpos
  have hlt : (C * H) ^ 8 < (L ^ ((1 : ℝ) / 8)) ^ 8 := by
    rw [hD8]
    nlinarith [pow_pos hCH 8]
  by_contra hcon
  push_neg at hcon
  have := pow_le_pow_left₀ (le_of_lt hDpos) hcon 8
  linarith

/-- The growth comparison. -/
private theorem leaf_log_growth_excludes481_inl481b (C : ℝ) (hC : 0 < C) (H : ℝ) (hH : 1 ≤ H) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      C * (Real.log X) ^ (7 / 8 : ℝ) < Real.log X / H := by
  have hHpos : 0 < H := by linarith
  have hCH : 0 < C * H := mul_pos hC hHpos
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp ((C * H) ^ 8 + 1))
  have hN1 : (0 : ℝ) < (N : ℝ) := by
    have hpos : (0 : ℝ) < Real.exp ((C * H) ^ 8 + 1) := Real.exp_pos _
    linarith
  refine ⟨N, fun X hX => ?_⟩
  have hL : (C * H) ^ 8 + 1 ≤ Real.log X := by
    have h1 : (C * H) ^ 8 + 1 ≤ Real.log (N : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos ((C * H) ^ 8 + 1)) (le_of_lt hN)
      rwa [Real.log_exp] at h
    have h2 : Real.log (N : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hN1 (by exact_mod_cast hX)
    linarith
  have hLpos : 0 < Real.log X := by
    have h0 : (0 : ℝ) ≤ (C * H) ^ 8 := by positivity
    linarith
  set D : ℝ := (Real.log X) ^ ((1 : ℝ) / 8) with hDdef
  have hDpos : 0 < D := Real.rpow_pos_of_pos hLpos _
  have hCHltD : C * H < D := lpz481_ch_lt_eighth hCH hL
  have hsplit : (Real.log X) ^ (7 / 8 : ℝ) = Real.log X / D := by
    have h78 : (7 : ℝ) / 8 = 1 - 1 / 8 := by norm_num
    rw [h78, Real.rpow_sub hLpos, Real.rpow_one, hDdef]
  have hkey : C * (Real.log X / D) = (C * Real.log X) / D := by ring
  rw [hsplit, hkey, div_lt_div_iff₀ hDpos hHpos]
  nlinarith [mul_pos hLpos (sub_pos.mpr hCHltD)]

/-- `Lg X = log X / log 2`. -/
private theorem lpz481_Lg_eq (X : ℕ) : Lg X = Real.log X / Real.log 2 := by
  rw [Lg, Real.log_div_log]

/-- Growth helper for the assembly. -/
private theorem lpz481_growth_helper (D H : ℝ) (hD : 0 < D) (hH : 1 ≤ H) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      Real.log 2 + 2 * Real.log (Lg X) + D * (Real.log X) ^ (7 / 8 : ℝ)
        ≤ Real.log X / (4 * 10 ^ 4 * H) := by
  set K : ℝ := 4 * 10 ^ 4 * H with hKdef
  have hKpos : 0 < K := by positivity
  set E : ℝ := (15 + D) * K with hEdef
  have hEpos : 0 < E := by
    rw [hEdef]
    have : 0 < 15 + D := by linarith
    exact mul_pos this hKpos
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (E ^ 8 + 1))
  refine ⟨max N 3, fun X hX => ?_⟩
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have := Real.exp_pos (E ^ 8 + 1)
    linarith
  have hLbig : E ^ 8 + 1 ≤ Real.log X := by
    have h1 : E ^ 8 + 1 ≤ Real.log (N : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos (E ^ 8 + 1)) (le_of_lt hN)
      rwa [Real.log_exp] at h
    have h2 : Real.log (N : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hNpos (by exact_mod_cast hXN)
    linarith
  have hLpos : 0 < Real.log X := by
    have h1 : (1 : ℝ) < (X : ℝ) := by
      have h : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
      linarith
    exact Real.log_pos h1
  have hLone : 1 ≤ Real.log X := by
    have h3X : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
    have h13 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    have h3 : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) h3X
    linarith
  set L : ℝ := Real.log X with hLdef
  have hLpos' : 0 < L := hLpos
  have hLone' : 1 ≤ L := hLone
  have h78one : (1 : ℝ) ≤ L ^ ((7 : ℝ) / 8) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hLone' (by norm_num : (0 : ℝ) ≤ 7 / 8)
    rwa [Real.one_rpow] at h
  have hlog2 : Real.log 2 ≤ L ^ ((7 : ℝ) / 8) := by
    have h := Real.log_two_lt_d9
    linarith
  have hLgbound : Real.log (Lg X) ≤ 1 + 6 * L ^ ((1 : ℝ) / 6) := by
    have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hLgpos : 0 < Lg X := by
      rw [lpz481_Lg_eq]
      exact div_pos hLpos' hlog2pos
    have hLgle : Lg X ≤ 2 * L := by
      rw [lpz481_Lg_eq, div_le_iff₀ hlog2pos]
      nlinarith [Real.log_two_gt_d9, hLpos']
    have hstep1 : Real.log (Lg X) ≤ Real.log (2 * L) := Real.log_le_log hLgpos hLgle
    have hstep2 : Real.log (2 * L) = Real.log 2 + Real.log L := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hLpos')]
    have hstep3 : Real.log L ≤ 6 * L ^ ((1 : ℝ) / 6) := lpz481_log_le_six_rpow hLpos'.le
    have hstep4 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have h16le : L ^ ((1 : ℝ) / 6) ≤ L ^ ((7 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hLone' (by norm_num)
  have hMain : (15 + D) * L ^ ((7 : ℝ) / 8) ≤ L / K := by
    have hKE : E ≤ L ^ ((1 : ℝ) / 8) := le_of_lt (lpz481_ch_lt_eighth hEpos hLbig)
    have hsplit : L ^ ((7 : ℝ) / 8) * L ^ ((1 : ℝ) / 8) = L := by
      rw [← Real.rpow_add hLpos', show (7 : ℝ) / 8 + 1 / 8 = 1 by norm_num, Real.rpow_one]
    rw [le_div_iff₀ hKpos]
    calc (15 + D) * L ^ ((7 : ℝ) / 8) * K
        = L ^ ((7 : ℝ) / 8) * E := by rw [hEdef]; ring
      _ ≤ L ^ ((7 : ℝ) / 8) * L ^ ((1 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_left hKE (le_of_lt (Real.rpow_pos_of_pos hLpos' _))
      _ = L := hsplit
  have hExp : Real.log 2 + 2 * Real.log (Lg X) + D * L ^ ((7 : ℝ) / 8)
      ≤ (15 + D) * L ^ ((7 : ℝ) / 8) := by
    have h16pos : 0 < L ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hLpos' _
    nlinarith [hlog2, hLgbound, h16le, h78one]
  have hfin := hExp.trans hMain
  rwa [hKdef] at hfin

/-- The split target: the statement of `nonreal_exceptional_radical481`, proved from the three
leaves through `oddRad131`, with constant one. -/
private theorem nonreal_exceptional_radical481_split_inl481b (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∃ a, (z.2.1 a).im ≠ 0) → c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by
  obtain ⟨C, hC, hden⟩ := leaf_denom_upper_bound481_inl481b T hT
  obtain ⟨X₁, hX₁⟩ := lpz481_growth_helper C H hC hH
  refine ⟨1, one_pos, max X₁ 3, ?_⟩
  intro X hX P hP z hz him
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have h2 : 2 ≤ X := by omega
  have hHpos : 0 < H := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast h2)
  have hlow : Real.log X / H ≤ iwaniecDenom481 z.1 z.2.2.im :=
    leaf_iwaniec_bound481_inl481b hiw H T hH hT X h2 P z hz him
  have hup : (Real.log ((z.1 : ℝ) * (|z.2.2.im| + 3)) *
      Real.log (2 * Real.log ((z.1 : ℝ) * (|z.2.2.im| + 3)))) ^ (3 / 4 : ℝ)
      ≤ C * (Real.log X) ^ (7 / 8 : ℝ) := hden X h2 P H hP z hz
  have hgro : Real.log 2 + 2 * Real.log (Lg X) + C * (Real.log X) ^ (7 / 8 : ℝ)
      ≤ Real.log X / (4 * 10 ^ 4 * H) := hX₁ X hX1
  have hdenom : iwaniecDenom481 z.1 z.2.2.im
      = 4 * 10 ^ 4 * (Real.log (2 * (oddRad131 z.1 : ℝ)) +
          (Real.log ((z.1 : ℝ) * (|z.2.2.im| + 3)) *
            Real.log (2 * Real.log ((z.1 : ℝ) * (|z.2.2.im| + 3)))) ^ (3 / 4 : ℝ)) := rfl
  rw [hdenom] at hlow
  have hstep : Real.log X / H ≤
      4 * 10 ^ 4 * (Real.log (2 * (oddRad131 z.1 : ℝ)) + C * (Real.log X) ^ (7 / 8 : ℝ)) := by
    nlinarith [hlow, hup]
  have hmain : Real.log X / (4 * 10 ^ 4 * H) - C * (Real.log X) ^ (7 / 8 : ℝ)
      ≤ Real.log (2 * (oddRad131 z.1 : ℝ)) := by
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * 10 ^ 4 * H)]
    rw [div_le_iff₀ hHpos] at hstep
    nlinarith [hstep]
  have hLgpos : 0 < Lg X := by
    rw [lpz481_Lg_eq]
    exact div_pos hlogX (by linarith [Real.log_two_gt_d9])
  have hexpand : Real.log (2 * Lg X ^ 2) = Real.log 2 + 2 * Real.log (Lg X) := by
    rw [Real.log_mul (x := (2 : ℝ)) (y := Lg X ^ 2) (by norm_num)
      (pow_ne_zero 2 (ne_of_gt hLgpos)), Real.log_pow]
    push_cast
    ring
  have hkey : Real.log (2 * Lg X ^ 2) ≤ Real.log (2 * (oddRad131 z.1 : ℝ)) := by
    rw [hexpand]
    linarith [hgro, hmain]
  have hoddpos : (0 : ℝ) < (oddRad131 z.1 : ℝ) := by
    have h := lpz481_oddRad_pos z.1
    exact_mod_cast h
  have := (Real.log_le_log_iff (by positivity : (0 : ℝ) < 2 * Lg X ^ 2) (by positivity)).mp hkey
  have hfin : Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by linarith
  simpa using hfin

/-- PROVED. P0045 page 6, last proof paragraph and display 10.
The Iwaniec region gives odd radical growth for nonreal exceptional characters.
This states the weaker quadratic conclusion actually used by the corollary. -/
theorem nonreal_exceptional_radical481 (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∃ a, (z.2.1 a).im ≠ 0) → c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) :=
  nonreal_exceptional_radical481_split_inl481b hiw H T hH hT

/-- LEAF. P0045 page 6, first proof paragraph following display 10.
Transfer the conductor lower bound through the three classified possibilities. -/
theorem real_radical_transfer481 {r : ℕ} {Y : ℝ}
    (hclass : r = oddRad131 r ∨ r = 4 * oddRad131 r ∨ r = 8 * oddRad131 r)
    (hY : Y ≤ (r : ℝ)) : Y / 8 ≤ (oddRad131 r : ℝ) := by
  have hr : r ≤ 8 * oddRad131 r := by rcases hclass with h | h | h <;> omega
  have hc : (r : ℝ) ≤ 8 * (oddRad131 r : ℝ) := by exact_mod_cast hr
  linarith

end
end LeanLab.LPZ2007
