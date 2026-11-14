module

public import LeanLab.Linnik.Decomp1532b
public import LeanLab.PNTPort.LargeSieve.Multiplicative
public import LeanLab.LanguascoPerelli1996.Primitive422

/-!
Gallagher 1975 P0094 p.127 Theorem 3.
The exponential error is retained. The exceptional conductor is shared by all frequencies.
The fixed positive exceptional strip is chosen from the proved Page and conductor bounds.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp466a

open Finset MeasureTheory
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries excSet)
open LeanLab.Linnik.U7204 (Sg)

/-- The fixed positive exceptional strip constant of Gallagher 1975 p.127.
Choose it small enough for the proved reality and conductor growth estimates. -/
noncomputable def exceptionalStrip : ℝ :=
  min (Classical.choose LeanLab.Linnik.Decomp1532b.exceptional_conductor_log_growth)
    (min (Classical.choose LeanLab.Linnik.Decomp1532b.page_real)
      (Classical.choose LeanLab.Linnik.Decomp1532b.page_subsingleton))

/-- Gallagher 1975 p.127. The fixed exceptional strip has positive width parameter. -/
theorem exceptionalStrip_pos : 0 < exceptionalStrip := by
  exact lt_min (Classical.choose_spec LeanLab.Linnik.Decomp1532b.exceptional_conductor_log_growth).1
    (lt_min (Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_real).1
      (Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_subsingleton).1)

/-- The weight |n| over phi of |n| in Gallagher 1975 p.127 Theorem 3. -/
noncomputable def totientWeight (n : ℤ) : ℝ :=
  (n.natAbs : ℝ) / n.natAbs.totient

/-- The quoted exceptional weight in Gallagher 1975 p.127 Theorem 3.
At r zero the weight is zero, encoding absence of the quoted term. -/
noncomputable def exceptionalWeight (r : ℕ) (n : ℤ) : ℝ :=
  (r : ℝ) * (Nat.gcd r n.natAbs).totient / (r.totient : ℝ) ^ 2

/-- The absolute frequency error in Gallagher 1975 p.127 Theorem 3. -/
noncomputable def frequencyError (N : ℕ) (θ : ℝ) (n : ℤ) : ℝ :=
  |(∫ α in majorArcs N ((N : ℝ) ^ θ), ‖Sg N α‖ ^ 2 *
    (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re) - Jn N n * (singSeries n).re|

/-- The complex absolute error printed in Gallagher 1975 p.127 Theorem 3. -/
noncomputable def complexFrequencyError (N : ℕ) (θ : ℝ) (n : ℤ) : ℝ :=
  ‖(∫ α in majorArcs N ((N : ℝ) ^ θ),
      ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)) -
    (Jn N n : ℂ) * singSeries n‖

/-- Gallagher 1975 p.127 Theorem 3, passage to the real correlation used on p.138.
Taking real parts never increases the absolute error. -/
theorem frequencyError_le_complexFrequencyError (N : ℕ) (θ : ℝ) (n : ℤ) :
    frequencyError N θ n ≤ complexFrequencyError N θ n := by
  let f : ℝ → ℂ := fun α => ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) *
    LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)
  have hs := LeanLab.Linnik.U7206.continuous_Sg N
  have hf : Continuous f := by
    dsimp [f]
    unfold LeanLab.PNTPort.LargeSieve.e
    fun_prop
  have hi : IntegrableOn f (majorArcs N ((N : ℝ) ^ θ)) :=
    hf.integrableOn_Icc.mono_set (fun _ h => h.1)
  have hre : (∫ α in majorArcs N ((N : ℝ) ^ θ), f α).re =
      ∫ α in majorArcs N ((N : ℝ) ^ θ), ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re := by
    have h := (integral_re hi).symm
    change (∫ α in majorArcs N ((N : ℝ) ^ θ), f α).re =
      ∫ α in majorArcs N ((N : ℝ) ^ θ), (f α).re at h
    simpa only [f, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using h
  have heq : ((∫ α in majorArcs N ((N : ℝ) ^ θ), f α) -
      (Jn N n : ℂ) * singSeries n).re =
      (∫ α in majorArcs N ((N : ℝ) ^ θ), ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re) - Jn N n * (singSeries n).re := by
    rw [Complex.sub_re, hre]
    simp
  unfold frequencyError complexFrequencyError
  rw [← heq]
  exact Complex.abs_re_le_norm _

end LeanLab.Linnik.Decomp466a

namespace LeanLab.Linnik.Decomp482a

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp1532b
open LeanLab.Linnik.U7204 (Sg)
open LeanLab.PNTPort.LargeSieve (e norm_e)

/-- Gallagher 1975 p.128. The primitive character prime sum A. -/
noncomputable def primeAmplitude {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (β : ℝ) : ℂ :=
  ∑ p ∈ Nat.primesLE N, χ p * LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * β)

/-- Gallagher 1975 p.131 display 14 uses the multiplicative large sieve.
The sharp finite inequality is already proved in the lab. -/
theorem multiplicative_sieve (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  exact LeanLab.Linnik.Decomp1532b.large_sieve a M N Q

/-- Gallagher 1975 p.128. The finite prime character sum is continuous in beta. -/
theorem continuous_primeAmplitude {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    Continuous (primeAmplitude χ N) := by
  exact LeanLab.Linnik.U1426ChainWire.continuous_SA (Nat.primesLE N) (fun p => χ p)

/-- Gallagher 1975 p.128 first character expansion at modulus one.
There is only the principal character and the expansion error is exactly zero. -/
theorem character_expansion_level_one (N a : ℕ) (ha : a ≤ 1) (β : ℝ) :
    ‖Sg N ((a : ℝ) / 1 + β) - (Nat.totient 1 : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ 1,
        χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ = 0 := by
  have hone (m : ℕ) : (1 : DirichletCharacter ℂ 1) m = 1 := by
    rw [show (m : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  have hprim (m : ℕ) : (1 : DirichletCharacter ℂ 1).primitiveCharacter m = 1 := by
    rw [DirichletCharacter.primitiveCharacter_one]
    apply MulChar.one_apply
    rw [DirichletCharacter.conductor_one]
    rw [show (m : ZMod 1) = 1 from Subsingleton.elim _ _]
    exact isUnit_one
  have hchars : (univ : Finset (DirichletCharacter ℂ 1)) = {1} := by
    ext χ
    simp only [mem_univ, mem_singleton, true_iff]
    exact DirichletCharacter.level_one χ
  have hgauss : gaussSum (1 : DirichletCharacter ℂ 1) ZMod.stdAddChar = 1 := by
    unfold gaussSum
    have hz : (univ : Finset (ZMod 1)) = {1} := by
      ext z
      simp only [mem_univ, mem_singleton, true_iff]
      exact Subsingleton.elim _ _
    rw [hz, sum_singleton, map_one]
    rw [show (1 : ZMod 1) = 0 from Subsingleton.elim _ _, AddChar.map_zero_eq_one]
    norm_num
  have hA : primeAmplitude (1 : DirichletCharacter ℂ 1).primitiveCharacter N β = Sg N β := by
    unfold primeAmplitude Sg LeanLab.Linnik.LiLiuLemma43.SA
    simp only [hprim, one_mul]
    congr 1
  have hshift : Sg N ((a : ℝ) / 1 + β) = Sg N β := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · simp
    · simpa only [Sg, Nat.cast_one, div_one, add_comm] using
        LeanLab.Linnik.LiLiuLemma43Int.SA_periodic
          (LeanLab.Linnik.U7204.primesLe N) (fun _ => 1) β
  rw [hshift]
  simp only [Nat.totient_one, Nat.cast_one, inv_one, one_mul, hchars, sum_singleton,
    hone, inv_one, hgauss, hA, sub_self, norm_zero]

/-- Gallagher 1975 p.128 first character expansion and definition of tau.
On every reduced residue, finite character orthogonality synthesizes the additive phase
from the inverse character Gauss sums. This step has no prime sum error. -/
theorem gauss_character_synthesis {q : ℕ} [NeZero q] (x : ZMod q) (hx : IsUnit x) :
    (∑ χ : DirichletCharacter ℂ q, χ x * gaussSum χ⁻¹ ZMod.stdAddChar) =
      (q.totient : ℂ) * ZMod.stdAddChar x := by
  have hi (χ : DirichletCharacter ℂ q) : χ⁻¹ x = χ x⁻¹ := by
    rw [← MulChar.star_apply', LeanLab.RieselVaughan1983.GaussImprim.star_apply_unit χ hx]
  have ho (y : ZMod q) : (∑ χ : DirichletCharacter ℂ q, χ x * χ⁻¹ y) =
      if x = y then (q.totient : ℂ) else 0 := by
    calc
      _ = ∑ χ : DirichletCharacter ℂ q, χ⁻¹ x * χ y :=
        Fintype.sum_bijective (fun χ : DirichletCharacter ℂ q => χ⁻¹)
          inv_involutive.bijective _ _ (fun χ => by simp)
      _ = ∑ χ : DirichletCharacter ℂ q, χ x⁻¹ * χ y := by simp only [hi]
      _ = _ := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hx y
  simp_rw [gaussSum, mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ y : ZMod q, (∑ χ : DirichletCharacter ℂ q, χ x * χ⁻¹ y) * ZMod.stdAddChar y := by
      simp_rw [sum_mul]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro χ _
      ring
    _ = ∑ y : ZMod q, (if x = y then (q.totient : ℂ) else 0) * ZMod.stdAddChar y := by
      simp only [ho]
    _ = _ := by simp [ite_mul]

/-- Gallagher 1975 p.128 first character expansion before primitive replacement.
Finite coefficients supported on reduced residues have an exact character expansion.
The coefficient phi q is retained on the left to avoid division in this identity. -/
theorem finite_character_expansion {q : ℕ} [NeZero q] (s : Finset ℕ) (w : ℕ → ℂ)
    (a : ZMod q) (ha : IsUnit a) (hs : ∀ n ∈ s, IsUnit (n : ZMod q)) :
    (q.totient : ℂ) * (∑ n ∈ s, w n * ZMod.stdAddChar (a * (n : ZMod q))) =
      ∑ χ : DirichletCharacter ℂ q,
        χ a * gaussSum χ⁻¹ ZMod.stdAddChar * (∑ n ∈ s, w n * χ n) := by
  calc
    _ = ∑ n ∈ s, w n * (∑ χ : DirichletCharacter ℂ q,
        χ (a * (n : ZMod q)) * gaussSum χ⁻¹ ZMod.stdAddChar) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      rw [gauss_character_synthesis _ (ha.mul (hs n hn))]
      ring
    _ = _ := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro χ _
      apply sum_congr rfl
      intro n _
      rw [map_mul]
      ring

open LeanLab.PNTPort.LargeSieve
  (ofReal_normSq_sum conj_stdAddChar sum_normSq_char sum_isUnit_eq_totient)

/-- Gallagher 1975 p.128 Gauss sums and p.129 display 6.
The additive shift second moment equals q times phi q for every character.
This extracts the finite calculation already used in PNTPort Multiplicative. -/
theorem gauss_shift_energy {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, ‖gaussSum χ (ZMod.stdAddChar.mulShift a)‖ ^ 2 =
      (q : ℝ) * q.totient := by
  let ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  change ∑ a : ZMod q, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 = (q : ℝ) * q.totient

  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.ofReal_pow]
  unfold gaussSum
  simp_rw [ofReal_normSq_sum, AddChar.mulShift_apply]
  have hc : ∀ z, (starRingEnd ℂ) (ψ z) = ψ (-z) := fun z => conj_stdAddChar z
  have hexp : ∀ a x y : ZMod q, χ x * ψ (a * x) * (starRingEnd ℂ) (χ y * ψ (a * y)) =
      χ x * (starRingEnd ℂ) (χ y) * ψ (a * (x - y)) := by
    intro a x y
    rw [(starRingEnd ℂ).map_mul, hc, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [hexp]
  rw [sum_comm]
  refine (sum_congr rfl (fun x _ => sum_comm)).trans ?_
  have hsum : ∀ x y : ZMod q, ∑ a : ZMod q, χ x * (starRingEnd ℂ) (χ y) * ψ (a * (x - y)) =
      if x = y then (q : ℂ) * (χ x * (starRingEnd ℂ) (χ x)) else 0 := by
    intro x y
    rw [← mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card]
    by_cases hxy : x = y
    · rw [if_pos (sub_eq_zero.2 hxy), if_pos hxy, hxy]; ring
    · rw [if_neg (fun h => hxy (sub_eq_zero.1 h)), if_neg hxy, Nat.cast_zero, mul_zero]
  simp_rw [hsum, sum_ite_eq, mem_univ, if_true]
  rw [← mul_sum]
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
  rw [← Complex.ofReal_sum, sum_normSq_char]
  norm_cast

/-- Gallagher 1975 p.129 display 6 gives the stronger conductor bound.
This general modulus bound applies to every character and controls primitive replacement. -/
theorem gauss_norm_le_sqrt_modulus {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt q := by
  let ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  have hl : (∑ a : ZMod q, if IsUnit a then ‖gaussSum χ ψ‖ ^ 2 else 0) ≤
      ∑ a : ZMod q, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 := by
    apply sum_le_sum
    intro a _
    by_cases ha : IsUnit a
    · rw [if_pos ha]
      have h := gaussSum_mulShift_eq χ ψ ha.unit
      rw [ha.unit_spec] at h
      rw [h, norm_mul]
      have hn : ‖χ⁻¹ a‖ = 1 := by
        simpa only [ha.unit_spec] using χ⁻¹.unit_norm_eq_one ha.unit
      rw [hn, one_mul]
    · rw [if_neg ha]
      positivity
  have ht (a : ZMod q) : (if IsUnit a then ‖gaussSum χ ψ‖ ^ 2 else 0) =
      (if IsUnit a then (1 : ℝ) else 0) * ‖gaussSum χ ψ‖ ^ 2 := by
    split_ifs <;> simp
  simp_rw [ht] at hl
  rw [← sum_mul, sum_isUnit_eq_totient, gauss_shift_energy χ] at hl
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hsq : ‖gaussSum χ ψ‖ ^ 2 ≤ (q : ℝ) :=
    (mul_le_mul_iff_right₀ hφ).mp (by simpa only [mul_comm] using hl)
  have hsqrt := Real.sqrt_le_sqrt hsq
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt

/-- Gallagher 1975 p.128 primitive replacement error.
Primes at most N that divide positive q number at most log q over log two. -/
theorem bad_prime_count (N q : ℕ) (hq : 0 < q) :
    (((Nat.primesLE N).filter (fun p => ¬ p.Coprime q)).card : ℝ) ≤
      Real.log q / Real.log 2 := by
  let B := (Nat.primesLE N).filter (fun p => ¬ p.Coprime q)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ h2).mpr
  calc
    (B.card : ℝ) * Real.log 2 = ∑ p ∈ B, Real.log 2 := by simp
    _ ≤ ∑ p ∈ B, ArithmeticFunction.vonMangoldt p := by
      apply sum_le_sum
      intro p hp
      have hprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
      rw [ArithmeticFunction.vonMangoldt_apply_prime hprime]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hprime.two_le)
    _ ≤ ∑ p ∈ q.divisors, ArithmeticFunction.vonMangoldt p := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
        exact Nat.mem_divisors.mpr ⟨hprime.dvd_iff_not_coprime.mpr (mem_filter.mp hp).2, hq.ne'⟩
      · intro p _ _
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log q := ArithmeticFunction.vonMangoldt_sum

/-- Gallagher 1975 p.128 primitive replacement error.
The inducing primitive prime sum differs only at primes dividing q.
The pointwise comparison is reused from Primitive422. -/
theorem amplitude_primitive_difference {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (N : ℕ) (β : ℝ) :
    ‖primeAmplitude χ N β - primeAmplitude χ.primitiveCharacter N β‖ ≤
      (((Nat.primesLE N).filter (fun p => ¬ p.Coprime q)).card : ℝ) := by
  unfold primeAmplitude
  rw [← sum_sub_distrib]
  calc
    _ = ‖∑ p ∈ Nat.primesLE N,
        (χ p - χ.primitiveCharacter p) * LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * β)‖ := by
      congr 1
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ p ∈ Nat.primesLE N, ‖(χ p - χ.primitiveCharacter p) *
        LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * β)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Nat.primesLE N, if p.Coprime q then (0 : ℝ) else 1 := by
      apply sum_le_sum
      intro p _
      rw [norm_mul, norm_e, mul_one]
      exact LeanLab.LanguascoPerelli1996.Primitive422.primitive_difference_norm χ p
    _ = ∑ p ∈ (Nat.primesLE N).filter (fun p => ¬ p.Coprime q), (1 : ℝ) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro p _
      by_cases hp : p.Coprime q <;> simp [hp]
    _ = _ := by simp

/-- Gallagher 1975 p.128 first character expansion before primitive replacement.
The prime sum restricted to units has an exact expansion with the original characters. -/
theorem imprimitive_expansion (N q : ℕ) [NeZero q] (a : ℕ) (ha : a.Coprime q) (β : ℝ) :
    (q.totient : ℂ) * (∑ p ∈ (Nat.primesLE N).filter (fun p => p.Coprime q),
      LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * ((a : ℝ) / q + β))) =
      ∑ χ : DirichletCharacter ℂ q,
        χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ N β := by
  let P := (Nat.primesLE N).filter (fun p => p.Coprime q)
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hp : ∀ p ∈ P, IsUnit (p : ZMod q) := fun p hp =>
    (ZMod.isUnit_iff_coprime p q).mpr (mem_filter.mp hp).2
  have he (p : ℕ) : LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * β) *
      ZMod.stdAddChar ((a : ZMod q) * (p : ZMod q)) =
        LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * ((a : ℝ) / q + β)) := by
    have h := LeanLab.PNTPort.LargeSieve.stdAddChar_mul_natCast (q := q) (p : ℤ) a
    simp only [Int.cast_natCast] at h
    rw [mul_comm (a : ZMod q) (p : ZMod q), h]
    rw [show (p : ℝ) * ((a : ℝ) / q + β) = p * β + p * ((a : ℝ) / q) by ring,
      LeanLab.PNTPort.LargeSieve.e_add]
  have hr (χ : DirichletCharacter ℂ q) :
      (∑ p ∈ P, LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * β) * χ p) =
        primeAmplitude χ N β := by
    unfold P primeAmplitude
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases hc : p.Coprime q
    · simp [hc, mul_comm]
    · have hz : χ (p : ZMod q) = 0 := MulChar.map_nonunit χ
        (by simpa only [ZMod.isUnit_iff_coprime] using hc)
      simp [hc, hz]
  have hh := finite_character_expansion P
    (fun p => LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * β)) (a : ZMod q) hu hp
  simpa only [he, hr] using hh

/-- LEAF. Gallagher 1975 p.128 first unnumbered display.
The prime sum on one rational arc is expanded in primitive character sums.
The error is uniform in N and beta. The logarithm of twice q also covers q one.
The finite synthesis and logarithmic bad prime count prove the uniform replacement error. -/
theorem character_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ N q : ℕ, ∀ [NeZero q], ∀ a : ℕ,
      Nat.Coprime a q → a ≤ q → ∀ β : ℝ,
        ‖Sg N ((a : ℝ) / q + β) - (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ ≤
          C * Real.sqrt q * Real.log (2 * q) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 / Real.log 2, by positivity, ?_⟩
  intro N q hq a ha haq β
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hφpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hqpos
  have hφne : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφpos.ne'
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  let B := (Nat.primesLE N).filter (fun p => ¬ p.Coprime q)
  let F : ℂ := ∑ p ∈ (Nat.primesLE N).filter (fun p => p.Coprime q),
    LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * ((a : ℝ) / q + β))
  let c : DirichletCharacter ℂ q → ℂ := fun χ => χ a * gaussSum χ⁻¹ ZMod.stdAddChar
  let H : ℂ := (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
    c χ * primeAmplitude χ.primitiveCharacter N β
  have hF : F = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      c χ * primeAmplitude χ N β := by
    have hh : (q.totient : ℂ) * F = ∑ χ : DirichletCharacter ℂ q,
        c χ * primeAmplitude χ N β := imprimitive_expansion N q a ha β
    rw [← hh, ← mul_assoc, inv_mul_cancel₀ hφne, one_mul]
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hsum : ‖(∑ χ : DirichletCharacter ℂ q, c χ * primeAmplitude χ N β) -
      (∑ χ : DirichletCharacter ℂ q, c χ * primeAmplitude χ.primitiveCharacter N β)‖ ≤
        (q.totient : ℝ) * (Real.sqrt q * (B.card : ℝ)) := by
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q,
          ‖c χ * primeAmplitude χ N β - c χ * primeAmplitude χ.primitiveCharacter N β‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, Real.sqrt q * (B.card : ℝ) := by
        apply sum_le_sum
        intro χ _
        have hn : ‖χ a‖ = 1 := by
          simpa only [hu.unit_spec] using χ.unit_norm_eq_one hu.unit
        rw [← mul_sub, norm_mul]
        change ‖χ a * gaussSum χ⁻¹ ZMod.stdAddChar‖ * _ ≤ _
        rw [norm_mul, hn, one_mul]
        exact mul_le_mul (gauss_norm_le_sqrt_modulus χ⁻¹)
          (amplitude_primitive_difference χ N β) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, hcard]
  have hFH : ‖F - H‖ ≤ Real.sqrt q * (B.card : ℝ) := by
    unfold H
    rw [hF, ← mul_sub, norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * (Real.sqrt q * (B.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hφpos.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hφpos.ne', one_mul]
  have hsplit : LeanLab.Linnik.U7204.Sg N ((a : ℝ) / q + β) =
      F + ∑ p ∈ B, LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * ((a : ℝ) / q + β)) := by
    unfold LeanLab.Linnik.U7204.Sg LeanLab.Linnik.LiLiuLemma43.SA
    simp only [one_mul]
    exact (sum_filter_add_sum_filter_not (Nat.primesLE N) (fun p => p.Coprime q)
      (fun p => LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * ((a : ℝ) / q + β)))).symm
  have hSF : ‖LeanLab.Linnik.U7204.Sg N ((a : ℝ) / q + β) - F‖ ≤ (B.card : ℝ) := by
    rw [hsplit, add_sub_cancel_left]
    calc
      _ ≤ ∑ p ∈ B, ‖LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * ((a : ℝ) / q + β))‖ :=
        norm_sum_le _ _
      _ = _ := by simp only [norm_e, sum_const, nsmul_eq_mul, mul_one]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hroot : 1 ≤ Real.sqrt q := by simpa using Real.sqrt_le_sqrt hq1
  have hlog : Real.log q ≤ Real.log (2 * q) :=
    Real.log_le_log (by exact_mod_cast hqpos) (by linarith)
  have hB : (B.card : ℝ) ≤ Real.log (2 * q) / Real.log 2 :=
    (bad_prime_count N q hqpos).trans (div_le_div_of_nonneg_right hlog h2.le)
  change ‖LeanLab.Linnik.U7204.Sg N ((a : ℝ) / q + β) - H‖ ≤ _
  calc
    _ = ‖(LeanLab.Linnik.U7204.Sg N ((a : ℝ) / q + β) - F) + (F - H)‖ := by
      congr 1
      ring
    _ ≤ ‖LeanLab.Linnik.U7204.Sg N ((a : ℝ) / q + β) - F‖ + ‖F - H‖ := norm_add_le _ _
    _ ≤ (B.card : ℝ) + Real.sqrt q * (B.card : ℝ) := add_le_add hSF hFH
    _ = (1 + Real.sqrt q) * (B.card : ℝ) := by ring
    _ ≤ (2 * Real.sqrt q) * (Real.log (2 * q) / Real.log 2) :=
      mul_le_mul (by linarith) hB (by positivity) (by positivity)
    _ = (2 / Real.log 2) * Real.sqrt q * Real.log (2 * q) := by ring


end LeanLab.Linnik.Decomp482a









