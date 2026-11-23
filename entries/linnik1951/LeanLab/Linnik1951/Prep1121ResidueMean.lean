module

public import LeanLab.Linnik1951.Decomp520a
public import LeanLab.Linnik1951.Decomp519a
public import LeanLab.Linnik1951.Decomp552g

/-!
P0093 pages 155, 156, 159 and 160, equations 2.3, 3.4, 5.2 and 5.4.
Closure of residue_square_mean520 along the paper's character expansion:
the residue error is the nonprincipal part of the character expansion plus the
prime divisor term of 2.3, character orthogonality and the Gauss bound of
Lemma 1 turn its residue square mean into the nonprincipal character square
means, and Lemma 2 in the form nonprincipal_mass519 bounds each of those.
CONDITIONAL ON GRH and on the open leaves of nonprincipal_mass519.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951
open Finset MeasureTheory

open Classical in
/-- P0093 page 155 equation 2.3. The damped prime series over the primes in
the reduced class b modulo q, the inner sum over p congruent to l there.
It is zero on nonunit classes. -/
noncomputable def classSeries1121 (N q : ℕ) (z : ℝ) (b : ZMod q) : ℂ :=
  ∑' p : Nat.Primes, if IsUnit b ∧ (((p : ℕ) : ZMod q) = b) then
    (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * (p : ℕ)) : ℝ) * Complex.I) else 0

/-- P0093 page 155 equation 2.3. The prime divisor part of S at a over q plus
z, the term written B ln q there. -/
noncomputable def divisorPart1121 (N q a : ℕ) (z : ℝ) : ℂ :=
  ∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
    Complex.exp ((-(2 * Real.pi * ((a : ℝ) / q + z) * p) : ℝ) * Complex.I)

/-- P0093 page 155 equation 2.3, the passage from the sum over all p to
the classes l coprime to q plus the term B ln q. An absolutely summable series
over primes splits into the primes not dividing q and the finite prime factor
sum of q. -/
theorem prime_tsum_split1121 (f : ℕ → ℂ) (hf : Summable (fun p : Nat.Primes => f p))
    (q : ℕ) (hq : q ≠ 0) :
    (∑' p : Nat.Primes, if ¬ ((p : ℕ) ∣ q) then f p else 0) =
      (∑' p : Nat.Primes, f p) - ∑ p ∈ q.primeFactors, f p := by
  classical
  have h1 : ∀ p : Nat.Primes, (if ¬ ((p : ℕ) ∣ q) then f p else 0) =
      f p - (if (p : ℕ) ∣ q then f p else 0) := by
    intro p; split_ifs <;> simp
  have hfin : Summable (fun p : Nat.Primes => if (p : ℕ) ∣ q then f p else 0) :=
    Summable.of_norm_bounded hf.norm (fun p => by split_ifs <;> simp)
  rw [tsum_congr h1, hf.tsum_sub hfin]
  congr 1
  have hinj : Set.InjOn (fun p : Nat.Primes => (p : ℕ))
      ((fun p : Nat.Primes => (p : ℕ)) ⁻¹' (q.primeFactors : Set ℕ)) :=
    Nat.Primes.coe_nat_injective.injOn
  rw [tsum_eq_sum (s := q.primeFactors.preimage (fun p : Nat.Primes => (p : ℕ)) hinj)]
  · have hs : (∑ p ∈ q.primeFactors.preimage (fun p : Nat.Primes => (p : ℕ)) hinj,
        (if (p : ℕ) ∣ q then f p else 0)) =
        ∑ p ∈ q.primeFactors.preimage (fun p : Nat.Primes => (p : ℕ)) hinj, f p := by
      apply sum_congr rfl
      intro p hp
      rw [if_pos (Nat.dvd_of_mem_primeFactors (mem_preimage.mp hp))]
    rw [hs, sum_preimage (fun p : Nat.Primes => (p : ℕ)) q.primeFactors hinj f]
    intro x hx hr
    exact absurd ⟨⟨x, Nat.prime_of_mem_primeFactors hx⟩, rfl⟩ hr
  · intro p hp
    rw [if_neg]
    intro hd
    apply hp
    rw [mem_preimage]
    exact Nat.mem_primeFactors.mpr ⟨p.2, hd, hq⟩

/-- P0093 page 155 equation 2.3. Regrouping a finite weighted sum of class
series by prime: only the class of p itself survives, and only if it is a unit. -/
theorem class_weighted1121 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) (w : ZMod q → ℂ) :
    (∑ b : ZMod q, w b * classSeries1121 N q z b) =
      ∑' p : Nat.Primes, if IsUnit (((p : ℕ) : ZMod q)) then
        w ((p : ℕ) : ZMod q) * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * (p : ℕ)) : ℝ) * Complex.I)) else 0 := by
  classical
  have hg := prime_fourier_summable111_up111 N hN z
  unfold classSeries1121
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum]
  swap
  · intro b _
    apply Summable.mul_left
    refine Summable.of_norm_bounded hg.norm (fun p => ?_)
    split_ifs <;> simp
  apply tsum_congr
  intro p
  by_cases hu : IsUnit (((p : ℕ) : ZMod q))
  · rw [if_pos hu, Finset.sum_eq_single (((p : ℕ) : ZMod q))]
    · rw [if_pos ⟨hu, rfl⟩]
    · intro b _ hb
      rw [if_neg, mul_zero]
      rintro ⟨_, hpb⟩
      exact hb hpb.symm
    · intro h; exact absurd (mem_univ _) h
  · rw [if_neg hu]
    apply sum_eq_zero
    intro b _
    rw [if_neg, mul_zero]
    rintro ⟨hb, hpb⟩
    exact hu (hpb ▸ hb)

/-- P0093 page 155 equation 2.3. A prime class is a unit exactly when the
prime does not divide q. -/
theorem prime_unit_iff1121 (q : ℕ) (p : Nat.Primes) :
    IsUnit (((p : ℕ) : ZMod q)) ↔ ¬ ((p : ℕ) ∣ q) :=
  (ZMod.isUnit_iff_coprime p q).trans (Nat.Prime.coprime_iff_not_dvd p.2)

/-- P0093 page 155 equation 2.3, definition of A chi. Summing the class
series against a Dirichlet character gives the character prime series A chi. -/
theorem class_character1121 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ)
    (χ : DirichletCharacter ℂ q) :
    (∑ b : ZMod q, χ b * classSeries1121 N q z b) = Task519.characterPrime519 χ N z := by
  rw [class_weighted1121 N q hN z χ]
  unfold Task519.characterPrime519
  apply tsum_congr
  intro p
  split_ifs with hu
  · ring
  · rw [MulChar.map_nonunit χ hu]; ring

/-- P0093 page 159 before equation 5.1, A chi0 for the principal
character. The class series summed over all classes is the principal series
with the prime divisors of q removed. -/
theorem class_principal1121 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) :
    (∑ b : ZMod q, classSeries1121 N q z b) = principalPrime520 N q z := by
  have h := class_weighted1121 N q hN z (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  simp_rw [prime_unit_iff1121]
  unfold principalPrime520 primeFourier111_up111
  exact prime_tsum_split1121 (fun n : ℕ => (Real.exp (-(n : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * z * n) : ℝ) * Complex.I))
    (prime_fourier_summable111_up111 N hN z) q (NeZero.ne q)

/-- P0093 page 155 equation 2.3, second line. The additive twist of the
class series at a reduced numerator a is S at a over q plus z with the prime
divisor part removed. -/
theorem class_transform1121 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) (a : ℕ)
    (_ha : Nat.Coprime a q) :
    (∑ b : ZMod q, ZMod.stdAddChar (-(b * (a : ZMod q))) * classSeries1121 N q z b) =
      primeFourier111_up111 N ((a : ℝ) / q + z) - divisorPart1121 N q a z := by
  rw [class_weighted1121 N q hN z]
  have hph : ∀ p : Nat.Primes,
      ZMod.stdAddChar (-((((p : ℕ) : ZMod q)) * (a : ZMod q))) *
        ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * (p : ℕ)) : ℝ) * Complex.I)) =
      (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * ((a : ℝ) / q + z) * (p : ℕ)) : ℝ) * Complex.I) := by
    intro p
    rw [negative_unit_phase470 q a p, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hph, prime_unit_iff1121]
  unfold divisorPart1121 primeFourier111_up111
  exact prime_tsum_split1121 (fun n : ℕ => (Real.exp (-(n : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * ((a : ℝ) / q + z) * n) : ℝ) * Complex.I))
    (prime_fourier_summable111_up111 N hN ((a : ℝ) / q + z)) q (NeZero.ne q)

/-- P0093 page 156 equation 3.3. The principal Gauss sum twisted by a
reduced numerator a is the Moebius value of q. -/
theorem principal_ramanujan1121 (q : ℕ) [NeZero q] (a : ℕ) (ha : Nat.Coprime a q) :
    (∑ b : ZMod q, ZMod.stdAddChar (-(b * (a : ZMod q))) *
      (1 : DirichletCharacter ℂ q) b) = (ArithmeticFunction.moebius q : ℂ) := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a q).mpr ha
  have h := gaussSum_mulShift (1 : MulChar (ZMod q) ℂ) ZMod.stdAddChar (-u)
  rw [MulChar.one_apply (Units.isUnit _), one_mul] at h
  rw [← LeanLab.Grimmelt2019.MainTerm.gaussSum_principal, ← h]
  unfold gaussSum
  apply sum_congr rfl
  intro b _
  rw [AddChar.mulShift_apply, mul_comm, Units.val_neg, hu]
  congr 2
  ring

/-- P0093 page 155 equation 2.3, the bound O of ln q. Crude form: the
prime divisor part has norm at most q. -/
theorem divisor_part_norm1121 (N q a : ℕ) (z : ℝ) :
    ‖divisorPart1121 N q a z‖ ≤ q := by
  have hcard : q.primeFactors.card ≤ q := by
    by_cases hq : q = 0
    · simp [hq]
    · calc q.primeFactors.card ≤ (Icc 1 q).card := by
            apply card_le_card
            intro p hp
            exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).one_le,
              Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.dvd_of_mem_primeFactors hp)⟩
        _ = q := by simp
  unfold divisorPart1121
  calc _ ≤ ∑ p ∈ q.primeFactors, ‖(Real.exp (-(p : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * ((a : ℝ) / q + z) * p) : ℝ) * Complex.I)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, (1 : ℝ) := by
        apply sum_le_sum
        intro p _
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
            (Nat.cast_nonneg _))
    _ = q.primeFactors.card := by simp
    _ ≤ q := by exact_mod_cast hcard

/-- P0093 page 160 sum over a coprime to q. Natural reduced
representatives index the units of ZMod q. -/
theorem coprime_range_sum1121 (q : ℕ) [NeZero q] (F : ZMod q → ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), F (a : ZMod q)) =
      ∑ a : ZMod q, if IsUnit a then F a else 0 := by
  rw [LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range, sum_filter]
  apply sum_congr rfl
  intro a ha
  simp [ZMod.isUnit_iff_coprime]

/-- P0093 page 160 equation 5.4, the factor phi of q there. There are
at most phi of q nonprincipal characters modulo q. -/
theorem nonprincipal_card1121 (q : ℕ) [NeZero q] :
    ((univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) ≤ q.totient := by
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hfilter : (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card ≤ q.totient := by
    simpa only [Finset.card_univ, hcard] using
      Finset.card_filter_le (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
        (p := fun χ => χ ≠ 1)
  exact_mod_cast hfilter

/-- P0093 pages 155 and 156 equations 2.3 and 3.4. The residue error is the
centred additive transform of the class series, the nonprincipal part of the
character expansion, plus the prime divisor part.
CONDITIONAL ON the leaves of this file. -/
theorem residue_split1121 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) (a : ℕ)
    (ha : Nat.Coprime a q) :
    residueError520 N q a z =
      (∑ b : ZMod q, ZMod.stdAddChar (-(b * (a : ZMod q))) *
        (classSeries1121 N q z b - (1 : DirichletCharacter ℂ q) b *
          ((∑ c : ZMod q, classSeries1121 N q z c) / (q.totient : ℂ)))) +
        divisorPart1121 N q a z := by
  have hT := class_transform1121 N q hN z a ha
  have hR := principal_ramanujan1121 q a ha
  have hP := class_principal1121 N q hN z
  have hsplit : (∑ b : ZMod q, ZMod.stdAddChar (-(b * (a : ZMod q))) *
        (classSeries1121 N q z b - (1 : DirichletCharacter ℂ q) b *
          ((∑ c : ZMod q, classSeries1121 N q z c) / (q.totient : ℂ)))) =
      (∑ b : ZMod q, ZMod.stdAddChar (-(b * (a : ZMod q))) * classSeries1121 N q z b) -
        (∑ b : ZMod q, ZMod.stdAddChar (-(b * (a : ZMod q))) *
          (1 : DirichletCharacter ℂ q) b) *
          ((∑ c : ZMod q, classSeries1121 N q z c) / (q.totient : ℂ)) := by
    rw [sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro b _
    ring
  rw [hsplit, hT, hR, hP]
  unfold residueError520 principalCoefficient520
  push_cast
  ring

/-- P0093 page 160 equation 5.4 at one point. The residue square energy is at
most twice q over phi q times the nonprincipal character energy, plus the
prime divisor contribution. CONDITIONAL ON the leaves of this file. -/
theorem pointwise_energy1121 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (z : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖residueError520 N q a z‖ ^ 2) ≤
      2 * ((q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖Task519.characterPrime519 χ N z‖ ^ 2) + 2 * (q : ℝ) ^ 3 := by
  classical
  let G : ZMod q → ℂ := classSeries1121 N q z
  have hG : ∀ b, ¬ IsUnit b → G b = 0 := by
    intro b hb
    simp [G, classSeries1121, hb]
  let T : ZMod q → ℂ := fun a => ∑ b : ZMod q, ZMod.stdAddChar (-(b * a)) *
    (G b - (1 : DirichletCharacter ℂ q) b * ((∑ c : ZMod q, G c) / (q.totient : ℂ)))
  have hE := centered_gauss_energy552 q G hG
  have hchar : (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ‖∑ b : ZMod q, χ b * G b‖ ^ 2) =
      ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        ‖Task519.characterPrime519 χ N z‖ ^ 2 := by
    apply sum_congr rfl
    intro χ _
    rw [class_character1121 N q hN z χ]
  rw [hchar] at hE
  have hpt : ∀ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ‖residueError520 N q a z‖ ^ 2 ≤ 2 * ‖T (a : ZMod q)‖ ^ 2 + 2 * (q : ℝ) ^ 2 := by
    intro a ha
    have hcop := (mem_filter.mp ha).2
    have hs := residue_split1121 N q hN z a hcop
    have hD := divisor_part_norm1121 N q a z
    have hx : ‖residueError520 N q a z‖ ≤ ‖T (a : ZMod q)‖ + (q : ℝ) := by
      rw [hs]
      exact (norm_add_le _ _).trans (add_le_add le_rfl hD)
    have h0 : 0 ≤ ‖residueError520 N q a z‖ := norm_nonneg _
    have h1 : 0 ≤ ‖T (a : ZMod q)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖T (a : ZMod q)‖ - (q : ℝ))]
  have hsumT : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖T (a : ZMod q)‖ ^ 2) =
      ∑ a : ZMod q, if IsUnit a then ‖T a‖ ^ 2 else 0 :=
    coprime_range_sum1121 q (fun a => ‖T a‖ ^ 2)
  have hcard : (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤ q := by
    have := (card_filter_le (range q) (fun a => Nat.Coprime a q)).trans
      (card_range q).le
    exact_mod_cast this
  calc
    _ ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        (2 * ‖T (a : ZMod q)‖ ^ 2 + 2 * (q : ℝ) ^ 2) := sum_le_sum hpt
    _ = 2 * (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖T (a : ZMod q)‖ ^ 2) +
        (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) * (2 * (q : ℝ) ^ 2) := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ 2 * ((q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ‖Task519.characterPrime519 χ N z‖ ^ 2) + (q : ℝ) * (2 * (q : ℝ) ^ 2) := by
      rw [hsumT]
      exact add_le_add (mul_le_mul_of_nonneg_left hE (by norm_num))
        (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = _ := by ring

end LeanLab.Linnik1951
