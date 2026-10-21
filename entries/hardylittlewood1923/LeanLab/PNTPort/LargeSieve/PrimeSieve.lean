module

public import LeanLab.PNTPort.LargeSieve.Parseval
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The arithmetic large sieve over prime moduli

Lab proof, unit U-5000. AI wrote this file. Known mathematics, Renyi and Gallagher's prime
modulus form, no cited input.

* `prime_large_sieve`: `∑_{p ≤ Q prime} (p ∑_{b<p} ‖Z(p,b)‖² - ‖Z‖²) ≤ (N + 2Q²) ∑ ‖a_n‖²`.
* `sifted_card_bound`: if a finite set `A ⊆ (M, M+N]` meets at most `p - ω p` residue
  classes modulo each prime `p ≤ Q`, with `ω p < p`, then
  `|A| ∑_{p ≤ Q prime} ω p / (p - ω p) ≤ N + 2Q²`.
-/

@[expose] public section


namespace LeanLab.PNTPort.LargeSieve

open Complex Finset Real

/-- The primes up to `Q`. -/
def primesUpTo (Q : ℕ) : Finset ℕ := (Icc 1 Q).filter Nat.Prime

lemma parseval_sub_zero (I : Finset ℤ) (a : ℤ → ℂ) {q : ℕ} (hq : 0 < q) :
    q * ∑ b ∈ range q, ‖resSum I a q b‖ ^ 2 - ‖∑ n ∈ I, a n‖ ^ 2 =
      ∑ c ∈ Ico 1 q, ‖∑ n ∈ I, a n * e (n * fareyPt (q, c))‖ ^ 2 := by
  rw [← parseval_mod I a hq, range_eq_Ico, sum_eq_sum_Ico_succ_bot hq]
  simp only [Nat.cast_zero, mul_zero, zero_div, e_zero, mul_one, add_sub_cancel_left, fareyPt]
  apply sum_congr rfl; intro c _
  simp_rw [mul_div_assoc]

/-- **The prime modulus large sieve.** -/
theorem prime_large_sieve {Q : ℕ} (hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ p ∈ primesUpTo Q, ((p : ℝ) * ∑ b ∈ range p, ‖resSum (Ioc M (M + N)) a p b‖ ^ 2 -
        ‖∑ n ∈ Ioc M (M + N), a n‖ ^ 2) ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  set I := Ioc M (M + N)
  set f : ℕ × ℕ → ℝ := fun x => ‖∑ n ∈ I, a n * e (n * fareyPt x)‖ ^ 2 with hf
  have hprime : ∀ p ∈ primesUpTo Q, p.Prime := fun p hp => (mem_filter.1 hp).2
  have h1 : ∑ p ∈ primesUpTo Q, ((p : ℝ) * ∑ b ∈ range p, ‖resSum I a p b‖ ^ 2 -
      ‖∑ n ∈ I, a n‖ ^ 2) = ∑ p ∈ primesUpTo Q, ∑ c ∈ Ico 1 p, f (p, c) :=
    sum_congr rfl (fun p hp => parseval_sub_zero I a (hprime p hp).pos)
  set T : Finset (ℕ × ℕ) := (primesUpTo Q).biUnion
    (fun p => (Ico 1 p).map ⟨fun c => (p, c), fun c c' h => by simpa using h⟩) with hT
  have h2 : ∑ p ∈ primesUpTo Q, ∑ c ∈ Ico 1 p, f (p, c) = ∑ x ∈ T, f x := by
    rw [hT, sum_biUnion]
    · apply sum_congr rfl; intro p _; rw [sum_map]; rfl
    · intro p _ p' _ hne
      refine disjoint_left.2 ?_
      intro x hx hx'
      rw [mem_map] at hx hx'
      obtain ⟨c, _, rfl⟩ := hx
      obtain ⟨c', _, h⟩ := hx'
      exact hne (congrArg Prod.fst h).symm
  have hsub : T ⊆ farey Q := by
    intro x hx
    rw [hT, mem_biUnion] at hx
    obtain ⟨p, hp, hx⟩ := hx
    rw [mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [mem_Ico] at hc
    have hpQ := (mem_Icc.1 (mem_filter.1 hp).1)
    rw [mem_farey]
    refine ⟨hpQ.1, hpQ.2, hc.2, ?_⟩
    show Nat.Coprime c p
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hprime p hp)]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have h3 : ∑ x ∈ T, f x ≤ ∑ x ∈ farey Q, f x :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  rw [h1, h2]
  exact h3.trans (farey_large_sieve hQ a M N)

/-- **Sifted set bound from the prime modulus large sieve.** -/
theorem sifted_card_bound {Q : ℕ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Ioc M (M + N)) (ω : ℕ → ℕ) (hω : ∀ p ∈ primesUpTo Q, ω p < p)
    (hres : ∀ p ∈ primesUpTo Q,
      ((range p).filter (fun b : ℕ => ∃ n ∈ A, n % (p : ℤ) = (b : ℤ))).card ≤ p - ω p) :
    (A.card : ℝ) * ∑ p ∈ primesUpTo Q, ((ω p : ℝ) / (p - ω p)) ≤ N + 2 * (Q : ℝ) ^ 2 := by
  set I := Ioc M (M + N)
  set a : ℤ → ℂ := fun n => if n ∈ A then 1 else 0 with ha
  have hprime : ∀ p ∈ primesUpTo Q, p.Prime := fun p hp => (mem_filter.1 hp).2
  have hnorm : ∀ n, ‖a n‖ ^ 2 = if n ∈ A then 1 else 0 := by
    intro n; simp only [ha]; split_ifs <;> simp
  have hsumsq : ∑ n ∈ I, ‖a n‖ ^ 2 = A.card := by
    simp_rw [hnorm]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter,
      inter_eq_right.2 hA]
  -- residue sums are counts
  have hres_eq : ∀ (p : ℕ) (b : ℕ),
      resSum I a p b = (((A.filter (fun n => n % (p : ℤ) = b)).card : ℕ) : ℂ) := by
    intro p b
    unfold resSum
    simp only [ha]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_filter]
    congr 2
    ext n
    simp only [mem_filter]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨hA h2, h1, h2⟩
  have htot : ∑ n ∈ I, a n = (A.card : ℂ) := by
    simp only [ha]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter,
      inter_eq_right.2 hA]
  set Acard : ℝ := (A.card : ℝ)
  -- Cauchy-Schwarz on each prime
  have hcs : ∀ p ∈ primesUpTo Q, Acard ^ 2 * ((ω p : ℝ) / (p - ω p)) ≤
      (p : ℝ) * ∑ b ∈ range p, ‖resSum I a p b‖ ^ 2 - ‖∑ n ∈ I, a n‖ ^ 2 := by
    intro p hp
    have hpp := (hprime p hp).pos
    have hωp := hω p hp
    set R := (range p).filter (fun b : ℕ => ∃ n ∈ A, n % (p : ℤ) = (b : ℤ)) with hR
    set z : ℕ → ℝ := fun b => ((A.filter (fun n => n % (p : ℤ) = b)).card : ℝ) with hz
    have hnormz : ∀ b, ‖resSum I a p b‖ ^ 2 = z b ^ 2 := by
      intro b; rw [hres_eq, Complex.norm_natCast]
    simp_rw [hnormz]
    rw [htot, Complex.norm_natCast]
    -- `|A| = ∑_{b ∈ R} z b`
    have hAsum : Acard = ∑ b ∈ R, z b := by
      have hfib : A.card = ∑ b ∈ range p, (A.filter (fun n => n % (p : ℤ) = b)).card := by
        rw [card_eq_sum_card_fiberwise (f := fun n => (n % (p : ℤ)).toNat)]
        · apply sum_congr rfl; intro b _
          congr 1; ext n; simp only [mem_filter]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, by
              have h0 : 0 ≤ n % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpp.ne')
              omega⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; simp⟩
        · intro n _
          simp only [coe_range, Set.mem_Iio]
          have h0 : 0 ≤ n % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpp.ne')
          have h1 : n % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hpp)
          omega
      have hzero : ∀ b ∈ range p, b ∉ R → z b = 0 := by
        intro b hb hbR
        simp only [hz, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
        intro n hn hnb
        exact hbR (mem_filter.2 ⟨hb, n, hn, hnb⟩)
      rw [show Acard = ((A.card : ℕ) : ℝ) from rfl, hfib, Nat.cast_sum]
      rw [← sum_subset (filter_subset _ _) hzero]
    have hRcard : (R.card : ℝ) ≤ p - ω p := by
      have := hres p hp
      have : ((R.card : ℕ) : ℝ) ≤ ((p - ω p : ℕ) : ℝ) := by exact_mod_cast this
      rwa [Nat.cast_sub hωp.le] at this
    have hpω : (0 : ℝ) < p - ω p := by
      have : (ω p : ℝ) < p := by exact_mod_cast hωp
      linarith
    have hcs1 : Acard ^ 2 ≤ (p - ω p) * ∑ b ∈ range p, z b ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := R) (f := z)
      rw [← hAsum] at this
      calc Acard ^ 2 ≤ R.card * ∑ b ∈ R, z b ^ 2 := this
        _ ≤ (p - ω p) * ∑ b ∈ R, z b ^ 2 :=
            mul_le_mul_of_nonneg_right hRcard (sum_nonneg (fun _ _ => by positivity))
        _ ≤ (p - ω p) * ∑ b ∈ range p, z b ^ 2 :=
            mul_le_mul_of_nonneg_left
              (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                (fun _ _ _ => by positivity)) hpω.le
    have hgoal : Acard ^ 2 * ((ω p : ℝ) / (p - ω p)) =
        Acard ^ 2 * (p / (p - ω p)) - Acard ^ 2 := by
      field_simp; ring
    rw [hgoal]
    have : Acard ^ 2 * (p / (p - ω p)) ≤ p * ∑ b ∈ range p, z b ^ 2 := by
      rw [mul_div_assoc', div_le_iff₀ hpω]
      have hp0 : (0 : ℝ) ≤ p := by positivity
      nlinarith
    linarith
  have hmain := prime_large_sieve hQ a M N
  rw [hsumsq] at hmain
  have hsum : Acard ^ 2 * ∑ p ∈ primesUpTo Q, ((ω p : ℝ) / (p - ω p)) ≤
      (N + 2 * (Q : ℝ) ^ 2) * Acard := by
    rw [mul_sum]
    exact (sum_le_sum hcs).trans hmain
  have hA0 : 0 ≤ Acard := Nat.cast_nonneg _
  rcases eq_or_lt_of_le hA0 with h | h
  · rw [← h, zero_mul]; positivity
  · have : Acard * (Acard * ∑ p ∈ primesUpTo Q, ((ω p : ℝ) / (p - ω p))) ≤
        Acard * (N + 2 * (Q : ℝ) ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this h

end LeanLab.PNTPort.LargeSieve
