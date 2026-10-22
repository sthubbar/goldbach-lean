module

public import LeanLab.Common.Goldbach

/-!
# Counting lemmas for Dudek's prime plus square-free theorem

Unit U-5500, CLOUD 20261019T1218Z-cloud24. AI wrote the Lean code. Known mathematics: the
counting behind Dudek 2017, BJS Theorem 53.

Let `A` be the primes in `[3, N]`. If `N - p` is not square-free for every `p ∈ A`, some odd prime
`r` has `r² ∣ N - p`. For `r ≤ Q` the prime `p` lies in the class `cls N r` of `N mod r²`; for
`r > Q` the number `N - p ≤ N` is a multiple of `r²`, at most `N/r²` choices.
`card_le_of_no_rep` states this count, and `sum_prime_inv_le` bounds `Σ 1/(r(r - 1))`. The lab
file also derived the even case for `N ≥ exp 12000` from a Selberg sieve Brun-Titchmarsh bound;
that part is not needed here, since `DudekFrom4e18.lean` and `DudekFrom1e9.lean` use the large
sieve form, and was removed from this copy.
-/

@[expose] public section


open Finset Real

noncomputable section

namespace LeanLab.AlmostPrimes.DudekLarge

/-- Telescoping: `Σ_{a < n ≤ M} 1/(n(n - 1)) = 1/a - 1/M` for `1 ≤ a ≤ M`. -/
theorem sum_Ioc_inv_mul_pred {a : ℕ} (ha : 1 ≤ a) :
    ∀ M : ℕ, a ≤ M →
      ∑ n ∈ Ioc a M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 / a - 1 / M := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih]
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    rw [show (M : ℝ) + 1 - 1 = M by ring]
    field_simp
    ring

theorem sum_Ioc_inv_mul_pred_le {a : ℕ} (ha : 1 ≤ a) (M : ℕ) :
    ∑ n ∈ Ioc a M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 / a := by
  rcases le_or_gt a M with h | h
  · rw [sum_Ioc_inv_mul_pred ha M h]
    have : (0 : ℝ) ≤ 1 / M := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp

/-- `Σ_{3 ≤ r ≤ Q, r prime} 1/(r(r - 1)) ≤ 3/10`; the true value of the full sum is `0.2731`. -/
theorem sum_prime_inv_le (Q : ℕ) :
    ∑ r ∈ (Icc 3 Q).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 3 / 10 := by
  have hsub : (Icc 3 Q).filter Nat.Prime ⊆ ((Icc 3 31).filter Nat.Prime) ∪ Ioc 31 Q := by
    intro r hr
    simp only [mem_filter, mem_Icc] at hr
    simp only [mem_union, mem_filter, mem_Icc, mem_Ioc]
    by_cases h : r ≤ 31
    · exact Or.inl ⟨⟨hr.1.1, h⟩, hr.2⟩
    · exact Or.inr ⟨by omega, hr.1.2⟩
  have hnn : ∀ r ∈ ((Icc 3 31).filter Nat.Prime) ∪ Ioc 31 Q,
      (0 : ℝ) ≤ 1 / ((r : ℝ) * ((r : ℝ) - 1)) := by
    intro r hr
    have : 1 ≤ r := by
      simp only [mem_union, mem_filter, mem_Icc, mem_Ioc] at hr; omega
    have : (1 : ℝ) ≤ r := by exact_mod_cast this
    have : (0 : ℝ) ≤ (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    positivity
  calc _ ≤ ∑ r ∈ ((Icc 3 31).filter Nat.Prime) ∪ Ioc 31 Q,
          (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := sum_le_sum_of_subset_of_nonneg hsub
            (fun r hr _ => hnn r hr)
    _ ≤ ∑ r ∈ (Icc 3 31).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) +
          ∑ r ∈ Ioc 31 Q, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := by
          rw [sum_union]
          rw [Finset.disjoint_left]
          intro r h1 h2
          simp only [mem_filter, mem_Icc, mem_Ioc] at h1 h2
          omega
    _ ≤ ∑ r ∈ (Icc 3 31).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) + 1 / 31 := by
          have := sum_Ioc_inv_mul_pred_le (a := 31) (by norm_num) Q
          push_cast at this
          linarith
    _ ≤ 3 / 10 := by
          have hS : (Icc 3 31).filter Nat.Prime = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
            decide
          rw [hS]
          simp
          norm_num

/-- The primes `p ≤ N + 1` in the class `N mod r²`, the set Brun-Titchmarsh bounds. -/
def cls (N r : ℕ) : Finset ℕ :=
  (Icc 1 (N + 1)).filter (fun p => p.Prime ∧ p % (r ^ 2) = N % (r ^ 2))

/-- At most `N / n²` numbers `p < N` have `n² ∣ N - p`. -/
theorem card_dvd_sub_le (N n : ℕ) :
    ((range N).filter (fun p => n ^ 2 ∣ N - p)).card ≤ N / n ^ 2 := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  apply card_le_card_of_injOn (fun p => N - p)
  · intro p hp
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hp
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq]
    exact ⟨⟨by omega, by omega⟩, hp.2⟩
  · intro p hp p' hp' h
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hp hp'
    simp only at h
    omega

/-- **Counting step.** If no even `N ≥ 4` decomposition `p + m` with `m` square-free exists, then
`π N - 1` is at most the Brun-Titchmarsh classes for odd primes `r ≤ Q` plus `Σ_{Q < n ≤ N} N/n²`. -/
theorem card_le_of_no_rep {N : ℕ} (Q : ℕ) (hE : Even N) (h4 : 4 ≤ N)
    (hno : ¬ ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m) :
    (Nat.primeCounting N : ℝ) - 1 ≤
      ∑ r ∈ (Icc 3 Q).filter Nat.Prime, ((cls N r).card : ℝ) +
        ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ) := by
  classical
  set A := (Icc 3 N).filter Nat.Prime with hA
  have h1 : Nat.primeCounting N ≤ A.card + 1 := by
    rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
    calc (N + 1).primesBelow.card ≤ (insert 2 A).card := by
          apply card_le_card
          intro p hp
          rw [Nat.mem_primesBelow] at hp
          rw [mem_insert, hA, mem_filter, mem_Icc]
          by_cases h2 : p = 2
          · exact Or.inl h2
          · have := hp.2.two_le
            exact Or.inr ⟨⟨by omega, by omega⟩, hp.2⟩
      _ ≤ A.card + 1 := card_insert_le _ _
  set B1 := ((Icc 3 Q).filter Nat.Prime).biUnion (fun r => cls N r) with hB1
  set B2 := (Ioc Q N).biUnion (fun n => (range N).filter (fun p => n ^ 2 ∣ N - p)) with hB2
  have hsub : A ⊆ B1 ∪ B2 := by
    intro p hp
    rw [hA, mem_filter, mem_Icc] at hp
    obtain ⟨⟨hp3, hpN⟩, hp⟩ := hp
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hpne : p ≠ N := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) hE
    have hm : ¬ Squarefree (N - p) := by
      intro hsq
      exact hno ⟨p, N - p, hp, by omega, hsq, by omega⟩
    rw [Nat.squarefree_iff_prime_squarefree] at hm
    push Not at hm
    obtain ⟨r, hr, hrr⟩ := hm
    have hmodd : Odd (N - p) := by
      rcases hE with ⟨k, hk⟩
      rcases hpodd with ⟨j, hj⟩
      exact ⟨k - j - 1, by omega⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      have : 2 ∣ N - p := (Dvd.intro 2 rfl).trans hrr
      exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr this)
    have hr3 : 3 ≤ r := by have := hr.two_le; omega
    have hrr' : r ^ 2 ∣ N - p := by rw [sq]; exact hrr
    rw [mem_union]
    by_cases hQ : r ≤ Q
    · left
      rw [hB1, mem_biUnion]
      refine ⟨r, by rw [mem_filter, mem_Icc]; exact ⟨⟨hr3, hQ⟩, hr⟩, ?_⟩
      rw [cls, mem_filter, mem_Icc]
      refine ⟨⟨by omega, by omega⟩, hp, ?_⟩
      exact ((Nat.modEq_iff_dvd' hpN).mpr hrr')
    · right
      rw [hB2, mem_biUnion]
      have hpos : 0 < N - p := by omega
      have hrle : r ≤ N - p := by
        have := Nat.le_of_dvd hpos hrr
        nlinarith
      refine ⟨r, by rw [mem_Ioc]; omega, ?_⟩
      rw [mem_filter, mem_range]
      exact ⟨by omega, hrr'⟩
  have hcard : A.card ≤ ∑ r ∈ (Icc 3 Q).filter Nat.Prime, (cls N r).card +
      ∑ n ∈ Ioc Q N, N / n ^ 2 := by
    calc A.card ≤ (B1 ∪ B2).card := card_le_card hsub
      _ ≤ B1.card + B2.card := card_union_le _ _
      _ ≤ _ := by
        apply add_le_add
        · exact card_biUnion_le
        · exact card_biUnion_le.trans (sum_le_sum fun n _ => card_dvd_sub_le N n)
  have : (Nat.primeCounting N : ℝ) ≤ (A.card : ℝ) + 1 := by exact_mod_cast h1
  have h2 : (A.card : ℝ) ≤ ∑ r ∈ (Icc 3 Q).filter Nat.Prime, ((cls N r).card : ℝ) +
      ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith

/-- `10⁴ (L + 1)⁵ ≤ e^{L/20}` for `L ≥ 12000`, from `e^t ≥ t¹²/12!` at `t = L/20 ≥ 600`. -/
theorem poly_le_exp {L : ℝ} (hL : 12000 ≤ L) : 10000 * (L + 1) ^ 5 ≤ exp (L / 20) := by
  set t := L / 20 with ht
  have ht600 : 600 ≤ t := by rw [ht]; linarith
  have h1 : L + 1 ≤ 21 * t := by rw [ht]; linarith
  have h5 : (L + 1) ^ 5 ≤ (21 * t) ^ 5 := pow_le_pow_left₀ (by linarith) h1 5
  have hexp := Real.pow_div_factorial_le_exp t (by linarith : 0 ≤ t) 12
  have hf : ((Nat.factorial 12 : ℕ) : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [hf] at hexp
  have h7 : (600 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht600 7
  have ht5 : 0 ≤ t ^ 5 := by positivity
  have hprod : (600 : ℝ) ^ 7 * t ^ 5 ≤ t ^ 7 * t ^ 5 := mul_le_mul_of_nonneg_right h7 ht5
  have h12 : t ^ 12 = t ^ 7 * t ^ 5 := by ring
  have h21 : (21 * t) ^ 5 = 4084101 * t ^ 5 := by ring
  have hdiv : t ^ 12 / 479001600 = t ^ 12 * (1 / 479001600) := by ring
  rw [hdiv] at hexp
  nlinarith

/-- `Σ_{Q < n ≤ N} ⌊N/n²⌋ ≤ N/Q`. -/
theorem tail_le {N Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ) ≤ N / Q := by
  calc ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ)
      ≤ ∑ n ∈ Ioc Q N, (N : ℝ) * (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
        apply sum_le_sum
        intro n hn
        rw [mem_Ioc] at hn
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
        have hpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
        calc ((N / n ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / ((n ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
          _ = (N : ℝ) / ((n : ℝ) ^ 2) := by push_cast; ring
          _ ≤ (N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
              apply div_le_div_of_nonneg_left (by positivity) hpos
              nlinarith
          _ = _ := by ring
    _ = (N : ℝ) * ∑ n ∈ Ioc Q N, (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by rw [mul_sum]
    _ ≤ (N : ℝ) * (1 / Q) := by
        apply mul_le_mul_of_nonneg_left (sum_Ioc_inv_mul_pred_le hQ N) (by positivity)
    _ = N / Q := by ring

end LeanLab.AlmostPrimes.DudekLarge

