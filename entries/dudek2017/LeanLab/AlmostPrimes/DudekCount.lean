module

public import LeanLab.AlmostPrimes.DudekFrom4e18

/-!
# Dudek's theorem with a count, for even `N ≥ e^42`

Unit U-5660, CLOUD 20261019T1515Z-cloud27. AI wrote the Lean code. KNOWN mathematics in method,
Estermann 1931 has the asymptotic count; Dudek 2017.

`dudek_count`: for even `N ≥ e^42`, at least `0.05 N / log N` primes `3 ≤ p ≤ N` have `N - p`
square-free and positive. No cited input. The count is `π(N) - 1` minus the bad primes, with
Chebyshev's `π(N) ≥ (0.9212 N - 5 log N)/log N` and `DudekFrom4e18.bad_sum_le`'s `0.87 N/log N`.
-/

@[expose] public section


open Finset Real

noncomputable section

namespace LeanLab.AlmostPrimes.DudekCount

open LeanLab.AlmostPrimes.DudekLarge LeanLab.AlmostPrimes.DudekFrom4e18

/-- The good primes: `3 ≤ p ≤ N` with `N - p` square-free. -/
def good (N : ℕ) : Finset ℕ :=
  (Icc 3 N).filter (fun p => p.Prime ∧ Squarefree (N - p))

/-- **Counting step.** For even `N ≥ 4`, `π N - 1 - #good` is at most the Brun-Titchmarsh classes
for odd primes `r ≤ Q` plus `Σ_{Q < n ≤ N} ⌊N/n²⌋`. -/
theorem card_bad_le {N : ℕ} (Q : ℕ) (hE : Even N) (h4 : 4 ≤ N) :
    (Nat.primeCounting N : ℝ) - 1 - (good N).card ≤
      ∑ r ∈ (Icc 3 Q).filter Nat.Prime, ((cls N r).card : ℝ) +
        ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ) := by
  classical
  set A := (Icc 3 N).filter Nat.Prime with hA
  set Bd := A.filter (fun p => ¬ Squarefree (N - p)) with hBd
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
  have hsplit : A.card = (good N).card + Bd.card := by
    rw [hBd, ← card_filter_add_card_filter_not (s := A) (fun p => Squarefree (N - p))]
    congr 1
    congr 1
    ext p; simp [good, hA, mem_filter, and_assoc]
  set B1 := ((Icc 3 Q).filter Nat.Prime).biUnion (fun r => cls N r) with hB1
  set B2 := (Ioc Q N).biUnion (fun n => (range N).filter (fun p => n ^ 2 ∣ N - p)) with hB2
  have hsub : Bd ⊆ B1 ∪ B2 := by
    intro p hp
    rw [hBd, mem_filter, hA, mem_filter, mem_Icc] at hp
    obtain ⟨⟨⟨hp3, hpN⟩, hp⟩, hm⟩ := hp
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hpne : p ≠ N := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) hE
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
  have hcard : Bd.card ≤ ∑ r ∈ (Icc 3 Q).filter Nat.Prime, (cls N r).card +
      ∑ n ∈ Ioc Q N, N / n ^ 2 := by
    calc Bd.card ≤ (B1 ∪ B2).card := card_le_card hsub
      _ ≤ B1.card + B2.card := card_union_le _ _
      _ ≤ _ := by
        apply add_le_add
        · exact card_biUnion_le
        · exact card_biUnion_le.trans (sum_le_sum fun n _ => card_dvd_sub_le N n)
  have e1 : (Nat.primeCounting N : ℝ) ≤ ((good N).card : ℝ) + Bd.card + 1 := by
    have : Nat.primeCounting N ≤ (good N).card + Bd.card + 1 := by omega
    exact_mod_cast this
  have e2 : (Bd.card : ℝ) ≤ ∑ r ∈ (Icc 3 Q).filter Nat.Prime, ((cls N r).card : ℝ) +
      ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith

/-- **Dudek's theorem with a count, PROVED, no cited input.** For even `N ≥ e^42`, at least
`0.05 N / log N` primes `3 ≤ p ≤ N` have `N - p` square-free. Each such `N - p` is positive, since
`N - p` is odd. -/
theorem dudek_count (N : ℕ) (hE : Even N) (hN : exp 42 ≤ N) :
    0.05 * N / Real.log N ≤ ((good N).card : ℝ) := by
  have hb := bad_sum_le N hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (exp_pos _) hN
  set L := Real.log N with hLdef
  have hL : 42 ≤ L := by
    have := Real.log_le_log (exp_pos 42) hN
    rwa [Real.log_exp] at this
  have hexpL : exp L = N := Real.exp_log hNpos
  have hexp55 : exp (0.55 * L) ≤ N := by
    rw [← hexpL]; exact Real.exp_le_exp.mpr (by linarith)
  have hNbig : 5000 * L * (L + 1) ≤ (N : ℝ) := (poly_le_exp42 hL).trans hexp55
  have hNL : 200000 * L ≤ (N : ℝ) := by nlinarith
  have h30 : 30 ≤ N := by
    have : (30 : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hcount := card_bad_le (40 * ⌈L⌉₊) hE (by omega)
  have hpi := LeanLab.ChebyshevExplicit.pi_ge_chebyshev30 N h30
  have hLpos : 0 < L := by linarith
  rw [div_le_iff₀ hLpos, ← hLdef] at hpi
  have h1 := hcount.trans hb
  rw [le_div_iff₀ hLpos] at h1
  rw [div_le_iff₀ hLpos]
  nlinarith

/-- The good primes give representations with `N - p ≥ 1`. -/
lemma good_rep {N p : ℕ} (hE : Even N) (hp : p ∈ good N) :
    p.Prime ∧ 0 < N - p ∧ Squarefree (N - p) ∧ N = p + (N - p) := by
  rw [good, mem_filter, mem_Icc] at hp
  obtain ⟨⟨h3, hpN⟩, hpp, hsq⟩ := hp
  have hpne : p ≠ N := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (hpp.odd_of_ne_two (by omega))) hE
  exact ⟨hpp, by omega, hsq, by omega⟩

end LeanLab.AlmostPrimes.DudekCount

