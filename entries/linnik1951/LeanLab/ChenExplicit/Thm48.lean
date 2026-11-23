module

public import LeanLab.ChenExplicit.C2Bound

/-!
AI-written Lean code, Claude, 2026-10-17, run 20261017T2104Z-19452, unit U-0373.
P0010 T. Yamada, Explicit Chen's theorem, arXiv 1511.03409v2, equation (48): `|A| > N / log N`.

We derive (48) from the Rosser-Schoenfeld 1962 lower bound `π(x) > x / (log x - 1/2)` for
`x ≥ 67`, as quoted in arXiv 2404.17165 Section 7.1; the 1962 paper itself was not read, its
Project Euclid page blocked the fetch. `|A| ≥ π(N) - ω(N)` and `ω(N) ≤ log N / log 2`, and the
gap `N / (log N - 1/2) - N / log N ≥ N / (2 log² N)` dwarfs `ω(N)`.
-/

@[expose] public section

open Finset Real

noncomputable section
namespace LeanLab.ChenExplicit.Yamada

/-- Rosser-Schoenfeld 1962, CITED as quoted in arXiv 2404.17165 Section 7.1:
`x / (log x - 1/2) < π(x)` for `x ≥ 67`; stated at natural `x`. -/
def RS62 : Prop := ∀ n : ℕ, 67 ≤ n → (n : ℝ) / (log n - 1 / 2) < (Nat.primeCounting n : ℝ)

lemma primeCounting_le_Acard_add (N : ℕ) (hN : N ≠ 0) :
    Nat.primeCounting N ≤ Acard N + #N.primeFactors := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have h := Finset.card_filter_add_card_filter_not (s := Nat.primesLE N) (fun p => p ∣ N)
  rw [← h, add_comm]
  apply add_le_add
  · apply Finset.card_le_card
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hp.1.2, hp.2⟩
    rcases Nat.lt_or_ge p N with h1 | h1
    · exact h1
    · exfalso; apply hp.2; rw [show p = N by omega]
  · apply Finset.card_le_card
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp
    exact Nat.mem_primeFactors.mpr ⟨hp.1.2, hp.2, hN⟩

lemma two_pow_card_primeFactors_le (N : ℕ) (hN : N ≠ 0) : 2 ^ #N.primeFactors ≤ N := by
  calc 2 ^ #N.primeFactors ≤ ∏ p ∈ N.primeFactors, p := by
        apply Finset.pow_card_le_prod
        intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.prod_primeFactors_dvd N)

lemma card_primeFactors_le_log (N : ℕ) (hN : N ≠ 0) :
    (#N.primeFactors : ℝ) ≤ 2 * log N := by
  have h := two_pow_card_primeFactors_le N hN
  have h' : ((2 : ℝ) ^ #N.primeFactors) ≤ N := by exact_mod_cast h
  have hl := Real.log_le_log (by positivity) h'
  rw [Real.log_pow] at hl
  have l2 := log_two_gt_d9
  norm_num at l2
  have hL : 0 ≤ log (N : ℝ) := Real.log_natCast_nonneg N
  nlinarith

/-- **(48) from Rosser-Schoenfeld, PROVED.** CONDITIONAL ON `RS62`. -/
theorem thm48_of_RS62 (hRS : RS62) : Thm48 := by
  intro N hEven hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hN0 : N ≠ 0 := by rintro rfl; simp at hpos
  set L := log (N : ℝ) with hLdef
  have hL : exp 36 < L := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have h36 : (100 : ℝ) ≤ exp 36 := by
    have := Real.quadratic_le_exp_of_nonneg (x := 36) (by norm_num); norm_num at this; linarith
  have hL100 : 100 < L := by linarith
  have hNe : (N : ℝ) = exp L := (exp_log hpos).symm
  have h67 : 67 ≤ N := by
    have : (67 : ℝ) < N := by
      rw [hNe]; have := add_one_le_exp L; linarith
    exact_mod_cast this.le
  have hrs := hRS N h67
  rw [← hLdef] at hrs
  have hcount := primeCounting_le_Acard_add N hN0
  have hcount' : (Nat.primeCounting N : ℝ) ≤ Acard N + #N.primeFactors := by exact_mod_cast hcount
  have hw := card_primeFactors_le_log N hN0
  rw [← hLdef] at hw
  -- N ≥ L⁴ / 24 ≥ 4 L³
  have h4 := Real.pow_div_factorial_le_exp L (by linarith) 4
  have hf : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf, ← hNe] at h4
  have hL3 : 4 * L ^ 3 ≤ (N : ℝ) := by
    have : 4 * L ^ 3 ≤ L ^ 4 / 24 := by
      rw [le_div_iff₀ (by norm_num)]
      have : 0 < L ^ 3 := by positivity
      nlinarith
    linarith
  -- the gap
  have hL0 : 0 < L := by linarith
  have hLh : 0 < L - 1 / 2 := by linarith
  have gap : (N : ℝ) / L + 2 * L ≤ N / (L - 1 / 2) := by
    rw [div_add' _ _ _ hL0.ne', div_le_div_iff₀ hL0 hLh]
    nlinarith
  show (N : ℝ) / L < Acard N
  linarith

/-- **Yamada Theorem 1.1** CONDITIONAL ON Theorems 5.1, 6.1, 7.1 and Rosser-Schoenfeld 1962. -/
theorem yamada_of_sieve_RS (hRS : RS62) (h51 : Thm51) (h61 : Thm61) (h71 : Thm71) : Yamada :=
  yamada_of_sieve (thm48_of_RS62 hRS) h51 h61 h71

end LeanLab.ChenExplicit.Yamada
