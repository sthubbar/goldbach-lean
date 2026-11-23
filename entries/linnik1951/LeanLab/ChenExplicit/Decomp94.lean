module

public import LeanLab.ChenExplicit.PrintedWiring
public import LeanLab.ChenExplicit.Thm48

/-!
AI wrote this Lean code. CODEX task94.
P0009 arXiv 2207.09452 v6, Lemma 42, eq 125, pages 39 and 40.
The final statement is the existing PrintedWiring.PrintedLemma42.
The explicit prime counting bounds stay CONDITIONAL ON Rosser and Schoenfeld.
We use the elementary bound 2 log N for excluded prime divisors.
This follows the counting argument with Lemma 22 eq 64 instead of eq 65.
Binary Goldbach is OPEN.
-/

@[expose] public section

open Real Finset

namespace LeanLab.ChenExplicit.Decomp94


/-- LEAF. P0009 page 40, first display of the proof of Lemma 42.
Discarding primes dividing N loses at most the number of distinct prime factors. -/
theorem count_sandwich (N : ℕ) (hN : N ≠ 0) :
    Nat.primeCounting N ≤ PrintedWiring.cardA N + #N.primeFactors ∧
      PrintedWiring.cardA N ≤ Nat.primeCounting N := by
  constructor
  · simpa only [PrintedWiring.cardA, Yamada.Acard] using
      Yamada.primeCounting_le_Acard_add N hN
  · rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card
    intro p hp
    simp only [PrintedWiring.cardA, mem_filter, mem_range] at hp
    simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_range]
    exact ⟨by omega, hp.2.1⟩

/-- LEAF. P0009 page 20, Lemma 22 eq 64, used in the page 40 counting step.
The elementary bound log N over log 2 is at most 2 log N. -/
theorem excluded_primes_le (N : ℕ) (hN : N ≠ 0) :
    (#N.primeFactors : ℝ) ≤ 2 * log N := by
  exact Yamada.card_primeFactors_le_log N hN

/-- LEAF. P0009 pages 39 and 40, the size condition before eq 125.
The lab threshold exp exp 32.155 gives log N at least 40000. -/
theorem log_floor (N : ℕ) (hN : PrintedWiring.X2 ≤ (N : ℝ)) :
    (40000 : ℝ) ≤ log N := by
  have hx : 0 < PrintedWiring.X2 := exp_pos _
  have hlog := Real.log_le_log hx hN
  change log (exp (exp (32155 / 1000))) ≤ log (N : ℝ) at hlog
  rw [log_exp] at hlog
  have hp := Real.pow_div_factorial_le_exp (32 : ℝ) (by norm_num) 5
  norm_num at hp
  have hm : exp (32 : ℝ) ≤ exp (32155 / 1000) := exp_le_exp.mpr (by norm_num)
  linarith

/-- LEAF. P0009 page 40, eq 130 implies the lower bound in eq 125.
The main term gap absorbs the elementary bound for excluded primes. -/
theorem lower_gap (L : ℝ) (hL : 40000 ≤ L) :
    exp L / L + 2 * L ≤ exp L / (L - 1 / 2) := by
  have hL0 : 0 < L := by linarith
  have hLh : 0 < L - 1 / 2 := by linarith
  have h4 := Real.pow_div_factorial_le_exp L hL0.le 4
  norm_num [Nat.factorial] at h4
  have hL3 : 4 * L ^ 3 ≤ exp L := by
    have hm := mul_nonneg (pow_nonneg hL0.le 3) (show 0 ≤ L - 96 by linarith)
    nlinarith
  rw [div_add' _ _ _ hL0.ne', div_le_div_iff₀ hL0 hLh]
  nlinarith

/-- LEAF. P0009 page 40, eq 130 implies the upper bound in eq 125. -/
theorem upper_gap (L : ℝ) (hL : 40000 ≤ L) :
    exp L / (L - 3 / 2) < 1.00005 * exp L / L := by
  have hL0 : 0 < L := by linarith
  have hLh : 0 < L - 3 / 2 := by linarith
  rw [div_lt_div_iff₀ hLh hL0]
  have hg : L < 1.00005 * (L - 3 / 2) := by linarith
  have hm := mul_lt_mul_of_pos_left hg (exp_pos L)
  nlinarith

/-- Lemma 42 eq 125 assembled from an explicit prime counting input.
CONDITIONAL ON hprime. This theorem itself has only the permitted axioms. -/
theorem lemma42_of_bounds
    (hprime : ∀ N : ℕ, (40000 : ℝ) ≤ log N →
      (N : ℝ) / (log N - 1 / 2) < Nat.primeCounting N ∧
        (Nat.primeCounting N : ℝ) < N / (log N - 3 / 2)) :
    PrintedWiring.PrintedLemma42 := by
  intro _ N hpos _ hN
  have hL := log_floor N hN
  have h0 : N ≠ 0 := Nat.ne_of_gt hpos
  have hn : (0 : ℝ) < N := by exact_mod_cast hpos
  have he : exp (log (N : ℝ)) = N := exp_log hn
  obtain ⟨hpLo, hpHi⟩ := hprime N hL
  obtain ⟨hcLo, hcHi⟩ := count_sandwich N h0
  have hcLo' : (Nat.primeCounting N : ℝ) ≤ PrintedWiring.cardA N + #N.primeFactors := by
    exact_mod_cast hcLo
  have hcHi' : (PrintedWiring.cardA N : ℝ) ≤ Nat.primeCounting N := by exact_mod_cast hcHi
  have hw := excluded_primes_le N h0
  have hg := lower_gap (log N) hL
  have hu := upper_gap (log N) hL
  rw [he] at hg hu
  constructor <;> linarith

/-- Concrete count instance from the statement twin. -/
example : PrintedWiring.cardA 6 = 1 := by decide

/-- Concrete prime count instance from the statement twin. -/
example : Nat.primeCounting 6 = 3 := by decide


end LeanLab.ChenExplicit.Decomp94
