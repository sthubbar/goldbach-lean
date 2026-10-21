module

public import LeanLab.SchnirelmannGoldbach.Statements
public import LeanLab.PNTSieve.MertensUpper

/-!
# Romanov's theorem, step 1: `singProd n ≤ e^13 log y` when `n` has at most `y` prime factors

Lab proof, unit U-5601, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics,
Romanov 1934 and Erdős 1950 for the method. Binary Goldbach is OPEN; this is the Linnik-Goldbach
line, IDEAS I-5052.

`singProd n = ∏_{p ∣ n} (1 + 1/p)`, the factor of the lab's uniform Brun bound
`BrunGap.gapUpper_uniform`.

* `singProd_eq_sum`: `singProd n = Σ_{s ⊆ primeFactors n} ∏_{p ∈ s} 1/p`.
* `two_pow_card_le`: `2^ω(n) ≤ n` for `n ≠ 0`.
* `singProd_le_log`: `singProd n ≤ e^13 log y` when `ω(n) ≤ y` and `y ≥ 2`, from the lab's
  `Σ_{p ≤ y} 1/p ≤ log log y + 12`.
-/

@[expose] public section


namespace LeanLab.Romanov

open Finset Real
open LeanLab.SchnirelmannGoldbach (singProd)

/-- The weight `w(s) = ∏_{p ∈ s} 1/p` of a finite set of primes. -/
noncomputable def w (s : Finset ℕ) : ℝ := ∏ p ∈ s, (1 / (p : ℝ))

lemma w_nonneg (s : Finset ℕ) : 0 ≤ w s := prod_nonneg fun _ _ => by positivity

theorem singProd_eq_sum (n : ℕ) : singProd n = ∑ s ∈ n.primeFactors.powerset, w s := by
  unfold singProd w
  exact prod_one_add _

theorem two_pow_card_le (n : ℕ) (hn : n ≠ 0) : 2 ^ n.primeFactors.card ≤ n := by
  calc 2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by rw [prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, p :=
        prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

theorem singProd_le_log (n y : ℕ) (hy : 2 ≤ y) (hω : n.primeFactors.card ≤ y) :
    singProd n ≤ exp 13 * log y := by
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hly : 0 < log (y : ℝ) := log_pos (by linarith)
  -- `1 + t ≤ e^t`
  have h1 : singProd n ≤ exp (∑ p ∈ n.primeFactors, (1 / (p : ℝ))) := by
    unfold singProd
    rw [exp_sum]
    gcongr with p hp
    · have := add_one_le_exp (1 / (p : ℝ))
      linarith
  -- split the primes at `y`
  set A := n.primeFactors.filter (fun p => p ≤ y)
  set B := n.primeFactors.filter (fun p => ¬ p ≤ y)
  have hsplit := sum_filter_add_sum_filter_not n.primeFactors (fun p => p ≤ y)
    (fun p => (1 / (p : ℝ)))
  have hA : ∑ p ∈ A, (1 / (p : ℝ)) ≤ log (log y) + 12 := by
    refine le_trans ?_ (LeanLab.PNTSieve.Mertens.sum_inv_primes_le y hy)
    refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    intro p hp
    simp only [A, mem_filter, Nat.mem_primeFactors] at hp
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨hp.1.1.one_lt.le, hp.2⟩, hp.1.1⟩
  have hB : ∑ p ∈ B, (1 / (p : ℝ)) ≤ 1 := by
    calc ∑ p ∈ B, (1 / (p : ℝ)) ≤ ∑ _p ∈ B, (1 / (y : ℝ)) := by
          refine sum_le_sum fun p hp => ?_
          simp only [B, mem_filter, not_le] at hp
          have : (y : ℝ) < p := by exact_mod_cast hp.2
          exact one_div_le_one_div_of_le (by linarith) this.le
      _ = B.card / (y : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 := by
          rw [div_le_one (by linarith)]
          have : B.card ≤ y := le_trans (card_filter_le _ _) hω
          exact_mod_cast this
  have hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) ≤ log (log y) + 13 := by
    rw [← hsplit]; linarith
  calc singProd n ≤ exp (∑ p ∈ n.primeFactors, (1 / (p : ℝ))) := h1
    _ ≤ exp (log (log y) + 13) := exp_le_exp.2 hsum
    _ = exp 13 * log y := by rw [exp_add, exp_log hly]; ring

end LeanLab.Romanov
