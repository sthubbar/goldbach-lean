module

public import Mathlib

/-!
# Glue for the Rényi route: totients of products of distinct primes

Lab proof, unit U-5331, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics.
For a finset `T` of primes, `d = ∏ T` is squarefree with `φ(d) = ∏_{p ∈ T} (p - 1)`; if no `p ∈ T`
divides `N` then `(d, N) = 1`. So Brun's pure sieve with densities `x_p = 1/(p - 1)`,
PNTSieve/BrunPure.lean, has main terms `X/φ(d)`, the form `bvPi` controls, IDEAS I-5051.

* `totient_prod_primes`: `φ(∏ T) = ∏_{p ∈ T} (p - 1)`;
* `coprime_prod_primes`: `(∏ T, N) = 1` when no `p ∈ T` divides `N`;
* `inv_totient_prod_primes`: `1/φ(∏ T) = ∏_{p ∈ T} 1/(p - 1)` in `ℝ`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset

theorem totient_prod_primes (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    (∏ p ∈ T, p).totient = ∏ p ∈ T, (p - 1) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
      have hap : a.Prime := hT a (mem_insert_self a T)
      have hT' : ∀ p ∈ T, p.Prime := fun p hp => hT p (mem_insert_of_mem hp)
      rw [prod_insert ha, prod_insert ha]
      have hcop : Nat.Coprime a (∏ p ∈ T, p) := by
        apply Nat.Coprime.prod_right
        intro p hp
        exact (Nat.coprime_primes hap (hT' p hp)).mpr (fun h => ha (h ▸ hp))
      rw [Nat.totient_mul hcop, Nat.totient_prime hap, ih hT']

theorem coprime_prod_primes (T : Finset ℕ) (N : ℕ) (hT : ∀ p ∈ T, p.Prime ∧ ¬ p ∣ N) :
    Nat.Coprime (∏ p ∈ T, p) N := by
  apply Nat.Coprime.prod_left
  intro p hp
  exact (Nat.Prime.coprime_iff_not_dvd (hT p hp).1).mpr (hT p hp).2

theorem inv_totient_prod_primes (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    (1 : ℝ) / ((∏ p ∈ T, p).totient : ℝ) = ∏ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1) := by
  rw [totient_prod_primes T hT, Nat.cast_prod, one_div, ← prod_inv_distrib]
  refine prod_congr rfl (fun p hp => ?_)
  rw [Nat.cast_sub (hT p hp).one_le, Nat.cast_one, one_div]

end LeanLab.PNTPort.BVMax

