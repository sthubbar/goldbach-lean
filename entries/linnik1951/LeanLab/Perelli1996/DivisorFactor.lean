module

public import LeanLab.Perelli1996.Section3

/-!
P0083, page 488. The finite Euler product for the arithmetic factor.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Section3
open Finset

/-- The divisor sum of f is its finite Euler product, including nonsquarefree n. -/
theorem sum_arithmeticFactor (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, arithmeticFactor d =
      ∏ p ∈ n.primeFactors, (1 + arithmeticFactor p) := by
  let af : ArithmeticFunction ℝ := ⟨arithmeticFactor, arithmeticFactor_even (dvd_zero 2)⟩
  have haf : af.IsMultiplicative :=
    ⟨arithmeticFactor_one, fun {m n} h => arithmeticFactor_mul h⟩
  let g : ArithmeticFunction ℝ := af * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hg : g.IsMultiplicative := haf.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  have hgval (k : ℕ) : g k = ∑ d ∈ k.divisors, arithmeticFactor d := by
    exact ArithmeticFunction.coe_mul_zeta_apply
  have hzero (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) : arithmeticFactor (p ^ k) = 0 := by
    apply arithmeticFactor_nonsquarefree
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
    simp only [not_and]
    intro _
    omega
  have hprime (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k) :
      ∑ j ∈ range (k + 1), arithmeticFactor (p ^ j) = 1 + arithmeticFactor p := by
    induction k, hk using Nat.le_induction with
    | base => simp [Finset.sum_range_succ, arithmeticFactor_one]
    | succ k hk ih =>
      rw [Finset.sum_range_succ, ih, hzero p (k + 1) hp (by omega), add_zero]
  have hall : ∀ k : ℕ, k ≠ 0 →
      ∑ d ∈ k.divisors, arithmeticFactor d =
        ∏ p ∈ k.primeFactors, (1 + arithmeticFactor p) := by
    intro k
    induction k using Nat.recOnPosPrimePosCoprime with
    | zero => intro h; exact (h rfl).elim
    | one => intro _; simp [arithmeticFactor_one]
    | prime_pow p k hp hk =>
      intro _
      rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton,
        Nat.sum_divisors_prime_pow hp]
      exact hprime p hp k hk
    | coprime a b ha hb hab ia ib =>
      intro _
      rw [← hgval, hg.map_mul_of_coprime hab, hgval, hgval,
        ia (by omega), ib (by omega), hab.primeFactors_mul,
        Finset.prod_union hab.disjoint_primeFactors]
  exact hall n hn

end LeanLab.Perelli1996.Section3
