module

public import LeanLab.Perelli1996.Roots
public import LeanLab.ChenExplicit.Statements

/-!
P0083, pages 479, 488 and 489. The average formula and its arithmetic factor.
The analytic estimates are cited Prop definitions. No theorem asserts them here.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Section3
open Finset Real Polynomial
noncomputable section

/-- The constant singular series on page 479. -/
def singularConstant : ℝ := 2 * LeanLab.ChenExplicit.twinC

/-- The constant C of F on page 479, using integer root representatives. -/
def averageConstant (F : ℤ[X]) : ℝ :=
  (F.leadingCoeff : ℝ) * ((Roots.rootResidues F 2).card : ℝ) / 2 * singularConstant *
    ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
      (1 + ((Roots.rootResidues F p.1).card : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 2)))

/-- Cited Theorem 2, page 479. -/
def Theorem2 (F : ℤ[X]) : Prop :=
  Admissible F → ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N₀ : ℝ,
    ∀ N H : ℝ, N₀ ≤ N → N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      |(∑ n ∈ win F N H, R (Fv F n).toNat) - averageConstant F * H * N| ≤
        C * H * N * Real.log N ^ (-A)

/-- The arithmetic factor f defined on page 488. -/
def arithmeticFactor (n : ℕ) : ℝ :=
  if n = 1 then 1 else if 2 ∣ n then 0 else
    (ArithmeticFunction.moebius n : ℝ) ^ 2 *
      ∏ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2)

/-- Cited average singular series estimate, page 489, equation 37. -/
def SingularAverage (F : ℤ[X]) : Prop :=
  Admissible F → ∀ ε : ℝ, 0 < ε → ∃ C N₀ : ℝ, ∀ N H : ℝ,
    N₀ ≤ N → 0 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
    |(∑ n ∈ win F N H, Sing (Fv F n).toNat) -
      ((Roots.rootResidues F 2).card : ℝ) / 2 * H * singularConstant *
        ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
          (1 + ((Roots.rootResidues F p.1).card : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 2)))| ≤
      C * N ^ ε

/-- The value at one, page 488. -/
theorem arithmeticFactor_one : arithmeticFactor 1 = 1 := by simp [arithmeticFactor]

/-- Even inputs have zero factor, page 488. -/
theorem arithmeticFactor_even {n : ℕ} (hn : 2 ∣ n) : arithmeticFactor n = 0 := by
  have hn1 : n ≠ 1 := by intro h; simpa [h] using hn
  simp [arithmeticFactor, hn1, hn]

/-- The factor is supported on squarefree integers, page 488. -/
theorem arithmeticFactor_nonsquarefree {n : ℕ} (hn : ¬ Squarefree n) :
    arithmeticFactor n = 0 := by
  have hn1 : n ≠ 1 := by intro h; subst n; exact hn squarefree_one
  simp [arithmeticFactor, hn1, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]

/-- At an odd prime the local factor is one over p minus two, page 488. -/
theorem arithmeticFactor_prime {p : ℕ} (hp : p.Prime) (hodd : 2 < p) :
    arithmeticFactor p = 1 / ((p : ℝ) - 2) := by
  have hnd : ¬ 2 ∣ p := by
    intro h
    have hd := (Nat.dvd_prime hp).mp h
    omega
  simp [arithmeticFactor, hp.ne_one, hnd, ArithmeticFunction.moebius_apply_prime hp,
    hp.primeFactors]

/-- Multiplicativity asserted just after the definition of f on page 488. -/
theorem arithmeticFactor_mul {m n : ℕ} (hcop : Nat.Coprime m n) :
    arithmeticFactor (m * n) = arithmeticFactor m * arithmeticFactor n := by
  by_cases hm : 2 ∣ m
  · rw [arithmeticFactor_even (dvd_trans hm (dvd_mul_right m n)), arithmeticFactor_even hm, zero_mul]
  by_cases hn : 2 ∣ n
  · rw [arithmeticFactor_even (dvd_trans hn (dvd_mul_left n m)), arithmeticFactor_even hn, mul_zero]
  have hmn : ¬ 2 ∣ m * n := by
    intro h
    exact ((Nat.prime_two.dvd_mul).mp h).elim hm hn
  have hform (k : ℕ) (hk : ¬ 2 ∣ k) : arithmeticFactor k =
      (ArithmeticFunction.moebius k : ℝ) ^ 2 *
        ∏ p ∈ k.primeFactors, 1 / ((p : ℝ) - 2) := by
    by_cases hk1 : k = 1
    · subst k; simp [arithmeticFactor]
    · simp [arithmeticFactor, hk1, hk]
  rw [hform (m * n) hmn, hform m hm, hform n hn,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    hcop.primeFactors_mul, Finset.prod_union hcop.disjoint_primeFactors]
  push_cast
  ring

/-- All arithmetic factors are nonnegative, page 488. -/
theorem arithmeticFactor_nonneg (n : ℕ) : 0 ≤ arithmeticFactor n := by
  unfold arithmeticFactor
  split_ifs with hn1 hn2
  · norm_num
  · norm_num
  · refine mul_nonneg (sq_nonneg _) (Finset.prod_nonneg ?_)
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hp3 : 3 ≤ p := by
      have hp2 := hprime.two_le
      have hpne : p ≠ 2 := by intro h; subst p; exact hn2 hdvd
      omega
    have hreal : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    apply div_nonneg (by norm_num)
    linarith

end
end LeanLab.Perelli1996.Section3
