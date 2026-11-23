module

public import LeanLab.LanguascoPintzZaccagnini2007.Decomp383a
public import LeanLab.LanguascoPintzZaccagnini2007.Audit1619

/-!
The arithmetic supply closes the second input of the existing two parameter route.
The remaining input is the printed Corollary 4.2 on J of X.
Every theorem here is CONDITIONAL on that explicit cited input.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real

/-- CONDITIONAL on printed Corollary 4.2 only. Journal page 778 Section 5.
The proved arithmetic supply removes the singular average input of U1619. -/
theorem repaired_main_cor42_supply383 (hcor : Cor42OnWindow131 evenJ131) : RepairedMainJ131 :=
  route_of_leaves1619 hcor major_arcs_combine_supply383

/-- CONDITIONAL on printed Corollary 4.2 only. The local prime existence
consequence of the repaired theorem on journal pages 772 and 778. -/
theorem local_primes_cor42_supply383 (hcor : Cor42OnWindow131 evenJ131) (k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((evenJ131 X).filter (fun N => primeRepresentationCount131 k X N = 0)).card : ℝ) ≤
        K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 :=
  almost_all_primes_of_repaired131 (repaired_main_cor42_supply383 hcor) k hk

/-- CONDITIONAL on printed Corollary 4.2 only. The prime existence conclusion
on the full interval follows by the paper covering argument on journal page 772. -/
theorem global_primes_cor42_supply383 (hcor : Cor42OnWindow131 evenJ131) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (allPrimeExceptions131 k X).card ≤ C * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 :=
  almost_all_primes_global_of_repaired131 (repaired_main_cor42_supply383 hcor) k hk

end LeanLab.LPZ2007

