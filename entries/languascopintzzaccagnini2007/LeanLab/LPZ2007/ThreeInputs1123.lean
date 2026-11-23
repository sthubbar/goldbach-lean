module

public import LeanLab.LPZ2007.Prep1121J131FourInputs
public import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b
public import LeanLab.LanguascoPintzZaccagnini2007.JutilaSrc481
public import LeanLab.LanguascoPintzZaccagnini2007.IwaniecCells1122

/-!
The repaired main theorem of Languasco, Pintz and Zaccagnini 2007 on J of X, Corollary 4.2
there, and the count of even numbers that are not sums of two primes and k powers of two, from
three cited inputs.

`Prep1121J131FourInputs` proves both from four cited inputs. Here the real zero bound
`RealZeroStatement481` is discharged by `real_zero_bound481`, proved from the lab's port of
Siegel's theorem. The Jutila input is taken in the form of Jutila 1977 Theorem 1 display 1.8 as
printed, `JutilaTheorem18_481`, and reduced to `JutilaStatement481` by
`jutilaStatement481_of_theorem18`. The Iwaniec input is taken in the form of Iwaniec 1974
Theorem 2 as printed on page 97, with `l = log q(|t| + 3)`, read for nonreal characters,
`IwaniecTheorem2_1123`, and reduced to `IwaniecStatement481` by
`iwaniecStatement481_of_printed1122`. The Pintz input `Lemma41Statement481` is Lemma 4.1 of
the paper, quoted there from Pintz ELAZ 2004 Theorem 10.
-/

@[expose] public section


namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- Iwaniec, On zeros of Dirichlet's L series, Invent. Math. 23 (1974), page 97, Theorem 2,
read for nonreal characters: for `q ≥ 3`, `d = ∏_{p ∣ q} p`, `l = log q(|t| + 3)` and
`θ⁻¹ = 4·10⁴ (log d + (l log 2l)^{3/4})`, the theorem allows a zero with `Re ρ > 1 - θ` only for
one real character modulo `q`, so `L(s, χ)` has no zero with `Re s > 1 - θ` when `χ` takes a
nonreal value. -/
def IwaniecTheorem2_1123 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ χ : DirichletCharacter ℂ r, (∃ a, (χ a).im ≠ 0) → ∀ s : ℂ,
    1 - 1 / (4 * 10 ^ 4 * (Real.log ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) +
      (Real.log ((r : ℝ) * (|s.im| + 3)) *
        Real.log (2 * Real.log ((r : ℝ) * (|s.im| + 3)))) ^ (3 / 4 : ℝ))) < s.re →
    Lfun481 χ s ≠ 0

/-- Languasco, Pintz and Zaccagnini 2007, Corollary 4.2 on the even numbers of J of X,
from the Pintz explicit formula, Jutila's density theorem and Iwaniec's zero free region. -/
theorem cor42_of_three_inputs (hexp : Lemma41Statement481) (hjut : JutilaTheorem18_481)
    (hiw : IwaniecTheorem2_1123) : Cor42OnWindow131 evenJ131 :=
  cor42_of_four_inputs1121 hexp (jutilaStatement481_of_theorem18 hjut) real_zero_bound481
    (iwaniecStatement481_of_printed1122 hiw)

/-- Languasco, Pintz and Zaccagnini 2007, the main theorem on the even numbers of J of X with
the corrected coefficient of display 25, from the same three cited inputs. -/
theorem repaired_mainJ131_of_three_inputs (hexp : Lemma41Statement481)
    (hjut : JutilaTheorem18_481) (hiw : IwaniecTheorem2_1123) : RepairedMainJ131 :=
  repaired_main_cor42_supply383 (cor42_of_three_inputs hexp hjut hiw)

/-- Languasco, Pintz and Zaccagnini 2007, the consequence of the Theorem for sums of two primes
and `k` powers of two: for `k ≥ 1`, all but `O(X^{3/5} (log X)^{10})` even `N ≤ X` are `p₁ + p₂ + 2^{ν₁} + … + 2^{ν_k}`
with `ν_i ∈ [1, log₂ X]`, from the same three cited inputs. -/
theorem global_primes_of_three_inputs (hexp : Lemma41Statement481)
    (hjut : JutilaTheorem18_481) (hiw : IwaniecTheorem2_1123) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (allPrimeExceptions131 k X).card ≤ C * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 :=
  global_primes_cor42_supply383 (cor42_of_three_inputs hexp hjut hiw) k hk

end

end LeanLab.LPZ2007
