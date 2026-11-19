module

public import LeanLab.ExceptionalSet.Decomp1539a

/-!
Theorem 2 of J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, page 354, from the paper's Lemma 10, pages 370 to 371,
which is Theorem 1 of A. A. Karacuba, Estimates for trigonometric sums by Vinogradov's method,
and some applications, Proc. Steklov Inst. Math. 112 (1973) 251-265, as the paper cites it.
Lemma 10 is taken as the explicit named hypothesis `Lemma10DQ5`, never as an axiom, and
`lemma10_named_eq_dq5` shows that it is by definition the statement `Lemma10` of
`State1539Data264`. `theorem2_of_named_dq5` proves Theorem 2 from it through
`theorem2_of_all_leaves` of `Decomp1539a`, the paper's section 8.

This copy keeps only these three declarations of the lab file of design queue item DQ5,
run 20261119T0802Z-29270; see `PORTING.md`. AI agents wrote the Lean code.
Goldbach's problem remains open and is not claimed.
-/

@[expose] public section

namespace LeanLab.ExceptionalSet.U1539

open Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- Named hypothesis, Lemma 10 of Brüdern and Perelli 1998, pages 370 to 371, Karacuba 1973 Theorem 1. -/
def Lemma10DQ5 : Prop :=
  ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ),
      KClass N θ Θ Θ₀ δ f k →
      ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2)

/-- Match: the named hypothesis is definitionally the sealed `Lemma10`. CLEAN. -/
theorem lemma10_named_eq_dq5 : Lemma10DQ5 = Lemma10 := rfl

/-- Theorem 2 of Brüdern and Perelli 1998, page 354, assuming the named hypothesis `Lemma10DQ5`. -/
theorem theorem2_of_named_dq5 (h10 : Lemma10DQ5) : Theorem2 :=
  theorem2_of_all_leaves h10

end LeanLab.ExceptionalSet.U1539
