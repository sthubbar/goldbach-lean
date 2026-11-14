module

public import LeanLab.Linnik.U1466Display17
public import LeanLab.PNTSieve.MertensProduct

/-!
The Mertens product bound `MertensProd` of U-1466, PROVED unconditionally.

`MertensProd`: there is `C` with `∏_{2 < p ≤ n}(p-1)/(p-2) ≤ C log n` for all `n ≥ 2`.

Route.
1. `(p-1)/(p-2) = 1 + 1/(p-2) ≤ exp(1/(p-2))`, so the product is at most `exp(∑ 1/(p-2))`.
2. `1/(p-2) ≤ 1/p + 6/p²` for `p ≥ 3`.
3. `∑_{p ≤ n} 1/p ≤ log log n + 12`, the lab's `LeanLab.PNTSieve.Mertens.sum_inv_primes_le`,
   PROVED there unconditionally from Legendre's formula, Stirling and Mathlib's Chebyshev bound
   `θ(x) ≤ x log 4`, by discrete Abel summation; its axioms are only the standard three, checked
   in this unit. It does not use the Dusart-conditional AlmostPrimes Mertens files.
4. `∑_{n ≤ N} 1/n² ≤ 2`, the lab's `LeanLab.PNTSieve.Mertens.sum_inv_sq_le_two`.
Hence the product is at most `exp(log log n + 24) = e^{24} log n`. The constant is crude.

Contents.
* `ratio_le_exp`, `inv_sub_two_le`: steps 1 and 2, PROVED.
* `oddPrimes_prod_le`: `∏_{2 < p ≤ n}(p-1)/(p-2) ≤ e^{24} log n` for `n ≥ 2`, PROVED.
* `mertensProd`: `U1466Display17.MertensProd`, PROVED unconditionally.
* `display17_of'`: `Display17` CONDITIONAL ON `R0Summable` only.
* `r6_lower9`: `r6_lower8` with `MertensProd` discharged.

Unit U-1469, run 20261022T0403Z-7595. AI-written Lean code, Claude. KNOWN mathematics, Mertens
1874 in a weak form. Nothing here is progress on Goldbach; binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Linnik.U1469Mertens

open Set Real Filter Finset Topology
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U7200Minor35
open LeanLab.Linnik.U1429Display58
open LeanLab.Linnik.U7203Display33
open LeanLab.Linnik.U7205Display34
open LeanLab.Linnik.U1447Display30
open LeanLab.Linnik.U1458Lemma42
open LeanLab.Linnik.U1464Display20
open LeanLab.Linnik.U1466Display17

/-- Step 1: for `p > 2`, `(p-1)/(p-2) ≤ exp(1/(p-2))`. -/
lemma ratio_le_exp {x : ℝ} (hx : 2 < x) : (x - 1) / (x - 2) ≤ Real.exp (1 / (x - 2)) := by
  have h : (x - 1) / (x - 2) = 1 / (x - 2) + 1 := by
    field_simp [show x - 2 ≠ 0 by linarith]
    ring
  rw [h]
  exact Real.add_one_le_exp _

/-- Step 2: for `p ≥ 3`, `1/(p-2) ≤ 1/p + 6/p²`. -/
lemma inv_sub_two_le {x : ℝ} (hx : 3 ≤ x) : 1 / (x - 2) ≤ 1 / x + 6 * (1 / x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hx2 : 0 < x - 2 := by linarith
  rw [div_le_iff₀ hx2]
  have e : (1 / x + 6 * (1 / x ^ 2)) * (x - 2) = 1 + (4 * x - 12) / x ^ 2 := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ (4 * x - 12) / x ^ 2 := div_nonneg (by linarith) (by positivity)
  linarith

lemma oddPrimes_sub_primes (n : ℕ) :
    oddPrimesUpTo n ⊆ (Finset.Icc 1 n).filter Nat.Prime := by
  intro p hp
  simp only [oddPrimesUpTo, Finset.mem_filter, Finset.mem_range] at hp
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hp.2.1.one_lt.le, by omega⟩, hp.2.1⟩

lemma oddPrimes_sub_Icc (n : ℕ) : oddPrimesUpTo n ⊆ Finset.Icc 1 n :=
  (oddPrimes_sub_primes n).trans (Finset.filter_subset _ _)

/-- `∑_{2 < p ≤ n} 1/(p-2) ≤ log log n + 24` for `n ≥ 2`. -/
lemma sum_inv_sub_two_le (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ oddPrimesUpTo n, 1 / ((p : ℝ) - 2) ≤ Real.log (Real.log n) + 24 := by
  have h3 : ∀ p ∈ oddPrimesUpTo n, (3 : ℝ) ≤ p := by
    intro p hp
    simp only [oddPrimesUpTo, Finset.mem_filter] at hp
    exact_mod_cast hp.2.2
  have h1 : ∑ p ∈ oddPrimesUpTo n, 1 / ((p : ℝ) - 2) ≤
      ∑ p ∈ oddPrimesUpTo n, (1 / (p : ℝ)) + 6 * ∑ p ∈ oddPrimesUpTo n, 1 / (p : ℝ) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p hp => inv_sub_two_le (h3 p hp)
  have h2 : ∑ p ∈ oddPrimesUpTo n, (1 / (p : ℝ)) ≤ Real.log (Real.log n) + 12 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (oddPrimes_sub_primes n)
      (fun p _ _ => by positivity)).trans (LeanLab.PNTSieve.Mertens.sum_inv_primes_le n hn)
  have h4 : ∑ p ∈ oddPrimesUpTo n, 1 / (p : ℝ) ^ 2 ≤ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (oddPrimes_sub_Icc n)
      (fun p _ _ => by positivity)).trans (LeanLab.PNTSieve.Mertens.sum_inv_sq_le_two n)
  linarith

/-- **The Mertens product bound, PROVED**: `∏_{2 < p ≤ n}(p-1)/(p-2) ≤ e^{24} log n`, `n ≥ 2`. -/
theorem oddPrimes_prod_le (n : ℕ) (hn : 2 ≤ n) :
    ∏ p ∈ oddPrimesUpTo n, ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ Real.exp 24 * Real.log n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  have h2 : ∀ p ∈ oddPrimesUpTo n, (2 : ℝ) < p := by
    intro p hp
    simp only [oddPrimesUpTo, Finset.mem_filter] at hp
    exact_mod_cast hp.2.2
  calc ∏ p ∈ oddPrimesUpTo n, ((p : ℝ) - 1) / ((p : ℝ) - 2)
      ≤ ∏ p ∈ oddPrimesUpTo n, Real.exp (1 / ((p : ℝ) - 2)) :=
        Finset.prod_le_prod₀ (fun p hp => by
            have := h2 p hp; exact div_nonneg (by linarith) (by linarith))
          (fun p hp => ratio_le_exp (h2 p hp))
    _ = Real.exp (∑ p ∈ oddPrimesUpTo n, 1 / ((p : ℝ) - 2)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (Real.log (Real.log n) + 24) := Real.exp_le_exp.mpr (sum_inv_sub_two_le n hn)
    _ = Real.exp 24 * Real.log n := by rw [Real.exp_add, Real.exp_log hL]; ring

/-- **`MertensProd` of U-1466, PROVED unconditionally**, with `C = e^{24}`. -/
theorem mertensProd : MertensProd := ⟨Real.exp 24, oddPrimes_prod_le⟩

/-- **Lemma 3.1, display (17), PROVED, CONDITIONAL ON `R0Summable` only**. -/
theorem display17_of' (hR : R0Summable) : Display17 := display17_of mertensProd hR

/-- **r₆''(N) ≫ N L⁶, CONDITIONAL ON** the cited Lemma 4.1 `Lemma41 κ P ε` for every `ε > 0`,
display (18) `Lemma31_18`, the convergence of `R₀` `R0Summable`, Proposition 3.2
`Prop32 Bdef (A_* + T)`, the cited (31) `Display31 6.7814`, `MinorSup1924 P`, the conditions (24)
on `P` and the cited constants of `k6_wired`. This is `r6_lower8` with `MertensProd` discharged. -/
theorem r6_lower9 {CR A22 A33 : ℝ} (T : Fin 3 → Fin 3 → ℝ) (hCR0 : 0 ≤ CR)
    (hPT : CR < 1.2784421041) (hJT2 : A22 ≤ 0.05549) (hJT3 : A33 ≤ 0.013598)
    (hT : ∀ i j, |T i j| ≤ √(T i i) * √(T j j))
    (hA11 : (LiLiu.Astar 0 0 : ℝ) + T 0 0 = CR - 1) (hA22 : (LiLiu.Astar 1 1 : ℝ) + T 1 1 = A22)
    (hA33 : (LiLiu.Astar 2 2 : ℝ) + T 2 2 = A33) (h31 : Display31 6.7814)
    (h18 : Lemma31_18) (hR : R0Summable)
    (h32 : Prop32 Bdef (fun i j => (LiLiu.Astar i j : ℝ) + T i j)) :
    ∀ {κ : ℝ}, 0 < κ → ∀ P : ℕ → ℝ,
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((11 : ℝ) / 25) ≤ P N) →
      (∀ᶠ N : ℕ in atTop, P N ≤ (N : ℝ) ^ (1 - κ)) →
      (∀ᶠ N : ℕ in atTop, 2 * P N ^ 2 < N) →
      MinorSup1924 P →
      (∀ ε > 0, Lemma41 κ P ε) →
      ∃ c > 0, ∀ᶠ N : ℕ in atTop, Even N →
        c * (N * (Lfun N : ℝ) ^ 6) ≤ r6pp (N1f κ N) N (Lfun N) :=
  r6_lower8 T hCR0 hPT hJT2 hJT3 hT hA11 hA22 hA33 h31 h18 mertensProd hR h32

/-- Vacuity, a nontrivial instance: at `n = 7` the odd primes are `3, 5, 7`. -/
theorem oddPrimes_seven : oddPrimesUpTo 7 = {3, 5, 7} := by decide

end LeanLab.Linnik.U1469Mertens
