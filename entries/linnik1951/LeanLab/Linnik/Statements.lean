module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.DERZ1997.Statements

/-!
Linnik's approximation to binary Goldbach: two primes plus K powers of 2.
P0093 Linnik 1951, Trudy Mat. Inst. Steklov 38, 152-169, "Prime numbers and powers of two".
P0094 Gallagher 1975, Invent. Math., "Primes and powers of 2", DOI 10.1007/bf01390190.
P0012 Heath-Brown, Puchta 2002, arXiv math/0201299, Theorems 1 and 2.
P0026 Pintz, Ruzsa 2003, Acta Arith. 109, 169-194, Theorem 1.
P0035 Pintz, Ruzsa 2020, real.mtak.hu/124682, abstract.
P0025 Johnston, Trudgian 2026, arXiv 2605.17825v2, abstract.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
Binary Goldbach is OPEN; K = 0 here would be binary Goldbach for large evens.
-/

@[expose] public section

namespace LeanLab.Linnik
open LeanLab.DERZ1997

/-- `N` is two primes plus exactly `K` powers of 2, each exponent at least 1, the
convention of P0012's `T(α) = Σ_{1 ≤ ν ≤ L} e(α 2^ν)`. -/
def LinnikExact (K N : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ ∃ ν : Fin K → ℕ, (∀ i, 1 ≤ ν i) ∧ N = p + q + ∑ i, 2 ^ ν i

/-- Two primes plus at most `K` powers of 2. -/
def LinnikAtMost (K N : ℕ) : Prop := ∃ k, k ≤ K ∧ LinnikExact k N

/-- Every sufficiently large even integer has property `P`. -/
def AllLargeEven (P : ℕ → Prop) : Prop := ∃ N0 : ℕ, ∀ N, Even N → N0 < N → P N

/-! ### Links, no placeholder proof -/

theorem atMost_of_exact {K N : ℕ} (h : LinnikExact K N) : LinnikAtMost K N := ⟨K, le_rfl, h⟩

theorem atMost_mono {K K' N : ℕ} (hK : K ≤ K') (h : LinnikAtMost K N) : LinnikAtMost K' N := by
  obtain ⟨k, hk, h⟩ := h; exact ⟨k, hk.trans hK, h⟩

theorem allLargeEven_mono {P Q : ℕ → Prop} (hPQ : ∀ N, P N → Q N) (h : AllLargeEven P) :
    AllLargeEven Q := by
  obtain ⟨N0, h⟩ := h; exact ⟨N0, fun N he hN => hPQ N (h N he hN)⟩

/-- Pintz-Ruzsa II gives Heath-Brown-Puchta's 13 in the at most form. -/
theorem hbp_atMost_of_pr2 (h : AllLargeEven (LinnikExact 8)) : AllLargeEven (LinnikAtMost 13) :=
  allLargeEven_mono (fun _ hN => atMost_mono (by norm_num) (atMost_of_exact hN)) h

/-- Heath-Brown-Puchta gives Gallagher's existence statement with `K = 13`. -/
theorem gallagher_of_hbp (h : AllLargeEven (LinnikExact 13)) : ∃ K, AllLargeEven (LinnikAtMost K) :=
  ⟨13, allLargeEven_mono (fun _ => atMost_of_exact) h⟩

/-- Pintz-Ruzsa I at `K = 7` is exactly Heath-Brown-Puchta Theorem 2. -/
theorem hbp_GRH_of_pr1 (h : GRH → ∀ K, 7 ≤ K → AllLargeEven (LinnikExact K)) :
    GRH → AllLargeEven (LinnikExact 7) := fun hG => h hG 7 le_rfl

/-- Johnston-Trudgian gives the GRH 7 in the at most form. -/
theorem atMost7_of_jt (h : GRH → AllLargeEven (LinnikExact 6)) :
    GRH → AllLargeEven (LinnikAtMost 7) :=
  fun hG => allLargeEven_mono (fun _ hN => atMost_mono (by norm_num) (atMost_of_exact hN)) (h hG)

/-- Any unconditional result gives Linnik's GRH statement. -/
theorem linnik1951_of_gallagher (h : ∃ K, AllLargeEven (LinnikAtMost K)) :
    GRH → ∃ K, AllLargeEven (LinnikAtMost K) := fun _ => h

/-! ### The papers, cited, with placeholder proofs, removed in this copy -/

/-- Binary Goldbach is the case `K = 0`. -/
theorem exact_zero_iff (N : ℕ) : LinnikExact 0 N ↔ IsGoldbachSum N := by
  constructor
  · rintro ⟨p, q, hp, hq, ν, -, hN⟩
    exact ⟨p, q, hp, hq, by simpa using hN.symm⟩
  · rintro ⟨p, q, hp, hq, h⟩
    exact ⟨p, q, hp, hq, Fin.elim0, fun i => i.elim0, by simp [h]⟩

/-- Not vacuous: `8 = 3 + 3 + 2^1`. -/
example : LinnikExact 1 8 :=
  ⟨3, 3, Nat.prime_three, Nat.prime_three, fun _ => 1, fun _ => le_rfl, by simp⟩

end LeanLab.Linnik
