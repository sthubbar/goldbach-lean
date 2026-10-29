module

public import LeanLab.AlmostPrimes.U1437DudekFast
public import LeanLab.AlmostPrimes.U1445DudekAllOdd
public import LeanLab.Verifications.U1497Split.Chain

/-!
# Dudek 2017 with the split square-free window chain, U-1497, run 20261022T2003Z-18, I-5067

Same statements as `U1437DudekAll.dudek_even_fast` and `U1445DudekAll.dudek_all_bmor`, with the
102 wide Mathlib window modules of `Verifications/U1437Fast` replaced by the narrow core only
window modules of `Verifications/U1497Split`, so no window module imports Mathlib.

* `sqf_upTo_1e9_split`: every `N` with `3 ≤ N ≤ 10⁹` is `p + (N - p)`, `N - p` square-free. PROVED.
* `dudek_even_split`: every even `N ≥ 4` is a prime plus a positive square-free number. PROVED.
* `dudek_all_bmor_split`: every `N > 2`, CONDITIONAL ON `BMORCor16`.
AI wrote the Lean code. KNOWN mathematics. Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.AlmostPrimes.U1497DudekAll

open LeanLab.AlmostPrimes.U1437DudekFast LeanLab.Verifications.U1437Fast
open LeanLab.AlmostPrimes.U1445DudekOdd

/-- Every `N` with `3 ≤ N ≤ 10⁹` is `p + (N - p)`, `p < N` prime, `N - p` square-free. PROVED. -/
theorem sqf_upTo_1e9_split : SqfUpTo (10 ^ 9) :=
  sqf_mono LeanLab.Verifications.U1497Split.sqfUpTo_end (by norm_num)

/-- **Every even `N ≥ 4` is a prime plus a positive square-free number. PROVED, no cited input.**
The statement of `U1437DudekAll.dudek_even_fast`, verbatim. -/
theorem dudek_even_split (N : ℕ) (hE : Even N) (h4 : 4 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m :=
  dudek_even_of_sqf sqf_upTo_1e9_split N hE h4

/-- **Dudek 2017 Theorem 1, every `N > 2`, CONDITIONAL ON `BMORCor16`.**
The statement of `U1445DudekAll.dudek_all_bmor`, verbatim. -/
theorem dudek_all_bmor_split (hB : BMORCor16) :
    ∀ N : ℕ, 2 < N → ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) :=
  LeanLab.AlmostPrimes.U1445DudekAllOdd.dudek_all_of_sqf_bmor sqf_upTo_1e9_split hB

end LeanLab.AlmostPrimes.U1497DudekAll
