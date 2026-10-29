module

public import LeanLab.AlmostPrimes.U1445DudekOdd
public import LeanLab.AlmostPrimes.U1437DudekFast

/-!
# Dudek 2017, the odd half wired into `DudekOddFrom`, U-1445, run 20261021T2003Z-599

AI wrote the Lean code. KNOWN mathematics, Dudek 2017 Theorem 1. Goldbach is OPEN.
This module does not import the square-free window chain `Verifications/U1437Fast/Chain`.

* `dudekOddFrom_1e9`: `DudekOddFrom (10^9)`, CONDITIONAL ON `BMORCor16`.
* `dudek_all_of_sqf_bmor`: every `N > 2` is a prime plus a positive square-free number, CONDITIONAL
  ON `BMORCor16` and given the finite check `SqfUpTo (10^9)`.
-/

@[expose] public section


namespace LeanLab.AlmostPrimes.U1445DudekAllOdd

open LeanLab.AlmostPrimes.U1445DudekOdd LeanLab.AlmostPrimes.U1437DudekFast
open LeanLab.Verifications.U1437Fast

/-- **`DudekOddFrom (10^9)`, CONDITIONAL ON `BMORCor16`.** -/
theorem dudekOddFrom_1e9 (hB : BMORCor16) : DudekOddFrom (10 ^ 9) :=
  fun N hO hN => dudek_odd_from_1e9 hB N hO hN

/-- **Dudek 2017 Theorem 1 from the finite check, CONDITIONAL ON `BMORCor16`.** -/
theorem dudek_all_of_sqf_bmor (h : SqfUpTo (10 ^ 9)) (hB : BMORCor16) :
    ∀ N : ℕ, 2 < N → ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) :=
  dudek_all_of_sqf h (dudekOddFrom_1e9 hB)

end LeanLab.AlmostPrimes.U1445DudekAllOdd
