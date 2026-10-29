module

public import LeanLab.AlmostPrimes.U1437DudekFast
public import LeanLab.Verifications.U1437Fast.Chain

/-!
# Dudek 2017, the even case, with the square-free window chain, U-1437, I-5067

`dudek_even_fast`: every even `N ≥ 4` is a prime plus a positive square-free number, PROVED, no
cited input, with the 102 square-free windows of `Verifications/U1437Fast`. `sqf_upTo_1e9`:
every `N` with `3 ≤ N ≤ 10⁹`, odd or even, PROVED. The odd case of Dudek's theorem for
`N > 10⁹` is not proved. AI wrote the Lean code. KNOWN mathematics. Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.AlmostPrimes.U1437DudekAll

open LeanLab.AlmostPrimes.U1437DudekFast LeanLab.Verifications.U1437Fast

/-- Every `N` with `3 ≤ N ≤ 10⁹` is `p + (N - p)`, `p < N` prime, `N - p` square-free. PROVED. -/
theorem sqf_upTo_1e9 : SqfUpTo (10 ^ 9) := sqf_mono sqfUpTo_end (by norm_num)

/-- **Every even `N ≥ 4` is a prime plus a positive square-free number. PROVED, no cited input.** -/
theorem dudek_even_fast (N : ℕ) (hE : Even N) (h4 : 4 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m :=
  dudek_even_of_sqf sqf_upTo_1e9 N hE h4

end LeanLab.AlmostPrimes.U1437DudekAll

