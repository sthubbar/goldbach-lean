module

public import LeanLab.AlmostPrimes.U1504DudekOdd12
public import LeanLab.AlmostPrimes.U1497DudekAll

/-!
# Dudek 2017 Theorem 1 from one modulus, U-1504, run 20261023T1343Z-19109, I-5067

AI wrote the Lean code. KNOWN mathematics, Dudek 2017 Theorem 1, arXiv 1410.7459. Goldbach is OPEN.

* `dudekOddFrom_1e9_ap12`: `DudekOddFrom (10^9)`, CONDITIONAL ON `AP12Lower 0.21` only.
* `dudek_all_ap12`: every `N > 2` is `p + (N - p)`, `p < N` prime, `N - p` square-free,
  CONDITIONAL ON `AP12Lower 0.21` only; the finite part is `U1497DudekAll.sqf_upTo_1e9_split`,
  PROVED, and the even half is unconditional.
* `dudek_all_ap12_pm`: the same in the form `N = p + m`, `m ≥ 1` square-free.
-/

@[expose] public section


namespace LeanLab.AlmostPrimes.U1504DudekAll

open LeanLab.AlmostPrimes.U1504DudekOdd12 LeanLab.AlmostPrimes.U1437DudekFast

/-- **`DudekOddFrom (10^9)`, CONDITIONAL ON `AP12Lower 0.21`.** -/
theorem dudekOddFrom_1e9_ap12 (hA : AP12Lower 0.21) : DudekOddFrom (10 ^ 9) :=
  fun N hO hN => dudek_odd_from_1e9_ap12 hA N hO hN

/-- **Dudek 2017 Theorem 1, every `N > 2`, CONDITIONAL ON `AP12Lower 0.21`.** The statement of
`U1497DudekAll.dudek_all_bmor_split` with `BMORCor16` replaced by the weaker `AP12Lower 0.21`. -/
theorem dudek_all_ap12 (hA : AP12Lower 0.21) :
    ∀ N : ℕ, 2 < N → ∃ p, p.Prime ∧ p < N ∧ Squarefree (N - p) :=
  dudek_all_of_sqf LeanLab.AlmostPrimes.U1497DudekAll.sqf_upTo_1e9_split (dudekOddFrom_1e9_ap12 hA)

/-- **The same, as `N = p + m` with `m ≥ 1` square-free, CONDITIONAL ON `AP12Lower 0.21`.** -/
theorem dudek_all_ap12_pm (hA : AP12Lower 0.21) (N : ℕ) (h3 : 3 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  rw [← dudekAt_iff]
  exact dudek_all_ap12 hA N (by omega)

end LeanLab.AlmostPrimes.U1504DudekAll
