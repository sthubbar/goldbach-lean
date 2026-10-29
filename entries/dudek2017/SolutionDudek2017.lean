module

public import LeanLab.AlmostPrimes.U1504DudekAll

/-!
# Proof of the Dudek 2017 entry

The three compared theorems are proved in the lab files under `LeanLab/`.

* `U1504DudekAll.dudek_all_ap12` splits the range. For `N ≤ 10⁹` it uses the kernel check
  `U1497DudekAll.sqf_upTo_1e9_split`; for even `N > 10⁹` the lab's analytic
  `DudekFrom1e9.dudek_even_from_1e9`; for odd `N > 10⁹` `U1504DudekOdd12.dudek_odd_from_1e9_ap12`,
  which takes `AP12Lower 0.21` as its hypothesis.
* For odd `N` the prime `p` is taken in a class `a mod 12` with `a ≡ N + 2 mod 4` and
  `a ≢ 0, N mod 3`, so neither `4` nor `9` divides `N - p`. The primes `p` with `r² ∣ N - p` for a
  prime `5 ≤ r ≤ 17` lie in one class mod `12r²` and are counted by a Brun-Titchmarsh bound proved
  in the lab from Montgomery's large sieve, `LeanLab/PNTPort/LargeSieve/`; those with `r ≥ 19` by
  `U1445DudekOdd.bad_sum_ge19`. The total is below `0.21 N / log N`.
* For even `N ≥ 10⁹`, `DudekFrom1e9.lean` bounds the primes in the classes `N mod r²` for odd
  primes `r` the same way and compares with an explicit Chebyshev bound,
  `LeanLab/ChebyshevExplicit/Psi30.lean`.
* `3 ≤ N ≤ 10⁹`: `LeanLab/Verifications/U1497Split/`. Each of 1011 windows checks with
  `decide +kernel`, on bit vectors, that every `N` in its range is `q + m` with `q` among the first
  16 primes and `m` square-free. The windows sit in 102 modules `W1` to `W102` that import only
  the core only checker `Core.lean`, not Mathlib; `Bridge.lean` proves the core definitions equal
  to the Mathlib ones of `U1437Fast/Sieve.lean`, and `C1` to `C11` and `Chain.lean` join the
  windows to `SqfUpTo (10^9)`.
* `U1497DudekAll.dudek_even_split` is the even case from the same pieces, with no hypothesis, and
  `U1504DudekOdd12.ap12Lower_of_bmor` derives `AP12Lower 0.21` from `BMORCor16`.

Binary Goldbach is open. AI wrote the Lean code, Claude, Anthropic; it was checked by the Lean
kernel.
-/
