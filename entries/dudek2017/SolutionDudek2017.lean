module

public import LeanLab.AlmostPrimes.U1437DudekAll

/-!
# Proof of the Dudek 2017 entry, the even case only

`dudek_even` is `LeanLab.AlmostPrimes.U1437DudekAll.dudek_even_fast`. The proof splits the range.

* `N ≥ 10⁹`: `LeanLab/AlmostPrimes/DudekFrom1e9.lean`, `dudek_even_from_1e9`. If `N - p` is not
  square-free for every prime `p ≤ N`, each such `p` lies in a class `N mod r²` for an odd prime
  `r`. The classes with `r ≤ 80⌈log N⌉` are counted with a Brun-Titchmarsh bound for primes in
  progressions, proved in the lab from Montgomery's large sieve, `LeanLab/PNTPort/LargeSieve/`;
  the rest are at most `Σ ⌊N/n²⌋`. The total is below `0.906 N / log N`, less than the number
  of primes up to `N` by an explicit Chebyshev bound, `LeanLab/ChebyshevExplicit/Psi30.lean`.
* `4 ≤ N ≤ 10⁹`: a kernel computation, `LeanLab/Verifications/U1437Fast/`. Each of 102 windows
  checks with `decide +kernel`, on bit vectors, that every `N` in its range is `q + m` with `q`
  among the first 16 primes and `m` square-free; `Chain.lean` joins the windows to
  `SqfUpTo (10^9)`. The windows use `decide +kernel` only, so the Lean kernel itself evaluates them.

The odd case of Dudek's Theorem 1 is not proved here. Binary Goldbach is open. AI wrote the Lean
code, Claude, Anthropic; it was checked by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.Dudek2017

/-- **Dudek 2017, Theorem 1, even case**: every even `N ≥ 4` is the sum of a prime `p` and a
square-free number `m ≥ 1`. -/
theorem dudek_even : ∀ N : ℕ, Even N → 4 ≤ N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m :=
  fun N hE h4 => LeanLab.AlmostPrimes.U1437DudekAll.dudek_even_fast N hE h4

end LeanLab.Dudek2017
