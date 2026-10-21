module

public import LeanLab.HardyLittlewood1923.TheoremBAll
public import LeanLab.HardyLittlewood1923.TheoremBUnlike
public import LeanLab.HardyLittlewood1923.TheoremB34
public import LeanLab.HardyLittlewood1923.TheoremC
public import LeanLab.HardyLittlewood1923.TheoremD
public import LeanLab.HardyLittlewood1923.TheoremE
public import LeanLab.HardyLittlewood1923.TheoremEAssigned
public import LeanLab.HardyLittlewood1923.TheoremF

/-!
# Proof of the Hardy-Littlewood 1923 entry

The compared theorems live in `LeanLab/HardyLittlewood1923/`, with no hypothesis where Hardy and
Littlewood assumed Hypothesis R. Theorem D, the ternary asymptotic, comes from
`LeanLab.VanDerCorput1939.vinogradov1`, the lab's unconditional circle method for three primes,
with Vinogradov's minor arc estimate and the Siegel-Walfisz theorem,
`LeanLab/PNTPort/Vinogradov/` and `LeanLab/PNTPort/PsiChi/`. Theorem C follows from a lower bound
for `N_r(n)` by induction on `r` from the ternary lower bound. Theorem E combines Theorem D with
the prime number theorem in progressions and a divisor expansion of the singular series. Theorem B
for every `r ≥ 3` is an induction on `r` from the case `r = 3`, with Siegel-Walfisz for each fixed
modulus and a Brun-Titchmarsh bound for the tail. Theorem F is Hardy and Littlewood's averaging
argument, with the prime number theorem. Parts of the analytic number theory of ζ(s) are ported
from PrimeNumberTheoremAnd, Apache 2.0, see `PORTING.md`. An AI agent, Claude by Anthropic, wrote
the Lean code; it was checked by the Lean kernel. Binary Goldbach is open.
-/
