module

public import LeanLab.HardyLittlewood1923.TheoremBAll
public import LeanLab.HardyLittlewood1923.TheoremBUnlike
public import LeanLab.HardyLittlewood1923.TheoremB34
public import LeanLab.HardyLittlewood1923.TheoremC
public import LeanLab.HardyLittlewood1923.TheoremD
public import LeanLab.HardyLittlewood1923.TheoremE
public import LeanLab.HardyLittlewood1923.TheoremEAssigned
public import LeanLab.HardyLittlewood1923.TheoremF
public import LeanLab.HardyLittlewood1923.U1503Endpoint
public import LeanLab.Verifications.U1574HLVerify

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
from PrimeNumberTheoremAnd, Apache 2.0, see `PORTING.md`. Theorem A, (3.113), is
`LeanLab.HardyLittlewood1923.U1503.printedA_form_all_U1503_closed`, on the paper's Hypothesis R at
level `Θ` for `47/64 ≤ Θ < 3/4`: from the zero-free half plane the lab proves a bound for
`ψ(x, χ)` by a smoothed explicit formula, `U1503Explicit` with `U1503Contour`, `U1503LogDeriv`
and `U1503Mellin`, feeds it into the major arcs of the circle method for `r = 3`, `U1453PrintedA3`
and `U1503Endpoint`, and lifts to every `r ≥ 3` by the recursion of Theorem B with the singular
series identities of `U1463ThmA` and `U1468SingR`. The derived results on Theorem A are in
`LeanLab/Verifications/U1574HLVerify.lean`. An AI agent, Claude by Anthropic, wrote
the Lean code; it was checked by the Lean kernel. Binary Goldbach is open.
-/
