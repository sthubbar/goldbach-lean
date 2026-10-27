module

public import LeanLab.Routes.U1508Compose445

/-!
# Proof of the Goldbach numbers in intervals of length 4.45 log² x entry, CONDITIONAL

`LeanLab/Routes/U1508Compose445.lean` proves `goldbach_445_hsw_gZ`: under the Riemann
Hypothesis, for every real `x ≥ 3` there is a Goldbach number `n`, a sum of two odd primes, with
`x < n < x + 4.45 (log x)²`, CONDITIONAL ON cited inputs taken as explicit hypotheses, never as
axioms: the truncated explicit formula `ExplicitA`, Montgomery-Vaughan (12.1); the Hadamard
product bound `HadamardK`; `Ordinates14`; the Brent-Platt-Trudgian zero count `BPTN`; the
Hasanalizade-Shen-Wong zero counts `HSWN70` and `HSWHead14`; and `EvenGoldbachUpTo (4 * 10 ^ 18)`,
the computation of Oliveira e Silva, Herzog and Pardi.

Route: Theorem 2 of Chirre and Hagen with the diagonal constant 1.0068,
`ChirreHagen2025.SmoothT2.theorem2_u6806`, from the smoothed mean square of the zero sum and
interval majorants summed by the Brent-Platt-Trudgian counts, then the passage from `ψ` to `θ`
and Section 5 of Chirre and Hagen, `Routes.U1505.goldbach_445_of_J_hsw`.

AI wrote the Lean code, Claude, Anthropic; it was checked by the Lean kernel. Binary Goldbach is
open.
-/
