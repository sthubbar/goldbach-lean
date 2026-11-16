module

public import LeanLab.Pintz2018.Numbers
public import LeanLab.Pintz2018.Density117
public import LeanLab.Pintz2018.Residual117
public import LeanLab.Pintz2018.Discrete117
public import LeanLab.Pintz2018.Laplace117
public import LeanLab.Pintz2018.Monotonicity117
public import LeanLab.Pintz2018.Instances117

/-!
# Proof of the Pintz 2018 entry

* `Greedy117.theoremK_ordered_integral` and `Residual117.saturation_and_residual`: the exchange
  argument of displays 8.12 to 8.16. Moving mass `η` from the last active coordinate to the
  first unsaturated one keeps the order, lowers a concave cost and raises a strictly convex
  objective, `Decomp117b.leaf_pair_exchange` and `Ordered117.saturation_ordered`. The cost
  of display 8.11 is concave and the objective `y^b - y^c` is strictly convex for `b > 1`,
  `Curvature117`; the substitution `y = e^{dT}` of display 8.10 is in `Greedy117`.
  `Laplace117` checks that the Laplace form of display 8.11 is such an integral cost.
* `Density117.excess_bound_of_720`: displays 7.20 and 8.1 to 8.4, the centring identity, the
  off diagonal count and the quadratic step of `Decomp117`.
* `basic_ineq`: `LeanLab/Pintz2018/Section9.lean`.
* `case8`: `LeanLab/Pintz2018/Numbers.lean`, with the Taylor bounds of `ExpBounds.lean`.

AI agents wrote the Lean code, see `PORTING.md`; it was checked by the Lean kernel.
-/
