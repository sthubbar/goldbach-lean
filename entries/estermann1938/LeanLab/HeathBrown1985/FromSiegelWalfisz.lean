module

public import Mathlib
public import LeanLab.HeathBrown1985.Sigma3Weighted
public import LeanLab.HeathBrown1985.Bridge

/-!
P0096 Heath-Brown 1985: Theorem 1 and Corollary 1 from the Siegel-Walfisz theorem 1.1 alone.
Every step from 1.1 to Theorem 1 is now machine-checked with zero sorry; 1.1 itself, a
classical theorem not yet in Mathlib, is the only input, taken as the hypothesis `hSW`.
AI-written Lean code, Claude, run 20261017T0603Z-10326. Checked only by the Lean kernel.
Binary Goldbach is OPEN; this is an almost-all result.
-/

@[expose] public section

namespace LeanLab.HeathBrown1985

/-- **Heath-Brown 1985, Corollary 1, from Siegel-Walfisz alone**, zero sorry: for every
`C > 0`, at most `O(x (log x)^{−C})` even numbers up to `x` fail to be a sum of two primes. -/
theorem corollary1_of_siegelWalfisz (hSW : SiegelWalfisz) : Corollary1 :=
  corollary1_of_theorem1 (theorem1_of_siegelWalfisz hSW)

end LeanLab.HeathBrown1985
