module

public import LeanLab.HelfgottMajor.Gaussian123Base

/-!
Route burst 2026-11-15, step gaussian_explicit_estimate p6, built on p5.
P0014 Helfgott, Major arcs for Goldbach's problem, Lemma 4.1, page 31, displays 4.1 to 4.3, for
the Gaussian weight as used on page 44, in CORRECTED form. This file holds that one LEAF.

The lab leaf SplitGaussian123.lemma_4_1_gaussian states the printed Lemma 4.1. It is SUSPECTED
FALSE for an even primitive character χ with q above 1: there L(0, χ) = 0, so L'/L has a simple
pole at s = 0 with residue 1, the Mellin transform G_δ has a simple pole there with residue
η(0), the pole of the product is double, and the factor x^s = 1 + s log x + ... adds
η(0) log x to the residue. Display 4.7 on page 33 defines R without the factor x^s and loses
that term. Candidate counterexample, reproduced by independent agents on 2026-11-12 and
2026-11-15: q = 5, the Legendre character, δ = 0, x = 20, where the printed inequality needs
an error of norm 1.916 against the allowed c0 = 1.40557, and the gap grows like log x.
Also the functional equation, display 4.8, relates L(s, χ) to L(1 − s, χ bar), so the constant
term carries L'/L(1, χ bar), the complex conjugate of L'/L(1, χ); display 4.2 prints χ.

The printed leaf is not changed. The corrected statement is written out with no definition:
the main part of the residue and the log x term appear in full.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.Lemma41Leaf123
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

end LeanLab.HelfgottMajor.Lemma41Leaf123
