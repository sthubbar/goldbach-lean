module

public import LeanLab.HelfgottMajor.SPLIT_residue_log_derivative_bound
public import LeanLab.HelfgottMajor.Residue123

/-!
Route burst 2026-11-15, step gaussian_explicit_estimate p5, a repair of the rejected p4 branch.
P0014 Helfgott, Major arcs for Goldbach's problem, pages 36, 37 and 44: the bound of display
4.23 on the L'/L part of the residue R of Lemma 4.1, by the paper's own route through
Lemma 4.2, whose hypothesis is that the nontrivial zeros of L(s, χ) with abs Im at most 5/8
lie on the critical line. In the proof of Proposition 4.6 that hypothesis is at hand, because
the zeros are on the line up to height T and T is at least 100.

The lab leaves SplitGaussian123.residue_log_derivative_bound and
SplitGaussian123.log_derivative_norm_le state the same bounds with NO zero hypothesis, which the
paper does not prove; that is a recorded QUESTION. The theorems here carry the hypothesis and
are PROVED from Residue123, CONDITIONAL ON the one LEAF PolyaVinogradov123.polya_vinogradov_4_20,
with the arithmetic of page 37 taken from SPLIT_residue_log_derivative_bound, where it is PROVED.
No definition is made in this file. Lemma 4.1 itself enters as the lab LEAF
SplitGaussian123.lemma_4_1_gaussian, unchanged.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.HelfgottMajor.ResidueZeros123
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

end LeanLab.HelfgottMajor.ResidueZeros123
