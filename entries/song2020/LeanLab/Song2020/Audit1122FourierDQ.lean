module

public import LeanLab.Song2020.Flag1734
public import LeanLab.Song2020.Prep1121FourierS2

/-!
AI wrote the Lean code, Claude, 2026-11-22.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, printed pages 3 to 5, Lemma 1 and the S2 bound.
Audit of `Flag1734.fourierApproxDQ_match`: the named hypothesis `Flag1734.FourierApproxDQ`,
a form of the step `fourier_approximation` of the lab file Decomp139, is proved: the two leaves
`weighted_window_bound` and `exponent_pair_half` of `Prep1121FourierS2` are proved, so the
assembly `Prep1121FourierS2.fourier_approximation_of_leaves` has axioms propext, Classical.choice
and Quot.sound only. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.Audit1122FourierDQ

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Song2020.Decomp139

/-- Proved. Song 2020 pages 3 to 5, Lemma 1 with the S2 bound: the named hypothesis
`FourierApproxDQ` of Flag1734 holds, by the closed split in Prep1121FourierS2. -/
theorem fourierApproxDQ_of_leaves : Flag1734.FourierApproxDQ :=
  Prep1121FourierS2.fourier_approximation_of_leaves

end LeanLab.Song2020.Audit1122FourierDQ
