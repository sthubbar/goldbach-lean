module

public import LeanLab.KumchevLiu2007.Thm1Written

/-!
# Proof of the Kumchev and Liu 2007 Theorem 1 entry

`LeanLab/KumchevLiu2007/Thm1Written.lean` proves `thm1_written_of_eq33`: Theorem 1 of
A. V. Kumchev and J. Y. Liu, Sums of primes and squares of primes in short intervals,
arXiv 0801.0130, page 2 display 9, on the range X to the 7/18 + ε at most H at most
X to the 1 - ε that the proof on page 16 writes, from the paper's Proposition 1 display 33,
which is the explicit hypothesis `Eq33Hyp`. The same file proves
`thm1_full_of_written_small_eps`, the printed range H at most X for ε at most 5/18, and
`written_range_nonempty`. Goldbach type questions remain open and are not claimed. AI agents
wrote the Lean code and it reuses ported and earlier lab code, see `PORTING.md`; it was
checked by the Lean kernel.
-/
