module

public import GoldbachLean.Wu2008.Err

/-!
# Proof of the Wu 2008 Lemma 2.2 entry

The proofs live in `GoldbachLean/Wu2008/`: `Real.lean` proves the pointwise inequality in the real
exponent model, `Int.lean` transfers it to integers through `p ↦ log p / log N`, `Sum.lean` sums it
over `A` against Wu's sieve sums, and `Err.lean` bounds the non-squarefree error. AI wrote the Lean
code, Claude, Anthropic; it was checked by the Lean kernel and reviewed against the paper by
separate AI subagents and by the submitter.
-/
