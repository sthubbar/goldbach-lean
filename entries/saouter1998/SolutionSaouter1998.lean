module

public import GoldbachLean.Saouter1998.Paper
public import GoldbachLean.Saouter1998.Lemma1Proof
public import GoldbachLean.Saouter1998.Theorem1
public import GoldbachLean.Saouter1998.Theorem2
public import GoldbachLean.Saouter1998.Table1
public import GoldbachLean.Saouter1998.ProthLadder

/-!
# Saouter 1998, the solution module

The compared theorems are proved in the `GoldbachLean` library.

* `Saouter1998/Paper.lean`: the corrected ladder constant, the printed misprint and Lemma 2.
* `Saouter1998/Lemma1Proof.lean`: Lemma 1, `BLS.lemma1`.
* `Saouter1998/Theorem2.lean` and `Saouter1998/Theorem1.lean`: Theorems 2 and 1, the first and the
  last prime of the paper.
* `Saouter1998/Table1.lean`: the 100 rungs of Table 1.
* `Saouter1998/ProthLadder.lean`: the derived range up to `10^20`, conditional on
  `EvenGoldbachUpTo (4 * 10^18)`.

AI wrote the Lean code: Claude by Anthropic for most files, Codex for Theorem 1 and the statement of Lemma 1, Gemini and Antigravity agents for parts of the Lemma 1 proof; it is checked by the Lean kernel.
-/
