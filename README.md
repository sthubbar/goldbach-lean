# GoldbachLean

Lean 4 formalizations from Steve Hubbard's Lean Lab project, which works toward the binary
Goldbach conjecture. The conjecture is still open, and nothing here claims to prove it.
The project formalizes published results about Goldbach's problem and its relatives,
checks their proofs and constants, and records the gaps it finds.

All Lean code here was written by an AI agent, Claude by Anthropic, under Steve Hubbard's
direction. It is checked by the Lean kernel and by Lean's Comparator. No human expert has
reviewed the mathematics.

## Entries

| Challenge | Solution | Comparator config | Metadata | Result |
|---|---|---|---|---|
| `ChallengeWu2008.lean` | `SolutionWu2008.lean` | `comparator-wu2008.json` | `entries/wu2008/formalization.yaml` | Wu 2008, Lemma 2.2, with the range of the last sum repaired |
| `ChallengeHeathBrown1985.lean` | `SolutionHeathBrown1985.lean` | `comparator-heathbrown1985.json` | `entries/heathbrown1985/formalization.yaml` | Heath-Brown 1985: Siegel-Walfisz, Theorem 1, almost all binary Goldbach, Vinogradov's three primes theorem, three primes in progression |

## Build

Lean v4.35.0, Mathlib v4.35.0.

    lake exe cache get
    lake build
    lake comparator --config=comparator-wu2008.json
    lake comparator --config=comparator-heathbrown1985.json

Entries are submitted to the Palomar registry through https://submit.palomar-registry.org/.

## Licence

Apache-2.0, see LICENSE. Files under `LeanLab/PNTPort/StrongPNT/` are ported from
PrimeNumberTheoremAnd, Apache-2.0; see NOTICE and PORTING.md.
