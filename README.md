# GoldbachLean

Lean 4 formalizations from Steve Hubbard's Lean Lab project, which works toward the binary
Goldbach conjecture. The conjecture is still open, and nothing here claims to prove it.
The project formalizes published results about Goldbach's problem and its relatives,
checks their proofs and constants, and records the gaps it finds.

The new Lean code here was written by an AI agent, Claude by Anthropic, under Steve Hubbard's
direction; the agent also did the port of the files under
`entries/heathbrown1985/LeanLab/PNTPort/StrongPNT/`, whose code was written by the
PrimeNumberTheoremAnd contributors, see NOTICE and `entries/heathbrown1985/PORTING.md`. It is checked by the Lean kernel and by Lean's Comparator. No human expert has
reviewed the mathematics.

## Entries

Each entry is its own Lake project, the `project_path` of its Palomar submission.

| Project | Challenge | Comparator config | Result |
|---|---|---|---|
| `entries/wu2008` | `ChallengeWu2008.lean` | `comparator-wu2008.json` | Wu 2008, Lemma 2.2, with the range of the last sum repaired |
| `entries/heathbrown1985` | `ChallengeHeathBrown1985.lean` | `comparator-heathbrown1985.json` | Heath-Brown 1985: Siegel-Walfisz, Theorem 1, almost all binary Goldbach, Vinogradov's three primes theorem, three primes in progression |
| `entries/granville2007` | `ChallengeGranville2007.lean` | `comparator-granville2007.json` | Granville 2007: RH is equivalent to a Goldbach average estimate, in an equivalent form |

## Build

Lean and Mathlib v4.35.0-rc3, the newest version Palomar's Challenge renderer currently
accepts. In an entry's folder:

    lake exe cache get
    lake build
    lake comparator --config=<its comparator config>

Entries are submitted to the Palomar registry through https://submit.palomar-registry.org/.

## Licence

Apache-2.0, see LICENSE. Files under `entries/heathbrown1985/LeanLab/PNTPort/StrongPNT/` and
`entries/granville2007/LeanLab/PNTPort/StrongPNT/` are ported from PrimeNumberTheoremAnd,
Apache-2.0; see NOTICE and each entry's PORTING.md.
