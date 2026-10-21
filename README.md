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
| `entries/romanov1934` | `ChallengeRomanov1934.lean` | `comparator-romanov1934.json` | Romanov 1934: the integers p + 2^k have positive lower density; Erdős 1950: so do the odd numbers not of that form |
| `entries/mann1942` | `ChallengeMann1942.lean` | `comparator-mann1942.json` | Mann 1942: the α + β theorem σ(A + B) ≥ min(1, σA + σB) for Mathlib's Schnirelmann density, a Mathlib TODO |
| `entries/brun1919` | `ChallengeBrun1919.lean` | `comparator-brun1919.json` | Brun 1919: the sum of the reciprocals of the twin primes converges, with π₂(N) ≪ N / log² N and the same for every even gap |
| `entries/schnirelmann1933` | `ChallengeSchnirelmann1933.lean` | `comparator-schnirelmann1933.json` | Schnirelmann 1933: every integer n ≥ 2 is a sum of a bounded number of primes, explicitly at most 30772, a Mathlib TODO |
| `entries/bombierivinogradov1965` | `ChallengeBombieriVinogradov1965.lean` | `comparator-bombierivinogradov1965.json` | Bombieri 1965 and A. I. Vinogradov 1965: the Bombieri-Vinogradov theorem with the maximum over y ≤ x and over reduced residues inside the sum, for ψ, θ and π |
| `entries/renyi1948` | `ChallengeRenyi1948.lean` | `comparator-renyi1948.json` | Rényi 1948: every large even N is p + m with p prime and m having at most 8 prime factors counted with multiplicity, with the count of such p, and infinitely many primes p with Ω(p + 2) ≤ 13000 |

## Build

Lean and Mathlib v4.35.0-rc3, the newest version Palomar's Challenge renderer currently
accepts. In an entry's folder:

    lake exe cache get
    lake build
    lake comparator --config=<its comparator config>

Entries are submitted to the Palomar registry through https://submit.palomar-registry.org/.

## Licence

Apache-2.0, see LICENSE. Files under `entries/heathbrown1985/LeanLab/PNTPort/StrongPNT/`,
`entries/granville2007/LeanLab/PNTPort/StrongPNT/`,
`entries/bombierivinogradov1965/LeanLab/PNTPort/StrongPNT/` and
`entries/renyi1948/LeanLab/PNTPort/StrongPNT/`, and the Selberg sieve files under
`entries/romanov1934/LeanLab/PNTSieve/`, `entries/brun1919/LeanLab/PNTSieve/`
and `entries/schnirelmann1933/LeanLab/PNTSieve/`, are ported from PrimeNumberTheoremAnd,
Apache-2.0; see NOTICE and each entry's PORTING.md.
