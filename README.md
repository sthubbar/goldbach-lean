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
| `entries/renyi1948` | `ChallengeRenyi1948.lean` | `comparator-renyi1948.json` | Rényi 1948: every large even N is p + m with p prime and m having at most 8 prime factors counted with multiplicity, with the count of such p; the entry also proves a derived twin-prime analogue by the same sieve method, not a result of Rényi 1948: infinitely many primes p with Ω(p + 2) ≤ 13000 |
| `entries/hardylittlewood1923` | `ChallengeHardyLittlewood1923.lean` | `comparator-hardylittlewood1923.json` | Hardy and Littlewood 1923, Partitio Numerorum III, Theorems B to F without Hypothesis R: asymptotics for sums of r ≥ 3 primes with the singular series, N_r(n) ∼ ν_r(n)/(log n)^r, three and four odd primes with C₃ and C₄, and Theorem F, A = 2C₂; version 2 adds Theorem A, eq. 3.113, on the paper's Hypothesis R at level Θ: ν_r of n is its main term with the singular series 𝔖_r of 3.114 up to an error O of n^{r−1+Θ−3/4} log^B n, for 47/64 ≤ Θ < 3/4 only, while the print allows every Θ < 3/4; the entry also proves derived results, not results of the paper: GRH gives the hypothesis, and 𝔖_r of n is positive in like parity |
| `entries/goldstonyang2016` | `ChallengeGoldstonYang2016.lean` | `comparator-goldstonyang2016.json` | Conditional on RH: Goldston and Yang 2017, Theorem 2, Σ_{n ≤ N} (1 − n/N) G(n) = N²/6 − 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)(ρ+2)) + O(N), with RH an explicit hypothesis and the zero sum proved absolutely convergent |
| `entries/languascozaccagnini2012` | `ChallengeLanguascoZaccagnini2012.lean` | `comparator-languascozaccagnini2012.json` | Conditional on RH: Languasco and Zaccagnini 2012, Theorem 1, Σ_{n ≤ N} G(n) = N²/2 − 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) + O(N log³ N), with RH an explicit hypothesis, the earlier bounds of Fujii and of Bhowmik and Schlage-Puchta, and the zero sum proved absolutely convergent |
| `entries/goldstonsuriajaya2021` | `ChallengeGoldstonSuriajaya2021.lean` | `comparator-goldstonsuriajaya2021.json` | Goldston and Suriajaya 2021, Theorem 1, the exact unconditional identity Σ_{n ≤ N} G(n) = N²/2 − 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) − (2 log 2π − 1/2) N + 2 (ζ'/ζ)(−1) − Σ_{k ≥ 1} N^{1−2k}/(k(2k−1)) + E(N), in ℂ and in ℝ, and eq. (13), the form with O(N); the entry also proves derived results, not statements of the paper: E(N) does not depend on r, every term is real, and the zero sum converges absolutely |
| `entries/dudek2017` | `ChallengeDudek2017.lean` | `comparator-dudek2017.json` | On the sum of a prime and a square-free number |
| `entries/alsetrishao2024` | `ChallengeAlsetriShao2024.lean` | `comparator-alsetrishao2024.json` | Alsetri and Shao 2024, Theorem 1.2: if a set A of primes has relative lower density above 1/2 in every reduced residue class, almost all even numbers are a sum of two primes from A; also the paper's Theorem 1.1, density 1 − ε in the primes alone does not suffice, and the sharpness of 1/2 from its Remark 1.3; the entry also proves a derived result, not a result of the paper: the hypothesis holds for the set of all primes, so the theorem is not vacuous |
| `entries/goldbachintervalsrh445` | `ChallengeGoldbachIntervalsRH445.lean` | `comparator-goldbachintervalsrh445.json` | CONDITIONAL on RH and cited zero counts: Goldbach numbers in intervals of length 4.45 log² x under RH, our preprint aiXiv.online 2610.02672: for every real x ≥ 3 there is a sum of two odd primes n with x < n < x + 4.45 (log x)², improving the constant 123 of Chirre and Hagen by their method; the cited inputs ExplicitA, HadamardK, Ordinates14, BPTN, HSWN70, HSWHead14 and even Goldbach up to 4·10¹⁸ are explicit hypotheses, never axioms |
| `entries/bordignonstarichkova2024grh` | `ChallengeBordignonStarichkova2024GRH.lean` | `comparator-bordignonstarichkova2024grh.json` | An explicit version of Chen's theorem assuming the Generalized Riemann Hypothesis |
| `entries/halupczok2012` | `ChallengeHalupczok2012.lean` | `comparator-halupczok2012.json` | CONDITIONAL on Perelli-Pintz-Salerno 1984 and Perelli-Pintz 1993: Halupczok 2013, JTNB, Theorem 1.2, repaired, a ternary Goldbach mean value theorem with primes in progressions and short intervals; the printed statement fails at a = 3, q = 3, and the repair sets the main term to 0 for q not coprime to a. The cited inputs are explicit hypotheses: the printed Remark p. 530 of Perelli, Pintz and Salerno, and the unnumbered Goldbach analogue of Perelli and Pintz 1993 sections 3 to 5 that the paper adapts |

## Build

Lean and Mathlib v4.35.0-rc3, the newest version Palomar's Challenge renderer currently
accepts. In an entry's folder:

    lake exe cache get
    lake build
    lake comparator --config=<its comparator config>

Entries are submitted to the Palomar registry through https://submit.palomar-registry.org/.

## Licence

Apache-2.0, see LICENSE. Files under `entries/heathbrown1985/LeanLab/PNTPort/StrongPNT/`, `entries/granville2007/LeanLab/PNTPort/StrongPNT/`, `entries/bombierivinogradov1965/LeanLab/PNTPort/StrongPNT/`, `entries/renyi1948/LeanLab/PNTPort/StrongPNT/`, `entries/hardylittlewood1923/LeanLab/PNTPort/StrongPNT/`, `entries/goldstonyang2016/LeanLab/PNTPort/StrongPNT/`, `entries/languascozaccagnini2012/LeanLab/PNTPort/StrongPNT/`, `entries/goldstonsuriajaya2021/LeanLab/PNTPort/StrongPNT/` and `entries/alsetrishao2024/LeanLab/PNTPort/StrongPNT/`, and the Selberg sieve files by Arend Mellendijk under `entries/romanov1934/LeanLab/PNTSieve/`, `entries/brun1919/LeanLab/PNTSieve/`, `entries/schnirelmann1933/LeanLab/PNTSieve/`, `entries/hardylittlewood1923/LeanLab/PNTSieve/` and `entries/alsetrishao2024/LeanLab/PNTSieve/`, except the lab-written BrunTitchmarshAP.lean and MertensUpper.lean, are ported from PrimeNumberTheoremAnd, Apache-2.0; see NOTICE and each entry's PORTING.md.
