# A. Trusted statement audit

Verdict: PASS

## 1. Diff against upstream Challenge.lean at 192ca57

Upstream HEAD confirmed: `192ca57362fa3ee737cd83205cb9ea99526c4553`.

A plain `diff` shows every line changed. That is line endings only: the upstream working copy is CRLF (`Unicode text, UTF-8 text, with CRLF line terminators`), the challenge is LF. `diff --strip-trailing-cr` and a diff against `git show HEAD:Challenge.lean` give the same real diff:

```
4c4
< # Challenge for leanprover/comparator
---
> # Challenge: upstream's `RamareMoebius` from upstream's `PlattGRH`
6,14c6,10
< (module docstring, upstream header text)
---
> (module docstring, new text naming 192ca57 and the solution)
69c65,67
< /-! ## Main theorems -/
---
> end TernaryGoldbach
>
> namespace TernaryGoldbach.RSBounds.Moebius003
71,74c69
< /-- Every odd `n ≥ 10²⁷` ... -/
< theorem ternary_goldbach_large_of_hypotheses (hGRH : PlattGRH) (hμ : RamareMoebius) :
<     TernaryGoldbachFrom (10 ^ 27) := by
<   sorry
---
> open TernaryGoldbach
76,78c71
< /-- The ternary Goldbach conjecture, given the three hypotheses. -/
< theorem ternary_goldbach_of_hypotheses (hGRH : PlattGRH) (hBG : BinaryGoldbachInput)
<     (hμ : RamareMoebius) : Statement := by
---
> theorem ramareMoebius_of_plattGRH (h : TernaryGoldbach.PlattGRH) : TernaryGoldbach.RamareMoebius := by
81c74
< end TernaryGoldbach
---
> end TernaryGoldbach.RSBounds.Moebius003
```

Lines 1 to 3 and 15 to 68 of upstream, which hold `import Mathlib`, all definitions, and all docstrings on definitions, are byte identical after CR stripping. Only the module docstring and the theorem block differ. The theorem sits in namespace `TernaryGoldbach.RSBounds.Moebius003` and names its types fully qualified; nothing else is declared in the file, so `TernaryGoldbach.PlattGRH` can only resolve to the upstream definition.

## 2. Hash

```
31cd8d5bccf87cd413bb1e56ab1cf3596af36a6ac8d3430fd621c197e6ea361d *~/ra/x/rsbounds-20261109-full/RSBounds-project/comparator/UpstreamRamareChallenge.lean
```
Matches expected.

## 3. What the theorem says

`ramareMoebius_of_plattGRH : PlattGRH → RamareMoebius`.

RamareMoebius: for every real x ≥ 11815,
|Σ_{1 ≤ n ≤ ⌊x⌋} μ(n)/n| ≤ 0.03 / ln x.

Edge cases:
- x is real, not natural. The sum is constant on [N, N+1) while 0.03/ln x falls, so the real statement equals: for every integer N ≥ 11815, |m(N)| ln(N+1) ≤ 0.03. That is slightly stronger than the integer form with ln N. Helfgott's note states and checks exactly this real form, item (m) uses log(n+1).
- `⌊x⌋₊` is Nat.floor, fine since x ≥ 11815 > 0.
- `Finset.Icc 1 ⌊x⌋₊` starts at 1, so n = 0 is excluded. Mathlib has μ(0) = 0 anyway.
- μ is the ℤ valued `ArithmeticFunction.moebius`, cast to ℝ, divided by n cast to ℝ. Real division, no truncation.
- `Real.log` is natural log, positive here, so no junk division by zero.
- Absolute value is `|·|` on ℝ.

PlattGRH: for every q ≥ 1 and every primitive Dirichlet character χ mod q, if q is odd and q ≤ 300000, every zero ρ of L(s, χ) with 0 < Re ρ < 1 and |Im ρ| ≤ 10^8/q has Re ρ = 1/2; if q is even and q ≤ 400000, the same up to height max(10^8/q, 200 + 7.5·10^7/q).

## 4. Comparison with the literature

[H] = Helfgott, The ternary Goldbach problem, arXiv:1501.05438, read via pdftotext. (2.21) is |Σ_{n ≤ x} μ(n)/n| ≤ 0.03/log x for x ≥ 11815, cited to [Ram13]. The bibliography resolves [Ram13] to Ramaré, "From explicit estimates for primes to explicit estimates for the Möbius function", Acta Arith. 157(4):365 to 379, 2013. That matches the upstream docstring.

Note: the paper title in my brief, "Explicit estimates on the summatory functions of the Möbius function with coprimality restrictions", is [Ram14], Acta Arith. 165 (2014). It is not the source of (2.21). The docstring cites the right paper; the brief had the wrong title.

Ramaré 2013, author preprint dated Nov 12 2012 at ramare-olivier.github.io/Maths/ElementaryConversion-11.pdf, read via pdftotext. Corollary 1.4: for D ≥ 50000, |Σ_{d ≤ D} μ(d)/d| ≤ (3 Log D − 10)/(100 (Log D)^2); "If we replace the -10 by 0, the resulting bound is valid from 11 815 onward." With −10 replaced by 0 this is 0.03/Log D. D is a real variable in that paper; its notation section writes D = [D] + {D}. Published journal version NOT CHECKED; preprint only.

Platt: [H] states Platt verified all odd q ≤ 3·10^5 with T_q = 10^8/q and all even q ≤ 4·10^5 with T_q = max(10^8/q, 200 + 7.5·10^7/q). The Lean definition matches these numbers.

## 5. Independent numeric check

Python sieve, my own script, μ up to 600001, run with `python -I`:

```
m(11814) 0.003230005808012021 |m|log11814 0.03028789543157522 |m|log11815 0.030288168824931683
max over 11815<=n<6e5 of |m(n)|log(n+1): 0.029496035857536147 at n= 11820
last n<11815 with |m(n)|log(n+1)>0.03: 11814
```

So the real x form holds on [11815, 600000) in floating point with margin, and fails on [11814, 11815). The threshold 11815 is sharp and correct for the real x reading. This matches the note's 0.030288 and 0.029496. Above 600000: NOT CHECKED here; that is the proof's job.

## 6. Is PlattGRH accidentally False?

No sign of it. Read from Mathlib source at the pinned rev 56a005855ea1 (both manifests agree):
- `DirichletCharacter.IsPrimitive χ := conductor χ = n`. Mod 1 the trivial character is primitive (`isPrimitive_one_level_one`), and `LFunction_modOne_eq : LFunction χ = riemannZeta`. So the q = 1 case is RH for ζ up to height 10^8, which is true by known verifications.
- `LFunction` is the genuine analytic continuation via Hurwitz zeta; agrees with the Dirichlet series for Re s > 1 (`LFunction_eq_LSeries`). The only junk value is at s = 1 for the trivial character, and Re ρ < 1 excludes it.
- `[NeZero q]` excludes q = 0. The 0 < Re ρ condition excludes trivial zeros.
- So PlattGRH is just Platt's real theorem in Mathlib's language. It would be False only if a real L-function had an off-line zero in Platt's verified range. One cosmetic point: Lean uses ≤ at the height bound, a closed range; Platt's verification is in practice carried a bit past the stated heights. Not a problem.

Lean elaboration of any of this: NOT CHECKED, per the no-build rule.
