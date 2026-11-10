# Auditor E: Schoenfeld 1976 statements, FiniteRH, PlattGRH step, PsiCert

All paths relative to P = ~/ra/x/rsbounds-20261109-full/RSBounds-project. I did not build or run Lean. Axiom results below are quoted from logs written by earlier runs, not rerun by me.

## Lean statements found

Goals.FiniteRH, RSBounds/Targets.lean:18

    def FiniteRH (A : ℝ) : Prop :=
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ A → ρ.re = 1 / 2

Mathlib riemannZeta, open strip 0 < re < 1, non-strict |im| ≤ A, both signs of im via abs, conclusion re = 1/2.

Schoenfeld targets, RSBounds/Schoenfeld1976Targets.lean and Schoenfeld1976TargetsExtra.lean. Each has premise FiniteRH 1894438.5122, real x, Mathlib Chebyshev.psi and Chebyshev.theta.

| display | Lean name | statement |
|---|---|---|
| 5.5a* | PsiLog | x ≥ 161971: abs(ψ−x) < 0.0220646 x/log x |
| 5.5b* | PsiLogLower | x ≥ 89909: −0.0220646 x/log x < ψ−x |
| 5.6a* | ThetaLogUpper | x > 1: θ−x < 0.0201384 x/log x |
| 5.6* | ThetaLog | x ≥ 758711: abs(θ−x) < 0.0239922 x/log x |
| 5.6b* | PsiThetaLog | x ≥ e^22: abs(ψ−x) and abs(θ−x) both < 0.0077629 x/log x |
| 7.2 | PsiTheorem11 | x ≥ 17: abs(ψ−x) < x ε0(x) |
| 7.3 | ThetaTheorem11 | x ≥ 101: abs(θ−x) < x ε0(x) |
| 7.4 | PsiUpperTheorem11 | x ≥ 1: θ−x ≤ ψ−x and ψ−x < x ε0(x) |

X = sqrt(log x / 9.645908801), ε0 = sqrt(8/(17π)) · sqrt(X) · e^(−X).

## Proved or assumed

Proved, with FiniteRH 1894438.5122 as the only premise. RSBounds/Schoenfeld1976Final.lean builds each from Schoenfeld1976Theorem7Proved / Theorem11Proved applied to psiCert, and psiCert is PsiFinite.psi_abs_sub_le_four_fifths_sqrt. PsiThetaLog needs no PsiCert. No sorry or axiom in RSBounds .lean files: grep found only the words in docstrings. logs-claude/final-axiom-audit.log (earlier run) reports only propext, Classical.choice, Quot.sound for all nine Final theorems; logs-claude/upstream-axiom-audit.log the same for finiteRH_of_plattGRH and ramareMoebius_of_plattGRH. Not rerun by me.

In the closure of Moebius003.Upstream, the Schoenfeld results enter as theorems, not hypotheses. The only hypothesis is PlattGRH.

## Comparison with Schoenfeld 1976

Primary source NOT CHECKED. AMS served a bot-verification page for the PDF and 403 for the landing pages; scispace copies were empty. I did not try to get past the check.

Secondary corroboration:
- Trudgian, arXiv 1401.2689, quoting [Schoenfeld 1976, Thm 11]: ε0(x) = sqrt(8/(17π)) X^(1/2) e^(−X), X = sqrt(log x / R0), R0 = 9.6459..., abs(θ(x)−x) < x ε0(x) for x ≥ 101. Matches ThetaTheorem11 and the ε0 definition. Strictness was lost in the text extraction.
- Broadbent, Kadiri, Lumley, Ng, Wilk, arXiv 2002.11068, Table 2 lists Schoenfeld 1976 with m1 = 0.02400 and X0 = 758711 for θ. Consistent with 5.6*, 0.0239922 rounded.
- 5.5a*, 5.5b*, 5.6a*, 5.6b*, 7.2 and 7.4 constants and ranges: NOT CHECKED against any source beyond the project's own transcription, docs/Schoenfeld1976Plan.md, which agrees with the Lean exactly.

(7.4): the project says the printed display has lost a relation and states θ−x ≤ ψ−x < xε0(x) for x ≥ 1. A Schoenfeld corrigendum, Math. Comp. 30 (1976) p. 900, exists and per its search abstract corrects (7.4). I could not read it. Whether the corrigendum's (7.4) equals the Lean form is NOT CHECKED. This is a fidelity question only: the Lean form is proved, and it is not used by the Moebius chain as far as the Final file shows.

## Height 1894438.5122

F(T) = (T/2π) log(T/2π) − T/2π + 7/8 at T = 1894438.5122 gives 3502499.99991 (computed here with Python). So it is RS75's A, the root of F(A) = 3502500, rounded down. Search results confirm RS75 used the first 3,502,500 zeros verified on the line. Rounding down weakens the hypothesis, which is the safe direction. That Schoenfeld 1976 itself uses this height: NOT CHECKED in the paper; it builds on RS75 Thm 1 with R0 = 9.645908801, per Trudgian.

## PlattGRH to FiniteRH 1894438.5122

Upstream ZetaZeroSums.lean:

    def RHBelow (H : ℝ) : Prop :=
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ H → ρ.re = 1 / 2
    theorem rh_upto_1e8 [h : Fact TernaryGoldbach.PlattGRH] : RHBelow 1e8

RHBelow is FiniteRH word for word, same binder order. rh_upto_1e8 applies PlattGRH at q = 1, the trivial character, odd branch, 1 ≤ 300000, and rewrites LFunction at level 1 to riemannZeta; 1e8/1 by simpa. finiteRH_of_plattGRH:

    intro ρ hz h0 h1 him
    exact TernaryGoldbach.Explicit.rh_upto_1e8 ρ hz h0 h1 (him.trans (by norm_num))

him : |ρ.im| ≤ 1894438.5122, norm_num closes 1894438.5122 ≤ 1e8, giving |ρ.im| ≤ 1e8. Right direction. Correct.

## PsiCert

RSBounds/PsiFinite/Final.lean:15

    theorem psi_abs_sub_le_four_fifths_sqrt {x : ℝ} (h₁ : 1500 ≤ x) (h₂ : x ≤ 10 ^ 10) :
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x

Goals.Schoenfeld1976.PsiCert is the same: real x, closed endpoints 1500 and 10^10, non-strict ≤, Mathlib Chebyshev.psi. No local Chebyshev namespace in RSBounds; upstream's Helfgott.psi on naturals is a different name and not used here.

Verdict: PASS on the Lean side. Schoenfeld primary-source comparison NOT CHECKED, partly corroborated for 7.3, ε0 and 5.6*.
