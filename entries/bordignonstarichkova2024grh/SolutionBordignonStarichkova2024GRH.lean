module

public import LeanLab.BS2022GRH.Cert1575Closed

/-!
# Proof of the Bordignon-Starichkova 2024 GRH Chen threshold entry, CONDITIONAL

`LeanLab/BS2022GRH/Cert1575Closed.lean` proves `chenThreshold13375_of_deep_closed`: under GRH,
taken as an explicit hypothesis inside `ChenThreshold13375`, every even `N ≥ exp(exp 13.375)` is
a prime plus a square-free number `η > 1` with at most two prime factors, CONDITIONAL ON the
cited Theorems 5, 6, 7 of the paper, `Thm5J`, `Thm6J`, `Thm7J`, and the cited linear sieve,
Theorem 4 with the Table 1 row `ε⁻¹ = 6100`, `LinearSieveT4 (1/8349) 112 114`, all taken as
explicit hypotheses, never as axioms.

Route: Chen's weighted inequality, Lemma 9 of the paper, `U7153.lemma10`, PROVED; the
Section 5.5 square-free step, PROVED; the main-term margin of Section 5.4 at the new
parameters, `Journal.theorem3_positive_main`, PROVED; the bracket certificate
`Cert1567.bracket13375_holds`, PROVED; and `ε(1500) < 1/8349`, `Cert1575.eps1500`, PROVED by a
kernel certificate, `decide +kernel` in the eleven window modules `Cert1575W00` to `Cert1575W10`,
for the prime sum up to 9003001, plus a Chebyshev θ tail bound.

AI wrote the Lean code, Claude, Anthropic; it was checked by the Lean kernel. Binary Goldbach is
open.
-/
