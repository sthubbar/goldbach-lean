module

public import LeanLab.Song2020.Characteristic139
public import LeanLab.Akeno2026.Vaughan86
public import LeanLab.Song2020.RouteVaughanTypeII

/-!
AI wrote the Lean code, 2026-11-15, leaves for the target vaughan_uv.
Source: Yanbo Song, https://arxiv.org/pdf/2012.06322 version 1, printed pages 5 to 7, from
"Apply Lemma 3.2 with uv <= n" to the display for x^(-epsilon) (Sigma2 + Sigma3).
This file holds the open leaves of the route for the page 7 displays, Sigma 2 and Sigma 3,
one statement per display of the paper. The page 6 display for Sigma 1 is not a leaf here:
it is RouteVaughanSigma1.sigma1_route, proved there from its own single leaf, the inner sum
for one fixed r. This file defines nothing. The proof that the leaves imply vaughan_uv is in
RouteVaughanUV.

How the paper's pieces map to the lab's proved Vaughan identity
LeanLab.Akeno2026.Vaughan86.vaughan_weighted_identity, whose four terms are, with mu_u the
Moebius function cut at arguments at most u and Lambda_v the von Mangoldt function cut at
arguments at most v, written with the existing definition Vaughan86.shortPart:
  A = mu_u * log,  B = mu_u * Lambda_v * zeta,  E = Lambda_v,
  D = (mu - mu_u) * (Lambda - Lambda_v) * zeta,   Lambda = A - B + E + D.
B is split at r at most u, where r = w t is the argument of g = mu_u * Lambda_v:
  B1 = shortPart g u * zeta,  B3 = (g - shortPart g u) * zeta,  B = B1 + B3.
Then the paper's Sigma 1 is the window sum of A minus the window sum of B1, the paper's
Sigma 3 is minus the window sum of B3, where r at most u v holds automatically, and the
paper's Sigma 2 is the window sum of D: the coefficient of D at x is the sum over x = r s,
s > v, of Lambda(s) times the sum of mu(d) over d dividing r with d > u, which forces r > u,
and for r > 1 that inner sum is minus the sum of mu(d) over d dividing r with d at most u,
which is the print's form with its minus sign. The term E, the short von Mangoldt sum, does
not appear in the paper, whose window sits above v; it is bounded trivially in
RouteVaughanUV.

Deviations from the print, the same in every statement here and the same as in the existing
statement SPLIT_vaughan_per_u.vaughan_uv: the phase R_b(x) is written alpha x + h x^gamma
with alpha free, which covers beta x - b x / q; the window is the initial segment
|x - n/3| < y and x at most t of the existing statement, covering the paper's maximum over
z; x is replaced by n in every power; the paper's log x, log^2 x and x^epsilon factors are
all carried by one factor n^epsilon; the implied constant is C, depending on gamma and
epsilon only, valid for n at least N0; u and v are free reals with 1 at most u, 1 at most v
and u v at most n; h is any nonzero integer.

Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.RouteVaughanLeaves

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Akeno2026.Vaughan86
open scoped Classical

noncomputable section

/-- Song 2020, page 7, the display "x^(-epsilon) Sigma2 << n v^(-1/2) +
n^(1-gamma/4) |h|^(-1/4) + n^(3/4) y^(1/4) u^(-1/4) + u^(-1/6) n^((gamma+3)/6) y^(1/3)
|h|^(1/6) + u^(-1/4) n^((gamma+1)/4) y^(1/2) |h|^(1/4)", which the paper gets from dyadic
division into T(R,S), Graham and Kolesnik Lemma 2.5, Iwaniec and Kowalski Corollary 8.13 and
Graham and Kolesnik Lemma 2.4. Sigma 2 is the window sum of (mu - mu_u) * (Lambda - Lambda_v)
* zeta, equal to the print's form with its minus sign and d at most u. Deviations: x^epsilon
written n^epsilon; the header of this file carries the full reading. 
Proved through RouteVaughanTypeII.sigma2_route. Conditional on the
one open leaf RouteVaughanTypeII.typeII_bound. -/
theorem sigma2_bound :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → u * v ≤ n →
            ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
                ((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
                    shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u) *
                  (ArithmeticFunction.vonMangoldt - shortPart ArithmeticFunction.vonMangoldt v) *
                  (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤
              C * (n : ℝ) ^ ε *
                ((n : ℝ) * v ^ (-(1 : ℝ) / 2) +
                (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  exact RouteVaughanTypeII.sigma2_route

/-- Song 2020, page 7, the display "x^(-epsilon) Sigma3 << n^(1/2) (u v)^(1/2) +
n^(1-gamma/4) |h|^(-1/4) + n^(3/4) y^(1/4) u^(-1/4) + u^(-1/6) n^((gamma+3)/6) y^(1/3)
|h|^(1/6) + u^(-1/4) n^((gamma+1)/4) y^(1/2) |h|^(1/4)", which the paper states with the one
word "Similarly". The window sum here is that of the part r > u of mu_u * Lambda_v * zeta,
which is minus the paper's Sigma 3; the norm does not see the sign. Deviations: x^epsilon
written n^epsilon; the header of this file carries the full reading. 
Proved through RouteVaughanTypeII.sigma3_route. Conditional on the
one open leaf RouteVaughanTypeII.typeII_bound. -/
theorem sigma3_bound :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → u * v ≤ n →
            ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
                (((shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u *
                      shortPart ArithmeticFunction.vonMangoldt v -
                    shortPart (shortPart (ArithmeticFunction.moebius : ArithmeticFunction ℝ) u *
                      shortPart ArithmeticFunction.vonMangoldt v) u) *
                  (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤
              C * (n : ℝ) ^ ε *
                ((n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2) +
                (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  exact RouteVaughanTypeII.sigma3_route

end

end LeanLab.Song2020.RouteVaughanLeaves
