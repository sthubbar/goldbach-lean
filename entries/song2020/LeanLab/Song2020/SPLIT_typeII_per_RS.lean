module

public import LeanLab.Song2020.Characteristic139
public import LeanLab.Song2020.RouteTypeIIWeyl
public import LeanLab.Song2020.RouteTypeIIInner

/-!
AI wrote the Lean code, 2026-11-15, the split of the
Type II display typeII_bound.
Source: Yanbo Song, https://arxiv.org/pdf/2012.06322 version 1, printed pages 6 and 7, from
"By Lemma 2.5 in [2], we have" to the five term display for T(R,S).
This new file states the two cited inputs of that passage as the paper applies them, both
now proved in the lab, in RouteTypeIIWeyl and RouteTypeIIInner: the
inequality of Graham and Kolesnik Lemma 2.5 for T(R,S)^2, and the van der Corput estimate
of Iwaniec and Kowalski Corollary 8.13 for the sum over r in I.
Reading common to the files of this split: x of the print is R S, the size of r s on the
dyadic block, and the passage from R S to n is made at the end by monotonicity; r ~ R is
R at most r < 2 R; the window is |r s - n/3| < y and r s at most t; the phase R_b(m) is
alpha m + h m^gamma. The file defines nothing.

Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.SPLIT_typeII_per_RS

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Proved in RouteTypeIIWeyl.weyl_shift_route.
Song 2020, page 7, "By Lemma 2.5 in [2], we have T(R,S)^2 << (RS)^2/L +
(R S^2/L) sum over 1 <= |l| <= L of max over S < s, s + l <= 2S of the modulus of the sum
over r in I of e(R_b(r(s+l)) - R_b(r s))", Graham and Kolesnik Lemma 2.5 applied to T(R,S)
with 1 <= L <= S. The interval I is cut out by r ~ R and the two window conditions. The
maximum over s is carried by a bound B l that holds for every admissible s; negative l is
covered by positive l through complex conjugation, at the cost of the constant. The print
has "RS 2/L" for R S^2/L. -/
theorem weyl_shift :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (y α t γ : ℝ) (h : ℤ) (a b : ℕ → ℂ),
      (∀ r, ‖a r‖ ≤ 1) → (∀ s, ‖b s‖ ≤ 1) → ∀ R S : ℝ, 1 ≤ R → 1 ≤ S →
        ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ S → ∀ B : ℕ → ℝ, (∀ l, 0 ≤ B l) →
          (∀ l : ℕ, 1 ≤ l → l ≤ L → ∀ s : ℕ, S ≤ (s : ℝ) → ((s + l : ℕ) : ℝ) < 2 * S →
            ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
              if (|((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t) ∧
                  (|((r * (s + l) : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧
                    ((r * (s + l) : ℕ) : ℝ) ≤ t) then
                eC ((α * ((r * (s + l) : ℕ) : ℝ) + h * ((r * (s + l) : ℕ) : ℝ) ^ γ) -
                  (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ))
              else 0‖ ≤ B l) →
          ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
              ∑ s ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun s : ℕ => S ≤ (s : ℝ) ∧ (s : ℝ) < 2 * S),
                if |((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t then
                  a r * b s * eC (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ)
                else 0‖ ^ 2 ≤
            C * ((R * S) ^ 2 / L + R * S ^ 2 / L * ∑ l ∈ Finset.Icc 1 L, B l) :=
  RouteTypeIIWeyl.weyl_shift_route

/-- Proved 2026-11-15 in RouteTypeIIInner.inner_vdc_route from the lab's
PortedVanDerCorput.vdC_second_derivative.
Song 2020, page 7, "By Cor. 8.13 in [3], we have sum over r in I of
e(R_b(r(s+l)) - R_b(r s)) << R^(1/2) x^(gamma/2-3/2) y |hl|^(1/2) + x^(1/2-gamma/2) R^(1/2)
|hl|^(-1/2)", with g''(r) of size x^(gamma-1) |hl| / R. Here x is R S and the length of I
is bounded by y/S + 1 where the print has y R / x; with x = R S the print's first term is
(y/S) R^(-1/2) (R S)^((gamma-1)/2) |hl|^(1/2). -/
theorem inner_vdc :
    ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (y : ℝ), 0 < y → ∀ (α t : ℝ)
      (h : ℤ), h ≠ 0 → ∀ R S : ℝ, 1 ≤ R → 1 ≤ S → ∀ l s : ℕ, 1 ≤ l → S ≤ (s : ℝ) →
        ((s + l : ℕ) : ℝ) < 2 * S →
          ‖∑ r ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
                (fun r : ℕ => R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R),
              if (|((r * s : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧ ((r * s : ℕ) : ℝ) ≤ t) ∧
                  (|((r * (s + l) : ℕ) : ℝ) - (n : ℝ) / 3| < y ∧
                    ((r * (s + l) : ℕ) : ℝ) ≤ t) then
                eC ((α * ((r * (s + l) : ℕ) : ℝ) + h * ((r * (s + l) : ℕ) : ℝ) ^ γ) -
                  (α * ((r * s : ℕ) : ℝ) + h * ((r * s : ℕ) : ℝ) ^ γ))
              else 0‖ ≤
            C * ((y / S + 1) * (R ^ (-(1 : ℝ) / 2) * (R * S) ^ ((γ - 1) / 2) *
                (|(h : ℝ)| * l) ^ ((1 : ℝ) / 2)) +
              R ^ ((1 : ℝ) / 2) * (R * S) ^ ((1 - γ) / 2) *
                (|(h : ℝ)| * l) ^ (-(1 : ℝ) / 2)) :=
  RouteTypeIIInner.inner_vdc_route

end

end LeanLab.Song2020.SPLIT_typeII_per_RS
