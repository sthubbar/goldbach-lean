module

public import Mathlib

/-!
# Helfgott's Proposition 6.2 on the ternary Goldbach minor arcs

H. A. Helfgott, *The ternary Goldbach conjecture is true*, arXiv 1312.7748v2, Section 6.1:
Lemma 6.1 on page 46 and Proposition 6.2 on page 47, proved on pages 46 to 48. These results
combine `l²` bounds over the major arcs `M_{δ0,r}` of display 3.5 with `l^∞` bounds off them, to
bound `∫ |S1|² |S2|` over the minor arcs. Four theorems are compared.

* `lemma61_paper`: Lemma 6.1, the summation by parts bound.
* `prop62`: Proposition 6.2 in an abstract measure form, for a natural upper endpoint.
* `prop62_arcs`: Proposition 6.2 for the arcs of display 3.5, a finite exponential polynomial `S1`
  and a natural upper endpoint.
* `prop62_series_real`: Proposition 6.2 for absolutely summable coefficients and a real upper
  endpoint, over any increasing measurable family of sets.

Hypotheses 6.4 and 6.5 of the Proposition stay hypotheses here, as in the paper. They are not
proved for any exponential sum, and Theorem 6.3 of the paper is not formalized. This entry does
not formalize the ternary Goldbach theorem. Binary Goldbach is open.

No single theorem here joins the arcs of display 3.5, general `L¹` coefficients and a real upper
endpoint: `prop62_arcs` has the arcs, `prop62_series_real` has the other two.

AI agents wrote the Lean code, Claude, Codex and other lab agents, as listed in PORTING.md. Lean
names keep the namespace of the lab where the proofs were written; every definition below is
restated under its exact name and in the same `open` context as in the solution files.
-/

@[expose] public section

namespace LeanLab.Helfgott2013.U1538

open Finset MeasureTheory intervalIntegral

variable {X : Type*} [MeasurableSpace X]

/-- Running maximum of `g` over the integers `n, n+1, ..., b`, floored at `0`. For `n > b` it is
`0`. If `n ≤ b` and `g ≥ 0` on those integers it is `max_{n ≤ m ≤ b} g(m)` of the paper, page 46.
The floor changes nothing in the paper's setting, where `g` takes values in `ℝ₀⁺`. -/
noncomputable def hmax (g : ℕ → ℝ) (b n : ℕ) : ℝ := (Finset.Icc n b).fold max 0 g

/-- `F` is non-decreasing and absolutely continuous on `[a, b]` with density `F' ≥ 0`: the
encoding of "continuous, piecewise differentiable and non-decreasing" in Lemma 6.1, page 46, and
Proposition 6.2, page 47. `F'` is nonnegative on `[a, b]` and interval integrable, and
`F y - F x = ∫_x^y F'` whenever `a ≤ x ≤ y ≤ b`. A function as in the paper meets this with `F'`
its derivative, given any nonnegative value at the finitely many break points. -/
def NondecFTC (F F' : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ u ∈ Set.Icc a b, 0 ≤ F' u) ∧ IntervalIntegrable F' volume a b ∧
    ∀ x y, a ≤ x → x ≤ y → y ≤ b → F y - F x = ∫ u in x..y, F' u

/-- `e(t) = exp(2πit)`, page 8, Section 2.1. -/
noncomputable def eC (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- The exponential polynomial `S1(α) = ∑_{n ∈ A} c_n e(αn)`: the `S1` of Proposition 6.2,
page 47, in the case of finitely many terms. -/
noncomputable def trig (A : Finset ℤ) (c : ℤ → ℂ) (α : ℝ) : ℂ := ∑ n ∈ A, c n * eC (α * n)

/-- The major arcs `M_{δ0,r}` of display 3.5, page 10, as a subset of `ℝ`, periodic mod `1`, closing the open
arcs of the paper: the closed arcs `[a/q - δ0 r/(2qx), a/q + δ0 r/(2qx)]` for odd `q ≤ r`, and
`[a/q - δ0 r/(qx), a/q + δ0 r/(qx)]` for even `q ≤ 2r`, with `(a, q) = 1`. Here `a` runs over all
integers, so intersecting with `[0, 1)` gives the arcs in `R/Z`. -/
def majorArcs (δ0 x r : ℝ) : Set ℝ :=
  {α | ∃ q : ℕ, ∃ a : ℤ, 0 < q ∧ Int.gcd a q = 1 ∧
    ((Odd q ∧ (q : ℝ) ≤ r ∧ |α - a / q| ≤ δ0 * r / (2 * q * x)) ∨
      (Even q ∧ (q : ℝ) ≤ 2 * r ∧ |α - a / q| ≤ δ0 * r / (q * x)))}

/-- Lemma 6.1, page 46. Let `a ≤ b` be naturals, `f ≥ 0`, `g ≥ 0` on `{a, ..., b}`, and `F`
non-decreasing with density `F'` on `[a, b]`. If display 6.1 holds, `∑_{a ≤ n ≤ x} f(n) ≤ F(x)`
for every real `x ∈ [a, b]`, then
`∑_{n=a}^{b} f(n) g(n) ≤ (max_{n ≥ a} g(n)) F(a) + ∫_a^b (max_{n ≥ u} g(n)) F'(u) du`,
where the maxima run over integers at most `b`. `f` is taken nonnegative on all naturals, which
loses nothing since only its values on `{a, ..., b}` matter. -/
theorem lemma61_paper {a b : ℕ} (hab : a ≤ b) (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hg : ∀ n ∈ Icc a b, 0 ≤ g n) (F F' : ℝ → ℝ) (hF : NondecFTC F F' a b)
    (h61 : ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → ∑ m ∈ Icc a ⌊x⌋₊, f m ≤ F x) :
    ∑ n ∈ Icc a b, f n * g n ≤
      hmax g b a * F a + ∫ u in (a : ℝ)..b, hmax g b ⌈u⌉₊ * F' u := by
  sorry

/-- Proposition 6.2, page 47, abstract measure form. `w` plays `|S1|² / ∑ |a_n|²`, of total
mass `1`, `s` plays `|S2|`, and `M` is any increasing family of measurable sets. Let `r0 ≤ r1` be
naturals, `0 ≤ s ≤ C` almost everywhere, `H` non-decreasing with density `H'` on `[r0, r1]` and
`H(r1) = 1`, `g ≥ 0` non-increasing on `[r0, r1]`. If display 6.4, `∫_{M(r+1)} w ≤ H(r)`, and
display 6.5, `s ≤ g(r)` off `M r`, hold at every integer `r0 ≤ r ≤ r1`, then display 6.6:
`∫_{(M r0)ᶜ} w s ≤ g(r0) (H(r0) - I0) + ∫_{r0}^{r1} g(r) H'(r) dr`, with `I0 = ∫_{M r0} w` as in
display 6.7. The paper's `r1` is real; this form takes it natural. -/
theorem prop62 {μ : Measure X} {w s : X → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hwi : Integrable w μ)
    (hw1 : ∫ y, w y ∂μ = 1) (hsm : AEStronglyMeasurable s μ) (hs0 : ∀ y, 0 ≤ s y) {C : ℝ}
    (hsC : ∀ᵐ y ∂μ, s y ≤ C) {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r))
    (hmono : Monotone M) {r0 r1 : ℕ} (hr : r0 ≤ r1) {H H' g : ℝ → ℝ}
    (hH : NondecFTC H H' r0 r1) (hH1 : H r1 = 1)
    (h64 : ∀ r : ℕ, r0 ≤ r → r ≤ r1 → ∫ y in M (r + 1), w y ∂μ ≤ H r)
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) r1, 0 ≤ g u) (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) r1))
    (h65 : ∀ r : ℕ, r0 ≤ r → r ≤ r1 → ∀ᵐ y ∂μ, y ∉ M r → s y ≤ g r) :
    ∫ y in (M r0)ᶜ, w y * s y ∂μ ≤
      g r0 * (H r0 - ∫ y in M r0, w y ∂μ) + ∫ u in (r0 : ℝ)..r1, g u * H' u := by
  sorry

/-- Proposition 6.2, page 47, for the arcs of display 3.5 and `S1 = ∑_{n ∈ A} c_n e(αn)` with
`N = ∑ |c_n|² > 0`, `A` finite, `R/Z` modelled as `[0, 1)`, natural `r0 ≤ r1`. If `H` is
non-decreasing with density `H'` on `[r0, r1]`, `H(r1) = 1`, display 6.4
`(1/N) ∫_{M_{δ0,r+1}} |S1|² ≤ H(r)` and display 6.5 `|S2(α)| ≤ g(r)` off `M_{δ0,r}` hold for
integers `r0 ≤ r ≤ r1`, with `g ≥ 0` non-increasing, then display 6.6:
`(1/N) ∫_{[0,1) \ M_{δ0,r0}} |S1|² |S2| ≤ g(r0) (H(r0) - I0) + ∫_{r0}^{r1} g(r) H'(r) dr`,
with `I0 = (1/N) ∫_{M_{δ0,r0}} |S1|²` as in display 6.7. `S2` is any continuous function on `ℝ`,
periodic or not. The paper's condition `δ0 ≤ x / 2 r1²` is not assumed. -/
theorem prop62_arcs (A : Finset ℤ) (c : ℤ → ℂ) (hN : 0 < ∑ n ∈ A, ‖c n‖ ^ 2)
    {S2 : ℝ → ℂ} (hS2 : Continuous S2) {δ0 x : ℝ} (hδ : 0 ≤ δ0) (hx : 0 < x) {r0 r1 : ℕ}
    (hr : r0 ≤ r1) {H H' g : ℝ → ℝ} (hH : NondecFTC H H' r0 r1) (hH1 : H r1 = 1)
    (h64 : ∀ r : ℕ, r0 ≤ r → r ≤ r1 →
      (∫ α in majorArcs δ0 x (r + 1 : ℕ) ∩ Set.Ico 0 1, ‖trig A c α‖ ^ 2) /
        ∑ n ∈ A, ‖c n‖ ^ 2 ≤ H r)
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) r1, 0 ≤ g u) (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) r1))
    (h65 : ∀ r : ℕ, r0 ≤ r → r ≤ r1 → ∀ α ∈ Set.Ico (0 : ℝ) 1, α ∉ majorArcs δ0 x r →
      ‖S2 α‖ ≤ g r) :
    (∫ α in (majorArcs δ0 x r0)ᶜ ∩ Set.Ico 0 1, ‖trig A c α‖ ^ 2 * ‖S2 α‖) /
        ∑ n ∈ A, ‖c n‖ ^ 2 ≤
      g r0 * (H r0 - (∫ α in majorArcs δ0 x r0 ∩ Set.Ico 0 1, ‖trig A c α‖ ^ 2) /
        ∑ n ∈ A, ‖c n‖ ^ 2) + ∫ u in (r0 : ℝ)..r1, g u * H' u := by
  sorry

/-- Proposition 6.2, pages 47 to 48, for `S1 = ∑_{n ∈ ℤ} c_n e(αn)` with absolutely summable
`c`, `N = ∑ |c_n|² > 0`, and a real upper endpoint `R`, over any increasing measurable family `M`
of subsets of `ℝ`, with `R/Z` modelled as `(0, 1]`. Displays 6.4 and 6.6 appear multiplied by
`N`: if `∫_{M(r+1)} |S1|² ≤ N H(r)` and `|S2(α)| ≤ g(r)` for `α ∈ (0, 1]` off `M r`, at every real
`r ∈ [r0, R]`, then
`∫_{(0,1] \ M r0} |S1|² |S2| ≤ g(r0) (N H(r0) - ∫_{M r0} |S1|²) + N ∫_{r0}^{R} g(r) H'(r) dr`.
The family `M` is not specialised to the arcs of display 3.5 here. -/
theorem prop62_series_real (c : ℤ → ℂ) (hc : Summable (fun n => ‖c n‖))
    (hN : 0 < ∑' n : ℤ, ‖c n‖ ^ 2)
    (S2 : ℝ → ℂ) (hS2 : Continuous S2) {M : ℝ → Set ℝ}
    (hM : ∀ r, MeasurableSet (M r)) (hmono : Monotone M)
    {r0 : ℕ} {R : ℝ} (hr : (r0 : ℝ) ≤ R) {H H' g : ℝ → ℝ}
    (hH : NondecFTC H H' r0 R) (hH1 : H R = 1)
    (h64 : ∀ r ∈ Set.Icc (r0 : ℝ) R,
      (∫ α in M (r + 1),
        ‖∑' n : ℤ, c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))‖ ^ 2
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤ (∑' n : ℤ, ‖c n‖ ^ 2) * H r)
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) R, 0 ≤ g u)
    (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) R))
    (h65 : ∀ r ∈ Set.Icc (r0 : ℝ) R, ∀ α ∈ Set.Ioc (0 : ℝ) 1,
      α ∉ M r → ‖S2 α‖ ≤ g r) :
    (∫ α in (M r0)ᶜ,
      ‖∑' n : ℤ, c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))‖ ^ 2 * ‖S2 α‖
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) ≤
      g r0 * ((∑' n : ℤ, ‖c n‖ ^ 2) * H r0 -
        ∫ α in M r0,
          ‖∑' n : ℤ, c n * Complex.exp (2 * Real.pi * Complex.I * (α * n : ℝ))‖ ^ 2
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) +
      (∑' n : ℤ, ‖c n‖ ^ 2) * ∫ u in (r0 : ℝ)..R, g u * H' u := by
  sorry

end LeanLab.Helfgott2013.U1538
