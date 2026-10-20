module

public import LeanLab.PNTPort.BV.Characters

/-!
# Bombieri-Vinogradov, statements

AI wrote this file. Definitions only, no proofs.

* `BombieriVinogradov`: for every `A > 0` there are `B > 0` and `K` with
  `∑_{q ≤ √x / (log x)^B} |ψ(x; q, a_q) - x/φ(q)| ≤ K x / (log x)^A` for every `x ≥ 2` and
  every choice of residues `a_q` coprime to `q`; the choice function form is the same as
  the usual `max_{(a,q)=1}` form.
* `LargeConductor`: the large conductor part, for every `A > 0` there are `C₁`, `B > 0`, `K`
  with `∑_{(log x)^C₁ < d ≤ √x/(log x)^B} φ(d)⁻¹ ∑_{χ primitive mod d} ‖ψ(x, χ)‖ ≤ K x/(log x)^A`.

Bombieri-Vinogradov is known mathematics, Bombieri 1965 and A. I. Vinogradov 1965.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset Real

/-- Pairs `⟨d, χ⟩` with `1 ≤ d ≤ Q` and `χ` primitive modulo `d`. -/
noncomputable def primSigma (Q : ℕ) : Finset (Σ d : ℕ, DirichletCharacter ℂ d) :=
  (Icc 1 Q).sigma (fun d => (univ : Finset (DirichletCharacter ℂ d)).filter
    (fun χ => χ.IsPrimitive))

/-- The Bombieri-Vinogradov theorem, as a statement. -/
def BombieriVinogradov : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ a : ℕ → ℕ,
    (∀ q, Nat.Coprime (a q) q) →
      ∑ q ∈ Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
        |HeathBrown1985.psi x q (a q) - x / q.totient| ≤ K * x / Real.log x ^ A

/-- The large conductor estimate, as a statement. -/
def LargeConductor : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C₁ B K : ℝ, 0 < B ∧ ∀ x : ℝ, 2 ≤ x →
    ∑ p ∈ (primSigma ⌊Real.sqrt x / Real.log x ^ B⌋₊).filter
        (fun p => Real.log x ^ C₁ < p.1),
      ‖psiChi x p.2‖ / p.1.totient ≤ K * x / Real.log x ^ A

end LeanLab.PNTPort.BV
