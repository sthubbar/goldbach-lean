module

public import LeanLab.PNTPort.BVMax.Grid
public import LeanLab.PNTPort.PsiChi.Unconditional

/-!
# Bombieri-Vinogradov, classical form, unconditional

Lab proof, unit U-5300, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
Bombieri 1965 and A. I. Vinogradov 1965, ineffective constants through Siegel's theorem.

`bombieriVinogradovMax`: for every `A > 0` there are `B > 0` and `K` with
`Σ_{q ≤ √x/(log x)^B} |ψ(y_q; q, a_q) - y_q/φ(q)| ≤ K x/(log x)^A` for every `x ≥ 2`, every choice of
`0 ≤ y_q ≤ x` and every choice of residues `a_q` coprime to `q`; that is the sum over `q` of
`max_{y ≤ x} max_{(a,q)=1} |ψ(y; q, a) - y/φ(q)|`. From `PsiChi.bombieriVinogradov`, the `y = x`
form, by `BVMax.bombieriVinogradovMax_of`. No cited input.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

theorem bombieriVinogradovMax : BombieriVinogradovMax :=
  bombieriVinogradovMax_of PsiChi.bombieriVinogradov

/-- Vacuity test: the hypotheses hold for `y_q = x` and `a_q = 1`, so the statement contains the
`y = x` form with residue `1`. -/
theorem bombieriVinogradovMax_at_x (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ,
    ∀ x : ℝ, 2 ≤ x → ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊,
      |HeathBrown1985.psi x q 1 - x / q.totient| ≤ K * x / Real.log x ^ A := by
  obtain ⟨B, hB, K, hK⟩ := bombieriVinogradovMax A hA
  exact ⟨B, hB, K, fun x hx => hK x hx (fun _ => 1) (fun q => Nat.coprime_one_left q)
    (fun _ => x) (fun _ => ⟨by linarith, le_rfl⟩)⟩

end LeanLab.PNTPort.BVMax

