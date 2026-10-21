module

public import LeanLab.PNTPort.BVMax.Primes
public import LeanLab.PNTPort.BVMax.Uncond

/-!
# Bombieri-Vinogradov for `θ` and `π`, classical form, unconditional

Lab proof, unit U-5301, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
ineffective constants through Siegel's theorem. No cited input.

* `bvTheta`: `Σ_{q ≤ √x/(log x)^B} max_{y ≤ x} max_{(a,q)=1} |θ(y; q, a) - y/φ(q)| ≤ K x/(log x)^A`;
* `bvPi`: `Σ_{q ≤ √x/(log x)^B} max_{y ≤ x} max_{(a,q)=1} |π(y; q, a) - liD(y)/φ(q)| ≤ K x/(log x)^A`,
  with `liD(y) = Σ_{2 ≤ n ≤ y} 1/log n`: the primes have level of distribution `1/2`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

theorem bvTheta : BVTheta := bvTheta_of bombieriVinogradovMax

theorem bvPi : BVPi := bvPi_of bvTheta

/-- Vacuity test and the `q = 1` term: for `y ≤ x`, `|π(y) - liD(y)| ≤ K x/(log x)^A`, a prime
number theorem with a log power saving, read off the first term of `bvPi`. -/
theorem pi_sub_liD (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
    1 ≤ Real.sqrt x / Real.log x ^ B → ∀ y : ℝ, 0 ≤ y → y ≤ x →
      |piAP y 1 1 - liD y| ≤ K * x / Real.log x ^ A := by
  obtain ⟨B, hB, K, hK⟩ := bvPi A hA
  refine ⟨B, hB, K, fun x hx hQ y hy hyx => ?_⟩
  have h := hK x hx (fun _ => 1) (fun q => Nat.coprime_one_left q) (fun _ => y)
    (fun _ => ⟨hy, hyx⟩)
  have h1 : 1 ∈ Finset.Icc 1 ⌊Real.sqrt x / Real.log x ^ B⌋₊ := by
    rw [Finset.mem_Icc]; exact ⟨le_rfl, Nat.le_floor (by simpa using hQ)⟩
  have := Finset.single_le_sum (f := fun q => |piAP y q 1 - liD y / q.totient|)
    (fun _ _ => abs_nonneg _) h1
  simp only [Nat.totient_one, Nat.cast_one, div_one] at this
  exact this.trans h

end LeanLab.PNTPort.BVMax

