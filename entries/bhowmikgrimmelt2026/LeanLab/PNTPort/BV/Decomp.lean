module

public import LeanLab.PNTPort.BV.Vaughan
public import LeanLab.PNTPort.BV.Characters

/-!
# Vaughan's decomposition of ψ(x, χ)

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

`psiChi_decomp`: `ψ(x, χ) = S₁ - S₂ + S₃ - S₄` with the four Vaughan sums below, for any
Dirichlet character `χ` and any `u`, `v ≥ 1`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

variable {q : ℕ} (x : ℝ) (u v : ℕ) (χ : DirichletCharacter ℂ q)

/-- The truncated Möbius sum `g_v(k) = ∑_{d ∣ k, d ≤ v} μ(d)`. -/
noncomputable def gV (v k : ℕ) : ℝ := ∑ d ∈ k.divisors, (if d ≤ v then (μ d : ℝ) else 0)

/-- `S₁ = ∑_{n ≤ x, n ≤ u} Λ(n) χ(n)`. -/
noncomputable def S1 : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ((if n ≤ u then vonMangoldt n else 0 : ℝ) : ℂ) * χ (n : ZMod q)

/-- `S₂ = ∑_{n ≤ x} χ(n) ∑_{t r = n} ∑_{m d = t, m ≤ u, d ≤ v} Λ(m) μ(d)`. -/
noncomputable def S2 : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ((∑ p ∈ n.divisorsAntidiagonal, ∑ y ∈ p.1.divisorsAntidiagonal,
    (if y.1 ≤ u ∧ y.2 ≤ v then vonMangoldt y.1 * (μ y.2 : ℝ) else 0) : ℝ) : ℂ) * χ (n : ZMod q)

/-- `S₃ = ∑_{n ≤ x} χ(n) ∑_{d h = n, d ≤ v} μ(d) log h`. -/
noncomputable def S3 : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ((∑ p ∈ n.divisorsAntidiagonal,
    (if p.1 ≤ v then (μ p.1 : ℝ) * Real.log p.2 else 0) : ℝ) : ℂ) * χ (n : ZMod q)

/-- `S₄ = ∑_{n ≤ x} χ(n) ∑_{m k = n, m > u, k > v} Λ(m) g_v(k)`. -/
noncomputable def S4 : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, ((∑ p ∈ n.divisorsAntidiagonal,
    (if u < p.1 ∧ v < p.2 then vonMangoldt p.1 * gV v p.2 else 0) : ℝ) : ℂ) * χ (n : ZMod q)

/-- **Vaughan's decomposition.** -/
theorem psiChi_decomp (hv : 1 ≤ v) :
    psiChi x χ = S1 x u χ - S2 x u v χ + S3 x v χ - S4 x u v χ := by
  unfold psiChi S1 S2 S3 S4
  rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
  have h := vaughan_identity u v hv n hn1
  rw [← sub_mul, ← add_mul, ← sub_mul]
  congr 1
  unfold gV
  exact_mod_cast h

end LeanLab.PNTPort.BV
