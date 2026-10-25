module

public import LeanLab.DensityGoldbach.U1478Arcs
public import LeanLab.DensityGoldbach.U1481Coef

/-!
Unit U-1481, run 20261022T1302Z-31860. P0047 Alsetri and Shao 2024, Theorem 1.2.

Partial assembly of `ArcClassBound` of U1478Arcs. If `-r/(WN) = ρ + β` with `ρ ∈ ℚ` and every
`S(X, k/W + ρ + β)` is within `E` of the major arc main term `μ(q_k)/φ(q_k) V(X, β)`, `q_k` the
reduced denominator of `k/W + ρ`, then `‖twS‖ ≤ ‖coefSum‖ ‖V(β)‖ + W E`, and at `W = z#` with
`den ρ ∤ W` this is at most `W/(φ(W) z) ‖V(β)‖ + W E` by `coefSum_not_dvd`.

What is not done: the Dirichlet choice of `ρ`, the case `den ρ ∣ W` through `V_period`, and the
minor arc case, so `ArcClassBound` is NOT proved here.

AI-written Lean code, Claude, 2026-10-22. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
noncomputable section
namespace LeanLab.DensityGoldbach.U1481

open LeanLab.DensityGoldbach.U1478

local notation "eL" => LeanLab.PNTPort.LargeSieve.e
local notation "SV" => LeanLab.PNTPort.Vinogradov.S
local notation "VV" => LeanLab.PNTPort.Vinogradov.V

/-- **Major arc assembly**: the twisted sum against the coefficient sum. -/
theorem twS_major {W b N r : ℕ} (ρ : ℚ) (β : ℝ)
    (hθ : -((r : ℝ) / (W * N)) = (ρ : ℝ) + β) {E : ℝ}
    (hE : ∀ k < W, ‖SV (Xc W b N) ((((k : ℚ) / W + ρ : ℚ) : ℝ) + β) -
      gμ (((k : ℚ) / W + ρ).den) * VV (Xc W b N) β‖ ≤ E) :
    ‖twS W b N r‖ ≤ ‖coefSum W b ρ‖ * ‖VV (Xc W b N) β‖ + W * E := by
  have hsplit : twS W b N r = coefSum W b ρ * VV (Xc W b N) β +
      ∑ k ∈ range W, eL (-((k : ℝ) * b / W)) *
        (SV (Xc W b N) ((((k : ℚ) / W + ρ : ℚ) : ℝ) + β) -
          gμ (((k : ℚ) / W + ρ).den) * VV (Xc W b N) β) := by
    unfold twS coefSum
    rw [sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    have : (k : ℝ) / W - (r : ℝ) / (W * N) = (((k : ℚ) / W + ρ : ℚ) : ℝ) + β := by
      push_cast; rw [sub_eq_add_neg, hθ]; ring
    rw [this]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k ∈ range W, ‖eL (-((k : ℝ) * b / W)) *
      (SV (Xc W b N) ((((k : ℚ) / W + ρ : ℚ) : ℝ) + β) -
        gμ (((k : ℚ) / W + ρ).den) * VV (Xc W b N) β)‖ ≤ E := by
    intro k hk
    rw [norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, one_mul]
    exact hE k (mem_range.1 hk)
  refine (sum_le_sum this).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]

/-- **Major arc case `den ρ ∤ z#`**: `‖twS‖ ≤ W/(φ(W) z) ‖V(β)‖ + W E`. -/
theorem twS_major_not_dvd {z b N r : ℕ} (hz1 : 1 ≤ z) (hb : Nat.Coprime b (primorial z))
    (ρ : ℚ) (hnd : ¬ ρ.den ∣ primorial z) (β : ℝ)
    (hθ : -((r : ℝ) / (primorial z * N)) = (ρ : ℝ) + β) {E : ℝ}
    (hE : ∀ k < primorial z, ‖SV (Xc (primorial z) b N)
      ((((k : ℚ) / primorial z + ρ : ℚ) : ℝ) + β) -
      gμ (((k : ℚ) / primorial z + ρ).den) * VV (Xc (primorial z) b N) β‖ ≤ E) :
    ‖twS (primorial z) b N r‖ ≤ (primorial z : ℝ) / Nat.totient (primorial z) / z *
      ‖VV (Xc (primorial z) b N) β‖ + primorial z * E := by
  refine (twS_major ρ β hθ hE).trans ?_
  gcongr
  exact ((coefSum_primorial hz1 hb ρ).2 hnd)

end LeanLab.DensityGoldbach.U1481

