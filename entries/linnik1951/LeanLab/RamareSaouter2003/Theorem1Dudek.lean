module

public import LeanLab.RamareSaouter2003.Statements
public import LeanLab.Dudek2014.SigmaTrudgianDownstream

/-!
P0099, unit U-6550, CLOUD 20261020T1518Z-cloud45, 2026-10-20.
Ramaré-Saouter 2003 Theorem 1, under RH a prime in `]x - (8/5) √x log x, x]` for `x ≥ 2`,
follows from Dudek 2014 Theorem 2, the shorter interval `]x - (4/π) √x log x, x]`, since
`4/π < 8/5`. So Theorem 1 is CONDITIONAL ON exactly the inputs of the lab's Dudek chain:
`theorem1_of_dudekInputs` on `DudekInputs Z`, and `theorem1_of_trudgian` on Lemma 4 for the zero
sum `Zr γ`, `TrudgianN70 γ` and Schoenfeld's ψ - θ bounds.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.RamareSaouter2003
open Real LeanLab.Dudek2014 LeanLab.Dudek2014.Section22 LeanLab.Dudek2014.Downstream

/-- `4/π < 8/5`, from `π > 3.14`. -/
lemma four_div_pi_lt : 4 / π < 8 / 5 := by
  rw [div_lt_div_iff₀ pi_pos (by norm_num)]
  linarith [pi_gt_d2]

/-- Dudek's interval is inside Ramaré-Saouter's: `(4/π) √x log x ≤ (8/5) √x log x` for `x ≥ 1`. -/
lemma dudekH_le {x : ℝ} (hx : 1 ≤ x) : dudekH x ≤ 8 / 5 * √x * Real.log x := by
  unfold dudekH
  have h0 : 0 ≤ √x * Real.log x := mul_nonneg (sqrt_nonneg x) (Real.log_nonneg hx)
  have := mul_le_mul_of_nonneg_right four_div_pi_lt.le h0
  linarith [mul_assoc (4 / π) (√x) (Real.log x), mul_assoc (8 / 5 : ℝ) (√x) (Real.log x)]

/-- **Theorem 1 from Dudek's Theorem 2**: the RH short interval `8/5` follows from `4/π`. -/
theorem theorem1_of_dudek (h : ∀ x : ℝ, 2 ≤ x → PrimeInDudekInterval x) :
    ∀ x : ℝ, 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x - 8 / 5 * √x * Real.log x < p ∧ (p : ℝ) ≤ x := by
  intro x hx
  obtain ⟨p, hp, hl, hu⟩ := h x hx
  exact ⟨p, hp, by linarith [dudekH_le (x := x) (by linarith)], hu⟩

/-- Theorem 1, CONDITIONAL ON Dudek's inputs for a zero sum `Z`. -/
theorem theorem1_of_dudekInputs {Z : ℝ → ℝ} (hD : DudekInputs Z) :
    ∀ x : ℝ, 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x - 8 / 5 * √x * Real.log x < p ∧ (p : ℝ) ≤ x :=
  theorem1_of_dudek (Downstream.theorem2 hD)

/-- Theorem 1, CONDITIONAL ON Lemma 4 for the critical line zero sum `Zr γ`, Trudgian's `N(T)`
bound for `γ` from `T = 70`, and Schoenfeld's ψ - θ bounds. -/
theorem theorem1_of_trudgian {ι : Type*} {γ : ι → ℝ} (h4 : Lemma4 (SigmaT.Zr γ))
    (hN : SigmaT.TrudgianN70 γ) (hSch : Schoenfeld) :
    ∀ x : ℝ, 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x - 8 / 5 * √x * Real.log x < p ∧ (p : ℝ) ≤ x :=
  theorem1_of_dudek (SigmaT.theorem2_of_trudgian h4 hN hSch)

end LeanLab.RamareSaouter2003
