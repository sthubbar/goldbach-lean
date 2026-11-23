module

public import Mathlib
public import LeanLab.Dudek2014.Display

/-!
P0100 Dudek 2014, page 4: identity (5) and Lemma 5 from Lemma 4.
- (5): `Σ Λ(n) w(n) = (ψ₁(x + h) - 2ψ₁(x) + ψ₁(x - h))/h`, `ψ₁(y) = Σ_{n≤y} (y - n) Λ(n)`,
  PROVED for `0 < h ≤ x`, from the pointwise identity
  `h w(n) = (x + h - n)₊ - 2(x - n)₊ + (x - h - n)₊`.
- Lemma 5 from Lemma 4: with `ψ₁(y) = y²/2 - Z(y) - y log 2π + ε(y)` and `|ε(y)| ≤ 2.393`,
  the second difference gives `Σ Λ w = h - Σ/h + ε(h)`, `|ε(h)| ≤ 4 · 2.393/h < 48/(5h)`,
  with `Σ = Z(x+h) - 2Z(x) + Z(x-h)`, the paper's zero sum. The cited Lemma 4 is taken for all
  `y > 0` with the paper's computed constant `2 + 2^{3/2}(2 + γ - log 4π) + (1/2) log(27/16)
  < 2.393` (`lemma4_const` pieces), the continuous extension of the paper's non-integer case.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.Section22
open Real Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- `ψ₁(y) = Σ_{n ≤ y} (y - n) Λ(n)`. -/
def psi1 (y : ℝ) : ℝ := ∑ n ∈ Iic ⌊y⌋₊, (y - n) * Λ n

/-- Lemma 4 with `Z(y) = Σ_ρ y^{ρ+1}/(ρ(ρ+1))`, for all `y > 0`, constant `2.393`. Cited when this
file was written; PROVED for `Zpatch` since 2026-10-20 as `PNTPort.ExplicitPsi1.Trivial.lemma4_Zpatch`,
verified PC U-1245. -/
def Lemma4 (Z : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → |psi1 y - (y ^ 2 / 2 - Z y - y * log (2 * π))| ≤ 2.393

theorem psi1_ext {y : ℝ} (hy : 0 ≤ y) {N : ℕ} (hN : ⌊y⌋₊ ≤ N) :
    ∑ n ∈ Iic N, max (y - n) 0 * Λ n = psi1 y := by
  unfold psi1
  rw [← Iic_union_Ioc_eq_Iic hN, sum_union (Iic_disjoint_Ioc le_rfl)]
  have h2 : ∑ n ∈ Ioc ⌊y⌋₊ N, max (y - n) 0 * Λ n = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [mem_Ioc] at hn
    have : y < n := by
      have := Nat.lt_floor_add_one y
      have : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn.1
      push_cast at this; linarith
    rw [max_eq_right (by linarith), zero_mul]
  rw [h2, add_zero]
  apply sum_congr rfl
  intro n hn
  rw [mem_Iic] at hn
  have : (n : ℝ) ≤ y := by
    have := Nat.floor_le hy
    have : (n : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hn
    linarith
  rw [max_eq_left (by linarith)]

theorem w_identity {x h : ℝ} (hh : 0 < h) (r : ℝ) :
    h * max 0 (1 - |r - x| / h) = max (x + h - r) 0 - 2 * max (x - r) 0 + max (x - h - r) 0 := by
  have e : h * max 0 (1 - |r - x| / h) = max 0 (h - |r - x|) := by
    rw [mul_max_of_nonneg _ _ hh.le, mul_zero]; congr 1; field_simp
  rw [e]
  rcases le_total r x with hr | hr
  · rw [abs_of_nonpos (by linarith)]
    simp only [max_def]; split_ifs <;> linarith
  · rw [abs_of_nonneg (by linarith)]
    simp only [max_def]; split_ifs <;> linarith

/-- **Identity (5)**, `0 < h ≤ x`. MATCHES. -/
theorem identity5 {x h : ℝ} (hh : 0 < h) (hhx : h ≤ x) :
    WS x h = (psi1 (x + h) - 2 * psi1 x + psi1 (x - h)) / h := by
  have hN1 : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  have hN2 : ⌊x - h⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  rw [← psi1_ext (by linarith) le_rfl, ← psi1_ext (by linarith) hN1,
    ← psi1_ext (by linarith) hN2, eq_div_iff hh.ne', mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  unfold WS
  rw [sum_mul]
  apply sum_congr rfl
  intro n _
  unfold w
  have := w_identity (x := x) hh (n : ℝ)
  linear_combination (Λ n) * this

/-- **Lemma 5 from Lemma 4**, with `Σ = Z(x+h) - 2Z(x) + Z(x-h)`. -/
theorem lemma5_of {Z : ℝ → ℝ} (h4 : Lemma4 Z) :
    Lemma5 (fun x h => Z (x + h) - 2 * Z x + Z (x - h)) := by
  intro x h hh hhx
  have e1 := h4 (x + h) (by linarith)
  have e2 := h4 x (by linarith)
  have e3 := h4 (x - h) (by linarith)
  rw [identity5 hh hhx.le]
  set E := psi1 (x + h) - 2 * psi1 x + psi1 (x - h) -
    (h ^ 2 - (Z (x + h) - 2 * Z x + Z (x - h))) with hE
  have hEb : |E| ≤ 4 * 2.393 := by
    have k : E = (psi1 (x + h) - ((x + h) ^ 2 / 2 - Z (x + h) - (x + h) * log (2 * π)))
        - 2 * (psi1 x - (x ^ 2 / 2 - Z x - x * log (2 * π)))
        + (psi1 (x - h) - ((x - h) ^ 2 / 2 - Z (x - h) - (x - h) * log (2 * π))) := by
      rw [hE]; ring
    rw [k]
    have a1 := abs_le.1 e1; have a2 := abs_le.1 e2; have a3 := abs_le.1 e3
    rw [abs_le]; constructor <;> linarith
  have e : (psi1 (x + h) - 2 * psi1 x + psi1 (x - h)) / h -
      (h - (Z (x + h) - 2 * Z x + Z (x - h)) / h) = E / h := by
    rw [hE]; field_simp
  rw [e, abs_div, abs_of_pos hh, show (48 : ℝ) / (5 * h) = (48 / 5) / h by field_simp,
    div_lt_div_iff_of_pos_right hh]
  linarith

/-- **Theorem 2 for every `x ≥ 2`, CONDITIONAL ON Lemma 4, the page 5 Σ bounds and
Schoenfeld's ψ - θ bounds.** -/
theorem theorem2_of_lemma4 {Z : ℝ → ℝ} (h4 : Lemma4 Z)
    (hS : SigmaBd (fun x h => Z (x + h) - 2 * Z x + Z (x - h))) (hSch : Schoenfeld) :
    ∀ x : ℝ, 2 ≤ x → PrimeInDudekInterval x :=
  theorem2_of_inputs (lemma5_of h4) hS hSch

end

end LeanLab.Dudek2014.Section22

