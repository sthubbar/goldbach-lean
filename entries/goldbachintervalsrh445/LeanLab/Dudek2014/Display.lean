module

public import Mathlib
public import LeanLab.Dudek2014.Theorem2

/-!
P0100 Dudek 2014, Section 2.2, pages 4 to 6: the page 6 display `Display22` derived from the
paper's named analytic inputs, stated as Props:
- `Lemma5`: `Σ Λ(n) w(n) = h - Σ/h + ε(h)` with `|ε(h)| < 48/(5h)`, `Σ` the sum over zeros;
- `SigmaBd`: `|Σ| ≤ |Σ₁| + |Σ₂|` with (7) and the Σ₂ bound at `α = 2`, page 5, both under RH;
- `Schoenfeld`: `0.98 √y < ψ(y) - θ(y) < 1.11 √y + 3 y^{1/3}` for `y ≥ 121`, page 6.
The zero sum `Σ(x, h)` is an abstract function `S`, since the lab has no zeta zeros; the three
Props are exactly the paper's cited steps. With `Theorem2.lean`, Theorem 2 for every `x ≥ 2`
is CONDITIONAL ON these three inputs only.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.Section22
open Real Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- `ψ(y) = Σ_{n ≤ y} Λ(n)`. -/
def psiF (y : ℝ) : ℝ := ∑ n ∈ Iic ⌊y⌋₊, Λ n

/-- `θ(y) = Σ_{p ≤ y} log p`. -/
def thetaF (y : ℝ) : ℝ := ∑ p ∈ (Iic ⌊y⌋₊).filter Nat.Prime, log p

/-- The weight `w(n) = 1 - |n - x|/h` on `(x - h, x + h)`, else `0`. -/
def w (x h : ℝ) (n : ℕ) : ℝ := max 0 (1 - |(n : ℝ) - x| / h)

/-- `Σ_n Λ(n) w(n)`, all `n ≤ x + h`. -/
def WS (x h : ℝ) : ℝ := ∑ n ∈ Iic ⌊x + h⌋₊, Λ n * w x h n

/-- Cited, Lemma 5 for `0 < h < x`, with the zero sum `S x h`. -/
def Lemma5 (S : ℝ → ℝ → ℝ) : Prop :=
  ∀ x h : ℝ, 0 < h → h < x → |WS x h - (h - S x h / h)| < 48 / (5 * h)

/-- Cited, page 5 under RH: (7) and the Σ₂ bound at `α = 2`, for `h = (2/π)√x log x`. -/
def SigmaBd (S : ℝ → ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 65000 ≤ x →
    |S x (hD x)| ≤ (2 * x * hD x / (π * √(x - hD x)) +
      4 * hD x * (x + hD x) ^ (3 / 2 : ℝ) / (π * 2 * x)) * log (2 * x / hD x)

/-- Cited, Schoenfeld 1976 Theorem 14 and (5.5), page 6. -/
def Schoenfeld : Prop :=
  ∀ y : ℝ, 121 ≤ y →
    0.98 * √y < psiF y - thetaF y ∧ psiF y - thetaF y < 1.11 * √y + 3 * y ^ (1 / 3 : ℝ)

theorem sum_Iic_sub {f : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Iic b, f n - ∑ n ∈ Iic a, f n = ∑ n ∈ Ioc a b, f n := by
  rw [← Iic_union_Ioc_eq_Iic hab, sum_union (Iic_disjoint_Ioc le_rfl)]; ring

/-- `hD x ≤ x / 2` and `x - hD x ≥ 121` for `x ≥ 65000`. -/
theorem hD_small {x : ℝ} (hx : 65000 ≤ x) : 0 < hD x ∧ hD x ≤ x / 2 := by
  have hx0 : 0 < x := by linarith
  have ht : 254 ≤ √x := by rw [le_sqrt (by norm_num) hx0.le]; linarith
  have hL : 11.07 ≤ log x := le_trans log_65000 (log_le_log (by norm_num) hx)
  have hLt : log x = 2 * log √x := by
    conv_lhs => rw [← sq_sqrt hx0.le]
    rw [log_pow]; push_cast; ring
  have hL2 : log x ^ 2 ≤ 0.9 * √x := by rw [hLt]; nlinarith [log_sq_le ht]
  have hLlin : log x ≤ 0.0813 * √x := by nlinarith
  obtain ⟨-, hc2⟩ := pi_bounds
  have hs2 : √x ^ 2 = x := sq_sqrt hx0.le
  constructor
  · unfold hD; have := pi_pos; positivity
  · unfold hD
    have h1 : 2 / π * √x * log x ≤ 0.63662 * √x * (0.0813 * √x) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hc2 (by linarith)) hLlin (by linarith)
        (by positivity)
    nlinarith

/-- **`Display22` from Lemma 5, the Σ bounds and Schoenfeld's bounds.** -/
theorem display_of {S : ℝ → ℝ → ℝ} (h5 : Lemma5 S) (hS : SigmaBd S) (hSch : Schoenfeld) :
    Display22 := by
  intro x hx
  obtain ⟨hh0, hhx⟩ := hD_small hx
  set h := hD x with hhdef
  have hx0 : 0 < x := by linarith
  have hlo : (121 : ℝ) ≤ x - h := by linarith
  have hab : ⌊x - h⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  -- Lemma 5 and the Σ bound
  have hW : h - (2 / π * (x / √(x - h) + (x + h) ^ (3 / 2 : ℝ) / x) * log (2 * x / h))
      - 48 / (5 * h) < WS x h := by
    have h1 := h5 x h hh0 (by linarith)
    have h2 := hS x hx
    rw [← hhdef] at h2
    have hpi := pi_pos
    have hsq : 0 < √(x - h) := sqrt_pos.2 (by linarith)
    have e : (2 * x * h / (π * √(x - h)) + 4 * h * (x + h) ^ (3 / 2 : ℝ) / (π * 2 * x)) *
        log (2 * x / h) / h =
        2 / π * (x / √(x - h) + (x + h) ^ (3 / 2 : ℝ) / x) * log (2 * x / h) := by
      field_simp; ring
    have h3 : S x h / h ≤ |S x h| / h := div_le_div_of_nonneg_right (le_abs_self _) hh0.le
    have h4 : |S x h| / h ≤ 2 / π * (x / √(x - h) + (x + h) ^ (3 / 2 : ℝ) / x) *
        log (2 * x / h) := by
      rw [← e]; exact div_le_div_of_nonneg_right h2 hh0.le
    have := (abs_lt.1 h1).1
    linarith
  -- WS ≤ Σ_{x-h<n≤x+h} Λ(n)
  have hWle : WS x h ≤ ∑ n ∈ Ioc ⌊x - h⌋₊ ⌊x + h⌋₊, Λ n := by
    unfold WS
    rw [← Iic_union_Ioc_eq_Iic hab, sum_union (Iic_disjoint_Ioc le_rfl)]
    have hz : ∑ n ∈ Iic ⌊x - h⌋₊, Λ n * w x h n = 0 := by
      apply sum_eq_zero
      intro n hn
      rw [mem_Iic] at hn
      have hnr : (n : ℝ) ≤ x - h := by
        have := Nat.floor_le (show 0 ≤ x - h by linarith)
        have : (n : ℝ) ≤ ⌊x - h⌋₊ := by exact_mod_cast hn
        linarith
      have hw : w x h n = 0 := by
        unfold w
        apply max_eq_left
        rw [sub_nonpos, le_div_iff₀ hh0, one_mul, abs_of_nonpos (by linarith)]
        linarith
      rw [hw, mul_zero]
    rw [hz, zero_add]
    apply sum_le_sum
    intro n _
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have hw1 : w x h n ≤ 1 := by
      unfold w
      apply max_le (by norm_num)
      have : 0 ≤ |(n : ℝ) - x| / h := div_nonneg (abs_nonneg _) hh0.le
      linarith
    nlinarith [show 0 ≤ w x h n from le_max_left _ _]
  -- ψ and θ differences
  have hpsi : psiF (x + h) - psiF (x - h) = ∑ n ∈ Ioc ⌊x - h⌋₊ ⌊x + h⌋₊, Λ n :=
    sum_Iic_sub hab
  have htheta : thetaF (x + h) - thetaF (x - h) =
      ∑ p ∈ (Ioc ⌊x - h⌋₊ ⌊x + h⌋₊).filter Nat.Prime, log p := by
    unfold thetaF
    rw [sum_filter, sum_filter, sum_filter]
    exact sum_Iic_sub hab
  obtain ⟨hA1, -⟩ := hSch (x - h) hlo
  obtain ⟨-, hB2⟩ := hSch (x + h) (by linarith)
  rw [← htheta]
  unfold rhs
  rw [← hhdef]
  linarith

/-- **Theorem 2 for every `x ≥ 2`, CONDITIONAL ON Lemma 5, the page 5 Σ bounds and
Schoenfeld's ψ - θ bounds**, the paper's own cited inputs. -/
theorem theorem2_of_inputs {S : ℝ → ℝ → ℝ} (h5 : Lemma5 S) (hS : SigmaBd S)
    (hSch : Schoenfeld) : ∀ x : ℝ, 2 ≤ x → PrimeInDudekInterval x :=
  theorem2_of_display (display_of h5 hS hSch)

end

end LeanLab.Dudek2014.Section22

