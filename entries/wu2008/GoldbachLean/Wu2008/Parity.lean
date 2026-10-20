module

public import GoldbachLean.Wu2008.Real

/-!
T3, unit U-1131, route R-0017, PC run 20261020T0003Z-10609. P0043 Wu 2008 Lemma 2.2, Υ₁₁ repaired:
the pointwise weight is parity blind. In the real exponent model of Wu2008Lemma22Real.lean, for any
admissible κ₁, κ₂, the right side of (2.2) at one a equals 4 both when a is a prime with exponent
e ≥ 1/3, `rhs_prime`, and when a = q₁q₂ with both exponents at least 1/3, `rhs_semiprime`. So a lower
bound built from this weight gives a large prime N − p and a semiprime N − p with two factors above
N^{1/3} exactly the same credit: Chen's method counts Ω ≤ 2, never Ω = 1. This is Selberg's parity
barrier seen in Wu's own weight; it extends R-5050, which showed the same for Lemma 2.1.
Numerics, numerics/r0017_parity_mass.py: at N = 10^7 the weight's mass on squarefree sifted a is
47.6 percent on primes, 27.2 percent on semiprimes with both factors above N^{1/3}, every one of them
weighted exactly 4, 30.9 percent on other semiprimes and −5.7 percent on Ω ≥ 3.
KNOWN mathematics. Route BLOCKED by parity. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace GoldbachLean.Wu2008.WuReal
open Finset

@[expose] public noncomputable section
open scoped Classical

section
variable {k1 k2 : ℝ} (hA : Admissible k1 k2)
include hA

lemma consts : k1 < k2 ∧ k2 < em k1 ∧ em k1 ≤ e13 ∧ 0 < k1 := by
  have := hA.1; have := hA.2.1; have := hA.2.2.1
  refine ⟨hA.2.1, ?_, ?_, ?_⟩
  · unfold em; linarith
  · unfold em e13; linarith
  · linarith

/-- A prime `a` with exponent `e ≥ 1/3` gets weight 4. -/
theorem rhs_prime {e : ℝ} (he : e13 ≤ e) : rhs k1 k2 {e} = 4 := by
  obtain ⟨c1, c2, c3, c4⟩ := consts hA
  have z2 : ∀ (P : ℝ × ℝ → Prop) [DecidablePred P], (∀ x y : ℝ, x = e → y = e → ¬ P (x, y)) →
      #(({e} ×ˢ {e} : Finset (ℝ × ℝ)).filter P) = 0 := by
    intro P _ h; rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨x, y⟩ hxy; simp only [mem_product, mem_singleton] at hxy; exact h x y hxy.1 hxy.2
  have z4 : ∀ (P : ℝ × ℝ × ℝ × ℝ → Prop) [DecidablePred P], (∀ x y : ℝ, x = e → y = e → ∀ t, ¬ P (x, y, t)) →
      #((quads {e}).filter P) = 0 := by
    intro P _ h; rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨x, y, t⟩ hxy; simp only [quads, mem_product, mem_singleton] at hxy
    exact h x y hxy.1 hxy.2.1 t
  unfold rhs U2 U3 U4 U5 U6 U7 U8 U9 U10 U11
  rw [z2 _ (fun x y hx hy h => by subst hx; subst hy; linarith [h.1]),
    z2 _ (fun x y hx hy h => by subst hx; subst hy; linarith [h.2.1, h.2.2.1]),
    z2 _ (fun x y hx hy h => by subst hx; subst hy; linarith [h.1]),
    z2 _ (fun x y hx hy h => by subst hx; subst hy; linarith [h.1, h.2.1]),
    z2 _ (fun x y hx hy h => by subst hx; subst hy; linarith [h.2.1, h.2.2.1]),
    z4 _ (fun x y hx hy t h => by subst hx; subst hy; linarith [h.1]),
    z4 _ (fun x y hx hy t h => by subst hx; subst hy; linarith [h.1])]
  have f3 : ({e} : Finset ℝ).filter (· < e13) = ∅ := by
    rw [filter_eq_empty_iff]; intro x hx; simp only [mem_singleton] at hx; subst hx; linarith
  have f4 : ({e} : Finset ℝ).filter (· < em k1) = ∅ := by
    rw [filter_eq_empty_iff]; intro x hx; simp only [mem_singleton] at hx; subst hx; linarith
  rw [f3, f4, if_pos (by intro q hq; simp only [mem_singleton] at hq; subst hq; linarith)]
  simp

/-- A squarefree `a = q₁q₂` with both exponents at least `1/3` gets weight 4. -/
theorem rhs_semiprime {e₁ e₂ : ℝ} (h1 : e13 ≤ e₁) (h12 : e₁ < e₂) : rhs k1 k2 {e₁, e₂} = 4 := by
  obtain ⟨c1, c2, c3, c4⟩ := consts hA
  have mem : ∀ x, x ∈ ({e₁, e₂} : Finset ℝ) → e13 ≤ x := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> linarith
  have z2 : ∀ (P : ℝ × ℝ → Prop) [DecidablePred P], (∀ x y : ℝ, e13 ≤ x → e13 ≤ y → ¬ P (x, y)) →
      #((({e₁, e₂} : Finset ℝ) ×ˢ {e₁, e₂}).filter P) = 0 := by
    intro P _ h; rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨x, y⟩ hxy; rw [mem_product] at hxy; exact h x y (mem x hxy.1) (mem y hxy.2)
  have z4 : ∀ (P : ℝ × ℝ × ℝ × ℝ → Prop) [DecidablePred P],
      (∀ x y : ℝ, e13 ≤ x → e13 ≤ y → ∀ t, ¬ P (x, y, t)) →
      #((quads ({e₁, e₂} : Finset ℝ)).filter P) = 0 := by
    intro P _ h; rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨x, y, t⟩ hxy; simp only [quads, mem_product] at hxy
    exact h x y (mem x hxy.1) (mem y hxy.2.1) t
  have he : e13 = 1 / 3 := rfl
  unfold rhs U2 U3 U4 U5 U6 U7 U8 U9 U10 U11
  rw [z2 _ (fun x y hx hy h => by linarith [h.2]),
    z2 _ (fun x y hx hy h => by linarith [h.2.1]),
    z2 _ (fun x y hx hy h => by linarith [h.2.2.1]),
    z2 _ (fun x y hx hy h => by linarith [h.1]),
    z2 _ (fun x y hx hy h => by linarith [h.2.1]),
    z4 _ (fun x y hx hy t h => by linarith [h.2.2.2.1, h.2.1, h.2.2.1]),
    z4 _ (fun x y hx hy t h => by linarith [h.2.2.1, h.2.1])]
  have f3 : ({e₁, e₂} : Finset ℝ).filter (· < e13) = ∅ := by
    rw [filter_eq_empty_iff]; intro x hx; have := mem x hx; linarith
  have f4 : ({e₁, e₂} : Finset ℝ).filter (· < em k1) = ∅ := by
    rw [filter_eq_empty_iff]; intro x hx; have := mem x hx; linarith
  rw [f3, f4, if_pos (by intro q hq; have := mem q hq; linarith)]
  simp

end

/-- Vacuity: Wu's constants, a prime with exponent 0.9 and a semiprime with exponents 0.4, 0.5. -/
example : rhs wk1 wk2 {9 / 10} = 4 ∧ rhs wk1 wk2 {2 / 5, 1 / 2} = 4 :=
  ⟨rhs_prime wu_admissible (by unfold e13; norm_num),
    rhs_semiprime wu_admissible (by unfold e13; norm_num) (by norm_num)⟩

end

end GoldbachLean.Wu2008.WuReal

