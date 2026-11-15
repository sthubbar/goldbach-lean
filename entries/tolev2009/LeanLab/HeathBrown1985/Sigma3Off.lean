module

public import Mathlib
public import LeanLab.HeathBrown1985.Statements

/-!
P0096 Heath-Brown 1985, pages 55 to 56, the off-diagonal inner sum for Σ₃: a sum of
`Δ_Q(j + r n)` over an interval of `n` is a difference of two class sums mod `r`
(the caveat on 2.7), and its bound from Lemma 1, 2.7, with the terms `Q L²` and `x L^{-A}` kept.
PROVED here, fully proved.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset

attribute [local instance] Classical.propDecidable

/-- `Σ_{a < n ≤ b} f(j + r n)` as a difference of two class sums `n ≡ j (mod r)`. -/
theorem sum_Ioc_class_eq (f : ℕ → ℝ) (j r a b : ℕ) (hr : 1 ≤ r) (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, f (j + r * n) =
      apSum f ((j + r * b : ℕ) : ℝ) r j - apSum f ((j + r * a : ℕ) : ℝ) r j := by
  simp only [apSum, Nat.floor_natCast]
  have e : ∀ N : ℕ, Icc 1 N = Ioc 0 N := fun N => by ext k; simp only [mem_Icc, mem_Ioc]; omega
  rw [e, e, sum_filter, sum_filter]
  have hle : j + r * a ≤ j + r * b := by have := Nat.mul_le_mul_left r hab; omega
  rw [← sum_Ioc_consecutive _ (Nat.zero_le (j + r * a)) hle, add_sub_cancel_left,
    ← sum_filter]
  have himg : (Ioc (j + r * a) (j + r * b)).filter (fun k => k % r = j % r) =
      (Ioc a b).image (fun n => j + r * n) := by
    ext k
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hjk : j ≤ k := by omega
      have hd : r ∣ k - j := (Nat.modEq_iff_dvd' hjk).mp h3.symm
      obtain ⟨n, hn⟩ := hd
      refine ⟨n, ⟨?_, ?_⟩, by omega⟩
      · by_contra hc
        push Not at hc
        have := Nat.mul_le_mul_left r hc
        omega
      · by_contra hc
        push Not at hc
        have := Nat.mul_le_mul_left r (Nat.succ_le_of_lt hc)
        rw [Nat.mul_succ] at this
        omega
    · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := Nat.mul_le_mul_left r (Nat.succ_le_of_lt h1); rw [Nat.mul_succ] at this; omega
      · have := Nat.mul_le_mul_left r h2; omega
      · simp [Nat.add_mul_mod_self_left]
  rw [himg, sum_image]
  intro n₁ _ n₂ _ h
  have : r * n₁ = r * n₂ := by simpa using h
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

/-- The Lemma 1 (2.7) bound at one class-sum endpoint `y`. -/
def lemma17Err (K A Q : ℝ) (y : ℝ) (k l : ℕ) : ℝ :=
  K * (Q * Real.log y ^ 2 + y * Real.log y / (k * Q) * (Nat.gcd k l : ℝ) *
    (k.divisors.card : ℝ) + y * Real.log y ^ (-A))

/-- The caveat on 2.7: the interval sum `Σ_{a < n ≤ b} Δ_Q(j + r n)` is bounded by the
2.7 bound at both endpoints `y₁ = j + r a`, `y₂ = j + r b`, all three terms kept. -/
theorem abs_sum_Ioc_DeltaQ_le (h7 : Lemma1_7) (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, ∀ Q : ℝ, 1 ≤ Q → ∀ j r a b : ℕ, 1 ≤ r → a ≤ b →
      (2 : ℝ) ≤ (j + r * a : ℕ) → Q ≤ (j + r * a : ℕ) → (r : ℝ) ≤ (j + r * a : ℕ) →
      |∑ n ∈ Ioc a b, DeltaQ Q (j + r * n)| ≤
        lemma17Err K A Q ((j + r * b : ℕ) : ℝ) r j + lemma17Err K A Q ((j + r * a : ℕ) : ℝ) r j := by
  obtain ⟨K, hK⟩ := h7 A hA
  refine ⟨K, fun Q hQ j r a b hr hab h2 hQy hry => ?_⟩
  have hle : ((j + r * a : ℕ) : ℝ) ≤ ((j + r * b : ℕ) : ℝ) := by
    have := Nat.mul_le_mul_left r hab; exact_mod_cast (by omega : j + r * a ≤ j + r * b)
  rw [sum_Ioc_class_eq _ j r a b hr hab]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · exact hK _ (h2.trans hle) Q hQ (hQy.trans hle) r j hr (hry.trans hle)
  · exact hK _ h2 Q hQ hQy r j hr hry

end LeanLab.HeathBrown1985
