module

public import Mathlib

/-!
# Sieve counts S(A_e; P(D), y)

Definitions shared by the Wu 2008 Lemma 2.2 development: `Sifted`, `S`, `PS`, as in
LeanLab/ChenDoubleSieve/Lemma41.lean of the Lean Lab, unit U-5400. AI wrote the Lean code.
-/

open Finset

@[expose] public noncomputable section
open scoped Classical

namespace GoldbachLean.Wu2008.WuSieve

/-- `a` survives sifting by `P(D) = {q prime : q ∤ D}` up to `y`. -/
def Sifted (D : ℕ) (y : ℝ) (a : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → (q : ℝ) < y → ¬ q ∣ D → ¬ q ∣ a

/-- `S(A_e; P(D), y)`. -/
def S (A : Finset ℕ) (e D : ℕ) (y : ℝ) : ℕ :=
  #{a ∈ A | e ∣ a ∧ Sifted D y a}

/-- The primes `p` with `w ≤ p < z` and `(p, N) = 1`. -/
def PS (N : ℕ) (w z : ℝ) : Finset ℕ :=
  {p ∈ range ⌈z⌉₊ | p.Prime ∧ w ≤ p ∧ (p : ℝ) < z ∧ p.Coprime N}

lemma S_eq_sum (A : Finset ℕ) (e D : ℕ) (y : ℝ) :
    S A e D y = ∑ a ∈ A, if e ∣ a ∧ Sifted D y a then 1 else 0 := by
  unfold S; rw [card_filter]

lemma sifted_mono {D : ℕ} {y y' : ℝ} (h : y ≤ y') {a : ℕ} (ha : Sifted D y' a) :
    Sifted D y a := fun q hq hqy hqD => ha q hq (lt_of_lt_of_le hqy h) hqD

lemma mem_PS {N : ℕ} {w z : ℝ} {p : ℕ} :
    p ∈ PS N w z ↔ p.Prime ∧ w ≤ p ∧ (p : ℝ) < z ∧ p.Coprime N := by
  unfold PS
  simp only [mem_filter, mem_range, and_iff_right_iff_imp]
  rintro ⟨-, -, hz, -⟩
  exact Nat.lt_ceil.mpr hz

end GoldbachLean.Wu2008.WuSieve
