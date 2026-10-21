module

public import Mathlib

/-!
# `k! e_k(x) ≤ (Σ x_p)^k`

Lab proof, unit U-5325, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics,
Maclaurin's elementary bound. With `Bonferroni.weighted_dev` it bounds the error of Brun's pure sieve
truncated at `r` by `(Σ_{p ∈ P} g(p))^{r+1}/(r + 1)!`.

* `esymm_succ_insert`: `e_{k+1}(P ∪ {a}) = e_{k+1}(P) + x_a e_k(P)` for `a ∉ P`;
* `pow_ge_two_terms`: `S^k + k y S^{k-1} ≤ (S + y)^k` for `S, y ≥ 0`;
* `factorial_mul_esymm_le`: `k! Σ_{T ⊆ P, |T| = k} ∏_T x_p ≤ (Σ_P x_p)^k` for `x ≥ 0`.
-/

@[expose] public section


namespace LeanLab.PNTSieve.Bonferroni

open Finset

variable {α : Type*} [DecidableEq α]

/-- `e_k(x; P) = Σ_{T ⊆ P, |T| = k} ∏_T x_p`. -/
def esymm (x : α → ℝ) (P : Finset α) (k : ℕ) : ℝ := ∑ T ∈ P.powersetCard k, ∏ p ∈ T, x p

lemma esymm_nonneg (x : α → ℝ) (hx : ∀ p, 0 ≤ x p) (P : Finset α) (k : ℕ) : 0 ≤ esymm x P k :=
  sum_nonneg fun T _ => prod_nonneg fun p _ => hx p

lemma esymm_zero (x : α → ℝ) (P : Finset α) : esymm x P 0 = 1 := by simp [esymm]

lemma esymm_empty_succ (x : α → ℝ) (k : ℕ) : esymm x ∅ (k + 1) = 0 := by
  rw [esymm, Finset.powersetCard_eq_empty.mpr (by simp)]; simp

lemma esymm_succ_insert (x : α → ℝ) {a : α} {P : Finset α} (ha : a ∉ P) (k : ℕ) :
    esymm x (insert a P) (k + 1) = esymm x P (k + 1) + x a * esymm x P k := by
  unfold esymm
  rw [powersetCard_succ_insert ha, sum_union]
  · congr 1
    rw [sum_image]
    · rw [mul_sum]
      refine sum_congr rfl (fun T hT => ?_)
      have : a ∉ T := fun h => ha ((mem_powersetCard.mp hT).1 h)
      rw [prod_insert this]
    · intro T₁ h₁ T₂ h₂ he
      have n₁ : a ∉ T₁ := fun h => ha ((mem_powersetCard.mp h₁).1 h)
      have n₂ : a ∉ T₂ := fun h => ha ((mem_powersetCard.mp h₂).1 h)
      simpa [n₁, n₂] using congrArg (fun U => U.erase a) he
  · rw [disjoint_left]
    intro T h1 h2
    obtain ⟨U, _, rfl⟩ := mem_image.mp h2
    exact ha ((mem_powersetCard.mp h1).1 (mem_insert_self a U))

lemma pow_ge_two_terms (S y : ℝ) (hS : 0 ≤ S) (hy : 0 ≤ y) (k : ℕ) :
    S ^ (k + 1) + (k + 1) * y * S ^ k ≤ (S + y) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : 0 ≤ S + y := by linarith
      calc S ^ (k + 1 + 1) + (↑(k + 1) + 1) * y * S ^ (k + 1)
          ≤ (S + y) * (S ^ (k + 1) + (k + 1) * y * S ^ k) := by
            push_cast
            have : 0 ≤ (k + 1 : ℝ) * y * y * S ^ k := by positivity
            have e : (S + y) * (S ^ (k + 1) + (k + 1) * y * S ^ k) =
                S ^ (k + 1 + 1) + ((k : ℝ) + 1 + 1) * y * S ^ (k + 1) + (k + 1) * y * y * S ^ k := by
              ring
            rw [e]; linarith
        _ ≤ (S + y) * (S + y) ^ (k + 1) := mul_le_mul_of_nonneg_left ih h1
        _ = (S + y) ^ (k + 1 + 1) := by ring

/-- `k! e_k(x) ≤ (Σ_P x_p)^k` for `x ≥ 0`. -/
theorem factorial_mul_esymm_le (x : α → ℝ) (hx : ∀ p, 0 ≤ x p) (P : Finset α) (k : ℕ) :
    (k.factorial : ℝ) * esymm x P k ≤ (∑ p ∈ P, x p) ^ k := by
  induction P using Finset.induction_on generalizing k with
  | empty =>
      rcases k with _ | k
      · simp [esymm_zero]
      · rw [esymm_empty_succ]; simp
  | insert a P ha ih =>
      rcases k with _ | k
      · simp [esymm_zero]
      · rw [esymm_succ_insert x ha, sum_insert ha]
        set S := ∑ p ∈ P, x p
        have hS : 0 ≤ S := sum_nonneg fun p _ => hx p
        have h1 := ih (k + 1)
        have h2 := ih k
        have hpow := pow_ge_two_terms S (x a) hS (hx a) k
        have hek := esymm_nonneg x hx P k
        rw [Nat.factorial_succ]
        push_cast
        have hxa := hx a
        have : ((k : ℝ) + 1) * k.factorial * (x a * esymm x P k) ≤ (k + 1) * x a * S ^ k := by
          have := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ (k + 1) * x a by positivity)
          nlinarith
        rw [add_comm S (x a)] at hpow
        have h1' : ((k : ℝ) + 1) * k.factorial * esymm x P (k + 1) ≤ S ^ (k + 1) := by
          have h := h1; rw [Nat.factorial_succ] at h; push_cast at h; linarith
        linarith

end LeanLab.PNTSieve.Bonferroni

