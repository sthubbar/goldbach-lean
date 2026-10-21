module

public import LeanLab.SchnirelmannExplicit.Sharper
public import LeanLab.Ramare1995.Theorem91

/-!
Explicit Schnirelmann constant halved by Dyson's theorem, unit U-0243.
The basis step of Sharper.lean used Schnirelmann's inequality, order `2 ⌈1/α⌉`. The covering
case of Dyson's theorem, proved in Ramare1995/Theorem91.lean, gives order `⌈1/α⌉`: if `0 ∈ A`
and `α m ≥ 1` with `α ≤ σ(A)`, then every natural number is a sum of `m` elements of `A`.
This is the classical corollary of Mann's theorem. KNOWN mathematics; Goldbach stays open.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0803Z-2223. Checked only by the Lean kernel.
-/

@[expose] public section

open Finset
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannExplicit.DysonBasis

open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannExplicit LeanLab.SchnirelmannExplicit.Sharper
open LeanLab.Ramare1995.Section9 LeanLab.Ramare1995.Theorem91

lemma sum_mem_nsmul (A : Set ℕ) : ∀ (m : ℕ) (f : ℕ → ℕ), (∀ i < m, f i ∈ A) →
    ∑ i ∈ range m, f i ∈ m • A
  | 0, f, _ => by simp
  | m + 1, f, hf => by
    rw [sum_range_succ, succ_nsmul]
    exact Set.add_mem_add (sum_mem_nsmul A m f fun i hi => hf i (by omega)) (hf m (by omega))

lemma cnt_ge (A : Set ℕ) (k : ℕ) : schnirelmannDensity A * k ≤ cnt A k := by
  have h := @schnirelmannDensity_mul_le_card_filter A _ k
  have e : ({a ∈ Ioc 0 k | a ∈ A} : Finset ℕ) = {a ∈ Icc 1 k | a ∈ A} := by
    ext a; simp only [mem_filter, mem_Ioc, mem_Icc]
    by_cases ha : a ∈ A
    · simp only [ha, and_true]; omega
    · simp [ha]
  unfold cnt; rw [← e]; exact h

/-- **Basis theorem of order `⌈1/α⌉` from Dyson.** If `0 ∈ A`, `α ≤ σ(A)` and `α m ≥ 1`, every
natural number is a sum of `m` elements of `A`. -/
theorem nsmul_eq_univ_dyson (A : Set ℕ) (hA : 0 ∈ A) (α : ℝ)
    (hσ : α ≤ schnirelmannDensity A) (m : ℕ) (hm : 1 ≤ α * m) : m • A = Set.univ := by
  obtain ⟨h, rfl⟩ : ∃ h, m = h + 1 := by
    rcases m with _ | h
    · simp at hm; linarith
    · exact ⟨h, rfl⟩
  ext n
  simp only [Set.mem_univ, iff_true]
  have hD : DysonHyp (fun _ => A) (h + 1) n := by
    intro k hk1 _
    simp only [phi, sum_const, card_range, smul_eq_mul]
    have h1 := cnt_ge A k
    have hα0 : 0 ≤ α := by
      by_contra hneg; replace hneg := not_le.mp hneg
      have : α * ((h + 1 : ℕ) : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le (by positivity)
      linarith
    have : (k : ℝ) ≤ ((h + 1) * cnt A k : ℕ) := by
      push_cast
      have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have h2 : α * k ≤ cnt A k := (mul_le_mul_of_nonneg_right hσ (by positivity)).trans h1
      push_cast at hm
      nlinarith
    exact_mod_cast this
  obtain ⟨f, hf, hs⟩ := dyson h n (fun _ => A) hD
  rw [← hs]
  exact sum_mem_nsmul A (h + 1) f fun i hi => by
    rcases hf i hi with h0 | h1
    · rw [h0]; exact hA
    · exact h1

/-- The halved constant `H₂ = 2 K₁ + 2`. -/
def H₂ : ℕ := 2 * K₁ + 2

lemma H₂_eq : H₂ = 12168431812 := by norm_num [H₂, K₁]

/-- **Schnirelmann's theorem, explicit, with Dyson's basis step.** Every integer `n ≥ 2` is a
sum of at most `H₂ = 12168431812` primes, about `1.22 · 10^10`, half of `H₁`. -/
theorem schnirelmann_bounded_primes_dyson :
    ∀ n : ℕ, 2 ≤ n → ∃ k ≤ H₂, SumOfPrimes k n := by
  have hh : K₁ • ({0, 1} ∪ G : Set ℕ) = Set.univ :=
    nsmul_eq_univ_dyson ({0, 1} ∪ G : Set ℕ) (Or.inl (Or.inl rfl)) α₁
      (by convert α₁_le_density) K₁ one_le_α₁_mul_K₁
  intro n hn
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · exact ⟨1, by norm_num [H₂], [2], rfl, by simp [Nat.prime_two], rfl⟩
  · exact ⟨1, by norm_num [H₂], [3], rfl, by simp [Nat.prime_three], rfl⟩
  · have hmem : n - 2 ∈ K₁ • ({0, 1} ∪ G : Set ℕ) := by rw [hh]; trivial
    obtain ⟨l, hl, hlA, hls⟩ := exists_list_of_mem_nsmul _ K₁ (n - 2) hmem
    obtain ⟨k, hk, hs⟩ := list_step l hlA 2 le_rfl
    rw [hls, show n - 2 + 2 = n by omega] at hs
    exact ⟨k, by unfold H₂; omega, hs⟩

lemma H₂_lt_H₁ : 2 * H₂ < H₁ + 4 := by norm_num [H₂, H₁, K₁]

end LeanLab.SchnirelmannExplicit.DysonBasis
