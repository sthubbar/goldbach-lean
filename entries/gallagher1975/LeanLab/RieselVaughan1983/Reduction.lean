module

public import LeanLab.RieselVaughan1983.Statements
public import LeanLab.Schnirelmann.Mann

/-!
P0032 Riesel-Vaughan 1983, page 45: (1.1) implies the Theorem "in the usual manner".
The usual manner here is Mann's theorem, the lab's `LeanLab.Schnirelmann.Mann.mann_sum`:
the set `B = {m : 2m is a sum of at most two primes}` has Schnirelmann density at least
1/9 by (1.1), so nine copies of `B` cover ℕ and every even `2m` is at most 18 primes.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LeanLab.RieselVaughan1983
open LeanLab.SchnirelmannConstant LeanLab.Schnirelmann.Mann
open LeanLab.Ramare1995.Section9 LeanLab.Ramare1995.Theorem91

/-- `B`: the `m` with `2m` a sum of at most two primes. -/
def B : Set ℕ := {m | AtMostPrimes 2 (2 * m)}

lemma zero_mem_B : 0 ∈ B := AtMostPrimes.zero.mono (by norm_num)

/-- `N(2n)` is at most the number of `m ∈ (0, n]` in `B`. -/
lemma ncount_le_cnt (n : ℕ) : NCount (2 * n : ℝ) ≤ cnt B n := by
  unfold NCount cnt
  have hf : ⌊(2 * n : ℝ)⌋₊ = 2 * n := by exact_mod_cast Nat.floor_natCast (2 * n)
  rw [hf]
  apply Finset.card_le_card_of_injOn (fun k => k / 2)
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨h1, h2⟩, ⟨j, hj⟩, hA⟩ := hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    subst hj
    simp only
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    show AtMostPrimes 2 (2 * ((j + j) / 2))
    have : 2 * ((j + j) / 2) = j + j := by omega
    rw [this]; exact hA
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    obtain ⟨_, ⟨i, hi⟩, _⟩ := ha
    obtain ⟨_, ⟨j, hj⟩, _⟩ := hb
    simp only at hab
    omega

/-- (1.1) gives `σ(B) ≥ 1/9`. -/
lemma density_B (h : Density11) : (1 / 9 : ℝ) ≤ schnirelmannDensity B := by
  apply le_density_of
  intro n hn
  have hx : (2 : ℝ) ≤ 2 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 := h _ hx
  have h2 : (NCount (2 * n : ℝ) : ℝ) ≤ cnt B n := by exact_mod_cast ncount_le_cnt n
  linarith

/-- Sums of `k` members of `B` (or zeros), doubled, are sums of at most `2k` primes. -/
lemma atMost_of_sum (f : ℕ → ℕ) :
    ∀ k : ℕ, (∀ i < k, f i = 0 ∨ f i ∈ B) →
      AtMostPrimes (2 * k) (2 * ∑ i ∈ range k, f i) := by
  intro k
  induction k with
  | zero => intro _; simpa using AtMostPrimes.zero
  | succ k ih =>
    intro hf
    have h1 := ih (fun i hi => hf i (by omega))
    have h2 : AtMostPrimes 2 (2 * f k) := by
      rcases hf k (by omega) with h | h
      · rw [h]; exact AtMostPrimes.zero.mono (by norm_num)
      · exact h
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, sum_range_succ, mul_add]
    exact h1.add h2

/-- **The Theorem from (1.1).** If `N(x) > x/18` for all `x ≥ 2`, every even natural
number is a sum of at most eighteen primes. -/
theorem theorem_of_density11 (h : Density11) : Theorem := by
  intro n hn
  obtain ⟨m, rfl⟩ := hn
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; exact AtMostPrimes.zero.mono (by norm_num)
  have hM := mann_sum (fun _ => B) 8
  have hsum : (1 : ℝ) ≤ ∑ i ∈ range (8 + 1), schnirelmannDensity ((fun _ => B) i) := by
    simp only [sum_const, card_range, nsmul_eq_mul]
    have := density_B h
    push_cast
    linarith
  rw [min_eq_left hsum] at hM
  have h1 : schnirelmannDensity (SumSet (fun _ => B) (8 + 1)) = 1 :=
    le_antisymm schnirelmannDensity_le_one hM
  rw [schnirelmannDensity_eq_one_iff] at h1
  have hmem : m ∈ SumSet (fun _ => B) (8 + 1) := h1 (by simp; omega)
  obtain ⟨f, hf, hs⟩ := hmem
  have := atMost_of_sum f 9 hf
  rw [hs] at this
  simpa [two_mul] using this

/-- **Corollary 19 from (1.1).** Every `n > 1` is a sum of at most nineteen primes. -/
theorem corollary19_of_density11 (h : Density11) : Corollary19 := by
  intro n hn
  have hT := theorem_of_density11 h
  rcases Nat.even_or_odd n with he | ho
  · exact (hT n he).mono (by norm_num)
  · have h3 : 3 ≤ n := by obtain ⟨k, rfl⟩ := ho; omega
    have he : Even (n - 3) := by
      obtain ⟨k, rfl⟩ := ho; exact ⟨k - 1, by omega⟩
    have := (AtMostPrimes.prime Nat.prime_three).add (hT (n - 3) he)
    rw [show 3 + (n - 3) = n by omega] at this
    simpa using this

end LeanLab.RieselVaughan1983
