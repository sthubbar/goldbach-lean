module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.HelfgottPlatt.Ladder
public import LeanLab.HelfgottPlatt.Proth

/-!
Helfgott and Platt 2013, P0006, unit U-6816, run 20261021T0316Z-cloud57.
The ladder reduction in its sharp form and Theorem 4.1 from the paper's own range structure.

1. Sharp gap: binary Goldbach to B plus odd prime rungs with every gap at most B - 2, not B - 4
   as in the lab's Ladder.lean, already gives ternary Goldbach to the top rung plus B. The gap B - 2 is
   exactly what the paper's Section 3 algorithm yields: it takes the largest Proth prime strictly
   below N0 + Δ, and two odd numbers differing by less than an even Δ differ by at most Δ - 2.
   With Δ = 4e18 this is the binary bound of P0005 exactly, with no room to spare.
2. Section 4 range structure: T = 492700 ranges of width W = 2^54 · 10^9; in each range a ladder
   that starts at most 2e18 above the left end point and ends strictly within 2e18 of the right
   end point. Theorem 4.1 follows from binary Goldbach to 4e18 and these 492700 ladders alone,
   with no lower ternary range, since the junction between ranges is itself a gap below 4e18.
   No ordering of the ranges or inclusion of a ladder in its range is needed.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN.

This file is the lab file `LeanLab/HelfgottPlatt/HelfgottPlattU6816Sharp.lean` in module syntax,
without `step2_of_ladderStep` and `chain_step2_of_chain`, which relate the sharp rung condition
to the weaker one of the lab ladder file and which no compared theorem uses, and without the
unused import `LeanLab.HelfgottPlatt.PaperNumbers`.
-/

@[expose] public section

namespace LeanLab.HelfgottPlatt.U6816

open LeanLab.HelfgottPlatt LeanLab.HelfgottPlatt.Proth

/-- One rung, sharp form: the next prime is larger and at most `B - 2` above. -/
def Step2 (B a b : ℕ) : Prop := a < b ∧ b ≤ a + (B - 2)

/-- Section 3, steps 2 to 4: the next rung is an odd prime strictly below `N0 + Δ`, `Δ` even,
so the gap is at most `Δ - 2`. -/
theorem algorithm_step {Δ N0 N1 : ℕ} (h0 : N0.Prime) (h1 : N1.Prime) (h03 : 3 ≤ N0)
    (hlt : N0 < N1) (hΔ : N1 < N0 + Δ) (hΔe : Even Δ) : Step2 Δ N0 N1 := by
  obtain ⟨x, hx⟩ := h0.odd_of_ne_two (by omega)
  obtain ⟨y, hy⟩ := h1.odd_of_ne_two (by omega)
  obtain ⟨z, hz⟩ := hΔe
  exact ⟨hlt, by omega⟩

/-- Base: binary Goldbach to `B` gives ternary Goldbach to `B + 3`, as `3 + (n - 3)`. -/
theorem base {B : ℕ} (hB : EvenGoldbachUpTo B) : TernaryGoldbachUpTo (B + 3) := by
  intro n hn h7 hnB
  have he : Even (n - 3) := Nat.Odd.sub_odd hn (by decide)
  obtain ⟨p, q, hp, hq, hpq⟩ := hB (n - 3) he (by omega) (by omega)
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-- The sharp ladder lemma, by induction along the ladder. -/
theorem ternary_of_ladder2_aux {B : ℕ} (hB : EvenGoldbachUpTo B) :
    ∀ (t : List ℕ) (a : ℕ), a.Prime → 3 ≤ a → (∀ p ∈ t, p.Prime) →
      (a :: t).IsChain (Step2 B) →
      ∀ n, Odd n → a + 4 ≤ n → n ≤ t.getLastD a + B → IsTernarySum n := by
  intro t
  induction t with
  | nil =>
    intro a ha ha3 _ _ n hn h1 h2
    exact ternary_step hB ha ha3 hn h1 (by simpa using h2)
  | cons b t ih =>
    intro a ha ha3 ht hc n hn h1 h2
    rw [List.isChain_cons_cons] at hc
    obtain ⟨⟨hab, hba⟩, hc⟩ := hc
    have hbp : b.Prime := ht b (by simp)
    by_cases hnb : b + 4 ≤ n
    · exact ih b hbp (by omega) (fun p hp => ht p (List.mem_cons_of_mem _ hp)) hc n hn hnb
        (by rw [getLastD_cons'] at h2; exact h2)
    · obtain ⟨x, hx⟩ := hn
      obtain ⟨y, hy⟩ := hbp.odd_of_ne_two (by omega)
      exact ternary_step hB ha ha3 ⟨x, hx⟩ h1 (by omega)

/-- The sharp ladder lemma from 3. -/
theorem ternary_of_ladder2 {B X : ℕ} (hB : EvenGoldbachUpTo B) (t : List ℕ)
    (ht : ∀ p ∈ t, p.Prime) (hc : (3 :: t).IsChain (Step2 B))
    (hX : X ≤ t.getLastD 3 + B) : TernaryGoldbachUpTo X := by
  intro n hn h7 hnX
  exact ternary_of_ladder2_aux hB t 3 Nat.prime_three le_rfl ht hc n hn (by omega) (by omega)

/-- The sharp ladder lemma from a lower ternary range `A` with `p₀ + 2 ≤ A`, the weakest
overlap that works, since the next odd number after `A` is then at least `p₀ + 4`. -/
theorem ternary_of_lower_and_ladder2 {B A X p₀ : ℕ} (hB : EvenGoldbachUpTo B)
    (hA : TernaryGoldbachUpTo A) (hp : p₀.Prime) (h3 : 3 ≤ p₀) (hpA : p₀ + 2 ≤ A)
    (t : List ℕ) (ht : ∀ p ∈ t, p.Prime) (hc : (p₀ :: t).IsChain (Step2 B))
    (hX : X ≤ t.getLastD p₀ + B) : TernaryGoldbachUpTo X := by
  intro n hn h7 hnX
  by_cases hnA : n ≤ A
  · exact hA n hn h7 hnA
  · have h4 : p₀ + 4 ≤ n := by
      obtain ⟨x, hx⟩ := hn
      obtain ⟨y, hy⟩ := hp.odd_of_ne_two (by omega)
      omega
    exact ternary_of_ladder2_aux hB t p₀ hp h3 ht hc n hn h4 (by omega)

/-! ### Section 4: the 492,700 ranges -/

/-- The range width of Section 4, `2^54 · 10^9`, as a numeral. -/
def W : ℕ := 18014398509481984000000000

theorem W_eq : W = 2 ^ 54 * 10 ^ 9 := by norm_num [W]

theorem T_eq_RW : T = 492700 * W := by norm_num [T, W]

/-- The ladder of range `i`: odd prime rungs with gaps at most `4e18 - 2`, starting at most
`2e18` above the left end point `i W` and ending strictly within `2e18` of the right end point
`(i + 1) W`. Nothing else is assumed, not even that the rungs lie in the range. -/
def RangeOK (i : ℕ) (l : List ℕ) : Prop :=
  ∃ h t, l = h :: t ∧ h.Prime ∧ 3 ≤ h ∧ (∀ p ∈ t, p.Prime) ∧
    (h :: t).IsChain (Step2 (4 * 10 ^ 18)) ∧ h ≤ i * W + 2 * 10 ^ 18 ∧
    (i + 1) * W < t.getLastD h + 2 * 10 ^ 18

/-- The last rung is at least the first. -/
theorem last_ge {B : ℕ} : ∀ (t : List ℕ) (a : ℕ), (a :: t).IsChain (Step2 B) → a ≤ t.getLastD a
  | [], _, _ => le_rfl
  | b :: t, a, hc => by
    rw [List.isChain_cons_cons] at hc
    rw [getLastD_cons']
    exact le_trans (Nat.le_of_lt hc.1.1) (last_ge t b hc.2)

theorem getLastD_mem : ∀ (c : ℕ) (u : List ℕ), u.getLastD c ∈ c :: u
  | c, [] => by simp
  | c, d :: u => by
    rw [getLastD_cons']
    exact List.mem_cons_of_mem _ (getLastD_mem d u)

/-- Ranges `0, ..., r - 1` give ternary Goldbach to `r W + 2e18 + 1`. -/
theorem upTo_ranges (hB : EvenGoldbachUpTo (4 * 10 ^ 18)) (L : ℕ → List ℕ) :
    ∀ r : ℕ, (∀ i < r, RangeOK i (L i)) → TernaryGoldbachUpTo (r * W + 2 * 10 ^ 18 + 1) := by
  intro r
  induction r with
  | zero =>
    intro _ n hn h7 hnX
    exact base hB n hn h7 (by simp at hnX; omega)
  | succ r ih =>
    intro hL
    have hA := ih (fun i hi => hL i (by omega))
    obtain ⟨h, t, -, hp, h3, ht, hc, hstart, hend⟩ := hL r (by omega)
    have hW : W = 18014398509481984000000000 := rfl
    have hpA : h + 2 ≤ r * W + 2 * 10 ^ 18 + 1 := by
      obtain ⟨y, hy⟩ := hp.odd_of_ne_two (by omega)
      rw [hW] at hstart ⊢
      omega
    refine ternary_of_lower_and_ladder2 hB hA hp h3 hpA t ht hc ?_
    have hodd : Odd (t.getLastD h) := by
      have hge := last_ge t h hc
      have hpl : (t.getLastD h).Prime := by
        cases t with
        | nil => exact hp
        | cons c u =>
          rw [getLastD_cons']
          exact ht _ (getLastD_mem c u)
      exact hpl.odd_of_ne_two (by omega)
    obtain ⟨y, hy⟩ := hodd
    rw [hW] at hend ⊢
    rw [hy] at hend ⊢
    omega

/-- Theorem 4.1, CONDITIONAL ON binary Goldbach to 4e18 and the 492,700 range ladders of
Section 4: every odd number from 7 to T is a sum of three primes. -/
theorem theorem4_1_of_ranges (hB : EvenGoldbachUpTo (4 * 10 ^ 18)) (L : ℕ → List ℕ)
    (hL : ∀ i < 492700, RangeOK i (L i)) : TernaryGoldbachUpTo T := by
  have h := upTo_ranges hB L 492700 hL
  rw [T_eq_RW]
  intro n hn h7 hnT
  have hle : n ≤ 492700 * W + 2 * 10 ^ 18 + 1 := le_trans hnT (by omega)
  exact h n hn h7 hle

end LeanLab.HelfgottPlatt.U6816

