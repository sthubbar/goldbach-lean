module

public import Mathlib
public import GoldbachLean.Saouter1998.Goldbach

/-!
# The prime ladder reduction

If binary Goldbach holds up to `B` and odd primes `3 = p₀ < p₁ < ... < p_k` have every gap at most
`B - 2`, then ternary Goldbach holds up to `p_k + B`: for odd `n` take a rung `p` with
`4 ≤ n - p ≤ B` and write `n - p` as a sum of two primes. This is the principle of Section 2 of
Saouter's paper and of Section 3 of Helfgott and Platt, in the sharp form.
AI wrote the Lean code: Claude by Anthropic for most files, Codex for Theorem 1 and the statement of Lemma 1, Gemini and Antigravity agents for parts of the Lemma 1 proof; it is checked only by the Lean kernel. Ternary Goldbach is
Helfgott's theorem, binary Goldbach is open.
-/

@[expose] public section

namespace GoldbachLean.Saouter1998.Ladder

/-- One rung, sharp form: the next prime is larger and at most `B - 2` above. -/
def Step2 (B a b : ℕ) : Prop := a < b ∧ b ≤ a + (B - 2)

/-- One step: an odd `n` with `a + 4 ≤ n ≤ a + B`, `a` an odd prime, is a sum of three primes. -/
theorem ternary_step {B : ℕ} (hB : EvenGoldbachUpTo B) {a n : ℕ} (ha : a.Prime) (ha3 : 3 ≤ a)
    (hn : Odd n) (h1 : a + 4 ≤ n) (h2 : n ≤ a + B) : IsTernarySum n := by
  have hao : Odd a := ha.odd_of_ne_two (by omega)
  have he : Even (n - a) := Nat.Odd.sub_odd hn hao
  obtain ⟨p, q, hp, hq, hpq⟩ := hB (n - a) he (by omega) (by omega)
  exact ⟨a, p, q, ha, hp, hq, by omega⟩

theorem getLastD_cons' (a b : ℕ) (t : List ℕ) : (b :: t).getLastD a = t.getLastD b := by
  cases t with
  | nil => rfl
  | cons c t => simp [List.getLastD]

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

end GoldbachLean.Saouter1998.Ladder
