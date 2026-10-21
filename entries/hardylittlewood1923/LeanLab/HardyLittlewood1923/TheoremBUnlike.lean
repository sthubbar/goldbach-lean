module

public import LeanLab.HardyLittlewood1923.TheoremBAll

/-!
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5902, paper P0004.

# Hardy-Littlewood 1923, Theorem B, (3.31): the unlike parity case

Paper p. 29: if `r ≥ 3` and `n`, `r` are of unlike parity, then `ν_r(n) = o(n^{r-1})`.
Proof: a sum of `r` odd primes has the parity of `r`, so every tuple counted by `ν_r(n)` has an
entry equal to `2`; `TheoremC.card_small_union` counts such tuples by `3 r (n+1)^{r-2}`, and each
carries weight at most `(log n)^r`. No hypothesis. Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.HardyLittlewood1923

open Real Finset Filter

/-- Unlike parity: every tuple has an entry below `3`. -/
lemma Nr_unlike_le (s n : ℕ) (h : n % 2 ≠ (s + 2) % 2) :
    Nr (s + 2) n ≤ (s + 2) * (3 * (n + 1) ^ s) := by
  rw [Nr_eq]
  refine le_trans (card_le_card fun t ht => ?_) (card_small_union s n 3)
  rw [mem_filter]
  refine ⟨ht, ?_⟩
  rw [mem_Sr] at ht
  by_contra hall
  push_neg at hall
  have hodd : ∀ i, (t i) % 2 = 1 := fun i =>
    Nat.odd_iff.mp (((ht.2.1 i).eq_two_or_odd').resolve_left (by have := hall i; omega))
  have key : ∀ m : ℕ, ∀ u : Fin m → ℕ, (∀ i, u i % 2 = 1) → (∑ i, u i) % 2 = m % 2 := by
    intro m
    induction m with
    | zero => intro u _; simp
    | succ m ih =>
      intro u hu
      rw [Fin.sum_univ_succ, Nat.add_mod, ih (fun i => u i.succ) (fun i => hu i.succ), hu 0]
      omega
  exact h (ht.2.2 ▸ key _ t hodd)

/-- **Hardy-Littlewood 1923, Theorem B, (3.31)**, explicit form:
for `n`, `r` of unlike parity, `ν_r(n) ≤ 3 r (n+1)^{r-2} (log n)^r`. -/
theorem nur_unlike_le (s n : ℕ) (h : n % 2 ≠ (s + 2) % 2) :
    nur (s + 2) n ≤ 3 * (s + 2) * ((n : ℝ) + 1) ^ s * Real.log n ^ (s + 2) := by
  refine (nur_le (s + 2) n).trans ?_
  have h1 : (Nr (s + 2) n : ℝ) ≤ (s + 2) * (3 * ((n : ℝ) + 1) ^ s) := by
    exact_mod_cast Nr_unlike_le s n h
  have h2 : 0 ≤ Real.log n ^ (s + 2) := pow_nonneg (Real.log_natCast_nonneg n) _
  calc (Nr (s + 2) n : ℝ) * Real.log n ^ (s + 2)
      ≤ (s + 2) * (3 * ((n : ℝ) + 1) ^ s) * Real.log n ^ (s + 2) := by gcongr
    _ = 3 * (s + 2) * ((n : ℝ) + 1) ^ s * Real.log n ^ (s + 2) := by ring

/-- **Theorem B, (3.31)**: `ν_r(n) = o(n^{r-1})` for `r ≥ 3` and `n`, `r` of unlike parity. -/
theorem theoremB_unlike : ∀ r : ℕ, 3 ≤ r → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ,
    n % 2 ≠ r % 2 → n₀ ≤ n → nur r n ≤ ε * (n : ℝ) ^ (r - 1) := by
  intro r hr ε hε
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    (small_pow_log s (s + 2) (3 * (s + 2)) ε (by positivity) hε)
  refine ⟨n₀, fun n hpar hn => ?_⟩
  rw [show s + 2 - 1 = s + 1 by omega]
  exact (nur_unlike_le s n hpar).trans (hn₀ n hn)

end LeanLab.HardyLittlewood1923

