module

public import LeanLab.Romanov.Final

/-!
# Romanov's theorem with k ≥ 1, the standard form

Unit U-1080, PC run 20261019T1603Z-20267. AI wrote the Lean code. Known mathematics, Romanov 1934.
No cited input. Binary Goldbach is OPEN.

`romanov` in Final.lean allows `k = 0`, so `p + 1` counts. The usual statement, as in
Romanov 1934 and Erdős 1950, takes `k ≥ 1`. `romanov_pos` derives it: the `k = 0` terms are
the `p + 1`, at most `π(x)` of them below `x`, and Mathlib's Chebyshev bound
`eventually_primeCounting_le` makes `π(x) ≤ (c/2) x` for large `x`.

* `romanov_pos`: an absolute `c > 0` and `X₀` such that for every `x ≥ X₀` at least `c x`
  numbers below `x` are `p + 2^k` with `p` prime and `k ≥ 1`. PROVED.
-/

@[expose] public section


namespace LeanLab.Romanov

open Finset Real Filter

attribute [local instance] Classical.propDecidable

/-- `π(x) ≤ ε x` for all large natural `x`, from Mathlib's Chebyshev upper bound. -/
lemma eventually_pi_le {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → (Nat.primeCounting x : ℝ) ≤ ε * x := by
  have h1 := Chebyshev.eventually_primeCounting_le (ε := 1) one_pos
  have h2 : ∀ᶠ x : ℝ in atTop, (log 4 + 1) / ε ≤ log x :=
    tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨X, hX⟩ := eventually_atTop.mp (h1.and (h2.and (eventually_gt_atTop 1)))
  refine ⟨⌈X⌉₊, fun x hx => ?_⟩
  have hxX : X ≤ (x : ℝ) := (Nat.ceil_le.mp hx)
  obtain ⟨hpi, hlog, hx1⟩ := hX x hxX
  rw [Nat.floor_natCast] at hpi
  have hlogpos : 0 < log (x : ℝ) := log_pos hx1
  have hc : 0 < log 4 + 1 := by have := log_nonneg (show (1:ℝ) ≤ 4 by norm_num); linarith
  calc (Nat.primeCounting x : ℝ) ≤ (log 4 + 1) * x / log x := hpi
    _ ≤ ε * x := by
      rw [div_le_iff₀ hlogpos]
      have hx0 : (0:ℝ) ≤ x := Nat.cast_nonneg _
      have : log 4 + 1 ≤ ε * log x := by
        rw [div_le_iff₀ hε] at hlog; linarith
      nlinarith

/-- **Romanov's theorem, `k ≥ 1`**: the numbers `p + 2^k`, `p` prime, `k ≥ 1`, have positive
lower density. PROVED, no cited input. -/
theorem romanov_pos : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∃ I : Finset ℕ,
    (∀ n ∈ I, n < x ∧ ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p + 2 ^ k) ∧ c * x ≤ #I := by
  obtain ⟨c, hc, h⟩ := romanov
  obtain ⟨X₁, hX₁⟩ := eventually_pi_le (half_pos hc)
  refine ⟨c / 2, half_pos hc, max 16 X₁, fun x hx => ?_⟩
  obtain ⟨I, hI, hcard⟩ := h x (le_of_max_le_left hx)
  set J := I.filter (fun n => ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p + 2 ^ k) with hJ
  refine ⟨J, fun n hn => ?_, ?_⟩
  · rw [hJ, mem_filter] at hn
    exact ⟨(hI n hn.1).1, hn.2⟩
  · -- the rest of `I` is made of `p + 1`
    have hsub : I \ J ⊆ (Nat.primesBelow x).image (· + 1) := by
      intro n hn
      obtain ⟨hnI, hnJ⟩ := Finset.mem_sdiff.mp hn
      obtain ⟨hnx, p, k, hp, rfl⟩ := hI n hnI
      have hk : k = 0 := by
        by_contra hk0
        exact hnJ (Finset.mem_filter.mpr ⟨hnI, p, k, hp, Nat.one_le_iff_ne_zero.mpr hk0, rfl⟩)
      subst hk
      rw [mem_image]
      refine ⟨p, ?_, by simp⟩
      rw [Nat.mem_primesBelow]
      exact ⟨by simp at hnx; omega, hp⟩
    have hrest : #(I \ J) ≤ Nat.primeCounting x := by
      calc #(I \ J) ≤ #((Nat.primesBelow x).image (· + 1)) := card_le_card hsub
        _ ≤ #(Nat.primesBelow x) := card_image_le
        _ = Nat.primeCounting' x := Nat.primesBelow_card_eq_primeCounting' x
        _ ≤ Nat.primeCounting x := Nat.monotone_primeCounting' (Nat.le_succ x)
    have hsplit : #I = #(I \ J) + #J := by
      rw [card_sdiff_add_card_eq_card (filter_subset _ _)]
    have hpi := hX₁ x (le_of_max_le_right hx)
    have h1 : (#I : ℝ) = #(I \ J) + #J := by exact_mod_cast hsplit
    have h2 : (#(I \ J) : ℝ) ≤ Nat.primeCounting x := by exact_mod_cast hrest
    linarith

end LeanLab.Romanov
