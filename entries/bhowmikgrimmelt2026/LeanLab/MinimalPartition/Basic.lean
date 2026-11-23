module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
Kernel-checked value of the smallest prime in a
Goldbach partition, OEIS A020481, at the record 2k = 3807404.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel, no native_decide.
-/

@[expose] public section

namespace LeanLab.MinimalPartition

/-- `hasDivFrom n fuel d` is `true` when some `m ≥ d` with `m * m ≤ n` divides `n`. -/
def hasDivFrom (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d => if n < d * d then false else if n % d = 0 then true else hasDivFrom n fuel (d + 1)

theorem hasDivFrom_sound (n : ℕ) : ∀ fuel d, hasDivFrom n fuel d = true →
    ∃ m, d ≤ m ∧ m * m ≤ n ∧ m ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [hasDivFrom] at h
  | succ k ih =>
    intro d h
    simp only [hasDivFrom] at h
    by_cases h1 : n < d * d
    · simp [h1] at h
    · simp only [h1, if_false] at h
      by_cases h2 : n % d = 0
      · exact ⟨d, le_rfl, by omega, Nat.dvd_of_mod_eq_zero h2⟩
      · simp only [h2, if_false] at h
        obtain ⟨m, hm, hmm, hdvd⟩ := ih (d + 1) h
        exact ⟨m, by omega, hmm, hdvd⟩

theorem not_prime_of_hasDiv {n : ℕ} (h : hasDivFrom n n 2 = true) : ¬ n.Prime := by
  obtain ⟨m, hm, hmm, hdvd⟩ := hasDivFrom_sound n n 2 h
  intro hp
  rcases hp.eq_one_or_self_of_dvd m hdvd with h1 | h1
  · omega
  · subst h1
    have : m * 2 ≤ m * m := Nat.mul_le_mul_left m hm
    have := hp.two_le
    omega

/-- For every `p < B`: `p < 2`, or `p` has a divisor, or `N - p` has a divisor. -/
def noSmaller (N : ℕ) : ℕ → Bool
  | 0 => true
  | B + 1 => (decide (B < 2) || hasDivFrom B B 2 || hasDivFrom (N - B) (N - B) 2) && noSmaller N B

theorem noSmaller_sound (N : ℕ) : ∀ B, noSmaller N B = true →
    ∀ p < B, p.Prime → ¬ (N - p).Prime := by
  intro B
  induction B with
  | zero => intro _ p hp; omega
  | succ k ih =>
    intro h p hp hpp
    simp only [noSmaller, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases Nat.lt_or_ge p k with hlt | hge
    · exact ih h2 p hlt hpp
    · have : p = k := by omega
      subst this
      rcases h1 with (h1 | h1) | h1
      · exact absurd hpp.two_le (by omega)
      · exact absurd hpp (not_prime_of_hasDiv h1)
      · exact not_prime_of_hasDiv h1

/-- A020481 at `2k = 3807404` is `751`: `751` and `3807404 - 751 = 3806653` are prime, and no
smaller prime `p` has `3807404 - p` prime. This is a record of `a(k) / (log 2k)^2 ≈ 3.27`. -/
theorem a_3807404 :
    IsLeast {p : ℕ | p.Prime ∧ (3807404 - p).Prime} 751 := by
  refine ⟨⟨primeB_sound (by decide +kernel), primeB_sound (by decide +kernel)⟩, ?_⟩
  intro p ⟨hp, hq⟩
  by_contra hlt
  push_neg at hlt
  exact noSmaller_sound 3807404 751 (by decide +kernel) p hlt hp hq

end LeanLab.MinimalPartition
