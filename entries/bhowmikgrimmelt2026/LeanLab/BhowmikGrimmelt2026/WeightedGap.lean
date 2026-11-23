module

public import LeanLab.BhowmikGrimmelt2026.ReducedPairs

/-!
The weighted nearest pair separation in Lemma 7.2, page 26.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

/-- Minimal weighted distance forces every other separated term away from the frequency. -/
theorem weighted_gap {q r R d e : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hqR : q ≤ R) (hrR : r ≤ R) (hd : 0 ≤ d)
    (hsep : 1 / (q * r) ≤ d + e) (hmin : r * e ≤ q * d) :
    1 / 2 ≤ q * R * d := by
  have hs := (div_le_iff₀ (mul_pos hq hr)).mp hsep
  have hm := mul_le_mul_of_nonneg_left hmin hq.le
  have hc := mul_le_mul_of_nonneg_left (add_le_add hqR hrR) (mul_nonneg hq.le hd)
  nlinarith only [hs, hm, hc]

/-- A minimizing reduced pair gives the weighted gap for every distinct pair. -/
theorem reduced_pair_gap {M : ℕ} {R α : ℝ} (hMR : (M : ℝ) ≤ R)
    {p₀ p : Σ _ : ℕ, ℕ} (hp₀ : p₀ ∈ reducedPairs M) (hp : p ∈ reducedPairs M)
    (hne : p ≠ p₀)
    (hmin : (p₀.1 : ℝ) * intDist (α - p₀.2 / p₀.1) ≤
      (p.1 : ℝ) * intDist (α - p.2 / p.1)) :
    1 / 2 ≤ (p.1 : ℝ) * R * intDist (α - p.2 / p.1) := by
  obtain ⟨hq0, hqM, ha, hcop⟩ := (mem_reducedPairs M p).mp hp
  obtain ⟨hr0, hrM, hb, hcop₀⟩ := (mem_reducedPairs M p₀).mp hp₀
  have hqp : (0 : ℝ) < p.1 := by exact_mod_cast hq0
  have hrp : (0 : ℝ) < p₀.1 := by exact_mod_cast hr0
  have hqR : (p.1 : ℝ) ≤ R := (by exact_mod_cast hqM : (p.1 : ℝ) ≤ M).trans hMR
  have hrR : (p₀.1 : ℝ) ≤ R := (by exact_mod_cast hrM : (p₀.1 : ℝ) ≤ M).trans hMR
  have hne' : (p.2, p.1) ≠ (p₀.2, p₀.1) := by
    intro heq
    apply hne
    have h1 := congrArg Prod.snd heq
    have h2 := congrArg Prod.fst heq
    exact Sigma.ext h1 (by simpa using h2)
  have hs := farey_intDist_separation ha hb hcop hcop₀ hne'
  have ht := intDist_sub_le (α - p₀.2 / p₀.1) (α - p.2 / p.1)
  have heq : (α - p₀.2 / p₀.1) - (α - p.2 / p.1) = p.2 / p.1 - p₀.2 / p₀.1 := by ring
  rw [heq] at ht
  exact weighted_gap hqp hrp hqR hrR (intDist_nonneg _) (by simpa only [add_comm] using hs.trans ht) hmin

end LeanLab.BhowmikGrimmelt2026
