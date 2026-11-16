module

public import Mathlib
public import LeanLab.Dudek2014.SmallRange
public import LeanLab.KadiriLumley2014.Corollary

/-!
The conclusion of Dudek's Theorem 2 for `2 ≤ x < 3999999999999999761` without the Riemann
hypothesis, from the maximal prime gap computation of Oliveira e Silva, Herzog and Pardi,
Math. Comp. 83, 2014, taken as the explicit hypothesis `MaxGap1476`: every gap between
consecutive primes up to `4 · 10^18` is at most 1476. The prime `3999999999999999761` is
certified in `KadiriLumley2014/Corollary.lean`. Prime gap tables are the standard way to cover
small `x`; this is a derived result, not a statement of Dudek's paper.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.Dudek2014
open Real

/-- The maximal prime gap of Oliveira e Silva, Herzog and Pardi 2014: if `p < q` are
consecutive primes with `q ≤ 4 · 10^18`, then `q - p ≤ 1476`. A cited computation, taken as a
hypothesis wherever it is used. -/
def MaxGap1476 : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p < q → q ≤ 4 * 10 ^ 18 →
    (∀ r, p < r → r < q → ¬ r.Prime) → q - p ≤ 1476

theorem gaps_huge (hG : MaxGap1476) :
    ∀ n, 2 ≤ n → n ≤ 3999999999999999761 → ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ n < p + 1477 := by
  intro n h2 hn
  by_cases hp : n.Prime
  · exact ⟨n, hp, le_rfl, by omega⟩
  have hP := LeanLab.KadiriLumley2014.pBig
  have hnP : n < 3999999999999999761 := by
    rcases Nat.lt_or_ge n 3999999999999999761 with h | h
    · exact h
    · exact absurd (show n = 3999999999999999761 by omega ▸ hP) hp
  -- p: the largest prime at most n
  have hex : ∃ m, m ≤ n ∧ m.Prime := ⟨2, h2, Nat.prime_two⟩
  set p := Nat.findGreatest Nat.Prime n with hpdef
  have hpP : p.Prime := Nat.findGreatest_spec (P := Nat.Prime) h2 Nat.prime_two
  have hpn : p ≤ n := Nat.findGreatest_le n
  have hpmax : ∀ r, p < r → r ≤ n → ¬ r.Prime := fun r h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  -- q: the least prime above n
  have hq : ∃ q, n < q ∧ q.Prime := ⟨_, hnP, hP⟩
  classical
  set q := Nat.find hq with hqdef
  have hqspec := Nat.find_spec hq
  have hqP : q ≤ 3999999999999999761 := Nat.find_min' hq ⟨hnP, hP⟩
  have hqmin : ∀ r, n < r → r < q → ¬ r.Prime := fun r h1 h2 hr =>
    Nat.find_min hq h2 ⟨h1, hr⟩
  have hgap := hG p q hpP hqspec.2 (by omega) (by omega) (fun r h1 h2 => by
    rcases Nat.lt_or_ge n r with h | h
    · exact hqmin r h h2
    · exact hpmax r h1 h)
  exact ⟨p, hpP, hpn, by omega⟩

/-- Dudek's Theorem 2 conclusion for `2 ≤ x < 3999999999999999761`, no RH. -/
theorem upTo_of_maxGap (hG : MaxGap1476) :
    ∀ x : ℝ, 2 ≤ x → x < 3999999999999999761 → PrimeInDudekInterval x := by
  intro x h2 hx
  rcases lt_or_ge x 67001 with hs | hb
  · exact small_range x h2 hs
  · refine tier 67000 3999999999999999760 1477 (by norm_num) ?_
      (fun n h1 h2' => gaps_huge hG n (by omega) (by omega)) x (by norm_num; linarith) (by norm_num; linarith)
    have hl : 11.09 ≤ Real.log 67000 := by
      have h65 : Real.log 65536 = 16 * Real.log 2 := by
        rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, Real.log_pow]; norm_num
      have := Real.log_le_log (show (0 : ℝ) < 65536 by norm_num) (show (65536 : ℝ) ≤ 67000 by norm_num)
      have := Real.log_two_gt_d9; linarith
    have := dudekH_lb (t := 67000) (s := 258) (l := 11.09) (by norm_num) (by norm_num)
      (by norm_num) hl
    norm_num at this ⊢; linarith

/-- Dudek's Theorem 2 needs RH only for `x ≥ 3999999999999999761`. -/
theorem theorem2_of_maxGap (hG : MaxGap1476)
    (hL : RiemannHypothesis → ∀ x : ℝ, 3999999999999999761 ≤ x → PrimeInDudekInterval x) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x → PrimeInDudekInterval x := by
  intro hRH x hx
  rcases lt_or_ge x 3999999999999999761 with h | h
  · exact upTo_of_maxGap hG x hx h
  · exact hL hRH x h

end LeanLab.Dudek2014
