module

public import Mathlib
public import LeanLab.GoldbachGaps.Sumset
public import LeanLab.Dudek2014.Statements

/-!
Connection sweep 2026-10-19, candidate C2, unit U-5467, T2 FRONTIER, CLOUD 20261019T1116Z-cloud23.

I-5020's sumset step `Sumset.core` needs one odd prime `p` with
`x - (4 · 10^18 - 1478) ≤ p ≤ x + 1475`. Under RH, Dudek 2014 Theorem 2, P0100, puts a prime in
`(x - (4/π) √x log x, x]` for every `x ≥ 2`, and `(4/π) √x log x ≤ 4 · 10^18 - 1478` up to
about `1.69 · 10^33`. So under RH, with the `4 · 10^18` even check and the maximal gap 1476:
every `(x, x + 1478]` with `2 ≤ x ≤ 1.6 · 10^33` holds a Goldbach number. The unconditional
`Sumset.goldbach_gap_1478_all` stops at `7.86 · 10^27`; `goldbach_10`'s `10 log² x` is about
`4 · 10^4` to `5.8 · 10^4` in this range.

Inputs, cited, not proved here: `hD`, Dudek's Theorem 2 conclusion, which the lab has as
`Dudek2014.theorem2` under RH, cited, and as `Dudek2014.Section22.theorem2_of_lemma4`
CONDITIONAL ON Lemma 4, the page 5 Σ bounds and Schoenfeld; `EvenGoldbachUpTo (4 · 10^18)`;
`GapBound1476`. KNOWN in method, I-5020's search; the explicit RH range is not claimed new.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach stays OPEN.
-/

@[expose] public section

namespace LeanLab.GoldbachGaps.DudekRH
open Real LeanLab.GoldbachGaps LeanLab.GoldbachGaps.Sumset

set_option exponentiation.threshold 3000 in
theorem log_ten_lt : Real.log 10 < 2.30261 := by
  have hn : (10 : ℕ) ^ 643 < 2 ^ 2136 := by norm_num
  have h : (10 : ℝ) ^ 643 < 2 ^ 2136 := by exact_mod_cast hn
  have h' := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h'
  push_cast at h'
  have := Real.log_two_lt_d9
  linarith

/-- `(4/π) √x log x ≤ 3.99 · 10^18` for `1 ≤ x ≤ 1.6 · 10^33`. -/
theorem dudekH_le {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 1.6e33) :
    LeanLab.Dudek2014.dudekH x ≤ 3.99e18 := by
  unfold LeanLab.Dudek2014.dudekH
  have hl : Real.log x ≤ 78.29 := by
    have a := Real.log_le_log (by linarith) (h2.trans (by norm_num : (1.6e33 : ℝ) ≤ 10 ^ 34))
    rw [Real.log_pow] at a
    have := log_ten_lt; push_cast at a; linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg h1
  have hs : √x ≤ 4e16 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num at h2 ⊢; linarith
  have hs0 := Real.sqrt_nonneg x
  have hpi := Real.pi_gt_d6
  have hq : 4 / π ≤ 1.273241 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hq0 : 0 ≤ 4 / π := by positivity
  calc 4 / π * √x * Real.log x ≤ 1.273241 * 4e16 * 78.29 := by
        apply mul_le_mul (mul_le_mul hq hs hs0 (by norm_num)) hl hl0 (by norm_num)
    _ ≤ 3.99e18 := by norm_num

/-- **Under RH, a Goldbach number in every `(x, x + 1478]` for `2 ≤ x ≤ 1.6 · 10^33`**,
CONDITIONAL ON Dudek's Theorem 2 conclusion `hD`, the `4 · 10^18` even check and the maximal
gap 1476. -/
theorem goldbach_gap_1478_RH (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hG : GapBound1476)
    (hD : ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x)
    {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 1.6e33) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1478 := by
  rcases le_or_gt x (4 * 10 ^ 18 - 2) with hs | hb
  · obtain ⟨n, hev, hlo, hhi⟩ := even_above x (by linarith)
    have hn4 : 4 ≤ n := by
      have : (2 : ℝ) < n := by linarith
      have h2 : 2 < n := by exact_mod_cast this
      rcases hev with ⟨k, hk⟩; omega
    have hnN : n ≤ 4 * 10 ^ 18 := by
      have : (n : ℝ) ≤ 4 * 10 ^ 18 := by linarith
      exact_mod_cast this
    exact ⟨n, ⟨hev, hE n hev hn4 hnN⟩, hlo, by linarith⟩
  · obtain ⟨p, hp, hpl, hpu⟩ := hD x hx
    have hH := dudekH_le (x := x) (by linarith) hx'
    have hp3 : 3 ≤ p := by
      have : (3 : ℝ) ≤ p := by linarith
      exact_mod_cast this
    exact core hG hp hp3 (by linarith) (by linarith)

/-- The same in the RH form: `hD2` is Dudek's Theorem 2 as an implication from RH, the
statement of the lab's cited `Dudek2014.theorem2`, taken as a hypothesis, so no unproved statement
enters; CONDITIONAL ON RH, `hD2`, the even check and the gap table. -/
theorem goldbach_gap_1478_of_RH (hRH : RiemannHypothesis)
    (hD2 : RiemannHypothesis → ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hG : GapBound1476)
    {x : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 1.6e33) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1478 :=
  goldbach_gap_1478_RH hE hG (hD2 hRH) hx hx'

/-- **Under RH, every `(x, x + max 1478 (10 log² x)]`, `x ≥ 2`, holds a Goldbach number**,
CONDITIONAL ON Dudek's Theorem 2 conclusion, the `4 · 10^18` check, `GapBound1476` and `hG10`,
the conclusion of the lab's `ChirreHagen2025.goldbach_10`, stated with that file's Goldbach
number, a sum of two odd primes. Up to `1.6 · 10^33` the length is `1478`. -/
theorem goldbach_gap_RH_all (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hG : GapBound1476)
    (hD : ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x)
    (hG10 : ∀ x : ℝ, 2 ≤ x → ∃ n : ℕ, (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p + q = n)
      ∧ x < n ∧ (n : ℝ) < x + 10 * Real.log x ^ 2)
    {x : ℝ} (hx : 2 ≤ x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + max 1478 (10 * Real.log x ^ 2) := by
  rcases le_or_gt x 1.6e33 with hs | hb
  · obtain ⟨n, hn, h1, h2⟩ := goldbach_gap_1478_RH hE hG hD hx hs
    exact ⟨n, hn, h1, by have := le_max_left (1478 : ℝ) (10 * Real.log x ^ 2); linarith⟩
  · obtain ⟨n, ⟨p, q, hp, hq, op, oq, rfl⟩, h1, h2⟩ := hG10 x hx
    refine ⟨p + q, ⟨op.add_odd oq, p, q, hp, hq, rfl⟩, h1, ?_⟩
    have := le_max_right (1478 : ℝ) (10 * Real.log x ^ 2)
    linarith

end LeanLab.GoldbachGaps.DudekRH

