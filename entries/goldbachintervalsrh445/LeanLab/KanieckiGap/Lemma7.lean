module

public import Mathlib

/-!
P0022 L. Kaniecki 1995, On Šnirelman's constant under the Riemann hypothesis,
Acta Arith. 72, 361-374, page 371, the gap function λ and Lemma 7, and one Section 3
number on page 371. Read from papers/P0022.pdf and its text, cloud session
20261019T1116Z-cloud23, unit U-5462.

Printed: λ(x) = 2 for 0 < x ≤ 7 and λ(x) = max_{p ≤ x} (p' - p) for x > 7, (p, p') consecutive
primes. "Lemma 7. Every interval of the form (x, x + λ(λ(x))), x > 4, contains a sum of two
odd primes."

Here, for integer x:
* `lemma7_printed_false_at_6`: the printed open-interval Lemma 7 fails at x = 6, since
  λ(λ(6)) = λ(2) = 2 and (6, 8) holds no even number.
* `lemma7_closed`: the half-open form (x, x + λ(λ(x))] holds for every integer x > 4,
  by the printed proof with `<` read as `≤` and a repair at x - p₁ = 7, where λ(7) = 2 is
  smaller than the gap 11 - 7.
* `lemma6_at_e78_matches`: Lemma 6's bound at x = e^78 is below the printed
  λ(x) < 4.1926 · 10^19 of Section 3, MATCH.

The paper applies Lemma 7 only through closed intervals [x, x + h], which contain
(x, x + h], so its Theorem is untouched.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.KanieckiGap

/-- The least prime greater than `p`. -/
noncomputable def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

theorem nextPrime_spec (p : ℕ) : p < nextPrime p ∧ (nextPrime p).Prime :=
  let h := Nat.find_spec (Nat.exists_infinite_primes (p + 1)); ⟨by unfold nextPrime; omega, h.2⟩

theorem nextPrime_min {p k : ℕ} (h1 : p < k) (hk : k.Prime) : nextPrime p ≤ k :=
  Nat.find_min' _ ⟨by omega, hk⟩

/-- The gap `p' - p` after `p`. -/
noncomputable def gapAt (p : ℕ) : ℕ := nextPrime p - p

/-- Kaniecki's `λ` at an integer `x`: `2` for `x ≤ 7`, else the largest gap `p' - p`
over primes `p ≤ x`. At `x = 0` the paper leaves `λ` undefined; the value is unused. -/
noncomputable def lam (x : ℕ) : ℕ :=
  if x ≤ 7 then 2 else ((Finset.range (x + 1)).filter Nat.Prime).sup gapAt

theorem gapAt_le_lam {p x : ℕ} (hp : p.Prime) (hpx : p ≤ x) (hx : 7 < x) : gapAt p ≤ lam x := by
  unfold lam; rw [if_neg (by omega)]
  exact Finset.le_sup (f := gapAt) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)

theorem nextPrime_three : nextPrime 3 = 5 := by
  unfold nextPrime
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by norm_num⟩, fun n hn ⟨h1, h2⟩ => ?_⟩
  interval_cases n; norm_num at h2

theorem two_le_lam (x : ℕ) : 2 ≤ lam x := by
  by_cases hx : x ≤ 7
  · unfold lam; rw [if_pos hx]
  · have := gapAt_le_lam (p := 3) (x := x) Nat.prime_three (by omega) (by omega)
    unfold gapAt at this; rw [nextPrime_three] at this; omega

theorem lam_mono {a b : ℕ} (hab : a ≤ b) : lam a ≤ lam b := by
  by_cases ha : a ≤ 7
  · have := two_le_lam b; unfold lam at *; rw [if_pos ha]; exact this
  · unfold lam; rw [if_neg ha, if_neg (by omega)]
    exact Finset.sup_mono fun q hq => by
      simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
      exact ⟨by omega, hq.2⟩

/-! ### The printed Lemma 7 fails at x = 6 -/

theorem lam_six : lam 6 = 2 := by unfold lam; rw [if_pos (by norm_num)]
theorem lam_two : lam 2 = 2 := by unfold lam; rw [if_pos (by norm_num)]

/-- **Lemma 7 as printed is false at `x = 6`**: no sum of two odd primes lies in the open
interval `(6, 6 + λ(λ(6))) = (6, 8)`. -/
theorem lemma7_printed_false_at_6 :
    ¬ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ Odd p₁ ∧ p₂.Prime ∧ Odd p₂ ∧
      6 < p₁ + p₂ ∧ p₁ + p₂ < 6 + lam (lam 6) := by
  rintro ⟨p₁, p₂, -, ⟨a, rfl⟩, -, ⟨b, rfl⟩, h1, h2⟩
  rw [lam_six, lam_two] at h2
  omega

/-! ### The half-open Lemma 7 holds -/

/-- An odd prime `q ≥ 3` has an even gap to the next prime. -/
theorem gap_even {q : ℕ} (hq : q.Prime) (h3 : 3 ≤ q) : Even (gapAt q) := by
  obtain ⟨hlt, hp⟩ := nextPrime_spec q
  have ho1 : Odd q := hq.odd_of_ne_two (by omega)
  have ho2 : Odd (nextPrime q) := hp.odd_of_ne_two (by omega)
  unfold gapAt
  exact Nat.Odd.sub_odd ho2 ho1

/-- **Kaniecki Lemma 7, half-open form**: for every integer `x > 4` there are odd primes
`p₁, p₂` with `x < p₁ + p₂ ≤ x + λ(λ(x))`. -/
theorem lemma7_closed (x : ℕ) (hx : 4 < x) :
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ Odd p₁ ∧ p₂.Prime ∧ Odd p₂ ∧
      x < p₁ + p₂ ∧ p₁ + p₂ ≤ x + lam (lam x) := by
  classical
  -- p₁, the greatest odd prime below x
  set P : ℕ → Prop := fun k => k.Prime ∧ Odd k with hP
  have h3 : P 3 := ⟨Nat.prime_three, by decide⟩
  set p₁ := Nat.findGreatest P (x - 1) with hp₁
  have hp₁P : P p₁ := Nat.findGreatest_spec (m := 3) (by omega) h3
  have hp₁3 : 3 ≤ p₁ := Nat.le_findGreatest (by omega) h3
  have hp₁x : p₁ ≤ x - 1 := Nat.findGreatest_le _
  have hp₁max : ∀ k, p₁ < k → k ≤ x - 1 → ¬ P k := fun k h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  -- y = x - p₁ is at most the gap after p₁
  set y := x - p₁ with hy
  obtain ⟨hn1, hn2⟩ := nextPrime_spec p₁
  have hnx : x ≤ nextPrime p₁ := by
    by_contra h
    exact hp₁max _ hn1 (by omega) ⟨hn2, hn2.odd_of_ne_two (by omega)⟩
  have hyg : y ≤ gapAt p₁ := by unfold gapAt; omega
  -- p₂, the least odd prime above y
  have hex : ∃ q, y < q ∧ q.Prime ∧ Odd q := by
    obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (y + 3)
    exact ⟨q, by omega, hq2, hq2.odd_of_ne_two (by omega)⟩
  set p₂ := Nat.find hex with hp₂
  obtain ⟨hp₂y, hp₂P, hp₂o⟩ := Nat.find_spec hex
  have hp₂min : ∀ q, y < q → q.Prime → Odd q → p₂ ≤ q := fun q a b c =>
    Nat.find_min' hex ⟨a, b, c⟩
  refine ⟨p₁, p₂, hp₁P.1, hp₁P.2, hp₂P, hp₂o, by omega, ?_⟩
  -- p₂ - y ≤ λ(λ(x))
  suffices hs : p₂ - y ≤ lam (lam x) by omega
  by_cases hy6 : y ≤ 6
  · have h2 : p₂ - y ≤ 2 := by
      have hy1 : 1 ≤ y := by omega
      rcases (by omega : y ≤ 2 ∨ (3 ≤ y ∧ y ≤ 4) ∨ 5 ≤ y) with h | h | h
      · have := hp₂min 3 (by omega) Nat.prime_three (by decide); omega
      · have := hp₂min 5 (by omega) Nat.prime_five (by decide); omega
      · have := hp₂min 7 (by omega) (by norm_num) (by decide); omega
    exact h2.trans (two_le_lam _)
  · -- y ≥ 7: the gap after p₁ is even and ≥ 7, so ≥ 8 and λ(x) ≥ 8
    have hgev := gap_even hp₁P.1 hp₁3
    have hg8 : 8 ≤ gapAt p₁ := by
      obtain ⟨r, hr⟩ := hgev; omega
    have hx7 : 7 < x := by omega
    have hlx : gapAt p₁ ≤ lam x := gapAt_le_lam hp₁P.1 (by omega) hx7
    -- q, the largest prime ≤ y, and its successor q' > y
    set q := Nat.findGreatest Nat.Prime y with hq
    have h7 : (7 : ℕ).Prime := by norm_num
    have hqP : q.Prime := Nat.findGreatest_spec (m := 7) (by omega) h7
    have hq7 : 7 ≤ q := Nat.le_findGreatest (by omega) h7
    have hqy : q ≤ y := Nat.findGreatest_le _
    obtain ⟨hq1, hq2⟩ := nextPrime_spec q
    have hq'y : y < nextPrime q := by
      by_contra h
      exact Nat.findGreatest_is_greatest (P := Nat.Prime) hq1 (by omega) hq2
    have hp₂q : p₂ ≤ nextPrime q := hp₂min _ hq'y hq2 (hq2.odd_of_ne_two (by omega))
    have hgq : gapAt q ≤ lam (lam x) := gapAt_le_lam hqP (by omega) (by omega)
    unfold gapAt at hgq
    omega

/-! ### Section 3, the bound λ(x) < 4.1926 · 10^19 for x ≤ e^78 -/

/-- Lemma 6's right side at `x = e^78`, `(1/4π) √((1 + 1/16597) x) log² x` as printed on page
371, the factor inside the root, is below the printed `4.1926 · 10^19`: MATCH, the formula
gives `4.19254 · 10^19`. An earlier draft of this file put the factor outside the root and
wrongly reported a slip; withdrawn after the falsifier read the page image. -/
theorem lemma6_at_e78_matches :
    1 / (4 * Real.pi) * √((1 + 1 / 16597) * Real.exp 78) * Real.log (Real.exp 78) ^ 2
      < (4.1926e19 : ℝ) := by
  rw [Real.log_exp]
  have he : Real.exp 39 ≤ (2.7182818286 : ℝ) ^ 39 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 39
    rwa [← Real.exp_nat_mul, show ((39 : ℕ) : ℝ) * 1 = 39 by norm_num] at h
  have he0 := Real.exp_pos 39
  have hs : √((1 + 1 / 16597) * Real.exp 78) ≤ (1 + 1 / 33194) * Real.exp 39 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : Real.exp 78 = Real.exp 39 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; nlinarith [sq_nonneg (Real.exp 39)]
  have hpi := Real.pi_gt_d6
  have hs0 := Real.sqrt_nonneg ((1 + 1 / 16597) * Real.exp 78)
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

end LeanLab.KanieckiGap

