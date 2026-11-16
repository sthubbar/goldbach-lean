module

public import Mathlib
public import LeanLab.Dudek2014.MaxGap

/-!
# A prime in `(x - √x log x, x]` for `2 ≤ x < 3999999999999999761`

Dudek's Theorem 3 gives, under the Riemann hypothesis, a prime in `(x - (1 + ε) √x log x, x]`
for every `ε > 0` and all large `x`. On the finite range `2 ≤ x < 3999999999999999761` the
interval with `ε = 0` holds a prime without the Riemann hypothesis, given the maximal prime gap
computation of Oliveira e Silva, Herzog and Pardi 2014, the explicit hypothesis `MaxGap1476`.
Below `67001` the proof uses kernel checked prime gap scans; above, the gap bound 1477. The
least constant that can work in place of `1` is `2 / (√5 log 5) = 0.5557...`, from the gap
between 3 and 5 as `x` tends to 5 from below; `not_primeInC_055` shows that `0.55` fails at
`x = 4.99`. These are derived results of the entry, not statements of Dudek's paper.
AI wrote the Lean code, Claude, 2026-11-03. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.Dudek2014.IntervalOne

open LeanLab.Dudek2014

open Real

/-- A prime in `(x - c √x log x, x]`. The paper's Theorem 3 interval is `c = 1 + ε`. -/
def PrimeInC (c x : ℝ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ x - c * √x * Real.log x < p ∧ (p : ℝ) ≤ x

/-- The interval only grows with `c`, for `x ≥ 1`. -/
theorem PrimeInC.mono {c c' x : ℝ} (hc : c ≤ c') (hx : 1 ≤ x) (h : PrimeInC c x) :
    PrimeInC c' x := by
  obtain ⟨p, hp, h1, h2⟩ := h
  refine ⟨p, hp, ?_, h2⟩
  have h3 : 0 ≤ √x * Real.log x := mul_nonneg (Real.sqrt_nonneg x) (Real.log_nonneg hx)
  nlinarith

/-- Vacuity: the predicate holds at `x = 2` with `c = 1`, by the prime 2. -/
theorem primeInC_two : PrimeInC 1 2 := by
  refine ⟨2, Nat.prime_two, ?_, by norm_num⟩
  have h : 0 < √(2 : ℝ) * Real.log 2 := mul_pos (by positivity) (Real.log_pos (by norm_num))
  norm_num
  exact Real.log_pos (by norm_num)

theorem sqrtlog_mono {t x : ℝ} (ht : 1 ≤ t) (hx : t ≤ x) :
    √t * Real.log t ≤ √x * Real.log x :=
  mul_le_mul (Real.sqrt_le_sqrt hx) (Real.log_le_log (by linarith) hx)
    (Real.log_nonneg ht) (Real.sqrt_nonneg x)

/-- The generic use of a natural gap bound, for `c = 1`. -/
theorem tier1 (t T g : ℕ) (ht : 1 ≤ t) (hg : (g : ℝ) ≤ √(t : ℝ) * Real.log t)
    (hscan : ∀ n, t ≤ n → n ≤ T → ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ n < p + g) :
    ∀ x : ℝ, (t : ℝ) ≤ x → x < T + 1 → PrimeInC 1 x := by
  intro x htx hxT
  have hx0 : 0 ≤ x := le_trans (by positivity) htx
  set n := ⌊x⌋₊ with hn
  have htn : t ≤ n := Nat.le_floor htx
  have hnT : n ≤ T := by
    have : n < T + 1 := by
      rw [hn, Nat.floor_lt hx0]; exact_mod_cast hxT
    omega
  obtain ⟨p, hp, hpn, hnp⟩ := hscan n htn hnT
  refine ⟨p, hp, ?_, ?_⟩
  · have h1 : x < n + 1 := Nat.lt_floor_add_one x
    have h2 : ((n : ℕ) : ℝ) + 1 ≤ (p : ℝ) + g := by exact_mod_cast hnp
    have h3 := sqrtlog_mono (t := (t : ℝ)) (x := x) (by exact_mod_cast ht) htx
    nlinarith
  · calc (p : ℝ) ≤ n := by exact_mod_cast hpn
      _ ≤ x := Nat.floor_le hx0

theorem sqrt_ge {a x : ℝ} (ha : 0 ≤ a) (h : a ^ 2 ≤ x) : a ≤ √x := Real.le_sqrt_of_sq_le h

/-- `log b ≥ (k / j) log 2` whenever `2 ^ k ≤ b ^ j`. -/
theorem log_ge_of_pow {b : ℝ} {j k : ℕ} (hb : 0 < b) (hj : 0 < j) (h : (2 : ℝ) ^ k ≤ b ^ j) :
    (k : ℝ) * Real.log 2 ≤ (j : ℝ) * Real.log b := by
  have := Real.log_le_log (by positivity) h
  simpa [Real.log_pow] using this

theorem interval_on_2_3 {x : ℝ} (h2 : 2 ≤ x) (h3 : x < 3) : PrimeInC 1 x := by
  refine ⟨2, Nat.prime_two, ?_, by exact_mod_cast h2⟩
  have hl2 := Real.log_two_gt_d9
  rcases lt_or_ge x 2.9 with a | a
  · have h1 : (1.414 : ℝ) ≤ √x := sqrt_ge (by norm_num) (by nlinarith)
    have h4 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) h2
    push_cast; nlinarith
  · have h1 : (1.7 : ℝ) ≤ √x := sqrt_ge (by norm_num) (by nlinarith)
    have h4 : (1 : ℝ) ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    push_cast; nlinarith

theorem interval_on_3_5 {x : ℝ} (h2 : 3 ≤ x) (h3 : x < 5) : PrimeInC 1 x := by
  refine ⟨3, Nat.prime_three, ?_, by exact_mod_cast h2⟩
  have h4 : (1 : ℝ) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  rcases lt_or_ge x 4 with a | a
  · have h1 : (1.7 : ℝ) ≤ √x := sqrt_ge (by norm_num) (by nlinarith)
    push_cast; nlinarith
  · have h1 : (2 : ℝ) ≤ √x := sqrt_ge (by norm_num) (by nlinarith)
    have h5 : (1.38 : ℝ) ≤ Real.log x :=
      le_trans (by have := log4_gt; linarith) (Real.log_le_log (by norm_num) a)
    push_cast; nlinarith

/-- **The interval `(x - √x log x, x]` holds a prime for `2 ≤ x < 3999999999999999761`,** given
the maximal prime gap bound `MaxGap1476` of Oliveira e Silva, Herzog and Pardi 2014. This is
Dudek's Theorem 3 interval with `ε = 0`, on a finite range and without the Riemann
hypothesis. -/
theorem dudek_interval_one (hG : MaxGap1476) :
    ∀ x : ℝ, 2 ≤ x → x < 3999999999999999761 → PrimeInC 1 x := by
  intro x h2 hx
  have hl2 := Real.log_two_gt_d9
  rcases lt_or_ge x 3 with a | a
  · exact interval_on_2_3 h2 a
  rcases lt_or_ge x 5 with b | b
  · exact interval_on_3_5 a b
  rcases lt_or_ge x 7 with c | c
  · refine tier1 5 6 2 (by norm_num) ?_ (fun n h1 h2 => scan_use (by decide +kernel) le_rfl scan_5 n h1 (by omega)) x
      (by exact_mod_cast b) (by norm_num; linarith)
    have h1 : (2.2 : ℝ) ≤ √((5 : ℕ) : ℝ) := sqrt_ge (by norm_num) (by norm_num)
    have h3 : (1 : ℝ) ≤ Real.log ((5 : ℕ) : ℝ) := log_ge_one (by norm_num)
    push_cast at h1 h3 ⊢; nlinarith
  rcases lt_or_ge x 23 with d | d
  · refine tier1 7 22 4 (by norm_num) ?_ (fun n h1 h2 => scan_use (by decide +kernel) le_rfl scan_7 n h1 (by omega)) x
      (by exact_mod_cast c) (by norm_num; linarith)
    have h1 : (2.645 : ℝ) ≤ √((7 : ℕ) : ℝ) := sqrt_ge (by norm_num) (by norm_num)
    have h3 := log_ge_of_pow (b := 7) (j := 5) (k := 14) (by norm_num) (by norm_num) (by norm_num)
    push_cast at h1 h3 ⊢; nlinarith
  rcases lt_or_ge x 200 with e | e
  · refine tier1 23 199 14 (by norm_num) ?_ (fun n h1 h2 => scan_use (by decide +kernel) le_rfl scan_23 n h1 (by omega)) x
      (by exact_mod_cast d) (by norm_num; linarith)
    have h1 : (4.79 : ℝ) ≤ √((23 : ℕ) : ℝ) := sqrt_ge (by norm_num) (by norm_num)
    have h3 := log_ge_of_pow (b := 23) (j := 2) (k := 9) (by norm_num) (by norm_num) (by norm_num)
    push_cast at h1 h3 ⊢; nlinarith
  rcases lt_or_ge x 67001 with f | f
  · refine tier1 200 67000 72 (by norm_num) ?_ gaps_big x
      (by exact_mod_cast e) (by norm_num; linarith)
    have h1 : (14.14 : ℝ) ≤ √((200 : ℕ) : ℝ) := sqrt_ge (by norm_num) (by norm_num)
    have h3 := log_ge_of_pow (b := 200) (j := 2) (k := 15) (by norm_num) (by norm_num) (by norm_num)
    push_cast at h1 h3 ⊢; nlinarith
  · refine tier1 67000 3999999999999999760 1477 (by norm_num) ?_
      (fun n h1 h2' => gaps_huge hG n (by omega) (by omega)) x (by norm_num; linarith) (by norm_num; linarith)
    have h1 : (258 : ℝ) ≤ √((67000 : ℕ) : ℝ) := sqrt_ge (by norm_num) (by norm_num)
    have h3 := log_ge_of_pow (b := 67000) (j := 1) (k := 16) (by norm_num) (by norm_num) (by norm_num)
    push_cast at h1 h3 ⊢; nlinarith

/-- The same for `(x - (1 + ε) √x log x, x]` with every `ε ≥ 0`, given `MaxGap1476`. -/
theorem dudek_interval_eps (hG : MaxGap1476) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ x : ℝ, 2 ≤ x → x < 3999999999999999761 → PrimeInC (1 + ε) x := fun x h2 hx =>
  (dudek_interval_one hG x h2 hx).mono (by linarith) (by linarith)

/-- 0.55 fails at `x = 4.99`, so the sharp constant is above 0.55. No hypothesis. -/
theorem not_primeInC_055 : ¬ PrimeInC (55 / 100) 4.99 := by
  rintro ⟨p, hp, h1, h2⟩
  have hs : √(4.99 : ℝ) ≤ 2.234 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 ≤ √(4.99 : ℝ) := Real.sqrt_nonneg _
  have hl : Real.log 4.99 ≤ 1.6175 := by
    have h5 := Real.log_le_log (by norm_num) (show (4.99 : ℝ) ^ 3 ≤ 2 ^ 7 by norm_num)
    rw [Real.log_pow, Real.log_pow] at h5
    have := Real.log_two_lt_d9
    push_cast at h5; linarith
  have hl0 : 0 ≤ Real.log 4.99 := Real.log_nonneg (by norm_num)
  have hm : √(4.99 : ℝ) * Real.log 4.99 ≤ 2.234 * 1.6175 := mul_le_mul hs hl hl0 (by norm_num)
  have h3 : (3 : ℝ) < p := by nlinarith
  have h3' : 3 < p := by exact_mod_cast h3
  have h4' : p ≤ 4 := by
    have : (p : ℝ) < 5 := by linarith
    have : p < 5 := by exact_mod_cast this
    omega
  have : p = 4 := by omega
  subst this
  exact absurd hp (by norm_num)

end LeanLab.Dudek2014.IntervalOne
