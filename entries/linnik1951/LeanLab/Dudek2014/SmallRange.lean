module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.Dudek2014.Statements

/-!
P0100 Dudek 2014, Theorem 2 for `2 ≤ x ≤ 67000`, unconditionally, by a kernel-checked prime
gap scan; then Theorem 2 for every `x ≥ 2` from the analytic range alone. The paper says only
that Mathematica checks the small range; this module does it in the Lean kernel.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.Dudek2014
open Real

/-- Scan `n = n0, ..., n0 + fuel - 1`, tracking the last prime seen, and check that each `n`
has a prime `p ≤ n` with `n < p + g`. -/
def gapScan (g : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | fuel + 1, n, last =>
      let last' := if primeB n then n else last
      (n < last' + g) && gapScan g fuel (n + 1) last'

theorem gapScan_sound (g : ℕ) : ∀ fuel n0 last, last.Prime → last ≤ n0 →
    gapScan g fuel n0 last = true →
    ∀ n, n0 ≤ n → n < n0 + fuel → ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ n < p + g := by
  intro fuel
  induction fuel with
  | zero => intro n0 last _ _ _ n h1 h2; omega
  | succ k ih =>
    intro n0 last hl hle h n h1 h2
    simp only [gapScan, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlt, hrest⟩ := h
    have hl' : (if primeB n0 = true then n0 else last).Prime := by
      split_ifs with hp
      · exact primeB_sound hp
      · exact hl
    have hle' : (if primeB n0 = true then n0 else last) ≤ n0 := by
      split_ifs <;> omega
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt1
    · exact ⟨_, hl', hle', hlt⟩
    · exact ih (n0 + 1) _ hl' (by omega) hrest n hlt1 (by omega)

theorem scan_2 : gapScan 1 1 2 2 = true := by decide +kernel
theorem scan_3 : gapScan 2 2 3 3 = true := by decide +kernel
theorem scan_5 : gapScan 2 2 5 5 = true := by decide +kernel
theorem scan_7 : gapScan 4 16 7 7 = true := by decide +kernel
theorem scan_23 : gapScan 14 177 23 23 = true := by decide +kernel
theorem scan_big0 : gapScan 72 6000 200 199 = true := by decide +kernel
theorem scan_big1 : gapScan 72 6000 6200 6199 = true := by decide +kernel
theorem scan_big2 : gapScan 72 6000 12200 12197 = true := by decide +kernel
theorem scan_big3 : gapScan 72 6000 18200 18199 = true := by decide +kernel
theorem scan_big4 : gapScan 72 6000 24200 24197 = true := by decide +kernel
theorem scan_big5 : gapScan 72 6000 30200 30197 = true := by decide +kernel
theorem scan_big6 : gapScan 72 6000 36200 36191 = true := by decide +kernel
theorem scan_big7 : gapScan 72 6000 42200 42197 = true := by decide +kernel
theorem scan_big8 : gapScan 72 6000 48200 48197 = true := by decide +kernel
theorem scan_big9 : gapScan 72 6000 54200 54193 = true := by decide +kernel
theorem scan_big10 : gapScan 72 6000 60200 60169 = true := by decide +kernel
theorem scan_big11 : gapScan 72 801 66200 66191 = true := by decide +kernel

/-- Generic use of one scan. -/
theorem scan_use {g fuel n0 last : ℕ} (hl : primeB last = true) (hle : last ≤ n0)
    (h : gapScan g fuel n0 last = true) :
    ∀ n, n0 ≤ n → n < n0 + fuel → ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ n < p + g :=
  gapScan_sound g fuel n0 last (primeB_sound hl) hle h

/-- Every `200 ≤ n ≤ 67000` has a prime `p ≤ n` with `n - p < 72`. -/
theorem gaps_big : ∀ n, 200 ≤ n → n ≤ 67000 → ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ n < p + 72 := by
  intro n h1 h2
  rcases Nat.lt_or_ge n 6200 with h0 | h0
  · exact scan_use (by decide +kernel) (by norm_num) scan_big0 n (by omega) (by omega)
  rcases Nat.lt_or_ge n 12200 with h1 | h1
  · exact scan_use (by decide +kernel) (by norm_num) scan_big1 n (by omega) (by omega)
  rcases Nat.lt_or_ge n 18200 with h2 | h2
  · exact scan_use (by decide +kernel) (by norm_num) scan_big2 n (by omega) (by omega)
  rcases Nat.lt_or_ge n 24200 with h3 | h3
  · exact scan_use (by decide +kernel) (by norm_num) scan_big3 n (by omega) (by omega)
  rcases Nat.lt_or_ge n 30200 with h4 | h4
  · exact scan_use (by decide +kernel) (by norm_num) scan_big4 n (by omega) (by omega)
  rcases Nat.lt_or_ge n 36200 with h5 | h5
  · exact scan_use (by decide +kernel) (by norm_num) scan_big5 n (by omega) (by omega)
  rcases Nat.lt_or_ge n 42200 with h6 | h6
  · exact scan_use (by decide +kernel) (by norm_num) scan_big6 n (by omega) (by omega)
  rcases Nat.lt_or_ge n 48200 with h7 | h7
  · exact scan_use (by decide +kernel) (by norm_num) scan_big7 n (by omega) (by omega)
  rcases Nat.lt_or_ge n 54200 with h8 | h8
  · exact scan_use (by decide +kernel) (by norm_num) scan_big8 n (by omega) (by omega)
  rcases Nat.lt_or_ge n 60200 with h9 | h9
  · exact scan_use (by decide +kernel) (by norm_num) scan_big9 n (by omega) (by omega)
  rcases Nat.lt_or_ge n 66200 with h10 | h10
  · exact scan_use (by decide +kernel) (by norm_num) scan_big10 n (by omega) (by omega)
  exact scan_use (by decide +kernel) (by norm_num) scan_big11 n (by omega) (by omega)

/-! ### From natural gaps to Dudek's real interval -/

theorem dudekH_mono {t x : ℝ} (ht : 1 ≤ t) (hx : t ≤ x) : dudekH t ≤ dudekH x := by
  unfold dudekH
  have hpi : 0 < 4 / π := by positivity
  have h1 : √t ≤ √x := Real.sqrt_le_sqrt hx
  have h2 : Real.log t ≤ Real.log x := Real.log_le_log (by linarith) hx
  have h3 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h4 : 0 ≤ √t := Real.sqrt_nonneg t
  have := mul_le_mul h1 h2 h3 (Real.sqrt_nonneg x)
  calc 4 / π * √t * Real.log t = 4 / π * (√t * Real.log t) := by ring
    _ ≤ 4 / π * (√x * Real.log x) := by gcongr
    _ = 4 / π * √x * Real.log x := by ring

theorem dudekH_lb {t s l : ℝ} (hs : 0 ≤ s) (hs2 : s ^ 2 ≤ t) (hl : 0 ≤ l)
    (hlog : l ≤ Real.log t) : 4 / 3.15 * s * l ≤ dudekH t := by
  unfold dudekH
  have hpi : 4 / 3.15 ≤ 4 / π := by
    apply div_le_div_of_nonneg_left (by norm_num) Real.pi_pos Real.pi_lt_d2.le
  have hst : s ≤ √t := Real.le_sqrt_of_sq_le hs2
  have := mul_le_mul hpi hst hs (by positivity)
  have := mul_le_mul this hlog hl (by positivity)
  linarith

theorem tier (t T g : ℕ) (ht : 1 ≤ t) (hg : (g : ℝ) ≤ dudekH t)
    (hscan : ∀ n, t ≤ n → n ≤ T → ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ n < p + g) :
    ∀ x : ℝ, (t : ℝ) ≤ x → x < T + 1 → PrimeInDudekInterval x := by
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
    have h3 : dudekH t ≤ dudekH x := dudekH_mono (by exact_mod_cast ht) htx
    linarith
  · calc (p : ℝ) ≤ n := by exact_mod_cast hpn
      _ ≤ x := Nat.floor_le hx0

theorem log4_gt : 1.3862 ≤ Real.log 4 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9; linarith

theorem log_ge_one {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9; linarith

theorem small_range : ∀ x : ℝ, 2 ≤ x → x < 67001 → PrimeInDudekInterval x := by
  intro x h2 hx
  rcases lt_or_ge x 3 with a | a
  · refine tier 2 2 1 (by norm_num) ?_ (fun n h1 h2 => scan_use (by decide +kernel) le_rfl scan_2 n h1 (by omega)) x
      (by exact_mod_cast h2) (by norm_num; linarith)
    have := dudekH_lb (t := 2) (s := 1.414) (l := 0.6931) (by norm_num) (by norm_num)
      (by norm_num) (by have := Real.log_two_gt_d9; linarith)
    norm_num at this ⊢; linarith
  rcases lt_or_ge x 5 with b | b
  · refine tier 3 4 2 (by norm_num) ?_ (fun n h1 h2 => scan_use (by decide +kernel) le_rfl scan_3 n h1 (by omega)) x
      (by exact_mod_cast a) (by norm_num; linarith)
    have := dudekH_lb (t := 3) (s := 1.732) (l := 1) (by norm_num) (by norm_num)
      (by norm_num) (log_ge_one le_rfl)
    norm_num at this ⊢; linarith
  rcases lt_or_ge x 7 with c | c
  · refine tier 5 6 2 (by norm_num) ?_ (fun n h1 h2 => scan_use (by decide +kernel) le_rfl scan_5 n h1 (by omega)) x
      (by exact_mod_cast b) (by norm_num; linarith)
    have := dudekH_lb (t := 5) (s := 2.236) (l := 1) (by norm_num) (by norm_num)
      (by norm_num) (log_ge_one (by norm_num))
    norm_num at this ⊢; linarith
  rcases lt_or_ge x 23 with d | d
  · refine tier 7 22 4 (by norm_num) ?_ (fun n h1 h2 => scan_use (by decide +kernel) le_rfl scan_7 n h1 (by omega)) x
      (by exact_mod_cast c) (by norm_num; linarith)
    have := dudekH_lb (t := 7) (s := 2.645) (l := 1.3862) (by norm_num) (by norm_num)
      (by norm_num) (le_trans log4_gt (Real.log_le_log (by norm_num) (by norm_num)))
    norm_num at this ⊢; linarith
  rcases lt_or_ge x 200 with e | e
  · refine tier 23 199 14 (by norm_num) ?_ (fun n h1 h2 => scan_use (by decide +kernel) le_rfl scan_23 n h1 (by omega)) x
      (by exact_mod_cast d) (by norm_num; linarith)
    have hl : 2.7724 ≤ Real.log 23 := by
      have h16 : Real.log 16 = 2 * Real.log 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_le_log (show (0 : ℝ) < 16 by norm_num) (show (16 : ℝ) ≤ 23 by norm_num)
      have := log4_gt; linarith
    have := dudekH_lb (t := 23) (s := 4.795) (l := 2.7724) (by norm_num) (by norm_num)
      (by norm_num) hl
    norm_num at this ⊢; linarith
  · refine tier 200 67000 72 (by norm_num) ?_ gaps_big x
      (by exact_mod_cast e) (by norm_num; linarith)
    have hl : 4.852 ≤ Real.log 200 := by
      have h128 : Real.log 128 = 7 * Real.log 2 := by
        rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
      have := Real.log_le_log (show (0 : ℝ) < 128 by norm_num) (show (128 : ℝ) ≤ 200 by norm_num)
      have := Real.log_two_gt_d9; linarith
    have := dudekH_lb (t := 200) (s := 14.14) (l := 4.852) (by norm_num) (by norm_num)
      (by norm_num) hl
    norm_num at this ⊢; linarith

/-- Dudek's Theorem 2 for every `x ≥ 2` from the analytic range `x ≥ 66799` alone. -/
theorem theorem2_of_large (hL : ∀ x : ℝ, 66799 ≤ x → PrimeInDudekInterval x) :
    ∀ x : ℝ, 2 ≤ x → PrimeInDudekInterval x := by
  intro x hx
  rcases lt_or_ge x 67001 with h | h
  · exact small_range x hx h
  · exact hL x (by linarith)

/-- So Theorem 2 needs RH only through the analytic range. -/
theorem theorem2_of_RH_large
    (hL : RiemannHypothesis → ∀ x : ℝ, 66799 ≤ x → PrimeInDudekInterval x) :
    RiemannHypothesis → ∀ x : ℝ, 2 ≤ x → PrimeInDudekInterval x :=
  fun hRH => theorem2_of_large (hL hRH)

end LeanLab.Dudek2014
