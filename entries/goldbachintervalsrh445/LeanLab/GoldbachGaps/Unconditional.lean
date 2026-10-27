module

public import Mathlib
public import LeanLab.Common.Goldbach
public import LeanLab.KadiriLumley2014.Statements

/-!
I-0018, unit U-0180, run 20261017T0303Z-29152. Unconditional, explicit Goldbach numbers in
short intervals: the counterpart without RH of I-0010, `ChirreHagen2025.goldbach_62`.
A Goldbach number here is an even `n` that is a sum of two primes.

Inputs, all cited, none proved here: Kadiri-Lumley 2014 Table 2 rows `KLRow`, P0059, and the
Oliveira e Silva, Herzog, Pardi even verification to `4 · 10^18`, P0005.
Idea: a prime `p` in `(x - 3, y)` gives the Goldbach number `p + 3` in `(x, y + 3)`, so a
prime gap bound is a Goldbach gap bound. Mathematics KNOWN in method; see IDEAS I-0018.
Binary Goldbach stays OPEN.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/

@[expose] public section

namespace LeanLab.GoldbachGaps
open Real LeanLab.KadiriLumley2014

/-- A Goldbach number: an even sum of two primes. -/
def IsGoldbachNumber (n : ℕ) : Prop := Even n ∧ IsGoldbachSum n

/-- One Table 2 row gives a Goldbach number in `(x, max (x + (x - 3)/(Δ - 1)) (x0 + 4))`
for every real `x ≥ 5`. -/
theorem goldbach_near_of_row {x0 Δ : ℝ} (h : KLRow x0 Δ) (hΔ : 1 < Δ) {x : ℝ}
    (hx : 5 ≤ x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧
      (n : ℝ) < max (x + (x - 3) / (Δ - 1)) (x0 + 4) := by
  have hΔ0 : Δ ≠ 0 := by positivity
  have hΔ1 : Δ - 1 ≠ 0 := by linarith
  have hΔ1p : 0 < Δ - 1 := by linarith
  set y : ℝ := max ((x - 3) * Δ / (Δ - 1)) (x0 + 1) with hy
  have hy0 : x0 < y := by
    have := le_max_right ((x - 3) * Δ / (Δ - 1)) (x0 + 1); linarith
  obtain ⟨p, hp, hl, hu⟩ := h y hy0
  have hc : 0 < 1 - 1 / Δ := by
    have : 1 / Δ < 1 := by rw [div_lt_one (by linarith)]; exact hΔ
    linarith
  have hid : (1 - 1 / Δ) * ((x - 3) * Δ / (Δ - 1)) = x - 3 := by
    field_simp
  have hlow : x - 3 < p := by
    have h1 : (x - 3) * Δ / (Δ - 1) ≤ y := le_max_left _ _
    have : (1 - 1 / Δ) * ((x - 3) * Δ / (Δ - 1)) ≤ (1 - 1 / Δ) * y :=
      mul_le_mul_of_nonneg_left h1 hc.le
    linarith
  have hp3 : 3 ≤ p := by
    have : (2 : ℝ) < p := by linarith
    have : 2 < p := by exact_mod_cast this
    omega
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  refine ⟨p + 3, ⟨?_, p, 3, hp, Nat.prime_three, rfl⟩, ?_, ?_⟩
  · exact hpo.add_odd (by decide)
  · push_cast; linarith
  · push_cast
    have hA : (x - 3) * Δ / (Δ - 1) + 3 = x + (x - 3) / (Δ - 1) := by
      field_simp; ring
    have : y + 3 ≤ max (x + (x - 3) / (Δ - 1)) (x0 + 4) := by
      rw [hy]
      rcases le_total ((x - 3) * Δ / (Δ - 1)) (x0 + 1) with hle | hle
      · rw [max_eq_right hle]
        have := le_max_right (x + (x - 3) / (Δ - 1)) (x0 + 4); linarith
      · rw [max_eq_left hle]
        have := le_max_left (x + (x - 3) / (Δ - 1)) (x0 + 4); linarith
    linarith

/-- Above `x0 + 4`, a row with `Δ` gives a Goldbach number in `(x, x + x/(Δ - 1))`, provided
that interval has length at least 4 at the start. -/
theorem goldbach_gap_of_row {x0 Δ : ℝ} (h : KLRow x0 Δ) (hΔ : 1 < Δ) {x : ℝ}
    (hx : 5 ≤ x) (hx0 : x0 ≤ x) (h4 : 4 * (Δ - 1) ≤ x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + x / (Δ - 1) := by
  obtain ⟨n, hn, hlo, hhi⟩ := goldbach_near_of_row h hΔ hx
  refine ⟨n, hn, hlo, lt_of_lt_of_le hhi (max_le ?_ ?_)⟩
  · have : (x - 3) / (Δ - 1) ≤ x / (Δ - 1) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    linarith
  · have : 4 ≤ x / (Δ - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
    linarith

/-- The smallest even number above `x` is at most `x + 2`. -/
theorem even_above (x : ℝ) (hx : 0 ≤ x) : ∃ n : ℕ, Even n ∧ x < n ∧ (n : ℝ) ≤ x + 2 := by
  set k : ℕ := ⌊x / 2⌋₊ with hk
  refine ⟨2 * (k + 1), even_two_mul _, ?_, ?_⟩
  · have := Nat.lt_floor_add_one (x / 2)
    push_cast; rw [← hk] at this; linarith
  · have := Nat.floor_le (show 0 ≤ x / 2 by linarith)
    push_cast; rw [← hk] at this; linarith

/-- I-0018, main form. From the `4 · 10^18` even check and Kadiri-Lumley's first Table 2 row:
every interval `(x, x + max 2 (x / 36082897)]` with real `x ≥ 2` holds a Goldbach number.
Below `4 · 10^18 - 2` the gap is at most 2; above it at most `x / 36082897`. -/
theorem goldbach_gaps (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (h1 : KLRow (4 * 10 ^ 18) 36082898) :
    ∀ x : ℝ, 2 ≤ x → ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧
      (n : ℝ) ≤ x + max 2 (x / 36082897) := by
  intro x hx
  rcases le_or_gt x (4 * 10 ^ 18 - 2) with hs | hb
  · obtain ⟨n, hev, hlo, hhi⟩ := even_above x (by linarith)
    have hn4 : 4 ≤ n := by
      have : (2 : ℝ) < n := by linarith
      have h2 : 2 < n := by exact_mod_cast this
      rcases hev with ⟨k, hk⟩; omega
    have hnN : n ≤ 4 * 10 ^ 18 := by
      have : (n : ℝ) ≤ 4 * 10 ^ 18 := by linarith
      exact_mod_cast this
    refine ⟨n, ⟨hev, hE n hev hn4 hnN⟩, hlo, ?_⟩
    have := le_max_left (2 : ℝ) (x / 36082897); linarith
  · obtain ⟨n, hn, hlo, hhi⟩ := goldbach_near_of_row h1 (by norm_num) (x := x) (by linarith)
    refine ⟨n, hn, hlo, ?_⟩
    have hm : max (x + (x - 3) / (36082898 - 1)) (4 * 10 ^ 18 + 4) ≤ x + x / 36082897 := by
      apply max_le
      · have : (x - 3) / (36082898 - 1) ≤ x / 36082897 := by
          rw [show (36082898 : ℝ) - 1 = 36082897 by norm_num]
          exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
        linarith
      · have : 6 ≤ x / 36082897 := by rw [le_div_iff₀ (by norm_num)]; linarith
        linarith
    have := le_max_right (2 : ℝ) (x / 36082897)
    linarith

/-- With the later rows: for `x ≥ e^60` the gap is below `x / 1966196910`. -/
theorem goldbach_gaps_60 (h : KLRow (Real.exp 60) 1966196911) :
    ∀ x : ℝ, Real.exp 60 ≤ x → ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧
      (n : ℝ) < x + x / 1966196910 := by
  intro x hx
  have he : (10 : ℝ) ^ 25 ≤ Real.exp 60 := by
    have : (2.7 : ℝ) ^ 60 ≤ Real.exp 1 ^ 60 := by
      gcongr; exact (Real.exp_one_gt_d9).le.trans' (by norm_num)
    have h60 : Real.exp 60 = Real.exp 1 ^ 60 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h60]; refine le_trans ?_ this; norm_num
  have := goldbach_gap_of_row h (by norm_num) (x := x) (by linarith) hx (by linarith)
  simpa [show (1966196911 : ℝ) - 1 = 1966196910 by norm_num] using this

/-- For `x ≥ e^150` the gap is below `x / 2442159713`. -/
theorem goldbach_gaps_150 (h : KLRow (Real.exp 150) 2442159714) :
    ∀ x : ℝ, Real.exp 150 ≤ x → ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧
      (n : ℝ) < x + x / 2442159713 := by
  intro x hx
  have he : (10 : ℝ) ^ 10 ≤ Real.exp 150 := by
    have h1 : (10 : ℝ) ^ 10 ≤ (2 : ℝ) ^ 150 := by norm_num
    have h2 : (2 : ℝ) ^ 150 ≤ Real.exp 1 ^ 150 := by
      gcongr; exact (Real.exp_one_gt_d9).le.trans' (by norm_num)
    have h3 : Real.exp 150 = Real.exp 1 ^ 150 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]; exact h1.trans h2
  have := goldbach_gap_of_row h (by norm_num) (x := x) (by linarith) hx (by linarith)
  simpa [show (2442159714 : ℝ) - 1 = 2442159713 by norm_num] using this

/-! ### Dusart 2018, Corollary 5.5: the `x / log² x` form -/

/-- Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 2018, 227-251,
Corollary 5.5, as quoted by Axler, Integers 18 2018 A52, eq. 4.2, and the TME-EMT page:
for every `x ≥ 468991632` there is a prime `p` with `x ≤ p ≤ x (1 + 1/(5000 log² x))`.
Encoded with the closed left end, the weaker reading of the secondary sources.
A cited input, not proved here. Not in arXiv 1002.0442, which has `1/(25 log² x)` above
396738. -/
def DusartCor55 : Prop :=
  ∀ x : ℝ, 468991632 ≤ x → ∃ p : ℕ, p.Prime ∧ x ≤ p ∧
    (p : ℝ) ≤ x * (1 + 1 / (5000 * Real.log x ^ 2))

/-- From Dusart: for `x ≥ 468991634` there is a Goldbach number in
`(x, x + 1 + (x - 2)/(5000 log² (x - 2))]`. -/
theorem goldbach_gaps_log (hD : DusartCor55) :
    ∀ x : ℝ, 468991634 ≤ x → ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧
      (n : ℝ) ≤ x + 1 + (x - 2) / (5000 * Real.log (x - 2) ^ 2) := by
  intro x hx
  obtain ⟨p, hp, hlo, hhi⟩ := hD (x - 2) (by linarith)
  have hp3 : 3 ≤ p := by
    have : (2 : ℝ) < p := by linarith
    have : 2 < p := by exact_mod_cast this
    omega
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  refine ⟨p + 3, ⟨hpo.add_odd (by decide), p, 3, hp, Nat.prime_three, rfl⟩, ?_, ?_⟩
  · push_cast; linarith
  · push_cast
    have : (x - 2) * (1 + 1 / (5000 * Real.log (x - 2) ^ 2)) =
        (x - 2) + (x - 2) / (5000 * Real.log (x - 2) ^ 2) := by ring
    linarith

/-- I-0018, the form to set beside the RH result `x + 62 log² x` of I-0010: unconditionally,
from the `4 · 10^18` check and Dusart's Corollary 5.5, every interval
`(x, x + max 2 (1 + (x - 2)/(5000 log² (x - 2)))]` with real `x ≥ 2` holds a Goldbach
number. -/
theorem goldbach_gaps_all (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hD : DusartCor55) :
    ∀ x : ℝ, 2 ≤ x → ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧
      (n : ℝ) ≤ x + max 2 (1 + (x - 2) / (5000 * Real.log (x - 2) ^ 2)) := by
  intro x hx
  rcases le_or_gt x (4 * 10 ^ 18 - 2) with hs | hb
  · obtain ⟨n, hev, hlo, hhi⟩ := even_above x (by linarith)
    have hn4 : 4 ≤ n := by
      have : (2 : ℝ) < n := by linarith
      have h2 : 2 < n := by exact_mod_cast this
      rcases hev with ⟨k, hk⟩; omega
    have hnN : n ≤ 4 * 10 ^ 18 := by
      have : (n : ℝ) ≤ 4 * 10 ^ 18 := by linarith
      exact_mod_cast this
    refine ⟨n, ⟨hev, hE n hev hn4 hnN⟩, hlo, ?_⟩
    have := le_max_left (2 : ℝ) (1 + (x - 2) / (5000 * Real.log (x - 2) ^ 2)); linarith
  · obtain ⟨n, hn, hlo, hhi⟩ := goldbach_gaps_log hD x (by linarith)
    refine ⟨n, hn, hlo, ?_⟩
    have := le_max_right (2 : ℝ) (1 + (x - 2) / (5000 * Real.log (x - 2) ^ 2)); linarith

end LeanLab.GoldbachGaps
