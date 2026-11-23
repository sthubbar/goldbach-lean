module

public import Mathlib
public import LeanLab.KanieckiGap.Final
public import LeanLab.GoldbachGaps.Sumset

/-!
Connection sweep 2026-10-19, candidate C3, unit U-5468, CLOUD 20261019T1116Z-cloud23.

Kaniecki's Lemma 6 and the odd step of his closing argument used Young-Potler's table, gaps
at most 778 below 7.263 · 10^13. The lab already cites the larger table of Oliveira e Silva,
Herzog, Pardi 2014, P0005, gaps at most 1476 below 4 · 10^18, as
`GoldbachGaps.Sumset.GapBound1476`. Here both steps run on that one table instead:
* `lemma6'`: Kaniecki Lemma 6 CONDITIONAL ON `Schoenfeld61` and `GapBound1476`;
* `odd_m_three'` and `kaniecki_odd_of'`: the closing step CONDITIONAL ON `GapBound1476`, with
  even Goldbach to 1480 kernel checked.
So INPUTS rank 7 enters P0022 through the same Prop as P0005, P0048 and I-5020.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel. Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.KanieckiGap
open Real Chebyshev LeanLab.SchnirelmannConstant
open LeanLab.GoldbachGaps.Sumset (GapBound1476)

/-- From the 1476 table: a prime `p` with `p + 1476 ≤ 4 · 10^18` has gap at most `1476`. -/
theorem gapAt_le_1476 (hG : GapBound1476) {p : ℕ} (hp : p.Prime)
    (hpb : p + 1476 ≤ 4 * 10 ^ 18) : gapAt p ≤ 1476 := by
  obtain ⟨q, hq, h1, h2⟩ := hG (p : ℝ) (by exact_mod_cast hp.two_le)
    (by exact_mod_cast hpb)
  have h1' : p < q := by exact_mod_cast h1
  have h2' : q ≤ p + 1476 := by exact_mod_cast h2
  have := nextPrime_min h1' hq
  unfold gapAt; omega

theorem gap_lt' (hS : LeanLab.DERZ1997.Schoenfeld61) (hG : GapBound1476) {p x : ℕ}
    (hp : p.Prime) (hpx : p ≤ x) (hx : 23 * 10 ^ 8 ≤ x) :
    (gapAt p : ℝ) < √(x : ℝ) * Real.log x ^ 2 / (4 * π) := by
  have hxR : (23 * 10 ^ 8 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hLx := log_ge_21_5 hxR
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  obtain ⟨hq1, hq2⟩ := nextPrime_spec p
  rcases Nat.lt_or_ge (4 * 10 ^ 18) (p + 1476) with hbig | hsmall
  · have hp13 : 23 * 10 ^ 8 ≤ p := by omega
    have hpR : (23 * 10 ^ 8 : ℝ) ≤ p := by exact_mod_cast hp13
    have h2p := nextPrime_le_two_mul (p := p) hp.one_lt.le
    set q := nextPrime p with hq
    have hθ := theta_before_next p
    rw [← hq] at hθ
    have hcast : ((q - 1 : ℕ) : ℝ) = (p : ℝ) + (gapAt p : ℝ) - 1 := by
      unfold gapAt; rw [← hq]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have hg1 : (1 : ℝ) ≤ gapAt p := by unfold gapAt; exact_mod_cast (by omega : 1 ≤ q - p)
    have hS1 := hS ((q - 1 : ℕ) : ℝ) (by rw [hcast]; linarith)
    have hS2 := hS (p : ℝ) hpR
    have hgp : (gapAt p : ℝ) ≤ p := by unfold gapAt; exact_mod_cast (by omega : q - p ≤ p)
    have hkey : (gapAt p : ℝ) - 1 < B p + B (p + gapAt p - 1) := by
      rw [hθ, hcast] at hS1
      have a1 := (abs_lt.mp hS1).1
      have a2 := (abs_lt.mp hS2).2
      unfold B; linarith
    refine (core hpR hg1 hgp hkey).trans_le ?_
    have hpx' : (p : ℝ) ≤ x := by exact_mod_cast hpx
    have hLp := log_ge_21_5 hpR
    gcongr
  · have h1476 := gapAt_le_1476 hG hp hsmall
    have : (gapAt p : ℝ) ≤ 1476 := by exact_mod_cast h1476
    have hsx : (47958 : ℝ) ≤ √(x : ℝ) := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
    have k1 : (47958 : ℝ) * 21.5 ^ 2 ≤ √(x : ℝ) * Real.log x ^ 2 :=
      mul_le_mul hsx (pow_le_pow_left₀ (by norm_num) hLx 2) (by norm_num) (Real.sqrt_nonneg _)
    rw [lt_div_iff₀ (by positivity)]
    clear hsmall h1476 hq1 hq2 hx hxR hpx
    have k2 : (gapAt p : ℝ) * (4 * π) ≤ 1476 * (4 * π) :=
      mul_le_mul_of_nonneg_right this (by positivity)
    have k3 : (1476 : ℝ) * (4 * π) < 47958 * 21.5 ^ 2 := by nlinarith
    linarith

/-- **Kaniecki Lemma 6** CONDITIONAL ON `Schoenfeld61` and the 1476 table. -/
theorem lemma6' (hS : LeanLab.DERZ1997.Schoenfeld61) (hG : GapBound1476) (x : ℕ)
    (hx : 23 * 10 ^ 8 ≤ x) :
    (lam x : ℝ) < 1 / (4 * π) * √((1 + 1 / 16597) * x) * Real.log x ^ 2 := by
  have hx7 : ¬ x ≤ 7 := by omega
  have hne : ((Finset.range (x + 1)).filter Nat.Prime).Nonempty :=
    ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩⟩
  obtain ⟨p, hpmem, hpeq⟩ := Finset.exists_mem_eq_sup _ hne gapAt
  rw [Finset.mem_filter, Finset.mem_range] at hpmem
  have hlam : lam x = gapAt p := by unfold lam; rw [if_neg hx7, hpeq]
  rw [hlam]
  refine (gap_lt' hS hG hpmem.2 (by omega) hx).trans_le ?_
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hsq : √(x : ℝ) ≤ √((1 + 1 / 16597) * x) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]
  gcongr

/-- Even Goldbach to `1480`, by the kernel. -/
theorem evenGoldbachUpTo_1480 : EvenGoldbachUpTo 1480 :=
  allEvenGB_sound 1480 (by decide +kernel)

/-- Odd `m` with `7 ≤ m ≤ 1.405 · 10^12` is a sum of three primes, from the 1476 table and
even Goldbach to `1480`. -/
theorem odd_m_three' (hG : GapBound1476) {m : ℕ} (ho : Odd m) (h7 : 7 ≤ m)
    (hm : m ≤ 1405 * 10 ^ 9) : IsTernarySum m := by
  classical
  have h3 : (3 : ℕ).Prime := Nat.prime_three
  set p := Nat.findGreatest Nat.Prime (m - 4) with hp
  have hpP : p.Prime := Nat.findGreatest_spec (m := 3) (by omega) h3
  have hp3 : 3 ≤ p := Nat.le_findGreatest (by omega) h3
  have hpm : p ≤ m - 4 := Nat.findGreatest_le _
  obtain ⟨hn1, hn2⟩ := nextPrime_spec p
  have hnm : m - 4 < nextPrime p := by
    by_contra h
    exact Nat.findGreatest_is_greatest (P := Nat.Prime) hn1 (by omega) hn2
  have hg := gapAt_le_1476 hG hpP (by omega)
  unfold gapAt at hg
  have hpo : Odd p := hpP.odd_of_ne_two (by omega)
  have hev : Even (m - p) := Nat.Odd.sub_odd ho hpo
  obtain ⟨q, r, hq, hr, hqr⟩ :=
    evenGoldbachUpTo_1480 (m - p) hev (by omega) (by omega)
  exact ⟨p, q, r, hpP, hq, hr, by omega⟩

/-- **Kaniecki, odd half**, CONDITIONAL ON the interval statement, the large-`n` input and
the 1476 table; no Young-Potler. -/
theorem kaniecki_odd_of' {N₀ : ℕ} (hI : IntervalProp (14045 * 10 ^ 8) N₀)
    (hCW : ∀ n : ℕ, Odd n → N₀ < n → IsTernarySum n) (hG : GapBound1476) :
    ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := by
  intro n ho h1
  rcases Nat.lt_or_ge N₀ n with hbig | hsmall
  · obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := hCW n ho hbig
    exact (((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add
      (AtMostPrimes.prime hr)).mono (by norm_num)
  rcases Nat.lt_or_ge n 10 with hlow | hn
  · obtain ⟨k, rfl⟩ := ho
    have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact (AtMostPrimes.prime Nat.prime_three).mono (by norm_num)
    · exact (AtMostPrimes.prime (by norm_num : Nat.Prime 5)).mono (by norm_num)
    · exact (AtMostPrimes.prime (by norm_num : Nat.Prime 7)).mono (by norm_num)
    · exact ((AtMostPrimes.prime Nat.prime_two).add
        (AtMostPrimes.prime (by norm_num : Nat.Prime 7))).mono (by norm_num)
  obtain ⟨p₁, p₂, h1', o1, h2', o2, hle, hm⟩ := step_m hI (by omega) hsmall
  have hpp : AtMostPrimes 2 (p₁ + p₂) :=
    (AtMostPrimes.prime h1').add (AtMostPrimes.prime h2')
  have hmo : Odd (n - (p₁ + p₂)) := Nat.Odd.sub_even (by omega) ho (o1.add_odd o2)
  have hn' : n = (p₁ + p₂) + (n - (p₁ + p₂)) := by omega
  rcases Nat.lt_or_ge (n - (p₁ + p₂)) 7 with h5 | h7
  · have h5' : n - (p₁ + p₂) = 5 := by
      obtain ⟨k, hk⟩ := hmo; omega
    rw [hn', h5']
    exact (hpp.add (show AtMostPrimes 2 5 from
      (AtMostPrimes.prime Nat.prime_two).add (AtMostPrimes.prime Nat.prime_three))).mono
      (by norm_num)
  · obtain ⟨p, q, r, hp, hq, hr, hs⟩ := odd_m_three' hG hmo h7 (by omega)
    rw [hn', ← hs]
    exact hpp.add (((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add
      (AtMostPrimes.prime hr))

end LeanLab.KanieckiGap

