module

public import Mathlib
public import LeanLab.KanieckiGap.Lemma6Gap
public import LeanLab.Dudek2014.Statements

/-!
Unit U-5474, CLOUD 20261019T1116Z-cloud23, from sweep candidate C3, I-5061.

Kaniecki's Lemma 6, `λ(x) < (1/4π) √((1 + 1/16597) x) log² x` for `x ≥ 2.3 · 10^9`, without
Schoenfeld (6.1): gaps with right end below `4 · 10^18` from the 1476 table, larger gaps from
Dudek 2014 Theorem 2, P0100, a prime in `(y - (4/π)√y log y, y]` for every `y ≥ 2` under RH.
For `x ≥ 3.9 · 10^18`, `1 + (4/π) √(2x) log(2x)` is about half of `√x log² x / (4π)`.
This sidesteps the θ or ψ QUESTION on Schoenfeld (6.1). Dudek's Theorem 2 is in the lab as
the cited `Dudek2014.theorem2` and as `Dudek2014.Section22.theorem2_of_lemma4`, CONDITIONAL ON
Lemma 4, the page 5 zero sums and Schoenfeld's ψ - θ bounds.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel. Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.KanieckiGap
open Real
open LeanLab.GoldbachGaps.Sumset (GapBound1476)

theorem gap_lt_dudek (hD : ∀ y : ℝ, 2 ≤ y → LeanLab.Dudek2014.PrimeInDudekInterval y)
    (hG : GapBound1476) {p x : ℕ} (hp : p.Prime) (hpx : p ≤ x) (hx : 23 * 10 ^ 8 ≤ x) :
    (gapAt p : ℝ) < √(x : ℝ) * Real.log x ^ 2 / (4 * π) := by
  have hxR : (23 * 10 ^ 8 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hLx := log_ge_21_5 hxR
  have hpi := Real.pi_lt_d2
  have hpi' := Real.pi_gt_d2
  have hpi0 := Real.pi_pos
  obtain ⟨hq1, hq2⟩ := nextPrime_spec p
  rcases Nat.lt_or_ge (4 * 10 ^ 18) (p + 1476) with hbig | hsmall
  · -- Dudek at y = q - 1
    have h2p := nextPrime_le_two_mul (p := p) hp.one_lt.le
    set q := nextPrime p with hq
    have hyR : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    obtain ⟨r, hr, hr1, hr2⟩ := hD ((q - 1 : ℕ) : ℝ) (by
      rw [hyR]; have : (4 * 10 ^ 18 : ℝ) < p + 1476 := by exact_mod_cast hbig
      have : (p : ℝ) < q := by exact_mod_cast hq1
      linarith)
    rw [hyR] at hr1 hr2
    have hrp : r ≤ p := by
      by_contra h
      push_neg at h
      have := nextPrime_min h hr
      rw [← hq] at this
      have : (r : ℝ) ≥ q := by exact_mod_cast this
      linarith
    have hrpR : (r : ℝ) ≤ p := by exact_mod_cast hrp
    -- g < 1 + dudekH (q - 1) ≤ 1 + (4/π) √(2x) log(2x)
    have hqx : (q : ℝ) - 1 ≤ 2 * x := by
      have : (q : ℝ) ≤ 2 * p := by exact_mod_cast h2p
      have : (p : ℝ) ≤ x := by exact_mod_cast hpx
      linarith
    have hq1R : (1 : ℝ) ≤ (q : ℝ) - 1 := by
      have : (4 * 10 ^ 18 : ℝ) < p + 1476 := by exact_mod_cast hbig
      have : (p : ℝ) < q := by exact_mod_cast hq1
      linarith
    have hgap : (gapAt p : ℝ) < 1 + 4 / π * √(2 * (x : ℝ)) * Real.log (2 * x) := by
      have e : (gapAt p : ℝ) = (q : ℝ) - p := by
        unfold gapAt; rw [← hq, Nat.cast_sub hq1.le]
      have hdu : LeanLab.Dudek2014.dudekH ((q : ℝ) - 1) ≤
          4 / π * √(2 * (x : ℝ)) * Real.log (2 * x) := by
        unfold LeanLab.Dudek2014.dudekH
        have hl : Real.log ((q : ℝ) - 1) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hqx
        have hl0 : 0 ≤ Real.log ((q : ℝ) - 1) := Real.log_nonneg hq1R
        have hs : √((q : ℝ) - 1) ≤ √(2 * (x : ℝ)) := Real.sqrt_le_sqrt hqx
        apply mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hl hl0 (by positivity)
      rw [e]; linarith
    -- the numerical comparison at x ≥ 3.9e18
    have hxbig : (3.9e18 : ℝ) ≤ x := by
      have : (4 * 10 ^ 18 : ℝ) < p + 1476 := by exact_mod_cast hbig
      have : (p : ℝ) ≤ x := by exact_mod_cast hpx
      linarith
    clear hbig h2p hrp hrpR hr1 hr2 hqx hq1R hx hpx hq1 hq2 hyR hr
    have hL42 : 42 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]
      have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 42
      rw [← Real.exp_nat_mul, show ((42 : ℕ) : ℝ) * 1 = 42 by norm_num] at h
      have : (2.7182818286 : ℝ) ^ 42 ≤ 3.9e18 := by norm_num
      linarith
    have hs2 : √(2 * (x : ℝ)) ≤ 1.41422 * √(x : ℝ) := by
      rw [Real.sqrt_mul (by norm_num)]
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hl2 : Real.log (2 * x) ≤ Real.log x + 0.6932 := by
      rw [Real.log_mul (by norm_num) hx0.ne']; have := Real.log_two_lt_d9; linarith
    have hsx : (10 ^ 9 : ℝ) ≤ √(x : ℝ) := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
    set s := √(x : ℝ)
    set L := Real.log x
    have hq4 : 4 / π ≤ 1.2733 := by have := Real.pi_gt_d4; rw [div_le_iff₀ hpi0]; nlinarith
    have hA : 4 / π * √(2 * (x : ℝ)) * Real.log (2 * x) ≤ 1.2733 * (1.41422 * s) * (L + 0.6932) := by
      have hl0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
      apply mul_le_mul (mul_le_mul hq4 hs2 (Real.sqrt_nonneg _) (by norm_num)) hl2 hl0
        (by positivity)
    rw [lt_div_iff₀ (by positivity)]
    have key : (1 + 1.2733 * (1.41422 * s) * (L + 0.6932)) * (4 * 3.15) < s * L ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hL42 (by positivity : (0 : ℝ) ≤ s)]
    have hg0 : (0 : ℝ) ≤ gapAt p := by positivity
    have : (gapAt p : ℝ) * (4 * π) ≤ (1 + 1.2733 * (1.41422 * s) * (L + 0.6932)) * (4 * 3.15) := by
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    linarith
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

/-- **Kaniecki Lemma 6** CONDITIONAL ON Dudek's Theorem 2 conclusion and the 1476 table; no
Schoenfeld (6.1). -/
theorem lemma6_dudek (hD : ∀ y : ℝ, 2 ≤ y → LeanLab.Dudek2014.PrimeInDudekInterval y)
    (hG : GapBound1476) (x : ℕ) (hx : 23 * 10 ^ 8 ≤ x) :
    (lam x : ℝ) < 1 / (4 * π) * √((1 + 1 / 16597) * x) * Real.log x ^ 2 := by
  have hx7 : ¬ x ≤ 7 := by omega
  have hne : ((Finset.range (x + 1)).filter Nat.Prime).Nonempty :=
    ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩⟩
  obtain ⟨p, hpmem, hpeq⟩ := Finset.exists_mem_eq_sup _ hne gapAt
  rw [Finset.mem_filter, Finset.mem_range] at hpmem
  have hlam : lam x = gapAt p := by unfold lam; rw [if_neg hx7, hpeq]
  rw [hlam]
  refine (gap_lt_dudek hD hG hpmem.2 (by omega) hx).trans_le ?_
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hsq : √(x : ℝ) ≤ √((1 + 1 / 16597) * x) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]
  gcongr

end LeanLab.KanieckiGap

