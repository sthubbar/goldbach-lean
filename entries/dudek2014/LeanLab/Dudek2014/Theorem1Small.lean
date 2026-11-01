module

public import Mathlib
public import LeanLab.Dudek2014.Statements
public import LeanLab.ChebyshevExplicit.Psi30

/-!
P0100 Dudek 2014, Theorem 1, Cramér's theorem, the range `2 ≤ x < 10^12` WITHOUT RH, unit U-6722,
CLOUD 20261020T2018Z-cloud50. With `c = 10^8` the interval `(x, x + c √x log x]` reaches past
`x log x`, so Chebyshev's lower bound `π(N) ≥ (0.9212 N - 5 log N)/log N` of
`ChebyshevExplicit.Psi30`, PROVED there with no cited input, and the trivial `π(x) ≤ x + 1` give
more than `√x` primes. No cited input. KNOWN mathematics, Chebyshev 1852.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/

@[expose] public section

namespace LeanLab.Dudek2014.Theorem1H
open Real Finset

/-- `primesIn x h` is monotone in `h`. -/
theorem primesIn_mono {x h₁ h₂ : ℝ} (hh : h₁ ≤ h₂) : primesIn x h₁ ≤ primesIn x h₂ := by
  unfold primesIn
  apply card_le_card
  apply filter_subset_filter
  have := Nat.floor_le_floor (show x + h₁ ≤ x + h₂ by linarith)
  intro i hi
  simp only [mem_range] at hi ⊢
  omega

/-- `primesIn x h ≥ π(⌊x + h⌋) - ⌊x⌋ - 1`. -/
theorem primesIn_ge (x h : ℝ) :
    (Nat.primeCounting ⌊x + h⌋₊ : ℝ) - ((⌊x⌋₊ : ℝ) + 1) ≤ primesIn x h := by
  have hA : Nat.primeCounting ⌊x + h⌋₊ ≤ primesIn x h + (⌊x⌋₊ + 1) := by
    rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting', Nat.primesBelow]
    unfold primesIn
    calc #((range (⌊x + h⌋₊ + 1)).filter Nat.Prime)
        ≤ #(((range (⌊x + h⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ x < (p : ℝ))) ∪
            range (⌊x⌋₊ + 1)) := by
          apply card_le_card
          intro p hp
          simp only [mem_filter, mem_range, mem_union] at hp ⊢
          by_cases hxp : x < (p : ℝ)
          · left; exact ⟨hp.1, hp.2, hxp⟩
          · right
            push Not at hxp
            have := Nat.le_floor hxp
            omega
      _ ≤ _ := (card_union_le _ _).trans (by rw [card_range])
  have : ((Nat.primeCounting ⌊x + h⌋₊ : ℕ) : ℝ) ≤ ((primesIn x h + (⌊x⌋₊ + 1) : ℕ) : ℝ) := by
    exact_mod_cast hA
  push_cast at this
  linarith

/-- `log y ≤ 48` for `0 < y ≤ 3 · 10^20`. -/
theorem log_le_48 {y : ℝ} (hy : 0 < y) (hy' : y ≤ 3 * 10 ^ 20) : Real.log y ≤ 48 := by
  rw [Real.log_le_iff_le_exp hy]
  have he : Real.exp 48 = Real.exp 1 ^ 48 := by rw [← Real.exp_nat_mul]; norm_num
  have h1 : (2.718 : ℝ) ^ 48 ≤ Real.exp 1 ^ 48 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 48
  rw [he]
  have : (3 * 10 ^ 20 : ℝ) ≤ (2.718 : ℝ) ^ 48 := by norm_num
  linarith

/-- **Cramér's theorem with `c = 10^8` for `2 ≤ x < 10^12`, PROVED with no cited input and no
RH**: more than `√x` primes in `(x, x + 10^8 √x log x]`. -/
theorem small_range {x : ℝ} (hx : 2 ≤ x) (hx' : x < 10 ^ 12) :
    √x < primesIn x (10 ^ 8 * √x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  set s := √x with hs
  set L := Real.log x with hL
  have hs2 : s ^ 2 = x := sq_sqrt hx0.le
  have hs0 : 0 < s := sqrt_pos.2 hx0
  have hs1 : 1.414 ≤ s := by
    rw [hs, le_sqrt (by norm_num) hx0.le]; linarith
  have hs6 : s ≤ 10 ^ 6 := by
    rw [hs, sqrt_le_left (by norm_num)]; linarith
  have hL1 : 0.6931 ≤ L := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hx
    linarith
  have hLs : L ≤ 2 * s := by
    have e : L = 2 * Real.log s := by
      rw [hL, hs, Real.log_sqrt hx0.le]; ring
    have := Real.log_le_sub_one_of_pos hs0
    linarith
  set H := 10 ^ 8 * s * L with hH
  have hH0 : 6.9e7 * s ≤ H := by rw [hH]; nlinarith
  set N := ⌊x + H⌋₊ with hN
  have hN1 : x + H - 1 ≤ (N : ℝ) := by
    have := Nat.lt_floor_add_one (x + H); linarith
  have hN2 : (N : ℝ) ≤ x + H := Nat.floor_le (by positivity)
  have hNpos : (30 : ℝ) ≤ N := by nlinarith
  have hN30 : 30 ≤ N := by exact_mod_cast hNpos
  have hlN : Real.log N ≤ 48 := by
    apply log_le_48 (by linarith)
    have : H ≤ 10 ^ 8 * s * (2 * s) := by rw [hH]; nlinarith
    nlinarith
  have hlN0 : 0 < Real.log N := Real.log_pos (by linarith)
  have hpi := LeanLab.ChebyshevExplicit.pi_ge_chebyshev30 N hN30
  rw [div_le_iff₀ hlN0] at hpi
  set P := (Nat.primeCounting N : ℝ)
  have hP : s ^ 2 + s + 1 < P := by
    by_contra hc
    push Not at hc
    have h1 : P * Real.log N ≤ (s ^ 2 + s + 1) * 48 := by
      have : 0 ≤ P := Nat.cast_nonneg _
      nlinarith
    nlinarith
  have hge := primesIn_ge x H
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  rw [← hN] at hge
  linarith

end LeanLab.Dudek2014.Theorem1H

