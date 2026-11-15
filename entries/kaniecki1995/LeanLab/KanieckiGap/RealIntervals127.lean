module

public import LeanLab.KanieckiGap.Decomp127

/-!
P0022, page 371. Extend the corrected half-open Lemma 7 to real arguments.
The printed open interval statement remains sealed and false at six.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.KanieckiGap.RealIntervals127

open Real

/-- Page 371. The real gap function is always at least two. -/
theorem two_le_lam (x : ℝ) : 2 ≤ LeanLab.Kaniecki1995.lam x := by
  by_cases hx : x ≤ 7
  · simp only [LeanLab.Kaniecki1995.lam, if_pos hx]
    exact le_rfl
  · have h := LeanLab.Kaniecki1995.gap_le_lam (p := 3)
      (lt_of_not_ge hx) Nat.prime_three (by norm_num; linarith)
    rw [Decomp127.nextPrime_eq, KanieckiGap.nextPrime_three] at h
    exact h

/-- Page 371. Enlarging the real cutoff cannot decrease the maximal gap. -/
theorem lam_mono {x y : ℝ} (hxy : x ≤ y) :
    LeanLab.Kaniecki1995.lam x ≤ LeanLab.Kaniecki1995.lam y := by
  by_cases hx : x ≤ 7
  · simpa only [LeanLab.Kaniecki1995.lam, if_pos hx] using two_le_lam y
  · have hy : ¬ y ≤ 7 := by linarith
    unfold LeanLab.Kaniecki1995.lam
    rw [if_neg hx, if_neg hy]
    apply Finset.sup_mono
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by have := Nat.floor_mono hxy; omega, hp.2⟩

/-- Page 371. Taking a natural floor gives a lower bound on the real maximal gap.
This is an inequality because the branch at seven need not agree. -/
theorem lam_floor_le (x : ℝ) (hx : 0 ≤ x) :
    KanieckiGap.lam ⌊x⌋₊ ≤ LeanLab.Kaniecki1995.lam x := by
  rw [← Decomp127.lam_nat_eq]
  exact lam_mono (Nat.floor_le hx)

/-- Page 371. The nested natural gap at the floor is bounded by the nested real gap. -/
theorem nested_lam_floor_le (x : ℝ) (hx : 0 ≤ x) :
    KanieckiGap.lam (KanieckiGap.lam ⌊x⌋₊) ≤
      LeanLab.Kaniecki1995.lam (LeanLab.Kaniecki1995.lam x) := by
  rw [← Decomp127.lam_nat_eq]
  exact lam_mono (by exact_mod_cast lam_floor_le x hx)

/-- Page 371, Lemma 7 with the right endpoint included. Every real x greater
than four has two odd primes whose sum lies in the interval open on the left
and closed on the right. No RH or cited analytic input is used. -/
theorem lemma7_closed_real (x : ℝ) (hx : 4 < x) :
    ∃ p q : ℕ, p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧
      x < ((p + q : ℕ) : ℝ) ∧
      ((p + q : ℕ) : ℝ) ≤ x +
        (LeanLab.Kaniecki1995.lam (LeanLab.Kaniecki1995.lam x) : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  by_cases hf : 4 < ⌊x⌋₊
  · obtain ⟨p, q, hp, op, hq, oq, hlo, hhi⟩ := KanieckiGap.lemma7_closed ⌊x⌋₊ hf
    have hfloor : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have hlo' : (⌊x⌋₊ : ℝ) + 1 ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hlo
    refine ⟨p, q, hp, op, hq, oq, hfloor.trans_le hlo', ?_⟩
    have hhi' : ((p + q : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) +
        (KanieckiGap.lam (KanieckiGap.lam ⌊x⌋₊) : ℝ) := by exact_mod_cast hhi
    have hnest : (KanieckiGap.lam (KanieckiGap.lam ⌊x⌋₊) : ℝ) ≤
        (LeanLab.Kaniecki1995.lam (LeanLab.Kaniecki1995.lam x) : ℝ) := by
      exact_mod_cast nested_lam_floor_le x hx0
    linarith [Nat.floor_le hx0]
  · have hx5 : x < 5 := (Nat.floor_lt hx0).mp (by omega : ⌊x⌋₊ < 5)
    have htwo : (2 : ℝ) ≤
        (LeanLab.Kaniecki1995.lam (LeanLab.Kaniecki1995.lam x) : ℝ) := by
      exact_mod_cast two_le_lam (LeanLab.Kaniecki1995.lam x)
    exact ⟨3, 3, Nat.prime_three, by decide, Nat.prime_three, by decide,
      by norm_num; linarith, by norm_num; linarith⟩

end LeanLab.KanieckiGap.RealIntervals127
