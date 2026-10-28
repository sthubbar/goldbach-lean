module

public import LeanLab.Halupczok2012.Statements

/-!
# Halupczok 2012, Theorem 1.2: the all `q` form with a vanishing main term

AI wrote the Lean code, Claude, Anthropic. Binary Goldbach is open; ternary Goldbach is a
theorem, Helfgott 2013.

The defect. As printed, Theorem 1.2 of the paper, JTNB p. 333, sums over all `q ≤ Q` with no
condition `(a, q) = 1`, its right side is `≪ Y₁ Y₂ L^{-A}` with no factor `Q`, and the printed
`T(n, q, a)` does not vanish when `(a, q) > 1`; for example `T(n, 3, 3) ≈ 0.767`. For such `q`
the prime sum is empty once `q ≤ X₁`, so the single term `q = 3` at `a = 3` is about
`0.767 Y₁ Y₂`, larger than the claimed bound. The proof says it assumes `(q, a) = 1` without
loss of generality.

The repair. Take the main term to vanish when `(a, q) > 1`, as the binary singular series
`S(r, q, a)` of the paper's display 1 does. `T0` is that convention. Then each non-coprime
prime sum is exactly zero once `q ≤ X₁`, since the only candidate `p₁` is a prime factor of `q`,
below `X₁`.

* `ternSum_noncoprime`: for `1 ≤ q ≤ X₁` and `(a, q) ≠ 1` the prime sum of Theorem 1.2 is `0`.
* `theorem2Zeroed_of_theorem2`: the coprime `Theorem2` implies `Theorem2Zeroed`, the sum over
  ALL `q ≤ Q` with `T0`, under the extra hypothesis `Q ≤ X₁`, which the paper's
  `Q ≪ Y₁ X₁^{-1/2} L^{-B}` gives for large `X₁`. Adding `(a, q) = 1` to the printed statement is
  the same theorem restricted to coprime `q`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset

/-- `T(n, q, a)` set to `0` when `(a, q) > 1`, as `S(r, q, a)` is in display 1. -/
noncomputable def T0 (n q : ℕ) (a : ℤ) : ℝ := if Int.gcd a q = 1 then T n q a else 0

/-- **The non-coprime prime sums vanish.** -/
theorem ternSum_noncoprime {n q : ℕ} {a : ℤ} {X1 Y1 X2 Y2 : ℝ} (hq : 1 ≤ q)
    (hg : Int.gcd a q ≠ 1) (hqX : (q : ℝ) ≤ X1) : ternSum n X1 Y1 X2 Y2 q a = 0 := by
  unfold ternSum
  apply Finset.sum_eq_zero
  intro x hx
  exfalso
  rw [Finset.mem_filter] at hx
  obtain ⟨-, hp1, -, -, -, hX1, -, -, -, hc⟩ := hx
  obtain ⟨d, hd, hdg⟩ := Nat.exists_prime_and_dvd hg
  have hdq' : (d : ℤ) ∣ (q : ℤ) := (Int.natCast_dvd_natCast.mpr hdg).trans (Int.gcd_dvd_right a q)
  have hdq : d ∣ q := Int.natCast_dvd_natCast.mp hdq'
  have hda : (d : ℤ) ∣ a := (Int.natCast_dvd_natCast.mpr hdg).trans (Int.gcd_dvd_left a q)
  have hx1 := prime_cong_noncoprime hp1 hd hc hdq hda
  have hdle : d ≤ q := Nat.le_of_dvd (by omega) hdq
  have : (x.1 : ℝ) ≤ q := by rw [hx1]; exact_mod_cast hdle
  linarith

/-- Theorem 2 over ALL `q ≤ Q` with the main term `T0`, plus `Q ≤ X₁`. -/
def Theorem2Zeroed : Prop :=
  ∀ A ε ε1 ε2 : ℝ, 0 < A → 0 < ε → 0 < ε1 → 0 < ε2 → ∃ B : ℝ, 0 < B ∧
  ∀ c : Fin 7 → ℝ, (∀ i, 0 < c i) → ∀ c7 : ℝ, 0 < c7 → ∀ a : ℤ, ∃ C Y0 : ℝ,
  ∀ (n : ℕ) (X1 Y1 X2 Y2 Q : ℝ), Y0 ≤ Y1 → Y0 ≤ Y2 → Thm2Hyp ε ε1 ε2 B c n X1 Y1 X2 Y2 Q →
    Q ≤ c7 * Y1 ^ (3 / 2 : ℝ) * ((n : ℝ) - X1) ^ (-(1 / 2) : ℝ) → (a : ℝ) ≤ (n : ℝ) - X1 - Y1 →
    Q ≤ X1 →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, |ternSum n X1 Y1 X2 Y2 q a - T0 n q a * Y1 * Y2|
      ≤ C * Y1 * Y2 * Real.log Y2 ^ (-A)

/-- **The all `q` form with `T0` follows from the coprime form.** -/
theorem theorem2Zeroed_of_theorem2 (h : Theorem2) : Theorem2Zeroed := by
  intro A ε ε1 ε2 hA hε hε1 hε2
  obtain ⟨B, hB, hrest⟩ := h A ε ε1 ε2 hA hε hε1 hε2
  refine ⟨B, hB, fun c hc c7 hc7 a => ?_⟩
  obtain ⟨C, Y0, hCY⟩ := hrest c hc c7 hc7 a
  refine ⟨C, Y0, fun n X1 Y1 X2 Y2 Q hY1 hY2 hH hQ ha hQX => ?_⟩
  have key := hCY n X1 Y1 X2 Y2 Q hY1 hY2 hH hQ ha
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 ⌊Q⌋₊) (fun q : ℕ => Int.gcd a (q : ℤ) = 1)]
  have hzero : ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => ¬ Int.gcd a (q : ℤ) = 1),
      |ternSum n X1 Y1 X2 Y2 q a - T0 n q a * Y1 * Y2| = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqQ⟩, hg⟩ := hq
    have hqR : (q : ℝ) ≤ Q := (Nat.le_floor_iff' (by omega)).mp hqQ
    rw [ternSum_noncoprime hq1 hg (hqR.trans hQX)]
    simp [T0, hg]
  rw [hzero, add_zero]
  have hcongr : ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      |ternSum n X1 Y1 X2 Y2 q a - T0 n q a * Y1 * Y2| =
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd a (q : ℤ) = 1),
      |ternSum n X1 Y1 X2 Y2 q a - T n q a * Y1 * Y2| := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_filter] at hq
    simp [T0, hq.2]
  rw [hcongr]
  exact key

end LeanLab.Halupczok2012
