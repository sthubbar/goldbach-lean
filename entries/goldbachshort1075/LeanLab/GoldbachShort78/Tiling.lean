module

public import LeanLab.GoldbachShort78.Statements

/-!
Primes in real intervals, and the tiling of a window `[x − 2Y, x − Y]` by short intervals.

AI wrote the Lean code, Codex, OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.GoldbachShort78

/-- The primes `p` with `a < p ≤ b`, for real `a`, `b`. -/
noncomputable def primeInterval (a b : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌈b⌉₊).filter fun p => a < (p : ℝ) ∧ (p : ℝ) ≤ b ∧ p.Prime

/-- Membership in a real prime interval has no rounding condition. -/
theorem mem_primeInterval {a b : ℝ} {p : ℕ} :
    p ∈ primeInterval a b ↔ a < (p : ℝ) ∧ (p : ℝ) ≤ b ∧ p.Prime := by
  classical
  simp only [primeInterval, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨Nat.zero_le _, ?_⟩, h⟩
    exact_mod_cast le_trans h.2.1 (Nat.le_ceil b)

/-- Disjoint right tiles contribute their total prime count to the containing window. -/
theorem right_tiles_count {x Y k : ℕ} {B L d : ℝ} (hL : 0 ≤ L)
    (hleft : (x - 2 * Y : ℕ) ≤ B - (k : ℝ) * L) (hright : B ≤ (x - Y : ℕ))
    (hcount : ∀ i ∈ Finset.range k,
      d ≤ ((primeInterval (B - ((i : ℝ) + 1) * L) (B - (i : ℝ) * L)).card : ℝ)) :
    (k : ℝ) * d ≤ ((primeWindow x Y).card : ℝ) := by
  classical
  let tile := fun i : ℕ => primeInterval (B - ((i : ℝ) + 1) * L) (B - (i : ℝ) * L)
  have hdisj : (↑(Finset.range k) : Set ℕ).PairwiseDisjoint tile := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := mem_primeInterval.mp hp
    have hq' := mem_primeInterval.mp hq
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · have hijr : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij'
      nlinarith [mul_nonneg (sub_nonneg.mpr hijr) hL]
    · have hijr : (j : ℝ) + 1 ≤ i := by exact_mod_cast hij'
      nlinarith [mul_nonneg (sub_nonneg.mpr hijr) hL]
  have hsub : (Finset.range k).biUnion tile ⊆ primeWindow x Y := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    have hp' := mem_primeInterval.mp hp
    have hik : (i : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.mp hi
    have hip : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hpl : (x - 2 * Y : ℕ) ≤ p := by
      have : ((x - 2 * Y : ℕ) : ℝ) ≤ p := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hik) hL]
      exact_mod_cast this
    have hpr : p ≤ x - Y := by
      have : (p : ℝ) ≤ (x - Y : ℕ) := by nlinarith [mul_nonneg hip hL]
      exact_mod_cast this
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpl, hpr⟩, hp'.2.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcard
  calc
    (k : ℝ) * d = ∑ i ∈ Finset.range k, d := by simp
    _ ≤ ∑ i ∈ Finset.range k, ((tile i).card : ℝ) := Finset.sum_le_sum hcount
    _ = ((∑ i ∈ Finset.range k, (tile i).card : ℕ) : ℝ) := by simp
    _ ≤ ((primeWindow x Y).card : ℝ) := by exact_mod_cast hcard

/-- Tiles of length `L` cover at least one quarter of a window of length `Y`.
The case of one tile keeps the endpoint exponent with no loss in `ε`. -/
theorem exists_tile_number {Y L : ℝ} (hL : 0 < L) (hLY : L ≤ Y) :
    ∃ k : ℕ, 0 < k ∧ (k : ℝ) * L ≤ Y ∧
      (k : ℝ) * L ≤ max (Y / 2) L ∧ Y / 4 ≤ (k : ℝ) * L := by
  by_cases h : 1 ≤ Y / (2 * L)
  · refine ⟨⌊Y / (2 * L)⌋₊, ?_, ?_, ?_, ?_⟩
    · have := (Nat.one_le_floor_iff _).mpr h
      omega
    · have hf := Nat.floor_le (by positivity : 0 ≤ Y / (2 * L))
      have hf' := (le_div_iff₀ (by positivity : 0 < 2 * L)).mp hf
      linarith
    · have hf := Nat.floor_le (by positivity : 0 ≤ Y / (2 * L))
      have hf' := (le_div_iff₀ (by positivity : 0 < 2 * L)).mp hf
      exact le_trans (by linarith) (le_max_left _ _)
    · have hf := Nat.lt_floor_add_one (Y / (2 * L))
      have hf' := (div_lt_iff₀ (by positivity : 0 < 2 * L)).mp hf
      have hk : (1 : ℝ) ≤ ⌊Y / (2 * L)⌋₊ := by
        exact_mod_cast (Nat.one_le_floor_iff _).mpr h
      nlinarith [mul_nonneg (sub_nonneg.mpr hk) hL.le]
  · refine ⟨1, by decide, by simpa using hLY, ?_, ?_⟩
    · simp
    · have hy : Y < 2 * L := (div_lt_one (by positivity : 0 < 2 * L)).mp (lt_of_not_ge h)
      simp only [Nat.cast_one, one_mul]
      linarith

/-- A base at least `x/4` retains at least one quarter of `x^a` for `0 ≤ a ≤ 1`. -/
theorem quarter_rpow_le {x t a : ℝ} (hx : 0 ≤ x) (ht : x / 4 ≤ t)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : x ^ a / 4 ≤ t ^ a := by
  have ht0 : 0 ≤ t := by linarith
  have h := Real.rpow_le_rpow hx (show x ≤ 4 * t by linarith) ha0
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) ht0] at h
  have h4 : (4 : ℝ) ^ a ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) ha1
    simpa using this
  have htpa : 0 ≤ t ^ a := Real.rpow_nonneg ht0 _
  nlinarith [mul_nonneg (sub_nonneg.mpr h4) htpa]

end LeanLab.GoldbachShort78
