module

public import LeanLab.Halupczok2012.U1462Tails

/-!
# P0077 Halupczok 2012, `Theorem5` shrunk to its minimal window scale, unit U-1493

AI wrote the Lean code, Claude, run 20261022T1603Z-23862. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

`Theorem5` is the paper's adaptation of Perelli-Pintz 1993, arXiv 1212.4406v1 Theorem 5, journal
JTNB 25 2013 Theorem 2.3 p. 339. It allows every window length `R` with
`c₂ Y^{1/3+ε} ≤ R ≤ c₃ Y`. Here:

* `Theorem5Min`: the same mean square bound, but only for windows of the MINIMAL scale
  `c₂ Y^{1/3+ε} ≤ R ≤ 2 c₂ Y^{1/3+ε}`, an extra hypothesis. A weaker Prop.
* `theorem5_of_min : Theorem5Min → Theorem5`. PROVED, by cutting `[X₁, X₁ + R]` into
  `m = ⌊R / (c₂ Y^{1/3+ε})⌋` windows of length `R/m` and summing.
* `theorem5Min_of_theorem5 : Theorem5 → Theorem5Min`. PROVED, so the two are equivalent.
* `theorem2Zeroed_U1493`: the F-0008 repair CONDITIONAL ON `Theorem3` and `Theorem5Min`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset

/-- **Theorem 5 at the minimal window scale.** Same as `Theorem5`, with the extra hypothesis
`R ≤ 2 c₂ Y^{1/3+ε}`. Cited input, a weakening of the paper's Theorem 5. -/
def Theorem5Min : Prop :=
  ∀ A ε ε2 : ℝ, 0 < A → 0 < ε → 0 < ε2 →
  ∀ c1 c2 c3 c4 c5 : ℝ, 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → 0 < c5 →
  ∃ C Y0 : ℝ, ∀ X1 X2 Y R : ℝ, Y0 ≤ Y →
    c1 * X2 ^ (7 / 12 + ε2) ≤ Y → Y ≤ X2 → c2 * Y ^ (1 / 3 + ε) ≤ R → R ≤ c3 * Y →
    R ≤ 2 * (c2 * Y ^ (1 / 3 + ε)) → R ≤ X1 →
    0 ≤ 2 * X1 - X2 - Y → c4 * Y ≤ 2 * X1 - X2 - Y → 2 * X1 - X2 - Y ≤ c5 * Y →
    ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
      C * R * Y ^ 2 * Real.log Y ^ (-A)

/-- The number of pieces: `1 ≤ m`, `R₀ ≤ R/m < 2 R₀` for `m = ⌊R/R₀⌋₊` and `R₀ ≤ R`. -/
theorem floor_pieces {R R0 : ℝ} (hR0 : 0 < R0) (h : R0 ≤ R) :
    1 ≤ ⌊R / R0⌋₊ ∧ R0 ≤ R / ⌊R / R0⌋₊ ∧ R / ⌊R / R0⌋₊ ≤ 2 * R0 := by
  set t := R / R0 with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hR0]; linarith
  have hm1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht1)
  have hmR : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by linarith
  have hle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hRt : R = t * R0 := by rw [ht]; field_simp
  refine ⟨hm1, ?_, ?_⟩
  · rw [le_div_iff₀ hmpos, hRt]; nlinarith
  · rw [div_le_iff₀ hmpos, hRt]; nlinarith

/-- **`Theorem5Min` implies `Theorem5`.** PROVED. -/
theorem theorem5_of_min (h : Theorem5Min) : Theorem5 := by
  intro A ε ε2 hA hε hε2 c1 c2 c3 c4 c5 hc1 hc2 hc3 hc4 hc5
  obtain ⟨C, Y0, hC⟩ := h A ε ε2 hA hε hε2 c1 c2 c3 c4 (c5 + 2 * c3) hc1 hc2 hc3 hc4
    (by positivity)
  refine ⟨C, max Y0 1, ?_⟩
  intro X1 X2 Y R hY h1 h2 h3 h4 h5 h6 h7 h8
  have hY0 : Y0 ≤ Y := le_trans (le_max_left _ _) hY
  have hY1 : 1 ≤ Y := le_trans (le_max_right _ _) hY
  set R0 := c2 * Y ^ (1 / 3 + ε) with hR0def
  have hR0 : 0 < R0 := by rw [hR0def]; exact mul_pos hc2 (Real.rpow_pos_of_pos (by linarith) _)
  obtain ⟨hm1, hlo, hhi⟩ := floor_pieces hR0 h3
  set m := ⌊R / R0⌋₊ with hmdef
  have hm0 : 0 < m := hm1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hRpos : 0 < R := lt_of_lt_of_le hR0 h3
  have hRm_le : R / m ≤ R := div_le_self hRpos.le (by exact_mod_cast hm1)
  set g : ℕ → ℝ := fun k => (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 with hg
  have hgnn : ∀ k, 0 ≤ g k := fun k => sq_nonneg _
  have hpiece : ∀ j ∈ range m, ∑ k ∈ kRange (X1 + j * (R / m)) (R / m), g k ≤
      C * (R / m) * Y ^ 2 * Real.log Y ^ (-A) := by
    intro j hj
    have hj' : (j : ℝ) < m := by exact_mod_cast Finset.mem_range.mp hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjR : (j : ℝ) * (R / m) ≤ R := by
      rw [mul_div_assoc']; rw [div_le_iff₀ hmR]; nlinarith
    have hjR0 : 0 ≤ (j : ℝ) * (R / m) := by positivity
    apply hC (X1 + j * (R / m)) X2 Y (R / m) hY0 h1 h2 hlo (by linarith) hhi (by linarith)
      (by linarith) (by linarith)
    nlinarith
  calc ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2
      = ∑ k ∈ kRange X1 R, g k := rfl
    _ ≤ ∑ j ∈ range m, ∑ k ∈ kRange (X1 + j * (R / m)) (R / m), g k :=
        sum_kRange_le_pieces X1 R hRpos m hm0 g hgnn
    _ ≤ ∑ j ∈ range m, C * (R / m) * Y ^ 2 * Real.log Y ^ (-A) := Finset.sum_le_sum hpiece
    _ = C * R * Y ^ 2 * Real.log Y ^ (-A) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

/-- **`Theorem5` implies `Theorem5Min`.** PROVED, so the shrink loses nothing. -/
theorem theorem5Min_of_theorem5 (h : Theorem5) : Theorem5Min := by
  intro A ε ε2 hA hε hε2 c1 c2 c3 c4 c5 hc1 hc2 hc3 hc4 hc5
  obtain ⟨C, Y0, hC⟩ := h A ε ε2 hA hε hε2 c1 c2 c3 c4 c5 hc1 hc2 hc3 hc4 hc5
  exact ⟨C, Y0, fun X1 X2 Y R hY h1 h2 h3 h4 _ h5 h6 h7 h8 =>
    hC X1 X2 Y R hY h1 h2 h3 h4 h5 h6 h7 h8⟩

/-- `Theorem5` and `Theorem5Min` are equivalent. PROVED. -/
theorem theorem5_iff_min : Theorem5 ↔ Theorem5Min :=
  ⟨theorem5Min_of_theorem5, theorem5_of_min⟩

/-! ### Vacuity: the hypotheses of `Theorem5Min` hold for every large `Y` -/

/-- For every `Y ≥ 1`, `ε ≤ 2/3`, `ε₂ ≤ 5/12`: `X₁ = 3Y/2`, `X₂ = Y`, `R = Y^{1/3+ε}` and all
constants `1` satisfy every hypothesis of `Theorem5Min`, so no threshold `Y₀` makes it vacuous. -/
theorem theorem5Min_hyp_instance (Y ε ε2 : ℝ) (hY : 1 ≤ Y) (hε : ε ≤ 2 / 3) (hε2 : ε2 ≤ 5 / 12) :
    1 * Y ^ (7 / 12 + ε2) ≤ Y ∧ Y ≤ Y ∧ 1 * Y ^ (1 / 3 + ε) ≤ Y ^ (1 / 3 + ε) ∧
    Y ^ (1 / 3 + ε) ≤ 1 * Y ∧ Y ^ (1 / 3 + ε) ≤ 2 * (1 * Y ^ (1 / 3 + ε)) ∧
    Y ^ (1 / 3 + ε) ≤ 3 * Y / 2 ∧ 0 ≤ 2 * (3 * Y / 2) - Y - Y ∧
    1 * Y ≤ 2 * (3 * Y / 2) - Y - Y ∧ 2 * (3 * Y / 2) - Y - Y ≤ 1 * Y := by
  have hpos : 0 ≤ Y ^ (1 / 3 + ε) := Real.rpow_nonneg (by linarith) _
  have e1 : Y ^ (1 / 3 + ε) ≤ Y := by
    calc Y ^ (1 / 3 + ε) ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by linarith)
      _ = Y := Real.rpow_one Y
  have e2 : Y ^ (7 / 12 + ε2) ≤ Y := by
    calc Y ^ (7 / 12 + ε2) ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by linarith)
      _ = Y := Real.rpow_one Y
  refine ⟨by linarith, le_rfl, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- **HEADLINE. The F-0008 repair, CONDITIONAL ON `Theorem3` and `Theorem5Min`.** -/
theorem theorem2Zeroed_U1493 (h3 : Theorem3) (h5 : Theorem5Min) : Theorem2Zeroed :=
  theorem2Zeroed_U1462 h3 (theorem5_of_min h5)

/-- Theorem 2 in the lab's coprime reading, CONDITIONAL ON `Theorem3` and `Theorem5Min`. -/
theorem theorem2_U1493 (h3 : Theorem3) (h5 : Theorem5Min) : Theorem2 :=
  theorem2_U1462 h3 (theorem5_of_min h5)

end LeanLab.Halupczok2012
