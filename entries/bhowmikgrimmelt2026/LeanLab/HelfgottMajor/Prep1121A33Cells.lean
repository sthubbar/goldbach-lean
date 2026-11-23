module

public import Mathlib

/-!
P0014 page 67, display A.33, first line, as a certified interval computation.

The quantity `(c0 - 1/√2)/(√2 c1 ρ)` of A.33 equals `a33G u` with `u = 1/υ(ρ)` in `(0,1)`;
that change of variables is in `Prep1121A33Reduce`. In the variable `u` the function is
continuous on the closed interval `[0,1]`, so the paper's two hand bounds, for `ρ ≥ 25` and
for `ρ ≤ 0.1`, become the two end segments `u ≤ 3/10` and `u ≥ 99/100` here, and the
bisection on `[0.1, 25]` becomes a finite list of first order cells plus one second order
window `[1/2, 4/5]` around the maximum at `u ≈ 0.64972`, `ρ ≈ 3.6015`, where the margin to
`0.0763896` is only about `2.9e-8` and is handled in `Prep1121A33Window`.

A cell `(u1, u2, A, Bb, R1, R2)` carries rational witnesses
`A ≤ √(1+u1)`, `√(1-u1) ≤ Bb`, `√(4-2u1²) ≤ R1`, `R2 ≤ √(4-2u2²)`; each square root is
monotone, which gives the enclosure. Checked by `decide +kernel` on rationals.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Prep1121A33Cells

open Real

/-- P0014 page 67, display A.33, first line, rewritten in `u = 1/υ(ρ)` with
`a = √(1+u)`, `b = √(1-u)`, `R = √(4-2u²)`:
`(c0 - 1/√2)/(√2 c1 ρ) = u/(4a) · (R - 2 + u + 2b(1-u)) / (R - b u)`. -/
noncomputable def a33G (u : ℝ) : ℝ :=
  u / (4 * √(1 + u)) *
    ((√(4 - 2 * u ^ 2) - 2 + u + 2 * √(1 - u) * (1 - u)) / (√(4 - 2 * u ^ 2) - √(1 - u) * u))

/-- The printed constant of P0014 page 67, display A.33, first line. -/
def a33B : ℚ := 763896 / 10000000

/-- A first order cell for P0014 page 67, display A.33: the rational check. -/
def cellOK (c : ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) : Bool :=
  match c with
  | (u1, u2, A, Bb, R1, R2) =>
    decide (0 ≤ u1) && decide (u1 < u2) && decide (u2 ≤ 1) && decide (0 < A) &&
    decide (A * A ≤ 1 + u1) && decide (0 ≤ Bb) && decide (1 - u1 ≤ Bb * Bb) &&
    decide (0 ≤ R1) && decide (4 - 2 * u1 * u1 ≤ R1 * R1) && decide (0 ≤ R2) &&
    decide (R2 * R2 ≤ 4 - 2 * u2 * u2) && decide (0 < R2 - Bb * u2) &&
    decide (0 ≤ R1 - 2 + u2 + 2 * Bb * (1 - u1)) &&
    decide (u2 * (R1 - 2 + u2 + 2 * Bb * (1 - u1)) ≤ 4 * A * (R2 - Bb * u2) * a33B)

/-- A chain of cells covering `(lo, hi]` for P0014 page 67, display A.33. -/
def chainOK : ℚ → List (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) → ℚ → Bool
  | lo, [], hi => decide (hi ≤ lo)
  | lo, c :: cs, hi => decide (c.1 ≤ lo) && cellOK c && chainOK c.2.1 cs hi

/-- P0014 page 67, display A.33, first line, one bisection cell.
Soundness of the first order cell check: monotone enclosure of the three square roots. -/
theorem cellOK_sound (c : ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) (h : cellOK c = true) (u : ℝ)
    (h1 : (c.1 : ℝ) ≤ u) (h2 : u ≤ (c.2.1 : ℝ)) : a33G u ≤ (a33B : ℝ) := by
  obtain ⟨u1, u2, A, Bb, R1, R2⟩ := c
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu1, hu12⟩, hu2⟩, hA0⟩, hA⟩, hB0⟩, hB⟩, hR10⟩, hR1⟩, hR20⟩, hR2⟩, hQ⟩,
    hP⟩, hF⟩ := h
  simp only at h1 h2
  have qu1 : (0:ℝ) ≤ u1 := by exact_mod_cast hu1
  have qu2 : (u2:ℝ) ≤ 1 := by exact_mod_cast hu2
  have qA0 : (0:ℝ) < A := by exact_mod_cast hA0
  have qA : (A:ℝ) * A ≤ 1 + u1 := by exact_mod_cast hA
  have qB0 : (0:ℝ) ≤ Bb := by exact_mod_cast hB0
  have qB : 1 - (u1:ℝ) ≤ Bb * Bb := by exact_mod_cast hB
  have qR10 : (0:ℝ) ≤ R1 := by exact_mod_cast hR10
  have qR1 : 4 - 2 * (u1:ℝ) * u1 ≤ R1 * R1 := by exact_mod_cast hR1
  have qR20 : (0:ℝ) ≤ R2 := by exact_mod_cast hR20
  have qR2 : (R2:ℝ) * R2 ≤ 4 - 2 * u2 * u2 := by exact_mod_cast hR2
  have qQ : (0:ℝ) < R2 - Bb * u2 := by exact_mod_cast hQ
  have qP : (0:ℝ) ≤ R1 - 2 + u2 + 2 * Bb * (1 - u1) := by exact_mod_cast hP
  have qF : (u2:ℝ) * (R1 - 2 + u2 + 2 * Bb * (1 - u1)) ≤ 4 * A * (R2 - Bb * u2) * a33B := by
    exact_mod_cast hF
  have hu0 : 0 ≤ u := le_trans qu1 h1
  have hu1' : u ≤ 1 := le_trans h2 qu2
  set a := √(1 + u) with ha
  set b := √(1 - u) with hb
  set R := √(4 - 2 * u ^ 2) with hR
  have ha_ge : (A:ℝ) ≤ a := Real.le_sqrt_of_sq_le (by nlinarith)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hb_le : b ≤ Bb := by
    rw [hb, Real.sqrt_le_left]
    · nlinarith
    · exact qB0
  have hR_le : R ≤ R1 := by
    rw [hR, Real.sqrt_le_left]
    · nlinarith
    · exact qR10
  have hR_ge : (R2:ℝ) ≤ R := Real.le_sqrt_of_sq_le (by nlinarith)
  have hPle : R - 2 + u + 2 * b * (1 - u) ≤ R1 - 2 + u2 + 2 * Bb * (1 - u1) := by
    have : b * (1 - u) ≤ Bb * (1 - u1) :=
      mul_le_mul hb_le (by linarith) (by linarith) qB0
    linarith
  have hQge : (R2:ℝ) - Bb * u2 ≤ R - b * u := by
    have : b * u ≤ Bb * u2 := mul_le_mul hb_le h2 hu0 qB0
    linarith
  have hQpos : 0 < R - b * u := lt_of_lt_of_le qQ hQge
  have hpre0 : 0 ≤ u / (4 * a) := by positivity
  have hpre : u / (4 * a) ≤ u2 / (4 * A) := by
    apply div_le_div₀ (by linarith) h2 (by positivity) (by linarith)
  unfold a33G
  rw [← ha, ← hb, ← hR]
  by_cases hPs : R - 2 + u + 2 * b * (1 - u) ≤ 0
  · have : (R - 2 + u + 2 * b * (1 - u)) / (R - b * u) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hPs hQpos.le
    have hB0 : (0:ℝ) ≤ a33B := by unfold a33B; norm_num
    nlinarith
  rw [not_le] at hPs
  have hfrac : (R - 2 + u + 2 * b * (1 - u)) / (R - b * u) ≤
      (R1 - 2 + u2 + 2 * Bb * (1 - u1)) / (R2 - Bb * u2) :=
    div_le_div₀ qP hPle qQ hQge
  calc u / (4 * a) * ((R - 2 + u + 2 * b * (1 - u)) / (R - b * u))
      ≤ u2 / (4 * A) * ((R1 - 2 + u2 + 2 * Bb * (1 - u1)) / (R2 - Bb * u2)) :=
        mul_le_mul hpre hfrac (div_nonneg hPs.le hQpos.le) (div_nonneg (by linarith) (by linarith))
    _ ≤ a33B := by
      rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
      linarith

/-- P0014 page 67, display A.33, first line: a checked chain covers its half open range. -/
theorem chainOK_sound : ∀ (cs : List (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)) (lo hi : ℚ),
    chainOK lo cs hi = true → ∀ u : ℝ, (lo : ℝ) < u → u ≤ (hi : ℝ) → a33G u ≤ (a33B : ℝ)
  | [], lo, hi, h, u, hl, hh => by
    simp only [chainOK, decide_eq_true_eq] at h
    have : (hi : ℝ) ≤ lo := by exact_mod_cast h
    linarith
  | c :: cs, lo, hi, h, u, hl, hh => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    by_cases hu : u ≤ (c.2.1 : ℝ)
    · exact cellOK_sound c h2 u (le_trans (by exact_mod_cast h1) hl.le) hu
    · exact chainOK_sound cs c.2.1 hi h3 u (lt_of_not_ge hu) hh

/-- Cells for the large `ρ` tail, `u ∈ (0, 3/10]`, about `ρ ≥ 21`. -/
def cellsTail : List (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) :=
  [((0 : ℚ), (3/20 : ℚ), (1 : ℚ), (10000001/10000000 : ℚ), (20000001/10000000 : ℚ), (19887181/10000000 : ℚ)),
  ((3/20 : ℚ), (9/40 : ℚ), (2144761/2000000 : ℚ), (1843909/2000000 : ℚ), (9943591/5000000 : ℚ), (4936313/2500000 : ℚ)),
  ((9/40 : ℚ), (3/10 : ℚ), (11067971/10000000 : ℚ), (8803409/10000000 : ℚ), (19745253/10000000 : ℚ), (977241/500000 : ℚ))]

/-- Cells for `u ∈ (3/10, 1/2]`, about `ρ` in `[7.7, 21]`. -/
def cellsLeft : List (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) :=
  [((3/10 : ℚ), (7/20 : ℚ), (5700877/5000000 : ℚ), (8366601/10000000 : ℚ), (19544821/10000000 : ℚ), (9688911/5000000 : ℚ)),
  ((7/20 : ℚ), (2/5 : ℚ), (232379/200000 : ℚ), (4031129/5000000 : ℚ), (19377823/10000000 : ℚ), (9591663/5000000 : ℚ)),
  ((2/5 : ℚ), (17/40 : ℚ), (11832159/10000000 : ℚ), (7745967/10000000 : ℚ), (19183327/10000000 : ℚ), (19075507/10000000 : ℚ)),
  ((17/40 : ℚ), (9/20 : ℚ), (1492167/1250000 : ℚ), (1895719/2500000 : ℚ), (4768877/2500000 : ℚ), (3792097/2000000 : ℚ)),
  ((9/20 : ℚ), (37/80 : ℚ), (6020797/5000000 : ℚ), (7416199/10000000 : ℚ), (9480243/5000000 : ℚ), (18900231/10000000 : ℚ)),
  ((37/80 : ℚ), (19/40 : ℚ), (6046693/5000000 : ℚ), (91643/125000 : ℚ), (2362529/1250000 : ℚ), (9419063/5000000 : ℚ)),
  ((19/40 : ℚ), (39/80 : ℚ), (12144957/10000000 : ℚ), (7245689/10000000 : ℚ), (18838127/10000000 : ℚ), (18774151/10000000 : ℚ)),
  ((39/80 : ℚ), (1/2 : ℚ), (1219631/1000000 : ℚ), (7158911/10000000 : ℚ), (2346769/1250000 : ℚ), (9354143/5000000 : ℚ))]

/-- Cells for `u ∈ (4/5, 99/100]`, about `ρ` in `[0.29, 1.9]`. -/
def cellsRight : List (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) :=
  [((4/5 : ℚ), (8119/10000 : ℚ), (13416407/10000000 : ℚ), (559017/1250000 : ℚ), (16492423/10000000 : ℚ), (16375703/10000000 : ℚ)),
  ((8119/10000 : ℚ), (4119/5000 : ℚ), (13460683/10000000 : ℚ), (86741/200000 : ℚ), (2046963/1250000 : ℚ), (3251281/2000000 : ℚ)),
  ((4119/5000 : ℚ), (2089/2500 : ℚ), (13504813/10000000 : ℚ), (4197619/10000000 : ℚ), (8128203/5000000 : ℚ), (3227101/2000000 : ℚ)),
  ((2089/2500 : ℚ), (339/400 : ℚ), (13548431/10000000 : ℚ), (4054627/10000000 : ℚ), (8067753/5000000 : ℚ), (8005447/5000000 : ℚ)),
  ((339/400 : ℚ), (4297/5000 : ℚ), (13592277/10000000 : ℚ), (31241/80000 : ℚ), (3202179/2000000 : ℚ), (15883523/10000000 : ℚ)),
  ((4297/5000 : ℚ), (1089/1250 : ℚ), (13635981/10000000 : ℚ), (3749667/10000000 : ℚ), (3970881/2500000 : ℚ), (15754431/10000000 : ℚ)),
  ((1089/1250 : ℚ), (179/200 : ℚ), (13679181/10000000 : ℚ), (448609/1250000 : ℚ), (246163/156250 : ℚ), (3097063/2000000 : ℚ)),
  ((179/200 : ℚ), (2297/2500 : ℚ), (13765899/10000000 : ℚ), (3240371/10000000 : ℚ), (3871329/2500000 : ℚ), (1520399/1000000 : ℚ)),
  ((2297/2500 : ℚ), (377/400 : ℚ), (554083/400000 : ℚ), (1424781/5000000 : ℚ), (15203991/10000000 : ℚ), (14911027/10000000 : ℚ)),
  ((377/400 : ℚ), (99/100 : ℚ), (13937359/10000000 : ℚ), (599479/2500000 : ℚ), (3727757/2500000 : ℚ), (3570539/2500000 : ℚ))]

/-- Cells for the small `ρ` tail, `u ∈ (99/100, 1]`, about `ρ ≤ 0.29`. -/
def cellsTailSmall : List (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) :=
  [((99/100 : ℚ), (1 : ℚ), (2821347/2000000 : ℚ), (1000001/10000000 : ℚ), (14282157/10000000 : ℚ), (2828427/2000000 : ℚ))]

/-- P0014 page 67, the hand bound for large `ρ` before A.33, here as a finite check. -/
theorem chain_tail : chainOK 0 cellsTail (3 / 10) = true := by decide +kernel

/-- P0014 page 67, display A.33, bisection range, cells for `u ∈ (3/10, 1/2]`. -/
theorem chain_left : chainOK (3 / 10) cellsLeft (1 / 2) = true := by decide +kernel

/-- P0014 page 67, display A.33, bisection range, cells for `u ∈ (4/5, 99/100]`. -/
theorem chain_right : chainOK (4 / 5) cellsRight (99 / 100) = true := by decide +kernel

/-- P0014 page 67, the hand bound for `ρ ≤ 0.1` before A.33, here as a finite check. -/
theorem chain_tail_small : chainOK (99 / 100) cellsTailSmall 1 = true := by decide +kernel

/-- P0014 page 67, display A.33, first line, outside the window `[1/2, 4/5]`. -/
theorem a33G_le_outside (u : ℝ) (h0 : 0 < u) (h1 : u ≤ 1) (hw : u < 1 / 2 ∨ 4 / 5 < u) :
    a33G u ≤ (a33B : ℝ) := by
  rcases hw with hw | hw
  · by_cases h3 : u ≤ 3 / 10
    · exact chainOK_sound _ _ _ chain_tail u (by simpa using h0) (by norm_num; linarith)
    · exact chainOK_sound _ _ _ chain_left u (by norm_num; linarith) (by norm_num; linarith)
  · by_cases h3 : u ≤ 99 / 100
    · exact chainOK_sound _ _ _ chain_right u (by norm_num; linarith) (by norm_num; linarith)
    · exact chainOK_sound _ _ _ chain_tail_small u (by norm_num; linarith) (by norm_num; linarith)

end LeanLab.HelfgottMajor.Prep1121A33Cells
