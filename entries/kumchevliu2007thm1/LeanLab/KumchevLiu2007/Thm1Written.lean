module

public import LeanLab.KumchevLiu2007.Decomp129

/-!
Theorem 1 of Kumchev and Liu, arXiv 0801.0130, page 2, on the range that the
proof on page 16 writes: X to the 7/18 + ε at most H at most X to the 1 - ε,
the proviso stated with display 55. Lab run 20261118T0802Z-4078.
`thm1_written_of_eq33` proves the restated Prop `kumchev_liu_thm1_written`
from Proposition 1 display 33 on page 8, taken as the explicit named hypothesis
`Eq33Hyp`. For ε at most 5/18 the restated form gives the full printed range
H at most X, since every count is supported below X + Y and Y is at most
X to the 1 - ε, `thm1_full_of_written_small_eps`.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Task129W

open Real Complex LeanLab.KumchevLiu2007 LeanLab.KumchevLiu2007.Task129
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Theorem 1, page 2 display 9, restated to X to the 7/18 + ε at most H at most
X to the 1 - ε, the range for which page 16 proves display 55. -/
def kumchev_liu_thm1_written : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧
    ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧
      ∀ X H : ℝ, X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
          ‖(primeCount X (windowY X ε) n : ℂ) -
            main2 X (windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
          C * H / Real.log X ^ A

/-- Proposition 1 display 33 on page 8 with the page 15 weights, in the range of
page 16 after display 55, as a named hypothesis. -/
def Eq33Hyp : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      (∑ n ∈ (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ)),
        err53 X ε B n ^ 2) ≤ C * H * windowY X ε / Real.log X ^ A

/-- VACUITY INSTANCE. The written range is nonempty: ε = 1/18 and X = 4. -/
theorem written_range_nonempty :
    ∃ X H ε : ℝ, 0 < ε ∧ 2 ≤ X ∧ X ^ (7 / 18 + ε) ≤ H ∧ H ≤ X ^ (1 - ε) := by
  refine ⟨4, (4 : ℝ) ^ (1 - 1 / 18 : ℝ), 1 / 18, by norm_num, by norm_num, ?_, le_rfl⟩
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- The upper end X to the 1 - ε of the written range is at most X. -/
theorem written_upper_le (X ε : ℝ) (hX : 2 ≤ X) (hε : 0 < ε) : X ^ (1 - ε) ≤ X := by
  have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X)
    (by linarith : 1 - ε ≤ 1)
  simpa only [Real.rpow_one] using h

/-- Page 16 display 53 from display 33 by the finite Chebyshev inequality.
CONDITIONAL ON the explicit display 33 hypothesis. -/
theorem eq53_of_eq33 (h33 : Eq33Hyp) (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B0, hB0, hmean⟩ := h33 (3 * A) (by positivity)
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hmean⟩ := hmean B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hH hHX
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hYpos : 0 < windowY X ε := Real.rpow_pos_of_pos hXpos _
  let T := Real.sqrt (windowY X ε) * Real.log X ^ (-A)
  have hT : 0 < T := mul_pos (Real.sqrt_pos.mpr hYpos) (Real.rpow_pos_of_pos hLpos _)
  let s := (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ))
  have hsub : ((Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ =>
      X < (n : ℝ) ∧ InH2 n ∧ T < err53 X ε B n)) ⊆
      s.filter (fun n => T ≤ |err53 X ε B n|) := by
    intro n hn
    obtain ⟨hr, hXn, _, he⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hr, hXn⟩,
      he.le.trans (le_abs_self _)⟩
  have hcard : (cntIoc (fun n => InH2 n ∧ T < err53 X ε B n) X H : ℝ) ≤
      ((s.filter (fun n => T ≤ |err53 X ε B n|)).card : ℝ) := by
    have hcast := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
    simpa only [cntIoc, Finset.filter_congr_decidable] using hcast
  have hcheb := U1534.chebyshev_count s (err53 X ε B) hT
  have hcnt := (mul_le_mul_of_nonneg_right hcard (sq_nonneg T)).trans hcheb
  have hsum := hmean X H hX hH hHX
  have hTsq : T ^ 2 = windowY X ε * Real.log X ^ (-2 * A) := by
    dsimp [T]
    rw [mul_pow, Real.sq_sqrt hYpos.le]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    congr 1
    push_cast
    ring
  have heq : C * H / Real.log X ^ A * T ^ 2 =
      C * H * windowY X ε / Real.log X ^ (3 * A) := by
    rw [hTsq, div_eq_mul_inv, div_eq_mul_inv,
      ← Real.rpow_neg hLpos.le, ← Real.rpow_neg hLpos.le]
    calc C * H * Real.log X ^ (-A) * (windowY X ε * Real.log X ^ (-2 * A)) =
        C * H * windowY X ε * (Real.log X ^ (-A) * Real.log X ^ (-2 * A)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hLpos]
        congr 1
        congr 1
        ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hT)).mp
    (by simpa only [mul_comm (T ^ 2)] using (hcnt.trans hsum).trans_eq heq.symm)

/-- Theorem 1 on the written range, assembled from a display 53 input on that
range, the series lower bound and the residual estimate. -/
theorem thm1_written_of_eq53
    (h53 : ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A) :
    kumchev_liu_thm1_written := by
  intro A hA
  obtain ⟨Bc, hBc, hc⟩ := circle_input_of_estimates A hA (fun X ε => X ^ (1 - ε))
    (fun X ε hX hε => written_upper_le X ε hX hε)
    (h53 (A + 5) (by linarith)) (eq48_49_series_lower A hA)
  obtain ⟨Br, hBr, hr⟩ := residual_input A hA
  let B := max Bc Br
  refine ⟨B, lt_of_lt_of_le hBc (le_max_left _ _), ?_⟩
  intro δ ε hδ hε
  obtain ⟨Cc, Kc, Xc, hCc, hKc, hXc, hc⟩ := hc B (le_max_left _ _) ε hε
  obtain ⟨Cr, Kr, Xr, hCr, hKr, hXr, hr⟩ := hr B (le_max_right _ _) δ ε hδ hε
  obtain ⟨L0, hL0, hL⟩ := log_absorption δ hδ
  refine ⟨Cc + Cr, Kc + Kr, max (max Xc Xr) (Real.exp L0),
    by positivity, by positivity, le_trans hXc (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro X H hX hH hHX
  have hXc' : Xc ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXr' : Xr ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have he : Real.exp L0 ≤ X := le_trans (le_max_right _ _) hX
  have hX2 : 2 ≤ X := le_trans hXc hXc'
  have hHfull : H ≤ X := hHX.trans (written_upper_le X ε hX2 hε)
  have hlog : L0 ≤ Real.log X := by
    rw [← Real.log_exp L0]
    exact Real.log_le_log (Real.exp_pos _) he
  let Y := windowY X ε
  let P := Real.log X ^ B
  let badc := fun n => InH2 n ∧ Kc * ‖main2 X Y P n‖ *
    (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) <
    ‖(roughCount X Y P n : ℂ) - main2 X Y P n‖
  let badr := fun n => InH2 n ∧ Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) <
    |residualCount X Y P n|
  have sub : ∀ n, (InH2 n ∧ (Kc + Kr) * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) <
      ‖(primeCount X Y n : ℂ) - main2 X Y P n‖) → badc n ∨ badr n := by
    intro n ⟨hn, hbad⟩
    by_contra h
    have hgood := not_or.mp h
    have hcv : ‖(roughCount X Y P n : ℂ) - main2 X Y P n‖ ≤
        Kc * ‖main2 X Y P n‖ * (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) := by
      exact le_of_not_gt (fun hh => hgood.1 ⟨hn, hh⟩)
    have hrv : |residualCount X Y P n| ≤
        Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) := by
      exact le_of_not_gt (fun hh => hgood.2 ⟨hn, hh⟩)
    have hcv' : ‖(roughCount X Y P n : ℂ) - main2 X Y P n‖ ≤
        Kc * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) :=
      hcv.trans (mul_le_mul_of_nonneg_left (hL _ hlog) (by positivity))
    have hrv' : ‖(roughCount X Y P n : ℂ) - (primeCount X Y n : ℂ)‖ ≤
        Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) := by
      have heq : (roughCount X Y P n : ℂ) - (primeCount X Y n : ℂ) =
          (residualCount X Y P n : ℂ) := by
        simp only [residualCount, Complex.ofReal_sub, Complex.ofReal_natCast]
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
      exact hrv
    have hcombined := combine_errors hcv' hrv'
    have heq : Kc * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) +
        Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) =
        (Kc + Kr) * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) := by ring
    rw [heq] at hcombined
    exact (not_lt_of_ge hcombined) hbad
  have hcount := le_trans (U1534.cnt_mono sub X H) (U1534.cnt_or_le badc badr X H)
  have hcountR : (cntIoc (fun n => InH2 n ∧
      (Kc + Kr) * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) <
      ‖(primeCount X Y n : ℂ) - main2 X Y P n‖) X H : ℝ) ≤
      (cntIoc badc X H : ℝ) + (cntIoc badr X H : ℝ) := by exact_mod_cast hcount
  have hcb := hc X H hXc' hH hHX
  have hrb := hr X H hXr' hH hHfull
  calc _ ≤ (cntIoc badc X H : ℝ) + (cntIoc badr X H : ℝ) := hcountR
    _ ≤ Cc * H / Real.log X ^ A + Cr * H / Real.log X ^ A := add_le_add hcb hrb
    _ = (Cc + Cr) * H / Real.log X ^ A := by ring

/-- DQ2. Theorem 1 on the written range, CONDITIONAL ON display 33 as an explicit
named hypothesis. Its other inputs are the series lower bound and the residual
estimate, whose axiom lists are recorded in the build log. -/
theorem thm1_written_of_eq33 (h33 : Eq33Hyp) : kumchev_liu_thm1_written :=
  thm1_written_of_eq53 (eq53_of_eq33 h33)

/-- The bad set of display 9 is supported below X + Y: beyond it the windows of
page 2 displays 4 to 6 are empty, so both counts and the main term vanish. -/
theorem bad_support (X ε B K δ : ℝ) (hY : 0 ≤ windowY X ε) (n : ℕ)
    (hK : 0 ≤ K) (hL : 0 ≤ Real.log X ^ (-1 + δ))
    (hbad : InH2 n ∧ K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
      ‖(primeCount X (windowY X ε) n : ℂ) - main2 X (windowY X ε) (Real.log X ^ B) n‖) :
    (n : ℝ) < X + windowY X ε := by
  by_contra hc
  push Not at hc
  have hE := windowPairs_empty_above X _ hY n hc
  have h1 : primeCount X (windowY X ε) n = 0 := by simp [primeCount, hE]
  have h2 : main2 X (windowY X ε) (Real.log X ^ B) n = 0 := by
    simp [main2, integerMain, hE]
  rw [h1, h2] at hbad
  simp at hbad

/-- For ε at most 5/18 the written form gives Theorem 1 on the printed range
H at most X for that ε, since Y is at most X to the 1 - ε. -/
theorem thm1_full_of_written_small_eps (hW : kumchev_liu_thm1_written)
    (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧
    ∀ δ ε : ℝ, 0 < δ → 0 < ε → ε ≤ 5 / 18 → ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧
      ∀ X H : ℝ, X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
          ‖(primeCount X (windowY X ε) n : ℂ) -
            main2 X (windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B, hB, h⟩ := hW A hA
  refine ⟨B, hB, ?_⟩
  intro δ ε hδ hε hε5
  obtain ⟨C, K, X0, hC, hK, hX0, h⟩ := h δ ε hδ hε
  refine ⟨C, K, X0, hC, hK, hX0, ?_⟩
  intro X H hX hH hHX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hLA : 0 ≤ Real.log X ^ A := Real.rpow_nonneg (Real.log_nonneg hX1) _
  have hHnn : 0 ≤ H := le_trans (Real.rpow_nonneg hXpos.le _) hH
  by_cases hsmall : H ≤ X ^ (1 - ε)
  · exact h X H hX hH hsmall
  · push Not at hsmall
    have hYle : windowY X ε ≤ X ^ (1 - ε) := by
      unfold windowY; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have hYlow : X ^ (7 / 18 + ε) ≤ windowY X ε := by
      unfold windowY; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have hYnn : 0 ≤ windowY X ε := Real.rpow_nonneg hXpos.le _
    have hYH : windowY X ε ≤ H := hYle.trans hsmall.le
    have hLd : 0 ≤ Real.log X ^ (-1 + δ) := Real.rpow_nonneg (Real.log_nonneg hX1) _
    have hc := cnt_le_of_support _ X (windowY X ε) H hYH
      (fun n hn => bad_support X ε B K δ hYnn n hK.le hLd hn)
    calc _ ≤ (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
          ‖(primeCount X (windowY X ε) n : ℂ) -
            main2 X (windowY X ε) (Real.log X ^ B) n‖) X (windowY X ε) : ℝ) := by
            exact_mod_cast hc
      _ ≤ C * windowY X ε / Real.log X ^ A := h X _ hX hYlow hYle
      _ ≤ C * H / Real.log X ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hYH hC.le) hLA

end LeanLab.KumchevLiu2007.Task129W
