module

public import Mathlib
public import LeanLab.Grimmelt2019.Statements
public import LeanLab.ExceptionalSet.Statements

/-!
P0074 L. Grimmelt, "Goldbach Numbers in Short Intervals: A Nonnegative Model Approach",
arXiv 1910.05187 v2. Unit U-6753, run 20261020T2317Z-cloud53.

Elementary bookkeeping of the proof of Theorem 1.1, Section 5 of the paper.

* The exponent: Lemma 5.1 takes `Y = X^{21/40+ε}` and `H = Y^{1/9+2ε}`, so
  `H = X^{(21/40+ε)(1/9+2ε)}`, and the proof says this is `X^{7/120+ε'}`. We prove the
  identity, that every `ε' > 0` is reached by some `ε > 0`, the parameter side conditions of
  Lemma 3.3 and of the rough support claim in the proof of Lemma 5.1, and the factor swap
  `11/20 → 21/40` that the introduction names as the whole saving over Harman.
* The exception count of Proposition 2.1 with the norms, `θ` and `κ` chosen in Section 5.
* The covering step. The proof of Theorem 1.1 treats one interval length,
  `H = X^{7/120+ε'}`, while Theorem 1.1 claims every `H > X^{7/120+ε}`. We prove that the
  exact length statement plus the classical full interval bound `|E(X)| ≪_A X (log X)^{-A}`
  gives the statement for all `H`. The full interval bound is a cited input here,
  `LeanLab.ExceptionalSet.LogPowerSaving`; the lab PROVED it unconditionally as
  `LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving`.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here proves Theorem 1.1 itself; the analytic core stays cited.
-/

@[expose] public section

namespace LeanLab.Grimmelt2019
open Real

attribute [local instance] Classical.propDecidable

/-! ### Exponent arithmetic of Section 5 and of the introduction -/

/-- `21/40 · 1/9 = 7/120`: the main exponent of Theorem 1.1 is the BHP exponent times `1/9`. -/
theorem exponent_thm1_1 : (21 / 40 : ℝ) * (1 / 9) = 7 / 120 := by norm_num

/-- `11/20 · 1/9 = 11/180`: Harman's exponent, from the `11/20` of equation (7). -/
theorem exponent_harman : (11 / 20 : ℝ) * (1 / 9) = 11 / 180 := by norm_num

/-- The introduction, p. 4: the saving over Harman is exactly the swap of `11/20` by `21/40`
in the factor before `1/9`. The gain is `1/360`. -/
theorem saving_eq_factor_swap :
    (11 / 180 : ℝ) - 7 / 120 = (11 / 20 - 21 / 40) * (1 / 9) ∧
      (11 / 180 : ℝ) - 7 / 120 = 1 / 360 := by
  constructor <;> norm_num

/-- Lemma 5.1 parameters: `(21/40+ε)(1/9+2ε) = 7/120 + (209/180) ε + 2 ε²`. -/
theorem lemma51_exponent (ε : ℝ) :
    (21 / 40 + ε) * (1 / 9 + 2 * ε) = 7 / 120 + 209 / 180 * ε + 2 * ε ^ 2 := by ring

/-- `H = Y^{1/9+2ε}` with `Y = X^{21/40+ε}` is `X^{7/120 + (209/180) ε + 2 ε²}`. -/
theorem lemma51_H_eq {X : ℝ} (hX : 0 ≤ X) (ε : ℝ) :
    (X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε) = X ^ (7 / 120 + 209 / 180 * ε + 2 * ε ^ 2) := by
  rw [← Real.rpow_mul hX, lemma51_exponent]

/-- For `ε > 0` the Lemma 5.1 exponent is strictly above `7/120`. -/
theorem lemma51_exponent_gt {ε : ℝ} (hε : 0 < ε) :
    7 / 120 < (21 / 40 + ε) * (1 / 9 + 2 * ε) := by
  rw [lemma51_exponent]; nlinarith

/-- Every exponent `7/120 + ε'` with `ε' > 0` is the Lemma 5.1 exponent of some `ε > 0`,
explicitly `ε = (√(b² + 8ε') - b)/4` with `b = 209/180`. So the parameter family of
Lemma 5.1 reaches every length `X^{7/120+ε'}` in Theorem 1.1. -/
theorem exists_lemma51_eps {ε' : ℝ} (hε' : 0 < ε') :
    ∃ ε : ℝ, 0 < ε ∧ (21 / 40 + ε) * (1 / 9 + 2 * ε) = 7 / 120 + ε' := by
  have hb : (0 : ℝ) ≤ 209 / 180 := by norm_num
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (209 / 180) ^ 2 + 8 * ε' by positivity)
  have hlt : (209 / 180 : ℝ) < Real.sqrt ((209 / 180) ^ 2 + 8 * ε') :=
    (Real.lt_sqrt hb).mpr (by linarith)
  refine ⟨(Real.sqrt ((209 / 180) ^ 2 + 8 * ε') - 209 / 180) / 4, by linarith, ?_⟩
  rw [lemma51_exponent]
  linear_combination (1 / 8 : ℝ) * hs

/-- Proof of Lemma 5.1: `ν` lives on `Y^{1/9}`-rough numbers, and Lemma 3.3 needs
`H^{1/2}`-rough support. With `H = Y^{1/9+2ε}` this needs `H^{1/2} = Y^{1/18+ε} < Y^{1/9}`,
true exactly for `ε < 1/18`; the paper writes `H^{1/2} = Y^{1/18}`, dropping the `ε`. -/
theorem rough_support {Y ε : ℝ} (hY : 1 < Y) (hε : ε < 1 / 18) :
    (Y ^ (1 / 9 + 2 * ε)) ^ (1 / 2 : ℝ) < Y ^ (1 / 9 : ℝ) := by
  rw [← Real.rpow_mul (by linarith)]
  exact Real.rpow_lt_rpow_of_exponent_lt hY (by linarith)

/-- Lemma 3.3 and Lemma 4.2 need `Y^δ < H < Y^{1-δ}` for some `δ > 0`; `δ = 1/9` works for
`H = Y^{1/9+2ε}` and `0 < ε < 7/18`. -/
theorem lemma33_range {Y ε : ℝ} (hY : 1 < Y) (hε0 : 0 < ε) (hε : ε < 7 / 18) :
    Y ^ (1 / 9 : ℝ) < Y ^ (1 / 9 + 2 * ε) ∧ Y ^ (1 / 9 + 2 * ε) < Y ^ (1 - 1 / 9 : ℝ) :=
  ⟨Real.rpow_lt_rpow_of_exponent_lt hY (by linarith),
    Real.rpow_lt_rpow_of_exponent_lt hY (by linarith)⟩

/-- Lemma 4.2 uses `D = H^{1/10}` and needs `q H^{1/10} ≪ q H^{1/2} / (log Y)^{A-1}`; the
step is `H^{1/10} · L ≤ H^{1/2}` once `L ≤ H^{2/5}`. -/
theorem lemma42_level {H L : ℝ} (hH : 0 ≤ H) (hL : L ≤ H ^ (2 / 5 : ℝ)) :
    H ^ (1 / 10 : ℝ) * L ≤ H ^ (1 / 2 : ℝ) := by
  calc H ^ (1 / 10 : ℝ) * L ≤ H ^ (1 / 10 : ℝ) * H ^ (2 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hH _)
    _ = H ^ (1 / 2 : ℝ) := by
        rcases hH.lt_or_eq with hpos | hzero
        · rw [← Real.rpow_add hpos]; norm_num
        · subst hzero; simp [Real.zero_rpow]

/-! ### The exception count of Proposition 2.1 with the Section 5 choices -/

/-- Proposition 2.1 bounds the exceptions by `H (‖ω‖² + ‖a‖²)(‖ν‖² + ‖T⁺‖² + ‖T‖²) √θ / κ²`.
With every squared norm at most `K Y L^B`, `θ = L^{-(A+1)}` and `κ = Y / L`, where
`L = log Y ≥ 1`, this is at most `6 K² H L^{2B + 2 - (A+1)/2}`. Note that the bound needs
`‖a‖² ≪ Y L^B` too, so `a` must be `Λ'` cut to a window of length `≪ Y`. -/
theorem prop21_exceptions_bookkeeping {Y L H K B A nω na nν nT nTp : ℝ}
    (hY : 0 < Y) (hL : 1 ≤ L) (hH : 0 ≤ H)
    (h0ω : 0 ≤ nω) (h0ν : 0 ≤ nν) (h0T : 0 ≤ nT) (h0Tp : 0 ≤ nTp)
    (hω : nω ≤ K * Y * L ^ B) (ha : na ≤ K * Y * L ^ B) (hν : nν ≤ K * Y * L ^ B)
    (hT : nT ≤ K * Y * L ^ B) (hTp : nTp ≤ K * Y * L ^ B) :
    H * (nω + na) * (nν + nTp + nT) * Real.sqrt (L ^ (-(A + 1))) / (Y / L) ^ 2
      ≤ 6 * K ^ 2 * H * L ^ (2 * B + 2 - (A + 1) / 2) := by
  have hLpos : 0 < L := by linarith
  have hsq : Real.sqrt (L ^ (-(A + 1))) = L ^ (-(A + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hLpos.le]; ring_nf
  have hpow : L ^ (2 * B + 2 - (A + 1) / 2) = (L ^ B) ^ 2 * L ^ 2 * L ^ (-(A + 1) / 2) := by
    rw [show 2 * B + 2 - (A + 1) / 2 = (B + B) + 2 + (-(A + 1) / 2) by ring,
      Real.rpow_add hLpos, Real.rpow_add hLpos, Real.rpow_add hLpos, Real.rpow_two]
    ring
  rw [hsq, hpow]
  set M := K * Y * L ^ B with hM
  set s := L ^ (-(A + 1) / 2) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg hLpos.le _
  have hP : (nω + na) * (nν + nTp + nT) ≤ (2 * M) * (3 * M) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
  have hYL : 0 < (Y / L) ^ 2 := by positivity
  rw [div_le_iff₀ hYL]
  calc H * (nω + na) * (nν + nTp + nT) * s = H * ((nω + na) * (nν + nTp + nT)) * s := by ring
    _ ≤ H * ((2 * M) * (3 * M)) * s := by gcongr
    _ = 6 * K ^ 2 * H * ((L ^ B) ^ 2 * L ^ 2 * s) * (Y / L) ^ 2 := by
        rw [hM]; field_simp; ring
    _ = _ := by ring

/-- Choosing `A ≥ 4B + 2A' + 3` turns the exception count into `≤ 6 K² H L^{-A'}`. -/
theorem prop21_exceptions_logSaving {L H K B A A' : ℝ} (hL : 1 ≤ L) (hH : 0 ≤ H)
    (hA : 4 * B + 2 * A' + 3 ≤ A) :
    6 * K ^ 2 * H * L ^ (2 * B + 2 - (A + 1) / 2) ≤ 6 * K ^ 2 * H * L ^ (-A') := by
  have : L ^ (2 * B + 2 - (A + 1) / 2) ≤ L ^ (-A') :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h0 : 0 ≤ 6 * K ^ 2 * H := by positivity
  exact mul_le_mul_of_nonneg_left this h0

/-- `log Y = (21/40 + ε) log X ≥ (1/2) log X` for `Y = X^{21/40+ε}`, so a saving in powers of
`log Y` is one in powers of `log X`. -/
theorem logY_ge_half_logX {X ε : ℝ} (hX : 1 ≤ X) (hε : 0 ≤ ε) :
    Real.log X / 2 ≤ Real.log (X ^ (21 / 40 + ε)) := by
  rw [Real.log_rpow (by linarith)]
  have := Real.log_nonneg hX
  nlinarith

/-! ### The covering step: from one length to every length -/

/-- The output of the proof of Theorem 1.1 in Section 5: the estimate (1) for the single
length `H = X^{c+ε}`, for every `ε > 0`, `A > 0`. -/
def ExactLengthLogSaving (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
    (EXH X (X ^ (c + ε)) : ℝ) ≤ C * X ^ (c + ε) / Real.log X ^ A

/-- The full count `EFull` of `Statements.lean` is the lab's `LeanLab.ExceptionalSet.E`. -/
theorem EFull_eq_E (X : ℕ) : EFull X = LeanLab.ExceptionalSet.E X := by
  unfold EFull LeanLab.ExceptionalSet.E
  congr 1

/-- Covering `[X - H, X]` by `N` pieces `[X - (j+1)h, X - jh]` once `H < N h`. -/
theorem EXH_le_sum_cover (X H h : ℝ) (hh : 0 < h) (N : ℕ) (hN : H < N * h) :
    EXH X H ≤ ∑ j ∈ Finset.range N, EXH (X - j * h) h := by
  unfold EXH
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨h4, hnX⟩, hlow, hev, hng⟩ := hn
  have hnX' : (n : ℝ) ≤ X := (Nat.le_floor_iff' (by omega)).mp hnX
  set j := ⌊(X - n) / h⌋₊ with hj
  have hd0 : 0 ≤ (X - n) / h := div_nonneg (by linarith) hh.le
  have hj1 : (j : ℝ) * h ≤ X - n := by
    have := Nat.floor_le hd0
    rwa [le_div_iff₀ hh] at this
  have hj2 : X - n < ((j : ℝ) + 1) * h := by
    have := Nat.lt_floor_add_one ((X - n) / h)
    rwa [div_lt_iff₀ hh] at this
  have hjN : j < N := by
    have : (j : ℝ) * h < N * h := by linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hh.le
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨j, hjN, ⟨h4, Nat.le_floor (by linarith)⟩, by linarith, hev, hng⟩

/-- `W / (log Z)^A ≤ 2^A W / (log X)^A` once `X ≥ 16` and `Z ≥ X/4`. -/
theorem div_logpow_le {X Z W A : ℝ} (hX : 16 ≤ X) (hZ : X / 4 ≤ Z) (hW : 0 ≤ W)
    (hA : 0 ≤ A) : W / Real.log Z ^ A ≤ (2 : ℝ) ^ A * W / Real.log X ^ A := by
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have h4 : Real.log 16 = 2 * Real.log 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlz : Real.log X - Real.log 4 ≤ Real.log Z := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) hZ
  have hl16 : Real.log 16 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hkey : Real.log X ≤ 2 * Real.log Z := by linarith
  have hlogZ : 0 < Real.log Z := by linarith
  have hpow : Real.log X ^ A ≤ (2 : ℝ) ^ A * Real.log Z ^ A := by
    rw [← Real.mul_rpow (by norm_num) hlogZ.le]
    exact Real.rpow_le_rpow hlogX.le hkey hA
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlogZ A) (Real.rpow_pos_of_pos hlogX A)]
  calc W * Real.log X ^ A ≤ W * ((2 : ℝ) ^ A * Real.log Z ^ A) :=
        mul_le_mul_of_nonneg_left hpow hW
    _ = (2 : ℝ) ^ A * W * Real.log Z ^ A := by ring

/-- Long intervals, `H ≥ X/2`, from the full interval bound. -/
theorem EXH_le_of_full {C1 A X H : ℝ} (hA : 0 ≤ A)
    (hfull : ∀ X : ℕ, 2 ≤ X → (LeanLab.ExceptionalSet.E X : ℝ) ≤ C1 * X / Real.log X ^ A)
    (hX : 16 ≤ X) (hH : X / 2 ≤ H) :
    (EXH X H : ℝ) ≤ (max C1 0 * 2 ^ (A + 1)) * H / Real.log X ^ A := by
  set Z : ℝ := (⌊X⌋₊ : ℝ) with hZ
  have hZX : Z ≤ X := Nat.floor_le (by linarith)
  have hZlow : X - 1 < Z := by
    have := Nat.lt_floor_add_one X; rw [hZ]; linarith
  have hfl2 : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hlogZ : 0 < Real.log Z := Real.log_pos (by rw [hZ]; linarith)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hZ0 : 0 ≤ Z := by positivity
  have h1 : (EXH X H : ℝ) ≤ C1 * Z / Real.log Z ^ A := by
    calc (EXH X H : ℝ) ≤ (EFull ⌊X⌋₊ : ℝ) := by exact_mod_cast EXH_le_EFull X H
      _ = LeanLab.ExceptionalSet.E ⌊X⌋₊ := by rw [EFull_eq_E]
      _ ≤ C1 * Z / Real.log Z ^ A := hfull _ hfl2
  have h2 : C1 * Z / Real.log Z ^ A ≤ max C1 0 * (Z / Real.log Z ^ A) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (div_nonneg hZ0 (Real.rpow_nonneg hlogZ.le _))
  have h3 : Z / Real.log Z ^ A ≤ (2 : ℝ) ^ A * Z / Real.log X ^ A :=
    div_logpow_le hX (by linarith) hZ0 hA
  have hM : 0 ≤ max C1 0 := le_max_right _ _
  have hLX : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogX A
  have h2A : (2 : ℝ) ^ (A + 1) = 2 ^ A * 2 := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
  calc (EXH X H : ℝ) ≤ max C1 0 * ((2 : ℝ) ^ A * Z / Real.log X ^ A) := by
        refine h1.trans (h2.trans ?_)
        exact mul_le_mul_of_nonneg_left h3 hM
    _ ≤ max C1 0 * ((2 : ℝ) ^ A * (2 * H) / Real.log X ^ A) := by
        gcongr; linarith
    _ = (max C1 0 * 2 ^ (A + 1)) * H / Real.log X ^ A := by rw [h2A]; ring

/-- CONDITIONAL ON `LeanLab.ExceptionalSet.LogPowerSaving`, the classical full interval bound,
which the lab has PROVED as `LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving`.
The estimate (1) for the single length `X^{c+ε}`, for every `ε`, gives (1) for every
`H > X^{c+ε}`: short pieces of length `(X/4)^{c+ε/2}` cover `[X - H, X]` when `H < X/2`, and
the full interval bound handles `H ≥ X/2`. This is the step from the one length treated in
the proof of Theorem 1.1 to the range claimed in its statement. -/
theorem logSaving_of_exactLength {c : ℝ} (hc : 0 ≤ c) (hcore : ExactLengthLogSaving c)
    (hfull : LeanLab.ExceptionalSet.LogPowerSaving) : ShortIntervalLogSaving c := by
  intro ε hε A hA
  obtain ⟨C1, hC1⟩ := hfull A hA
  obtain ⟨C0, X0, hC0⟩ := hcore (ε / 2) (by linarith) A hA
  set e := c + ε / 2 with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  set M0 := max C0 0 with hM0def
  have hM0 : 0 ≤ M0 := le_max_right _ _
  refine ⟨max C1 0 * 2 ^ (A + 1) + M0 * 2 ^ A * (4 ^ e + 2),
    max (max 16 (4 * X0)) ((2 : ℝ) ^ (2 / ε)), fun X H hX hH => ?_⟩
  have hX16 : 16 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX0 : 4 * X0 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX2 : (2 : ℝ) ^ (2 / ε) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogX A
  have hHpos : 0 < H := lt_of_le_of_lt (Real.rpow_nonneg hXpos.le _) hH
  have hC1' : 0 ≤ max C1 0 := le_max_right _ _
  have hfirst : 0 ≤ max C1 0 * 2 ^ (A + 1) * H / Real.log X ^ A := by positivity
  have hsecond : 0 ≤ M0 * 2 ^ A * (4 ^ e + 2) * H / Real.log X ^ A := by positivity
  rcases le_or_gt (X / 2) H with hbig | hsmall
  · calc (EXH X H : ℝ) ≤ (max C1 0 * 2 ^ (A + 1)) * H / Real.log X ^ A :=
          EXH_le_of_full hA.le hC1 hX16 hbig
      _ ≤ _ := by rw [add_mul, add_div]; linarith
  · have hXe2 : 2 ≤ X ^ (ε / 2) := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (2 / ε)) ^ (ε / 2) := by
            rw [← Real.rpow_mul (by norm_num)]
            rw [show 2 / ε * (ε / 2) = 1 by field_simp, Real.rpow_one]
        _ ≤ X ^ (ε / 2) := Real.rpow_le_rpow (by positivity) hX2 (by positivity)
    have hsplit : X ^ (c + ε) = X ^ e * X ^ (ε / 2) := by
      rw [← Real.rpow_add hXpos, he]; ring_nf
    have hXe_pos : 0 < X ^ e := Real.rpow_pos_of_pos hXpos _
    have hXeH : 2 * X ^ e < H := by
      have : X ^ e * 2 ≤ X ^ e * X ^ (ε / 2) := mul_le_mul_of_nonneg_left hXe2 hXe_pos.le
      rw [← hsplit] at this; linarith
    set h := (X / 4) ^ e with hdef
    have hh_pos : 0 < h := Real.rpow_pos_of_pos (by linarith) _
    have hhXe : h ≤ X ^ e := Real.rpow_le_rpow (by linarith) (by linarith) he0
    set N := ⌈H / h⌉₊ + 1 with hNdef
    have hceil1 : H / h ≤ (⌈H / h⌉₊ : ℝ) := Nat.le_ceil _
    have hceil2 : (⌈H / h⌉₊ : ℝ) < H / h + 1 := Nat.ceil_lt_add_one (by positivity)
    have hHh : H = H / h * h := by field_simp
    have hN : H < (N : ℝ) * h := by
      rw [hNdef]; push_cast
      nlinarith
    have hNh : (N : ℝ) * h ≤ H + 2 * h := by
      rw [hNdef]; push_cast
      nlinarith
    have hcover := EXH_le_sum_cover X H h hh_pos N hN
    have hpiece : ∀ j ∈ Finset.range N,
        (EXH (X - j * h) h : ℝ) ≤ M0 * 2 ^ A * X ^ e / Real.log X ^ A := by
      intro j hj
      have hjN : j < N := Finset.mem_range.mp hj
      have hj_le : (j : ℝ) ≤ ⌈H / h⌉₊ := by
        have : j ≤ ⌈H / h⌉₊ := by omega
        exact_mod_cast this
      have hjh : (j : ℝ) * h < H + h := by
        calc (j : ℝ) * h ≤ (⌈H / h⌉₊ : ℝ) * h := mul_le_mul_of_nonneg_right hj_le hh_pos.le
          _ < (H / h + 1) * h := mul_lt_mul_of_pos_right hceil2 hh_pos
          _ = H + h := by field_simp
      have hj0 : 0 ≤ (j : ℝ) * h := by positivity
      have hXj_low : X / 4 ≤ X - j * h := by linarith
      have hXj_le : X - j * h ≤ X := by linarith
      have hXj0 : X0 ≤ X - j * h := by linarith
      have hlen : h ≤ (X - j * h) ^ e := Real.rpow_le_rpow (by linarith) hXj_low he0
      have hlogXj : 0 < Real.log (X - j * h) := Real.log_pos (by linarith)
      calc (EXH (X - j * h) h : ℝ) ≤ EXH (X - j * h) ((X - j * h) ^ e) := by
            exact_mod_cast EXH_mono_H (X - j * h) hlen
        _ ≤ C0 * (X - j * h) ^ e / Real.log (X - j * h) ^ A := hC0 _ hXj0
        _ ≤ M0 * ((X - j * h) ^ e / Real.log (X - j * h) ^ A) := by
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _)
              (div_nonneg (Real.rpow_nonneg (by linarith) _)
                (Real.rpow_nonneg hlogXj.le _))
        _ ≤ M0 * (2 ^ A * (X - j * h) ^ e / Real.log X ^ A) :=
            mul_le_mul_of_nonneg_left
              (div_logpow_le hX16 hXj_low (Real.rpow_nonneg (by linarith) _) hA.le) hM0
        _ ≤ M0 * (2 ^ A * X ^ e / Real.log X ^ A) := by
            gcongr
            linarith
        _ = M0 * 2 ^ A * X ^ e / Real.log X ^ A := by ring
    have hsum : (EXH X H : ℝ) ≤ N * (M0 * 2 ^ A * X ^ e / Real.log X ^ A) := by
      calc (EXH X H : ℝ) ≤ ∑ j ∈ Finset.range N, (EXH (X - j * h) h : ℝ) := by
            exact_mod_cast hcover
        _ ≤ ∑ _j ∈ Finset.range N, M0 * 2 ^ A * X ^ e / Real.log X ^ A :=
            Finset.sum_le_sum hpiece
        _ = N * (M0 * 2 ^ A * X ^ e / Real.log X ^ A) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hXe_eq : X ^ e = 4 ^ e * h := by
      rw [hdef, ← Real.mul_rpow (by norm_num) (by linarith)]; ring_nf
    have h4e : 0 < (4 : ℝ) ^ e := by positivity
    have hNX : (N : ℝ) * X ^ e ≤ (4 ^ e + 2) * H := by
      calc (N : ℝ) * X ^ e = 4 ^ e * ((N : ℝ) * h) := by rw [hXe_eq]; ring
        _ ≤ 4 ^ e * (H + 2 * h) := mul_le_mul_of_nonneg_left hNh h4e.le
        _ = 4 ^ e * H + 2 * X ^ e := by rw [hXe_eq]; ring
        _ ≤ (4 ^ e + 2) * H := by nlinarith
    have h2A : (0 : ℝ) ≤ 2 ^ A := by positivity
    calc (EXH X H : ℝ) ≤ N * (M0 * 2 ^ A * X ^ e / Real.log X ^ A) := hsum
      _ = M0 * 2 ^ A * ((N : ℝ) * X ^ e) / Real.log X ^ A := by ring
      _ ≤ M0 * 2 ^ A * ((4 ^ e + 2) * H) / Real.log X ^ A := by gcongr
      _ = M0 * 2 ^ A * (4 ^ e + 2) * H / Real.log X ^ A := by ring
      _ ≤ _ := by rw [add_mul, add_div]; linarith

/-- CONDITIONAL ON `LeanLab.ExceptionalSet.LogPowerSaving` and on the Lemma 5.1 core: the
proof of Theorem 1.1 in the parameters of Lemma 5.1, the estimate (1) at the single length
`H = Y^{1/9+2ε}`, `Y = X^{21/40+ε}`, for every small `ε > 0`, gives Theorem 1.1 as stated. -/
theorem thm1_1_of_lemma51_core
    (hcore : ∀ ε : ℝ, 0 < ε → ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      (EXH X ((X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε)) : ℝ)
        ≤ C * (X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε) / Real.log X ^ A)
    (hfull : LeanLab.ExceptionalSet.LogPowerSaving) : ShortIntervalLogSaving (7 / 120) := by
  refine logSaving_of_exactLength (by norm_num) ?_ hfull
  intro ε' hε' A hA
  obtain ⟨ε, hε, hεeq⟩ := exists_lemma51_eps hε'
  obtain ⟨C, X0, hC⟩ := hcore ε hε A hA
  refine ⟨C, max X0 0, fun X hX => ?_⟩
  have hX0 : 0 ≤ X := le_trans (le_max_right _ _) hX
  have hrw : (X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε) = X ^ (7 / 120 + ε') := by
    rw [← Real.rpow_mul hX0, hεeq]
  have := hC X (le_trans (le_max_left _ _) hX)
  rwa [hrw] at this

end LeanLab.Grimmelt2019
