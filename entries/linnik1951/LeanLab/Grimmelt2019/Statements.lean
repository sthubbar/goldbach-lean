module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
P0074 L. Grimmelt, "Goldbach Numbers in Short Intervals: A Nonnegative Model Approach",
arXiv 1910.05187, v2 read 2026-10-17.
Theorem 1.1: for ε, A > 0 and H > X^{7/120+ε}, |E(X,H)| ≪_{ε,A} H (log X)^{-A}, where
E(X,H) is the set of even n ∈ [X - H, X] that are not a sum of two primes.
The introduction also quotes Harman, Chapter 10 of his book "Prime-detecting sieves", for the
same bound in the range H > X^{11/180+ε}, and Jia 1996 for "a version" with H > X^{7/108+ε}.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN. These results say exceptions in short intervals, if any, are rare.
-/

@[expose] public section

namespace LeanLab.Grimmelt2019
open Real Filter

attribute [local instance] Classical.propDecidable

/-! ### Definitions -/

/-- `EXH X H`, the number of even `n` with `4 ≤ n`, `X - H ≤ n ≤ X` that are not a sum of two
primes. The paper's `E(X,H)` counts all even `n ∈ [X - H, X]` with `n ≠ p₁ + p₂`; dropping
`n = 0, 2` changes the count by at most 2, which changes none of the bounds below since in
them `H / (log X)^A → ∞`. This follows the convention of `LeanLab.ExceptionalSet.E`. -/
noncomputable def EXH (X H : ℝ) : ℕ :=
  ((Finset.Icc 4 ⌊X⌋₊).filter (fun n : ℕ => X - H ≤ (n : ℝ) ∧ Even n ∧ ¬ IsGoldbachSum n)).card

/-- The full exceptional count, identical to `LeanLab.ExceptionalSet.E`, restated here because
that module is not yet built in the shared workspace. -/
noncomputable def EFull (X : ℕ) : ℕ :=
  ((Finset.Icc 4 X).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)).card

/-- `E X ≪ X^θ`, identical to `LeanLab.ExceptionalSet.PowerBound`. -/
def FullPowerBound (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → (EFull X : ℝ) ≤ C * (X : ℝ) ^ θ

/-- The estimate (1) of the paper in the range `H > X^{c+ε}`: for every `ε > 0` and `A > 0`
there are constants `C` and `X0`, depending on `ε` and `A`, with
`|E(X,H)| ≤ C · H / (log X)^A` for all `X ≥ X0` and all `H > X^{c+ε}`.
The asymptotic `≪_{ε,A}` is encoded by the existential `C`; the threshold `X0` only makes
`log X` positive and is equivalent to the paper's form. -/
def ShortIntervalLogSaving (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X H : ℝ, X0 ≤ X →
    X ^ (c + ε) < H → (EXH X H : ℝ) ≤ C * H / Real.log X ^ A

/-- Almost all even integers in `[X - H, X]` are Goldbach sums when `H > X^{c+ε}`:
`|E(X,H)| ≤ η H` for every `η > 0` once `X` is large. The weakest reading of the
abstract's "almost all", used for Jia's result which P0074 only calls "a version". -/
def ShortIntervalAlmostAll (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X H : ℝ, X0 ≤ X →
    X ^ (c + ε) < H → (EXH X H : ℝ) ≤ η * H

/-- Every interval `[X - H, X]` with `X^{c+ε} < H ≤ X` and `X` large contains an even
Goldbach sum. -/
def GoldbachInShortIntervals (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X0 : ℝ, ∀ X H : ℝ, X0 ≤ X → X ^ (c + ε) < H → H ≤ X →
    ∃ n : ℕ, Even n ∧ IsGoldbachSum n ∧ X - H ≤ n ∧ (n : ℝ) ≤ X

/-! ### The paper's results as explicit cited inputs -/

/-- Cited. P0074 Theorem 1.1: let `ε, A > 0`; the estimate (1),
`|E(X,H)| ≪_{ε,A} H (log X)^{-A}`, holds for `H > X^{7/120+ε}`. -/
def grimmelt_thm1_1 : Prop := ShortIntervalLogSaving (7 / 120)

/-- Cited, as quoted in P0074 equation (1): Harman, Chapter 10 of "Prime-detecting sieves",
2007, shows (1) for any `ε > 0`, `A > 0` in the range `H > X^{11/180+ε}`. -/
def harman_quoted : Prop := ShortIntervalLogSaving (11 / 180)

/-- Cited, as quoted in P0074: Jia 1996 proved "a version of Theorem 1.1" for
`H > X^{7/108+ε}`. P0074 does not state the saving, so only the almost all form is stated. -/
def jia_quoted : Prop := ShortIntervalAlmostAll (7 / 108)

/-! ### Sanity lemmas, no placeholder proof -/

theorem EXH_mono_H (X : ℝ) {H H' : ℝ} (h : H ≤ H') : EXH X H ≤ EXH X H' := by
  unfold EXH
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, by linarith [hn.2.1], hn.2.2⟩

theorem EXH_le_EFull (X H : ℝ) : EXH X H ≤ EFull ⌊X⌋₊ := by
  unfold EXH EFull
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.2⟩

/-- Binary Goldbach makes every short interval count zero. -/
theorem EXH_eq_zero_of_binaryGoldbach (hG : BinaryGoldbach) (X H : ℝ) : EXH X H = 0 := by
  unfold EXH
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn ⟨_, he, hng⟩
  simp only [Finset.mem_Icc] at hn
  exact hng (hG n he hn.1)

/-! ### Monotonicity in the exponent, no placeholder proof -/

theorem shortIntervalLogSaving_mono {c c' : ℝ} (hc : c ≤ c') (h : ShortIntervalLogSaving c) :
    ShortIntervalLogSaving c' := by
  intro ε hε A hA
  obtain ⟨C, X0, hC⟩ := h ε hε A hA
  refine ⟨C, max X0 1, fun X H hX hH => hC X H (le_of_max_le_left hX) ?_⟩
  have hX1 : 1 ≤ X := le_of_max_le_right hX
  exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hH

theorem shortIntervalAlmostAll_mono {c c' : ℝ} (hc : c ≤ c') (h : ShortIntervalAlmostAll c) :
    ShortIntervalAlmostAll c' := by
  intro ε hε η hη
  obtain ⟨X0, hC⟩ := h ε hε η hη
  refine ⟨max X0 1, fun X H hX hH => hC X H (le_of_max_le_left hX) ?_⟩
  have hX1 : 1 ≤ X := le_of_max_le_right hX
  exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hH

/-! ### Strength of bound, no placeholder proof -/

/-- The log power saving gives the almost all form. -/
theorem almostAll_of_logSaving {c : ℝ} (h : ShortIntervalLogSaving c) :
    ShortIntervalAlmostAll c := by
  intro ε hε η hη
  obtain ⟨C, X0, hC⟩ := h ε hε 1 one_pos
  set M := max C 0
  refine ⟨max (max X0 2) (Real.exp (M / η)), fun X H hX hH => ?_⟩
  have hX0 : X0 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : (2 : ℝ) ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp (M / η) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogM : M / η ≤ Real.log X := by
    rw [← Real.log_exp (M / η)]; exact Real.log_le_log (Real.exp_pos _) hXe
  have hHpos : 0 < H := lt_of_le_of_lt (Real.rpow_nonneg hXpos.le _) hH
  have hb := hC X H hX0 hH
  rw [Real.rpow_one] at hb
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMle : M ≤ η * Real.log X := by
    rw [div_le_iff₀ hη] at hlogM; linarith
  calc (EXH X H : ℝ) ≤ C * H / Real.log X := hb
    _ ≤ M * H / Real.log X := by gcongr; exact le_max_left _ _
    _ ≤ η * H := by
        rw [div_le_iff₀ hlogpos]
        calc M * H ≤ (η * Real.log X) * H := by gcongr
          _ = η * H * Real.log X := by ring

/-- Binary Goldbach would give the log power saving for every exponent. -/
theorem logSaving_of_binaryGoldbach (hG : BinaryGoldbach) (c : ℝ) :
    ShortIntervalLogSaving c := by
  intro ε _ A _
  refine ⟨0, 0, fun X H _ _ => ?_⟩
  rw [EXH_eq_zero_of_binaryGoldbach hG X H]; simp

/-- A full interval power bound `E X ≪ X^θ` with `0 ≤ θ ≤ c` gives the short interval log
power saving in the range `H > X^{c+ε}`. -/
theorem logSaving_of_fullPowerBound {θ c : ℝ} (hθ : 0 ≤ θ) (hθc : θ ≤ c)
    (h : FullPowerBound θ) : ShortIntervalLogSaving c := by
  obtain ⟨C, hC⟩ := h
  intro ε hε A hA
  set M := max C 0
  set δ := ε / A with hδ
  have hδpos : 0 < δ := div_pos hε hA
  refine ⟨M / δ ^ A, 2, fun X H hX hH => ?_⟩
  have hXpos : 0 < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogpos A
  have hM0 : 0 ≤ M := le_max_right _ _
  have hfl1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX1)
  have hflX : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hXpos.le
  have hflpos : (0 : ℝ) ≤ ⌊X⌋₊ := Nat.cast_nonneg _
  -- E bound
  have hE : (EXH X H : ℝ) ≤ M * X ^ c := by
    calc (EXH X H : ℝ) ≤ EFull ⌊X⌋₊ := by exact_mod_cast EXH_le_EFull X H
      _ ≤ C * (⌊X⌋₊ : ℝ) ^ θ := hC _ hfl1
      _ ≤ M * (⌊X⌋₊ : ℝ) ^ θ := by
          gcongr; exact le_max_left _ _
      _ ≤ M * X ^ θ := by gcongr
      _ ≤ M * X ^ c := by gcongr
  -- log bound
  have hlog : Real.log X ≤ X ^ δ / δ := Real.log_le_rpow_div hXpos.le hδpos
  have hkey : Real.log X ^ A ≤ X ^ ε / δ ^ A := by
    calc Real.log X ^ A ≤ (X ^ δ / δ) ^ A := Real.rpow_le_rpow hlogpos.le hlog hA.le
      _ = X ^ ε / δ ^ A := by
          rw [Real.div_rpow (Real.rpow_nonneg hXpos.le _) hδpos.le, ← Real.rpow_mul hXpos.le]
          congr 2
          rw [hδ]; field_simp
  have hδA : 0 < δ ^ A := Real.rpow_pos_of_pos hδpos A
  rw [le_div_iff₀ hlogA]
  calc (EXH X H : ℝ) * Real.log X ^ A ≤ M * X ^ c * (X ^ ε / δ ^ A) := by
        apply mul_le_mul hE hkey hlogA.le (by positivity)
    _ = M / δ ^ A * (X ^ c * X ^ ε) := by ring
    _ = M / δ ^ A * X ^ (c + ε) := by rw [Real.rpow_add hXpos]
    _ ≤ M / δ ^ A * H := by gcongr

/-! ### From few exceptions to Goldbach numbers in every short interval, no placeholder proof -/

/-- An interval `[X - H, X]` with `0 ≤ H ≤ X` has more than `H/2 - 2` even numbers `n ≥ 4`;
if none is a Goldbach sum, all of them are counted by `EXH`. -/
theorem exists_goldbach_of_EXH_small {X H : ℝ} (hH0 : 0 ≤ H) (hHX : H ≤ X)
    (hsmall : (EXH X H : ℝ) ≤ H / 2 - 2) :
    ∃ n : ℕ, Even n ∧ IsGoldbachSum n ∧ X - H ≤ n ∧ (n : ℝ) ≤ X := by
  by_contra hno
  push Not at hno
  have hX0 : 0 ≤ X := le_trans hH0 hHX
  set a : ℕ := max 2 ⌈(X - H) / 2⌉₊ with ha
  set b : ℕ := ⌊X / 2⌋₊ with hb
  have hsub : (Finset.Icc a b).image (fun k => 2 * k) ⊆
      (Finset.Icc 4 ⌊X⌋₊).filter (fun n : ℕ => X - H ≤ (n : ℝ) ∧ Even n ∧ ¬ IsGoldbachSum n) := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_Icc] at hn
    obtain ⟨k, ⟨hak, hkb⟩, rfl⟩ := hn
    have h2a : 2 ≤ a := le_max_left _ _
    have hca : ⌈(X - H) / 2⌉₊ ≤ a := le_max_right _ _
    have hlow : X - H ≤ ((2 * k : ℕ) : ℝ) := by
      have h1 : (X - H) / 2 ≤ (⌈(X - H) / 2⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈(X - H) / 2⌉₊ : ℝ) ≤ k := by exact_mod_cast hca.trans hak
      push_cast; linarith
    have hup : ((2 * k : ℕ) : ℝ) ≤ X := by
      have : (k : ℝ) ≤ X / 2 := le_trans (by exact_mod_cast hkb) (Nat.floor_le (by linarith))
      push_cast; linarith
    have hev : Even (2 * k) := even_two_mul k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, Nat.le_floor hup⟩, hlow, hev, fun hg => ?_⟩
    exact absurd hup (not_le.mpr (hno _ hev hg hlow))
  have hcard : (Finset.Icc a b).card ≤ EXH X H := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun x y hxy => by simpa using hxy
    rw [← Finset.card_image_of_injective (Finset.Icc a b) hinj]
    exact Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hnat : b + 1 ≤ (b + 1 - a) + a := by omega
  have hreal : (b : ℝ) + 1 ≤ (EXH X H : ℝ) + a := by
    have : ((b + 1 : ℕ) : ℝ) ≤ ((b + 1 - a + a : ℕ) : ℝ) := by exact_mod_cast hnat
    have h2 : ((b + 1 - a : ℕ) : ℝ) ≤ EXH X H := by exact_mod_cast hcard
    push_cast at this; linarith
  have hb' : X / 2 < (b : ℝ) + 1 := Nat.lt_floor_add_one _
  have ha' : (a : ℝ) ≤ max 2 ((X - H) / 2 + 1) := by
    rw [ha]; push_cast
    apply max_le_max le_rfl
    exact (Nat.ceil_lt_add_one (by linarith)).le
  rcases le_total 2 ((X - H) / 2 + 1) with h | h
  · rw [max_eq_right h] at ha'; linarith
  · rw [max_eq_left h] at ha'; linarith

/-- The almost all form, for an exponent `c ≥ 0`, puts an even Goldbach sum in every interval
`[X - H, X]` with `X^{c+ε} < H ≤ X` and `X` large. -/
theorem goldbachInShortIntervals_of_almostAll {c : ℝ} (hc : 0 ≤ c)
    (h : ShortIntervalAlmostAll c) : GoldbachInShortIntervals c := by
  intro ε hε
  obtain ⟨X0, hX0⟩ := h ε hε (1 / 4) (by norm_num)
  refine ⟨max (max X0 1) ((8 : ℝ) ^ (1 / (c + ε))), fun X H hX hH hHX => ?_⟩
  have hXX0 : X0 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX1 : 1 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX8 : (8 : ℝ) ^ (1 / (c + ε)) ≤ X := le_trans (le_max_right _ _) hX
  have hce : 0 < c + ε := by linarith
  have h8 : (8 : ℝ) ≤ X ^ (c + ε) := by
    calc (8 : ℝ) = ((8 : ℝ) ^ (1 / (c + ε))) ^ (c + ε) := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ X ^ (c + ε) := Real.rpow_le_rpow (by positivity) hX8 hce.le
  have hH8 : 8 < H := lt_of_le_of_lt h8 hH
  have hb := hX0 X H hXX0 hH
  exact exists_goldbach_of_EXH_small (by linarith) hHX (by linarith)

/-! ### The chain, no placeholder proof -/

/-- Grimmelt's range contains Harman's. -/
theorem harman_of_grimmelt (h : ShortIntervalLogSaving (7 / 120)) :
    ShortIntervalLogSaving (11 / 180) :=
  shortIntervalLogSaving_mono (by norm_num) h

/-- Harman's result gives the almost all form in Jia's range. -/
theorem jia_of_harman (h : ShortIntervalLogSaving (11 / 180)) :
    ShortIntervalAlmostAll (7 / 108) :=
  shortIntervalAlmostAll_mono (by norm_num) (almostAll_of_logSaving h)

/-- Theorem 1.1 puts an even Goldbach sum in `[X - H, X]` whenever `X^{7/120+ε} < H ≤ X`
and `X` is large. -/
theorem goldbach_in_short_intervals_of_grimmelt (h : ShortIntervalLogSaving (7 / 120)) :
    GoldbachInShortIntervals (7 / 120) :=
  goldbachInShortIntervals_of_almostAll (by norm_num) (almostAll_of_logSaving h)

/-- Zhao 2025's `E X ≪ X^{7/10}`, `LeanLab.ExceptionalSet.zhao`, gives only the trivial short
interval range `H > X^{7/10+ε}`; Theorem 1.1 is far stronger. -/
theorem logSaving_seven_tenths_of_zhao (h : FullPowerBound (7 / 10)) :
    ShortIntervalLogSaving (7 / 10) :=
  logSaving_of_fullPowerBound (by norm_num) le_rfl h

end LeanLab.Grimmelt2019
