module

public import Mathlib
public import LeanLab.Common.Goldbach

/-!
The exceptional set of binary Goldbach, E(X), from almost all to X^{7/10}.
P0063 van der Corput, almost all even numbers; catalogued as Acta Arith. 2, 1936, while
  Nathanson's survey arXiv math/0412220 and Montgomery-Vaughan's reference list give 1938,
  Proc. Akad. Wet. Amsterdam 41. QUESTION for the catalogue.
P0064 Chudakov 1938, Izv. Akad. Nauk SSSR, density of non-representable evens.
  Nathanson's survey credits van der Corput, Chudakov and Estermann together with
  E(X) = O(X (log X)^{-A}) for every A; the title forms are density zero.
P0091 Estermann 1938, Proc. LMS 44, almost all even numbers, title; the strength
  E(X) ≪ X (log X)^{-A} is the classical form of the Vinogradov-method result as Zhao 2025
  states it, not read from Estermann's text.
P0015 Montgomery, Vaughan 1975, Acta Arith. 27, E(X) ≪ X^{1-δ}, as Zhao 2025 states it.
P0095 Lu 2010, J. Number Theory 130, δ = 0.121, as Zhao 2025 states it.
P0016 Pintz 2018, arXiv 1804.09084, abstract: E(X) < X^0.72 for sufficiently large X.
P0040 Zhao 2025, arXiv 2511.05631, Theorem 1.1: E(X) = O(X^{7/10}), ineffective constant.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN; these results say exceptions, if any, are rare.
-/

@[expose] public section

namespace LeanLab.ExceptionalSet
open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-- `E X`, the number of even `n` with `4 ≤ n ≤ X` that are not a sum of two primes.
The papers count evens below or up to `X` that are not a sum of two primes, or of two odd
primes, Montgomery-Vaughan also counting `2`; `4 = 2 + 2` is a Goldbach sum here, so the counts
differ from `E X` by at most 2, which changes none of the bounds. -/
noncomputable def E (X : ℕ) : ℕ :=
  ((Finset.Icc 4 X).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)).card

theorem E_le (X : ℕ) : E X ≤ X := by
  unfold E
  refine (Finset.card_filter_le _ _).trans ?_
  simp only [Nat.card_Icc]; omega

theorem E_eq_zero_of_upTo {N : ℕ} (h : EvenGoldbachUpTo N) (X : ℕ) (hX : X ≤ N) : E X = 0 := by
  unfold E
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn ⟨he, hng⟩
  simp only [Finset.mem_Icc] at hn
  exact hng (h n he hn.1 (hn.2.trans hX))

/-- Binary Goldbach is exactly `E X = 0` for every `X`. -/
theorem binaryGoldbach_iff : BinaryGoldbach ↔ ∀ X, E X = 0 := by
  constructor
  · intro h X
    exact E_eq_zero_of_upTo (N := X) (fun n he h4 _ => h n he h4) X le_rfl
  · intro h n he h4
    by_contra hng
    have : 0 < E n := by
      unfold E
      apply Finset.card_pos.mpr
      exact ⟨n, by simp [Finset.mem_Icc, h4, he, hng]⟩
    rw [h n] at this; exact lt_irrefl 0 this

/-! ### The strengths of bound -/

/-- Almost all even numbers are Goldbach sums: `E X / X → 0`. -/
def DensityZero : Prop := Tendsto (fun X : ℕ => (E X : ℝ) / X) atTop (𝓝 0)

/-- `E X ≪_A X / (log X)^A` for every `A > 0`. -/
def LogPowerSaving : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → (E X : ℝ) ≤ C * X / Real.log X ^ A

/-- `E X ≪ X^θ`. -/
def PowerBound (θ : ℝ) : Prop := ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → (E X : ℝ) ≤ C * (X : ℝ) ^ θ

/-- `E X ≪ X^{1-δ}` for some `δ > 0`. -/
def PowerSaving : Prop := ∃ δ : ℝ, 0 < δ ∧ PowerBound (1 - δ)

/-- `E X < X^θ` for all sufficiently large `X`. -/
def EventuallyBelow (θ : ℝ) : Prop := ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → (E X : ℝ) < (X : ℝ) ^ θ

/-! ### The papers, cited, with `sorry`

The first four titles are now plain `Prop`s, `_stmt`, PROVED unconditional in
`ExceptionalSet/Discharged.lean` from the lab's Siegel-Walfisz chain, audit U-1058,
PC run 20261019T1204Z-858. They cannot be proved here, since that chain imports this file. -/

/-- P0063 van der Corput, title: Goldbach holds for almost all even numbers. -/
def vanDerCorput_stmt : Prop := DensityZero

/-- P0064 Chudakov 1938, title: the non-representable evens have density zero. -/
def chudakov_stmt : Prop := DensityZero

/-- P0063 and P0064 in the log power strength that Nathanson's survey credits to them. -/
def vanDerCorput_chudakov_strong_stmt : Prop := LogPowerSaving

/-- P0091 Estermann 1938, almost all even numbers, in the classical log power form. -/
def estermann_stmt : Prop := LogPowerSaving






/-! ### Each result implies the older ones, zero sorry -/

theorem powerBound_mono {θ θ' : ℝ} (hθ : θ ≤ θ') (h : PowerBound θ) : PowerBound θ' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  calc (E X : ℝ) ≤ C * (X : ℝ) ^ θ := hC X hX
    _ ≤ max C 0 * (X : ℝ) ^ θ := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * (X : ℝ) ^ θ' :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 hθ) (le_max_right _ _)

theorem powerBound_of_eventuallyBelow {θ : ℝ} (hθ : 0 ≤ θ) (h : EventuallyBelow θ) :
    PowerBound θ := by
  obtain ⟨X0, hX0⟩ := h
  refine ⟨X0 + 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpow : (1 : ℝ) ≤ (X : ℝ) ^ θ := Real.one_le_rpow hX1 hθ
  rcases Nat.lt_or_ge X X0 with hlt | hge
  · have hE : (E X : ℝ) ≤ X := by exact_mod_cast E_le X
    have : (X : ℝ) ≤ X0 := by exact_mod_cast hlt.le
    nlinarith
  · have := hX0 X hge
    nlinarith

theorem eventuallyBelow_of_powerBound {θ θ' : ℝ} (hθ : θ < θ') (h : PowerBound θ) :
    EventuallyBelow θ' := by
  obtain ⟨C, hC⟩ := h
  have ht : Tendsto (fun X : ℕ => (X : ℝ) ^ (θ' - θ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨X0, hX0⟩ := (ht.eventually_gt_atTop (max C 0)).exists_forall_of_atTop
  refine ⟨max X0 1, fun X hX => ?_⟩
  have hX1 : (1 : ℕ) ≤ X := le_of_max_le_right hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hbig := hX0 X (le_of_max_le_left hX)
  have hpos : (0 : ℝ) < (X : ℝ) ^ θ := Real.rpow_pos_of_pos hXpos θ
  calc (E X : ℝ) ≤ C * (X : ℝ) ^ θ := hC X hX1
    _ ≤ max C 0 * (X : ℝ) ^ θ := by gcongr; exact le_max_left _ _
    _ < (X : ℝ) ^ (θ' - θ) * (X : ℝ) ^ θ := by gcongr
    _ = (X : ℝ) ^ θ' := by rw [← Real.rpow_add hXpos]; ring_nf

theorem logPowerSaving_of_powerBound {θ : ℝ} (hθ : θ < 1) (h : PowerBound θ) :
    LogPowerSaving := by
  obtain ⟨C, hC⟩ := h
  intro A hA
  set ε : ℝ := (1 - θ) / A with hε
  have hεpos : 0 < ε := div_pos (by linarith) hA
  refine ⟨max C 0 * (1 / ε ^ A), fun X hX => ?_⟩
  have hX1 : (1 : ℕ) ≤ X := by omega
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogpos A
  -- (log X)^A ≤ X^{1-θ} / ε^A
  have hlog : Real.log X ≤ (X : ℝ) ^ ε / ε := Real.log_le_rpow_div hXpos.le hεpos
  have hkey : Real.log X ^ A ≤ (X : ℝ) ^ (1 - θ) / ε ^ A := by
    calc Real.log X ^ A ≤ ((X : ℝ) ^ ε / ε) ^ A :=
          Real.rpow_le_rpow hlogpos.le hlog hA.le
      _ = (X : ℝ) ^ (1 - θ) / ε ^ A := by
          rw [Real.div_rpow (Real.rpow_nonneg hXpos.le _) hεpos.le, ← Real.rpow_mul hXpos.le]
          congr 2
          rw [hε]; field_simp
  have hEX := hC X hX1
  have hC0 : (E X : ℝ) ≤ max C 0 * (X : ℝ) ^ θ :=
    hEX.trans (by gcongr; exact le_max_left _ _)
  rw [le_div_iff₀ hlogA]
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have hθpos : 0 < (X : ℝ) ^ θ := Real.rpow_pos_of_pos hXpos θ
  calc (E X : ℝ) * Real.log X ^ A ≤ max C 0 * (X : ℝ) ^ θ * ((X : ℝ) ^ (1 - θ) / ε ^ A) := by
        apply mul_le_mul hC0 hkey hlogA.le (by positivity)
    _ = max C 0 * (1 / ε ^ A) * ((X : ℝ) ^ θ * (X : ℝ) ^ (1 - θ)) := by ring
    _ = max C 0 * (1 / ε ^ A) * X := by
        rw [← Real.rpow_add hXpos]; norm_num

theorem densityZero_of_logPowerSaving (h : LogPowerSaving) : DensityZero := by
  obtain ⟨C, hC⟩ := h 1 one_pos
  have hlog : Tendsto (fun X : ℕ => C / Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog ?_ ?_
  · exact Eventually.of_forall fun X => by positivity
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
    have hXpos : (0 : ℝ) < X := by linarith
    have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
    have := hC X hX
    rw [Real.rpow_one] at this
    rw [div_le_div_iff₀ hXpos hlogpos]
    calc (E X : ℝ) * Real.log X ≤ (C * X / Real.log X) * Real.log X := by gcongr
      _ = C * X := by field_simp

/-! ### The chain, newest to oldest -/

theorem pintz_of_zhao (h : PowerBound (7 / 10)) : EventuallyBelow 0.72 :=
  eventuallyBelow_of_powerBound (by norm_num) h

theorem lu_of_pintz (h : EventuallyBelow 0.72) : PowerBound 0.879 :=
  powerBound_mono (by norm_num) (powerBound_of_eventuallyBelow (by norm_num) h)

theorem li_of_lu (h : PowerBound 0.879) : PowerBound 0.914 := powerBound_mono (by norm_num) h

theorem montgomeryVaughan_of_li (h : PowerBound 0.914) : PowerSaving :=
  ⟨0.086, by norm_num, by convert h using 1; norm_num⟩

theorem montgomeryVaughan_of_lu (h : PowerBound 0.879) : PowerSaving :=
  ⟨0.121, by norm_num, by convert h using 1; norm_num⟩

theorem estermann_of_montgomeryVaughan (h : PowerSaving) : LogPowerSaving := by
  obtain ⟨δ, hδ, hb⟩ := h
  exact logPowerSaving_of_powerBound (by linarith) hb

theorem densityZero_of_estermann (h : LogPowerSaving) : DensityZero :=
  densityZero_of_logPowerSaving h

/-- The strong form of P0063 and P0064 gives their title forms. -/
theorem vanDerCorput_of_strong (h : LogPowerSaving) : DensityZero :=
  densityZero_of_logPowerSaving h

/-- Zhao 2025 implies every older result in this module. -/
theorem all_of_zhao (h : PowerBound (7 / 10)) :
    EventuallyBelow 0.72 ∧ PowerBound 0.879 ∧ PowerSaving ∧ LogPowerSaving ∧ DensityZero := by
  have h1 := pintz_of_zhao h
  have h2 := lu_of_pintz h1
  have h3 := montgomeryVaughan_of_lu h2
  have h4 := estermann_of_montgomeryVaughan h3
  exact ⟨h1, h2, h3, h4, densityZero_of_estermann h4⟩

/-- Binary Goldbach would give every bound here with room to spare. -/
theorem zhao_of_binaryGoldbach (h : BinaryGoldbach) : PowerBound (7 / 10) :=
  ⟨0, fun X _ => by simp [binaryGoldbach_iff.mp h X]⟩

end LeanLab.ExceptionalSet
