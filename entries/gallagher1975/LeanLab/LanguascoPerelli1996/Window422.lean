module

public import LeanLab.LanguascoPerelli1996.Decomp381a
public import LeanLab.PNTPort.Gallagher.Basic

/-!
P0071 pages 355 through 358, Gallagher windows for the stopped remainder.
The integer window version reuses PNTPort.Gallagher.gallagher.
Keep both boundary pieces as required by page 359.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.LanguascoPerelli1996.Window422
open Real MeasureTheory intervalIntegral

/-- Pages 355 and 358 displays 14 and 23, the actual remainder coefficients.
The upper endpoint is supplied by the finite polynomial length. -/
noncomputable def coeff (X : ℝ) (q a n : ℕ) : ℂ :=
  if ⌈X / 4⌉₊ ≤ n then
    (ArithmeticFunction.vonMangoldt n : ℂ) * e ((n : ℝ) * ((a : ℝ) / q)) -
      (muPhi q : ℂ)
  else 0

/-- Page 356, the leading window mass in the integer Gallagher formulation.
Only windows whose upper endpoint precedes the final cutoff occur here. -/
noncomputable def leadingMass (X Y : ℝ) (q a L : ℕ) : ℝ :=
  ∑ m ∈ (Finset.range (⌊Y⌋₊ + 1 + L)).filter
    (fun m => m < ⌊Y⌋₊ + 1 ∧ m < ⌈X / 4⌉₊ + L),
    ‖LeanLab.PNTPort.Gallagher.win (coeff X q a) (⌊Y⌋₊ + 1) L m‖ ^ 2

/-- Page 356, the interior window mass in the integer formulation. -/
noncomputable def interiorMass (X Y : ℝ) (q a L : ℕ) : ℝ :=
  ∑ m ∈ (Finset.range (⌊Y⌋₊ + 1 + L)).filter
    (fun m => m < ⌊Y⌋₊ + 1 ∧ ⌈X / 4⌉₊ + L ≤ m),
    ‖LeanLab.PNTPort.Gallagher.win (coeff X q a) (⌊Y⌋₊ + 1) L m‖ ^ 2

/-- Pages 356 and 357, the trailing window mass in the integer formulation.
The strict final cutoff prevents overlap with the leading piece. -/
noncomputable def trailingMass (X Y : ℝ) (q a L : ℕ) : ℝ :=
  ∑ m ∈ (Finset.range (⌊Y⌋₊ + 1 + L)).filter (fun m => ⌊Y⌋₊ + 1 ≤ m),
    ‖LeanLab.PNTPort.Gallagher.win (coeff X q a) (⌊Y⌋₊ + 1) L m‖ ^ 2

/-- Page 358 display 21, the stopped polynomial in the range convention
of the existing discrete Gallagher theorem. No endpoint is discarded. -/
theorem partialR_eq_range (X Y η : ℝ) (q a : ℕ) :
    Decomp381a.partialR X Y η q a =
      ∑ n ∈ Finset.range (⌊Y⌋₊ + 1),
        coeff X q a n * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * η) := by
  have he (t : ℝ) : LeanLab.PNTPort.LargeSieve.e t = e t := by
    unfold LeanLab.PNTPort.LargeSieve.e e
    congr 1
    push_cast
    ring
  simp_rw [he, coeff, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hs : (Finset.range (⌊Y⌋₊ + 1)).filter (fun n => ⌈X / 4⌉₊ ≤ n) =
      Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hs]
  rfl

/-- Pages 356 and 357, the three Gallagher regions partition every
integer window. This identity also covers windows longer than the polynomial. -/
theorem window_mass_split (X Y : ℝ) (q a L : ℕ) :
    (∑ m ∈ Finset.range (⌊Y⌋₊ + 1 + L),
      ‖LeanLab.PNTPort.Gallagher.win (coeff X q a) (⌊Y⌋₊ + 1) L m‖ ^ 2) =
      leadingMass X Y q a L + interiorMass X Y q a L + trailingMass X Y q a L := by
  unfold leadingMass interiorMass trailingMass
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h : m < ⌊Y⌋₊ + 1
  · by_cases hl : m < ⌈X / 4⌉₊ + L
    · simp [h, hl, Nat.not_le.mpr hl, Nat.not_le.mpr h]
    · simp [h, hl, Nat.le_of_not_lt hl, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]

/-- Pages 355 and 358 displays 14 and 23, the finite Gallagher transfer.
The three masses retain the original endpoints of the stopped sum. -/
theorem remainder_mass_le_windows (X Y : ℝ) (q a L : ℕ) (hL : 0 < L)
    {ξ : ℝ} (hξ : 0 < ξ) (hξL : ξ ≤ 1 / (2 * (L : ℝ))) :
    (∫ t in (-ξ)..ξ, ‖Decomp381a.partialR X Y t q a‖ ^ 2) ≤
      (Real.pi / (2 * (L : ℝ))) ^ 2 *
        (leadingMass X Y q a L + interiorMass X Y q a L + trailingMass X Y q a L) := by
  have hc : Continuous (fun t : ℝ => Decomp381a.partialR X Y t q a) := by
    unfold Decomp381a.partialR e
    fun_prop
  have hsub : (∫ t in (-ξ)..ξ, ‖Decomp381a.partialR X Y t q a‖ ^ 2) ≤
      ∫ t in (-(1 / (2 * (L : ℝ))))..(1 / (2 * (L : ℝ))),
        ‖Decomp381a.partialR X Y t q a‖ ^ 2 :=
    integral_mono_interval (by linarith) (by linarith) hξL
      (Filter.Eventually.of_forall fun t => sq_nonneg _)
      ((hc.norm.pow 2).intervalIntegrable _ _)
  have hg := LeanLab.PNTPort.Gallagher.gallagher (coeff X q a) (⌊Y⌋₊ + 1) L hL
  simp_rw [← partialR_eq_range] at hg
  rw [window_mass_split] at hg
  exact hsub.trans hg

/-- Derived integer choice for pages 355 and 358, h comparable to one
over twice the arc radius. Both reciprocal bounds survive rounding. -/
theorem window_length_exists {ξ : ℝ} (hξ : 0 < ξ) (hξ2 : ξ ≤ 1 / 2) :
    ∃ L : ℕ, 0 < L ∧ 1 / (4 * (L : ℝ)) ≤ ξ ∧ ξ ≤ 1 / (2 * (L : ℝ)) := by
  let L := ⌊1 / (2 * ξ)⌋₊
  have hu : 1 ≤ 1 / (2 * ξ) := (le_div_iff₀ (by positivity)).2 (by linarith)
  have hL : 0 < L := Nat.floor_pos.mpr hu
  have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hlo : (L : ℝ) ≤ 1 / (2 * ξ) := Nat.floor_le (by positivity)
  have hhi : 1 / (2 * ξ) < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  refine ⟨L, hL, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity)).2
    have hh : 1 < ((L : ℝ) + 1) * (2 * ξ) := (div_lt_iff₀ (by positivity)).1 hhi
    nlinarith [mul_le_mul_of_nonneg_right hL1 hξ.le]
  · apply (le_div_iff₀ (by positivity)).2
    have hh := (le_div_iff₀ (by positivity)).1 hlo
    nlinarith

/-- Derived scalar step after Gallagher in page 358 display 23.
Three window bounds at scale L X to the one plus epsilon give the
desired arc mass scale xi X to the one plus epsilon. -/
theorem window_scale {ξ Z A B C u v w : ℝ} {L : ℕ}
    (hL : 0 < L) (hξ : 0 < ξ) (hlo : 1 / (4 * (L : ℝ)) ≤ ξ)
    (hZ : 0 ≤ Z) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hu : u ≤ A * L * Z) (hv : v ≤ B * L * Z) (hw : w ≤ C * L * Z) :
    (Real.pi / (2 * (L : ℝ))) ^ 2 * (u + v + w) ≤
      (Real.pi ^ 2 * (A + B + C)) * ξ * Z := by
  have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hsum : u + v + w ≤ (A + B + C) * L * Z := by linarith
  calc
    _ ≤ (Real.pi / (2 * (L : ℝ))) ^ 2 * ((A + B + C) * L * Z) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (Real.pi ^ 2 * (A + B + C) * Z) * (1 / (4 * (L : ℝ))) := by
      field_simp [ne_of_gt hLr]
      <;> ring
    _ ≤ (Real.pi ^ 2 * (A + B + C) * Z) * ξ :=
      mul_le_mul_of_nonneg_left hlo (by positivity)
    _ = _ := by ring

end LeanLab.LanguascoPerelli1996.Window422

