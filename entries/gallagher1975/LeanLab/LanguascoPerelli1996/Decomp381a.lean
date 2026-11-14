module

public import LeanLab.LanguascoPerelli1996.Statements
public import LeanLab.LanguascoPerelli1996.Partial381
public import LeanLab.LanguascoPerelli1996.Point381

/-!
P0071 pages 358 and 359, displays 20, 21 and 24.
Keep the truncated endpoint in display 21 rather than treating the
without loss of generality passage to display 22 as an exact inequality.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.LanguascoPerelli1996.Decomp381a
open scoped ContDiff
open Real MeasureTheory intervalIntegral

/-- Page 358 display 21. The remainder polynomial stopped at Y. -/
noncomputable def partialR (X Y η : ℝ) (q a : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊,
    ((ArithmeticFunction.vonMangoldt n : ℂ) * e ((n : ℝ) * ((a : ℝ) / q)) -
      (muPhi q : ℂ)) * e ((n : ℝ) * η)

/-- Page 358 display 21 at its full endpoint. The stopped polynomial is R. -/
theorem partialR_full (X η : ℝ) (q a : ℕ) : partialR X (2 * X) η q a = R X η q a := by
  unfold partialR R S Tsum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have he : e ((n : ℝ) * ((a : ℝ) / q + η)) =
      e ((n : ℝ) * ((a : ℝ) / q)) * e ((n : ℝ) * η) := by
    unfold e
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Page 358 display 21, a finite mass witness for its hypothesis.
There are only finitely many integer upper cutoffs below 2X, so a
nonnegative common mass bound exists without GRH or GMCxi. -/
theorem partial_mass_bound_exists (X : ℝ) {ξ : ℝ} (hξ : 0 < ξ) (q a : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
      (∫ t in (-ξ)..ξ, ‖partialR X Y t q a‖ ^ 2) ≤ M := by
  let N := ⌊2 * X⌋₊
  let mass := fun k : ℕ => ∫ t in (-ξ)..ξ, ‖partialR X (k : ℝ) t q a‖ ^ 2
  have hmass (k : ℕ) : 0 ≤ mass k :=
    integral_nonneg_of_forall (by linarith) (fun _ => sq_nonneg _)
  refine ⟨∑ k ∈ Finset.range (N + 1), mass k,
    Finset.sum_nonneg (fun k _ => hmass k), ?_⟩
  intro Y hY hY2
  have hk : ⌊Y⌋₊ ∈ Finset.range (N + 1) := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.floor_le_floor hY2)
  have heq (t : ℝ) : partialR X Y t q a = partialR X (⌊Y⌋₊ : ℝ) t q a := by
    simp only [partialR, Nat.floor_natCast]
  simp_rw [heq]
  exact Finset.single_le_sum (fun k _ => hmass k) hk

/-- LEAF. Page 358 display 20. Sobolev Gallagher and Cauchy Schwarz
for the actual finite remainder polynomial. The explicit constant two
allows the two terms printed with an implied absolute constant. -/
theorem remainder_point_control {X ξ η : ℝ} (hξ : 0 < ξ) (hη : |η| ≤ ξ)
    (q a : ℕ) :
    ‖R X η q a‖ ^ 2 ≤ 2 *
      ((∫ t in (-ξ)..ξ, ‖R X t q a‖ ^ 2) / ξ +
        Real.sqrt ((∫ t in (-ξ)..ξ, ‖R X t q a‖ ^ 2) *
          (∫ t in (-ξ)..ξ, ‖deriv (fun v : ℝ => R X v q a) t‖ ^ 2))) := by
  have hc : ContDiff ℝ ∞ (fun t : ℝ => R X t q a) := by
    unfold R S Tsum e
    have hcast : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
    fun_prop
  exact Point381.point_control hc hξ hη

/-- LEAF. Page 358 display 21, partial summation in L2.
An upper bound M for every stopped polynomial controls the derivative
mass by an absolute constant times X squared M. This retains the maximum
in display 21 and does not assert display 22 for the fixed polynomial. -/
theorem remainder_derivative_of_partial_mass :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ X : ℝ, 1 ≤ X → ∀ ξ : ℝ, 0 < ξ →
      ∀ q a : ℕ, ∀ M : ℝ, 0 ≤ M →
        (∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
          (∫ t in (-ξ)..ξ, ‖partialR X Y t q a‖ ^ 2) ≤ M) →
        (∫ t in (-ξ)..ξ, ‖deriv (fun v : ℝ => R X v q a) t‖ ^ 2) ≤
          A * X ^ 2 * M := by
  refine ⟨64 * Real.pi ^ 2, by positivity, ?_⟩
  intro X hX ξ hξ q a M hM hm
  let m := ⌈X / 4⌉₊
  let N := ⌊2 * X⌋₊
  let c : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
    e ((n : ℝ) * ((a : ℝ) / q)) - (muPhi q : ℂ)
  have hN0 : (0 : ℝ) ≤ 2 * X := by linarith
  have hNle : (N : ℝ) ≤ 2 * X := Nat.floor_le hN0
  have hmN : m ≤ N := by
    apply Nat.ceil_le.mpr
    have hfloor := Nat.lt_floor_add_one (2 * X)
    dsimp [N]
    linarith
  have hm0 : X / 4 ≤ (m : ℝ) := Nat.le_ceil _
  have hprefix : ∀ k, m ≤ k → k ≤ N →
      (∫ t in (-ξ)..ξ, ‖∑ n ∈ Finset.Icc m k, c n * e ((n : ℝ) * t)‖ ^ 2) ≤ M := by
    intro k hmk hkN
    have hkr : (k : ℝ) ≤ 2 * X := (Nat.cast_le.mpr hkN).trans hNle
    have hkl : X / 4 ≤ (k : ℝ) := hm0.trans (Nat.cast_le.mpr hmk)
    have hh := hm (k : ℝ) hkl hkr
    simpa only [partialR, Nat.floor_natCast, m, c] using hh
  have hh := Partial381.polynomial_derivative_mass hmN c (show -ξ ≤ ξ by linarith) hM hprefix
  have heq : (fun v : ℝ => R X v q a) =
      (fun v : ℝ => ∑ n ∈ Finset.Icc m N, c n * e ((n : ℝ) * v)) := by
    funext v
    exact (partialR_full X v q a).symm
  rw [heq]
  calc
    _ ≤ 16 * Real.pi ^ 2 * (N : ℝ) ^ 2 * M := hh
    _ ≤ 64 * Real.pi ^ 2 * X ^ 2 * M := by
      have hs := pow_le_pow_left₀ (Nat.cast_nonneg N) hNle 2
      nlinarith [mul_le_mul_of_nonneg_right hs (show 0 ≤ 16 * Real.pi ^ 2 * M by positivity)]

end LeanLab.LanguascoPerelli1996.Decomp381a


