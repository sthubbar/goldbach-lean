module

public import LeanLab.GoldbachShort78.LiCounts
public import LeanLab.GoldbachShort78.Growth

/-!
R. Li, arXiv 2407.05651 v6, Theorem 1.1, page 2, as a count of exceptions, and its passage to the
dyadic count used in the Goldbach argument. The source has intervals of length depending on `n`
and a positive `ε`, and so does this statement.

AI wrote the Lean code, Codex, OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.GoldbachShort78

/-- The integers `z ∈ [Y, 2Y]` whose closed interval `[z, z + z^a]` has no prime. -/
noncomputable def powerBadSet (a : ℝ) (Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc Y (2 * Y)).filter fun z =>
    ∀ p : ℕ, z ≤ p → (p : ℝ) ≤ z + (z : ℝ) ^ a → ¬p.Prime

/-- Cited input, R. Li, arXiv 2407.05651 v6, Theorem 1.1, page 2, in exceptional count form: for
every `η > 0` and all large `Y`, at most `C Y / log³ Y` of the integers `z ∈ [Y, 2Y]` have no prime
in `[z, z + z^{1/21.5 + η}]`. The theorem allows every large power of the
logarithm, and the power three follows, since `log^{-B} ≤ log^{-3}` for `B ≥ 3`. It is printed for sufficiently small positive `ε`, and a longer interval
can only have fewer exceptions, so it extends to every `η > 0`. -/
def LiPrintedExceptionalCount : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C y₀ : ℝ, 0 < C ∧ ∀ Y : ℕ, y₀ ≤ Y →
    ((powerBadSet (1 / 21.5 + η) Y).card : ℝ) ≤ C * Y / Real.log Y ^ 3

/-- Positive exponent slack absorbs the dyadic factor and the implied constant. -/
theorem almostAllCount_of_power_exceptions {a b C y₀ : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (_hC : 0 < C)
    (hin : ∀ Y : ℕ, y₀ ≤ Y → ((powerBadSet a Y).card : ℝ) ≤ C * Y / Real.log Y ^ 3) :
    ∃ X : ℝ, AlmostAllCount b X := by
  classical
  have hgrowth : ∀ᶠ y : ℝ in Filter.atTop, (2 : ℝ) ^ a ≤ y ^ (b - a) :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop ((2 : ℝ) ^ a)
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hgrowth
  have hlog : ∀ᶠ y : ℝ in Filter.atTop, max C 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop (max C 1)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hlog
  refine ⟨max y₀ (max A (max B 2)), ?_⟩
  intro Y hY H hH
  have hY0 : y₀ ≤ (Y : ℝ) := by grind
  have hYA : A ≤ (Y : ℝ) := by grind
  have hYB : B ≤ (Y : ℝ) := by grind
  have hY2 : (2 : ℝ) ≤ Y := by grind
  have hYpos : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := by have := hB Y hYB; grind
  have hCle : C ≤ Real.log Y := le_trans (le_max_left _ _) (hB Y hYB)
  have hsub : badSet Y H ⊆ powerBadSet a Y := by
    intro z hz
    obtain ⟨hzmem, hfree⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzY, hz2Y⟩ := Finset.mem_Icc.mp hzmem
    have hz2 : (z : ℝ) ≤ 2 * (Y : ℝ) := by exact_mod_cast hz2Y
    have hlength : (z : ℝ) ^ a ≤ H := by
      calc
        (z : ℝ) ^ a ≤ (2 * (Y : ℝ)) ^ a :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hz2 ha
        _ = (2 : ℝ) ^ a * (Y : ℝ) ^ a := Real.mul_rpow (by norm_num) hYpos.le
        _ ≤ (Y : ℝ) ^ (b - a) * (Y : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right (hA Y hYA) (by positivity)
        _ = (Y : ℝ) ^ b := by rw [← Real.rpow_add hYpos]; congr 1; ring
        _ ≤ H := hH
    apply Finset.mem_filter.mpr
    refine ⟨hzmem, ?_⟩
    intro p hzp hpupper hpprime
    have hpH : p ≤ z + H := by
      have hpr : (p : ℝ) ≤ (z : ℝ) + H := by linarith
      exact_mod_cast hpr
    exact hfree p (Finset.mem_Icc.mpr ⟨hzp, hpH⟩) hpprime
  have hcard : ((badSet Y H).card : ℝ) ≤ (powerBadSet a Y).card := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    ((badSet Y H).card : ℝ) ≤ (powerBadSet a Y).card := hcard
    _ ≤ C * Y / Real.log Y ^ 3 := hin Y hY0
    _ ≤ (Y : ℝ) / Real.log Y ^ 2 := by
      apply (div_le_div_iff₀ (pow_pos hlogY 3) (pow_pos hlogY 2)).mpr
      have hm := mul_le_mul_of_nonneg_right hCle
        (show 0 ≤ (Y : ℝ) * Real.log Y ^ 2 by positivity)
      nlinarith

/-- The dyadic count at exponent `1/21.5 + ε` follows from `LiPrintedExceptionalCount`, for every
positive `ε`. -/
theorem liAlmostAllCountEps_of_printed (hin : LiPrintedExceptionalCount) {ε : ℝ}
    (hε : 0 < ε) : ∃ y₀ : ℝ, LiAlmostAllCountEps ε y₀ := by
  obtain ⟨C, y₀, hC, hbound⟩ := hin (ε / 2) (by linarith)
  exact almostAllCount_of_power_exceptions
    (by positivity : (0 : ℝ) ≤ 1 / 21.5 + ε / 2)
    (by linarith : (1 : ℝ) / 21.5 + ε / 2 < 1 / 21.5 + ε) hC hbound

end LeanLab.GoldbachShort78
