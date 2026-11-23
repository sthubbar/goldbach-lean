module

public import LeanLab.BhowmikGrimmelt2026.Statements

/-!
Equation 7.4 of Bhowmik and Grimmelt 2026, page 26.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- The positive sign discrete transform from page 26 below equation 7.4. -/
noncomputable def GThat (G : ℝ → ℝ) (T β : ℝ) : ℂ :=
  ∑' n : ℤ, (GT G T n : ℂ) * ee (β * n)

/-- The scaled weight vanishes outside its scaled support. -/
theorem GT_eq_zero {G : ℝ → ℝ} (hG : Function.support G ⊆ Set.Icc (-2) 2)
    {T x : ℝ} (hT : 0 < T) (hx : 2 * T < |x|) : GT G T x = 0 := by
  have hg : G (x / T) = 0 := by
    by_contra hn
    have h := hG hn
    have hl : -2 * T ≤ x := (le_div_iff₀ hT).mp h.1
    have hu : x ≤ 2 * T := (div_le_iff₀ hT).mp h.2
    have ha : |x| ≤ 2 * T := abs_le.mpr ⟨by linarith, hu⟩
    linarith
  simp [GT, hg]

/-- Integer samples have support in an explicit finite interval. -/
theorem GT_int_eq_zero {G : ℝ → ℝ} (hG : Function.support G ⊆ Set.Icc (-2) 2)
    {T : ℝ} (hT : 0 < T) (n : ℤ)
    (hn : n ∉ Finset.Icc ⌈-2 * T⌉ ⌊2 * T⌋) : GT G T n = 0 := by
  apply GT_eq_zero hG hT
  by_contra h
  have hbound : |(n : ℝ)| ≤ 2 * T := le_of_not_gt h
  have hlo := (abs_le.mp hbound).1
  have hhi := (abs_le.mp hbound).2
  apply hn
  exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr hhi⟩

/-- The integer samples of the scaled weight are summable. -/
theorem summable_GT {G : ℝ → ℝ} (hG : Function.support G ⊆ Set.Icc (-2) 2)
    {T : ℝ} (hT : 0 < T) : Summable (fun n : ℤ => GT G T n) := by
  exact summable_of_ne_finset_zero (GT_int_eq_zero hG hT)

/-- Multiplying integer samples by any complex sequence preserves finite support. -/
theorem summable_GT_mul {G : ℝ → ℝ} (hG : Function.support G ⊆ Set.Icc (-2) 2)
    {T : ℝ} (hT : 0 < T) (f : ℤ → ℂ) :
    Summable (fun n : ℤ => (GT G T n : ℂ) * f n) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc ⌈-2 * T⌉ ⌊2 * T⌋)
  intro n hn
  simp [GT_int_eq_zero hG hT n hn]

/-- Scaling preserves evenness, including at the totalized value T zero. -/
theorem GT_even {G : ℝ → ℝ} (hG : ∀ x, G (-x) = G x) (T x : ℝ) :
    GT G T (-x) = GT G T x := by
  simp [GT, neg_div, hG]

/-- The positive and negative discrete Fourier signs agree for an even weight. -/
theorem GThat_eq_neg {G : ℝ → ℝ} (hG : ∀ x, G (-x) = G x) (T β : ℝ) :
    GThat G T β = ∑' n : ℤ, (GT G T n : ℂ) * ee (-(β * n)) := by
  unfold GThat
  conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply, Int.cast_neg, GT_even hG, mul_neg]

/-- Multiplication of the additive exponential adds its real arguments. -/
theorem ee_mul (x y : ℝ) : ee x * ee y = ee (x + y) := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Equation 7.4 with the paper's positive sign transform. -/
theorem bRhat_eq {G : ℝ → ℝ} (hsupp : Function.support G ⊆ Set.Icc (-2) 2)
    (heven : ∀ x, G (-x) = G x) (R : ℝ) (T : ℕ → ℝ)
    (hT : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q) (α : ℝ) :
    bRhat G R T α = ∑ q ∈ Finset.Icc 1 ⌊R⌋₊,
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        GThat G (T q) (α - a / q) := by
  classical
  have hs (q : ℕ) (hq : q ∈ Finset.Icc 1 ⌊R⌋₊) (a : ℕ) :
      Summable (fun n : ℤ =>
        ee ((a : ℝ) * n / q) * (GT G (T q) n : ℂ) * ee (-(α * n))) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      summable_GT_mul hsupp (hT q hq)
        (fun n => ee ((a : ℝ) * n / q) * ee (-(α * n)))
  unfold bRhat bR ramanujan
  simp_rw [Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun q hq => summable_sum (fun a _ => hs q hq a))]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Summable.tsum_finsetSum (fun a _ => hs q hq a)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [GThat_eq_neg heven]
  apply tsum_congr
  intro n
  calc
    ee ((a : ℝ) * n / q) * (GT G (T q) n : ℂ) * ee (-(α * n)) =
        (GT G (T q) n : ℂ) * (ee ((a : ℝ) * n / q) * ee (-(α * n))) := by ring
    _ = (GT G (T q) n : ℂ) * ee (-((α - a / q) * n)) := by
      rw [ee_mul]
      congr 2
      ring

end LeanLab.BhowmikGrimmelt2026
