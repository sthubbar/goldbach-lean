module

public import LeanLab.Linnik.ExplicitFormula.Defs

/-!
# From the Cesaro sum to sharp sums, Davenport ch. 17

AI wrote the Lean code. Binary Goldbach is OPEN.
`J(x) = x² S(x, χ) = Σ_{n ≤ x} n χ(n) Λ(n) (x - n)`, so `(J(x + h) - J(x))/h` is the sharp sum
`Σ_{n ≤ x} b(n)` up to the `b(n)` with `x < n ≤ x + h`, as in the lab's von Koch squeeze
`LeanLab.PNTPort.ExplicitPsi1.VonKoch2`.
-/

@[expose] public section


namespace LeanLab.Linnik.ExplicitFormula

open Complex Finset

/-- `J(x) = Σ_{n ≤ x} b(n) (x - n)` for `x > 0`. -/
theorem Jchi_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    Jchi χ x = ∑ n ∈ range (⌊x⌋₊ + 1), bCoef χ n * ((x : ℂ) - n) := by
  unfold Jchi cesaroChi bCoef
  rw [mul_sum]
  refine sum_congr rfl fun n hn => ?_
  have hn' : n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (mem_range.mp hn)
  have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hn') (Nat.floor_le hx.le)
  rw [wK_of_le ((div_le_one hx).mpr hnx)]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp

/-- `‖b(n)‖ ≤ n log n`. -/
theorem norm_bCoef_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖bCoef χ n‖ ≤ n * Real.log n := by
  unfold bCoef
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
  have h2 : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ Real.log n := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact ArithmeticFunction.vonMangoldt_le_log
  have h3 : 0 ≤ ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ := norm_nonneg _
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (n : ℝ) * ‖χ n‖ * ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖
      ≤ n * 1 * ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ := by gcongr
    _ ≤ n * 1 * Real.log n := by gcongr
    _ = n * Real.log n := by ring

/-- The first difference of `J` is the sharp sum up to the next `h` terms. -/
theorem first_difference {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x h : ℝ} (hx : 0 < x)
    (hh : 0 < h) :
    ‖(Jchi χ (x + h) - Jchi χ x) / h - ∑ n ∈ range (⌊x⌋₊ + 1), bCoef χ n‖ ≤
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖bCoef χ n‖ := by
  have hxh : 0 < x + h := by linarith
  set a := ⌊x⌋₊ with ha
  set c := ⌊x + h⌋₊ with hc
  have hac : a ≤ c := Nat.floor_le_floor (by linarith)
  have key : (Jchi χ (x + h) - Jchi χ x) / h - ∑ n ∈ range (a + 1), bCoef χ n =
      ∑ n ∈ Ioc a c, bCoef χ n * ((((x + h - n) / h : ℝ)) : ℂ) := by
    rw [Jchi_eq χ hxh, Jchi_eq χ hx, ← hc, ← ha,
      ← Finset.sum_range_add_sum_Ico _ (by omega : a + 1 ≤ c + 1), Finset.Ico_add_one_add_one_eq_Ioc]
    have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    have e1 : ∑ n ∈ range (a + 1), bCoef χ n * (((x + h : ℝ) : ℂ) - n) -
        ∑ n ∈ range (a + 1), bCoef χ n * ((x : ℂ) - n) =
        (h : ℂ) * ∑ n ∈ range (a + 1), bCoef χ n := by
      rw [← sum_sub_distrib, mul_sum]
      refine sum_congr rfl fun n _ => ?_
      push_cast; ring
    have e2 : ∑ n ∈ Ioc a c, bCoef χ n * (((x + h : ℝ) : ℂ) - n) =
        (h : ℂ) * ∑ n ∈ Ioc a c, bCoef χ n * ((((x + h - n) / h : ℝ)) : ℂ) := by
      rw [mul_sum]
      refine sum_congr rfl fun n _ => ?_
      push_cast; field_simp
    rw [add_sub_right_comm, e1, e2]
    field_simp
    ring
  rw [key]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
  have hnx : x < n := by
    have := Nat.lt_floor_add_one x
    have : ((a + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn1
    push_cast at this
    linarith
  have hnxh : (n : ℝ) ≤ x + h := le_trans (by exact_mod_cast hn2) (Nat.floor_le hxh.le)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have t0 : 0 ≤ (x + h - n) / h := div_nonneg (by linarith) hh.le
  have t1 : (x + h - n) / h ≤ 1 := (div_le_one hh).mpr (by linarith)
  rw [abs_of_nonneg t0]
  calc ‖bCoef χ n‖ * ((x + h - n) / h) ≤ ‖bCoef χ n‖ * 1 :=
        mul_le_mul_of_nonneg_left t1 (norm_nonneg _)
    _ = ‖bCoef χ n‖ := mul_one _

/-- The trivial bound on that error: `≤ (h + 1) (x + h) log(x + h)`. -/
theorem first_difference_err_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x h : ℝ} (hx : 1 ≤ x)
    (hh : 0 < h) :
    ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖bCoef χ n‖ ≤ (h + 1) * (x + h) * Real.log (x + h) := by
  have hxh : 1 ≤ x + h := by linarith
  set a := ⌊x⌋₊ with ha
  set c := ⌊x + h⌋₊ with hc
  have hac : a ≤ c := Nat.floor_le_floor (by linarith)
  have hM : 0 ≤ (x + h) * Real.log (x + h) :=
    mul_nonneg (by linarith) (Real.log_nonneg hxh)
  have hb : ∀ n ∈ Ioc a c, ‖bCoef χ n‖ ≤ (x + h) * Real.log (x + h) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le a) hn1))
    have hnxh : (n : ℝ) ≤ x + h := le_trans (by exact_mod_cast hn2) (Nat.floor_le (by linarith))
    refine (norm_bCoef_le χ n).trans ?_
    exact mul_le_mul hnxh (Real.log_le_log (by linarith) hnxh) (Real.log_nonneg hn1')
      (by linarith)
  refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
  rw [Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hac]
  have h1 : (c : ℝ) ≤ x + h := Nat.floor_le (by linarith)
  have h2 : x < (a : ℝ) + 1 := Nat.lt_floor_add_one x
  have h3 : (c : ℝ) - a ≤ h + 1 := by linarith
  calc ((c : ℝ) - a) * ((x + h) * Real.log (x + h))
      ≤ (h + 1) * ((x + h) * Real.log (x + h)) := mul_le_mul_of_nonneg_right h3 hM
    _ = (h + 1) * (x + h) * Real.log (x + h) := by ring

end LeanLab.Linnik.ExplicitFormula
