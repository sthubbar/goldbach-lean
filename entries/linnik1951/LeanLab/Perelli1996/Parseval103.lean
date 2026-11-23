module

public import LeanLab.Perelli1996.Definitions103

/-!
P0083 Perelli 1996, page 481 equation 5.
Finite Fourier expansion before the Weyl and Farey estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Perelli1996.Parseval103
open Finset Real Polynomial MeasureTheory
open scoped ComplexConjugate
noncomputable section

/-- Conjugation reverses the phase of the exponential kernel. -/
theorem conj_e (x : ℝ) : conj (Kernel.e x) = Kernel.e (-x) := by
  unfold Kernel.e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- Addition of phases multiplies their exponential kernels. -/
theorem e_add (x y : ℝ) : Kernel.e (x + y) = Kernel.e x * Kernel.e y := by
  unfold Kernel.e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The finite Fourier quadratic identity on any subset of the unit interval. -/
theorem quadratic_identity (s : Set ℝ) (hs : s ⊆ Set.Icc 0 1)
    (f : ℝ → ℂ) (hf : Continuous f) (v : Finset ℕ) (m : ℕ → ℝ) :
    (∫ ξ in s, f ξ * (∫ α in s, conj (f α) *
      ∑ n ∈ v, Kernel.e (m n * (α - ξ)))) =
      ∑ n ∈ v, ((‖∫ α in s, f α * Kernel.e (-m n * α)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  let z (n : ℕ) := ∫ α in s, f α * Kernel.e (-m n * α)
  have hphase (n : ℕ) (α ξ : ℝ) :
      Kernel.e (m n * (α - ξ)) = Kernel.e (-m n * ξ) * conj (Kernel.e (-m n * α)) := by
    rw [conj_e, ← e_add]
    congr 1
    ring
  have hint (n : ℕ) : IntegrableOn (fun α => f α * Kernel.e (-m n * α)) s := by
    apply Continuous.integrableOn_Icc _ |>.mono_set hs
    unfold Kernel.e
    fun_prop
  have hinner (ξ : ℝ) : (∫ α in s, conj (f α) *
      ∑ n ∈ v, Kernel.e (m n * (α - ξ))) =
      ∑ n ∈ v, Kernel.e (-m n * ξ) * conj (z n) := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      simp_rw [hphase]
      have heq (α : ℝ) : conj (f α) *
          (Kernel.e (-m n * ξ) * conj (Kernel.e (-m n * α))) =
          Kernel.e (-m n * ξ) * conj (f α * Kernel.e (-m n * α)) := by
        rw [map_mul]
        ring
      simp_rw [heq]
      rw [integral_const_mul, integral_conj]
    · intro n hn
      apply Continuous.integrableOn_Icc _ |>.mono_set hs
      unfold Kernel.e
      fun_prop
  simp_rw [hinner, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    have heq (ξ : ℝ) : f ξ * (Kernel.e (-m n * ξ) * conj (z n)) =
      (f ξ * Kernel.e (-m n * ξ)) * conj (z n) := by ring
    simp_rw [heq]
    rw [integral_mul_const]
    simpa only [z, Complex.normSq_eq_norm_sq] using Complex.mul_conj (z n)
  · intro n hn
    apply Continuous.integrableOn_Icc _ |>.mono_set hs
    unfold Kernel.e
    fun_prop

/-- A uniform weighted kernel moment controls the finite Fourier mean square. -/
theorem quadratic_le (s : Set ℝ) (hs : s ⊆ Set.Icc 0 1) (hms : MeasurableSet s)
    (f : ℝ → ℂ) (hf : Continuous f) (v : Finset ℕ) (m : ℕ → ℝ)
    (U : ℝ) (hU : 0 ≤ U)
    (hbound : ∀ ξ ∈ s, (∫ α in s, ‖f α‖ *
      ‖∑ n ∈ v, Kernel.e (m n * (α - ξ))‖) ≤ U) :
    ∑ n ∈ v, ‖∫ α in s, f α * Kernel.e (-m n * α)‖ ^ 2 ≤
      (∫ ξ in s, ‖f ξ‖) * U := by
  have hid := quadratic_identity s hs f hf v m
  have hnorm : ‖∑ n ∈ v, ((‖∫ α in s, f α * Kernel.e (-m n * α)‖ ^ 2 : ℝ) : ℂ)‖ =
      ∑ n ∈ v, ‖∫ α in s, f α * Kernel.e (-m n * α)‖ ^ 2 := by
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [← hnorm, ← hid]
  have hi : IntegrableOn (fun ξ => ‖f ξ‖ * U) s :=
    (hf.norm.mul continuous_const).integrableOn_Icc.mono_set hs
  calc
    _ ≤ ∫ ξ in s, ‖f ξ‖ * U := by
      apply norm_integral_le_of_norm_le hi
      apply (ae_restrict_iff' hms).mpr
      filter_upwards [] with ξ hξ
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ ∫ α in s, ‖conj (f α) * ∑ n ∈ v, Kernel.e (m n * (α - ξ))‖ :=
          norm_integral_le_integral_norm _
        _ = ∫ α in s, ‖f α‖ * ‖∑ n ∈ v, Kernel.e (m n * (α - ξ))‖ := by
          simp only [norm_mul, RCLike.norm_conj]
        _ ≤ U := hbound ξ hξ
    _ = _ := integral_mul_const _ _
/-- Integral orthogonality of integer exponential phases on one period. -/
theorem integral_e_int (z : ℤ) :
    (∫ α in Set.Icc (0 : ℝ) 1, Kernel.e ((z : ℝ) * α)) =
      if z = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  by_cases hz : z = 0
  · simp [hz, Kernel.e]
  · rw [if_neg hz]
    have heq : (fun α : ℝ => Kernel.e ((z : ℝ) * α)) =
        fun α : ℝ => Complex.exp (((z : ℂ) * (2 * Real.pi * Complex.I)) * α) := by
      funext α
      unfold Kernel.e
      congr 1
      push_cast
      ring
    rw [heq, integral_exp_mul_complex]
    · simp [Complex.exp_int_mul_two_pi_mul_I]
    · apply mul_ne_zero
      · exact_mod_cast hz
      · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

/-- Parseval for a finite sum with real coefficients and distinct natural frequencies. -/
theorem integral_norm_sum_sq (v : Finset ℕ) (w : ℕ → ℝ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ‖∑ n ∈ v, (w n : ℂ) * Kernel.e ((n : ℝ) * α)‖ ^ 2) = ∑ n ∈ v, w n ^ 2 := by
  classical
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have heq (α : ℝ) :
      ((‖∑ n ∈ v, (w n : ℂ) * Kernel.e ((n : ℝ) * α)‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ v, ∑ q ∈ v, ((w p * w q : ℝ) : ℂ) * Kernel.e ((((p : ℤ) - q : ℤ) : ℝ) * α) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [map_sum, map_mul, Complex.conj_ofReal, conj_e]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [Complex.ofReal_mul]
    have hphase : Kernel.e ((((p : ℤ) - q : ℤ) : ℝ) * α) =
        Kernel.e ((p : ℝ) * α) * Kernel.e (-((q : ℝ) * α)) := by
      rw [← e_add]
      congr 1
      push_cast
      ring
    rw [hphase]
    ring
  simp_rw [heq]
  have hint (p q : ℕ) : IntegrableOn (fun α : ℝ =>
      ((w p * w q : ℝ) : ℂ) * Kernel.e ((((p : ℤ) - q : ℤ) : ℝ) * α)) (Set.Icc 0 1) := by
    apply Continuous.integrableOn_Icc
    unfold Kernel.e
    fun_prop
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hint p q))]
  simp_rw [integral_finsetSum _ (fun q _ => hint _ q), integral_const_mul, integral_e_int]
  simp only [sub_eq_zero, Int.natCast_inj, mul_ite, mul_one, mul_zero]
  simp [Complex.ofReal_sum, Complex.ofReal_pow, pow_two]

/-- The prime sum second moment from finite orthogonality and Chebyshev's bound. -/
theorem prime_second_moment (M : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1, ‖Decomp88.primeSum M α‖ ^ 2) ≤
      (Real.log 4 + 4) * M * Real.log (M + 1) := by
  open scoped ArithmeticFunction.vonMangoldt in
  have hid := integral_norm_sum_sq (range (M + 1)) (fun n => Λ n)
  change (∫ α in Set.Icc (0 : ℝ) 1,
    ‖∑ n ∈ range (M + 1), (ArithmeticFunction.vonMangoldt n : ℂ) * Kernel.e ((n : ℝ) * α)‖ ^ 2) ≤ _
  rw [hid]
  have hlog : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M; linarith)
  have hpsi : (∑ n ∈ range (M + 1), ArithmeticFunction.vonMangoldt n) = Chebyshev.psi M := by
    have hset : range (M + 1) = Icc 0 M := by ext n; simp
    rw [hset, Chebyshev.psi_eq_sum_Icc]
    simp
  calc
    _ ≤ ∑ n ∈ range (M + 1), ArithmeticFunction.vonMangoldt n * Real.log (M + 1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnM : n ≤ M := by have := Finset.mem_range.mp hn; omega
      by_cases hn0 : n = 0
      · simp [hn0]
      have hlogn : Real.log (n : ℝ) ≤ Real.log (M + 1) :=
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) (by exact_mod_cast Nat.le_succ_of_le hnM)
      have hv := ArithmeticFunction.vonMangoldt_le_log (n := n)
      have hnnon := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      nlinarith
    _ = Chebyshev.psi M * Real.log (M + 1) := by rw [← Finset.sum_mul, hpsi]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg M)) hlog

/-- The full prime second moment has the N log N scale for every fixed cutoff c. -/
theorem prime_second_moment_scaled (c : ℝ) (hc : 0 < c) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      (∫ α in Set.Icc (0 : ℝ) 1, ‖Decomp88.primeSum ⌊c * N⌋₊ α‖ ^ 2) ≤
        C * N * Real.log N := by
  let C := (Real.log 4 + 4) * c * (Real.log (c + 1) + 1)
  have hcLog : 0 ≤ Real.log (c + 1) := Real.log_nonneg (by linarith)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨C, max 3 (Real.exp 1), by dsimp [C]; positivity, le_max_left _ _, ?_⟩
  intro N hN
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hNL : Real.exp 1 ≤ N := (le_max_right _ _).trans hN
  have hL : 1 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 1) hNL
    simpa using this
  let M := ⌊c * N⌋₊
  have hM : (M : ℝ) ≤ c * N := Nat.floor_le (by positivity)
  have hlogM0 : 0 ≤ Real.log ((M : ℝ) + 1) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M; linarith)
  have hM1 : (M : ℝ) + 1 ≤ (c + 1) * N := by nlinarith
  have hlogM : Real.log ((M : ℝ) + 1) ≤ (Real.log (c + 1) + 1) * Real.log N := by
    calc
      _ ≤ Real.log ((c + 1) * N) := Real.log_le_log (by positivity) hM1
      _ = Real.log (c + 1) + Real.log N := Real.log_mul (by positivity) hN0.ne'
      _ ≤ _ := by nlinarith
  calc
    _ ≤ (Real.log 4 + 4) * M * Real.log ((M : ℝ) + 1) := prime_second_moment M
    _ ≤ (Real.log 4 + 4) * (c * N) * ((Real.log (c + 1) + 1) * Real.log N) := by gcongr
    _ = _ := by dsimp [C]; ring


end
end LeanLab.Perelli1996.Parseval103
