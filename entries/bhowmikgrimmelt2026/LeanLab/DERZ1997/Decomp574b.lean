module

public import LeanLab.DERZ1997.Decomp1529a
public import LeanLab.PNTPort.BV.Characters
public import LeanLab.PNTPort.BV.Helpers

/-!
Principal-character Euler-factor reductions for the DERZ1997 explicit formula.
The final estimate is conditional on its displayed zeta error premise.
It does not call either sealed explicit-formula leaf.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.DERZ1997.Decomp574b
open Complex Real Set Filter Topology
open LeanLab.DERZ1997.Decomp1529a


/-- Principal-character strip zeros and multiplicities are the zeta data.
The finite Euler factors do not vanish in the positive half-plane.
Auxiliary reduction for Davenport chapter 19 pages 119 to 120.
-/
theorem principal_zero_data574 {q : ℕ} [NeZero q] {ρ : ℂ}
    (hr0 : 0 < ρ.re) (hr1 : ρ.re < 1) :
    (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ = 0 ↔
      riemannZeta ρ = 0) ∧
    LMult (1 : DirichletCharacter ℂ q) ρ = zetaMult ρ := by
  have hρ1 : ρ ≠ 1 := by intro hh; rw [hh] at hr1; norm_num at hr1
  have hh := changeLevel_zero_data193 (Nat.one_dvd q)
    (1 : DirichletCharacter ℂ 1) hr0 hρ1
  simpa only [DirichletCharacter.changeLevel_one, DirichletCharacter.LFunction_modOne_eq,
    LMult, zetaMult] using hh


/-- The finite principal-character zero sum equals the zeta zero sum at every cutoff.
Auxiliary reduction for Davenport chapter 19 pages 119 to 120.
-/
theorem principal_zero_sum574 {q : ℕ} [NeZero q] (x T : ℝ)
    (hfL : (LZeros (1 : DirichletCharacter ℂ q) T).Finite)
    (hfZ : (zetaZeros T).Finite) :
    (∑ ρ ∈ hfL.toFinset, (LMult (1 : DirichletCharacter ℂ q) ρ : ℂ) * (x : ℂ) ^ ρ / ρ) =
      ∑ ρ ∈ hfZ.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  classical
  have hset : LZeros (1 : DirichletCharacter ℂ q) T = zetaZeros T := by
    ext ρ
    constructor
    · intro hρ
      exact ⟨(principal_zero_data574 (q := q) hρ.2.1 hρ.2.2.1).1.mp hρ.1, hρ.2⟩
    · intro hρ
      exact ⟨(principal_zero_data574 (q := q) hρ.2.1 hρ.2.2.1).1.mpr hρ.1, hρ.2⟩
  apply Finset.sum_congr
  · exact Set.Finite.toFinset_inj.mpr hset
  · intro ρ hρ
    obtain ⟨hz, hr0, hr1, ht⟩ := hfZ.mem_toFinset.mp hρ
    rw [(principal_zero_data574 (q := q) hr0 hr1).2]


/-- The principal twisted psi differs from psi by the Euler-factor prime powers only.
The bound reuses the proved bad-prime sum estimate in PNTPort.BV.
Auxiliary reduction for Davenport chapter 19 page 119.
-/
theorem principal_psi_error574 {q : ℕ} [NeZero q] {x : ℝ} (hx : 1 ≤ x) :
    ‖(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (1 : DirichletCharacter ℂ q) (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) -
        (Chebyshev.psi x : ℂ)‖ ≤ Real.log q / Real.log 2 * Real.log x := by
  have he : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (1 : DirichletCharacter ℂ q) (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) =
      LeanLab.PNTPort.BV.psiChi x (1 : DirichletCharacter ℂ q) := by
    unfold LeanLab.PNTPort.BV.psiChi
    rw [show Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ by ext n; simp; omega]
    exact Finset.sum_congr rfl (fun n _ => mul_comm _ _)
  rw [he]
  exact (LeanLab.PNTPort.BV.norm_psiChi_one_sub x).trans
    (LeanLab.PNTPort.BV.psiBad_le hx (NeZero.pos q))




/-- The principal-character explicit formula follows from the matching zeta estimate.
CONDITIONAL ON the displayed zeta error bound. The constant 2002 is derived here.
Auxiliary Euler-factor reduction for Davenport chapter 19 page 120.
-/
theorem principal_error_of_zeta574 {q : ℕ} [NeZero q] {x T : ℝ}
    (hx : 2 ≤ x) (hT : 2 ≤ T)
    (hfL : (LZeros (1 : DirichletCharacter ℂ q) T).Finite)
    (hfZ : (zetaZeros T).Finite)
    (hZ : ‖(Chebyshev.psi x : ℂ) - x +
      ∑ ρ ∈ hfZ.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        1000 * (x * Real.log x ^ 2 / T + Real.log x)) :
    ‖(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (1 : DirichletCharacter ℂ q) (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) - x +
      ∑ ρ ∈ hfL.toFinset, (LMult (1 : DirichletCharacter ℂ q) ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        2002 * (x * Real.log ((q : ℝ) * x) ^ 2 / T + Real.sqrt x +
          Real.log ((q : ℝ) * x) ^ 2) := by
  rw [principal_zero_sum574 x T hfL hfZ]
  let P : ℂ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
    (1 : DirichletCharacter ℂ q) (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)
  let Z : ℂ := ∑ ρ ∈ hfZ.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ
  let L : ℝ := Real.log ((q : ℝ) * x)
  let A : ℝ := x * L ^ 2 / T
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hqx : 2 ≤ (q : ℝ) * x := by nlinarith
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hqx
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogq : Real.log q ≤ L := Real.log_le_log hq0 (by nlinarith)
  have hlogx : Real.log x ≤ L := Real.log_le_log hx0 (by nlinarith)
  have hlog20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinv : 1 / Real.log 2 ≤ (2 : ℝ) := (div_le_iff₀ hlog20).mpr (by linarith [Real.log_two_gt_d9])
  have hmul : Real.log q * Real.log x ≤ L ^ 2 := by
    simpa only [pow_two] using mul_le_mul hlogq hlogx hlogx0 hL0
  have hEuler : Real.log q / Real.log 2 * Real.log x ≤ 2 * L ^ 2 := by
    calc
      _ = (Real.log q * Real.log x) / Real.log 2 := by ring
      _ ≤ L ^ 2 / Real.log 2 := div_le_div_of_nonneg_right hmul hlog20.le
      _ = (1 / Real.log 2) * L ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hinv (sq_nonneg L)
  have hlin : Real.log x ≤ 2 * L ^ 2 := by
    have := Real.log_two_gt_d9
    nlinarith
  have hmain : x * Real.log x ^ 2 / T ≤ A := by
    dsimp [A]
    gcongr
  have hpsi : ‖P - (Chebyshev.psi x : ℂ)‖ ≤ 2 * L ^ 2 :=
    (principal_psi_error574 (q := q) (by linarith : 1 ≤ x)).trans hEuler
  have hz : ‖(Chebyshev.psi x : ℂ) - x + Z‖ ≤ 1000 * (A + 2 * L ^ 2) :=
    hZ.trans (by nlinarith)
  have htri : ‖P - x + Z‖ ≤ ‖P - (Chebyshev.psi x : ℂ)‖ +
      ‖(Chebyshev.psi x : ℂ) - x + Z‖ := by
    have he : P - x + Z = (P - (Chebyshev.psi x : ℂ)) + ((Chebyshev.psi x : ℂ) - x + Z) := by ring
    rw [he]
    exact norm_add_le _ _
  change ‖P - x + Z‖ ≤ 2002 * (A + Real.sqrt x + L ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  nlinarith [Real.sqrt_nonneg x]


end LeanLab.DERZ1997.Decomp574b
