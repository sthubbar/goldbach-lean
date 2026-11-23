module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
An elementary convergence criterion for the tail reduction in P0014 page 41.
A polynomial shell count suffices for convergence, without the sharp density bound.
The analytic envelope and zero count remain explicit inputs.
AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section


namespace LeanLab.HelfgottMajor.Decomp454c
open Real

/-- A polynomial shell count makes an exponentially weighted series summable.
Derived convergence step for P0014 page 38 display 4.26 and page 41 display 4.33.
CONDITIONAL ON hcount, the shell count budget. No quantitative tail estimate is asserted.
-/
theorem summable_exp_of_shell_count {ι : Type*} (height : ι → ℕ) (w : ι → ℝ)
    (C a : ℝ) (ha : 0 < a) (hw : ∀ i, 0 ≤ w i)
    (hfinite : ∀ n, {i | height i = n}.Finite)
    (hcount : ∀ n : ℕ, (∑' i : {i // height i = n}, w i.val) ≤
      C * ((n : ℝ) + 1) ^ 2) :
    Summable (fun i => w i * exp (-a * (height i : ℝ))) := by
  have hs0 := summable_pow_mul_exp_neg_nat_mul 0 ha
  have hs1 := summable_pow_mul_exp_neg_nat_mul 1 ha
  have hs2 := summable_pow_mul_exp_neg_nat_mul 2 ha
  have hmajor : Summable (fun n : ℕ => C * ((n : ℝ) + 1) ^ 2 * exp (-a * n)) := by
    convert ((hs2.add (hs1.mul_left 2)).add hs0).mul_left C using 1
    ext n
    simp only [pow_zero, pow_one]
    ring
  have hnonneg : ∀ i, 0 ≤ w i * exp (-a * (height i : ℝ)) := by
    intro i
    exact mul_nonneg (hw i) (exp_pos _).le
  apply (summable_partition hnonneg (s := fun n => {i | height i = n})
    (fun i => ⟨height i, rfl, fun n hn => hn.symm⟩)).mpr
  have hinner (n : ℕ) : Summable (fun i : {i // height i = n} =>
      w i.val * exp (-a * (height i.val : ℝ))) := by
    let : Fintype {i // height i = n} := (hfinite n).fintype
    exact (hasSum_fintype _).summable
  refine ⟨hinner, ?_⟩
  apply Summable.of_nonneg_of_le
    (fun n => tsum_nonneg (fun i : {i // height i = n} => hnonneg i.val)) _ hmajor
  intro n
  have heq : (fun i : {i // height i = n} =>
      w i.val * exp (-a * (height i.val : ℝ))) =
        (fun i : {i // height i = n} => w i.val * exp (-a * (n : ℝ))) := by
    funext i
    rw [i.property]
  rw [heq, tsum_mul_right]
  exact mul_le_mul_of_nonneg_right (hcount n) (exp_pos _).le

/-- A real nonnegative height can be grouped into unit shells without losing convergence.
Derived convergence step for P0014 page 38 display 4.26 and page 41 display 4.33.
CONDITIONAL ON hcount, the polynomial multiplicity budget in each unit shell.
-/
theorem summable_exp_real_of_shell_count {ι : Type*} (height w : ι → ℝ)
    (C a : ℝ) (ha : 0 < a) (hw : ∀ i, 0 ≤ w i) (hh : ∀ i, 0 ≤ height i)
    (hfinite : ∀ n, {i | ⌊height i⌋₊ = n}.Finite)
    (hcount : ∀ n : ℕ, (∑' i : {i // ⌊height i⌋₊ = n}, w i.val) ≤
      C * ((n : ℝ) + 1) ^ 2) :
    Summable (fun i => w i * exp (-a * height i)) := by
  have hs := summable_exp_of_shell_count (fun i => ⌊height i⌋₊) w C a ha hw hfinite hcount
  apply hs.of_norm_bounded
  intro i
  rw [Real.norm_of_nonneg (mul_nonneg (hw i) (exp_pos _).le)]
  apply mul_le_mul_of_nonneg_left _ (hw i)
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (Nat.floor_le (hh i)) (by linarith)

/-- A mass dominated by exponential decay is summable under a polynomial shell count.
This isolates the convergence half of P0014 page 41 displays 4.33 to 4.35.
CONDITIONAL ON hcount and hdecay. Neither analytic input is asserted here.
-/
theorem summable_mass_of_shell_count {ι : Type*} (height w mass : ι → ℝ)
    (C a B : ℝ) (ha : 0 < a) (hw : ∀ i, 0 ≤ w i) (hh : ∀ i, 0 ≤ height i)
    (hm : ∀ i, 0 ≤ mass i)
    (hfinite : ∀ n, {i | ⌊height i⌋₊ = n}.Finite)
    (hcount : ∀ n : ℕ, (∑' i : {i // ⌊height i⌋₊ = n}, w i.val) ≤
      C * ((n : ℝ) + 1) ^ 2)
    (hdecay : ∀ i, mass i ≤ B * (w i * exp (-a * height i))) :
    Summable mass := by
  apply ((summable_exp_real_of_shell_count height w C a ha hw hh hfinite hcount).mul_left B).of_norm_bounded
  intro i
  rw [Real.norm_of_nonneg (hm i)]
  exact hdecay i

end LeanLab.HelfgottMajor.Decomp454c
