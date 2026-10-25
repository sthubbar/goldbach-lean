module

public import LeanLab.DensityGoldbach.U1502Final

/-!
Unit U-1506, run 20261025T0416Z-19415. Vacuity test for `AlsetriShao12`.
AI-written Lean code, Claude, 2026-10-25. Binary Goldbach is OPEN.

The hypotheses of `AlsetriShao12` hold for `A = P` and `η = 3/4`: every reduced class
`b mod W` has relative lower density exactly `1`, by Dirichlet's theorem in Mathlib.
-/

@[expose] public section

open Finset Filter
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach.U1506

theorem lowerDensityRes_P (W b : ℕ) (hW : 0 < W) (hb : Nat.Coprime b W) :
    lowerDensityRes P b W = 1 := by
  haveI : NeZero W := ⟨hW.ne'⟩
  have hu : IsUnit ((b : ℕ) : ZMod W) := (ZMod.isUnit_iff_coprime b W).2 hb
  obtain ⟨p, -, hp, hpb⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu 0
  have hmod : p % W = b % W := (ZMod.natCast_eq_natCast_iff' p b W).1 hpb
  unfold lowerDensityRes
  have hev : ∀ᶠ N : ℕ in atTop,
      ((#{n ∈ Icc 1 N | n ∈ P ∧ n.Prime ∧ n % W = b % W} : ℝ) /
        #{n ∈ Icc 1 N | n.Prime ∧ n % W = b % W}) = 1 := by
    filter_upwards [eventually_ge_atTop p] with N hN
    have hset : ({n ∈ Icc 1 N | n ∈ P ∧ n.Prime ∧ n % W = b % W} : Finset ℕ) =
        {n ∈ Icc 1 N | n.Prime ∧ n % W = b % W} := by
      ext n; simp only [mem_filter, P, Set.mem_setOf_eq]; tauto
    have hpos : (0 : ℝ) < #{n ∈ Icc 1 N | n.Prime ∧ n % W = b % W} := by
      have : p ∈ ({n ∈ Icc 1 N | n.Prime ∧ n % W = b % W} : Finset ℕ) := by
        simp only [mem_filter, mem_Icc]; exact ⟨⟨hp.one_lt.le, hN⟩, hp, hmod⟩
      exact_mod_cast card_pos.2 ⟨p, this⟩
    rw [hset]; exact div_self hpos.ne'
  rw [liminf_congr hev, liminf_const]

/-- The hypotheses of `AlsetriShao12` are satisfiable: `A = P`, `η = 3/4`. -/
theorem hyp_satisfiable : P ⊆ P ∧ (1 / 2 : ℝ) < 3 / 4 ∧
    ∀ W b : ℕ, 0 < W → Nat.Coprime b W → (3 / 4 : ℝ) ≤ lowerDensityRes P b W :=
  ⟨le_rfl, by norm_num, fun W b hW hb => by rw [lowerDensityRes_P W b hW hb]; norm_num⟩

/-- Instance of the proved statement at `A = P`, `η = 3/4`: almost all even numbers are sums of
two primes, the classical almost-all binary Goldbach theorem, not binary Goldbach. -/
theorem instance_P : Tendsto (fun X : ℕ =>
    (#{n ∈ Icc 1 X | Even n ∧ ¬ ∃ a ∈ P, ∃ b ∈ P, a + b = n} : ℝ) / X) atTop (nhds 0) :=
  LeanLab.DensityGoldbach.U1502.alsetriShao_1_2 P le_rfl (3 / 4) (by norm_num)
    (fun W b hW hb => hyp_satisfiable.2.2 W b hW hb)

/-- Independent type check: the U-1502 theorem has exactly the Statements.lean type. -/
example : LeanLab.DensityGoldbach.AlsetriShao12 := LeanLab.DensityGoldbach.U1502.alsetriShao_1_2

end LeanLab.DensityGoldbach.U1506

