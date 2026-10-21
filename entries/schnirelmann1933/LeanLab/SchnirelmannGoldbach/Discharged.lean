module

public import LeanLab.SchnirelmannGoldbach.Unconditional

/-!
The five roadmap statements of Statements.lean, each PROVED from the lab's own results, with no placeholder proofs:
S1u_holds in S1/Final.lean, a port of the PNT+ Selberg sieve by Arend Mellendijk, Apache 2.0;
S2_holds in S2.lean; S3_of_S1u_S2 in S3.lean; S4_of_S3 in FromDensity.lean;
schnirelmann_bounded_primes in Unconditional.lean.
Unit U-1052, PC run 20261019T1003Z-30522. Before this file the roadmap kept these five as
unproved theorems although every one was already proved under another name since 2026-10-16.
AI-written Lean code, Claude. Checked only by the Lean kernel. Known mathematics, Schnirelmann
1930, Nathanson GTM 164 chapter 7. Binary Goldbach is OPEN.
-/

@[expose] public section

open Finset

namespace LeanLab.SchnirelmannGoldbach

/-- S1, the sieve upper bound `r n ≤ C n / log² n · ∏_{p ∣ n} (1 + 1/p)` for `n ≥ 3`: `S1u` at `N = n`. -/
theorem S1_sieve_upper : S1_sieve_upper_stmt := by
  obtain ⟨C, hC⟩ := S1u_holds
  exact ⟨C, fun n hn => hC n hn n (mem_Icc.mpr ⟨by omega, le_rfl⟩)⟩

/-- S2, the mean square of the singular product is linear. -/
theorem S2_mean_square : S2_mean_square_stmt := S2_holds

/-- S3, Goldbach sums have positive lower density. -/
theorem S3_positive_lower_density : S3_positive_lower_density_stmt :=
  S3_of_S1u_S2 S1u_holds S2_holds

/-- S4, `{0, 1} ∪ G` has positive Schnirelmann density. -/
theorem S4_schnirelmann_pos : S4_schnirelmann_pos_stmt :=
  S4_of_S3 S3_positive_lower_density

/-- Schnirelmann 1930: every `n ≥ 2` is a sum of at most `H` primes. -/
theorem schnirelmann_goldbach : schnirelmann_goldbach_stmt := schnirelmann_bounded_primes

/-- Vacuity test: the statement of S1 is not empty at `n = 4`, where `r 4 = 1` from `2 + 2`. -/
example : r 4 = 1 := by decide

end LeanLab.SchnirelmannGoldbach

