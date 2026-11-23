module

public import LeanLab.KadiriLumley2014.TableRounding

/-!
Kadiri and Lumley 2014, arXiv 1407.7902v1 page 11 Theorem 3.2 and Table 1, page 13 Table 2.
Finite rational domain checks only. These do not verify any zeta zeros.
AI wrote this Lean code, Codex by OpenAI. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.Task259

open Task64

/-- Table 1 lists sigma in hundredths and its three rational density coefficients. -/
def densityTable : List (ℕ × ℚ × ℚ × ℚ) := [
  (90, 5.8494, 0.4659, -179050000000),
  (91, 5.6991, 0.4539, -174440000000),
  (92, 5.5564, 0.4426, -170070000000),
  (93, 5.4206, 0.4318, -165920000000),
  (94, 5.2913, 0.4215, -161960000000),
  (95, 5.1680, 0.4116, -158190000000),
  (96, 5.0503, 0.4023, -154580000000),
  (97, 4.9379, 0.3933, -151140000000),
  (98, 4.8304, 0.3848, -147850000000),
  (99, 4.7274, 0.3766, -144700000000)]

/-- All Table 1 coefficients have the signs and sigma range used by Theorem 2.4. -/
theorem densityTable_domain : ∀ r ∈ densityTable,
    60 < r.1 ∧ r.1 < 100 ∧ 0 < r.2.1 ∧ 0 < r.2.2.1 ∧ r.2.2.2 < 0 := by
  decide +kernel

/-- Every Table 2 sigma has a matching row of the published density coefficient table. -/
theorem tableTwo_density_covered : ∀ r ∈ tableTwo,
    ∃ s ∈ densityTable, s.1 = r.sigmaUnits := by
  decide +kernel

/-- The linear density contribution is positive at the published height H.
The negative intercept cannot be discarded when certifying a printed budget. -/
theorem densityTable_positive_linear_part : ∀ r ∈ densityTable,
    0 < r.2.1 * (30610000000 : ℚ) + r.2.2.2 := by
  decide +kernel

/-- The printed heights lie strictly between the verified low-zero cutoff and H. -/
theorem tableTwo_height_domain : ∀ r ∈ tableTwo,
    (1132491 : ℚ) < r.height ∧ (r.height : ℚ) < 30610000000 := by
  decide +kernel

end LeanLab.KadiriLumley2014.Task259

namespace LeanLab.KadiriLumley2014.Task92
open Task64

/-- Page 13 Table 2 and page 2 equation 2.1. Every printed smoothing
step is positive and lies inside the small-parameter range. -/
theorem table_small_steps : ∀ r ∈ tableTwo,
    (0 : ℚ) < r.deltaQ ∧ r.deltaQ ≤ 0.0001 ∧
      1 / 10 ^ 12 ≤ r.uQ ∧ r.uQ ≤ 0.0001 := by
  decide +kernel

end LeanLab.KadiriLumley2014.Task92
