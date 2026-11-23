module

public import LeanLab.Linnik1951.Data357
public import LeanLab.Linnik1951.Decomp357i
public import LeanLab.Linnik1951.Asymptotics357
public import LeanLab.HeathBrown1985.DivisorEps

/-!
P0093 page 168 equation 10.5. The independent divisor growth and real power steps.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- LEAF. P0093 page 168 last inequality in equation 10.5. The standard
small power bound for the divisor count used there, with exponent three
hundredths. This is independent of the singular series and its cutoff. -/
theorem small_power_divisors376 :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 2 ≤ n →
      (n.divisors.card : ℝ) ≤ D * (n : ℝ) ^ (3 / 100 : ℝ) := by
  obtain ⟨D, hD, hd⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow 100 (by norm_num)
  refine ⟨D, hD, ?_⟩
  intro n hn
  apply (hd n (by omega)).trans
  apply mul_le_mul_of_nonneg_left _ hD.le
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)

/-- P0093 page 168 equation 10.5. Multiplying the divisor loss with the
tail saving gives exponent negative two hundredths, which is stronger than
the negative one hundredth requested by singular_tail357. -/
theorem combine_tail_powers376 (x : ℝ) (hx : 1 ≤ x) :
    x ^ (3 / 100 : ℝ) * x ^ (-(1 / 20 : ℝ)) ≤ x ^ (-(1 / 100 : ℝ)) := by
  rw [← Real.rpow_add (by linarith : 0 < x)]
  exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

end LeanLab.Linnik1951
