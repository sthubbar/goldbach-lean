module

public import LeanLab.KadiriLumley2014.PalomarEntry

/-!
Kadiri and Lumley 2014, page 13 Table 2 row 45, Delta = 95381241 from e^45, in a natural
number form, conditional on explicit inputs. An uncertified floating point check found
display 2.64 positive at row 45 from published zero data alone. AI wrote this Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KadiriLumley2014.PalomarKL45
open Real
open LeanLab.KadiriLumley2014.Task64 LeanLab.KadiriLumley2014.Task92

/-- Table 2 row 45 in the form of `kl45_of_row`: for every natural `y > e^45` there is a prime
`p < y` with `95381241 (y - p) < y`. Conditional on Montgomery and Vaughan 1973 Theorem 2,
Dusart 2010 Theorem 5.2 row eta_2 = 0.05, and display 2.64 with the true zero sum at Table 2
row 45. -/
theorem kl45_of_inputs
    (hMV : LeanLab.RamareSaouter2003.Thm4Parts.MVBrunTitchmarsh)
    (hDus : ∀ t : ℝ, 122568683 ≤ t →
      |Chebyshev.theta t - t| < 0.05 * t / Real.log t ^ 2)
    (h45 : let r : PrintedRow := ⟨45, 7, 16280, 797398875, 92, 2494, 95381241⟩
      (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
        tailCoefficient r.deltaQ r.uQ (rowEndpointX r) *
            tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
        (Real.exp r.uQ - 1) * rowEndpointX r *
          (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r))) :
    ∀ y : ℕ, Real.exp 45 < y → ∃ p : ℕ, p.Prime ∧ p < y ∧ 95381241 * (y - p) < y := by
  have hC : CostaEstimate := CostaSplit.costa_of_dusart hDus
  have r45 : KLRow (Real.exp 45) 95381241 := by
    convert (PalomarEntry.row_of_inputs hC hMV
      (r := ⟨45, 7, 16280, 797398875, 92, 2494, 95381241⟩) (by decide +kernel) h45)
      using 1 <;> norm_num [Task64.PrintedRow.threshold, Task64.evenBase]
  exact kl45_of_row r45

end LeanLab.KadiriLumley2014.PalomarKL45
