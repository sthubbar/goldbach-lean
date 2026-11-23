module

public import LeanLab.Linnik1951.Decomp280a

/-!
P0093 Sections 3 to 10. Analytic decomposition of error_bound111.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951

/-- P0093 page 159, the character prime sum preceding equation 5.1. -/
noncomputable def characterPrime280 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (α : ℝ) : ℂ :=
  ∑' p : Nat.Primes, χ (p : ℕ) * (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
    Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)

/-- CITED. P0093 page 159 equation 5.2 with equal nonprincipal characters
and tau equal to N to the one seventh. This is the Mellin estimate used below. -/
def MellinBound280 : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ ((N : ℝ) ^ (1 / 7 : ℝ)) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        (∫ α in -(1 / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))..(1 / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
          ‖characterPrime280 χ N α‖ ^ 2) ≤
            B * (N : ℝ) / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) * Real.log N ^ 13

/-- P0093 page 165 Section 8. Major arcs with Q equal to N to the one tenth
and tau equal to N to the one seventh, clipped to the unit interval. -/
noncomputable def majorArcs280 (N : ℕ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 1 ∧ ∃ r : ℚ, (r.den : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
    |α - r| ≤ 1 / ((r.den : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))}

/-- P0093 pages 162 and 167. Exceptional minor points where T is large. -/
noncomputable def exceptionalArcs280 (N : ℕ) (η : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc 0 1 ∧ α ∉ majorArcs280 N ∧
    (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖}

/-- P0093 page 167 before equation 10.1. The remaining minor points. -/
noncomputable def goodMinorArcs280 (N : ℕ) (η : ℝ) : Set ℝ :=
  Set.Icc 0 1 \ (majorArcs280 N ∪ exceptionalArcs280 N η)

/-- P0093 pages 154 and 167 equations 2.2 and 10.2. Real contribution of a
measurable arc set, including the factor e from exponential damping. -/
noncomputable def arcContribution280 (k N : ℕ) (s : Set ℝ) : ℝ :=
  Real.exp 1 * (∫ α in s, primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
    Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)).re


/-- LEAF. P0093 page 167 immediately before equation 10.1.
Outside the exceptional set the power series is at most its chosen threshold. -/
theorem good_minor_power_bound280 (N : ℕ) (η α : ℝ)
    (hα : α ∈ goodMinorArcs280 N η) :
    ‖powerFourier111 N α‖ ≤ (1 - η) * ‖powerFourier111 N 0‖ := by
  exact le_of_not_gt (fun h => hα.2 (Or.inr ⟨hα.1, fun hm => hα.2 (Or.inl hm), h⟩))

/-- LEAF. P0093 page 167 equation 10.1 with the factor e from equation 2.2
absorbed in an absolute constant. Lemma 3 and the bound on T outside its
exceptional set give geometric decay in k minus two. -/
theorem minor_error280 (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hT : ∀ N : ℕ, ∀ α : ℝ, α ∈ goodMinorArcs280 N η →
      ‖powerFourier111 N α‖ ≤ (1 - η) * ‖powerFourier111 N 0‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 < N →
        |arcContribution280 k N (goodMinorArcs280 N η)| ≤
          C * scale111 k N * (1 - η) ^ (k - 2) := by
  exact minor_error_proved357_up111 η hη hη1 hT

/-- LEAF. P0093 page 154 equation 2.2 and page 167 equation 10.2.
Fourier orthogonality counts the representations and the disjoint measurable
partition of the unit interval splits its integral into three pieces. -/
theorem circle_partition280 (k N : ℕ) (hN : 1 ≤ N) (η : ℝ) :
    (representationCount111 k N : ℝ) =
      arcContribution280 k N (majorArcs280 N) +
      arcContribution280 k N (exceptionalArcs280 N η) +
      arcContribution280 k N (goodMinorArcs280 N η) := by
  exact circle_partition_proved435_up111 k N hN η

end LeanLab.Linnik1951
