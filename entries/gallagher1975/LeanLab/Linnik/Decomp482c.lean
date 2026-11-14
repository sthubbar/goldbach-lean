module

public import LeanLab.Linnik.Decomp486b

/-!
Gallagher 1975 pp.128 through 132 displays 3 through 17.
The arithmetic major arc reduction is separated from the character energy estimate.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp482c

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (excSet)
open LeanLab.Linnik.U7204 (Sg)

/-- ASSEMBLY. CONDITIONAL ON the two Decomp486b arithmetic cases.
Gallagher 1975 p.131 display 13 and pp.131 and 132 displays 15 through 17.
From the rational arc character expansion derive the frequency error in terms
of corrected character energy and the exceptional conductor coefficient.
The energy decay estimate in display 14 is not assumed here.
All frequencies share the supplied exceptional character and zero. -/
theorem major_arc_energy_bound
    (hExpansion : ∃ C : ℝ, 0 < C ∧ ∀ N q : ℕ, ∀ [NeZero q], ∀ a : ℕ,
      Nat.Coprime a q → a ≤ q → ∀ β : ℝ,
        ‖Sg N ((a : ℝ) / q + β) - (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ ≤
          C * Real.sqrt q * Real.log (2 * q)) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) := by
  exact LeanLab.Linnik.Decomp486b.major_arc_energy_bound_split hExpansion

/-- Gallagher 1975 p.131 combining displays 13 and 14.
The quadratic normalized energy has the same exponential decay. -/
theorem quadratic_energy_decay {E C x : ℝ} (hE0 : 0 ≤ E) (hC : 0 ≤ C)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hE : E ≤ C * x) :
    (1 + E) * E ≤ C * (1 + C) * x := by
  have hEC : E ≤ C := hE.trans (mul_le_of_le_one_right hC hx1)
  calc
    (1 + E) * E ≤ (1 + C) * (C * x) :=
      mul_le_mul (by linarith) hE hE0 (by linarith)
    _ = C * (1 + C) * x := by ring

/-- Gallagher 1975 p.131 combining displays 13 and 14 with display 17.
The exact Theorem 3 conclusion follows from the two explicit uniform bounds.
CONDITIONAL ON the supplied energy decay and arithmetic major arc bound. -/
theorem gallagher_theorem3_of_energy_bounds
    (hDecay : ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ, ∃ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) ∧
          normalizedEnergy N θ r γ ≤ C * Real.exp (-c / θ))
    (hMajor : ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n)) :
    ∃ c K θ₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ) ∧
          ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                Real.exp (-c / θ) + exceptionalWeight r n) := by
  obtain ⟨c, C, θb, hc, hC, hθb, hθb1, hdecay⟩ := hDecay
  obtain ⟨K, θa, hK, hθa, hθa1, hmajor⟩ := hMajor
  let D : ℝ := max 1 (C * (1 + C))
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDq : C * (1 + C) ≤ D := le_max_right _ _
  refine ⟨c, K * D, min θa θb, hc, mul_pos hK (lt_of_lt_of_le zero_lt_one hD1),
    lt_min hθa hθb, (min_le_left _ _).trans hθa1, ?_⟩
  intro θ hθ hθlim
  obtain ⟨Nb, hb⟩ := hdecay θ hθ (hθlim.trans (min_le_right _ _))
  obtain ⟨Na, ha⟩ := hmajor θ hθ (hθlim.trans (min_le_left _ _))
  refine ⟨max 2 (max Na Nb), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := (le_max_left Na Nb).trans ((le_max_right 2 _).trans hN)
  have hNb : Nb ≤ N := (le_max_right Na Nb).trans ((le_max_right 2 _).trans hN)
  obtain ⟨r, γ, hr, hE⟩ := hb N hNb
  refine ⟨r, ?_, ?_⟩
  · rcases hr with hr | ⟨x, hx, hr, hrP, hrest⟩
    · exact Or.inl hr
    · exact Or.inr ⟨x, hx, hr, hrP⟩
  · intro n hn
    have hraw := ha N hNa r γ hr n hn
    have hexp0 : 0 ≤ Real.exp (-c / θ) := (Real.exp_pos _).le
    have hexp1 : Real.exp (-c / θ) ≤ 1 := Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hθ.le)
    have hquad := quadratic_energy_decay (normalizedEnergy_nonneg hN2 θ r γ) hC.le
      hexp0 hexp1 hE
    have hlogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have hP1 : 1 ≤ (N : ℝ) ^ θ := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) hθ.le
    have hd : 0 ≤ Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card :=
      mul_nonneg (div_nonneg (Real.log_nonneg hP1) (by positivity)) (by positivity)
    have hexc : 0 ≤ exceptionalWeight r n := by unfold exceptionalWeight; positivity
    have hsum :
        Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
          (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ + exceptionalWeight r n ≤
        D * (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
          Real.exp (-c / θ) + exceptionalWeight r n) := by
      have hdx := mul_le_mul_of_nonneg_right hDq hexp0
      have hdd := mul_le_mul_of_nonneg_right hD1 hd
      have hde := mul_le_mul_of_nonneg_right hD1 hexc
      linarith only [hquad, hdx, hdd, hde]
    have hweight : 0 ≤ K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n := by
      unfold totientWeight
      positivity
    exact hraw.trans (by
      calc
        _ ≤ K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
            (D * (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
              Real.exp (-c / θ) + exceptionalWeight r n)) :=
          mul_le_mul_of_nonneg_left hsum hweight
        _ = _ := by ring)


/-- Gallagher 1975 p.127 Theorem 3 exactly, CONDITIONAL ON the two analytic leaves.
The exponential term and the common exceptional conductor are retained. -/
theorem gallagher_theorem3_split :
    ∃ c K θ₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ) ∧
          ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                Real.exp (-c / θ) + exceptionalWeight r n) := by
  exact gallagher_theorem3_of_energy_bounds corrected_energy_decay
    (major_arc_energy_bound character_expansion)

end LeanLab.Linnik.Decomp482c


