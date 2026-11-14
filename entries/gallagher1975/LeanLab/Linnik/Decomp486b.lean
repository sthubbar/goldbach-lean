module

public import LeanLab.Linnik.Decomp482b
public import LeanLab.Linnik.MajorArcEnergy.Display1517

/-!
Gallagher 1975 p.131 display 13 and pp.131 and 132 displays 15 through 17.
Split the arithmetic major arc estimate at conductor zero.
No character energy decay is assumed in either leaf.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp486b

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (excSet)
open LeanLab.Linnik.U7204 (Sg)

/-- Gallagher 1975 p.128 Schwarz inequality for the arc integral.
The additive character has norm one, so the coefficient is at most the
product of the two square root mean squares on the same compact window. -/
theorem arc_pair_integral_le (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) (a b : ℝ)
    (n : ℝ) :
    ‖∫ t in Set.Icc a b, star (f t) * g t * LeanLab.PNTPort.LargeSieve.e (n * t)‖ ≤
      Real.sqrt (∫ t in Set.Icc a b, ‖f t‖ ^ 2) *
        Real.sqrt (∫ t in Set.Icc a b, ‖g t‖ ^ 2) := by
  let μ := volume.restrict (Set.Icc a b)
  have hfMem : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
      ((hf.norm.pow 2).integrableOn_Icc)
  have hgMem : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
      ((hg.norm.pow 2).integrableOn_Icc)
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by simpa using hfMem) (by simpa using hgMem)
  have hcs : (∫ t in Set.Icc a b, ‖f t‖ * ‖g t‖) ≤
      Real.sqrt (∫ t in Set.Icc a b, ‖f t‖ ^ 2) *
        Real.sqrt (∫ t in Set.Icc a b, ‖g t‖ ^ 2) := by
    simpa only [μ, Real.rpow_two, ← Real.sqrt_eq_rpow] using hholder
  calc
    _ ≤ ∫ t in Set.Icc a b, ‖star (f t) * g t * LeanLab.PNTPort.LargeSieve.e (n * t)‖ := norm_integral_le_integral_norm _
    _ = ∫ t in Set.Icc a b, ‖f t‖ * ‖g t‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by simp only [norm_mul, norm_star, LeanLab.PNTPort.LargeSieve.norm_e, mul_one]
    _ ≤ _ := hcs
/-- Gallagher 1975 p.128 Schwarz inequality with the common beta window.
If the arc radius is at most R, its pair integral is bounded by the two
mean square norms on the common window of radius R. -/
theorem arc_pair_integral_le_common_window (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (δ R n : ℝ) (hδR : δ ≤ R) :
    ‖∫ t in Set.Icc (-δ) δ,
      star (f t) * g t * LeanLab.PNTPort.LargeSieve.e (n * t)‖ ≤
      Real.sqrt (∫ t in Set.Icc (-R) R, ‖f t‖ ^ 2) *
        Real.sqrt (∫ t in Set.Icc (-R) R, ‖g t‖ ^ 2) := by
  have hsub : Set.Icc (-δ) δ ⊆ Set.Icc (-R) R := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hm (h : ℝ → ℂ) (hh : Continuous h) :
      (∫ t in Set.Icc (-δ) δ, ‖h t‖ ^ 2) ≤
        ∫ t in Set.Icc (-R) R, ‖h t‖ ^ 2 :=
    setIntegral_mono_set ((hh.norm.pow 2).integrableOn_Icc)
      (Filter.Eventually.of_forall (fun t => sq_nonneg ‖h t‖))
      (Filter.Eventually.of_forall (fun t ht => hsub ht))
  exact (arc_pair_integral_le f g hf hg (-δ) δ n).trans
    (mul_le_mul (Real.sqrt_le_sqrt (hm f hf)) (Real.sqrt_le_sqrt (hm g hg))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Gallagher 1975 p.128 Schwarz inequality and p.129 display 8.
A pair of primitive corrected amplitudes on any smaller arc has integral norm
at most the square of the total corrected energy. -/
theorem corrected_pair_integral_le_energy_sq (N r k j : ℕ) (θ γ δ n : ℝ)
    (χ : DirichletCharacter ℂ (k + 1)) (ψ : DirichletCharacter ℂ (j + 1))
    (hk : k < ⌊(N : ℝ) ^ θ⌋₊) (hj : j < ⌊(N : ℝ) ^ θ⌋₊)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hδ : δ ≤ (N : ℝ) ^ θ / N) :
    ‖∫ β in Set.Icc (-δ) δ,
      star (correctedAmplitude χ N r γ β) * correctedAmplitude ψ N r γ β *
        LeanLab.PNTPort.LargeSieve.e (n * β)‖ ≤ correctedEnergy N θ r γ ^ 2 := by
  have hcs := arc_pair_integral_le_common_window
    (correctedAmplitude χ N r γ) (correctedAmplitude ψ N r γ)
    (continuous_correctedAmplitude χ N r γ) (continuous_correctedAmplitude ψ N r γ)
    δ ((N : ℝ) ^ θ / N) n hδ
  apply hcs.trans
  simpa only [pow_two] using mul_le_mul
    (LeanLab.Linnik.Decomp486c.corrected_norm_le_energy N r k θ γ χ hk hχ)
    (LeanLab.Linnik.Decomp486c.corrected_norm_le_energy N r j θ γ ψ hj hψ)
    (Real.sqrt_nonneg _) (correctedEnergy_nonneg N θ r γ)

/-- CONDITIONAL ON the leaves of LeanLab/Linnik/MajorArcEnergy/Leaves13.lean, via
`LeanLab.Linnik.MajorArcEnergy.major_arc_energy_zero_split`; formerly a LEAF.
Gallagher 1975 p.131 display 13.
The uncorrected energy controls the major arc error without a separate
exceptional contribution. This is the conductor zero case of the reduction.
The supplied expansion is the proved rational arc character expansion. -/
theorem major_arc_energy_zero
    (hExpansion : ∃ C : ℝ, 0 < C ∧ ∀ N q : ℕ, ∀ [NeZero q], ∀ a : ℕ,
      Nat.Coprime a q → a ≤ q → ∀ β : ℝ,
        ‖Sg N ((a : ℝ) / q + β) - (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ a * gaussSum χ⁻¹ ZMod.stdAddChar * primeAmplitude χ.primitiveCharacter N β‖ ≤
          C * Real.sqrt q * Real.log (2 * q)) :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
          K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
            (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
              (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0) := by
  exact LeanLab.Linnik.MajorArcEnergy.major_arc_energy_zero_split hExpansion

/-- CONDITIONAL ON the leaves of LeanLab/Linnik/MajorArcEnergy/Leaves13.lean and
Leaves1517.lean, via `LeanLab.Linnik.MajorArcEnergy.major_arc_energy_exceptional_split`;
formerly a LEAF. Gallagher 1975 p.131 displays 15 through 17 and p.132.
For a positive exceptional conductor the corrected character energy controls
the remaining terms and the exceptional coefficient has the printed weight.
This is only the positive conductor case of the arithmetic reduction. -/
theorem major_arc_energy_exceptional
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
          0 < r → ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n) := by
  exact LeanLab.Linnik.MajorArcEnergy.major_arc_energy_exceptional_split hExpansion

/-- Gallagher 1975 p.131 display 13 and displays 15 through 17.
Combine the two arithmetic cases with uniform constants and thresholds.
CONDITIONAL ON the supplied conductor zero and positive conductor estimates. -/
theorem major_arc_energy_bound_of_cases
    (hZero :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
          K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
            (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
              (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0))
    (hExceptional :
    ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, ∀ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) →
          0 < r → ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
                exceptionalWeight r n)) :
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
  obtain ⟨Kz, θz, hKz, hθz, hθz1, hz⟩ := hZero
  obtain ⟨Ke, θe, hKe, hθe, hθe1, he⟩ := hExceptional
  refine ⟨max Kz Ke, min θz θe, lt_of_lt_of_le hKz (le_max_left _ _),
    lt_min hθz hθe, (min_le_left _ _).trans hθz1, ?_⟩
  intro θ hθ hθlim
  obtain ⟨Nz, hz⟩ := hz θ hθ (hθlim.trans (min_le_left _ _))
  obtain ⟨Ne, he⟩ := he θ hθ (hθlim.trans (min_le_right _ _))
  refine ⟨max 2 (max Nz Ne), fun N hN r γ hr n hn => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNz : Nz ≤ N := (le_max_left Nz Ne).trans ((le_max_right 2 _).trans hN)
  have hNe : Ne ≤ N := (le_max_right Nz Ne).trans ((le_max_right 2 _).trans hN)
  have hE := normalizedEnergy_nonneg hN2 θ r γ
  have hP : 1 ≤ (N : ℝ) ^ θ :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) hθ.le
  have ht : 0 ≤ Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card :=
    mul_nonneg (div_nonneg (Real.log_nonneg hP) (by positivity)) (by positivity)
  have hx : 0 ≤ exceptionalWeight r n := by unfold exceptionalWeight; positivity
  have hb : 0 ≤ ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
      (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
        (1 + normalizedEnergy N θ r γ) * normalizedEnergy N θ r γ +
        exceptionalWeight r n) := by
    unfold totientWeight
    positivity
  by_cases hr0 : r = 0
  · subst r
    have hraw := hz N hNz n hn
    have hraw' : complexFrequencyError N θ n ≤
        Kz * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
          (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
            (1 + normalizedEnergy N θ 0 γ) * normalizedEnergy N θ 0 γ +
            exceptionalWeight 0 n) := by
      simpa only [normalizedEnergy_zero_conductor N θ γ 0, exceptionalWeight,
        Nat.cast_zero, zero_mul, zero_div, add_zero] using hraw
    apply hraw'.trans
    convert mul_le_mul_of_nonneg_right (le_max_left Kz Ke) hb using 1 <;> ring
  · have hraw := he N hNe r γ hr (Nat.pos_of_ne_zero hr0) n hn
    apply hraw.trans
    convert mul_le_mul_of_nonneg_right (le_max_right Kz Ke) hb using 1 <;> ring


/-- Gallagher 1975 p.131 display 13 and displays 15 through 17.
The full arithmetic bound follows from the conductor zero and positive cases.
CONDITIONAL ON the two smaller arithmetic leaves. -/
theorem major_arc_energy_bound_split
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
  exact major_arc_energy_bound_of_cases (major_arc_energy_zero hExpansion)
    (major_arc_energy_exceptional hExpansion)

end LeanLab.Linnik.Decomp486b





