module

public import LeanLab.Linnik.MajorArcEnergy.Defs

/-!
Gallagher 1975 P0094 pp.128 to 131. Elementary steps of the display 13 reduction:
display 4 by the Schwarz inequality, display 10, and the identification of the
energy E of display 13 with the lab's correctedEnergy at conductor zero.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.MajorArcEnergy

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b

/-- Gallagher 1975 p.128 last line, the Schwarz inequality behind display 4:
on a compact window the integral of |f| |g| is at most the product of the two
square root mean squares. Proved from Mathlib's Hoelder inequality with p = q = 2. -/
theorem integral_norm_mul_le_sqrt (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) :
    (∫ t in Set.Icc a b, ‖f t‖ * ‖g t‖) ≤
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
  simpa only [μ, Real.rpow_two, ← Real.sqrt_eq_rpow] using hholder

/-- Gallagher 1975 p.128 last line and p.129 display 4: the Schwarz inequality for
I_{n,q}, with the arc of radius delta inside the common window of radius R. -/
theorem arc_integral_le_window (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (δ R n : ℝ) (hδR : δ ≤ R) :
    ‖∫ t in Set.Icc (-δ) δ, star (f t) * g t * LeanLab.PNTPort.LargeSieve.e (n * t)‖ ≤
      Real.sqrt (∫ t in Set.Icc (-R) R, ‖f t‖ ^ 2) *
        Real.sqrt (∫ t in Set.Icc (-R) R, ‖g t‖ ^ 2) := by
  have hsub : Set.Icc (-δ) δ ⊆ Set.Icc (-R) R := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hm (h : ℝ → ℂ) (hh : Continuous h) :
      (∫ t in Set.Icc (-δ) δ, ‖h t‖ ^ 2) ≤ ∫ t in Set.Icc (-R) R, ‖h t‖ ^ 2 :=
    setIntegral_mono_set ((hh.norm.pow 2).integrableOn_Icc)
      (Filter.Eventually.of_forall (fun t => sq_nonneg ‖h t‖))
      (Filter.Eventually.of_forall (fun t ht => hsub ht))
  calc
    _ ≤ ∫ t in Set.Icc (-δ) δ,
        ‖star (f t) * g t * LeanLab.PNTPort.LargeSieve.e (n * t)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t in Set.Icc (-δ) δ, ‖f t‖ * ‖g t‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        simp only [norm_mul, norm_star, LeanLab.PNTPort.LargeSieve.norm_e, mul_one]
    _ ≤ _ := integral_norm_mul_le_sqrt f g hf hg (-δ) δ
    _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt (hm f hf)) (Real.sqrt_le_sqrt (hm g hg))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Gallagher 1975 p.130 display 10: the triangle inequality in L2 on a compact window,
the step ||A(1)|| at most ||T|| plus ||R|| for A(1) equal to T plus R. -/
theorem sqrt_integral_add_le (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) :
    Real.sqrt (∫ t in Set.Icc a b, ‖f t + g t‖ ^ 2) ≤
      Real.sqrt (∫ t in Set.Icc a b, ‖f t‖ ^ 2) +
        Real.sqrt (∫ t in Set.Icc a b, ‖g t‖ ^ 2) := by
  set A := Real.sqrt (∫ t in Set.Icc a b, ‖f t‖ ^ 2)
  set B := Real.sqrt (∫ t in Set.Icc a b, ‖g t‖ ^ 2)
  have hA : A ^ 2 = ∫ t in Set.Icc a b, ‖f t‖ ^ 2 :=
    Real.sq_sqrt (setIntegral_nonneg measurableSet_Icc fun t _ => sq_nonneg _)
  have hB : B ^ 2 = ∫ t in Set.Icc a b, ‖g t‖ ^ 2 :=
    Real.sq_sqrt (setIntegral_nonneg measurableSet_Icc fun t _ => sq_nonneg _)
  have hcs := integral_norm_mul_le_sqrt f g hf hg a b
  have i1 : IntegrableOn (fun t => ‖f t‖ ^ 2) (Set.Icc a b) :=
    (hf.norm.pow 2).integrableOn_Icc
  have i2 : IntegrableOn (fun t => 2 * (‖f t‖ * ‖g t‖)) (Set.Icc a b) :=
    (continuous_const.mul (hf.norm.mul hg.norm)).integrableOn_Icc
  have i3 : IntegrableOn (fun t => ‖g t‖ ^ 2) (Set.Icc a b) :=
    (hg.norm.pow 2).integrableOn_Icc
  have hle : (∫ t in Set.Icc a b, ‖f t + g t‖ ^ 2) ≤
      ∫ t in Set.Icc a b, (‖f t‖ ^ 2 + 2 * (‖f t‖ * ‖g t‖) + ‖g t‖ ^ 2) := by
    apply setIntegral_mono_on ((hf.add hg).norm.pow 2).integrableOn_Icc
      ((i1.add i2).add i3) measurableSet_Icc
    intro t _
    have h := norm_add_le (f t) (g t)
    dsimp only [Pi.add_apply, Pi.pow_apply]
    nlinarith [norm_nonneg (f t + g t), norm_nonneg (f t), norm_nonneg (g t)]
  have heq : (∫ t in Set.Icc a b, (‖f t‖ ^ 2 + 2 * (‖f t‖ * ‖g t‖) + ‖g t‖ ^ 2)) =
      (∫ t in Set.Icc a b, ‖f t‖ ^ 2) + 2 * (∫ t in Set.Icc a b, ‖f t‖ * ‖g t‖) +
        ∫ t in Set.Icc a b, ‖g t‖ ^ 2 := by
    rw [integral_add, integral_add, integral_const_mul]
    all_goals first | exact i1 | exact i2 | exact i3 | exact i1.add i2
  rw [heq] at hle
  have hsq : (∫ t in Set.Icc a b, ‖f t + g t‖ ^ 2) ≤ (A + B) ^ 2 := by
    nlinarith [hcs]
  calc
    _ ≤ Real.sqrt ((A + B) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = A + B := Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Gallagher 1975 p.128 last line and p.129 display 4: by the Schwarz inequality
|I_{n,q}(chi, chi')| is at most ||A(chi)|| ||A(chi')||, hence
|J_n(chi, chi')| is at most C_n(chi, chi') ||A(chi)|| ||A(chi')||. -/
theorem pair_sum_schwarz (N : ℕ) (P : ℝ) (hP : 0 ≤ P) (n : ℤ) (x y : PChar) :
    ‖pairSum N P n x y‖ ≤ pairWeight P n x y * ampNorm N P x * ampNorm N P y := by
  unfold pairSum pairWeight
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
  have hrad : P / (q * N) ≤ P / N := by
    rw [mul_comm, ← div_div]
    exact div_le_self (div_nonneg hP (Nat.cast_nonneg _)) (by exact_mod_cast hq1)
  have harc : ‖arcIntegral N P n q x y‖ ≤ ampNorm N P x * ampNorm N P y :=
    arc_integral_le_window _ _ (continuous_primeAmplitude x.2 N)
      (continuous_primeAmplitude y.2 N) _ _ _ hrad
  have hw : ‖(1 / (q.totient : ℂ) ^ 2)‖ = 1 / (q.totient : ℝ) ^ 2 := by
    simp
  rw [norm_mul, norm_mul, hw, mul_assoc (1 / (q.totient : ℝ) ^ 2 * _)]
  exact mul_le_mul_of_nonneg_left harc (by positivity)

/-- Gallagher 1975 p.130 display 10: ||A(1)|| is at most a constant times
N^(1/2) L^(-1) plus ||R||, for every window of radius at most one half. -/
theorem principal_amp_norm :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ P : ℝ, P / N ≤ 1 / 2 →
      ampNorm N P one ≤ K * (Real.sqrt N / Real.log N) + remNorm N P := by
  obtain ⟨N₁, hN₁⟩ := LeanLab.Linnik.Decomp486c.principalMain_window_mean_eventually 1 one_pos
  refine ⟨2, two_pos, max 2 N₁, fun N hN P hPN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hT := hN₁ N ((le_max_right _ _).trans hN) (P / N) hPN
  have hmink := sqrt_integral_add_le (principalMain N)
    (fun β => primeAmplitude one.2 N β - principalMain N β)
    (LeanLab.Linnik.Decomp482b.continuous_principalMain N)
    ((continuous_primeAmplitude one.2 N).sub
      (LeanLab.Linnik.Decomp482b.continuous_principalMain N)) (-(P / N)) (P / N)
  simp only [add_sub_cancel] at hmink
  unfold ampNorm remNorm
  refine hmink.trans (add_le_add ?_ le_rfl)
  have hK : 2 * (Real.sqrt N / Real.log N) =
      Real.sqrt (4 * ((N : ℝ) / Real.log N ^ 2)) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_div' _ (sq_nonneg _),
      Real.sqrt_sq hl.le, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hK]
  apply Real.sqrt_le_sqrt
  have : 0 ≤ (N : ℝ) / Real.log N ^ 2 := by positivity
  linarith

/-- Gallagher 1975 p.131 display 13: E equals ||R|| plus the sum of ||A(chi)|| over the
primitive chi other than 1 to conductors at most P; this is the lab's correctedEnergy
at conductor zero. -/
theorem correctedEnergy_zero_eq (N : ℕ) (θ : ℝ) (hP : 1 ≤ (N : ℝ) ^ θ) :
    correctedEnergy N θ 0 0 = remNorm N ((N : ℝ) ^ θ) +
      ∑ x ∈ (family ((N : ℝ) ^ θ)).erase one, ampNorm N ((N : ℝ) ^ θ) x := by
  have hone : one ∈ family ((N : ℝ) ^ θ) := by
    unfold family one
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Nat.floor_pos.mpr hP, DirichletCharacter.isPrimitive_one_level_one⟩
  unfold correctedEnergy
  rw [← Finset.sum_sigma (range ⌊(N : ℝ) ^ θ⌋₊)
    (fun k => (univ : Finset (DirichletCharacter ℂ (k + 1))).filter fun χ => χ.IsPrimitive)
    (fun x => Real.sqrt (∫ β in Set.Icc (-((N : ℝ) ^ θ / N)) ((N : ℝ) ^ θ / N),
      ‖correctedAmplitude x.2 N 0 0 β‖ ^ 2))]
  change ∑ x ∈ family ((N : ℝ) ^ θ), _ = _
  rw [← Finset.add_sum_erase _ _ hone]
  congr 1
  · simp [remNorm, one, correctedAmplitude]
  · apply Finset.sum_congr rfl
    intro x hx
    have hx1 : x.1 ≠ 0 := by
      intro h0
      apply (Finset.mem_erase.mp hx).1
      obtain ⟨k, χ⟩ := x
      simp only at h0
      subst h0
      simp only [one, DirichletCharacter.level_one χ]
    simp [ampNorm, correctedAmplitude, hx1]

/-- The principal character to modulus 1 lies in the family once P is at least 1. -/
theorem one_mem_family {P : ℝ} (hP : 1 ≤ P) : one ∈ family P := by
  unfold family one
  simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨Nat.floor_pos.mpr hP, DirichletCharacter.isPrimitive_one_level_one⟩

end LeanLab.Linnik.MajorArcEnergy

