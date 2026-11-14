module

public import LeanLab.Linnik.Decomp482a
public import LeanLab.PNTPort.Gallagher.Basic
public import LeanLab.Linnik.ExplicitFormula.Assembly

/-!
Gallagher 1975 p.131 display 14.
Shared energy definitions and the two cases of the explicit formula estimate.
Source https://doi.org/10.1007/BF01390190
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp482b

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp1532b (zeroCount excSet)
open LeanLab.PNTPort.LargeSieve (e)

/-- Gallagher 1975 p.130. The principal main polynomial T. -/
noncomputable def principalMain (N : ℕ) (β : ℝ) : ℂ :=
  ∑ m ∈ Ioc 1 N, (1 / Real.log m : ℂ) * LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * β)

/-- Gallagher 1975 p.131 below display 14. The exceptional main polynomial. -/
noncomputable def exceptionalMain (N : ℕ) (γ β : ℝ) : ℂ :=
  ∑ m ∈ Ioc 1 N, ((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) * LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * β)

/-- Gallagher 1975 pp.130 and 131. Subtract T from the principal sum.
Add the exceptional main polynomial at conductor r since A equals minus T tilde plus R tilde. -/
noncomputable def correctedAmplitude {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) (r : ℕ) (γ β : ℝ) : ℂ :=
  primeAmplitude χ N β - (if q = 1 then principalMain N β else 0) +
    (if q = r ∧ χ.LFunction (γ : ℂ) = 0 then exceptionalMain N γ β else 0)

/-- Gallagher 1975 p.131 display 14 and p.128 norm definition.
Sum the L2 norms after removing the principal and exceptional main polynomials.
The window has radius one over Q equal to P over N. -/
noncomputable def correctedEnergy (N : ℕ) (θ : ℝ) (r : ℕ) (γ : ℝ) : ℝ :=
  ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
      Real.sqrt (∫ β in Set.Icc (-((N : ℝ) ^ θ / N)) ((N : ℝ) ^ θ / N),
        ‖correctedAmplitude χ N r γ β‖ ^ 2)

/-- Gallagher 1975 p.131 display 14 divided by the natural scale sqrt N over log N. -/
noncomputable def normalizedEnergy (N : ℕ) (θ : ℝ) (r : ℕ) (γ : ℝ) : ℝ :=
  correctedEnergy N θ r γ / (Real.sqrt N / Real.log N)

/-- Gallagher 1975 p.130. The principal main polynomial is continuous. -/
theorem continuous_principalMain (N : ℕ) : Continuous (principalMain N) := by
  exact LeanLab.Linnik.U1426ChainWire.continuous_SA (Ioc 1 N) (fun m => 1 / Real.log m)

/-- Gallagher 1975 p.131 after display 14. The exceptional main polynomial is continuous. -/
theorem continuous_exceptionalMain (N : ℕ) (γ : ℝ) : Continuous (exceptionalMain N γ) := by
  exact LeanLab.Linnik.U1426ChainWire.continuous_SA (Ioc 1 N)
    (fun m => (((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) : ℂ))

/-- Gallagher 1975 p.131. The corrected primitive character amplitude is continuous. -/
theorem continuous_correctedAmplitude {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N r : ℕ) (γ : ℝ) : Continuous (correctedAmplitude χ N r γ) := by
  have hp := continuous_primeAmplitude χ N
  have hm := continuous_principalMain N
  have he := continuous_exceptionalMain N γ
  unfold correctedAmplitude
  split_ifs <;> fun_prop

/-- Gallagher 1975 p.128 norm definition and p.131 corrected norm.
Every corrected squared amplitude is integrable on its compact beta window. -/
theorem integrableOn_corrected_norm_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N r : ℕ) (γ a b : ℝ) :
    IntegrableOn (fun β => ‖correctedAmplitude χ N r γ β‖ ^ 2) (Set.Icc a b) := by
  exact ((continuous_correctedAmplitude χ N r γ).norm.pow 2).integrableOn_Icc

/-- Gallagher 1975 p.127 no exceptional conductor convention.
The normalized energy at conductor zero is independent of the unused real zero parameter. -/
theorem normalizedEnergy_zero_conductor (N : ℕ) (θ γ γ' : ℝ) :
    normalizedEnergy N θ 0 γ = normalizedEnergy N θ 0 γ' := by
  simp [normalizedEnergy, correctedEnergy, correctedAmplitude]

/-- Gallagher 1975 p.131 display 14. The zero density input near sigma one
is already proved in the lab. The endpoint sigma one is retained. -/
theorem density_near_one :
    ∃ c C : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ∑ q ∈ range ⌊T⌋₊,
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
          (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  exact LeanLab.Linnik.Decomp1532b.gallagher_density

/-- Gallagher 1975 p.131. The corrected energy is nonnegative. -/
theorem correctedEnergy_nonneg (N : ℕ) (θ : ℝ) (r : ℕ) (γ : ℝ) :
    0 ≤ correctedEnergy N θ r γ := by
  classical
  exact sum_nonneg fun k _ => sum_nonneg fun χ _ => Real.sqrt_nonneg _

/-- Gallagher 1975 p.131. The normalized corrected energy is nonnegative for N at least two. -/
theorem normalizedEnergy_nonneg {N : ℕ} (hN : 2 ≤ N) (θ : ℝ) (r : ℕ) (γ : ℝ) :
    0 ≤ normalizedEnergy N θ r γ := by
  unfold normalizedEnergy
  apply div_nonneg (correctedEnergy_nonneg N θ r γ)
  exact div_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))

/-- Gallagher 1975 p.131 display 14. Normalizing the energy loses no information
for N at least two because sqrt N over log N is strictly positive. -/
theorem normalizedEnergy_le_iff {N : ℕ} (hN : 2 ≤ N) (θ : ℝ) (r : ℕ) (γ B : ℝ) :
    normalizedEnergy N θ r γ ≤ B ↔
      correctedEnergy N θ r γ ≤ B * (Real.sqrt N / Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  exact div_le_iff₀ (div_pos (Real.sqrt_pos.mpr hN0) (Real.log_pos hN1))

end LeanLab.Linnik.Decomp482b

namespace LeanLab.Linnik.Decomp486c

open Finset MeasureTheory Filter
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (excSet)

/-- Gallagher 1975 p.127 exceptional zero convention.
A character in the fixed exceptional strip has a real zero strictly below one.
This is an elementary use of the proved reality and Siegel estimates. -/
theorem exceptional_real_zero {T : ℝ} (hT : 2 ≤ T)
    (x : Σ q : ℕ, DirichletCharacter ℂ (q + 1))
    (hx : x ∈ excSet exceptionalStrip T) :
    ∃ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 ∧
      1 - exceptionalStrip / Real.log T ≤ γ ∧ γ < 1 := by
  let br := Classical.choose LeanLab.Linnik.Decomp1532b.page_real
  have hb : exceptionalStrip ≤ br := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hxr := LeanLab.Linnik.Decomp1532b.excSet_mono hb hT hx
  obtain ⟨ρ, hz, hβ, ht⟩ := hx.2.2
  have hβr : 1 - br / Real.log T ≤ ρ.re := by
    have hd := div_le_div_of_nonneg_right hb
      (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have hp := (Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_real).2 T hT x hxr
  have him := hp.2 ρ hz hβr ht
  have he : (ρ.re : ℂ) = ρ := by apply Complex.ext <;> simp [him]
  have hzreal : x.2.LFunction (ρ.re : ℂ) = 0 := by rwa [he]
  obtain ⟨c, hc, hs⟩ := LeanLab.Linnik.Decomp1532b.siegel 1 zero_lt_one
  have hbound := hs x.1 x.2 hx.2.1 hp.1 ρ.re hzreal
  have hpos : 0 < c * ((x.1 : ℝ) + 1) ^ (-(1 : ℝ)) :=
    mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  exact ⟨ρ.re, hzreal, hβ, by linarith⟩

/-- Gallagher 1975 p.128 common norm and p.131 corrected energy.
Each primitive corrected character norm is at most the total corrected energy.
The conductor index must lie in the finite family. -/
theorem corrected_norm_le_energy (N r k : ℕ) (θ γ : ℝ)
    (χ : DirichletCharacter ℂ (k + 1)) (hk : k < ⌊(N : ℝ) ^ θ⌋₊)
    (hχ : χ.IsPrimitive) :
    Real.sqrt (∫ β in Set.Icc (-((N : ℝ) ^ θ / N)) ((N : ℝ) ^ θ / N),
      ‖correctedAmplitude χ N r γ β‖ ^ 2) ≤ correctedEnergy N θ r γ := by
  classical
  unfold correctedEnergy
  calc
    _ ≤ ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
          (fun ψ => ψ.IsPrimitive),
        Real.sqrt (∫ β in Set.Icc (-((N : ℝ) ^ θ / N)) ((N : ℝ) ^ θ / N),
          ‖correctedAmplitude ψ N r γ β‖ ^ 2) :=
      single_le_sum (fun ψ _ => Real.sqrt_nonneg _) (mem_filter.mpr ⟨mem_univ χ, hχ⟩)
    _ ≤ _ := by
      apply single_le_sum (f := fun j : ℕ =>
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (j + 1))).filter
            (fun ψ => ψ.IsPrimitive),
          Real.sqrt (∫ β in Set.Icc (-((N : ℝ) ^ θ / N)) ((N : ℝ) ^ θ / N),
            ‖correctedAmplitude ψ N r γ β‖ ^ 2))
        (fun j _ => sum_nonneg fun ψ _ => Real.sqrt_nonneg _) (mem_range.mpr hk)

/-- Gallagher 1975 p.131 display 14 and Montgomery and Vaughan 1975 p.366 Section 7.
Auxiliary obstruction to keeping a pointwise conductor count loss.
At fixed positive theta, P squared times the fixed exponential factor grows
without bound. This is a statement about a crude bound, not about the energy. -/
theorem pointwise_character_loss_tendsto_atTop {θ : ℝ} (hθ : 0 < θ) (c : ℝ) :
    Tendsto (fun N : ℕ => ((N : ℝ) ^ θ) ^ 2 * Real.exp (-c / θ)) atTop atTop := by
  apply Filter.Tendsto.atTop_mul_const (Real.exp_pos _)
  exact (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
    ((tendsto_rpow_atTop hθ).comp (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- Gallagher 1975 p.130 principal polynomial norm.
Its full period mean square is exactly J of zero by finite Parseval. -/
theorem principalMain_mean_square (N : ℕ) :
    (∫ β in Set.Icc (0 : ℝ) 1, ‖principalMain N β‖ ^ 2) =
      LeanLab.Linnik.Decomp1532b.Jn N 0 := by
  rw [LeanLab.Linnik.Decomp1532b.Jn_zero_eq_sum]
  have h := LeanLab.Linnik.U1426ChainWire.parseval (Ioc 1 N) (fun m => 1 / Real.log m)
  simpa [principalMain, LeanLab.Linnik.LiLiuLemma43.SA, div_pow] using h
/-- Gallagher 1975 p.130 principal polynomial norm.
Every symmetric window of radius at most one half has mean square at most
J of zero. Periodicity moves the enclosing window to the unit interval. -/
theorem principalMain_window_mean_le (N : ℕ) (R : ℝ) (hR : R ≤ 1 / 2) :
    (∫ β in Set.Icc (-R) R, ‖principalMain N β‖ ^ 2) ≤
      LeanLab.Linnik.Decomp1532b.Jn N 0 := by
  have hper : Function.Periodic (fun β => ‖principalMain N β‖ ^ 2) 1 := by
    intro β
    have hp := LeanLab.Linnik.LiLiuLemma43Int.SA_periodic (Ioc 1 N)
      (fun m => (1 / Real.log m : ℂ)) β
    have hT : principalMain N (β + 1) = principalMain N β := by
      simpa only [principalMain, LeanLab.Linnik.LiLiuLemma43.SA] using hp
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hT
  have heq : (∫ β in Set.Icc (-1 / 2 : ℝ) (1 / 2), ‖principalMain N β‖ ^ 2) =
      ∫ β in Set.Icc (0 : ℝ) 1, ‖principalMain N β‖ ^ 2 := by
    simpa only [show (-1 / 2 : ℝ) + 1 = 1 / 2 by ring, zero_add,
      intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc] using hper.intervalIntegral_add_eq (-1 / 2) 0
  have hsub : Set.Icc (-R) R ⊆ Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro β hβ
    exact ⟨by linarith [hβ.1], by linarith [hβ.2]⟩
  calc
    _ ≤ ∫ β in Set.Icc (-1 / 2 : ℝ) (1 / 2), ‖principalMain N β‖ ^ 2 :=
      setIntegral_mono_set ((continuous_principalMain N).norm.pow 2).integrableOn_Icc
        (Filter.Eventually.of_forall fun β => sq_nonneg ‖principalMain N β‖)
        (Filter.Eventually.of_forall fun β hβ => hsub hβ)
    _ = _ := heq.trans (principalMain_mean_square N)
/-- Gallagher 1975 p.130 norm estimate for the principal polynomial.
Uniformly over radii at most one half, its mean square is at most
one plus epsilon times N over log squared N for all sufficiently large N. -/
theorem principalMain_window_mean_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ R : ℝ, R ≤ 1 / 2 →
      (∫ β in Set.Icc (-R) R, ‖principalMain N β‖ ^ 2) ≤
        (1 + ε) * ((N : ℝ) / Real.log N ^ 2) := by
  have h := LeanLab.Linnik.Decomp1532b.J0_asymp.eventually
    (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + ε))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨max 2 N₀, fun N hN R hR => (principalMain_window_mean_le N R hR).trans ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  exact ((div_lt_iff₀ (div_pos hn (sq_pos_of_pos hl))).mp
    (hN₀ N ((le_max_right _ _).trans hN))).le

/-- Gallagher 1975 pp.130 and 131 main polynomial subtraction.
The explicit finite coefficient of the corrected amplitude. -/
noncomputable def correctedCoefficient {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (r : ℕ) (γ : ℝ) (m : ℕ) : ℂ :=
  (if m.Prime then χ m else 0) -
    (if q = 1 then (if 1 < m then (1 / Real.log m : ℂ) else 0) else 0) +
    (if q = r ∧ χ.LFunction (γ : ℂ) = 0 then
      (if 1 < m then (((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) : ℂ) else 0) else 0)

/-- Gallagher 1975 pp.130 and 131 corrected amplitude.
Its finite Fourier coefficients are exactly correctedCoefficient. -/
theorem correctedAmplitude_eq_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N r : ℕ) (γ β : ℝ) :
    correctedAmplitude χ N r γ β =
      ∑ m ∈ range (N + 1), correctedCoefficient χ r γ m *
        LeanLab.PNTPort.LargeSieve.e ((m : ℝ) * β) := by
  classical
  have hp : Nat.primesLE N = (range (N + 1)).filter Nat.Prime := by rfl
  have hi : Ioc 1 N = (range (N + 1)).filter (fun m => 1 < m) := by
    ext m
    simp only [mem_Ioc, mem_filter, mem_range]
    omega
  by_cases hq : q = 1 <;> by_cases he : q = r ∧ χ.LFunction (γ : ℂ) = 0 <;>
    simp [correctedAmplitude, correctedCoefficient, primeAmplitude, principalMain,
      exceptionalMain, hp, hi, Finset.sum_filter, hq, he, sub_mul, add_mul, ite_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Gallagher 1975 p.131 display 14 and the method cited from reference 10 Section 7.
Finite short window reduction by the proved discrete Gallagher inequality.
This does not estimate the resulting short interval character sums. -/
theorem corrected_amplitude_short_window_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (N r L : ℕ) (γ : ℝ) (hL : 0 < L) :
    (∫ β in Set.Icc (-(1 / (2 * L) : ℝ)) (1 / (2 * L)),
      ‖correctedAmplitude χ N r γ β‖ ^ 2) ≤
      (Real.pi / (2 * L)) ^ 2 *
        ∑ m ∈ range (N + 1 + L),
          ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ r γ) (N + 1) L m‖ ^ 2 := by
  simp_rw [correctedAmplitude_eq_sum]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by
      have h : (0 : ℝ) ≤ 1 / (2 * L) := by positivity
      linarith : -(1 / (2 * L) : ℝ) ≤ 1 / (2 * L))]
  exact LeanLab.PNTPort.Gallagher.gallagher (correctedCoefficient χ r γ) (N + 1) L hL

/-- Gallagher 1975 p.131 exceptional main polynomial norm before display 15.
For gamma at most one its full period mean square is at most J of zero.
This uses Parseval and coefficient comparison without an exceptional zero input. -/
theorem exceptionalMain_mean_square_le (N : ℕ) (γ : ℝ) (hγ : γ ≤ 1) :
    (∫ β in Set.Icc (0 : ℝ) 1, ‖exceptionalMain N γ β‖ ^ 2) ≤
      LeanLab.Linnik.Decomp1532b.Jn N 0 := by
  have heq : (∫ β in Set.Icc (0 : ℝ) 1, ‖exceptionalMain N γ β‖ ^ 2) =
      ∑ m ∈ Ioc 1 N, ((m : ℝ) ^ (γ - 1) / Real.log m) ^ 2 := by
    simpa [exceptionalMain, LeanLab.Linnik.LiLiuLemma43.SA] using
      LeanLab.Linnik.U1426ChainWire.parseval (Ioc 1 N)
        (fun m => (m : ℝ) ^ (γ - 1) / Real.log m)
  rw [heq, LeanLab.Linnik.Decomp1532b.Jn_zero_eq_sum]
  apply sum_le_sum
  intro m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (le_of_lt (mem_Ioc.mp hm).1)
  have hp0 : 0 ≤ (m : ℝ) ^ (γ - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hp1 : (m : ℝ) ^ (γ - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)
  rw [div_pow]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
/-- Gallagher 1975 p.131 exceptional main polynomial norm before display 15.
The same bound holds on every symmetric window of radius at most one half. -/
theorem exceptionalMain_window_mean_le (N : ℕ) (γ : ℝ) (hγ : γ ≤ 1) (R : ℝ) (hR : R ≤ 1 / 2) :
    (∫ β in Set.Icc (-R) R, ‖exceptionalMain N γ β‖ ^ 2) ≤
      LeanLab.Linnik.Decomp1532b.Jn N 0 := by
  have hper : Function.Periodic (fun β => ‖exceptionalMain N γ β‖ ^ 2) 1 := by
    intro β
    have hp := LeanLab.Linnik.LiLiuLemma43Int.SA_periodic (Ioc 1 N)
      (fun m => (((m : ℝ) ^ (γ - 1) / Real.log m : ℝ) : ℂ)) β
    have hT : exceptionalMain N γ (β + 1) = exceptionalMain N γ β := by
      simpa only [exceptionalMain, LeanLab.Linnik.LiLiuLemma43.SA] using hp
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hT
  have heq : (∫ β in Set.Icc (-1 / 2 : ℝ) (1 / 2), ‖exceptionalMain N γ β‖ ^ 2) =
      ∫ β in Set.Icc (0 : ℝ) 1, ‖exceptionalMain N γ β‖ ^ 2 := by
    simpa only [show (-1 / 2 : ℝ) + 1 = 1 / 2 by ring, zero_add,
      intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc] using hper.intervalIntegral_add_eq (-1 / 2) 0
  have hsub : Set.Icc (-R) R ⊆ Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro β hβ
    exact ⟨by linarith [hβ.1], by linarith [hβ.2]⟩
  calc
    _ ≤ ∫ β in Set.Icc (-1 / 2 : ℝ) (1 / 2), ‖exceptionalMain N γ β‖ ^ 2 :=
      setIntegral_mono_set ((continuous_exceptionalMain N γ).norm.pow 2).integrableOn_Icc
        (Filter.Eventually.of_forall fun β => sq_nonneg ‖exceptionalMain N γ β‖)
        (Filter.Eventually.of_forall fun β hβ => hsub hβ)
    _ = _ := heq
    _ ≤ _ := exceptionalMain_mean_square_le N γ hγ

/-- Gallagher 1975 p.131 display 14 by the method of reference 10 Section 7, Gallagher 1970
Lemma 1. The window length, about N over 2P with P equal to N to theta, so that the
p.128 norm window of radius P over N lies inside the Gallagher window of radius 1 over 2L. -/
noncomputable def gallagherLength (N : ℕ) (θ : ℝ) : ℕ :=
  ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊

/-- Gallagher 1975 p.131 display 14 with the p.128 norm window of radius P over N.
For theta at most one half and N at least four, the window length is positive and
P over N is at most 1 over 2L. Elementary. -/
theorem gallagherLength_spec {N : ℕ} {θ : ℝ} (_hθ : 0 ≤ θ) (hθ2 : θ ≤ 1 / 2) (hN : 4 ≤ N) :
    0 < gallagherLength N θ ∧
      (N : ℝ) ^ θ / N ≤ 1 / (2 * (gallagherLength N θ : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hP : 0 < (N : ℝ) ^ θ := Real.rpow_pos_of_pos hN0 _
  have hkey : 2 * (N : ℝ) ^ θ ≤ N := by
    have h1 : (N : ℝ) ^ θ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 hθ2
    have h2 : 2 * (N : ℝ) ^ (1 / 2 : ℝ) ≤ N := by
      rw [← Real.sqrt_eq_rpow]
      have hs : 2 ≤ Real.sqrt N := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
      have hm := Real.mul_self_sqrt hN0.le
      nlinarith
    linarith
  have hx1 : 1 ≤ (N : ℝ) / (2 * (N : ℝ) ^ θ) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hL : 0 < gallagherLength N θ := Nat.floor_pos.mpr hx1
  refine ⟨hL, ?_⟩
  have hLle : (gallagherLength N θ : ℝ) ≤ N / (2 * (N : ℝ) ^ θ) :=
    Nat.floor_le (by positivity)
  have hLpos : (0 : ℝ) < gallagherLength N θ := by exact_mod_cast hL
  have hm := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ) ^ θ)).mp hLle
  rw [div_le_div_iff₀ hN0 (by positivity)]
  nlinarith

/-- Gallagher 1975 p.131, the first step of the method of reference 10 Section 7:
Gallagher 1970 Lemma 1 bounds the p.128 norm of a corrected character amplitude over
the window of radius P over N by pi over 2L times the L2 norm of its window sums of
length L. From the proved discrete Gallagher inequality. -/
theorem energy_window_gallagher {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N r L : ℕ) (θ γ : ℝ) (hL : 0 < L)
    (hR : (N : ℝ) ^ θ / N ≤ 1 / (2 * (L : ℝ))) :
    Real.sqrt (∫ β in Set.Icc (-((N : ℝ) ^ θ / N)) ((N : ℝ) ^ θ / N),
      ‖correctedAmplitude χ N r γ β‖ ^ 2) ≤
    Real.pi / (2 * L) * Real.sqrt (∑ m ∈ range (N + 1 + L),
      ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ r γ) (N + 1) L m‖ ^ 2) := by
  have hsub : Set.Icc (-((N : ℝ) ^ θ / N)) ((N : ℝ) ^ θ / N) ⊆
      Set.Icc (-(1 / (2 * L) : ℝ)) (1 / (2 * L)) := fun β hβ =>
    ⟨by linarith [hβ.1], by linarith [hβ.2]⟩
  have hmono := setIntegral_mono_set
    (integrableOn_corrected_norm_sq χ N r γ (-(1 / (2 * L) : ℝ)) (1 / (2 * L)))
    (Filter.Eventually.of_forall fun β => sq_nonneg ‖correctedAmplitude χ N r γ β‖)
    (Filter.Eventually.of_forall fun β hβ => hsub hβ)
  have h := hmono.trans (corrected_amplitude_short_window_le χ N r L γ hL)
  calc
    _ ≤ Real.sqrt ((Real.pi / (2 * L)) ^ 2 * ∑ m ∈ range (N + 1 + L),
          ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ r γ) (N + 1) L m‖ ^ 2) :=
      Real.sqrt_le_sqrt h
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- Gallagher 1975 p.127 definition of the exceptional zero relative to T equal to P to
the fifth, used on p.131 after display 14. If no conductor at most P lies in the
exceptional set, every zero of a primitive L function of conductor at most P with
height at most P to the fifth lies left of the line 1 minus b over log T. Elementary. -/
theorem nonexceptional_zero_gap {N : ℕ} {θ : ℝ} (hN : 1 ≤ N) (hθ : 0 ≤ θ)
    (hno : ¬ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
      ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ) :
    ∀ k < ⌊(N : ℝ) ^ θ⌋₊, ∀ χ : DirichletCharacter ℂ (k + 1), χ.IsPrimitive →
      ∀ ρ : ℂ, χ.LFunction ρ = 0 → |ρ.im| ≤ ((N : ℝ) ^ θ) ^ 5 →
        ρ.re < 1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) := by
  intro k hk χ hχ ρ hρ him
  by_contra hre
  push_neg at hre
  have hP1 : 1 ≤ (N : ℝ) ^ θ := Real.one_le_rpow (by exact_mod_cast hN) hθ
  have hkP : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ :=
    (Nat.le_floor_iff (by linarith)).mp (Nat.succ_le_of_lt hk)
  have hP5 : (N : ℝ) ^ θ ≤ ((N : ℝ) ^ θ) ^ 5 := le_self_pow₀ hP1 (by norm_num)
  have hk5 : (k : ℝ) + 1 ≤ ((N : ℝ) ^ θ) ^ 5 := by push_cast at hkP; linarith
  exact hno ⟨⟨k, χ⟩, ⟨hk5, hχ, ρ, hρ, hre, him⟩, hkP⟩

/-- CONDITIONAL ON the ExplicitFormula lemmas, via
`LeanLab.Linnik.ExplicitFormula.mean_decay_nonexceptional`; formerly a LEAF.
Gallagher 1975 p.131 display 14, E at most N to the one half over log N times
e to the minus c over theta, "by the method of [10, Section 7]", Gallagher 1970 Invent.
Math. 11 Section 7, in the case with no exceptional zero. After the Gallagher window step
energy_window_gallagher, the remaining content is the mean square of the short interval
corrected prime sums of length about N over 2P, summed over primitive characters of
conductor at most P, given the zero gap of nonexceptional_zero_gap. Its proof needs the
explicit formula for primitive L of s and chi uniform in q, the proved density
estimate density_near_one, and the classical zero free region above height P to the fifth. -/
theorem short_interval_mean_decay :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∀ k < ⌊(N : ℝ) ^ θ⌋₊, ∀ χ : DirichletCharacter ℂ (k + 1), χ.IsPrimitive →
          ∀ ρ : ℂ, χ.LFunction ρ = 0 → |ρ.im| ≤ ((N : ℝ) ^ θ) ^ 5 →
            ρ.re < 1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5)) →
        ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ 0 0) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  exact LeanLab.Linnik.ExplicitFormula.mean_decay_nonexceptional exceptionalStrip
    exceptionalStrip_pos

/-- CONDITIONAL ON short_interval_mean_decay. Gallagher 1975 p.131 display 14 before the exceptional replacement.
If no character in the fixed strip has conductor at most P, the principal
corrected energy decays exponentially. The zero density bound is already proved. -/
theorem energy_decay_without_exception :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (¬ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ) →
        normalizedEnergy N θ 0 0 ≤ C * Real.exp (-c / θ) := by
  obtain ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀2, hleaf⟩ := short_interval_mean_decay
  refine ⟨c, C, θ₀, hc, hC, hθ₀, by linarith, fun θ hθ hθle => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hleaf θ hθ hθle
  refine ⟨max N₀ 4, fun N hN hno => ?_⟩
  have hN4 : 4 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hL, hR⟩ := gallagherLength_spec hθ.le (hθle.trans hθ₀2) hN4
  have hgap := nonexceptional_zero_gap (by omega) hθ.le hno
  have hsum := hN₀ N ((le_max_left _ _).trans hN) hgap
  rw [normalizedEnergy_le_iff (by omega)]
  refine le_trans ?_ hsum
  unfold correctedEnergy
  exact sum_le_sum fun k _ => sum_le_sum fun χ _ =>
    energy_window_gallagher χ N 0 _ θ 0 hL hR

/-- CONDITIONAL ON the ExplicitFormula lemmas via `ExplicitFormula.mean_decay_exceptional_max` with the largest real zero
from `ExplicitFormula.exists_max_real_zero`; it no longer uses the leaf short_interval_mean_decay_exceptional.
Gallagher 1975 p.131 display 14 and the paragraph following it.
For a character in the fixed strip with conductor at most P, removing its real
zero main polynomial gives exponential decay of the corrected energy.
Only the exceptional case is asserted here. -/
theorem energy_decay_with_exception :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∃ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 ∧
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1 ∧
            normalizedEnergy N θ (x.1 + 1) γ ≤ C * Real.exp (-c / θ) := by
  obtain ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀2, hleaf⟩ :=
    LeanLab.Linnik.ExplicitFormula.mean_decay_exceptional_max
  refine ⟨c, C, θ₀, hc, hC, hθ₀, by linarith, fun θ hθ hθle => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hleaf θ hθ hθle
  have hev : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ θ :=
    ((tendsto_rpow_atTop hθ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max N₀ N₁) 4, fun N hN x hx hxP => ?_⟩
  have hN4 : 4 ≤ N := (le_max_right _ _).trans hN
  have hNN₀ : N₀ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNN₁ : N₁ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hP2 : (2 : ℝ) ≤ (N : ℝ) ^ θ := hN₁ N hNN₁
  have hT : (2 : ℝ) ≤ ((N : ℝ) ^ θ) ^ 5 :=
    hP2.trans (le_self_pow₀ (by linarith) (by norm_num))
  obtain ⟨γ, hz, hlo, hlt, hmax⟩ := LeanLab.Linnik.ExplicitFormula.exists_max_real_zero hT x hx
  obtain ⟨hL, hR⟩ := gallagherLength_spec hθ.le (hθle.trans hθ₀2) hN4
  have hsum := hN₀ N hNN₀ x hx hxP γ hz hlo hlt hmax
  refine ⟨γ, hz, hlo, hlt, ?_⟩
  rw [normalizedEnergy_le_iff (by omega)]
  refine le_trans ?_ hsum
  unfold correctedEnergy
  exact sum_le_sum fun k _ => sum_le_sum fun χ _ =>
    energy_window_gallagher χ N (x.1 + 1) _ θ γ hL hR

/-- Gallagher 1975 p.131 display 14 and its exceptional replacement.
Combine the two cases after choosing a real exceptional zero when one exists.
CONDITIONAL ON the supplied energy estimates in the two cases. -/
theorem corrected_energy_decay_of_cases
    (hZero :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (¬ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ) →
        normalizedEnergy N θ 0 0 ≤ C * Real.exp (-c / θ))
    (hExceptional :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∃ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 ∧
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1 ∧
            normalizedEnergy N θ (x.1 + 1) γ ≤ C * Real.exp (-c / θ)) :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ, ∃ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) ∧
          normalizedEnergy N θ r γ ≤ C * Real.exp (-c / θ) := by
  classical
  obtain ⟨cz, Cz, θz, hcz, hCz, hθz, hθz1, hz⟩ := hZero
  obtain ⟨ce, Ce, θe, hce, hCe, hθe, hθe1, he⟩ := hExceptional
  have hC : 0 < max Cz Ce := lt_of_lt_of_le hCz (le_max_left _ _)
  refine ⟨min cz ce, max Cz Ce, min θz θe, lt_min hcz hce, hC,
    lt_min hθz hθe, (min_le_left _ _).trans hθz1, ?_⟩
  intro θ hθ hθlim
  obtain ⟨Nz, hz⟩ := hz θ hθ (hθlim.trans (min_le_left _ _))
  obtain ⟨Ne, he⟩ := he θ hθ (hθlim.trans (min_le_right _ _))
  refine ⟨max Nz Ne, fun N hN => ?_⟩
  have hNz : Nz ≤ N := (le_max_left _ _).trans hN
  have hNe : Ne ≤ N := (le_max_right _ _).trans hN
  have absorb {E c C : ℝ} (hc : min cz ce ≤ c) (hC' : C ≤ max Cz Ce)
      (hE : E ≤ C * Real.exp (-c / θ)) :
      E ≤ max Cz Ce * Real.exp (-min cz ce / θ) := by
    apply hE.trans
    apply mul_le_mul hC' _ (Real.exp_pos _).le hC.le
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hc) hθ.le)
  by_cases hex : ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
      ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ
  · obtain ⟨x, hx, hxP⟩ := hex
    obtain ⟨γ, hγ, hlo, hγ1, henergy⟩ := he N hNe x hx hxP
    refine ⟨x.1 + 1, γ, Or.inr ⟨x, hx, rfl, hxP, hγ, hlo, hγ1⟩, ?_⟩
    exact absorb (min_le_right _ _) (le_max_right _ _) henergy
  · refine ⟨0, 0, Or.inl rfl, ?_⟩
    exact absorb (min_le_left _ _) (le_max_left _ _) (hz N hNz hex)

/-- Gallagher 1975 p.131 display 14, CONDITIONAL ON the two explicit formula cases.
The selected exceptional zero is shared by every corrected character amplitude. -/
theorem corrected_energy_decay_split :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ, ∃ γ : ℝ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ ∧
              x.2.LFunction (γ : ℂ) = 0 ∧
              1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ ∧ γ < 1) ∧
          normalizedEnergy N θ r γ ≤ C * Real.exp (-c / θ) := by
  exact corrected_energy_decay_of_cases energy_decay_without_exception energy_decay_with_exception

end LeanLab.Linnik.Decomp486c






