module

public import LeanLab.Tolev2009.Displays14to16

/-!
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/

@[expose] public section

open Finset Real MeasureTheory

namespace LeanLab.Tolev2009.Displays19to20

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16

/-- Display 12, cited to Tolev 1999 Lemma 12 and page 88.
The L2 integral is over the full unit interval as printed on page 4. -/
def Display12 (A cSup cL2 Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) : Prop :=
  (∀ α ∈ Set.Ioo (-1 / τ) (1 - 1 / τ), α ∉ majorArcs Q τ →
    ‖Kfun lam l₃ K₃ N α‖ ≤ cSup * N * Real.log N ^ (350 - 4 * A)) ∧
  (∫ α in (0 : ℝ)..1, ‖Kfun lam l₃ K₃ N α‖ ^ 2) ≤ cL2 * N * Real.log N ^ (20 : ℕ)

/-- The zero Fourier coefficient is the minor arc L2 mass. -/
theorem norm_Kc_zero (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) :
    ‖Kc a Q τ lam l₃ K₃ N 0‖ = ∫ α, ‖Km Q τ lam l₃ K₃ N α‖ ^ 2 ∂μI a := by
  have h0 : 0 ≤ ∫ α, ‖Km Q τ lam l₃ K₃ N α‖ ^ 2 ∂μI a :=
    integral_nonneg fun _ => sq_nonneg _
  simp only [Kc, Int.cast_zero, zero_mul, ee_zero, mul_one]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]

/-- There is exactly one zero term for each modulus pair in display 18. -/
theorem Wzero_eq (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ) :
    Wzero a Q τ lam l₃ K₃ N K₁ K₂ =
      (K₁ : ℝ) * K₂ * ∫ α, ‖Km Q τ lam l₃ K₃ N α‖ ^ 2 ∂μI a := by
  have hz : ∀ k₁ k₂, (nSet N k₁ k₂).filter (fun n => n = 0) = {0} := by
    intro k₁ k₂
    ext n
    simp only [mem_filter, nSet, mem_Icc, mem_singleton]
    constructor
    · intro h; exact h.2
    · intro h; subst n; simp
  simp only [Wzero, hz, sum_singleton, norm_Kc_zero, sum_const, Nat.card_Ioc, nsmul_eq_mul]
  rw [show 2 * K₁ - K₁ = K₁ by omega, show 2 * K₂ - K₂ = K₂ by omega]
  ring

/-- Integer frequencies make the prime sum one periodic. -/
theorem Sexp_periodic (k l N : ℕ) : Function.Periodic (Sexp k l N) 1 := by
  intro α
  simp only [Sexp]
  refine sum_congr rfl fun p _ => ?_
  have he : ee ((α + 1) * p) = ee (α * p) := by
    rw [show (α + 1) * (p : ℝ) = α * p + p by ring, ee_add,
      show ee (p : ℝ) = 1 from ee_int (p : ℤ), mul_one]
  rw [he]

theorem Kfun_periodic (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) :
    Function.Periodic (Kfun lam l₃ K₃ N) 1 := by
  intro α
  exact sum_congr rfl fun k _ => congrArg ((lam k : ℂ) * ·) (Sexp_periodic k l₃ N α)

/-- The full L2 mass has the paper's normalisation on every unit interval. -/
theorem Kfun_mass_shift (a : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) :
    (∫ α, ‖Kfun lam l₃ K₃ N α‖ ^ 2 ∂μI a) =
      ∫ α in (0 : ℝ)..1, ‖Kfun lam l₃ K₃ N α‖ ^ 2 := by
  have hp : Function.Periodic (fun α => ‖Kfun lam l₃ K₃ N α‖ ^ 2) 1 :=
    fun α => congrArg (fun z : ℂ => ‖z‖ ^ 2) (Kfun_periodic lam l₃ K₃ N α)
  rw [μI, ← intervalIntegral.integral_of_le (by linarith)]
  simpa only [zero_add] using hp.intervalIntegral_add_eq a 0

/-- Restricting to the minor arcs can only decrease the L2 mass. -/
theorem minor_mass_le (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) :
    (∫ α, ‖Km Q τ lam l₃ K₃ N α‖ ^ 2 ∂μI a) ≤
      ∫ α in (0 : ℝ)..1, ‖Kfun lam l₃ K₃ N α‖ ^ 2 := by
  have hK : MB (Kfun lam l₃ K₃ N) :=
    ⟨(continuous_Kfun _ _ _ _).measurable, Bdd.sum _ fun k => (Bdd.const _).mul (bdd_Sexp _ _ _)⟩
  rw [← Kfun_mass_shift a]
  refine integral_mono (mb_Km _ _ _ _ _ _).integrable_normSq hK.integrable_normSq ?_
  intro α
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_indicator_le_norm_self _ _) 2

/-- Display 19 before the size restriction on the two block scales.
Derived from Display12. -/
theorem display19_scales (A cSup cL2 Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ)
    (h12 : Display12 A cSup cL2 Q τ lam l₃ K₃ N) :
    Wzero (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂ ≤
      (K₁ : ℝ) * K₂ * (cL2 * N * Real.log N ^ (20 : ℕ)) := by
  rw [Wzero_eq]
  exact mul_le_mul_of_nonneg_left ((minor_mass_le _ _ _ _ _ _ _).trans h12.2) (by positivity)

/-- Display 19 with precisely the exponent printed on page 7.
Derived from Display12. -/
theorem display19 (A B cSup cL2 Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ)
    (hL : 1 ≤ Real.log N) (hc : 0 ≤ cL2)
    (hK₁ : (K₁ : ℝ) ≤ Real.sqrt N * Real.log N ^ (-B))
    (hK₂ : (K₂ : ℝ) ≤ Real.sqrt N * Real.log N ^ (-B))
    (h12 : Display12 A cSup cL2 Q τ lam l₃ K₃ N) :
    Wzero (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂ ≤ cL2 * Real.log N ^ (20 - 2 * B) * (N : ℝ) ^ 2 := by
  have hL0 : 0 < Real.log N := by linarith
  have hp := mul_le_mul hK₁ hK₂ (Nat.cast_nonneg K₂) (by positivity)
  have hn : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg N)
  calc
    _ ≤ (K₁ : ℝ) * K₂ * (cL2 * N * Real.log N ^ (20 : ℕ)) := display19_scales _ _ _ _ _ _ _ _ _ _ _ h12
    _ ≤ (Real.sqrt N * Real.log N ^ (-B)) * (Real.sqrt N * Real.log N ^ (-B)) *
        (cL2 * N * Real.log N ^ (20 : ℕ)) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = cL2 * (N : ℝ) ^ 2 * (Real.log N ^ (20 : ℝ) * (Real.log N ^ (-B) * Real.log N ^ (-B))) := by
      rw [show Real.log N ^ (20 : ℝ) = Real.log N ^ (20 : ℕ) by norm_cast]
      calc
        _ = cL2 * (Real.sqrt N * Real.sqrt N) * N *
          (Real.log N ^ (20 : ℕ) * (Real.log N ^ (-B) * Real.log N ^ (-B))) := by ring
        _ = _ := by rw [hn]; ring
    _ = _ := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      rw [show (20 : ℝ) + (-B + -B) = 20 - 2 * B by ring]
      ring

/-- Identification with Mathlib Fourier coefficients on the same unit interval. -/
theorem Kc_fourierCoeffOn (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (n : ℤ) :
    Kc a Q τ lam l₃ K₃ N n =
      fourierCoeffOn (show a < a + 1 by linarith)
        (fun α => ((‖Km Q τ lam l₃ K₃ N α‖ ^ 2 : ℝ) : ℂ)) (-n) := by
  rw [Kc, fourierCoeffOn_eq_integral]
  simp only [add_sub_cancel_left, one_div, inv_one, one_smul, neg_neg, smul_eq_mul]
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine integral_congr_ae (ae_of_all _ fun α => ?_)
  dsimp only
  rw [fourier_coe_apply]
  simp only [add_sub_cancel_left, Complex.ofReal_one, div_one]
  simp only [ee, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring_nf

/-- Finite Bessel inequality for the coefficients used in display 20. -/
theorem Kc_bessel (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (s : Finset ℤ) :
    ∑ n ∈ s, ‖Kc a Q τ lam l₃ K₃ N n‖ ^ 2 ≤
      ∫ α, ‖Km Q τ lam l₃ K₃ N α‖ ^ 4 ∂μI a := by
  let f := fun α => ((‖Km Q τ lam l₃ K₃ N α‖ ^ 2 : ℝ) : ℂ)
  have hf : MB f := (mb_Km _ _ _ _ _ _).normSq
  obtain ⟨C, hC⟩ := hf.2
  have hLp : MemLp f 2 (μI a) :=
    MemLp.of_bound hf.1.aestronglyMeasurable C (ae_of_all _ hC)
  have hsum := hasSum_sq_fourierCoeffOn (show a < a + 1 by linarith) hLp
  have h := sum_le_hasSum (s.image (fun n : ℤ => -n)) (fun _ _ => sq_nonneg _) hsum
  rw [sum_image (fun x _ y _ hxy => neg_injective hxy)] at h
  simp only [add_sub_cancel_left, inv_one, one_smul] at h
  dsimp only [f] at h
  simp_rw [← Kc_fourierCoeffOn] at h
  refine h.trans_eq ?_
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine integral_congr_ae (ae_of_all _ fun α => ?_)
  dsimp only
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖Km Q τ lam l₃ K₃ N α‖)]
  ring

/-- The signed nonzero frequencies used in display 20. -/
def nonzeroSet (N : ℕ) : Finset ℤ := (Icc (-(N : ℤ)) N).filter (fun n => n ≠ 0)

/-- Number of positive divisors of the absolute value of an integer. -/
def divisorCount (n : ℤ) : ℕ := n.natAbs.divisors.card

/-- The elementary divisor fourth moment cited on page 7, with signed frequencies
and exponent 16 to absorb the square root into L to the eighth. -/
def DivisorFourthMoment (N : ℕ) (c : ℝ) : Prop :=
  ∑ n ∈ nonzeroSet N, (divisorCount n : ℝ) ^ 4 ≤ c * N * Real.log N ^ (16 : ℕ)

/-- Any positive moduli dividing a nonzero integer inject into its positive divisors. -/
theorem divisor_filter_card_le (s : Finset ℕ) (_hs : ∀ k ∈ s, 1 ≤ k) (n : ℤ) (hn : n ≠ 0) :
    (s.filter (fun k : ℕ => (k : ℤ) ∣ n)).card ≤ divisorCount n := by
  apply card_le_card
  intro k hk
  rw [mem_filter] at hk
  exact Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp hk.2, Int.natAbs_ne_zero.mpr hn⟩

/-- The nonzero Fourier sum for any two finite modulus sets. -/
noncomputable def starSum (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (s t : Finset ℕ) : ℝ :=
  ∑ x ∈ s, ∑ y ∈ t, ∑ n ∈ (nSet N x y).filter (fun n => n ≠ 0),
    ‖Kc a Q τ lam l₃ K₃ N n‖

/-- Regroup the nonzero terms by frequency before counting divisors. -/
theorem starSum_regroup (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (s t : Finset ℕ) :
    starSum a Q τ lam l₃ K₃ N s t =
      ∑ n ∈ nonzeroSet N, ∑ x ∈ s, ∑ y ∈ t,
        if (x : ℤ) ∣ n ∧ (y : ℤ) ∣ n then ‖Kc a Q τ lam l₃ K₃ N n‖ else 0 := by
  unfold starSum
  have he : ∀ x y, (nSet N x y).filter (fun n => n ≠ 0) =
      (nonzeroSet N).filter (fun n => (x : ℤ) ∣ n ∧ (y : ℤ) ∣ n) := by
    intro x y
    ext n
    simp only [nSet, nonzeroSet, mem_filter]
    tauto
  simp_rw [he, sum_filter]
  simp_rw [sum_comm (s := t) (t := nonzeroSet N)]
  rw [sum_comm]

/-- Two positive modulus sets give at most the square of the divisor count pairs. -/
theorem divisor_pair_sum_le (s t : Finset ℕ) (hs : ∀ k ∈ s, 1 ≤ k)
    (ht : ∀ k ∈ t, 1 ≤ k) (n : ℤ) (hn : n ≠ 0) (X : ℝ) (hX : 0 ≤ X) :
    (∑ x ∈ s, ∑ y ∈ t, if (x : ℤ) ∣ n ∧ (y : ℤ) ∣ n then X else 0) ≤
      (divisorCount n : ℝ) ^ 2 * X := by
  have he : (∑ x ∈ s, ∑ y ∈ t, if (x : ℤ) ∣ n ∧ (y : ℤ) ∣ n then X else 0) =
      ∑ x ∈ s.filter (fun x : ℕ => (x : ℤ) ∣ n), ∑ y ∈ t.filter (fun y : ℕ => (y : ℤ) ∣ n), X := by
    simp only [sum_filter]
    refine sum_congr rfl fun x _ => ?_
    by_cases hx : (x : ℤ) ∣ n <;> simp [hx]
  rw [he]
  simp only [sum_const, nsmul_eq_mul]
  have hcs : ((s.filter (fun x : ℕ => (x : ℤ) ∣ n)).card : ℝ) ≤ divisorCount n :=
    by exact_mod_cast divisor_filter_card_le s hs n hn
  have hct : ((t.filter (fun x : ℕ => (x : ℤ) ∣ n)).card : ℝ) ≤ divisorCount n :=
    by exact_mod_cast divisor_filter_card_le t ht n hn
  have hmul := mul_le_mul hcs hct (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_right hmul hX

/-- The divisor and Cauchy steps of display 20, with no analytic estimate assumed. -/
theorem starSum_cauchy (a Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (s t : Finset ℕ)
    (hs : ∀ k ∈ s, 1 ≤ k) (ht : ∀ k ∈ t, 1 ≤ k) :
    starSum a Q τ lam l₃ K₃ N s t ≤
      Real.sqrt (∑ n ∈ nonzeroSet N, (divisorCount n : ℝ) ^ 4) *
        Real.sqrt (∫ α, ‖Km Q τ lam l₃ K₃ N α‖ ^ 4 ∂μI a) := by
  rw [starSum_regroup]
  have hcs := Real.sum_sqrt_mul_sqrt_le (nonzeroSet N)
    (f := fun n => (divisorCount n : ℝ) ^ 4)
    (g := fun n => ‖Kc a Q τ lam l₃ K₃ N n‖ ^ 2)
    (fun _ => by positivity) (fun _ => by positivity)
  have he : ∀ n : ℤ, Real.sqrt ((divisorCount n : ℝ) ^ 4) = (divisorCount n : ℝ) ^ 2 := by
    intro n
    rw [show (divisorCount n : ℝ) ^ 4 = ((divisorCount n : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  simp only [he, Real.sqrt_sq (norm_nonneg _)] at hcs
  refine (sum_le_sum fun n hn => divisor_pair_sum_le s t hs ht n (mem_filter.mp hn).2 _
    (norm_nonneg _)).trans (hcs.trans ?_)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Kc_bessel a Q τ lam l₃ K₃ N _))
    (Real.sqrt_nonneg _)

/-- Interpolation between the L2 mass and a minor arc supremum bound. -/
theorem fourth_mass_le (a Q τ S : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ)
    (_hS : 0 ≤ S) (hb : ∀ᵐ α ∂μI a, ‖Km Q τ lam l₃ K₃ N α‖ ≤ S) :
    (∫ α, ‖Km Q τ lam l₃ K₃ N α‖ ^ 4 ∂μI a) ≤
      S ^ 2 * ∫ α, ‖Km Q τ lam l₃ K₃ N α‖ ^ 2 ∂μI a := by
  have hi4 : Integrable (fun α => ‖Km Q τ lam l₃ K₃ N α‖ ^ 4) (μI a) := by
    have hi := ((mb_Km Q τ lam l₃ K₃ N).normSq).integrable_normSq (μ := μI a)
    convert hi using 1
    ext α
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖Km Q τ lam l₃ K₃ N α‖)]
    ring
  rw [← integral_const_mul]
  refine integral_mono_ae hi4 ((mb_Km _ _ _ _ _ _).integrable_normSq.const_mul _) ?_
  filter_upwards [hb] with α hα
  have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hα 2)
    (sq_nonneg ‖Km Q τ lam l₃ K₃ N α‖)
  nlinarith

/-- Display 20 for arbitrary positive modulus sets.
Derived from Display12 and the cited divisor fourth moment. -/
theorem display20_sets (A cSup cL2 cD Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N : ℕ)
    (s t : Finset ℕ) (hs : ∀ k ∈ s, 1 ≤ k) (ht : ∀ k ∈ t, 1 ≤ k)
    (hL : 1 ≤ Real.log N) (hcSup : 0 ≤ cSup) (hcL2 : 0 ≤ cL2) (hcD : 0 ≤ cD)
    (h12 : Display12 A cSup cL2 Q τ lam l₃ K₃ N) (hD : DivisorFourthMoment N cD) :
    starSum (-1 / τ) Q τ lam l₃ K₃ N s t ≤
      Real.sqrt cD * cSup * Real.sqrt cL2 * (N : ℝ) ^ 2 * Real.log N ^ (400 - 4 * A) := by
  let S := cSup * N * Real.log N ^ (350 - 4 * A)
  let M := ∫ α in (0 : ℝ)..1, ‖Kfun lam l₃ K₃ N α‖ ^ 2
  have hS : 0 ≤ S := by positivity
  have hb : ∀ᵐ α ∂μI (-1 / τ), ‖Km Q τ lam l₃ K₃ N α‖ ≤ S := by
    have hm : μI (-1 / τ) = volume.restrict (Set.Ioo (-1 / τ) (-1 / τ + 1)) :=
      (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
    rw [hm]
    filter_upwards [ae_restrict_mem (μ := volume) (s := Set.Ioo (-1 / τ) (-1 / τ + 1))
      measurableSet_Ioo] with α hα
    by_cases hm : α ∈ (majorArcs Q τ)ᶜ
    · simpa only [Km, Set.indicator_of_mem hm] using
        h12.1 α (by convert hα using 1; ring) hm
    · simp only [Km, Set.indicator_of_notMem hm, norm_zero]
      exact hS
  have h4 := fourth_mass_le (-1 / τ) Q τ S lam l₃ K₃ N hS hb
  have hm := minor_mass_le (-1 / τ) Q τ lam l₃ K₃ N
  have hroot : Real.sqrt (∫ α, ‖Km Q τ lam l₃ K₃ N α‖ ^ 4 ∂μI (-1 / τ)) ≤ S * Real.sqrt M := by
    refine (Real.sqrt_le_sqrt (h4.trans (mul_le_mul_of_nonneg_left hm (sq_nonneg _)))).trans_eq ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hS]
  have hdroot : Real.sqrt (∑ n ∈ nonzeroSet N, (divisorCount n : ℝ) ^ 4) ≤
      Real.sqrt cD * Real.sqrt N * Real.log N ^ (8 : ℕ) := by
    refine (Real.sqrt_le_sqrt hD).trans_eq ?_
    rw [show Real.log N ^ (16 : ℕ) = (Real.log N ^ (8 : ℕ)) ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul hcD, Real.sqrt_sq (by positivity)]
  have hw : starSum (-1 / τ) Q τ lam l₃ K₃ N s t ≤
      Real.sqrt cD * Real.log N ^ (8 : ℝ) * Real.sqrt N * (S * Real.sqrt M) := by
    refine (starSum_cauchy _ _ _ _ _ _ _ _ _ hs ht).trans ?_
    have h := mul_le_mul hdroot hroot (Real.sqrt_nonneg _) (by positivity)
    convert h using 1; norm_cast; ring
  apply Wstar_bookkeeping hL (Nat.cast_nonneg N) hcSup hcL2 (Real.sqrt_nonneg cD)
    (le_refl S) (show M ≤ cL2 * N * Real.log N ^ (20 : ℝ) by
      simpa only [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using h12.2) hw

/-- Display 20 for the original Vblk scales.
Derived from Display12 and the cited divisor fourth moment. -/
theorem display20 (A cSup cL2 cD Q τ : ℝ) (lam : ℕ → ℝ) (l₃ K₃ N K₁ K₂ : ℕ)
    (hL : 1 ≤ Real.log N) (hcSup : 0 ≤ cSup) (hcL2 : 0 ≤ cL2) (hcD : 0 ≤ cD)
    (h12 : Display12 A cSup cL2 Q τ lam l₃ K₃ N) (hD : DivisorFourthMoment N cD) :
    Wstar (-1 / τ) Q τ lam l₃ K₃ N K₁ K₂ ≤
      Real.sqrt cD * cSup * Real.sqrt cL2 * (N : ℝ) ^ 2 * Real.log N ^ (400 - 4 * A) := by
  exact display20_sets _ _ _ _ _ _ _ _ _ _ _ _
    (fun k hk => by have := (mem_Ioc.mp hk).1; omega)
    (fun k hk => by have := (mem_Ioc.mp hk).1; omega) hL hcSup hcL2 hcD h12 hD

end LeanLab.Tolev2009.Displays19to20
