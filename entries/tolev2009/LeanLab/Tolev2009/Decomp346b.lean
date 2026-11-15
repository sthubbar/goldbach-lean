module

public import LeanLab.Tolev2009.ScalarEnvelope346
public import LeanLab.Tolev2009.LcmAverage346

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 page 9 to 10, O2.
The scalar rectangular mean is proved. The exact assemblies are derived from it.
-/

@[expose] public section

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.Decomp346b
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp314a LeanLab.Tolev2009.Progression346
open LeanLab.Tolev2009.ScalarEnvelope346
open LeanLab.Tolev2009.Discrepancy346 LeanLab.HeathBrown1985

set_option maxHeartbeats 1000000

/-- `1 + log K` is nonnegative, including `K = 0`. -/
private theorem one_add_log_nat_nonneg (K : ℕ) : (0 : ℝ) ≤ 1 + Real.log K := by
  rcases Nat.eq_zero_or_pos K with h | h
  · simp [h]
  · have : (0 : ℝ) ≤ Real.log K := Real.log_natCast_nonneg K
    linarith

/-- Harmonic sums against `log`. -/
private theorem sum_Icc_inv_le (K : ℕ) :
    (∑ m ∈ Icc 1 K, ((m : ℝ))⁻¹) ≤ 1 + Real.log K := by
  have h : (harmonic K : ℝ) ≤ 1 + Real.log K := by
    have := harmonic_le_one_add_log K
    exact_mod_cast this
  calc (∑ m ∈ Icc 1 K, ((m : ℝ))⁻¹) = (harmonic K : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rfl
    _ ≤ _ := h

/-- The divisor count is at most `k / φ k`. -/
private theorem card_divisors_mul_totient (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ≤ (k.totient : ℝ) * (k.divisors.card : ℝ) := by
  have hsum : (∑ d ∈ k.divisors, (d.totient : ℝ)) = (k : ℝ) := by
    have := Nat.sum_totient k
    exact_mod_cast this
  have hle : (∑ d ∈ k.divisors, (d.totient : ℝ)) ≤
      ∑ _d ∈ k.divisors, (k.totient : ℝ) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    have hdvd : d ∣ k := (Nat.mem_divisors.mp hd).1
    have hpos : 0 < k.totient := Nat.totient_pos.mpr hk
    have hdvd' : d.totient ∣ k.totient := Nat.totient_dvd_of_dvd hdvd
    have : d.totient ≤ k.totient := Nat.le_of_dvd hpos hdvd'
    exact_mod_cast this
  rw [hsum] at hle
  have hcardsum : (∑ _d ∈ k.divisors, (k.totient : ℝ)) =
      (k.totient : ℝ) * (k.divisors.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hcardsum] at hle
  exact hle

/-- `1/φ k ≤ τ k / k`. -/
private theorem inv_totient_le (k : ℕ) (hk : 1 ≤ k) :
    ((k.totient : ℝ))⁻¹ ≤ (k.divisors.card : ℝ) / (k : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ht0 : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  rw [show ((k.totient : ℝ))⁻¹ = 1 / (k.totient : ℝ) by rw [one_div],
    div_le_div_iff₀ ht0 hk0, one_mul, mul_comm]
  exact card_divisors_mul_totient k hk

/-- A filtered reciprocal sum over a divisibility condition. -/
private theorem sum_filter_dvd_inv (m K : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ (Icc 1 K).filter (fun k => m ∣ k), ((k : ℝ))⁻¹) =
      ∑ j ∈ Icc 1 (K / m), ((m * j : ℕ) : ℝ)⁻¹ := by
  have hm0 : 0 < m := by omega
  have hset : (Icc 1 K).filter (fun k => m ∣ k) = (Icc 1 (K / m)).image (fun j => m * j) := by
    ext k
    constructor
    · intro hk
      obtain ⟨hkI, hdvd⟩ := Finset.mem_filter.mp hk
      obtain ⟨j, rfl⟩ := hdvd
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h; simp at hkI
        · exact h
      refine Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj1, ?_⟩, rfl⟩
      exact (Nat.le_div_iff_mul_le hm0).mpr (by rw [Nat.mul_comm]; exact (Finset.mem_Icc.mp hkI).2)
    · intro hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hmj : 1 ≤ m * j := by simpa using Nat.mul_le_mul hm hj1
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmj, ?_⟩, ⟨j, rfl⟩⟩
      calc m * j ≤ m * (K / m) := Nat.mul_le_mul_left m (Finset.mem_Icc.mp hj).2
        _ ≤ K := Nat.mul_div_le K m
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.mul_left_cancel hm0 hab

/-- `Σ_{k ≤ K} τ k / k ≪ log² K`. -/
private theorem sum_card_divisors_div_le (K : ℕ) :
    (∑ k ∈ Icc 1 K, (k.divisors.card : ℝ) / (k : ℝ)) ≤ (1 + Real.log K) ^ 2 := by
  have hpoint : ∀ k ∈ Icc 1 K, (k.divisors.card : ℝ) / (k : ℝ) =
      ∑ d ∈ Icc 1 K, if d ∣ k then ((k : ℝ))⁻¹ else 0 := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have kK : k ≤ K := (Finset.mem_Icc.mp hk).2
    have hkk : k ≠ 0 := by omega
    have hdiv : (Icc 1 K).filter (fun d => d ∣ k) = k.divisors := by
      ext d
      constructor
      · intro hd
        exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hkk⟩
      · intro hd
        have hdk : d ∣ k := (Nat.mem_divisors.mp hd).1
        have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdk (by omega)
        have hdk' : d ≤ k := Nat.le_of_dvd (by omega) hdk
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, by omega⟩, hdk⟩
    have hfil : (∑ d ∈ Icc 1 K, if d ∣ k then ((k : ℝ))⁻¹ else 0) =
        ∑ d ∈ (Icc 1 K).filter (fun d => d ∣ k), ((k : ℝ))⁻¹ := (Finset.sum_filter _ _).symm
    rw [hfil, hdiv, div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]
  calc (∑ k ∈ Icc 1 K, (k.divisors.card : ℝ) / (k : ℝ))
      = ∑ k ∈ Icc 1 K, ∑ d ∈ Icc 1 K, if d ∣ k then ((k : ℝ))⁻¹ else 0 :=
        Finset.sum_congr rfl hpoint
    _ = ∑ d ∈ Icc 1 K, ∑ k ∈ Icc 1 K, if d ∣ k then ((k : ℝ))⁻¹ else 0 := Finset.sum_comm
    _ ≤ ∑ d ∈ Icc 1 K, ((d : ℝ))⁻¹ * (1 + Real.log K) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
        rw [← Finset.sum_filter]
        calc (∑ k ∈ (Icc 1 K).filter (fun k => d ∣ k), ((k : ℝ))⁻¹)
            = ∑ j ∈ Icc 1 (K / d), ((d * j : ℕ) : ℝ)⁻¹ := sum_filter_dvd_inv d K hd1
          _ = ((d : ℝ))⁻¹ * ∑ j ∈ Icc 1 (K / d), ((j : ℝ))⁻¹ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Nat.cast_mul, mul_inv]
          _ ≤ ((d : ℝ))⁻¹ * (1 + Real.log K) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rcases Nat.eq_zero_or_pos (K / d) with h0 | hpos
              · rw [h0]
                simp only [Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), Finset.sum_empty]
                exact one_add_log_nat_nonneg K
              · have hle : ((K / d : ℕ) : ℝ) ≤ (K : ℝ) := by
                  exact_mod_cast Nat.div_le_self K d
                have hlog : Real.log ((K / d : ℕ) : ℝ) ≤ Real.log K :=
                  Real.log_le_log (by exact_mod_cast hpos) hle
                linarith [sum_Icc_inv_le (K / d)]
    _ = (∑ d ∈ Icc 1 K, ((d : ℝ))⁻¹) * (1 + Real.log K) := by rw [Finset.sum_mul]
    _ ≤ (1 + Real.log K) * (1 + Real.log K) := by
        refine mul_le_mul_of_nonneg_right (sum_Icc_inv_le K) ?_
        linarith [one_add_log_nat_nonneg K]
    _ = (1 + Real.log K) ^ 2 := by ring

/-- `Σ_{k ≤ K} 1/φ(k) ≪ log² K`. -/
private theorem sum_inv_totient_le (K : ℕ) :
    (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ≤ (1 + Real.log K) ^ 2 := by
  refine (Finset.sum_le_sum (fun k hk => inv_totient_le k (Finset.mem_Icc.mp hk).1)).trans
    (sum_card_divisors_div_le K)

/-! ### The degree-two factorization of `scalarMean 2` -/

/-- `scalarArc 2` at a tripled index is the explicit three-term product. -/
private theorem scalarArc_two (Q : ℝ) (N q k1 k2 k3 : ℕ) :
    scalarArc 2 Q N q ![k1, k2, k3] =
      (2 * Q / (N : ℝ)) *
        (errorProfile Q N q k1 * errorProfile Q N q k2 * mainProfile N q k3 +
         errorProfile Q N q k1 * mainProfile N q k2 * errorProfile Q N q k3 +
         mainProfile N q k1 * errorProfile Q N q k2 * errorProfile Q N q k3) := by
  unfold scalarArc positivePart
  simp

/-- A product of three one-dimensional sums. -/
private theorem triple_factor {I1 I2 I3 : Finset ℕ} (f1 f2 f3 : ℕ → ℝ) :
    (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f1 k1 * f2 k2 * f3 k3)
      = (∑ k1 ∈ I1, f1 k1) * (∑ k2 ∈ I2, f2 k2) * (∑ k3 ∈ I3, f3 k3) := by
  have h1 : (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f1 k1 * f2 k2 * f3 k3)
      = ∑ k1 ∈ I1, ∑ k2 ∈ I2, (f1 k1 * f2 k2) * (∑ k3 ∈ I3, f3 k3) := by
    refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun k2 _ => ?_))
    rw [Finset.mul_sum]
  have h2 : (∑ k1 ∈ I1, ∑ k2 ∈ I2, (f1 k1 * f2 k2) * (∑ k3 ∈ I3, f3 k3))
      = (∑ k1 ∈ I1, ∑ k2 ∈ I2, f1 k1 * f2 k2) * (∑ k3 ∈ I3, f3 k3) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k1 _ => ?_)
    rw [Finset.sum_mul]
  have h3 : (∑ k1 ∈ I1, ∑ k2 ∈ I2, f1 k1 * f2 k2)
      = (∑ k1 ∈ I1, f1 k1) * (∑ k2 ∈ I2, f2 k2) :=
    (Finset.sum_mul_sum _ _ _ _).symm
  rw [h1, h2, h3]

/-- Splitting a three-term summand at each of three sum levels. -/
private theorem sum3_add {I : Finset ℕ} (f g h : ℕ → ℝ) :
    (∑ x ∈ I, (f x + g x + h x)) = ∑ x ∈ I, f x + ∑ x ∈ I, g x + ∑ x ∈ I, h x := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- The degree-two positive polynomial as a sum of three products of sums. -/
private theorem triple_q {I1 I2 I3 : Finset ℕ} (d1 b2 : ℕ → ℝ) :
    (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3,
        (d1 k1 * d1 k2 * b2 k3 + d1 k1 * b2 k2 * d1 k3 + b2 k1 * d1 k2 * d1 k3))
      = (∑ k1 ∈ I1, d1 k1) * (∑ k2 ∈ I2, d1 k2) * (∑ k3 ∈ I3, b2 k3)
        + (∑ k1 ∈ I1, d1 k1) * (∑ k2 ∈ I2, b2 k2) * (∑ k3 ∈ I3, d1 k3)
        + (∑ k1 ∈ I1, b2 k1) * (∑ k2 ∈ I2, d1 k2) * (∑ k3 ∈ I3, d1 k3) := by
  simp only [sum3_add]
  rw [triple_factor, triple_factor, triple_factor]

/-- A constant pulls out of three `k`-sums. -/
private theorem sum_const_mul_three {I1 I2 I3 : Finset ℕ} (c : ℝ) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, c * f k1 k2 k3)
      = c * ∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  rw [Finset.mul_sum]

/-- The `q`-sum moves outside three `k`-sums. -/
private theorem swap_four {I1 I2 I3 Iq : Finset ℕ} (f : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, ∑ q ∈ Iq, f k1 k2 k3 q)
      = ∑ q ∈ Iq, ∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 q := by
  have h3 : ∀ k1 k2, (∑ k3 ∈ I3, ∑ q ∈ Iq, f k1 k2 k3 q)
      = ∑ q ∈ Iq, ∑ k3 ∈ I3, f k1 k2 k3 q := fun _ _ => Finset.sum_comm
  have h2 : ∀ k1, (∑ k2 ∈ I2, ∑ q ∈ Iq, ∑ k3 ∈ I3, f k1 k2 k3 q)
      = ∑ q ∈ Iq, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 q := fun _ => Finset.sum_comm
  have h1 : (∑ k1 ∈ I1, ∑ q ∈ Iq, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 q)
      = ∑ q ∈ Iq, ∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 q := Finset.sum_comm
  calc (∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ k3 ∈ I3, ∑ q ∈ Iq, f k1 k2 k3 q)
      = ∑ k1 ∈ I1, ∑ k2 ∈ I2, ∑ q ∈ Iq, ∑ k3 ∈ I3, f k1 k2 k3 q := by simp only [h3]
    _ = ∑ k1 ∈ I1, ∑ q ∈ Iq, ∑ k2 ∈ I2, ∑ k3 ∈ I3, f k1 k2 k3 q := by simp only [h2]
    _ = _ := h1

/-- The exact degree-two rectangular sum, factorized into `q`-indexed products of
one-dimensional sums of the error and main profiles. -/
private theorem scalarMean_two_eq (A : ℝ) (N : ℕ) :
    scalarMean 2 A N =
      (2 * Qof A N / (N : ℝ)) * ∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
        (((∑ k ∈ Icc 1 (Dyadic.cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k)
            * (∑ k ∈ Icc 1 (Dyadic.cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k)
            * (∑ k ∈ Icc 1 (Dyadic.cutoff3 (10 ^ 4 * A) N), mainProfile N q k))
          + ((∑ k ∈ Icc 1 (Dyadic.cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k)
            * (∑ k ∈ Icc 1 (Dyadic.cutoff (10 ^ 4 * A) N), mainProfile N q k)
            * (∑ k ∈ Icc 1 (Dyadic.cutoff3 (10 ^ 4 * A) N), errorProfile (Qof A N) N q k))
          + ((∑ k ∈ Icc 1 (Dyadic.cutoff (10 ^ 4 * A) N), mainProfile N q k)
            * (∑ k ∈ Icc 1 (Dyadic.cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k)
            * (∑ k ∈ Icc 1 (Dyadic.cutoff3 (10 ^ 4 * A) N), errorProfile (Qof A N) N q k))) := by
  set I1 : Finset ℕ := Icc 1 (Dyadic.cutoff (10 ^ 4 * A) N) with hI1
  set I3 : Finset ℕ := Icc 1 (Dyadic.cutoff3 (10 ^ 4 * A) N) with hI3
  set Iq : Finset ℕ := Icc 1 ⌊Qof A N⌋₊ with hIq
  have hunfold : scalarMean 2 A N = ∑ k1 ∈ I1, ∑ k2 ∈ I1, ∑ k3 ∈ I3, ∑ q ∈ Iq,
      scalarArc 2 (Qof A N) N q ![k1, k2, k3] := by
    simp only [scalarMean, scalarEnvelope, hI1, hI3, hIq]
  rw [hunfold, swap_four]
  simp only [scalarArc_two]
  have hper : ∀ q ∈ Iq,
      (∑ k1 ∈ I1, ∑ k2 ∈ I1, ∑ k3 ∈ I3,
        (2 * Qof A N / (N : ℝ)) *
          (errorProfile (Qof A N) N q (k1) * errorProfile (Qof A N) N q (k2) *
              mainProfile N q (k3) +
            errorProfile (Qof A N) N q (k1) * mainProfile N q (k2) *
              errorProfile (Qof A N) N q (k3) +
            mainProfile N q (k1) * errorProfile (Qof A N) N q (k2) *
              errorProfile (Qof A N) N q (k3)))
        = (2 * Qof A N / (N : ℝ)) *
          (((∑ k ∈ I1, errorProfile (Qof A N) N q k) * (∑ k ∈ I1, errorProfile (Qof A N) N q k)
              * (∑ k ∈ I3, mainProfile N q k))
            + ((∑ k ∈ I1, errorProfile (Qof A N) N q k) * (∑ k ∈ I1, mainProfile N q k)
              * (∑ k ∈ I3, errorProfile (Qof A N) N q k))
            + ((∑ k ∈ I1, mainProfile N q k) * (∑ k ∈ I1, errorProfile (Qof A N) N q k)
              * (∑ k ∈ I3, errorProfile (Qof A N) N q k))) := by
    intro q _
    rw [sum_const_mul_three]
    congr 1
    exact triple_q (d1 := fun k => errorProfile (Qof A N) N q k)
      (b2 := fun k => mainProfile N q k)
  rw [Finset.sum_congr rfl hper, ← Finset.mul_sum]


/-! ### The one-dimensional profile sums -/

/-- The error profile sums to a theta sum plus `K` copies of the log profile. -/
private theorem error_sum_eq (Q : ℝ) (N q K : ℕ) :
    (∑ k ∈ Icc 1 K, errorProfile Q N q k) =
      (1 + 2 * π) * Q *
        ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) := by
  unfold errorProfile
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
    Nat.add_sub_cancel]

/-- The main profile sums to `N q` times the reciprocal totient sum. -/
private theorem main_sum_eq (N q K : ℕ) :
    (∑ k ∈ Icc 1 K, mainProfile N q k)
      = (N : ℝ) * q * ∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹ := by
  unfold mainProfile
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [div_eq_mul_inv]

/-- The averaged squared theta discrepancy at `r = 2` of `product_lcm_average`. -/
private theorem theta_sq_average (A : ℝ) (hA : 10 ^ 4 ≤ A) :
    ∃ C : ℝ, ∀ (N : ℕ), 3 ≤ N → 1 ≤ Real.log N → ∀ K : ℕ,
      K ≤ Dyadic.cutoff (10 ^ 4 * A) N →
        (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
            (∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 / (q : ℝ) ^ 2) ≤
          Hn ⌊Qof A N⌋₊ ^ 4 * (C * (N : ℝ) / Real.log N ^ (100 * A)) ^ 2 := by
  obtain ⟨C, hC⟩ := LeanLab.Tolev2009.LcmAverage346.product_lcm_average A hA
  refine ⟨C, fun N hN hL K hK => ?_⟩
  have h := hC N hN hL 2 (by norm_num) (fun _ : Fin 2 => K) (fun _ => hK)
  simpa [Fin.prod_univ_two, Nat.reducePow, pow_two] using h

/-- `log N ≥ 1` at `N ≥ 3`. -/
private theorem one_le_log {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  linarith [Real.exp_one_lt_d9]

/-- The totient harmonic sum at the first cutoff. -/
private theorem Qof_rpow_eq (A : ℝ) (N : ℕ) : Qof A N = Real.log N ^ (20 * A) := rfl

/-- `Hn` at the first cutoff is at most `21 A log N`. -/
private theorem Hn_le (A : ℝ) (hA : 10 ^ 4 ≤ A) {N : ℕ} (hN : 3 ≤ N) :
    Hn ⌊Qof A N⌋₊ ≤ 21 * A * Real.log N := by
  have hL1 : 1 ≤ Real.log N := one_le_log hN
  have hL : 0 < Real.log N := by linarith
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hQpos : (0 : ℝ) < Qof A N := Real.rpow_pos_of_pos hL _
  have hQ1 : 1 ≤ Qof A N := Real.one_le_rpow hL1 (by linarith : (0 : ℝ) ≤ 20 * A)
  have hlogQ : Real.log (Qof A N) = 20 * A * Real.log (Real.log N) := by
    rw [Qof_rpow_eq A N, Real.log_rpow hL]
  have hlogL : Real.log (Real.log N) ≤ Real.log N := Real.log_le_self hL.le
  have hstep : Hn ⌊Qof A N⌋₊ ≤ 1 + Real.log (Qof A N) := by
    unfold Hn
    refine (sum_Icc_inv_le ⌊Qof A N⌋₊).trans ?_
    rcases Nat.eq_zero_or_pos ⌊Qof A N⌋₊ with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      have h0' : (0 : ℝ) ≤ Real.log (Qof A N) := Real.log_nonneg hQ1
      linarith
    · have hle : ((⌊Qof A N⌋₊ : ℕ) : ℝ) ≤ Qof A N := Nat.floor_le hQpos.le
      have hpos' : (0 : ℝ) < ((⌊Qof A N⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpos
      have := Real.log_le_log hpos' hle
      linarith
  rw [hlogQ] at hstep
  nlinarith

/-- `log q ≤ 20 A log N` below the first cutoff. -/
private theorem log_q_le (A : ℝ) (hA : 10 ^ 4 ≤ A) {N q : ℕ} (hN : 3 ≤ N)
    (hq : (q : ℝ) ≤ Qof A N) :
    Real.log q ≤ 20 * A * Real.log N := by
  have hL1 : 1 ≤ Real.log N := one_le_log hN
  have hL : (0 : ℝ) < Real.log N := by linarith
  have h20 : (0 : ℝ) ≤ 20 * A := by linarith
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h
    simp only [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg h20 hL.le
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast h
    have h1 : Real.log q ≤ Real.log (Qof A N) := Real.log_le_log hq0 hq
    have h2 : Real.log (Qof A N) = 20 * A * Real.log (Real.log N) := by
      rw [Qof_rpow_eq A N, Real.log_rpow hL]
    have h3 : Real.log (Real.log N) ≤ Real.log N := Real.log_le_self hL.le
    have h4 := mul_le_mul_of_nonneg_left h3 h20
    rw [h2] at h1
    linarith

/-- The logarithmic profile of one modulus. -/
private theorem c_q_le (A : ℝ) (hA : 10 ^ 4 ≤ A) {N q : ℕ} (hN : 3 ≤ N) (hq1 : 1 ≤ q)
    (hq : (q : ℝ) ≤ Qof A N) :
    (Real.log q / Real.log 2 * Real.log N) / q ≤ 40 * A * Real.log N ^ 2 / q := by
  have hL1 : 1 ≤ Real.log N := one_le_log hN
  have hL : (0 : ℝ) < Real.log N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by nlinarith [Real.log_two_gt_d9]
  have hlogq := log_q_le A hA hN hq
  have hlq : (0 : ℝ) ≤ Real.log q := Real.log_natCast_nonneg q
  have hratio : Real.log q / Real.log 2 ≤ 2 * Real.log q := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log 2)]
    nlinarith
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hnum : Real.log q / Real.log 2 * Real.log N ≤ 40 * A * Real.log N ^ 2 := by
    have h2 : Real.log q / Real.log 2 * Real.log N ≤ 2 * Real.log q * Real.log N :=
      mul_le_mul_of_nonneg_right hratio hL.le
    have h3 : 2 * Real.log q * Real.log N ≤ 2 * (20 * A * Real.log N) * Real.log N := by
      have hL2 : (0 : ℝ) ≤ 2 * Real.log N := by linarith
      nlinarith [hlogq, hL2]
    nlinarith [h2, h3]
  rw [div_le_div_iff_of_pos_right hq0] at *
  exact hnum


/-! ### The rectangular bound -/

private theorem scalarMean_two_bound (A : ℝ) (hA : 10 ^ 4 ≤ A) {N : ℕ} (hN : 3 ≤ N) :
    scalarMean 2 A N ≤ 12 * (1 + 2 * π) ^ 2 * (Qof A N) ^ 6
      * (∑ k ∈ Icc 1 (Dyadic.cutoff (10 ^ 4 * A) N), ((k.totient : ℝ))⁻¹)
      * ((∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
            (∑ k ∈ Icc 1 (Dyadic.cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) ^ 2
              / (q : ℝ) ^ 2)
        + (Dyadic.cutoff (10 ^ 4 * A) N : ℝ) ^ 2 *
          ∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
            ((Real.log q / Real.log 2 * Real.log N) / q) ^ 2 / (q : ℝ) ^ 2) := by
  set Q : ℝ := Qof A N with hQ
  set K : ℕ := Dyadic.cutoff (10 ^ 4 * A) N with hK
  set K3 : ℕ := Dyadic.cutoff3 (10 ^ 4 * A) N with hK3
  set Iq : Finset ℕ := Icc 1 ⌊Q⌋₊ with hIq
  set SK : ℝ := ∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹ with hSK
  set Th : ℝ := ∑ q ∈ Iq,
    (∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 / (q : ℝ) ^ 2 with hTh
  set Cs : ℝ := ∑ q ∈ Iq,
    ((Real.log q / Real.log 2 * Real.log N) / q) ^ 2 / (q : ℝ) ^ 2 with hCs
  have hL1 : 1 ≤ Real.log N := one_le_log hN
  have hL0 : 0 < Real.log N := by linarith
  have hQ1 : 1 ≤ Q := by
    rw [hQ]; exact Real.one_le_rpow hL1 (by linarith : (0 : ℝ) ≤ 20 * A)
  have hQ0 : 0 < Q := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hK3K : K3 ≤ K := by
    rw [hK3, hK]
    exact LeanLab.Tolev2009.Level346.third_cutoff_le_first _ N (by omega)
  have hmono : ∀ (F : ℕ → ℕ → ℝ), (∀ q k, 0 ≤ F q k) → ∀ q,
      (∑ k ∈ Icc 1 K3, F q k) ≤ (∑ k ∈ Icc 1 K, F q k) := by
    intro F hF q
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hK3K)
      (fun x _ _ => hF q x)
  have herr_nn : ∀ q k, 0 ≤ errorProfile Q N q k := fun q k => errorProfile_nonneg Q N q k hQ0.le
  have hmain_nn : ∀ q k, 0 ≤ mainProfile N q k := fun q k => mainProfile_nonneg N q k
  -- the factorized rectangular sum
  have hstep : scalarMean 2 A N = (2 * Q / (N : ℝ)) * ∑ q ∈ Iq,
      ((∑ k ∈ Icc 1 K, errorProfile Q N q k) * (∑ k ∈ Icc 1 K, errorProfile Q N q k)
          * (∑ k ∈ Icc 1 K3, mainProfile N q k)
        + (∑ k ∈ Icc 1 K, errorProfile Q N q k) * (∑ k ∈ Icc 1 K, mainProfile N q k)
          * (∑ k ∈ Icc 1 K3, errorProfile Q N q k)
        + (∑ k ∈ Icc 1 K, mainProfile N q k) * (∑ k ∈ Icc 1 K, errorProfile Q N q k)
          * (∑ k ∈ Icc 1 K3, errorProfile Q N q k)) := by
    rw [scalarMean_two_eq A N]
  -- the pointwise three-term bound
  have hpt : ∀ q ∈ Iq,
      ((∑ k ∈ Icc 1 K, errorProfile Q N q k) * (∑ k ∈ Icc 1 K, errorProfile Q N q k)
          * (∑ k ∈ Icc 1 K3, mainProfile N q k)
        + (∑ k ∈ Icc 1 K, errorProfile Q N q k) * (∑ k ∈ Icc 1 K, mainProfile N q k)
          * (∑ k ∈ Icc 1 K3, errorProfile Q N q k)
        + (∑ k ∈ Icc 1 K, mainProfile N q k) * (∑ k ∈ Icc 1 K, errorProfile Q N q k)
          * (∑ k ∈ Icc 1 K3, errorProfile Q N q k))
      ≤ 3 * ((1 + 2 * π) * Q *
            ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
              (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q))) ^ 2
          * ((N : ℝ) * q * SK) := by
    intro q hq
    have hD := error_sum_eq Q N q K
    have hB := main_sum_eq N q K
    have hD3 : (∑ k ∈ Icc 1 K3, errorProfile Q N q k) ≤
        (1 + 2 * π) * Q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) := by
      refine (hmono (fun q k => errorProfile Q N q k) herr_nn q).trans_eq ?_
      exact hD
    have hB3 : (∑ k ∈ Icc 1 K3, mainProfile N q k) ≤ (N : ℝ) * q * SK := by
      refine (hmono (fun q k => mainProfile N q k) hmain_nn q).trans_eq ?_
      exact hB
    have hDnn : 0 ≤ (1 + 2 * π) * Q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
        (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) := by
      have := hmono (fun q k => errorProfile Q N q k) herr_nn q
      rw [hD] at this
      exact (Finset.sum_nonneg (fun k _ => herr_nn q k)).trans this
    have hBnn : 0 ≤ (N : ℝ) * q * SK := by
      have := hmono (fun q k => mainProfile N q k) hmain_nn q
      rw [hB] at this
      exact (Finset.sum_nonneg (fun k _ => hmain_nn q k)).trans this
    rw [hD, hB]
    have e1 : (1 + 2 * π) * Q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) *
        ((1 + 2 * π) * Q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q))) *
        (∑ k ∈ Icc 1 K3, mainProfile N q k) ≤
      ((1 + 2 * π) * Q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q))) ^ 2 * ((N : ℝ) * q * SK) := by
      have h := mul_le_mul_of_nonneg_left hB3 (mul_nonneg hDnn hDnn)
      calc _ ≤ _ := h
        _ = _ := by ring
    have e2 : (1 + 2 * π) * Q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) * ((N : ℝ) * q * SK) *
        (∑ k ∈ Icc 1 K3, errorProfile Q N q k) ≤
      ((1 + 2 * π) * Q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q))) ^ 2 * ((N : ℝ) * q * SK) := by
      have h := mul_le_mul_of_nonneg_left hD3 (mul_nonneg hDnn hBnn)
      calc _ ≤ _ := h
        _ = _ := by ring
    have e3 : (N : ℝ) * q * SK * ((1 + 2 * π) * Q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q))) *
        (∑ k ∈ Icc 1 K3, errorProfile Q N q k) ≤
      ((1 + 2 * π) * Q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q))) ^ 2 * ((N : ℝ) * q * SK) := by
      have h := mul_le_mul_of_nonneg_left hD3 (mul_nonneg hBnn hDnn)
      calc _ ≤ _ := h
        _ = _ := by ring
    nlinarith [e1, e2, e3]
  -- sum the pointwise bound
  have hsum1 : (∑ q ∈ Iq,
      ((∑ k ∈ Icc 1 K, errorProfile Q N q k) * (∑ k ∈ Icc 1 K, errorProfile Q N q k)
          * (∑ k ∈ Icc 1 K3, mainProfile N q k)
        + (∑ k ∈ Icc 1 K, errorProfile Q N q k) * (∑ k ∈ Icc 1 K, mainProfile N q k)
          * (∑ k ∈ Icc 1 K3, errorProfile Q N q k)
        + (∑ k ∈ Icc 1 K, mainProfile N q k) * (∑ k ∈ Icc 1 K, errorProfile Q N q k)
          * (∑ k ∈ Icc 1 K3, errorProfile Q N q k)))
      ≤ ∑ q ∈ Iq, 3 * ((1 + 2 * π) * Q *
            ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
              (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q))) ^ 2
          * ((N : ℝ) * q * SK) := Finset.sum_le_sum hpt
  -- split the squared theta-plus-log bound
  have hsum2 : (∑ q ∈ Iq, 3 * ((1 + 2 * π) * Q *
          ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
            (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q))) ^ 2
        * ((N : ℝ) * q * SK))
      ≤ ∑ q ∈ Iq, 3 * (((1 + 2 * π) * Q) ^ 2 *
            (2 * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 +
              ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2)))
          * ((N : ℝ) * q * SK) := by
    refine Finset.sum_le_sum (fun q hq => ?_)
    have hsplit : ((1 + 2 * π) * Q *
        ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q))) ^ 2
        ≤ ((1 + 2 * π) * Q) ^ 2 *
            (2 * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 +
              ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2)) := by
      have h2 : ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2 ≤
          2 * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 +
            ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2) := by
        nlinarith [sq_nonneg ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) -
          (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q))]
      calc _ = ((1 + 2 * π) * Q) ^ 2 *
            ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
              (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hsplit (by norm_num)
  -- pull the constants out
  have hsum3 : (∑ q ∈ Iq, 3 * (((1 + 2 * π) * Q) ^ 2 *
            (2 * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 +
              ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2)))
          * ((N : ℝ) * q * SK))
      = 6 * ((1 + 2 * π) * Q) ^ 2 * (N : ℝ) * SK * ∑ q ∈ Iq,
          q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 +
              ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  -- shift `q ≤ Q` into the denominator, theta part
  have hqQ : ∀ q ∈ Iq, (q : ℝ) ≤ Q := by
    intro q hq
    have h2 : (q : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hq).2
    exact h2.trans (Nat.floor_le hQ0.le)
  have hhalf1 : (∑ q ∈ Iq, q * (∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2)
      ≤ Q ^ 3 * Th := by
    have hpt2 : ∀ q ∈ Iq, q * (∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2
        ≤ Q ^ 3 * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 / (q : ℝ) ^ 2) := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
      have hqQ' := hqQ q hq
      have hid : (q : ℝ) * (∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2
          = (q : ℝ) ^ 3 * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 / (q : ℝ) ^ 2) := by
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hqQ' 3)
        (div_nonneg (sq_nonneg _) (by positivity))
    refine (Finset.sum_le_sum hpt2).trans ?_
    rw [← Finset.mul_sum, hTh]
  -- shift `q ≤ Q` into the denominator, log part
  have hhalf2 : (∑ q ∈ Iq, q * ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2)
      ≤ Q ^ 3 * ((K : ℝ) ^ 2 * Cs) := by
    have hpt2 : ∀ q ∈ Iq, q * ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2
        ≤ Q ^ 3 * (((K : ℝ) ^ 2 * ((Real.log q / Real.log 2 * Real.log N) / q) ^ 2)
          / (q : ℝ) ^ 2) := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
      have hqQ' := hqQ q hq
      have hid : (q : ℝ) * ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2
          = (q : ℝ) ^ 3 * (((K : ℝ) ^ 2 * ((Real.log q / Real.log 2 * Real.log N) / q) ^ 2)
            / (q : ℝ) ^ 2) := by
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hqQ' 3)
        (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity))
    have hkey : (∑ i ∈ Iq, ((K : ℝ) ^ 2 *
          ((Real.log i / Real.log 2 * Real.log N) / i) ^ 2) / (i : ℝ) ^ 2)
        = (K : ℝ) ^ 2 * Cs := by
      rw [hCs, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    refine (Finset.sum_le_sum hpt2).trans ?_
    rw [← Finset.mul_sum, hkey]
  -- combine
  have hsum4 : (∑ q ∈ Iq,
        q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 +
              ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2))
      ≤ Q ^ 3 * (Th + (K : ℝ) ^ 2 * Cs) := by
    have hsplit : ∀ q ∈ Iq,
        q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 +
              ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2)
          = q * (∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 +
            q * ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2 := by
      intro q _; ring
    calc (∑ q ∈ Iq, q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 +
              ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2))
        = (∑ q ∈ Iq, q * (∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2)
          + ∑ q ∈ Iq, q * ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2 := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun q hq => hsplit q hq)
      _ ≤ Q ^ 3 * Th + Q ^ 3 * ((K : ℝ) ^ 2 * Cs) := add_le_add hhalf1 hhalf2
      _ = Q ^ 3 * (Th + (K : ℝ) ^ 2 * Cs) := by ring
  calc scalarMean 2 A N
      = (2 * Q / (N : ℝ)) * ∑ q ∈ Iq,
        ((∑ k ∈ Icc 1 K, errorProfile Q N q k) * (∑ k ∈ Icc 1 K, errorProfile Q N q k)
            * (∑ k ∈ Icc 1 K3, mainProfile N q k)
          + (∑ k ∈ Icc 1 K, errorProfile Q N q k) * (∑ k ∈ Icc 1 K, mainProfile N q k)
            * (∑ k ∈ Icc 1 K3, errorProfile Q N q k)
          + (∑ k ∈ Icc 1 K, mainProfile N q k) * (∑ k ∈ Icc 1 K, errorProfile Q N q k)
            * (∑ k ∈ Icc 1 K3, errorProfile Q N q k)) := hstep
    _ ≤ (2 * Q / (N : ℝ)) * (∑ q ∈ Iq, 3 * ((1 + 2 * π) * Q *
            ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) +
              (K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q))) ^ 2
          * ((N : ℝ) * q * SK)) := by
        refine mul_le_mul_of_nonneg_left hsum1 ?_
        positivity
    _ ≤ (2 * Q / (N : ℝ)) * (∑ q ∈ Iq, 3 * (((1 + 2 * π) * Q) ^ 2 *
            (2 * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 +
              ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2)))
          * ((N : ℝ) * q * SK)) := by
        refine mul_le_mul_of_nonneg_left hsum2 ?_
        positivity
    _ = (2 * Q / (N : ℝ)) * (6 * ((1 + 2 * π) * Q) ^ 2 * (N : ℝ) * SK *
          ∑ q ∈ Iq, q * ((∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 +
              ((K : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 2)) := by
        rw [hsum3]
    _ ≤ (2 * Q / (N : ℝ)) * (6 * ((1 + 2 * π) * Q) ^ 2 * (N : ℝ) * SK *
          (Q ^ 3 * (Th + (K : ℝ) ^ 2 * Cs))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left hsum4 (by positivity)
    _ = 12 * (1 + 2 * π) ^ 2 * Q ^ 6 * SK * (Th + (K : ℝ) ^ 2 * Cs) := by
        field_simp
        ring


/-- Four `rpow` factors multiply, and the exponent comparison is enough. -/
private theorem rpow_prod_four {x : ℝ} (hx : 1 ≤ x) {a b c d e : ℝ} (h : a + b + c + d ≤ e) :
    x ^ a * x ^ b * x ^ c * x ^ d ≤ x ^ e := by
  have hx0 : 0 < x := by linarith
  have e1 : x ^ a * x ^ b = x ^ (a + b) := (Real.rpow_add hx0 a b).symm
  have e2 : x ^ (a + b) * x ^ c = x ^ (a + b + c) := (Real.rpow_add hx0 (a + b) c).symm
  have e3 : x ^ (a + b + c) * x ^ d = x ^ (a + b + c + d) :=
    (Real.rpow_add hx0 (a + b + c) d).symm
  calc x ^ a * x ^ b * x ^ c * x ^ d = x ^ (a + b + c + d) := by rw [e1, e2, e3]
    _ ≤ x ^ e := Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-- `(log N)^{20 A}` raised to a natural power. -/
private theorem rpow_pow_local {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (n : ℕ) : (x ^ a) ^ n = x ^ (n * a) := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx]
  congr 1
  ring

/-- Five `rpow` factors multiply to a single one. -/
private theorem rpow_prod_five {x : ℝ} (hx : 0 < x) {a b c d e : ℝ} :
    x ^ a * x ^ b * x ^ c * x ^ d * x ^ e = x ^ (a + b + c + d + e) := by
  have e1 : x ^ a * x ^ b = x ^ (a + b) := (Real.rpow_add hx a b).symm
  have e2 : x ^ (a + b) * x ^ c = x ^ (a + b + c) := (Real.rpow_add hx (a + b) c).symm
  have e3 : x ^ (a + b + c) * x ^ d = x ^ (a + b + c + d) :=
    (Real.rpow_add hx (a + b + c) d).symm
  have e4 : x ^ (a + b + c + d) * x ^ e = x ^ (a + b + c + d + e) :=
    (Real.rpow_add hx (a + b + c + d) e).symm
  calc x ^ a * x ^ b * x ^ c * x ^ d * x ^ e = x ^ (a + b + c + d + e) := by rw [e1, e2, e3, e4]

private theorem quadratic_scalar_mean_proof :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      scalarMean 2 A N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA
  obtain ⟨Cθ, hCθ⟩ := theta_sq_average A hA
  refine ⟨96 * (1 + 2 * π) ^ 2 * ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2), 3,
    fun N _ hN => ?_⟩
  have hN3 : 3 ≤ N := by exact_mod_cast hN
  set L : ℝ := Real.log N with hL
  set Q : ℝ := Qof A N with hQ
  set K : ℕ := Dyadic.cutoff (10 ^ 4 * A) N with hK
  have hL1 : 1 ≤ L := by rw [hL]; exact one_le_log hN3
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hQ1 : 1 ≤ Q := by
    rw [hQ]; exact Real.one_le_rpow hL1 (by linarith : (0 : ℝ) ≤ 20 * A)
  have hQ0 : 0 < Q := by linarith
  have hSK : (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ≤ (1 + L) ^ 2 := by
    rw [hL]
    refine (sum_inv_totient_le K).trans ?_
    have hLN : 1 ≤ Real.log N := by rw [← hL]; exact hL1
    have hKN : K ≤ N := by
      rw [hK]
      exact Dyadic.cutoff_le (10 ^ 4 * A) N (by positivity) hLN
    have hKle : ((K : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hKN
    have hlog : Real.log K ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos K with h0 | hpos
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg N
      · exact Real.log_le_log (Nat.cast_pos.mpr hpos) hKle
    have h1 : (1 + Real.log K) ^ 2 ≤ (1 + Real.log N) ^ 2 := by
      have h0 := one_add_log_nat_nonneg K
      have h2 : 1 + Real.log K ≤ 1 + Real.log N := by linarith
      nlinarith
    exact h1
  have hTh : (∑ q ∈ Icc 1 ⌊Q⌋₊,
        (∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 / (q : ℝ) ^ 2)
      ≤ (Hn ⌊Q⌋₊) ^ 4 * (Cθ * (N : ℝ) * L ^ (-(100 * A))) ^ 2 := by
    have h := hCθ N hN3 hL1 K (le_of_eq hK)
    have hconv : Cθ * (N : ℝ) / Real.log N ^ (100 * A) =
        Cθ * (N : ℝ) * L ^ (-(100 * A)) := by
      rw [hL, Real.rpow_neg hL0.le, div_eq_mul_inv]
    rw [hconv] at h
    exact h
  have hHn : (Hn ⌊Q⌋₊) ^ 4 ≤ (21 * A) ^ 4 * L ^ 4 := by
    have h1 : Hn ⌊Q⌋₊ ≤ 21 * A * L := by
      rw [hL, hQ]
      exact Hn_le A hA hN3
    have h2 : (0 : ℝ) ≤ Hn ⌊Q⌋₊ := Hn_nonneg _
    have h3 : Hn ⌊Q⌋₊ ^ 4 ≤ (21 * A * L) ^ 4 := pow_le_pow_left₀ h2 h1 4
    calc Hn ⌊Q⌋₊ ^ 4 ≤ (21 * A * L) ^ 4 := h3
      _ = (21 * A) ^ 4 * L ^ 4 := by ring
  have hCs : (∑ q ∈ Icc 1 ⌊Q⌋₊,
        ((Real.log q / Real.log 2 * Real.log N) / q) ^ 2 / (q : ℝ) ^ 2)
      ≤ Q * (40 * A * L ^ 2) ^ 2 := by
    have hpt : ∀ q ∈ Icc 1 ⌊Q⌋₊,
        ((Real.log q / Real.log 2 * Real.log N) / q) ^ 2 / (q : ℝ) ^ 2
          ≤ (40 * A * L ^ 2) ^ 2 := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
      have hqQ : (q : ℝ) ≤ Q := by
        have h2 : (q : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hq).2
        exact h2.trans (Nat.floor_le hQ0.le)
      have hc := c_q_le A hA hN3 hq1 hqQ
      have hlog2 : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hc0 : 0 ≤ (Real.log q / Real.log 2 * Real.log N) / q :=
        div_nonneg (mul_nonneg (div_nonneg (Real.log_natCast_nonneg q) hlog2.le) hL0.le) hq0.le
      have hY : (0 : ℝ) ≤ 40 * A * L ^ 2 := by positivity
      have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      calc ((Real.log q / Real.log 2 * Real.log N) / q) ^ 2 / (q : ℝ) ^ 2
          ≤ ((40 * A * L ^ 2) / q) ^ 2 / (q : ℝ) ^ 2 := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_left₀ hc0 hc 2
        _ = (40 * A * L ^ 2) ^ 2 / (q : ℝ) ^ 4 := by
            rw [div_pow]
            ring
        _ ≤ (40 * A * L ^ 2) ^ 2 := by
            rw [div_le_iff₀ (by positivity)]
            have hq4 : (1 : ℝ) ≤ (q : ℝ) ^ 4 := by
              simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hq1' 4
            nlinarith [hY, hq4, sq_nonneg (40 * A * L ^ 2)]
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hcard : ((⌊Q⌋₊ + 1 - 1 : ℕ) : ℝ) ≤ Q := by
      have h1 : ⌊Q⌋₊ + 1 - 1 = ⌊Q⌋₊ := by omega
      rw [h1]
      exact Nat.floor_le hQ0.le
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hK2 : (K : ℝ) ^ 2 ≤ (N : ℝ) * L ^ (-(2 * (10 ^ 4) * A)) := by
    have hKle : (K : ℝ) ≤ Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A)) := by
      rw [hK]
      exact Nat.floor_le (by positivity)
    have hsq : (K : ℝ) ^ 2 ≤ (Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hKle 2
    have hid : (Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A))) ^ 2
        = (N : ℝ) * L ^ (-(2 * (10 ^ 4) * A)) := by
      rw [mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ N), hL,
        rpow_pow_local hL0.le,
        show ((2 : ℕ) : ℝ) * (-(10 ^ 4 * A)) = -(2 * (10 ^ 4) * A) from by ring]
    rw [hid] at hsq
    exact hsq
  have hQ6 : Q ^ 6 = L ^ (120 * A) := by
    rw [hQ, hL, Qof_rpow_eq, rpow_pow_local hL0.le]
    congr 1
    ring
  have hQ20 : Q = L ^ (20 * A) := by rw [hQ, hL, Qof_rpow_eq]
  have h1L : (1 + L) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have hC2 : (Cθ * (N : ℝ) * L ^ (-(100 * A))) ^ 2 = Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-(200 * A)) := by
    rw [mul_pow, mul_pow, rpow_pow_local hL0.le]
    congr 1
    push_cast
    ring
  have hM : Cθ ^ 2 ≤ Cθ ^ 2 + 1 := by linarith
  have hSKnn : (0 : ℝ) ≤ ∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹ :=
    Finset.sum_nonneg (fun k _ => by positivity)
  have hHnNN : (0 : ℝ) ≤ Hn ⌊Q⌋₊ ^ 4 := by positivity
  have hThnn : (0 : ℝ) ≤ (∑ q ∈ Icc 1 ⌊Q⌋₊,
      (∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 / (q : ℝ) ^ 2) :=
    Finset.sum_nonneg (fun q _ => by positivity)
  have hCsnn : (0 : ℝ) ≤ (∑ q ∈ Icc 1 ⌊Q⌋₊,
      ((Real.log q / Real.log 2 * Real.log N) / q) ^ 2 / (q : ℝ) ^ 2) :=
    Finset.sum_nonneg (fun q _ => by positivity)
  -- piece 1: the averaged theta square
  have hP1 : 12 * (1 + 2 * π) ^ 2 * Q ^ 6 *
        (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) *
        ((Hn ⌊Q⌋₊) ^ 4 * (Cθ * (N : ℝ) * L ^ (-(100 * A))) ^ 2)
      ≤ 48 * (1 + 2 * π) ^ 2 * ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2) *
        (N : ℝ) ^ 2 * L ^ (-A) := by
    have hcore : L ^ (120 * A) * L ^ 2 * L ^ 4 * L ^ (-(200 * A)) ≤ L ^ (-A) := by
      rw [show L ^ (2 : ℕ) = L ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast L 2).symm,
        show L ^ (4 : ℕ) = L ^ ((4 : ℕ) : ℝ) from (Real.rpow_natCast L 4).symm]
      refine rpow_prod_four (x := L) hL1 (a := 120 * A) (b := (2 : ℕ)) (c := (4 : ℕ))
        (d := -(200 * A)) (e := -A) ?_
      push_cast
      nlinarith
    have hstep : 12 * (1 + 2 * π) ^ 2 * Q ^ 6 *
          (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) *
          ((Hn ⌊Q⌋₊) ^ 4 * (Cθ * (N : ℝ) * L ^ (-(100 * A))) ^ 2)
        ≤ 48 * (1 + 2 * π) ^ 2 * (21 * A) ^ 4 * Cθ ^ 2 * (N : ℝ) ^ 2 *
          (L ^ (120 * A) * L ^ 2 * L ^ 4 * L ^ (-(200 * A))) := by
      rw [hQ6, hC2]
      have h1 : (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ≤ (1 + L) ^ 2 := hSK
      have h2 : Hn ⌊Q⌋₊ ^ 4 ≤ (21 * A) ^ 4 * L ^ 4 := hHn
      have h3 : (1 + L) ^ 2 ≤ 4 * L ^ 2 := h1L
      have hC2nn : (0 : ℝ) ≤ Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-(200 * A)) := by positivity
      have hb1 : (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ≤ 4 * L ^ 2 := h1.trans h3
      have hb2 : Hn ⌊Q⌋₊ ^ 4 * (Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-(200 * A)))
          ≤ ((21 * A) ^ 4 * L ^ 4) * (Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-(200 * A))) :=
        mul_le_mul_of_nonneg_right h2 hC2nn
      have e0 : 12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) *
            (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) *
            (Hn ⌊Q⌋₊ ^ 4 * (Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-(200 * A))))
          ≤ 12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) * (4 * L ^ 2) *
            ((21 * A) ^ 4 * L ^ 4 * (Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-(200 * A)))) := by
        calc 12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) *
              (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) *
              (Hn ⌊Q⌋₊ ^ 4 * (Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-(200 * A))))
            ≤ 12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) *
              (4 * L ^ 2) *
              (((21 * A) ^ 4 * L ^ 4) * (Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-(200 * A)))) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hb1 (by positivity)) hb2
                (by positivity) (by positivity)
          _ = 12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) * (4 * L ^ 2) *
              ((21 * A) ^ 4 * L ^ 4 * (Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-(200 * A)))) := by ring
      refine e0.trans ?_
      have hid : 12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) * (4 * L ^ 2) *
            ((21 * A) ^ 4 * L ^ 4 * (Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-(200 * A))))
          = (48 * (1 + 2 * π) ^ 2 * (21 * A) ^ 4 * Cθ ^ 2 * (N : ℝ) ^ 2) *
            (L ^ (120 * A) * L ^ 2 * L ^ 4 * L ^ (-(200 * A))) := by ring
      rw [hid]
    refine hstep.trans ?_
    have hc1 : (0 : ℝ) ≤ 48 * (1 + 2 * π) ^ 2 * (21 * A) ^ 4 * Cθ ^ 2 * (N : ℝ) ^ 2 := by
      positivity
    refine (mul_le_mul_of_nonneg_left hcore hc1).trans ?_
    -- replace `Cθ ^ 2` by the larger constant and `L ^ (-A)` by itself
    have hfinal : 48 * (1 + 2 * π) ^ 2 * (21 * A) ^ 4 * Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-A)
        ≤ 48 * (1 + 2 * π) ^ 2 * ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2) *
          (N : ℝ) ^ 2 * L ^ (-A) := by
      have hY4 : (0 : ℝ) ≤ (40 * A) ^ 2 := by positivity
      have hA4 : (0 : ℝ) ≤ (21 * A) ^ 4 := by positivity
      have hpp : (0 : ℝ) ≤ 48 * (1 + 2 * π) ^ 2 * (N : ℝ) ^ 2 * L ^ (-A) := by positivity
      have hkey : (21 * A) ^ 4 * Cθ ^ 2 ≤ (21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2 := by
        nlinarith [hM, hA4, hY4, sq_nonneg Cθ]
      calc 48 * (1 + 2 * π) ^ 2 * (21 * A) ^ 4 * Cθ ^ 2 * (N : ℝ) ^ 2 * L ^ (-A)
          = (48 * (1 + 2 * π) ^ 2) * ((21 * A) ^ 4 * Cθ ^ 2) *
              ((N : ℝ) ^ 2 * L ^ (-A)) := by ring
        _ ≤ (48 * (1 + 2 * π) ^ 2) *
              ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2) *
              ((N : ℝ) ^ 2 * L ^ (-A)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hkey (by positivity)) le_rfl
              (by positivity) (by positivity)
        _ = 48 * (1 + 2 * π) ^ 2 * ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2) *
              (N : ℝ) ^ 2 * L ^ (-A) := by ring
    exact hfinal
  -- piece 2: the logarithmic profile
  have hP2 : 12 * (1 + 2 * π) ^ 2 * Q ^ 6 *
        (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) *
        ((K : ℝ) ^ 2 * (Q * (40 * A * L ^ 2) ^ 2))
      ≤ 48 * (1 + 2 * π) ^ 2 * ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2) *
        (N : ℝ) ^ 2 * L ^ (-A) := by
    have hcore2 : L ^ (120 * A) * L ^ 2 * L ^ (20 * A) * L ^ 4 * L ^ (-(20000 * A))
        = L ^ (6 - 19860 * A) := by
      rw [show L ^ (2 : ℕ) = L ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast L 2).symm,
        show L ^ (4 : ℕ) = L ^ ((4 : ℕ) : ℝ) from (Real.rpow_natCast L 4).symm]
      rw [rpow_prod_five hL0]
      congr 1
      push_cast
      ring
    have hsplit2 : L ^ (6 - 19860 * A) = L ^ (6 - 19859 * A) * L ^ (-A) := by
      rw [← Real.rpow_add hL0]
      congr 1
      ring
    have hNN : L ^ (6 - 19860 * A) * (N : ℝ) ≤ (N : ℝ) ^ 2 * L ^ (-A) := by
      rw [hsplit2]
      calc L ^ (6 - 19859 * A) * L ^ (-A) * (N : ℝ)
          = L ^ (6 - 19859 * A) * (L ^ (-A) * (N : ℝ)) := by ring
        _ ≤ 1 * (L ^ (-A) * (N : ℝ) ^ 2) := by
            refine mul_le_mul ?_ ?_ (by positivity) (by norm_num)
            · exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by nlinarith)
            · exact mul_le_mul_of_nonneg_left hN2 (by positivity)
        _ = (N : ℝ) ^ 2 * L ^ (-A) := by ring
    have hstep : 12 * (1 + 2 * π) ^ 2 * Q ^ 6 *
          (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) *
          ((K : ℝ) ^ 2 * (Q * (40 * A * L ^ 2) ^ 2))
        ≤ 48 * (1 + 2 * π) ^ 2 * (40 * A) ^ 2 *
          ((L ^ (120 * A) * L ^ 2 * L ^ (20 * A) * L ^ 4 * L ^ (-(20000 * A))) * (N : ℝ)) := by
      rw [hQ6, hQ20]
      have h1 : (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ≤ (1 + L) ^ 2 := hSK
      have h2 : (K : ℝ) ^ 2 ≤ (N : ℝ) * L ^ (-(2 * (10 ^ 4) * A)) := hK2
      have h3 : (1 + L) ^ 2 ≤ 4 * L ^ 2 := h1L
      have h4 : L ^ (-(2 * (10 ^ 4) * A)) = L ^ (-(20000 * A)) := by
        congr 1
        ring
      rw [h4] at h2
      have e0 : 12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) *
            (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) *
            ((K : ℝ) ^ 2 * (L ^ (20 * A) * (40 * A * L ^ 2) ^ 2))
          ≤ 12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) * (4 * L ^ 2) *
            (((N : ℝ) * L ^ (-(20000 * A))) * (L ^ (20 * A) * (40 * A * L ^ 2) ^ 2)) := by
        have hc : (0 : ℝ) ≤ 12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) := by positivity
        have hb1 : 12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) *
            (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) ≤
            12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) * (4 * L ^ 2) :=
          (mul_le_mul_of_nonneg_left h1 hc).trans (mul_le_mul_of_nonneg_left h3 hc)
        exact mul_le_mul hb1 (mul_le_mul_of_nonneg_right h2 (by positivity))
          (by positivity) (by positivity)
      refine e0.trans ?_
      have hid : 12 * (1 + 2 * π) ^ 2 * L ^ (120 * A) * (4 * L ^ 2) *
            (((N : ℝ) * L ^ (-(20000 * A))) * (L ^ (20 * A) * (40 * A * L ^ 2) ^ 2))
          = 48 * (1 + 2 * π) ^ 2 * (40 * A) ^ 2 *
            ((L ^ (120 * A) * L ^ 2 * L ^ (20 * A) * L ^ 4 * L ^ (-(20000 * A))) * (N : ℝ)) := by
        ring
      rw [hid]
    refine hstep.trans ?_
    have hc2 : (0 : ℝ) ≤ 48 * (1 + 2 * π) ^ 2 * (40 * A) ^ 2 := by positivity
    rw [hcore2]
    have hbig : 48 * (1 + 2 * π) ^ 2 * (40 * A) ^ 2 ≤
        48 * (1 + 2 * π) ^ 2 * ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2) := by
      have hA4 : (0 : ℝ) ≤ (21 * A) ^ 4 * (Cθ ^ 2 + 1) := by positivity
      nlinarith [hA4]
    calc 48 * (1 + 2 * π) ^ 2 * (40 * A) ^ 2 * (L ^ (6 - 19860 * A) * (N : ℝ))
        ≤ 48 * (1 + 2 * π) ^ 2 * (40 * A) ^ 2 * ((N : ℝ) ^ 2 * L ^ (-A)) :=
          mul_le_mul_of_nonneg_left hNN hc2
      _ ≤ 48 * (1 + 2 * π) ^ 2 * ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2) *
            ((N : ℝ) ^ 2 * L ^ (-A)) := mul_le_mul_of_nonneg_right hbig (by positivity)
      _ = 48 * (1 + 2 * π) ^ 2 * ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2) *
            (N : ℝ) ^ 2 * L ^ (-A) := by ring
  -- assemble
  have hmain := scalarMean_two_bound A hA hN3
  have hbr : ((∑ q ∈ Icc 1 ⌊Q⌋₊,
        (∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 / (q : ℝ) ^ 2))
      + (K : ℝ) ^ 2 * (∑ q ∈ Icc 1 ⌊Q⌋₊,
        ((Real.log q / Real.log 2 * Real.log N) / q) ^ 2 / (q : ℝ) ^ 2)
      ≤ (Hn ⌊Q⌋₊) ^ 4 * (Cθ * (N : ℝ) * L ^ (-(100 * A))) ^ 2
        + (K : ℝ) ^ 2 * (Q * (40 * A * L ^ 2) ^ 2) := by
    refine add_le_add hTh ?_
    exact mul_le_mul_of_nonneg_left hCs (by positivity : (0 : ℝ) ≤ (K : ℝ) ^ 2)
  have hQ6nn : (0 : ℝ) ≤ Q ^ 6 := by positivity
  have hfac : (0 : ℝ) ≤ 12 * (1 + 2 * π) ^ 2 * Q ^ 6 *
      (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) := by positivity
  calc scalarMean 2 A N
      ≤ 12 * (1 + 2 * π) ^ 2 * Q ^ 6 * (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) *
          (((∑ q ∈ Icc 1 ⌊Q⌋₊,
            (∑ k ∈ Icc 1 K, thetaError N (Nat.lcm k q)) ^ 2 / (q : ℝ) ^ 2))
          + (K : ℝ) ^ 2 * (∑ q ∈ Icc 1 ⌊Q⌋₊,
            ((Real.log q / Real.log 2 * Real.log N) / q) ^ 2 / (q : ℝ) ^ 2)) := hmain
    _ ≤ 12 * (1 + 2 * π) ^ 2 * Q ^ 6 * (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) *
          ((Hn ⌊Q⌋₊) ^ 4 * (Cθ * (N : ℝ) * L ^ (-(100 * A))) ^ 2
            + (K : ℝ) ^ 2 * (Q * (40 * A * L ^ 2) ^ 2)) :=
        mul_le_mul_of_nonneg_left hbr hfac
    _ = 12 * (1 + 2 * π) ^ 2 * Q ^ 6 * (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) *
          ((Hn ⌊Q⌋₊) ^ 4 * (Cθ * (N : ℝ) * L ^ (-(100 * A))) ^ 2)
        + 12 * (1 + 2 * π) ^ 2 * Q ^ 6 * (∑ k ∈ Icc 1 K, ((k.totient : ℝ))⁻¹) *
          ((K : ℝ) ^ 2 * (Q * (40 * A * L ^ 2) ^ 2)) := by ring
    _ ≤ 48 * (1 + 2 * π) ^ 2 * ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2) *
          (N : ℝ) ^ 2 * L ^ (-A)
        + 48 * (1 + 2 * π) ^ 2 * ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2) *
          (N : ℝ) ^ 2 * L ^ (-A) := add_le_add hP1 hP2
    _ = 96 * (1 + 2 * π) ^ 2 * ((21 * A) ^ 4 * (Cθ ^ 2 + 1) + (40 * A) ^ 2) *
          (N : ℝ) ^ 2 * L ^ (-A) := by ring

/-- Halupczok page 9 to 10, O2, the positive scalar rectangular mean.
Only real theta discrepancies, totients, logarithms and natural modulus sums occur.
There are no prime polynomials, rational phases, residue variables, signed weights
or integrals in this arithmetic leaf. The bad prime profile is explicit. Proved. -/
theorem quadratic_scalar_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      scalarMean 2 A N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  exact quadratic_scalar_mean_proof

/-- Halupczok page 9 to 10, O2, after discrete partial summation on page 7.
Estimate only the static positive degree 2 rational prefix discrepancy average.
There is no beta variable, integral or arbitrary lambda. The full prime interval
and the fixed third residue retain the sealed 2009 adaptation.
Derived from quadratic_scalar_mean. -/
theorem quadratic_prefix_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
        EF (fun k l => errorEnvelope 2 (Qof A N) (τof A N) k l N)
          (fun _ => 1) l₃ (10 ^ 4 * A) N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, h⟩ := quadratic_scalar_mean A hA
  refine ⟨C, max N₀ 3, fun N hodd hN => ?_⟩
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    linarith [Real.exp_one_lt_d9]
  have hQ : 1 ≤ Qof A N := Real.one_le_rpow hL (by linarith)
  exact (prefix_mean_le_scalar 2 A N l₃ hQ (by exact_mod_cast (show (1 : ℝ) ≤ N by linarith))).trans
    (h N hodd ((le_max_left _ _).trans hN))

/-- The exact sealed degree 2 remainder statement.
Derived from the static positive prefix mean. No new integral estimate is assumed. -/
theorem quadratic_remainder_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => errorTerm 2 (Qof A N) (τof A N) k l N)
            lam l₃ (10 ^ 4 * A) N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, h⟩ := quadratic_prefix_mean A hA l₃ hl₃
  exact ⟨C, N₀, fun lam hlam N hodd hN =>
    (error_mean_bound 2 A lam l₃ N hlam).trans (h N hodd hN)⟩

end LeanLab.Tolev2009.Decomp346b
