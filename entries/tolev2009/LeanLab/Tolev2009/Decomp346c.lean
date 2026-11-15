module

public import LeanLab.Tolev2009.ScalarEnvelope346
public import LeanLab.Tolev2009.LcmAverage346

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 page 10 to 11, O3.
The scalar rectangular mean is proved. The exact assemblies are derived from it.
-/

@[expose] public section

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.Decomp346c
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp314a LeanLab.Tolev2009.Progression346
open LeanLab.Tolev2009.ScalarEnvelope346
open LeanLab.Tolev2009.Dyadic
open LeanLab.Tolev2009.Discrepancy346
open LeanLab.Tolev2009.LcmAverage346
open LeanLab.HeathBrown1985

theorem cutoff3_le_cutoff_local {B : ℝ} {N : ℕ} (hN : 1 < N) : cutoff3 B N ≤ cutoff B N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hL : (0 : ℝ) < Real.log N := Real.log_pos hN1
  unfold cutoff3 cutoff
  refine Nat.floor_mono ?_
  have hpow : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_left_iff hN1).mpr (by norm_num)
  exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hL.le _)

/-- The three `k`-sums of a product factor into a product of sums, with the
`q`-sum outermost. -/
theorem triple_sum_mul {I1 I2 I3 Iq : Finset ℕ} {c : ℝ} {d : ℕ → ℕ → ℝ} :
    (∑ k₁ ∈ I1, ∑ k₂ ∈ I2, ∑ k₃ ∈ I3, ∑ q ∈ Iq, c * (d k₁ q * d k₂ q * d k₃ q))
      = c * ∑ q ∈ Iq,
          (∑ k ∈ I1, d k q) * (∑ k ∈ I2, d k q) * (∑ k ∈ I3, d k q) := by
  have key : ∀ q, (∑ k₁ ∈ I1, d k₁ q) * (∑ k₂ ∈ I2, d k₂ q) * (∑ k₃ ∈ I3, d k₃ q)
      = ∑ k₁ ∈ I1, ∑ k₂ ∈ I2, ∑ k₃ ∈ I3, d k₁ q * d k₂ q * d k₃ q := by
    intro q
    rw [Finset.sum_mul_sum (s := I1) (t := I2) (f := fun k => d k q) (g := fun k => d k q)]
    rw [Finset.sum_mul (s := I1) (f := fun k₁ => ∑ k₂ ∈ I2, d k₁ q * d k₂ q)
      (a := ∑ k₃ ∈ I3, d k₃ q)]
    refine Finset.sum_congr rfl (fun k₁ _ => ?_)
    rw [Finset.sum_mul (s := I2) (f := fun k₂ => d k₁ q * d k₂ q)
      (a := ∑ k₃ ∈ I3, d k₃ q)]
    refine Finset.sum_congr rfl (fun k₂ _ => ?_)
    exact Finset.mul_sum (s := I3) (f := fun k => d k q) (a := d k₁ q * d k₂ q)
  have hq : ∀ q, c * ((∑ k₁ ∈ I1, d k₁ q) * (∑ k₂ ∈ I2, d k₂ q) * (∑ k₃ ∈ I3, d k₃ q))
      = ∑ k₁ ∈ I1, ∑ k₂ ∈ I2, ∑ k₃ ∈ I3, c * (d k₁ q * d k₂ q * d k₃ q) := by
    intro q
    rw [key q, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k₁ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k₂ _ => ?_)
    rw [Finset.mul_sum]
  have e1 : (∑ q ∈ Iq, ∑ k₁ ∈ I1, ∑ k₂ ∈ I2, ∑ k₃ ∈ I3,
        c * (d k₁ q * d k₂ q * d k₃ q))
      = ∑ k₁ ∈ I1, ∑ q ∈ Iq, ∑ k₂ ∈ I2, ∑ k₃ ∈ I3, c * (d k₁ q * d k₂ q * d k₃ q) :=
    Finset.sum_comm
  have e2 : (∑ k₁ ∈ I1, ∑ q ∈ Iq, ∑ k₂ ∈ I2, ∑ k₃ ∈ I3,
        c * (d k₁ q * d k₂ q * d k₃ q))
      = ∑ k₁ ∈ I1, ∑ k₂ ∈ I2, ∑ q ∈ Iq, ∑ k₃ ∈ I3, c * (d k₁ q * d k₂ q * d k₃ q) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_comm)
  have e3 : (∑ k₁ ∈ I1, ∑ k₂ ∈ I2, ∑ q ∈ Iq, ∑ k₃ ∈ I3,
        c * (d k₁ q * d k₂ q * d k₃ q))
      = ∑ k₁ ∈ I1, ∑ k₂ ∈ I2, ∑ k₃ ∈ I3, ∑ q ∈ Iq, c * (d k₁ q * d k₂ q * d k₃ q) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun k₂ _ => Finset.sum_comm))
  have hR : c * ∑ q ∈ Iq,
        (∑ k ∈ I1, d k q) * (∑ k ∈ I2, d k q) * (∑ k ∈ I3, d k q)
      = ∑ k₁ ∈ I1, ∑ k₂ ∈ I2, ∑ k₃ ∈ I3, ∑ q ∈ Iq, c * (d k₁ q * d k₂ q * d k₃ q) := by
    refine ((Finset.mul_sum (s := Iq)
      (f := fun q => (∑ k ∈ I1, d k q) * (∑ k ∈ I2, d k q) * (∑ k ∈ I3, d k q))
      (a := c)).trans ?_).trans ((e1.trans e2).trans e3)
    exact Finset.sum_congr rfl (fun q _ => hq q)
  exact hR.symm

/-- One `k`-sum of error profiles: one theta sum plus `k` copies of the
logarithmic profile. -/
theorem inner_sum_eq (Q : ℝ) (N : ℕ) (q k : ℕ) :
    ∑ k' ∈ Icc 1 k, errorProfile Q N q k' =
      (1 + 2 * π) * Q *
        (∑ k' ∈ Icc 1 k, thetaError N (Nat.lcm k' q) +
          (k : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) := by
  unfold errorProfile
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
    Nat.add_sub_cancel]

/-- Each degree-three arc is the `2Q/N` multiple of the three error profiles. -/
theorem scalarArc_eq (Q : ℝ) (N q k₁ k₂ k₃ : ℕ) :
    scalarArc 3 Q N q ![k₁, k₂, k₃] =
      (2 * Q / N) * (errorProfile Q N q k₁ * errorProfile Q N q k₂ * errorProfile Q N q k₃) := by
  unfold scalarArc
  simp only [positivePart]
  norm_num

/-- The rectangular mean, with the `q`-sum outermost and the `k`-sums factored. -/
theorem scalarMean_eq (A : ℝ) (N : ℕ) :
    scalarMean 3 A N
      = (2 * Qof A N / N) * ∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
          (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k) *
          (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k) *
          (∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), errorProfile (Qof A N) N q k) := by
  rw [← triple_sum_mul (I1 := Icc 1 (cutoff (10 ^ 4 * A) N))
    (I2 := Icc 1 (cutoff (10 ^ 4 * A) N)) (I3 := Icc 1 (cutoff3 (10 ^ 4 * A) N))
    (Iq := Icc 1 ⌊Qof A N⌋₊) (c := 2 * Qof A N / N)
    (d := fun k q => errorProfile (Qof A N) N q k)]
  unfold scalarMean scalarEnvelope
  refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun k₂ _ =>
    Finset.sum_congr rfl (fun k₃ _ => Finset.sum_congr rfl (fun q _ => ?_))))
  exact scalarArc_eq (Qof A N) N q k₁ k₂ k₃

/-- The theta sum is monotone in the outer cutoff. -/
theorem theta_sum_mono {N q : ℕ} {k k' : ℕ} (h : k ≤ k') :
    (∑ m ∈ Icc 1 k, thetaError N (Nat.lcm m q)) ≤
      ∑ m ∈ Icc 1 k', thetaError N (Nat.lcm m q) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
    (fun _ _ _ => thetaError_nonneg _ _)

/-- Three factors bounded by one common nonnegative bound. -/
theorem prod_three_le {a₀ a₁ a₂ b : ℝ} (h₀ : a₀ ≤ b) (h₁ : a₁ ≤ b) (h₂ : a₂ ≤ b)
    (n₁ : 0 ≤ a₁) (n₂ : 0 ≤ a₂) (nb : 0 ≤ b) :
    a₀ * a₁ * a₂ ≤ b ^ 3 := by
  calc a₀ * a₁ * a₂ ≤ b * b * b := by
        refine mul_le_mul (mul_le_mul h₀ h₁ n₁ nb) h₂ n₂ (by positivity)
    _ = b ^ 3 := by ring


/-- Step 1 of the leaf: the three factorized error-profile sums are dominated by
one cube of a theta sum plus the logarithmic profile. -/
theorem mean_le_cube (A : ℝ) (hA : 10 ^ 4 ≤ A) {N : ℕ} (hN : 3 ≤ N) :
    scalarMean 3 A N ≤
      (2 * Qof A N / N) * ((1 + 2 * π) * Qof A N) ^ 3 *
        ∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
          ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
            (cutoff (10 ^ 4 * A) N : ℝ) *
              ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 3 := by
  have hN1 : 1 < N := by omega
  have hLnn : (0 : ℝ) ≤ Real.log N := Real.log_natCast_nonneg N
  have hQnn : (0 : ℝ) ≤ Qof A N := Real.rpow_nonneg hLnn _
  have hfac0 : (0 : ℝ) ≤ (1 + 2 * π) * Qof A N := by positivity
  have hK3le : cutoff3 (10 ^ 4 * A) N ≤ cutoff (10 ^ 4 * A) N :=
    cutoff3_le_cutoff_local (B := 10 ^ 4 * A) hN1
  rw [scalarMean_eq]
  have hconst : (0 : ℝ) ≤ 2 * Qof A N / N :=
    div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hQnn) (Nat.cast_nonneg N)
  have hinner : (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
      (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k) *
      (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k) *
      (∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), errorProfile (Qof A N) N q k))
      ≤ ∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
          ((1 + 2 * π) * Qof A N) ^ 3 *
            ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
              (cutoff (10 ^ 4 * A) N : ℝ) *
                ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 3 := by
    refine Finset.sum_le_sum (fun q hq => ?_)
    have hq1 : (1 : ℕ) ≤ q := (Finset.mem_Icc.mp hq).1
    have hS := fun (k : ℕ) => inner_sum_eq (Qof A N) N q k
    rw [hS (cutoff (10 ^ 4 * A) N)]
    rw [hS (cutoff3 (10 ^ 4 * A) N)]
    set c : ℝ := (Real.log q / Real.log 2 * Real.log N) / q with hc
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
    have hc0 : 0 ≤ c := by
      rw [hc]
      exact div_nonneg (mul_nonneg (div_nonneg (Real.log_natCast_nonneg q)
        (by linarith [Real.log_two_gt_d9])) hLnn) hqpos.le
    have hTle : (∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) ≤
        ∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q) :=
      theta_sum_mono hK3le
    have hcast : ((cutoff3 (10 ^ 4 * A) N : ℝ)) ≤ ((cutoff (10 ^ 4 * A) N : ℝ)) := by
      exact_mod_cast hK3le
    have hX : (∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
          (cutoff3 (10 ^ 4 * A) N : ℝ) * c ≤
        (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
          (cutoff (10 ^ 4 * A) N : ℝ) * c := by
      have := mul_le_mul_of_nonneg_right hcast hc0
      linarith
    have hTnn : (0 : ℝ) ≤ ∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q) :=
      Finset.sum_nonneg (fun _ _ => thetaError_nonneg _ _)
    have hT3nn : (0 : ℝ) ≤ ∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), thetaError N (Nat.lcm k q) :=
      Finset.sum_nonneg (fun _ _ => thetaError_nonneg _ _)
    have hb0 : (0 : ℝ) ≤ (1 + 2 * π) * Qof A N *
        ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
          (cutoff (10 ^ 4 * A) N : ℝ) * c) := by
      refine mul_nonneg hfac0 ?_
      have := mul_nonneg (Nat.cast_nonneg (cutoff (10 ^ 4 * A) N) : (0 : ℝ) ≤ _) hc0
      linarith
    have hb2 : (0 : ℝ) ≤ (1 + 2 * π) * Qof A N *
        ((∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
          (cutoff3 (10 ^ 4 * A) N : ℝ) * c) := by
      refine mul_nonneg hfac0 ?_
      have := mul_nonneg (Nat.cast_nonneg (cutoff3 (10 ^ 4 * A) N) : (0 : ℝ) ≤ _) hc0
      linarith
    have hmain := prod_three_le (a₀ := (1 + 2 * π) * Qof A N *
        ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
          (cutoff (10 ^ 4 * A) N : ℝ) * c))
      (a₁ := (1 + 2 * π) * Qof A N *
        ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
          (cutoff (10 ^ 4 * A) N : ℝ) * c))
      (a₂ := (1 + 2 * π) * Qof A N *
        ((∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
          (cutoff3 (10 ^ 4 * A) N : ℝ) * c))
      le_rfl le_rfl (mul_le_mul_of_nonneg_left hX hfac0) hb0 hb2 hb0
    calc (1 + 2 * π) * Qof A N *
          ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
            (cutoff (10 ^ 4 * A) N : ℝ) * c) *
        ((1 + 2 * π) * Qof A N *
          ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
            (cutoff (10 ^ 4 * A) N : ℝ) * c)) *
        ((1 + 2 * π) * Qof A N *
          ((∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
            (cutoff3 (10 ^ 4 * A) N : ℝ) * c)) ≤ _ := hmain
      _ = ((1 + 2 * π) * Qof A N) ^ 3 *
          ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
            (cutoff (10 ^ 4 * A) N : ℝ) * c) ^ 3 := by ring
  calc (2 * Qof A N / N) * (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
      (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k) *
      (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), errorProfile (Qof A N) N q k) *
      (∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), errorProfile (Qof A N) N q k))
      ≤ (2 * Qof A N / N) * ∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
          ((1 + 2 * π) * Qof A N) ^ 3 *
            ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
              (cutoff (10 ^ 4 * A) N : ℝ) *
                ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 3 :=
        mul_le_mul_of_nonneg_left hinner hconst
    _ = (2 * Qof A N / N) * ((1 + 2 * π) * Qof A N) ^ 3 *
          ∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
            ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
              (cutoff (10 ^ 4 * A) N : ℝ) *
                ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 3 := by
        rw [← Finset.mul_sum]
        ring


theorem rpow_pow_local {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (n : ℕ) : (x ^ a) ^ n = x ^ (n * a) := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx]
  congr 1
  ring

theorem rpow_mul_rpow_local {x : ℝ} (hx : 0 < x) (a b : ℝ) : x ^ a * x ^ b = x ^ (a + b) :=
  (Real.rpow_add hx a b).symm

set_option maxHeartbeats 1000000 in
theorem arith_two_terms {A CL Q L hN h : ℝ} (hA : 10 ^ 4 ≤ A) (hCL0 : 0 ≤ CL)
    (hN3 : (3 : ℝ) ≤ hN) (hLdef : L = Real.log hN) (hQdef : Q = L ^ (20 * A))
    (hK1 : (0 : ℝ) ≤ L ^ (-(10 ^ 4 * A)) * Real.sqrt hN)
    (hHn : h ≤ 40 * A * L) (hh0 : 0 ≤ h) :
    (2 * Q / hN) * ((1 + 2 * π) * Q) ^ 3 *
        (8 * (Q ^ 3 * (h ^ 8 * (CL * hN * L ^ (-(100 * A))) ^ 3)) +
          8 * (Real.sqrt hN * L ^ (-(10 ^ 4 * A))) ^ 3 *
            (8 * L ^ 3 * (20 * A * L) ^ 3 * Q))
      ≤ (16 * (40 * A) ^ 8 * (1 + 2 * π) ^ 3 * CL ^ 3 +
          1024000 * (1 + 2 * π) ^ 3 * A ^ 3) * hN ^ 2 * L ^ (-A) := by
  have hN0 : (0 : ℝ) < hN := by linarith
  have hN1 : (1 : ℝ) < hN := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith : (0:ℝ) < hN)]
    nlinarith [Real.exp_one_lt_d9]
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := hLpos.le
  have hQnn : 0 ≤ Q := by rw [hQdef]; exact Real.rpow_nonneg hLnn _
  have hQ7 : Q ^ 7 = L ^ (140 * A) := by
    rw [hQdef, rpow_pow_local hLnn]
    congr 1
    ring
  have hQ5 : Q ^ 5 = L ^ (100 * A) := by
    rw [hQdef, rpow_pow_local hLnn]
    congr 1
    ring
  have hs3 : (Real.sqrt hN) ^ 3 = hN ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, rpow_pow_local hN0.le]
    congr 1
    ring
  have hB3 : (L ^ (-(10 ^ 4 * A))) ^ 3 = L ^ (-(3 * (10 ^ 4 * A))) := by
    rw [rpow_pow_local hLnn]
    congr 1
    ring
  -- factor out and split
  have hsplit : (2 * Q / hN) * ((1 + 2 * π) * Q) ^ 3 *
        (8 * (Q ^ 3 * (h ^ 8 * (CL * hN * L ^ (-(100 * A))) ^ 3)) +
          8 * (Real.sqrt hN * L ^ (-(10 ^ 4 * A))) ^ 3 *
            (8 * L ^ 3 * (20 * A * L) ^ 3 * Q))
      = (2 * Q / hN) * ((1 + 2 * π) * Q) ^ 3 *
          (8 * (Q ^ 3 * (h ^ 8 * (CL * hN * L ^ (-(100 * A))) ^ 3)))
        + (2 * Q / hN) * ((1 + 2 * π) * Q) ^ 3 *
          (8 * (Real.sqrt hN * L ^ (-(10 ^ 4 * A))) ^ 3 *
            (8 * L ^ 3 * (20 * A * L) ^ 3 * Q)) := by ring
  rw [hsplit]
  have hCnn : (0 : ℝ) ≤ (2 * Q / hN) * ((1 + 2 * π) * Q) ^ 3 := by positivity
  have hT : (2 * Q / hN) * ((1 + 2 * π) * Q) ^ 3 *
        (8 * (Q ^ 3 * (h ^ 8 * (CL * hN * L ^ (-(100 * A))) ^ 3)))
      ≤ 16 * (40 * A) ^ 8 * (1 + 2 * π) ^ 3 * CL ^ 3 * hN ^ 2 * L ^ (-A) := by
    have hA8 : h ^ 8 ≤ (40 * A * L) ^ 8 := pow_le_pow_left₀ hh0 hHn 8
    have hXnn : (0 : ℝ) ≤ CL * hN * L ^ (-(100 * A)) := by positivity
    have hstep : (2 * Q / hN) * ((1 + 2 * π) * Q) ^ 3 *
          (8 * (Q ^ 3 * (h ^ 8 * (CL * hN * L ^ (-(100 * A))) ^ 3)))
        ≤ (2 * Q / hN) * ((1 + 2 * π) * Q) ^ 3 *
          (8 * (Q ^ 3 * ((40 * A * L) ^ 8 * (CL * hN * L ^ (-(100 * A))) ^ 3))) := by
      refine mul_le_mul_of_nonneg_left ?_ hCnn
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 8)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA8 (by positivity))
        (pow_nonneg hQnn 3)
    refine hstep.trans ?_
    have hp : (CL * hN * L ^ (-(100 * A))) ^ 3 = CL ^ 3 * hN ^ 3 * L ^ (-(300 * A)) := by
      rw [show (CL * hN * L ^ (-(100 * A))) ^ 3 =
        CL ^ 3 * hN ^ 3 * (L ^ (-(100 * A))) ^ 3 from by ring, rpow_pow_local hLnn]
      congr 2
      ring
    have hid : (2 * Q / hN) * ((1 + 2 * π) * Q) ^ 3 *
          (8 * (Q ^ 3 * ((40 * A * L) ^ 8 * (CL * hN * L ^ (-(100 * A))) ^ 3)))
        = 16 * (1 + 2 * π) ^ 3 * (40 * A) ^ 8 * CL ^ 3 * Q ^ 7 * hN ^ 2 *
            (L ^ ((8 : ℕ) : ℝ) * L ^ (-(300 * A))) := by
      rw [hp, show (40 * A * L) ^ 8 = (40 * A) ^ 8 * L ^ 8 from by rw [mul_pow],
        Real.rpow_natCast L 8]
      field_simp
      ring
    rw [hid, hQ7]
    have e1 : L ^ ((8 : ℕ) : ℝ) * L ^ (-(300 * A)) = L ^ (((8 : ℕ) : ℝ) + -(300 * A)) :=
      rpow_mul_rpow_local hLpos _ _
    have e2 : L ^ (140 * A) * L ^ (((8 : ℕ) : ℝ) + -(300 * A)) =
        L ^ (140 * A + (((8 : ℕ) : ℝ) + -(300 * A))) := rpow_mul_rpow_local hLpos _ _
    have hcore : L ^ (140 * A) * (L ^ ((8 : ℕ) : ℝ) * L ^ (-(300 * A))) ≤ L ^ (-A) := by
      rw [e1, e2]
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      push_cast
      nlinarith
    have hfac : 16 * (1 + 2 * π) ^ 3 * (40 * A) ^ 8 * CL ^ 3 * L ^ (140 * A) * hN ^ 2 *
          (L ^ ((8 : ℕ) : ℝ) * L ^ (-(300 * A)))
        = (16 * (1 + 2 * π) ^ 3 * (40 * A) ^ 8 * CL ^ 3 * hN ^ 2) *
            (L ^ (140 * A) * (L ^ ((8 : ℕ) : ℝ) * L ^ (-(300 * A)))) := by ring
    rw [hfac]
    refine (mul_le_mul_of_nonneg_left hcore (by positivity)).trans (le_of_eq ?_)
    ring
  have hB : (2 * Q / hN) * ((1 + 2 * π) * Q) ^ 3 *
        (8 * (Real.sqrt hN * L ^ (-(10 ^ 4 * A))) ^ 3 *
          (8 * L ^ 3 * (20 * A * L) ^ 3 * Q))
      ≤ 1024000 * (1 + 2 * π) ^ 3 * A ^ 3 * hN ^ 2 * L ^ (-A) := by
    have hcube : (Real.sqrt hN * L ^ (-(10 ^ 4 * A))) ^ 3 =
        hN ^ ((3 : ℝ) / 2) * L ^ (-(3 * (10 ^ 4 * A))) := by
      rw [show (Real.sqrt hN * L ^ (-(10 ^ 4 * A))) ^ 3 =
        (Real.sqrt hN) ^ 3 * (L ^ (-(10 ^ 4 * A))) ^ 3 from by ring, hs3, hB3]
    have hN32 : hN ^ ((3 : ℝ) / 2) = hN ^ (1 : ℝ) * hN ^ ((1 : ℝ) / 2) := by
      have e := rpow_mul_rpow_local hN0 (1 : ℝ) ((1 : ℝ) / 2)
      rw [e]
      congr 1
      norm_num
    have hfirst : (2 * Q / hN) * ((1 + 2 * π) * Q) ^ 3 *
          (8 * (hN ^ ((3 : ℝ) / 2) * L ^ (-(3 * (10 ^ 4 * A)))) *
            (8 * L ^ 3 * (20 * A * L) ^ 3 * Q))
        = 128 * (1 + 2 * π) ^ 3 * (20 * A) ^ 3 * Q ^ 5 *
            (hN ^ ((1 : ℝ) / 2) * L ^ (-(3 * (10 ^ 4 * A))) * (L ^ 3 * L ^ 3)) := by
      rw [hN32, show (20 * A * L) ^ 3 = (20 * A) ^ 3 * L ^ 3 from by rw [mul_pow],
        Real.rpow_one]
      field_simp
      ring
    rw [hcube, hfirst]
    have hL6 : L ^ 3 * L ^ 3 = L ^ ((6 : ℕ) : ℝ) := by
      have e : L ^ ((3 : ℕ) : ℝ) * L ^ ((3 : ℕ) : ℝ) = L ^ (((3 : ℕ) : ℝ) + ((3 : ℕ) : ℝ)) :=
        rpow_mul_rpow_local hLpos _ _
      rw [← Real.rpow_natCast L 3, e]
      congr 1
      push_cast
      norm_num
    have hsecond : 128 * (1 + 2 * π) ^ 3 * (20 * A) ^ 3 * Q ^ 5 *
          (hN ^ ((1 : ℝ) / 2) * L ^ (-(3 * (10 ^ 4 * A))) * (L ^ 3 * L ^ 3))
        = 1024000 * (1 + 2 * π) ^ 3 * A ^ 3 * hN ^ ((1 : ℝ) / 2) *
            (L ^ (-(3 * (10 ^ 4 * A))) * (L ^ ((6 : ℕ) : ℝ) * L ^ (100 * A))) := by
      rw [hQ5, hL6]
      ring
    rw [hsecond]
    have e3 : L ^ ((6 : ℕ) : ℝ) * L ^ (100 * A) = L ^ (((6 : ℕ) : ℝ) + 100 * A) :=
      rpow_mul_rpow_local hLpos _ _
    have e4 : L ^ (-(3 * (10 ^ 4 * A))) * L ^ (((6 : ℕ) : ℝ) + 100 * A) =
        L ^ (-(3 * (10 ^ 4 * A)) + (((6 : ℕ) : ℝ) + 100 * A)) := rpow_mul_rpow_local hLpos _ _
    have hcore : L ^ (-(3 * (10 ^ 4 * A))) * (L ^ ((6 : ℕ) : ℝ) * L ^ (100 * A)) ≤ L ^ (-A) := by
      rw [e3, e4]
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      push_cast
      nlinarith
    have hN12 : hN ^ ((1 : ℝ) / 2) ≤ hN ^ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le hN1.le (by norm_num : (1 : ℝ) / 2 ≤ (2 : ℕ))
      rwa [Real.rpow_natCast] at h
    have hc : (0 : ℝ) ≤ 1024000 * (1 + 2 * π) ^ 3 * A ^ 3 := by positivity
    have hprod := mul_le_mul hN12 hcore (by positivity) (by positivity)
    nlinarith [hprod, hc]
  refine (add_le_add hT hB).trans (le_of_eq ?_)
  ring

/-- `log q ≤ 20 A log N` for `q ≤ Q = (log N)^{20 A}`. -/
theorem log_le_log_Q_local {A : ℝ} (hA : 0 ≤ A) {N q : ℕ} (hN : 2 ≤ N)
    (hq : (q : ℝ) ≤ Qof A N) : Real.log q ≤ 20 * A * Real.log N := by
  have hN1 : (1 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hL : (0 : ℝ) < Real.log N := Real.log_pos hN1
  have h20 : (0 : ℝ) ≤ 20 * A := by linarith
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h
    simp only [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg h20 hL.le
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast h
    have h1 : Real.log q ≤ Real.log (Qof A N) := Real.log_le_log hq0 hq
    have h2 : Real.log (Qof A N) = 20 * A * Real.log (Real.log N) := by
      unfold Qof
      rw [Real.log_rpow hL]
    have h3 : Real.log (Real.log N) ≤ Real.log N := Real.log_le_self hL.le
    have h4 := mul_le_mul_of_nonneg_left h3 h20
    linarith

/-- The logarithmic profile costs at most one `(40 A log N)³` per modulus. -/
theorem sum_c_cube_le {A : ℝ} (hA : 10 ^ 4 ≤ A) {N : ℕ} (hN : 3 ≤ N) :
    (∑ q ∈ Icc 1 ⌊Qof A N⌋₊, ((Real.log q / Real.log 2 * Real.log N) / q) ^ 3)
      ≤ 8 * Real.log N ^ 3 * (20 * A * Real.log N) ^ 3 * Qof A N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3r : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    nlinarith [Real.exp_one_lt_d9]
  have hLpos : (0 : ℝ) < Real.log N := by linarith
  have hQnn : (0 : ℝ) ≤ Qof A N := Real.rpow_nonneg hLpos.le _
  have hlog2 : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpoint : ∀ q ∈ Icc 1 ⌊Qof A N⌋₊,
      ((Real.log q / Real.log 2 * Real.log N) / q) ^ 3 ≤ (40 * A * Real.log N * Real.log N) ^ 3 := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hqQ : (q : ℝ) ≤ Qof A N := by
      have h2 : (q : ℝ) ≤ ((⌊Qof A N⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hq).2
      exact h2.trans (Nat.floor_le hQnn)
    have hlogq : Real.log q ≤ 20 * A * Real.log N :=
      log_le_log_Q_local (by linarith) (by omega) hqQ
    have hlq : (0 : ℝ) ≤ Real.log q := Real.log_natCast_nonneg q
    have hratio : Real.log q / Real.log 2 ≤ 2 * Real.log q := by
      rw [div_le_iff₀ hlog2]
      nlinarith [Real.log_two_gt_d9]
    have hnum : Real.log q / Real.log 2 * Real.log N ≤ 40 * A * Real.log N * Real.log N := by
      have hmul : Real.log q / Real.log 2 * Real.log N ≤ 2 * Real.log q * Real.log N :=
        mul_le_mul_of_nonneg_right hratio hLpos.le
      have h2L : (0 : ℝ) ≤ 2 * Real.log N := by linarith
      have h20 : 2 * Real.log q * Real.log N ≤ 2 * (20 * A * Real.log N) * Real.log N := by
        have hh := mul_le_mul_of_nonneg_left hlogq h2L
        nlinarith [hh]
      have heq : 2 * (20 * A * Real.log N) * Real.log N = 40 * A * Real.log N * Real.log N := by
        ring
      exact hmul.trans (h20.trans (le_of_eq heq))
    have hnum0 : (0 : ℝ) ≤ Real.log q / Real.log 2 * Real.log N := by
      have : (0 : ℝ) ≤ Real.log q / Real.log 2 := div_nonneg hlq hlog2.le
      exact mul_nonneg this hLpos.le
    have hle : (Real.log q / Real.log 2 * Real.log N) / q ≤ 40 * A * Real.log N * Real.log N := by
      rw [div_le_iff₀ hq0]
      have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
      have hb0 : (0 : ℝ) ≤ 40 * A * Real.log N * Real.log N := by positivity
      have hle' : 40 * A * Real.log N * Real.log N ≤ 40 * A * Real.log N * Real.log N * q := by
        nlinarith [hb0, hq1']
      linarith [hnum, hle']
    have hle0 : (0 : ℝ) ≤ (Real.log q / Real.log 2 * Real.log N) / q :=
      div_nonneg hnum0 hq0.le
    exact pow_le_pow_left₀ hle0 hle 3
  refine (Finset.sum_le_sum hpoint).trans ?_
  have hcard : (((Icc 1 ⌊Qof A N⌋₊).card : ℕ) : ℝ) ≤ Qof A N := by
    have h1 : (Icc 1 ⌊Qof A N⌋₊).card ≤ ⌊Qof A N⌋₊ := by
      rw [Nat.card_Icc]
      omega
    exact (by exact_mod_cast h1 : ((Icc 1 ⌊Qof A N⌋₊).card : ℝ) ≤ ((⌊Qof A N⌋₊ : ℕ) : ℝ)).trans
      (Nat.floor_le hQnn)
  have hcardle : ∑ _q ∈ Icc 1 ⌊Qof A N⌋₊, (40 * A * Real.log N * Real.log N) ^ 3
      ≤ Qof A N * (40 * A * Real.log N * Real.log N) ^ 3 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  refine hcardle.trans (le_of_eq ?_)
  have hEq : (40 * A * Real.log N * Real.log N) ^ 3 = 8 * Real.log N ^ 3 * (20 * A * Real.log N) ^ 3 := by
    ring
  rw [hEq]
  ring

/-- The averaged theta cube, straight from `product_lcm_average` at `r = 3`. -/
theorem sum_T_cube_le {A CL : ℝ} (hA : 10 ^ 4 ≤ A) {N : ℕ} (hN : 3 ≤ N)
    (hCL : ∀ N : ℕ, 3 ≤ N → 1 ≤ Real.log N → ∀ r : ℕ, 1 ≤ r → ∀ K : Fin r → ℕ,
      (∀ i, K i ≤ cutoff (10 ^ 4 * A) N) →
        (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
          (∏ i : Fin r, ∑ k ∈ Icc 1 (K i), thetaError N (Nat.lcm k q)) / (q : ℝ) ^ r)
          ≤ Hn ⌊Qof A N⌋₊ ^ 2 ^ r * (CL * (N : ℝ) / Real.log N ^ (100 * A)) ^ r) :
    (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
        (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) ^ 3)
      ≤ Qof A N ^ 3 * (Hn ⌊Qof A N⌋₊ ^ 8 *
          (CL * (N : ℝ) * Real.log N ^ (-(100 * A))) ^ 3) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3r : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    nlinarith [Real.exp_one_lt_d9]
  have hLpos : (0 : ℝ) < Real.log N := by linarith
  have hQnn : (0 : ℝ) ≤ Qof A N := Real.rpow_nonneg hLpos.le _
  have hQpos : (0 : ℝ) < Qof A N :=
    lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hL1 (by linarith : (0 : ℝ) ≤ 20 * A))
  have h := hCL N hN hL1 3 (by norm_num) (fun _ : Fin 3 => cutoff (10 ^ 4 * A) N)
    (fun _ => le_rfl)
  have hprod : ∀ q, (∏ i : Fin 3, ∑ k ∈ Icc 1 ((fun _ : Fin 3 => cutoff (10 ^ 4 * A) N) i),
      thetaError N (Nat.lcm k q))
      = (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) ^ 3 := by
    intro q
    rw [Fin.prod_univ_three]
    ring
  simp only [hprod, show (2 : ℕ) ^ 3 = 8 from by norm_num] at h
  have hconv : (CL * (N : ℝ) / Real.log N ^ (100 * A)) ^ 3 =
      (CL * (N : ℝ) * Real.log N ^ (-(100 * A))) ^ 3 := by
    have h1 : Real.log N ^ (-(100 * A)) = (Real.log N ^ (100 * A))⁻¹ :=
      Real.rpow_neg hLpos.le _
    rw [h1, div_eq_mul_inv]
  rw [hconv] at h
  have hpoint : ∀ q ∈ Icc 1 ⌊Qof A N⌋₊,
      (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) ^ 3
        ≤ Qof A N ^ 3 * ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N),
            thetaError N (Nat.lcm k q)) ^ 3 / (q : ℝ) ^ 3) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hqQ : (q : ℝ) ≤ Qof A N := by
      have h2 : (q : ℝ) ≤ ((⌊Qof A N⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hq).2
      exact h2.trans (Nat.floor_le hQnn)
    have hTc : (0 : ℝ) ≤ (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N),
        thetaError N (Nat.lcm k q)) ^ 3 :=
      pow_nonneg (Finset.sum_nonneg (fun _ _ => thetaError_nonneg _ _)) 3
    have hid : (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) ^ 3
        = (q : ℝ) ^ 3 * ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N),
            thetaError N (Nat.lcm k q)) ^ 3 / (q : ℝ) ^ 3) := by
      field_simp
    conv_lhs => rw [hid]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0.le hqQ 3)
      (div_nonneg hTc (pow_nonneg hq0.le 3))
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h (pow_nonneg hQnn 3)

/-- A cube of a sum of two nonnegative reals costs eight times the two cubes. -/
theorem add_cube_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) ^ 3 ≤ 8 * (a ^ 3 + b ^ 3) := by
  have hm : max a b = a ∨ max a b = b := max_choice a b
  have h1 : a ≤ max a b := le_max_left a b
  have h2 : b ≤ max a b := le_max_right a b
  have h0 : (0 : ℝ) ≤ max a b := le_trans ha h1
  have hle : a + b ≤ 2 * max a b := by linarith
  have hcube : (a + b) ^ 3 ≤ (2 * max a b) ^ 3 := pow_le_pow_left₀ (by linarith) hle 3
  have ha3 : (0 : ℝ) ≤ a ^ 3 := pow_nonneg ha 3
  have hb3 : (0 : ℝ) ≤ b ^ 3 := pow_nonneg hb 3
  rcases hm with h | h
  · rw [h] at hcube
    nlinarith
  · rw [h] at hcube
    nlinarith

set_option maxHeartbeats 2000000 in
/-- **The leaf, proved.** `cubic_scalar_mean`, from the lab's own averaged theta
input `product_lcm_average`. -/
theorem cubic_scalar_mean_proof :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      scalarMean 3 A N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA
  obtain ⟨CL, hCL⟩ := product_lcm_average A hA
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
    nlinarith [Real.exp_one_lt_d9]
  have hQ3 : (1 : ℝ) ≤ Qof A 3 := Real.one_le_rpow hlog3 (by linarith)
  have hfl3 : 1 ≤ ⌊Qof A 3⌋₊ := Nat.le_floor (by simpa using hQ3)
  have hHnpos : 0 < Hn ⌊Qof A 3⌋₊ := by
    have h1 : ((1 : ℕ) : ℝ)⁻¹ ≤ Hn ⌊Qof A 3⌋₊ :=
      Finset.single_le_sum (f := fun j : ℕ => ((j : ℝ))⁻¹) (fun i _ => by positivity)
        (Finset.mem_Icc.mpr ⟨le_rfl, hfl3⟩)
    have h2 : (1 : ℝ) ≤ Hn ⌊Qof A 3⌋₊ := by simpa using h1
    linarith
  have hCL0 : 0 ≤ CL := by
    have h := hCL 3 (by norm_num) hlog3 3 (by norm_num) (fun _ : Fin 3 => 0) (fun _ => by simp)
    have hzero : (∑ q ∈ Icc 1 ⌊Qof A 3⌋₊,
        (∏ i : Fin 3, ∑ k ∈ Icc 1 ((fun _ : Fin 3 => 0) i), thetaError 3 (Nat.lcm k q))
          / (q : ℝ) ^ (3 : ℕ)) = 0 := by simp
    rw [hzero] at h
    have hx : (0 : ℝ) < (3 : ℝ) / Real.log 3 ^ (100 * A) := by
      have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Real.log 3) (100 * A)
      positivity
    have h8 : (0 : ℝ) ≤ Hn ⌊Qof A 3⌋₊ ^ 8 * (CL * ((3 : ℝ) / Real.log 3 ^ (100 * A))) ^ 3 := by
      convert h using 2 <;> ring
    have hcub : (0 : ℝ) ≤ (CL * ((3 : ℝ) / Real.log 3 ^ (100 * A))) ^ 3 :=
      (mul_nonneg_iff_of_pos_left (pow_pos hHnpos 8)).mp h8
    have hcl : (0 : ℝ) ≤ CL * ((3 : ℝ) / Real.log 3 ^ (100 * A)) := by
      rcases le_total 0 (CL * ((3 : ℝ) / Real.log 3 ^ (100 * A))) with hpos | hneg
      · exact hpos
      · rcases lt_trichotomy (CL * ((3 : ℝ) / Real.log 3 ^ (100 * A))) 0 with hlt | heq | hgt
        · exfalso
          have h2 : (0 : ℝ) < (CL * ((3 : ℝ) / Real.log 3 ^ (100 * A))) *
              (CL * ((3 : ℝ) / Real.log 3 ^ (100 * A))) := by nlinarith
          have h3 : (CL * ((3 : ℝ) / Real.log 3 ^ (100 * A))) ^ 3 < 0 := by
            have h4 : (CL * ((3 : ℝ) / Real.log 3 ^ (100 * A))) ^ 3 =
                (CL * ((3 : ℝ) / Real.log 3 ^ (100 * A))) *
                  (CL * ((3 : ℝ) / Real.log 3 ^ (100 * A))) *
                  (CL * ((3 : ℝ) / Real.log 3 ^ (100 * A))) := by ring
            rw [h4]
            nlinarith
          linarith
        · linarith
        · exact hgt.le
    exact (mul_nonneg_iff_of_pos_right hx).mp hcl
  refine ⟨16 * (40 * A) ^ 8 * (1 + 2 * π) ^ 3 * CL ^ 3 + 1024000 * (1 + 2 * π) ^ 3 * A ^ 3,
    3, fun N hodd hN => ?_⟩
  have hN3 : 3 ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    nlinarith [Real.exp_one_lt_d9]
  have hLpos : 0 < Real.log N := by linarith
  have hQnn : 0 ≤ Qof A N := Real.rpow_nonneg hLpos.le _
  have hK1le : ((cutoff (10 ^ 4 * A) N : ℕ) : ℝ) ≤
      Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A)) := by
    rw [cutoff]
    exact Nat.floor_le (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hLpos.le _))
  have hHn40 : Hn ⌊Qof A N⌋₊ ≤ 40 * A * Real.log N := by
    have h1 : Hn ⌊Qof A N⌋₊ ≤ 1 + Real.log ((⌊Qof A N⌋₊ : ℕ) : ℝ) := Hn_le _
    have h2 : Real.log ((⌊Qof A N⌋₊ : ℕ) : ℝ) ≤ 20 * A * Real.log N := by
      rcases Nat.eq_zero_or_pos ⌊Qof A N⌋₊ with h | h
      · rw [h]
        simp only [Nat.cast_zero, Real.log_zero]
        nlinarith [hLpos]
      · refine le_trans (Real.log_le_log (by exact_mod_cast h) (Nat.floor_le hQnn)) ?_
        unfold Qof
        rw [Real.log_rpow hLpos]
        have h3 : Real.log (Real.log N) ≤ Real.log N := Real.log_le_self hLpos.le
        exact mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 20 * A)
    have h3 : (1 : ℝ) ≤ 20 * A * Real.log N := by nlinarith [hA, hL1]
    linarith
  have h1 := mean_le_cube A hA hN3
  have hsplit : (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
      ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
        (cutoff (10 ^ 4 * A) N : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 3)
      ≤ 8 * (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
          (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) ^ 3)
        + 8 * ((cutoff (10 ^ 4 * A) N : ℝ) ^ 3 *
          (∑ q ∈ Icc 1 ⌊Qof A N⌋₊, ((Real.log q / Real.log 2 * Real.log N) / q) ^ 3)) := by
    have hp : ∀ q ∈ Icc 1 ⌊Qof A N⌋₊,
        ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
          (cutoff (10 ^ 4 * A) N : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 3
        ≤ 8 * ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) ^ 3 +
          ((cutoff (10 ^ 4 * A) N : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 3) := by
      intro q hq
      refine add_cube_le ?_ ?_
      · exact Finset.sum_nonneg (fun _ _ => thetaError_nonneg _ _)
      · refine mul_nonneg (Nat.cast_nonneg _) ?_
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
        exact div_nonneg (mul_nonneg (div_nonneg (Real.log_natCast_nonneg q)
          (by linarith [Real.log_two_gt_d9])) hLpos.le) hq0.le
    refine (Finset.sum_le_sum hp).trans (le_of_eq ?_)
    have hstep : ∀ q, 8 * ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N),
          thetaError N (Nat.lcm k q)) ^ 3 +
          ((cutoff (10 ^ 4 * A) N : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 3)
        = 8 * (∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) ^ 3
          + (8 * (cutoff (10 ^ 4 * A) N : ℝ) ^ 3) *
            ((Real.log q / Real.log 2 * Real.log N) / q) ^ 3 := by
      intro q
      rw [mul_pow]
      ring
    simp only [hstep, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hT := sum_T_cube_le (A := A) (CL := CL) hA hN3 hCL
  have hc := sum_c_cube_le (A := A) hA hN3
  have hK13 : ((cutoff (10 ^ 4 * A) N : ℕ) : ℝ) ^ 3 ≤
      (Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A))) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hK1le 3
  have hbound : (∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
      ((∑ k ∈ Icc 1 (cutoff (10 ^ 4 * A) N), thetaError N (Nat.lcm k q)) +
        (cutoff (10 ^ 4 * A) N : ℝ) * ((Real.log q / Real.log 2 * Real.log N) / q)) ^ 3)
      ≤ 8 * (Qof A N ^ 3 * (Hn ⌊Qof A N⌋₊ ^ 8 *
            (CL * (N : ℝ) * Real.log N ^ (-(100 * A))) ^ 3))
        + 8 * (Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A))) ^ 3 *
            (8 * Real.log N ^ 3 * (20 * A * Real.log N) ^ 3 * Qof A N) := by
    refine hsplit.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left hT (by norm_num)
    · have hCs : (0 : ℝ) ≤ ∑ q ∈ Icc 1 ⌊Qof A N⌋₊,
          ((Real.log q / Real.log 2 * Real.log N) / q) ^ 3 :=
        Finset.sum_nonneg (fun q _ => pow_nonneg
          (div_nonneg (mul_nonneg (div_nonneg (Real.log_natCast_nonneg q)
            (by linarith [Real.log_two_gt_d9])) hLpos.le) (by positivity)) 3)
      have hstep1 : 8 * ((cutoff (10 ^ 4 * A) N : ℕ) : ℝ) ^ 3
          ≤ 8 * (Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A))) ^ 3 :=
        mul_le_mul_of_nonneg_left hK13 (by norm_num)
      have hstep2 : 8 * (((cutoff (10 ^ 4 * A) N : ℕ) : ℝ) ^ 3 *
            (∑ q ∈ Icc 1 ⌊Qof A N⌋₊, ((Real.log q / Real.log 2 * Real.log N) / q) ^ 3))
          ≤ 8 * ((Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A))) ^ 3 *
            (∑ q ∈ Icc 1 ⌊Qof A N⌋₊, ((Real.log q / Real.log 2 * Real.log N) / q) ^ 3)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hK13 hCs) (by norm_num)
      have hstep3 : 8 * ((Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A))) ^ 3 *
            (∑ q ∈ Icc 1 ⌊Qof A N⌋₊, ((Real.log q / Real.log 2 * Real.log N) / q) ^ 3))
          ≤ 8 * ((Real.sqrt N * Real.log N ^ (-(10 ^ 4 * A))) ^ 3 *
            (8 * Real.log N ^ 3 * (20 * A * Real.log N) ^ 3 * Qof A N)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hc (by positivity)) (by norm_num)
      refine hstep2.trans (hstep3.trans (le_of_eq ?_))
      ring
  have harith := arith_two_terms (A := A) (CL := CL) (Q := Qof A N) (L := Real.log N)
    (hN := (N : ℝ)) hA hCL0 hN rfl rfl
    (mul_nonneg (Real.rpow_nonneg hLpos.le _) (Real.sqrt_nonneg N)) hHn40 (Hn_nonneg _)
  have hCnn : (0 : ℝ) ≤ (2 * Qof A N / N) * ((1 + 2 * π) * Qof A N) ^ 3 :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hQnn) (Nat.cast_nonneg N))
      (pow_nonneg (mul_nonneg (by positivity) hQnn) 3)
  exact h1.trans ((mul_le_mul_of_nonneg_left hbound hCnn).trans harith)

/-- Halupczok page 10 to 11, O3, the positive scalar rectangular mean.
Only real theta discrepancies, totients, logarithms and natural modulus sums occur.
There are no prime polynomials, rational phases, residue variables, signed weights
or integrals in this arithmetic leaf. The bad prime profile is explicit. Proved. -/
theorem cubic_scalar_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      scalarMean 3 A N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) :=
  cubic_scalar_mean_proof

/-- Halupczok page 10 to 11, O3, after discrete partial summation on page 7.
Estimate only the static positive degree 3 rational prefix discrepancy average.
There is no beta variable, integral or arbitrary lambda. The full prime interval
and the fixed third residue retain the sealed 2009 adaptation.
Derived from cubic_scalar_mean. -/
theorem cubic_prefix_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
        EF (fun k l => errorEnvelope 3 (Qof A N) (τof A N) k l N)
          (fun _ => 1) l₃ (10 ^ 4 * A) N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, h⟩ := cubic_scalar_mean A hA
  refine ⟨C, max N₀ 3, fun N hodd hN => ?_⟩
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    linarith [Real.exp_one_lt_d9]
  have hQ : 1 ≤ Qof A N := Real.one_le_rpow hL (by linarith)
  exact (prefix_mean_le_scalar 3 A N l₃ hQ (by exact_mod_cast (show (1 : ℝ) ≤ N by linarith))).trans
    (h N hodd ((le_max_left _ _).trans hN))

/-- The exact sealed degree 3 remainder statement.
Derived from the static positive prefix mean. No new integral estimate is assumed. -/
theorem cubic_remainder_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => errorTerm 3 (Qof A N) (τof A N) k l N)
            lam l₃ (10 ^ 4 * A) N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, h⟩ := cubic_prefix_mean A hA l₃ hl₃
  exact ⟨C, N₀, fun lam hlam N hodd hN =>
    (error_mean_bound 3 A lam l₃ N hlam).trans (h N hodd hN)⟩

end LeanLab.Tolev2009.Decomp346c
