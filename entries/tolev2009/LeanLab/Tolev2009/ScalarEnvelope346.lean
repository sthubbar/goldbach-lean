module

public import LeanLab.Tolev2009.RationalCRT346

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 pages 7 to 11, positive discrepancy products before averaging.
The extra rational factor q is retained explicitly.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.ScalarEnvelope346
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Progression346 LeanLab.Tolev2009.Discrepancy346
open LeanLab.Tolev2009.RationalPrefix346 LeanLab.Tolev2009.RationalCRT346

/-- Halupczok page 8, the scalar main profile after the elementary coefficient bound. -/
noncomputable def mainProfile (N q k : ℕ) : ℝ := (N : ℝ) * q / k.totient

/-- Halupczok pages 7 to 8, a scalar error profile with the exact bad prime allowance. -/
noncomputable def errorProfile (Q : ℝ) (N q k : ℕ) : ℝ :=
  (1 + 2 * π) * Q * (thetaError N (Nat.lcm k q) +
    (Real.log q / Real.log 2 * Real.log N) / q)

/-- Halupczok page 8, monotonicity of each positive homogeneous polynomial. -/
theorem positivePart_mono (j : ℕ) (b d B D : Fin 3 → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hd0 : ∀ i, 0 ≤ d i)
    (hB0 : ∀ i, 0 ≤ B i) (hD0 : ∀ i, 0 ≤ D i)
    (hb : ∀ i, b i ≤ B i) (hd : ∀ i, d i ≤ D i) :
    positivePart j b d ≤ positivePart j B D := by
  have hb00 := hb0 0
  have hb01 := hb0 1
  have hb02 := hb0 2
  have hd00 := hd0 0
  have hd01 := hd0 1
  have hd02 := hd0 2
  have hB00 := hB0 0
  have hB01 := hB0 1
  have hB02 := hB0 2
  have hD00 := hD0 0
  have hD01 := hD0 1
  have hD02 := hD0 2
  unfold positivePart
  split_ifs <;> gcongr <;> first | apply hb | apply hd | positivity

/-- Halupczok page 8, the main scalar profile is nonnegative. -/
theorem mainProfile_nonneg (N q k : ℕ) : 0 ≤ mainProfile N q k := by
  unfold mainProfile
  positivity

/-- Halupczok page 8, the error scalar profile is nonnegative for nonnegative Q. -/
theorem errorProfile_nonneg (Q : ℝ) (N q k : ℕ) (hQ : 0 ≤ Q) :
    0 ≤ errorProfile Q N q k := by
  unfold errorProfile
  exact mul_nonneg (mul_nonneg (by positivity) hQ)
    (add_nonneg (thetaError_nonneg _ _) (div_nonneg
      (mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Real.log_nonneg (by norm_num)))
        (Real.log_natCast_nonneg _)) (Nat.cast_nonneg _)))

/-- Halupczok pages 7 to 8, replace the lcm totient by the progression totient. -/
theorem main_profile_bound (k l N q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    (N : ℝ) * ‖mainCoeff k l q a‖ ≤ mainProfile N q k := by
  have hkφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  have hM : 0 < Nat.lcm k q := Nat.lcm_pos hk hq
  have hφ : (k.totient : ℝ) ≤ (Nat.lcm k q).totient := by
    exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr hM)
      (Nat.totient_dvd_of_dvd (Nat.dvd_lcm_left k q))
  have hc := (mainCoeff_norm_le k l q a hk hq).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg q) hkφ hφ)
  simpa only [mainProfile, mul_div_assoc] using mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg N)

/-- Halupczok page 8, the scalar error profile controls a complete rational arc. -/
theorem error_profile_bound (Q : ℝ) (k l N q a : ℕ) (hQ : 1 ≤ Q)
    (hk : 1 ≤ k) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q)
    (hl : Nat.Coprime l k) (hN : 1 ≤ N) :
    (1 + 2 * π * |1 / ((q : ℝ) * ((N : ℝ) / Q))| * N) * prefixError k l q a N ≤
      errorProfile Q N q k := by
  have hQ0 : 0 < Q := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : |1 / ((q : ℝ) * ((N : ℝ) / Q))| = Q / ((q : ℝ) * N) := by
    rw [abs_of_pos (by positivity)]
    field_simp
  have hfac : 1 + 2 * π * |1 / ((q : ℝ) * ((N : ℝ) / Q))| * N ≤
      (1 + 2 * π) * (Q / q) := by
    rw [hs]
    have he : 2 * π * (Q / ((q : ℝ) * N)) * N = 2 * π * (Q / q) := by field_simp
    rw [he]
    have hx := (one_le_div hq0).mpr hqQ
    nlinarith
  refine (mul_le_mul hfac (prefixError_le_theta k l N q a hk hq hl hN)
    (prefixError_nonneg _ _ _ _ _) (by positivity)).trans_eq ?_
  unfold errorProfile
  field_simp

/-- Halupczok page 8, the scalar degree j bound after summing the rational numerators. -/
noncomputable def scalarArc (j : ℕ) (Q : ℝ) (N q : ℕ) (k : Fin 3 → ℕ) : ℝ :=
  (2 * Q / N) * positivePart j (fun i => mainProfile N q (k i))
    (fun i => errorProfile Q N q (k i))

/-- Halupczok pages 8 to 11, a positive arithmetic envelope with no residue or phase parameters. -/
noncomputable def scalarEnvelope (j : ℕ) (Q : ℝ) (N : ℕ) (k : Fin 3 → ℕ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊Q⌋₊, scalarArc j Q N q k

/-- Halupczok page 8, every scalar arc bound is nonnegative. -/
theorem scalarArc_nonneg (j : ℕ) (Q : ℝ) (N q : ℕ) (k : Fin 3 → ℕ) (hQ : 0 ≤ Q) :
    0 ≤ scalarArc j Q N q k := by
  exact mul_nonneg (by positivity)
    (positivePart_nonneg _ _ _ (fun i => mainProfile_nonneg _ _ _)
      (fun i => errorProfile_nonneg _ _ _ _ hQ))

/-- Halupczok page 8, every scalar denominator sum is nonnegative. -/
theorem scalarEnvelope_nonneg (j : ℕ) (Q : ℝ) (N : ℕ) (k : Fin 3 → ℕ) (hQ : 0 ≤ Q) :
    0 ≤ scalarEnvelope j Q N k := sum_nonneg fun q hq => scalarArc_nonneg j Q N q k hQ

/-- Halupczok page 8, each rational numerator costs at most one qth of the scalar arc. -/
theorem arcEnvelope_le_scalar (j : ℕ) (Q : ℝ) (N q a : ℕ) (k l : Fin 3 → ℕ)
    (hQ : 1 ≤ Q) (hN : 1 ≤ N) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) :
    arcEnvelope j ((N : ℝ) / Q) k l N q a ≤ scalarArc j Q N q k / q := by
  have hQ0 : 0 < Q := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ hq0).mpr
  have hp := positivePart_mono j
    (fun i => (N : ℝ) * ‖mainCoeff (k i) (l i) q a‖)
    (fun i => (1 + 2 * π * |1 / ((q : ℝ) * ((N : ℝ) / Q))| * N) *
      prefixError (k i) (l i) q a N)
    (fun i => mainProfile N q (k i)) (fun i => errorProfile Q N q (k i))
    (fun i => by positivity)
    (fun i => mul_nonneg (by positivity) (prefixError_nonneg _ _ _ _ _))
    (fun i => mainProfile_nonneg _ _ _)
    (fun i => errorProfile_nonneg _ _ _ _ hQ0.le)
    (fun i => main_profile_bound (k i) (l i) N q a (hk i) hq)
    (fun i => error_profile_bound Q (k i) (l i) N q a hQ (hk i) hq hqQ (hl i) hN)
  have hs : (2 * |1 / ((q : ℝ) * ((N : ℝ) / Q))|) * q = 2 * Q / N := by
    rw [abs_of_pos (by positivity)]
    field_simp
  calc
    _ = (2 * Q / N) * positivePart j
        (fun i => (N : ℝ) * ‖mainCoeff (k i) (l i) q a‖)
        (fun i => (1 + 2 * π * |1 / ((q : ℝ) * ((N : ℝ) / Q))| * N) *
          prefixError (k i) (l i) q a N) := by
      unfold arcEnvelope
      rw [mul_right_comm, hs]
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

/-- Halupczok page 8, reduce the entire positive arc envelope to scalar arithmetic. -/
theorem errorEnvelope_le_scalar (j : ℕ) (Q : ℝ) (N : ℕ) (k l : Fin 3 → ℕ)
    (hQ : 1 ≤ Q) (hN : 1 ≤ N) (hk : ∀ i, 1 ≤ k i)
    (hl : ∀ i, Nat.Coprime (l i) (k i)) :
    errorEnvelope j Q ((N : ℝ) / Q) k l N ≤ scalarEnvelope j Q N k := by
  apply sum_le_sum
  intro q hq
  have hq1 := (mem_Icc.mp hq).1
  have hqQ : (q : ℝ) ≤ Q := (Nat.cast_le.mpr (mem_Icc.mp hq).2).trans (Nat.floor_le (by linarith))
  have hc : (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤ q := by
    exact_mod_cast (card_filter_le (range q) (fun a => Nat.Coprime a q)).trans_eq (card_range q)
  calc
    _ ≤ ∑ _a ∈ (range q).filter (fun a => Nat.Coprime a q), scalarArc j Q N q k / q :=
      sum_le_sum fun a ha => arcEnvelope_le_scalar j Q N q a k l hQ hN hq1 hqQ hk hl
    _ ≤ _ := by
      rw [sum_const, nsmul_eq_mul]
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
      calc
        _ ≤ (q : ℝ) * (scalarArc j Q N q k / q) :=
          mul_le_mul_of_nonneg_right hc (div_nonneg (scalarArc_nonneg j Q N q k (by linarith)) hq0.le)
        _ = _ := by field_simp

/-- Halupczok page 8, remove the residue maximum of a nonnegative residue independent bound. -/
theorem EF_independent_le (G : (Fin 3 → ℕ) → ℝ) (hG : ∀ k, 0 ≤ G k)
    (l₃ : ℕ) (B : ℝ) (N : ℕ) :
    EF (fun k _l => G k) (fun _ => 1) l₃ B N ≤
      ∑ k₁ ∈ Icc 1 (Dyadic.cutoff B N), ∑ k₂ ∈ Icc 1 (Dyadic.cutoff B N),
        ∑ k₃ ∈ Icc 1 (Dyadic.cutoff3 B N), G ![k₁, k₂, k₃] := by
  unfold EF
  apply sum_le_sum
  intro k₁ hk₁
  apply sum_le_sum
  intro k₂ hk₂
  have h0 : 0 ≤ ∑ k₃ ∈ Icc 1 (Dyadic.cutoff3 B N), G ![k₁, k₂, k₃] :=
    sum_nonneg fun _ _ => hG _
  unfold innerF
  refine Real.iSup_le (fun l₁ => Real.iSup_le (fun h₁ => Real.iSup_le
    (fun l₂ => Real.iSup_le (fun h₂ => ?_) h0) h0) h0) h0
  simp only [one_mul]
  rw [abs_of_nonneg (sum_nonneg fun _ _ => hG _)]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => hG _)

/-- Halupczok pages 8 to 11, the complete positive scalar rectangular average. -/
noncomputable def scalarMean (j : ℕ) (A : ℝ) (N : ℕ) : ℝ :=
  ∑ k₁ ∈ Icc 1 (Dyadic.cutoff (10 ^ 4 * A) N),
    ∑ k₂ ∈ Icc 1 (Dyadic.cutoff (10 ^ 4 * A) N),
      ∑ k₃ ∈ Icc 1 (Dyadic.cutoff3 (10 ^ 4 * A) N),
        scalarEnvelope j (Qof A N) N ![k₁, k₂, k₃]

/-- Halupczok pages 8 to 11, the rational prefix mean follows from a scalar rectangular mean. -/
theorem prefix_mean_le_scalar (j : ℕ) (A : ℝ) (N l₃ : ℕ)
    (hQ : 1 ≤ Qof A N) (hN : 1 ≤ N) :
    EF (fun k l => errorEnvelope j (Qof A N) (τof A N) k l N)
      (fun _ => 1) l₃ (10 ^ 4 * A) N ≤ scalarMean j A N := by
  have hQ0 : 0 ≤ Qof A N := by linarith
  refine le_trans ?_ (EF_independent_le (scalarEnvelope j (Qof A N) N)
    (fun k => scalarEnvelope_nonneg j (Qof A N) N k hQ0) l₃ (10 ^ 4 * A) N)
  simpa only [one_mul] using Decomp314b.EF_dominate
    (fun k l => errorEnvelope j (Qof A N) (τof A N) k l N)
    (fun k _l => scalarEnvelope j (Qof A N) N k)
    (fun _ => 1) l₃ (10 ^ 4 * A) 1 N (by intro k; norm_num) (by norm_num)
    (fun k l => scalarEnvelope_nonneg j (Qof A N) N k hQ0)
    (by
      intro k l hk hl
      rw [abs_of_nonneg (errorEnvelope_nonneg _ _ _ _ _ _)]
      simpa only [one_mul, τof] using errorEnvelope_le_scalar j (Qof A N) N k l hQ hN hk hl)

end LeanLab.Tolev2009.ScalarEnvelope346
