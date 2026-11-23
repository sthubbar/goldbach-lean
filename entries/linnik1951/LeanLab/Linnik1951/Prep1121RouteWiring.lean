module

public import LeanLab.Linnik1951.Decomp111
public import LeanLab.Linnik1951.SPLIT_lemma2_outer_square519
public import LeanLab.Linnik1951.SPLIT_principal_model520

/-!
Prep1121 route wiring for P0093, Linnik 1951. Burst prep 2026-11-21, step L51-wiring.

lemma2_outer_square519 of Decomp519a and principal_model520 of Decomp520a still carry
their placeholder proofs, although main proves both statements in SPLIT_lemma2_outer_square519 and
SPLIT_principal_model520. Those split files import Decomp519a and Decomp520a, so the
old files cannot call them, and the route to linnik1951_decomposed111 kept the two
placeholder proofs. This file is the assembly twin: it repeats, statement for statement and proof
for proof, the chain from those two steps up to linnik1951_decomposed111, with every
call of lemma2_outer_square519 replaced by lemma2_outer_square519_split and every call
of principal_model520 replaced by principal_model520_split. Each twin carries the
suffix _w1121 and the statement of its original, unchanged. No existing file is edited
and this file has no placeholder proof of its own and no new definition.

Twin chain, P0093 pages 156 to 169.
Lemma 2 side: lemma2_positive_square519, lemma2_square519, nonprincipal_mass519,
system_character_bound519, system_mass519, then system_mass_split111 of Lemma6Split111,
then covered_square_split111, exceptional_square_split111, lemma7_split111,
exceptional_error_split111 of Decomp111.
Principal model side: principal_convolution520, local_expansion520, major_expansion520,
then major_local_expansion_m111 of Major81Split111, then major_truncated_split111 and
major_error_split111 of Decomp111.
Top: error_bound111 and linnik1951_decomposed111 of Decomp111.

The final theorem linnik1951_decomposed_prep1121 has the exact statement of
linnik1951_decomposed111. It is CONDITIONAL ON GRH, its hypothesis, and on the open
leaves still left in its closure, which #print axioms reports as the placeholder axiom; the companion
file Prep1121WiringAudit lists them by name.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

/-- TWIN of lemma2_positive_square519 in Decomp519a, same statement, proof copied with the split calls.
P0093 page 158 equations 4.7 and 4.8. The full positive half interval
is assembled from the clean central part and the signed outer estimate.
CONDITIONAL ON lemma2_outer_square519_split. -/
theorem lemma2_positive_square519_w1121 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2) (Set.Icc 0 (1 / R)) ∧
          (∫ α in 0..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 13) := by
  obtain ⟨Cc, hCc, Nc, hc⟩ := central_square_mass519 B0 hB0
  obtain ⟨Co, hCo, No, ho⟩ := lemma2_outer_square519_split B0 hB0
  have hscale : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ (5 / 7 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 7)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  have hlogs : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨Ns, hs⟩ := eventually_atTop.mp hscale
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp hlogs
  refine ⟨Cc + Co, by positivity, max 3 (max Nc (max No (max Ns Nl))), ?_⟩
  intro N hN R hR hRN M hM
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hRp : 0 < R := by linarith
  have hlog : 1 ≤ Real.log N := hl N (by omega)
  have hlog0 : 0 ≤ Real.log N := by linarith
  have h4R : 4 * R ≤ N := by
    calc _ ≤ 4 * (N : ℝ) ^ (2 / 7 : ℝ) := mul_le_mul_of_nonneg_left hRN (by norm_num)
      _ ≤ (N : ℝ) ^ (5 / 7 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_right (hs N (by omega)) (by positivity)
      _ = N := by rw [← Real.rpow_add hNp]; norm_num
  have hδr : 4 / (N : ℝ) ≤ 1 / R :=
    (div_le_div_iff₀ hNp hRp).mpr (by simpa only [one_mul] using h4R)
  obtain ⟨hiC, hbC⟩ := hc N (by omega) M hM
  obtain ⟨hiO, hbO⟩ := ho N (by omega) R hR hRN M hM
  have hiCI := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by positivity : (0 : ℝ) ≤ 4 / (N : ℝ))).mpr hiC
  have hiOI := (intervalIntegrable_iff_integrableOn_Icc_of_le hδr).mpr hiO
  have hiP := hiCI.trans hiOI
  have hRleN : R ≤ N := by
    calc R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hRN
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have hNR : 1 ≤ (N : ℝ) / R := (le_div_iff₀ hRp).mpr (by simpa using hRleN)
  have hlogscale : Real.log N ^ 13 ≤ (N : ℝ) / R * Real.log N ^ 13 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hNR (pow_nonneg hlog0 13)
  have hcu : (∫ α in 0..(4 / (N : ℝ)), ‖mellinU519 N M α‖ ^ 2) ≤
      Cc * ((N : ℝ) / R * Real.log N ^ 13) :=
    hbC.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hlog (by omega : 6 ≤ 13)) hCc.le).trans
        (mul_le_mul_of_nonneg_left hlogscale hCc.le))
  have hou : (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
      Co * ((N : ℝ) / R * Real.log N ^ 13) := by
    apply hbO.trans
    gcongr
    norm_num
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le
    (by positivity : (0 : ℝ) ≤ 1 / R)).mp hiP, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hiCI hiOI]
  calc _ ≤ Cc * ((N : ℝ) / R * Real.log N ^ 13) +
      Co * ((N : ℝ) / R * Real.log N ^ 13) := add_le_add hcu hou
    _ = _ := by ring

/-- TWIN of lemma2_square519 in Decomp519a, same statement, proof copied with the split calls.
P0093 pages 156 through 158 Lemma 2 equations 4.1 through 4.8.
The diagonal square estimate is assembled from the clean central interval,
the signed outer estimate and the proved conjugate reflection.
CONDITIONAL ON lemma2_outer_square519_split. No GRH or prime occurs here. -/
theorem lemma2_square519_w1121 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
          ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) →
          IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2) (Set.Icc (-(1 / R)) (1 / R)) ∧
          (∫ α in -(1 / R)..(1 / R), ‖mellinU519 N M α‖ ^ 2) ≤
            C * ((N : ℝ) / R * Real.log N ^ 13) := by
  obtain ⟨C, hC, Np, hp⟩ := lemma2_positive_square519_w1121 B0 hB0
  refine ⟨2 * C, by positivity, max 1 Np, ?_⟩
  intro N hN R hR hRN M hM
  have hN1 : 1 ≤ N := by omega
  have hr0 : (0 : ℝ) ≤ 1 / R := by positivity
  obtain ⟨hiP, hbP⟩ := hp N (by omega) R hR hRN M hM
  have hMref := reflected_line_bound519 N B0 M hM.1 hM.2
  obtain ⟨hiQ, hbQ⟩ := hp N (by omega) R hR hRN
    (fun t => (starRingEnd ℂ) (M (-t))) hMref
  have hiN : IntegrableOn (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      (Set.Icc (-(1 / R)) 0) := by
    simpa only [Set.neg_Icc, neg_zero, mellin_reflection519 N hN1 M,
      Complex.norm_conj, neg_neg] using hiQ.comp_neg
  have hiPI := (intervalIntegrable_iff_integrableOn_Icc_of_le hr0).mpr hiP
  have hiNI := (intervalIntegrable_iff_integrableOn_Icc_of_le
    (neg_nonpos.mpr hr0)).mpr hiN
  have hiFull := hiNI.trans hiPI
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le
    (show -(1 / R) ≤ 1 / R by linarith)).mp hiFull, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hiNI hiPI,
    mellin_negative_square519 N hN1 M (1 / R)]
  calc _ ≤ C * ((N : ℝ) / R * Real.log N ^ 13) +
      C * ((N : ℝ) / R * Real.log N ^ 13) := add_le_add hbQ hbP
    _ = _ := by ring

end LeanLab.Linnik1951.Task519

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- TWIN of principal_convolution520 in Decomp520a, same statement, proof copied with the split calls.
P0093 pages 160 and 161 equations 6.1 through 6.3.
CONDITIONAL on principal_model520_split. Extend the principal square to a full period and read its exact convolution.
No fixed one over N shoulder is removed. -/
theorem principal_convolution520_w1121 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖principalIntegral520 N q n -
        ((Real.exp (-(n : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ)‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C, hC, N0, hmodel⟩ := principal_model520_split hG
  refine ⟨C, hC, max N0 1, ?_⟩
  intro N hN q hq hqQ n hn
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by have := le_max_right N0 1; omega
  have h := hmodel N hN0 q hq hqQ n hn
  rwa [logFourier_square_integral520 N hN1 n] at h

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997
open Finset Filter MeasureTheory

end LeanLab.Linnik1951
