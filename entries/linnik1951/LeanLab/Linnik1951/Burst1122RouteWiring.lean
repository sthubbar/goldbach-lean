module

public import LeanLab.Linnik1951.Prep1121RouteWiring
public import LeanLab.Linnik1951.Prep1121ResidueMean
public import LeanLab.Linnik1951.Prep1121MixedRepair520
public import LeanLab.Linnik1951.Prep1121DL51Fourier
public import LeanLab.Linnik1951.Prep1121DL51Damped
public import LeanLab.Linnik1951.Decomp552e

/-!
Burst 1122 route wiring for P0093, Linnik 1951. Burst 2026-11-22, session S3,
units P1122-0023 and P1122-0025, step route_wiring1122.

Main proves residue_square_mean1121 in Prep1121ResidueMean, the statement of
residue_square_mean520, and mixed_bound520_repaired_prep1121 in Prep1121MixedRepair520,
the ln^7 repair of mixed_bound520, whose two open leaves are proved exactly by
principal_fourier_coeff_sq_prep1121D and damped_from_count_prep1121D. The route to
linnik1951_decomposed111 still called the unproved versions in Decomp520a, and
residue_square_mean1121 still went through nonprincipal_mass519, which reaches the
unproved lemma2_outer_square519 and the leaf grh_mellin_transfer519.

This file is the assembly twin with suffix _b1122. Every statement is the statement of
its original word for word, plus one hypothesis hT placed right after hG. The
hypothesis hT is written inline, with no definition: it is the exact Prop that
Task519.grh_mellin_transfer519 asserts after hG, P0093 page 159 before equation 5.1.
Every proof is the proof of its original, with the twin calls below.
Lemma 2 side: nonprincipal_mass519_b1122 uses hT and lemma2_square519_w1121 of
Prep1121RouteWiring, so lemma2_outer_square519 is reached only through its proved
split; then system_character_bound519_b1122 and system_mass519_b1122.
Local side: residue_square_mean520_b1122, the proof of residue_square_mean1121;
principal_parseval_b1122 and prime_damped_chebyshev_b1122 with the two D leaves;
mixed_bound520_repaired_b1122 with ln^7; local_expansion520_b1122 with ln^13, which
uses principal_convolution520_w1121 and so principal_model520_split;
major_expansion520_b1122.
Top: the chain of Prep1121RouteWiring from system_mass_split111 to error_bound111,
then linnik1951_decomposed_of_transfer_b1122, and the twin
local_arc_small_residual_supply552_b1122 of Decomp552e.
Instantiation with Task519.grh_mellin_transfer519 hG gives linnik1951_decomposed_b1122
and local_arc_small_residual_supply552_inst_b1122 with the exact statements of
linnik1951_decomposed111 and local_arc_small_residual_supply552.

No existing file is edited, no new definition, no placeholder proof here. The theorems with hT are
CONDITIONAL ON GRH and hT; the instantiations are CONDITIONAL ON GRH and on the leaf
grh_mellin_transfer519, which Burst1122WiringAudit checks is the only unproved carrier
left in the closure.

AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

/-- TWIN of nonprincipal_mass519 in Decomp519a, same statement plus hT, proof copied with the twin calls.
P0093 page 159 equation 5.2. The corrected Mellin transfer and the
abstract square estimate imply the nonprincipal character square estimate.
CONDITIONAL ON the transfer hypothesis hT, the statement of grh_mellin_transfer519,
and on lemma2_square519_w1121. -/
theorem nonprincipal_mass519_b1122 (hG : LeanLab.DERZ1997.GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
            (∫ α in -(1 / R)..(1 / R), ‖characterPrime519 χ N α‖ ^ 2) ≤
              C * ((N : ℝ) / R * Real.log N ^ 13) := by
  obtain ⟨B0, hB0, B, hB, Nt, ht⟩ := hT
  obtain ⟨C, hC, Nm, hm⟩ := lemma2_square519_w1121 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨2 * C + 4 * B ^ 2, by positivity, max 1 (max L (max Nt Nm)), ?_⟩
  intro N hN q hq hqN χ hχ R hR hRN
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R := by linarith
  have hNt : Nt < N := by omega
  have hNm : Nm < N := by omega
  have hLN : (L : ℝ) < N := by exact_mod_cast (show L < N by omega)
  have hlog : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hLN).le
  have hlog13 : 1 ≤ Real.log N ^ 13 := one_le_pow₀ hlog
  obtain ⟨M, hM, hrem⟩ := ht N hNt q hq hqN χ hχ
  obtain ⟨hiM, hmass⟩ := hm N hNm R hR hRN M hM
  have hc := (continuous_character_prime519 χ N hN1).norm.pow 2
  have hle : ∀ α : ℝ, ‖characterPrime519 χ N α‖ ^ 2 ≤
      2 * ‖mellinU519 N M α‖ ^ 2 + 2 * B ^ 2 * N := by
    intro α
    have htri : ‖characterPrime519 χ N α‖ ≤
        ‖mellinU519 N M α‖ + B * Real.sqrt N := by
      have := norm_add_le (mellinU519 N M α)
        (characterPrime519 χ N α - mellinU519 N M α)
      have he : mellinU519 N M α +
          (characterPrime519 χ N α - mellinU519 N M α) = characterPrime519 χ N α := by ring
      rw [he] at this
      exact this.trans (add_le_add le_rfl (hrem α))
    nlinarith [sq_nonneg (‖mellinU519 N M α‖ - B * Real.sqrt N),
      Real.sq_sqrt hNp.le, norm_nonneg (characterPrime519 χ N α),
      norm_nonneg (mellinU519 N M α), Real.sqrt_nonneg (N : ℝ)]
  have hiMi : IntervalIntegrable (fun α : ℝ => ‖mellinU519 N M α‖ ^ 2)
      volume (-(1 / R)) (1 / R) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [one_div_nonneg.mpr hRp.le] : -(1 / R) ≤ (1 / R))).mpr
    exact hiM
  have hh := intervalIntegral.integral_mono_on (by linarith [one_div_nonneg.mpr hRp.le] : -(1 / R) ≤ (1 / R))
    (hc.intervalIntegrable _ _)
    ((hiMi.const_mul 2).add (intervalIntegrable_const (a := -(1 / R)) (b := 1 / R)))
    (fun α _ => hle α)
  rw [intervalIntegral.integral_add (hiMi.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hh
  calc
    _ ≤ 2 * (∫ α in -(1 / R)..(1 / R), ‖mellinU519 N M α‖ ^ 2) +
        (1 / R - -(1 / R)) * (2 * B ^ 2 * N) := hh
    _ ≤ 2 * (C * ((N : ℝ) / R * Real.log N ^ 13)) +
        (1 / R - -(1 / R)) * (2 * B ^ 2 * N) := by gcongr
    _ ≤ (2 * C + 4 * B ^ 2) * ((N : ℝ) / R * Real.log N ^ 13) := by
      have he : (1 / R - -(1 / R)) * (2 * B ^ 2 * N) =
          4 * B ^ 2 * ((N : ℝ) / R) := by ring
      rw [he]
      have := mul_le_mul_of_nonneg_left hlog13
        (show 0 ≤ 4 * B ^ 2 * ((N : ℝ) / R) by positivity)
      nlinarith

/-- TWIN of system_character_bound519 in Decomp519a, same statement plus hT, proof copied with the twin calls.
P0093 page 166 equation 9.1. The finite character expansion and the
nonprincipal square estimate give the system bound before power absorption.
CONDITIONAL ON the transfer hypothesis hT, the statement of grh_mellin_transfer519,
and on lemma2_square519_w1121. -/
theorem system_character_bound519_b1122 (hG : LeanLab.DERZ1997.GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, (N : ℝ) ^ (1 / 10 : ℝ) < q →
        (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        (∫ α in arcSystem519 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
          ‖primeFourier111_up111 N α‖ ^ 2) ≤
            C * ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13) := by
  classical
  obtain ⟨B, hB, hb⟩ := doubled_system_characters1622_split
  obtain ⟨X, hX, Nx, hx⟩ := nonprincipal_mass519_b1122 hG hT
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  have hτev : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 7)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  obtain ⟨Nt, ht⟩ := eventually_atTop.mp hτev
  refine ⟨B * (10 + 2 * X), by positivity, max 1 (max L (max Nx Nt)), ?_⟩
  intro N hN q hq hqt
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hq1R : (1 : ℝ) < q :=
    (Real.one_le_rpow hNR (by norm_num : (0 : ℝ) ≤ 1 / 10)).trans_lt hq
  have hq2 : 2 ≤ q := by exact_mod_cast hq1R
  have hqp : (0 : ℝ) < q := by linarith
  haveI : NeZero q := ⟨by omega⟩
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hτ : 4 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := ht N (by omega)
  have hτp : 0 < (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hqN : (q : ℝ) ≤ N := hqt.trans (by
    calc (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
      _ = N := Real.rpow_one _)
  have hLN : (L : ℝ) < N := by exact_mod_cast (show L < N by omega)
  have hlog : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hLN).le
  have hlog13 : 1 ≤ Real.log N ^ 13 := one_le_pow₀ hlog
  let τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ)
  let R : ℝ := (q : ℝ) * τ / 2
  let r : ℝ := 2 / ((q : ℝ) * τ)
  have hR1 : 1 ≤ R := by dsimp [R, τ]; nlinarith
  have hRN : R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by
    have hqq : (q : ℝ) * τ ≤ τ * τ := mul_le_mul_of_nonneg_right hqt hτp.le
    have he : τ * τ = (N : ℝ) ^ (2 / 7 : ℝ) := by
      dsimp [τ]; rw [← Real.rpow_add hNp]; norm_num
    dsimp [R]; rw [← he]; nlinarith [mul_nonneg hτp.le hτp.le]
  have hr0 : 0 ≤ r := by dsimp [r, τ]; positivity
  have hrh : r ≤ 1 / 2 := by
    dsimp [r, τ]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hrR : 1 / R = r := by dsimp [R, r]; ring
  let F : Finset (DirichletCharacter ℂ q) := Finset.univ.filter (fun χ => χ ≠ 1)
  have hsum : (∑ χ ∈ F, ∫ z in -r..r, ‖characterPrime519 χ N z‖ ^ 2) ≤
      (q.totient : ℝ) * (X * ((N : ℝ) / R * Real.log N ^ 13)) := by
    have hi : ∀ χ ∈ F, (∫ z in -r..r, ‖characterPrime519 χ N z‖ ^ 2) ≤
        X * ((N : ℝ) / R * Real.log N ^ 13) := by
      intro χ hχ
      have hh := hx N (by omega) q (by omega) hqt χ (Finset.mem_filter.mp hχ).2 R hR1 hRN
      simpa only [hrR] using hh
    have hc : (F.card : ℝ) ≤ q.totient := by
      have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
      have hfilter : F.card ≤ q.totient := by
        simpa only [F, Finset.card_univ, hcard] using
          Finset.card_filter_le (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
            (p := fun χ => χ ≠ 1)
      exact_mod_cast hfilter
    calc _ ≤ (F.card : ℝ) * (X * ((N : ℝ) / R * Real.log N ^ 13)) := by
          simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul F _ _ hi
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  have hprin := character_local_mass519 (1 : DirichletCharacter ℂ q) N hN1 r hr0 hrh
  have he : (N : ℝ) / τ ≤ (N : ℝ) ^ (9 / 10 : ℝ) := by
    calc _ = (N : ℝ) ^ (6 / 7 : ℝ) := by
          dsimp [τ]; conv_lhs => lhs; rw [← Real.rpow_one (N : ℝ)]
          rw [← Real.rpow_sub hNp]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
  have hp := principal_arithmetic519 N q hN1 hlog hq.le hqN
  have hp13 : (N : ℝ) / q.totient ≤
      4 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13 := by
    have hl : Real.log N ≤ Real.log N ^ 13 := by
      calc _ = Real.log N ^ 1 := by ring
        _ ≤ _ := pow_le_pow_right₀ hlog (by omega)
    exact hp.trans (mul_le_mul_of_nonneg_left hl (by positivity))
  have hcorr : (q.totient : ℝ) * r * Real.log q ^ 2 ≤
      2 * ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13) := by
    have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hlq : Real.log q ^ 2 ≤ Real.log N ^ 13 := by
      have h0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
      have hl := Real.log_le_log hqp hqN
      exact (pow_le_pow_left₀ h0 hl 2).trans (pow_le_pow_right₀ hlog (by omega))
    have hrr : (q : ℝ) * r = 2 / τ := by dsimp [r]; field_simp
    calc _ ≤ (q : ℝ) * r * Real.log N ^ 13 := by gcongr
      _ = 2 / τ * Real.log N ^ 13 := by rw [hrr]
      _ ≤ 2 * ((N : ℝ) / τ) * Real.log N ^ 13 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [mul_div_assoc', div_le_div_iff₀ hτp hτp]
        nlinarith
      _ ≤ (2 * (N : ℝ) ^ (9 / 10 : ℝ)) * Real.log N ^ 13 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (by norm_num)) (by positivity)
      _ = _ := by ring
  have hmass := hb N q τ hN1 hq2 hτ
  have hm : (∫ α in arcSystem519 q τ ∩ Set.Icc 0 1,
      ‖primeFourier111_up111 N α‖ ^ 2) ≤
      B / (q.totient : ℝ) * (2 * N + (q : ℝ) *
        ((q.totient : ℝ) * (X * ((N : ℝ) / R * Real.log N ^ 13)))) +
        B * (q.totient : ℝ) * r * Real.log q ^ 2 := by
    exact hmass.trans (add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add hprin
        (mul_le_mul_of_nonneg_left hsum hqp.le)) (by positivity)) le_rfl)
  have hid : B / (q.totient : ℝ) * (2 * N + (q : ℝ) *
      ((q.totient : ℝ) * (X * ((N : ℝ) / R * Real.log N ^ 13)))) =
      2 * B * ((N : ℝ) / q.totient) +
        2 * B * X * ((N : ℝ) / τ * Real.log N ^ 13) := by
    dsimp [R]; field_simp [hφ.ne', hqp.ne', hτp.ne'] <;> ring
  rw [hid] at hm
  calc
    _ ≤ 2 * B * ((N : ℝ) / q.totient) +
        2 * B * X * ((N : ℝ) / τ * Real.log N ^ 13) +
        B * ((q.totient : ℝ) * r * Real.log q ^ 2) := by simpa only [mul_assoc] using hm
    _ ≤ 2 * B * (4 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13) +
        2 * B * X * ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13) +
        B * (2 * ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13)) := by gcongr
    _ = _ := by ring

/-- TWIN of system_mass519 in Decomp519a, same statement plus hT, proof copied with the twin calls.
P0093 page 166 equations 9.1 and 9.3. Logarithmic absorption of
the character system estimate on the minor denominator range.
CONDITIONAL ON the transfer hypothesis hT, the statement of grh_mellin_transfer519,
and on lemma2_square519_w1121. -/
theorem system_mass519_b1122 (hG : LeanLab.DERZ1997.GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, (N : ℝ) ^ (1 / 10 : ℝ) < (q : ℝ) → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        (∫ α in arcSystem519 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
          ‖primeFourier111_up111 N α‖ ^ 2) ≤ C * (N : ℝ) ^ (93 / 100 : ℝ) := by
  obtain ⟨C, hC, Ns, hs⟩ := system_character_bound519_b1122 hG hT
  have hlo := (isLittleO_log_rpow_rpow_atTop (13 : ℝ)
    (by norm_num : (0 : ℝ) < 3 / 100)).def (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hlo)
  refine ⟨C, hC, max 1 (max Ns Nl), ?_⟩
  intro N hN q hq hqt
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlN : Real.log N ^ 13 ≤ (N : ℝ) ^ (3 / 100 : ℝ) := by
    have hh := hl N (by omega)
    simpa [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg hlog,
      abs_of_nonneg (pow_nonneg hlog 13), abs_of_pos (Real.rpow_pos_of_pos hNp _)] using hh
  calc
    _ ≤ C * ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 13) := hs N (by omega) q hq hqt
    _ ≤ C * ((N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (3 / 100 : ℝ)) := by gcongr
    _ = _ := by rw [← Real.rpow_add hNp]; norm_num

end LeanLab.Linnik1951.Task519

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- TWIN of residue_square_mean1121 in Prep1121ResidueMean, proof copied with
nonprincipal_mass519 replaced by nonprincipal_mass519_b1122.
P0093 pages 159 and 160 equations 5.2 and 5.4, the exact statement of
residue_square_mean520 plus the hypothesis hT. CONDITIONAL ON GRH and hT. -/
theorem residue_square_mean520_b1122 (hG : LeanLab.DERZ1997.GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))), ‖residueError520 N q a z‖ ^ 2) ≤
        C * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 := by
  classical
  obtain ⟨C, hC, N0, hm⟩ := Task519.nonprincipal_mass519_b1122 hG hT
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨2 * C + 4, by positivity, max 1 (max L N0), ?_⟩
  intro N hN q hq hqN
  have : NeZero q := ⟨by omega⟩
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hLN : (L : ℝ) < N := by exact_mod_cast (show L < N by omega)
  have hlog : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hLN).le
  have hlog13 : 1 ≤ Real.log N ^ 13 := one_le_pow₀ hlog
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτdef
  have hτp : 0 < τ := by positivity
  have hτ1 : 1 ≤ τ := Real.one_le_rpow hN1R (by norm_num)
  have h10 : (N : ℝ) ^ (1 / 10 : ℝ) ≤ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
  have hq7 : (q : ℝ) ≤ τ := hqN.trans h10
  set R : ℝ := (q : ℝ) * τ with hRdef
  have hRp : 0 < R := by positivity
  have hR1 : 1 ≤ R := by nlinarith
  have hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by
    have : (N : ℝ) ^ (2 / 7 : ℝ) = τ * τ := by
      rw [hτdef, ← Real.rpow_add hNp]; norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_right hq7 hτp.le
  have hr0 : 0 ≤ 1 / R := by positivity
  have hab : -(1 / R) ≤ 1 / R := by linarith
  -- integrability of every integrand
  have hEi : ∀ a, IntervalIntegrable (fun z => ‖residueError520 N q a z‖ ^ 2)
      volume (-(1 / R)) (1 / R) := fun a =>
    ((continuous_residue520 N q a hN1).norm.pow 2).intervalIntegrable _ _
  have hAi : ∀ χ : DirichletCharacter ℂ q,
      IntervalIntegrable (fun z => ‖Task519.characterPrime519 χ N z‖ ^ 2)
        volume (-(1 / R)) (1 / R) := fun χ =>
    ((Task519.continuous_character_prime519 χ N hN1).norm.pow 2).intervalIntegrable _ _
  have hcardχ := nonprincipal_card1121 q
  have hφp : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hAc : Continuous (fun z => ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ‖Task519.characterPrime519 χ N z‖ ^ 2) :=
    continuous_finsetSum _ fun χ _ =>
      (Task519.continuous_character_prime519 χ N hN1).norm.pow 2
  -- integrate the pointwise energy
  have hint :
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / R)..(1 / R), ‖residueError520 N q a z‖ ^ 2) ≤
      2 * ((q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ∫ z in -(1 / R)..(1 / R), ‖Task519.characterPrime519 χ N z‖ ^ 2) +
        2 * (q : ℝ) ^ 3 * (2 / R) := by
    rw [← intervalIntegral.integral_finsetSum (fun a _ => hEi a)]
    have hrhs : (∫ z in -(1 / R)..(1 / R), (2 * ((q : ℝ) / q.totient *
          ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖Task519.characterPrime519 χ N z‖ ^ 2) + 2 * (q : ℝ) ^ 3)) =
        2 * ((q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ∫ z in -(1 / R)..(1 / R), ‖Task519.characterPrime519 χ N z‖ ^ 2) +
        2 * (q : ℝ) ^ 3 * (2 / R) := by
      have h1 : IntervalIntegrable (fun z => 2 * ((q : ℝ) / q.totient *
          ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ‖Task519.characterPrime519 χ N z‖ ^ 2)) volume (-(1 / R)) (1 / R) :=
        ((continuous_const.mul (continuous_const.mul hAc))).intervalIntegrable _ _
      rw [intervalIntegral.integral_add h1 intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun χ _ => hAi χ),
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← hrhs]
    apply intervalIntegral.integral_mono_on hab
    · exact (continuous_finsetSum _ fun a _ =>
        (continuous_residue520 N q a hN1).norm.pow 2).intervalIntegrable _ _
    · exact ((continuous_const.mul (continuous_const.mul hAc)).add
        continuous_const).intervalIntegrable _ _
    · intro z _
      exact pointwise_energy1121 N q hN1 z
  -- the character square means
  have hmass : ∀ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      (∫ z in -(1 / R)..(1 / R), ‖Task519.characterPrime519 χ N z‖ ^ 2) ≤
        C * ((N : ℝ) / R * Real.log N ^ 13) := by
    intro χ hχ
    exact hm N (by omega) q hq hq7 χ (mem_filter.mp hχ).2 R hR1 hR2
  have hsumχ : (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ∫ z in -(1 / R)..(1 / R), ‖Task519.characterPrime519 χ N z‖ ^ 2) ≤
      (q.totient : ℝ) * (C * ((N : ℝ) / R * Real.log N ^ 13)) := by
    calc _ ≤ ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          C * ((N : ℝ) / R * Real.log N ^ 13) := sum_le_sum hmass
      _ = _ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcardχ (by positivity)
  have hq2 : (q : ℝ) ^ 2 ≤ N := by
    have h1 : (q : ℝ) ^ 2 ≤ ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 2 := pow_le_pow_left₀ hqp.le hqN 2
    have h2 : ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 2 ≤ N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      calc (N : ℝ) ^ ((1 / 10 : ℝ) * ((2 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
        _ = N := Real.rpow_one _
    linarith
  have hfin1 : 2 * ((q : ℝ) / q.totient *
      ((q.totient : ℝ) * (C * ((N : ℝ) / R * Real.log N ^ 13)))) =
      2 * C * (N : ℝ) / τ * Real.log N ^ 13 := by
    rw [hRdef]; field_simp
  have hfin2 : 2 * (q : ℝ) ^ 3 * (2 / R) ≤ 4 * (N : ℝ) / τ * Real.log N ^ 13 := by
    have he : 2 * (q : ℝ) ^ 3 * (2 / R) = 4 * (q : ℝ) ^ 2 / τ := by
      rw [hRdef]; field_simp; ring
    rw [he]
    have h4 : 4 * (q : ℝ) ^ 2 / τ ≤ 4 * (N : ℝ) / τ :=
      div_le_div_of_nonneg_right (by linarith) hτp.le
    have h5 : 4 * (N : ℝ) / τ ≤ 4 * (N : ℝ) / τ * Real.log N ^ 13 :=
      le_mul_of_one_le_right (by positivity) hlog13
    linarith
  have hfin0 : 2 * ((q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ∫ z in -(1 / R)..(1 / R), ‖Task519.characterPrime519 χ N z‖ ^ 2) ≤
      2 * ((q : ℝ) / q.totient *
        ((q.totient : ℝ) * (C * ((N : ℝ) / R * Real.log N ^ 13)))) := by
    gcongr
  calc _ ≤ _ := hint
    _ ≤ 2 * C * (N : ℝ) / τ * Real.log N ^ 13 + 4 * (N : ℝ) / τ * Real.log N ^ 13 := by
      rw [← hfin1]; exact add_le_add hfin0 hfin2
    _ = _ := by ring

/-- TWIN of principal_parseval_prep1121 in Prep1121MixedRepair520, proof copied
with the proved leaf principal_fourier_coeff_sq_prep1121D.
P0093 page 159 before display 5.3, the Parseval step of the trivial
estimate. Over one full period the squared norm of the principal series
integrates to at most the damped sum over all primes with doubled decay. -/
theorem principal_parseval_b1122 (N q : ℕ) (hN : 1 ≤ N) :
    ∫ z in (0 : ℝ)..1, ‖principalPrime520 N q z‖ ^ 2 ≤
      ∑' p : Nat.Primes, Real.exp (-(2 * ((p : ℕ) : ℝ)) / N) := by
  rw [principal_parseval_identity_prep1121 N q hN]
  exact principal_fourier_coeff_sq_prep1121D N q hN

/-- TWIN of prime_damped_chebyshev_prep1121 in Prep1121MixedRepair520, proof
copied with the proved leaf damped_from_count_prep1121D.
P0093 page 159 before display 5.3, the size N over ln N of the trivial
estimate: the damped prime sum is at most a constant times N over ln N. -/
theorem prime_damped_chebyshev_b1122 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∑' p : Nat.Primes, Real.exp (-(2 * ((p : ℕ) : ℝ)) / N) ≤
        C * (N : ℝ) / Real.log N := by
  obtain ⟨C, hC, hcount⟩ := prime_count_chebyshev_prep1121
  exact damped_from_count_prep1121D C hC hcount

/-- TWIN of mixed_bound520_repaired_prep1121 in Prep1121MixedRepair520, proof copied
with residue_square_mean520_b1122, principal_parseval_b1122 and
prime_damped_chebyshev_b1122. REPAIRED mixed_bound520, P0093 page 160 display 5.5
with ln^7 N in place of ln^6 N. CONDITIONAL ON GRH and hT. -/
theorem mixed_bound520_repaired_b1122 (hG : LeanLab.DERZ1997.GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖mixedIntegral520 N q n‖ ≤ C * (N : ℝ) * Real.log N ^ 7 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨C2, hC2, N2, hR⟩ := residue_square_mean520_b1122 hG hT
  obtain ⟨C1, hC1, N1, hCheb⟩ := prime_damped_chebyshev_b1122
  obtain ⟨N3, hTot⟩ := q_div_totient_le_log_prep1121
  refine ⟨2 * Real.sqrt (C1 * C2), by positivity, max 200 (max N1 (max N2 N3)), ?_⟩
  intro N hN q hq hqQ n hn
  have h200 : 200 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNs : max N1 (max N2 N3) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hNs
  have hN2 : N2 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hNs
  have hN3 : N3 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hNs
  have hNone : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτdef
  have hτ : 0 < τ := Real.rpow_pos_of_pos hNpos _
  -- tau is at least two, so the arc radius is at most one half
  have hτ2 : (2 : ℝ) ≤ τ := by
    have h128 : ((2 : ℝ) ^ (7 : ℝ)) ≤ (N : ℝ) := by
      have : (128 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 128 ≤ N by omega)
      have e : ((2 : ℝ) ^ (7 : ℝ)) = 128 := by norm_num
      linarith
    have hmono := Real.rpow_le_rpow (by positivity) h128 (show (0 : ℝ) ≤ 1 / 7 by norm_num)
    have e2 : ((2 : ℝ) ^ (7 : ℝ)) ^ (1 / 7 : ℝ) = 2 := by
      rw [← Real.rpow_mul (by norm_num)]
      norm_num
    rw [e2] at hmono
    exact hmono
  set r : ℝ := 1 / ((q : ℝ) * τ) with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hrhalf : r ≤ 1 / 2 := by
    rw [hrdef]
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have : (2 : ℝ) ≤ q * τ := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num) this
  have hL : 1 ≤ Real.log N := by
    have h3 : Real.exp 1 ≤ (N : ℝ) := by
      have he := Real.exp_one_lt_d9
      have : (200 : ℝ) < (N : ℝ) := by exact_mod_cast h200
      linarith
    have := Real.log_le_log (Real.exp_pos 1) h3
    simpa using this
  -- the pieces
  set s := (range q).filter (fun a => Nat.Coprime a q) with hs
  have hcard : (s.card : ℝ) = (q.totient : ℝ) := by
    rw [hs, Nat.totient_eq_card_coprime]
    congr 2
    apply Finset.filter_congr
    intro a _
    exact Nat.coprime_comm
  set M : ℝ := ∫ z in -r..r, ‖principalPrime520 N q z‖ ^ 2 with hMdef
  set R : ℝ := ∑ a ∈ s, ∫ z in -r..r, ‖residueError520 N q a z‖ ^ 2 with hRdef
  set S : ℝ := ∑ a ∈ s, ∫ z in -r..r, ‖principalPrime520 N q z‖ * ‖residueError520 N q a z‖
    with hSdef
  have hm := mixed_norm_le_prep1121 N q hNone n
  have hc := coefficient_le_inv_totient_prep1121 q hq
  have hS : S ≤ Real.sqrt ((q.totient : ℝ) * M) * Real.sqrt R := by
    have h := arc_cauchy_schwarz_prep1121 s r hr0 (fun z => ‖principalPrime520 N q z‖)
      (fun a z => ‖residueError520 N q a z‖)
      (continuous_principal520 N q hNone).norm
      (fun a => (continuous_residue520 N q a hNone).norm)
    rw [hcard] at h
    exact h
  have hM : M ≤ C1 * (N : ℝ) / Real.log N :=
    ((principal_arc_le_period_prep1121 N q hNone r hr0 hrhalf).trans
      (principal_parseval_b1122 N q hNone)).trans (hCheb N hN1)
  have hR' : R ≤ C2 * (N : ℝ) / τ * Real.log N ^ 13 := hR N hN2 q hq hqQ
  have hqφ := hTot N hN3 q hq hqQ
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact intervalIntegral.integral_nonneg (by linarith) (fun z _ => by positivity)
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    exact Finset.sum_nonneg (fun a _ =>
      intervalIntegral.integral_nonneg (by linarith) (fun z _ => by positivity))
  exact mixed_chain_prep1121 _ _ S M R _ _ τ _ _ C1 C2 hφ hqpos hτ hNpos.le hL hC1 hC2
    (norm_nonneg _) hM0 hR0 hm hc hS hM hR' hqφ

/-- TWIN of local_expansion520 in Decomp520a, same statement plus hT, proof copied with the twin calls.
P0093 pages 160 and 161 equations 5.4, 5.5 and 6.3.
CONDITIONAL ON GRH and hT; it uses mixed_bound520_repaired_b1122 with ln^7,
residue_square_mean520_b1122 and principal_model520_split through
principal_convolution520_w1121. The elementary
assembly retains the exact Ramanujan coefficient and damped convolution. -/
theorem local_expansion520_b1122 (hG : LeanLab.DERZ1997.GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖localArc520 N q n - localMain520 N q n‖ ≤
        B * (N : ℝ) * Real.log N ^ 13 *
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C1, hC1, N1, h1⟩ := mixed_bound520_repaired_b1122 hG hT
  obtain ⟨C2, hC2, N2, h2⟩ := residue_square_mean520_b1122 hG hT
  obtain ⟨C3, hC3, N3, h3⟩ := principal_convolution520_w1121 hG
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨C1 + C2 + C3, by positivity, max 2 (max L (max N1 (max N2 N3))), ?_⟩
  intro N hN q hq hqQ n hn
  have hN2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNL : L < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNs : max N1 (max N2 N3) < N :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hNs
  have hN2' : N2 < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hNs
  have hN3 : N3 < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hNs
  have hlog : 1 ≤ Real.log N := by
    have hreal : (L : ℝ) < (N : ℝ) := by exact_mod_cast hNL
    have hh := Real.log_le_log (Real.exp_pos 1) (hL.trans hreal).le
    simpa using hh
  have hlog7 : Real.log N ^ 7 ≤ Real.log N ^ 13 :=
    pow_le_pow_right₀ hlog (by omega)
  let τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ)
  let X : ℝ := (N : ℝ) * Real.log N ^ 13
  let E : ℝ := X * (1 / τ + 1 / Real.sqrt ((q : ℝ) * τ))
  have hτ : 0 < τ := Real.rpow_pos_of_pos (by positivity) _
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hfirst : X / τ ≤ E := by
    dsimp [E]
    simpa only [div_eq_mul_inv, one_div, mul_add, one_mul] using
      (le_add_of_nonneg_right (show 0 ≤ X / Real.sqrt ((q : ℝ) * τ) by positivity) :
        X / τ ≤ X / τ + X / Real.sqrt ((q : ℝ) * τ))
  have hsecond : X / Real.sqrt ((q : ℝ) * τ) ≤ E := by
    dsimp [E]
    simpa only [div_eq_mul_inv, one_div, mul_add, one_mul] using
      (le_add_of_nonneg_left (show 0 ≤ X / τ by positivity) :
        X / Real.sqrt ((q : ℝ) * τ) ≤ X / τ + X / Real.sqrt ((q : ℝ) * τ))
  have hb : ‖mixedIntegral520 N q n‖ ≤ C1 * E := by
    calc
      _ ≤ C1 * N * Real.log N ^ 7 / Real.sqrt ((q : ℝ) * τ) := h1 N hN1 q hq hqQ n hn
      _ ≤ C1 * N * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * τ) := by gcongr
      _ = C1 * (X / Real.sqrt ((q : ℝ) * τ)) := by dsimp [X]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsecond hC1.le
  have hc : ‖errorIntegral520 N q n‖ ≤ C2 * E := by
    calc
      _ ≤ C2 * N / τ * Real.log N ^ 13 :=
        (error_integral_le520 N q n).trans (h2 N hN2' q hq hqQ)
      _ = C2 * (X / τ) := by dsimp [X]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfirst hC2.le
  have hd : ‖principalCoefficient520 q ^ 2 * signedRamanujan520 q n *
      principalIntegral520 N q n - localMain520 N q n‖ ≤ C3 * E := by
    unfold localMain520
    rw [← mul_sub, norm_mul]
    have hp := h3 N hN3 q hq hqQ n hn
    have hcoef := principal_coefficient_norm520 q hq n
    have hrec : 1 / ((q : ℝ) * τ) ≤ 1 / τ := by
      apply one_div_le_one_div_of_le hτ
      have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
    calc
      _ ≤ 1 * ‖principalIntegral520 N q n -
          ((Real.exp (-(n : ℝ) / N) * logConvolution520 n.toNat : ℝ) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ ≤ C3 * X * (1 / ((q : ℝ) * τ) + 1 / Real.sqrt ((q : ℝ) * τ)) := by
        simpa [X, τ, mul_assoc] using hp
      _ ≤ C3 * X * (1 / τ + 1 / Real.sqrt ((q : ℝ) * τ)) := by gcongr
      _ = _ := by dsimp [E]; ring
  rw [local_decomposition520 N q (by omega) n]
  have heq (p m e t : ℂ) : p + m + e - t = (p - t) + m + e := by ring
  rw [heq]
  calc
    _ ≤ ‖principalCoefficient520 q ^ 2 * signedRamanujan520 q n *
        principalIntegral520 N q n - localMain520 N q n‖ +
        ‖mixedIntegral520 N q n‖ + ‖errorIntegral520 N q n‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C3 * E + C1 * E + C2 * E := add_le_add (add_le_add hd hb) hc
    _ = _ := by dsimp [E, X, τ]; ring

/-- TWIN of major_expansion520 in Decomp520a, same statement plus hT, proof copied with the twin calls.
P0093 pages 161 and 165 equations 6.4 and 8.1. The per modulus
expansion and the exact disjoint arc partition give the summed expansion.
CONDITIONAL on residue_square_mean520, mixed_bound520 and principal_model520_split. -/
theorem major_expansion520_b1122 (hG : LeanLab.DERZ1997.GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ n : ℤ, n ≤ N →
      ‖(∫ α in majorArcs280_up111 N, primeFourier111_up111 N α ^ 2 *
          Complex.exp (((2 * Real.pi * α * (n : ℝ)) : ℝ) * Complex.I)) -
        ((Real.exp (-(n : ℝ) / N) *
          (∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
            ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
              ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
                Real.cos (2 * Real.pi * (n.toNat : ℝ) * (a : ℝ) / (q : ℝ))) *
          logConvolution520 n.toNat : ℝ) : ℂ)‖ ≤
        B * N * Real.log N ^ 13 * ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            1 / Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨B, hB, N0, hlocal⟩ := local_expansion520_b1122 hG hT
  refine ⟨B, hB, max N0 (2 ^ 70), ?_⟩
  intro N hN n hn
  have hN0 := lt_of_le_of_lt (le_max_left N0 (2 ^ 70)) hN
  have hN70 := lt_of_le_of_lt (le_max_right N0 (2 ^ 70)) hN
  rw [major_integral_partition520 N hN70 n]
  have hmain : (∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊, localMain520 N q n) =
      ((Real.exp (-(n : ℝ) / N) *
        (∑ q ∈ Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 *
            ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
              Real.cos (2 * Real.pi * (n.toNat : ℝ) * (a : ℝ) / (q : ℝ))) *
        logConvolution520 n.toNat : ℝ) : ℂ) := by
    rw [mul_sum, sum_mul, Complex.ofReal_sum]
    apply sum_congr rfl
    intro q hq
    exact local_main_cos520 N q (mem_Icc.mp hq).1 n
  rw [← hmain, ← sum_sub_distrib, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro q hq
  have hqr : (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    (Nat.cast_le.mpr (mem_Icc.mp hq).2).trans (Nat.floor_le (by positivity))
  exact hlocal N hN0 q (mem_Icc.mp hq).1 hqr n hn

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997
open Finset Filter MeasureTheory

/-- TWIN of system_mass_split111 in Lemma6Split111, same statement plus hT, proof copied with the twin calls.
LEAF under GRH. P0093 page 166 equation 9.1, obtained in the paper by a trivial
modification of the derivation of 6.4 from 3.4, so through Lemma 1, Lemma 2 and
Sections 3 to 6. For one system F_q with Q equal to N to the one tenth below q and q
at most tau equal to N to the one seventh, the integral of the squared prime series over
F_q in the unit interval is at most C times N to the 93 hundredths. Equation 9.1 gives
mu squared of q over phi of q times N over ln N plus B N ln to the 13 of N times
1 over tau plus 2 over the square root of q tau, which is N to the 0.9 plus o of 1 for
such q, so the exponent 93 hundredths leaves room for every logarithm. No cover and no
count is left in this leaf. -/
theorem system_mass_split111_b1122 (hG : GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, (N : ℝ) ^ (1 / 10 : ℝ) < (q : ℝ) → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        (∫ α in arcSystemSplit111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
          ‖primeFourier111_up111 N α‖ ^ 2) ≤ C * (N : ℝ) ^ (93 / 100 : ℝ) := by
  exact Task519.system_mass519_b1122 hG hT

/-- TWIN of major_local_expansion_m111 in Major81Split111, same statement plus hT, proof copied with the twin calls.
CONDITIONAL under GRH on the three local analytic leaves of Decomp520a.
P0093 page 161 equation 6.4, from 3.4, 5.4, 5.5 and
6.3 on pages 156 and 159 to 161, for each q at most Q equal to N to the one tenth, summed over the
disjoint arcs of the major arcs as in 8.1 on page 165, at one residual n, uniformly in n.
The main term keeps the exact convolution of 6.3 and the damping e to the minus n over N,
which the printed e to the minus 1 absorbs together with the tuple weight; it is zero for
n below 4. The error is B N ln to the 13 of N times the sum over q at most Q of 1 over
tau plus 1 over the square root of q tau, as on the original scan pages 161 and 165, with
tau equal to N to the one seventh. -/
theorem major_local_expansion_m111_b1122 (hG : GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ n : ℤ, n ≤ N →
      ‖(∫ α in majorArcs280_up111 N, primeFourier111_up111 N α ^ 2 *
            Complex.exp (((2 * Real.pi * α * (n : ℝ)) : ℝ) * Complex.I)) -
          (((Real.exp (-(n : ℝ) / N) * truncSingular_m111 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ n.toNat *
            logConv_m111 n.toNat) : ℝ) : ℂ)‖ ≤
        B * N * Real.log N ^ 13 * ∑ q ∈ Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊,
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt (q * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  simpa only [truncSingular_m111, logConv_m111, logConvolution520] using
    major_expansion520_b1122 hG hT

/-- TWIN of covered_square_split111 in Decomp111, same statement plus hT, proof copied with the twin calls.
SPLIT 9 LEAF under GRH. P0093 page 166, Lemma 6, the GRH estimate 9.1 on the
systems F_q with q above Q, and the count in the proof of Lemma 7, equation
9.3, without the factor T to the k: for any at most N to the 0.01 segments of
length N to the minus 0.99, the integral of the squared prime series over their
minor arc part is at most B N times N to the minus one twentieth. -/
theorem covered_square_split111_b1122 (hG : GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      ∀ s : Finset ℝ, (s.card : ℝ) ≤ (N : ℝ) ^ (1 / 100 : ℝ) →
        ∫ α in coverSet111 N s ∩ (Set.Icc 0 1 \ majorArcsSplit111 N),
            ‖primeSeriesSplit111 N α‖ ^ 2 ≤ B * N / (N : ℝ) ^ (1 / 20 : ℝ) := by
  -- SPLIT burst 8 p3: Lemma 6 and the count of 9.3 are proved in Lemma6Split111;
  -- the GRH content is the single system leaf system_mass_split111_b1122, equation 9.1.
  classical
  obtain ⟨C, hC, N1, hm⟩ := system_mass_split111_b1122 hG hT
  refine ⟨C, hC, max N1 1, fun N _ hN s hs => ?_⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN : 1 ≤ N := by have := le_max_right N1 1; omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  let f : ℝ → ℝ := fun α => ‖primeSeriesSplit111 N α‖ ^ 2
  let minor : Set ℝ := Set.Icc 0 1 \ majorArcsSplit111 N
  let J : ℝ → Set ℝ := fun c => Set.Icc (c - 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ)))
    (c + 1 / (2 * (N : ℝ) ^ (99 / 100 : ℝ)))
  have hsel : ∀ c : ℝ, ∃ t : Set ℝ, J c ∩ minor ⊆ t ∧ MeasureTheory.IntegrableOn f t ∧
      ∫ α in t, f α ≤ C * (N : ℝ) ^ (93 / 100 : ℝ) := by
    intro c
    by_cases hne : (J c ∩ minor).Nonempty
    · obtain ⟨θ, hθJ, hθ01, hθM⟩ := hne
      have hθm : ¬ ∃ r : ℚ, (r.den : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
          |θ - r| ≤ 1 / ((r.den : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) :=
        fun hr => hθM ⟨hθ01, hr⟩
      obtain ⟨q, hqQ, hqτ, hsub⟩ := lemma6_split111 N hN c θ hθJ hθm
      refine ⟨arcSystemSplit111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1, ?_, ?_, ?_⟩
      · intro α hα
        exact ⟨hsub hα.1, hα.2.1⟩
      · exact prime_square_integrableOn_split111 N hN _ Set.inter_subset_right
      · exact hm N hN1 q hqQ hqτ
    · refine ⟨∅, ?_, by simp, by simp; positivity⟩
      intro α hα
      exact hne ⟨α, hα⟩
  choose t ht using hsel
  have hcover : coverSet111 N s ∩ minor ⊆ ⋃ c ∈ s, t c := by
    intro α hα
    have h1 := hα.1
    simp only [coverSet111, Set.mem_iUnion] at h1
    obtain ⟨c, hc, hαc⟩ := h1
    exact Set.mem_biUnion hc ((ht c).1 ⟨hαc, hα.2⟩)
  have hsum := finite_cover_integral_split111 f (fun α => by positivity)
    (coverSet111 N s ∩ minor) s t (fun c _ => (ht c).2.1) hcover
  have hcount : ∑ c ∈ s, ∫ α in t c, f α ≤
      (s.card : ℝ) * (C * (N : ℝ) ^ (93 / 100 : ℝ)) := by
    have := Finset.sum_le_card_nsmul s (fun c => ∫ α in t c, f α)
      (C * (N : ℝ) ^ (93 / 100 : ℝ)) (fun c _ => (ht c).2.2)
    simpa [nsmul_eq_mul] using this
  have hpos93 : 0 ≤ C * (N : ℝ) ^ (93 / 100 : ℝ) := by positivity
  have hfinal : (N : ℝ) ^ (1 / 100 : ℝ) * (C * (N : ℝ) ^ (93 / 100 : ℝ)) ≤
      C * N / (N : ℝ) ^ (1 / 20 : ℝ) := by
    have h1 : (N : ℝ) ^ (1 / 100 : ℝ) * (C * (N : ℝ) ^ (93 / 100 : ℝ)) =
        C * (N : ℝ) ^ (94 / 100 : ℝ) := by
      rw [mul_left_comm, ← Real.rpow_add hNp]; norm_num
    have h2 : C * N / (N : ℝ) ^ (1 / 20 : ℝ) = C * (N : ℝ) ^ (19 / 20 : ℝ) := by
      rw [mul_div_assoc]
      congr 1
      rw [show (19 / 20 : ℝ) = 1 - 1 / 20 by norm_num, Real.rpow_sub hNp, Real.rpow_one]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)) hC.le
  calc ∫ α in coverSet111 N s ∩ (Set.Icc 0 1 \ majorArcsSplit111 N),
        ‖primeSeriesSplit111 N α‖ ^ 2
      ≤ ∑ c ∈ s, ∫ α in t c, f α := hsum
    _ ≤ (s.card : ℝ) * (C * (N : ℝ) ^ (93 / 100 : ℝ)) := hcount
    _ ≤ (N : ℝ) ^ (1 / 100 : ℝ) * (C * (N : ℝ) ^ (93 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_right hs hpos93
    _ ≤ C * N / (N : ℝ) ^ (1 / 20 : ℝ) := hfinal

/-- TWIN of exceptional_square_split111 in Decomp111, same statement plus hT, proof copied with the twin calls.
SPLIT 9 under GRH, proved from the two leaves above. P0093 pages 162 to 166: Lemma 4 equation 7.6,
Lemma 5 equation 7.19, Lemma 6 and the GRH estimate 9.1, assembled as in the
proof of Lemma 7, equation 9.3, before the factor T to the k is inserted. For
one fixed eta, the integral of the squared prime series over the minor points
where T is large is at most B N times N to the minus one twentieth. The lab arcs
use tau equal to N to the one seventh instead of the paper's N to the one half;
the bound N to the minus 0.05 in 9.3 still holds for that tau, see the note. -/
theorem exceptional_square_split111_b1122 (hG : GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 < N →
        ∫ α in exceptionalArcsSplit111 N η, ‖primeSeriesSplit111 N α‖ ^ 2 ≤
          B * N / (N : ℝ) ^ (1 / 20 : ℝ) := by
  -- SPLIT burst 9: Lemma 5 covering leaf and the GRH covered square leaf.
  obtain ⟨η, hη, hη1, N1, h5⟩ := lemma5_cover_split111
  obtain ⟨B, hB, N2, hsq⟩ := covered_square_split111_b1122 hG hT
  refine ⟨η, hη, hη1, B, hB, max N1 (max N2 1), fun N hev hN => ?_⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : 1 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨s, hs, hcov⟩ := h5 N hN1
  have hsub : exceptionalArcsSplit111 N η ⊆
      coverSet111 N s ∩ (Set.Icc 0 1 \ majorArcsSplit111 N) :=
    fun α hα => ⟨hcov hα, hα.1, hα.2.1⟩
  have hint := prime_square_integrableOn_split111 N (by omega)
    (coverSet111 N s ∩ (Set.Icc 0 1 \ majorArcsSplit111 N))
    (fun α hα => hα.2.1)
  calc _ ≤ ∫ α in coverSet111 N s ∩ (Set.Icc 0 1 \ majorArcsSplit111 N),
        ‖primeSeriesSplit111 N α‖ ^ 2 :=
      MeasureTheory.setIntegral_mono_set hint
        (Filter.Eventually.of_forall (fun α => by positivity))
        (Filter.Eventually.of_forall hsub)
    _ ≤ _ := hsq N hev hN2 s hs

/-- TWIN of lemma7_split111 in Decomp111, same statement plus hT, proof copied with the twin calls.
SPLIT 9, P0093 page 166, Lemma 7 equation 9.2. Derived from the leaf
exceptional_square_split111_b1122 and the bound T of alpha at most T of zero, which
is how 9.3 inserts the factor ln to the k of N. Proved from the leaf. -/
theorem lemma7_split111_b1122 (hG : GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ B : ℝ, 0 < B ∧ ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 < N →
        ∫ α in exceptionalArcsSplit111 N η,
            ‖primeSeriesSplit111 N α‖ ^ 2 * ‖powerSeriesSplit111 N α‖ ^ k ≤
          B ^ k * N * Real.log N ^ k / (N : ℝ) ^ (1 / 20 : ℝ) := by
  obtain ⟨η, hη, hη1, B, hB, N0, h9⟩ := exceptional_square_split111_b1122 hG hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D : ℝ := 1 / Real.log 2 + 2
  have hD : 0 < D := by positivity
  refine ⟨η, hη, hη1, D * max B 1, by positivity, fun k hk => ⟨max N0 3, fun N hev hN => ?_⟩⟩
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN3 : 3 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNr : (3 : ℝ) < N := by exact_mod_cast hN3
  have hL1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set c : ℝ := Real.log N / Real.log 2 + 2
  have hc0 : 0 ≤ c := by positivity
  have hcD : c ≤ D * Real.log N := by
    simp only [c, D]
    rw [add_mul, div_mul_eq_mul_div, one_mul]
    linarith
  have hsub : exceptionalArcsSplit111 N η ⊆ Set.Icc 0 1 := fun α hα => hα.1
  have hint := prime_square_integrableOn_split111 N (by omega) _ hsub
  have hstep1 : ∫ α in exceptionalArcsSplit111 N η,
        ‖primeSeriesSplit111 N α‖ ^ 2 * ‖powerSeriesSplit111 N α‖ ^ k ≤
      ∫ α in exceptionalArcsSplit111 N η, c ^ k * ‖primeSeriesSplit111 N α‖ ^ 2 := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun α => by positivity)
    · exact hint.const_mul _
    · refine Filter.Eventually.of_forall (fun α => ?_)
      have hp := power_norm_le_split111 N (by omega) α
      have hpk : ‖powerSeriesSplit111 N α‖ ^ k ≤ c ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) hp k
      simp only
      rw [mul_comm (c ^ k)]
      exact mul_le_mul_of_nonneg_left hpk (by positivity)
  rw [MeasureTheory.integral_const_mul] at hstep1
  have hNc : 0 < (N : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hsq := h9 N hev hN0
  have hck : c ^ k ≤ D ^ k * Real.log N ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hc0 hcD k
  have hBk : B ≤ max B 1 ^ k := by
    calc B ≤ max B 1 := le_max_left _ _
      _ = max B 1 ^ 1 := (pow_one _).symm
      _ ≤ max B 1 ^ k := pow_le_pow_right₀ (le_max_right _ _) (by omega)
  have hQ : 0 ≤ (N : ℝ) / (N : ℝ) ^ (1 / 20 : ℝ) := by positivity
  calc _ ≤ c ^ k * ∫ α in exceptionalArcsSplit111 N η, ‖primeSeriesSplit111 N α‖ ^ 2 := hstep1
    _ ≤ c ^ k * (B * N / (N : ℝ) ^ (1 / 20 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (pow_nonneg hc0 _)
    _ ≤ (D ^ k * Real.log N ^ k) * (max B 1 ^ k * ((N : ℝ) / (N : ℝ) ^ (1 / 20 : ℝ))) := by
        rw [mul_div_assoc]
        exact mul_le_mul hck (mul_le_mul_of_nonneg_right hBk hQ)
          (mul_nonneg hB.le hQ) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- TWIN of major_truncated_split111 in Decomp111, same statement plus hT, proof copied with the twin calls.
SPLIT 9 LEAF under GRH. P0093 Sections 3 to 6 with equation 6.4 on page 161,
Section 8 equations 8.1 and 8.2 on page 165, and equation 10.7 on page 168.
The major arc integral equals the main term built from the truncated singular
series at Q equal to N to the one tenth, up to an error that is eventually
below any epsilon times the scale. -/
theorem major_truncated_split111_b1122 (hG : GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContributionSplit111 k N (majorArcsSplit111 N) -
          mainTermTrunc111 k N ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊| ≤ ε * scale111 k N := by
  -- SPLIT burst 8 p3: the tuple expansion of 8.1 is proved; the GRH core 6.4 is the leaf
  -- major_local_expansion_m111_b1122 and the bookkeeping of 8.1, 8.2 and 10.7 is the
  -- unconditional leaf major_bookkeeping_m111, both in Major81Split111.
  obtain ⟨B, hB, N1, hA⟩ := major_local_expansion_m111_b1122 hG hT
  obtain ⟨N2, hC⟩ := major_bookkeeping_m111 k hk ε hε B hB
  refine ⟨max N1 (max N2 1), fun N hEv hN => ?_⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN0 : 1 ≤ N := by
    have := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    omega
  rw [major_tuple_expand_split111 k N hN0]
  exact hC N hEv hN2
    (fun t => ∫ α in majorArcsSplit111 N, primeSeriesSplit111 N α ^ 2 *
      Complex.exp (((2 * Real.pi * α * t) : ℝ) * Complex.I))
    (fun n hn => hA N hN1 n hn)

/-- TWIN of major_error_split111 in Decomp111, same statement plus hT, proof copied with the twin calls.
SPLIT piece 2 of error_bound111_b1122. P0093 Sections 3 to 6, pages 155 to 161,
the GRH Mellin estimate 5.2 on page 159, and Section 8 equations 8.1 and 8.2
on page 165 with equations 10.5 to 10.7 on page 168. For fixed k the major arc
integral equals the singular series main term up to an error that is
arbitrarily small relative to the scale. -/
theorem major_error_split111_b1122 (hG : GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContributionSplit111 k N (majorArcsSplit111 N) - mainTerm111 k N| ≤
        ε * scale111 k N := by
  -- SPLIT burst 9: truncated major arc leaf, singular truncation, proved absorption.
  obtain ⟨N1, h1⟩ := major_truncated_split111_b1122 hG hT k hk (ε / 2) (by positivity)
  obtain ⟨B, hB, N2, h2⟩ := singular_truncation_split111
  obtain ⟨N3, h3⟩ := trunc_absorb_split111 k (by omega) B (ε / 2) hB.le (by positivity)
  refine ⟨max N1 (max N2 N3), fun N hev hN => ?_⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : N3 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNc : 0 < (N : ℝ) ^ (1 / 50 : ℝ) := Real.rpow_pos_of_pos (by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact this) _
  have hd := trunc_difference_split111 k N ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ _
    (by positivity) (h2 N hN2)
  have ha := h1 N hev hN1
  have hb := h3 N hN3
  calc _ = |(arcContributionSplit111 k N (majorArcsSplit111 N) -
          mainTermTrunc111 k N ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊) +
        (mainTermTrunc111 k N ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ - mainTerm111 k N)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ ε / 2 * scale111 k N + ε / 2 * scale111 k N := add_le_add ha (hd.trans hb)
    _ = ε * scale111 k N := by ring

/-- TWIN of exceptional_error_split111 in Decomp111, same statement plus hT, proof copied with the twin calls.
SPLIT piece 3 of error_bound111_b1122. P0093 pages 162 to 166, Lemmas 4 to 7,
equations 7.6, 9.1 and 9.2. Under GRH one absolute eta makes the set where T
is large so small that its minor arc contribution is arbitrarily small relative
to the scale for each fixed k. -/
theorem exceptional_error_split111_b1122 (hG : GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ k : ℕ, 3 ≤ k →
      ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |arcContributionSplit111 k N (exceptionalArcsSplit111 N η)| ≤
          ε * scale111 k N := by
  -- SPLIT burst 9: Lemma 7 from the square leaf, then proved absorption.
  obtain ⟨η, hη, hη1, B, hB, h7⟩ := lemma7_split111_b1122 hG hT
  refine ⟨η, hη, hη1, fun k hk ε hε => ?_⟩
  obtain ⟨N1, h1⟩ := h7 k hk
  obtain ⟨N2, h2⟩ := exceptional_absorb_split111 k (by omega) B ε hε
  refine ⟨max N1 N2, fun N hev hN => ?_⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  calc _ ≤ _ := arc_abs_le_split111 k N _
    _ ≤ Real.exp 1 * (B ^ k * N * Real.log N ^ k / (N : ℝ) ^ (1 / 20 : ℝ)) :=
        mul_le_mul_of_nonneg_left (h1 N hev hN1) (Real.exp_pos 1).le
    _ ≤ _ := h2 N hN2

/-- TWIN of error_bound111 in Decomp111, same statement plus hT, proof copied with the twin calls.
LEAF. P0093 Section 10, page 168 after equation 10.7.
This leaf includes the analytic work of Sections 3 to 10 and Romanov 1940,
reference 4, used by Lemma 3 on page 162. The geometric exponent is weakened
from k minus 1 to k minus 2 using zero less than eta less than one. -/
theorem error_bound111_b1122 (hG : GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ η < 1 ∧
      ∀ k : ℕ, 3 ≤ k → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |(representationCount111 k N : ℝ) - mainTerm111 k N| ≤
          5 * C * scale111 k N * (1 - η) ^ (k - 2) := by
  -- P0093 page 168 after equation 10.7: combine the three arc estimates.
  obtain ⟨η, hη, hη1, hE⟩ := exceptional_error_split111_b1122 hG hT
  obtain ⟨C, hC, hR⟩ := minor_error_split111 η hη hη1
    (fun N α hα => good_minor_power_bound_split111 N η α hα)
  refine ⟨C, η, hC, hη, hη1, ?_⟩
  intro k hk
  have hr : 0 < (1 - η) ^ (k - 2) := pow_pos (by linarith) _
  have hε : 0 < C * (1 - η) ^ (k - 2) := mul_pos hC hr
  obtain ⟨NM, hM⟩ := major_error_split111_b1122 hG hT k hk _ hε
  obtain ⟨NE, hE⟩ := hE k hk _ hε
  obtain ⟨NR, hR⟩ := hR k hk
  refine ⟨max 1 (max NM (max NE NR)), ?_⟩
  intro N hev hN
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hm : NM < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have he : NE < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hg : NR < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hmajor := hM N hev hm
  have hexc := hE N hev he
  have hminor := hR N hev hg
  have hs : 0 ≤ scale111 k N := by
    unfold scale111
    have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg hl hl2) _)
  have hid := circle_partition_split111 k N (by omega) η
  have htri := abs_add_le
    (arcContributionSplit111 k N (majorArcsSplit111 N) - mainTerm111 k N)
    (arcContributionSplit111 k N (exceptionalArcsSplit111 N η))
  have htri' := abs_add_le
    ((arcContributionSplit111 k N (majorArcsSplit111 N) - mainTerm111 k N) +
      arcContributionSplit111 k N (exceptionalArcsSplit111 N η))
    (arcContributionSplit111 k N (goodMinorArcsSplit111 N η))
  have heq : (representationCount111 k N : ℝ) - mainTerm111 k N =
    ((arcContributionSplit111 k N (majorArcsSplit111 N) - mainTerm111 k N) +
      arcContributionSplit111 k N (exceptionalArcsSplit111 N η)) +
      arcContributionSplit111 k N (goodMinorArcsSplit111 N η) := by rw [hid]; ring
  rw [heq]
  nlinarith [mul_nonneg (mul_nonneg hC.le hs) hr.le]

/-- TWIN of linnik1951_decomposed111 in Decomp111, statement copied with the hypothesis
hT added, proof copied from linnik1951_decomposed111_w1121 with error_bound111_b1122.
P0093 pages 154 and 168 to 169. Assembly of the exact lab statement.
CONDITIONAL ON GRH and on hT, the statement of grh_mellin_transfer519. -/
theorem linnik1951_decomposed_of_transfer_b1122 (hG : GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N) :
    ∃ K, AllLargeEven (LinnikAtMost K) := by
  obtain ⟨C, η, hC, hη, hη1, he⟩ := error_bound111_b1122 hG hT
  obtain ⟨c, hc, hm⟩ := main_lower111
  obtain ⟨k, hk, hkc⟩ := choose_exponent111 hC hc hη hη1
  obtain ⟨Ne, he⟩ := he k hk
  obtain ⟨Nm, hm⟩ := hm k hk
  refine ⟨k, max 1 (max Ne Nm), ?_⟩
  intro N hev hN
  have h1 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNe : Ne < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNm : Nm < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have he' := he N hev hNe
  have hpos : 0 < (representationCount111 k N : ℝ) :=
    positive_of_error111 (scale_pos111 k N h1) hkc (hm N hev hNm) (by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using he')
  exact atMost_of_exact (representation_of_count_pos111 (by exact_mod_cast hpos))

/-- TWIN of local_arc_small_residual_supply552 in Decomp552e, statement copied with the
hypothesis hT added, proof copied with local_expansion520_b1122.
P0093 pages 160 and 161 equations 5.4, 5.5 and 6.3.
CONDITIONAL ON GRH and hT. -/
theorem local_arc_small_residual_supply552_b1122 (hG : LeanLab.DERZ1997.GRH)
    (hT : ∃ B0 : ℝ, 0 < B0 ∧ ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∃ M : ℝ → ℂ, (Continuous M ∧ ∀ t : ℝ,
            ‖M t‖ ≤ B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧ ∀ α : ℝ,
              ‖Task519.characterPrime519 χ N α - Task519.mellinU519 N M α‖ ≤ B * Real.sqrt N)
    (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        n ≤ 3 →
        n ≤ N →
        ‖localArc1622 N q n‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  clear hM
  obtain ⟨c, hc, N0, h⟩ := local_expansion520_b1122 hG hT
  refine ⟨c, hc, N0, ?_⟩
  intro N hN q hq hqQ n hn3 hnN
  have hzero : localMain520 N q n = 0 := by
    simp [localMain520, logConvolution_vanish520 n.toNat (by omega)]
  have hb := h N hN q hq hqQ n hnN
  rw [hzero, sub_zero] at hb
  exact hb

end LeanLab.Linnik1951
