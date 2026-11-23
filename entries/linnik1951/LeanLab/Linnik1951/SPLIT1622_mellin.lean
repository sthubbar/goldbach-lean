module

public import LeanLab.Linnik1951.Repair493MellinData
public import LeanLab.Linnik1951.SPLIT_central_kernel_mass442

/-!
Unit U-1622. Source faithful re-cut of the Mellin square bounds of P0093.
Replaces the dead pointwise splits in SPLIT_mellin_near357 and SPLIT_mellin_positive_far357.
The original scan of pages 156 to 159 controls the statements.
AI wrote the Lean code. Binary Goldbach is open.

Lemma 2 of page 156 is abstract. Its two steps carry no GRH and no primes.
The transfer leaf is the only place GRH enters. The assembly proves the exact types
of mellin_near357, mellin_positive_far357 and MellinBound280, and the same bound at
any radius 1 over R, which section 9 needs at radius 2 over q tau.
-/

@[expose] public section

namespace LeanLab.Linnik1951


/-- LEAF. P0093 page 158 display before equation 4.8, on the central interval
only. For any coefficient with the line bound, U is at most B times N over the
square root of R times ln cubed N when |alpha| is at most 4 over N. Here R stands
for q tau. No GRH, no primes. -/
theorem lemma2_central1622 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
        ∀ α : ℝ, |α| ≤ 4 / (N : ℝ) →
          ‖mellinU1622 N M α‖ ≤ B * (N : ℝ) / Real.sqrt R * Real.log N ^ 3 := by
  obtain ⟨C, hC, N0, hc⟩ := central_kernel_mass442_split
  refine ⟨(1 / (2 * Real.pi)) * B0 * C, by positivity, max 1 N0, ?_⟩
  intro N hN R hR1 hR M hM α hα
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hRp : 0 < R := by linarith
  have hRN : R ≤ N := by
    calc R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hR
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
      _ = N := Real.rpow_one _
  obtain ⟨hI, hm⟩ := hc N (by omega) α hα
  have hl : 0 ≤ Real.log N ^ 3 := pow_nonneg (Real.log_nonneg hNr) 3
  calc
    _ ≤ (1 / (2 * Real.pi)) * B0 *
        (∫ t : ℝ, ‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
      mellin_kernel_domination442 N α B0 hB0.le M hM hI
    _ ≤ (1 / (2 * Real.pi)) * B0 * (C * Real.sqrt N * Real.log N ^ 3) := by
      gcongr
    _ ≤ (1 / (2 * Real.pi)) * B0 * (C * ((N : ℝ) / Real.sqrt R) * Real.log N ^ 3) := by
      gcongr
      exact sqrt_scale442 N R hNp hRp hRN
    _ = _ := by ring


/-- For N at least 8 the power 4 times N to the two sevenths is at most N. -/
theorem four_rpow1622 (N : ℕ) (hN : 8 ≤ N) : 4 * (N : ℝ) ^ (2 / 7 : ℝ) ≤ N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h8R : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h5 : (4 : ℝ) ≤ (N : ℝ) ^ (5 / 7 : ℝ) := by
    have hpow : (4 : ℝ) ^ 7 ≤ (N : ℝ) ^ 5 := by
      have h1 : (8 : ℝ) ^ 5 ≤ (N : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) h8R 5
      norm_num at h1 ⊢
      linarith
    have hle := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ 7) hpow
      (by norm_num : (0 : ℝ) ≤ 1 / 7)
    have h4 : ((4 : ℝ) ^ ((7 : ℕ) : ℝ)) ^ (1 / 7 : ℝ) = 4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show (((7 : ℕ) : ℝ)) * (1 / 7 : ℝ) = 1 by norm_num, Real.rpow_one]
    have hN5 : ((N : ℝ) ^ ((5 : ℕ) : ℝ)) ^ (1 / 7 : ℝ) = (N : ℝ) ^ (5 / 7 : ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hNpos)]
      norm_num
    rwa [← Real.rpow_natCast (4 : ℝ) 7, ← Real.rpow_natCast (N : ℝ) 5, h4, hN5] at hle
  have he : (N : ℝ) ^ (5 / 7 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) = (N : ℝ) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hm : (4 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) ^ (5 / 7 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) :=
    mul_le_mul_of_nonneg_right h5 (Real.rpow_pos_of_pos hNpos _).le
  linarith

/-- If x is within b of u, then the square of x is at most twice the square of u
plus twice the square of b. -/
theorem norm_sq_le_of_near1622 {x u : ℂ} {b : ℝ} (h : ‖x - u‖ ≤ b) :
    ‖x‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * b ^ 2 := by
  have h1 : ‖x‖ ≤ ‖u‖ + ‖x - u‖ := by
    calc ‖x‖ = ‖u + (x - u)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have h0 := norm_nonneg (x - u)
  have h2 : ‖x‖ ≤ ‖u‖ + b := by linarith
  have h3 : ‖x‖ ^ 2 ≤ (‖u‖ + b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith [sq_nonneg (‖u‖ - b)]

/-- q tau with q at most tau is at most N to the two sevenths, and at least 1. -/
theorem qtau_range1622 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hqt : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) :
    1 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ∧
      (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hτ : 1 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := Real.one_le_rpow hNr (by norm_num)
  constructor
  · nlinarith
  · have h2 : (N : ℝ) ^ (1 / 7 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) = (N : ℝ) ^ (2 / 7 : ℝ) := by
      rw [← Real.rpow_add hNp]
      norm_num
    nlinarith

end LeanLab.Linnik1951
