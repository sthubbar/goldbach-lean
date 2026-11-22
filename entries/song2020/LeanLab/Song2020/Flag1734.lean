module

public import LeanLab.Song2020.Decomp139b

/-!
Song 2020, arXiv 2012.06322 v1. A lab review found that the steps `logarithmic_transfer139`
and `fourier_error` cannot be proved as transcribed.

Part A. `logarithmic_transfer139`, Decomp139b, printed page 9, Section 4.
The flag is right in substance. Lemma 4 gives the bound for every positive epsilon only,
and at windows y just above n to the power songExponent the product of Lemma 4 with
Lemma 5 is y squared times n to the power epsilon divided by y to the power 8/31 times
n to the power 8/31 songExponent, which leaves exactly n to the epsilon, as
`Audit139.threshold_exponent_loss139` shows. No logarithmic saving follows. The
step is not refuted: it is an existential claim about the true size of f minus g and
may well hold, so it is accepted as the named hypothesis `LogTransferDQ` with a match
theorem. The corrected statement `LogTransferMarginDQ` adds a positive window margin
delta and is proved below from Lemma 4 and Lemma 5 as explicit arguments.

Part B. `fourier_error`, DecompJ1132, printed pages 4 and 5.
The flag is right. Lemma 1 on page 4 is the Vaaler construction: specific coefficients
a_h together with a majorant with coefficients b_h, and the S2 bound uses b_h. The
leaf quantifies over EVERY family a bounded by K over the absolute value of h, which is
far stronger than the paper and almost surely false, but no Lean refutation is given,
so it is an open question, not a refuted statement. The assembly `fourier_approximation` only needs one
family, so the leaf is re-cut as the existential named hypothesis `FourierApproxDQ`.

AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.Flag1734

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Song2020.Decomp139

noncomputable section

/-! ## Part A -/

/-- Named hypothesis. The exact conclusion of `logarithmic_transfer139`, page 9.
Twin: the maximum of the absolute value of f minus g, times the two mean squares,
is at most a constant times y squared over the fourth power of log n. -/
def LogTransferDQ : Prop :=
  ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
      ∃ D : ℝ, 0 ≤ D ∧ (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) ∧
        2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
          (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
            C * (y ^ 2 / Real.log (n : ℝ) ^ 4)

/-- Match theorem: the named hypothesis gives the lab step for every Lemma 4 input. -/
theorem logTransferDQ_match (h : LogTransferDQ) (H4 : Lemma4) :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
        ∃ D : ℝ, 0 ≤ D ∧ (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) ∧
          2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
            (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
              C * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by
  have _ := H4
  exact h

/-- Corrected statement, page 9, with window margin `δ`.
Twin: for y larger than n to the power songExponent plus delta, the Section 4 error of
f against g is at most a constant times y squared over the fourth power of log n. -/
def LogTransferMarginDQ (δ : ℝ) : Prop :=
  ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ (songExponent γ + δ) < y → y ≤ (n : ℝ) / 3 →
      ∃ D : ℝ, 0 ≤ D ∧ (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) ∧
        2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
          (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
            C * (y ^ 2 / Real.log (n : ℝ) ^ 4)

/-- Eventually the fourth power of log n is at most n to a positive power. -/
theorem log_pow_four_le_rpow (r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Real.log (n : ℝ) ^ 4 ≤ (n : ℝ) ^ r := by
  have ho := (isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < r / 4)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hn := tendsto_natCast_atTop_atTop.eventually (ho.and (Filter.eventually_ge_atTop 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hn
  refine ⟨N, fun n hn' => ?_⟩
  obtain ⟨hb, h1⟩ := hN n hn'
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hl0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0,
    abs_of_nonneg (Real.rpow_nonneg hn0 _), one_mul] at hb
  calc Real.log (n : ℝ) ^ 4 ≤ ((n : ℝ) ^ (r / 4)) ^ 4 := by gcongr
    _ = (n : ℝ) ^ r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num

/-- Proved from Lemma 4 and Lemma 5 as explicit arguments: the corrected statement. -/
theorem logTransferMargin_of (H4 : Lemma4) (H5 : Lemma5) (δ : ℝ) (hδ : 0 < δ) :
    LogTransferMarginDQ δ := by
  intro γ hγ hγ1
  obtain ⟨C4, N4, h4⟩ := H4 γ hγ hγ1 (2 * δ / 31) (by positivity)
  obtain ⟨C5, N5, h5⟩ := H5 γ hγ hγ1
  obtain ⟨NL, hL⟩ := log_pow_four_le_rpow (6 * δ / 31) (by positivity)
  refine ⟨4 * |C4| * |C5|, max 3 (max N4 (max N5 NL)), ?_⟩
  intro n hn y hy hy3
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (n : ℝ) ^ songExponent γ < y :=
    lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hy
  have hy0 : 0 < y := lt_of_le_of_lt (Real.rpow_nonneg hn0.le _) hs
  set X : ℝ := (n : ℝ) ^ (21 / 31 - 14 * γ / 31 + 2 * δ / 31) * y ^ ((23 : ℝ) / 31)
  have hX : 0 ≤ X := by positivity
  refine ⟨|C4| * X, by positivity, fun α => ?_, ?_⟩
  · exact (h4 n (by omega) y hs hy3 α).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX)
  obtain ⟨hf, hg⟩ := h5 n (by omega) y hs hy3
  set If := ∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2
  set Ig := ∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2
  have hp1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 - γ) := Real.one_le_rpow hn1 (by linarith)
  have hI : If + Ig ≤ 2 * |C5| * ((n : ℝ) ^ (1 - γ) * y) := by
    have a1 : C5 * ((n : ℝ) ^ (1 - γ) * y) ≤ |C5| * ((n : ℝ) ^ (1 - γ) * y) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have a2 : C5 * y ≤ |C5| * ((n : ℝ) ^ (1 - γ) * y) := by
      calc C5 * y ≤ |C5| * y := mul_le_mul_of_nonneg_right (le_abs_self _) hy0.le
        _ ≤ |C5| * ((n : ℝ) ^ (1 - γ) * y) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); nlinarith
    linarith
  have hIf0 : 0 ≤ If := intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => by positivity)
  have hIg0 : 0 ≤ Ig := intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => by positivity)
  -- the exponent identity
  have hsplit : (n : ℝ) ^ (21 / 31 - 14 * γ / 31 + 2 * δ / 31) * (n : ℝ) ^ (1 - γ) =
      ((n : ℝ) ^ (songExponent γ + δ)) ^ ((8 : ℝ) / 31) * (n : ℝ) ^ (-(6 * δ / 31)) := by
    rw [← Real.rpow_mul hn0.le, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1; unfold songExponent; ring
  have hlog : Real.log (n : ℝ) ^ 4 * (n : ℝ) ^ (-(6 * δ / 31)) ≤ 1 := by
    have := hL n (by omega)
    rw [Real.rpow_neg hn0.le]
    have hp : 0 < (n : ℝ) ^ (6 * δ / 31) := by positivity
    rw [← div_eq_mul_inv, div_le_one hp]; exact this
  have hy8 : ((n : ℝ) ^ (songExponent γ + δ)) ^ ((8 : ℝ) / 31) ≤ y ^ ((8 : ℝ) / 31) :=
    Real.rpow_le_rpow (by positivity) hy.le (by norm_num)
  have hyy : y ^ ((8 : ℝ) / 31) * y ^ ((23 : ℝ) / 31) * y = y ^ 2 := by
    rw [← Real.rpow_add hy0]; norm_num; ring
  have hlogpos : 0 < Real.log (n : ℝ) ^ 4 := by
    have : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    positivity
  have hkey : X * ((n : ℝ) ^ (1 - γ) * y) * Real.log (n : ℝ) ^ 4 ≤ y ^ 2 := by
    have e : X * ((n : ℝ) ^ (1 - γ) * y) * Real.log (n : ℝ) ^ 4 =
        ((n : ℝ) ^ (21 / 31 - 14 * γ / 31 + 2 * δ / 31) * (n : ℝ) ^ (1 - γ)) *
          Real.log (n : ℝ) ^ 4 * (y ^ ((23 : ℝ) / 31) * y) := by
      simp only [X]; ring
    rw [e, hsplit, ← hyy]
    have hA : 0 ≤ ((n : ℝ) ^ (songExponent γ + δ)) ^ ((8 : ℝ) / 31) := by positivity
    have hB : 0 ≤ y ^ ((23 : ℝ) / 31) * y := by positivity
    calc ((n : ℝ) ^ (songExponent γ + δ)) ^ ((8 : ℝ) / 31) * (n : ℝ) ^ (-(6 * δ / 31)) *
          Real.log (n : ℝ) ^ 4 * (y ^ ((23 : ℝ) / 31) * y)
        = ((n : ℝ) ^ (songExponent γ + δ)) ^ ((8 : ℝ) / 31) *
            (Real.log (n : ℝ) ^ 4 * (n : ℝ) ^ (-(6 * δ / 31))) *
              (y ^ ((23 : ℝ) / 31) * y) := by ring
      _ ≤ ((n : ℝ) ^ (songExponent γ + δ)) ^ ((8 : ℝ) / 31) * 1 *
              (y ^ ((23 : ℝ) / 31) * y) := by gcongr
      _ ≤ y ^ ((8 : ℝ) / 31) * 1 * (y ^ ((23 : ℝ) / 31) * y) := by gcongr
      _ = y ^ ((8 : ℝ) / 31) * y ^ ((23 : ℝ) / 31) * y := by ring
  have hkey' : X * ((n : ℝ) ^ (1 - γ) * y) ≤ y ^ 2 / Real.log (n : ℝ) ^ 4 := by
    rw [le_div_iff₀ hlogpos]; exact hkey
  calc 2 * (|C4| * X) * (If + Ig)
      ≤ 2 * (|C4| * X) * (2 * |C5| * ((n : ℝ) ^ (1 - γ) * y)) := by gcongr
    _ = 4 * |C4| * |C5| * (X * ((n : ℝ) ^ (1 - γ) * y)) := by ring
    _ ≤ 4 * |C4| * |C5| * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by gcongr

/-- Vacuity instance: at gamma 89/90 and delta 1/32 the window hypotheses hold at
n equal to 2 to the 64 and y equal to n over 3. -/
theorem logTransferMargin_vacuity :
    ∃ γ δ : ℝ, 44 / 45 < γ ∧ γ < 1 ∧ 0 < δ ∧ ∃ n : ℕ, ∃ y : ℝ,
      (n : ℝ) ^ (songExponent γ + δ) < y ∧ y ≤ (n : ℝ) / 3 := by
  refine ⟨89 / 90, 1 / 32, by norm_num, by norm_num, by norm_num, 2 ^ 64,
    ((2 ^ 64 : ℕ) : ℝ) / 3, ?_, le_rfl⟩
  have he : songExponent (89 / 90) + 1 / 32 = (1 / 64 : ℝ) * 62 := by
    unfold songExponent; norm_num
  rw [he, Real.rpow_mul (by positivity)]
  have h2 : ((2 ^ 64 : ℕ) : ℝ) ^ (1 / 64 : ℝ) = 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h2]; norm_num

/-! ## Part B -/

/-- Named hypothesis, the re-cut of `fourier_error`: one Vaaler family, pages 4 and 5,
Lemma 1 with the S2 bound. Twin: there are coefficients a_h bounded by K over the
absolute value of h whose truncated sum approximates the sawtooth prime sum within the
S2 budget. Vaaler via Graham and Kolesnik Theorem A.6, plus van der Corput. -/
def FourierApproxDQ : Prop :=
  ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
    ∃ a : ℕ → ℤ → ℂ, ∃ K : ℝ, 1 ≤ K ∧
      (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
        ∀ H : ℕ, 1 ≤ H → ∀ α : ℝ,
          ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤ C * tailBudget γ n y H

/-- Match theorem: `FourierApproxDQ` is exactly the lab step `fourier_approximation`. -/
theorem fourierApproxDQ_match : FourierApproxDQ ↔
    (∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ a : ℕ → ℤ → ℂ, ∃ K : ℝ, 1 ≤ K ∧
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
          ∀ H : ℕ, 1 ≤ H → ∀ α : ℝ,
            ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
              C * tailBudget γ n y H) := Iff.rfl

end

end LeanLab.Song2020.Flag1734
