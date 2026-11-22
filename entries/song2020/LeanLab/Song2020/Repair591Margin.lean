module

public import LeanLab.Song2020.Decomp139b
public import LeanLab.Song2020.Consequences139

/-!
AI wrote the Lean code, Codex by OpenAI.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, Section 4, page 9.
The positive margin below is an added hypothesis. It is not the printed exact window.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.Repair591Margin

open LeanLab.Song2020 LeanLab.Song2020.State1562

/-- Song 2020, page 9, scalar transfer with an added positive window margin.
The power error times the mean square scale saves n to the 4 delta over 31. -/
theorem margin_budget591 (γ δ n y : ℝ) (hn : 1 ≤ n) (hδ : 0 < δ)
    (hy : n ^ (songExponent γ + δ) ≤ y) :
    (n ^ (21 / 31 - 14 * γ / 31 + 4 * δ / 31) * y ^ ((23 : ℝ) / 31)) *
        (n ^ (1 - γ) * y) ≤ y ^ 2 * n ^ (-4 * δ / 31) := by
  have hn0 : 0 < n := by linarith
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hn0 _).trans_le hy
  have hm : n ^ ((songExponent γ + δ) * ((8 : ℝ) / 31)) ≤ y ^ ((8 : ℝ) / 31) := by
    rw [Real.rpow_mul hn0.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hn0.le _) hy (by norm_num)
  have he : n ^ (21 / 31 - 14 * γ / 31 + 4 * δ / 31) * n ^ (1 - γ) =
      n ^ (-4 * δ / 31) * n ^ ((songExponent γ + δ) * ((8 : ℝ) / 31)) := by
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1
    unfold songExponent
    ring
  have heY : y ^ ((8 : ℝ) / 31) * y ^ ((23 : ℝ) / 31) * y = y ^ 2 := by
    rw [← Real.rpow_add hy0]
    norm_num
    ring
  calc _ = (n ^ (21 / 31 - 14 * γ / 31 + 4 * δ / 31) * n ^ (1 - γ)) *
          y ^ ((23 : ℝ) / 31) * y := by ring
    _ = (n ^ (-4 * δ / 31) * n ^ ((songExponent γ + δ) * ((8 : ℝ) / 31))) *
          y ^ ((23 : ℝ) / 31) * y := by rw [he]
    _ ≤ (n ^ (-4 * δ / 31) * y ^ ((8 : ℝ) / 31)) * y ^ ((23 : ℝ) / 31) * y := by
      gcongr
    _ = y ^ 2 * n ^ (-4 * δ / 31) := by
      calc _ = n ^ (-4 * δ / 31) * (y ^ ((8 : ℝ) / 31) * y ^ ((23 : ℝ) / 31) * y) := by ring
           _ = _ := by rw [heY]; ring

/-- Song 2020, page 9, logarithmic absorption after a positive power saving.
This uses Mathlib log_le_rpow_div with exponent eta over four. -/
theorem log_power_absorption591 (n η : ℝ) (hn : 1 < n) (hη : 0 < η) :
    n ^ (-η) ≤ (4 / η) ^ 4 / Real.log n ^ 4 := by
  have hn0 : 0 < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hn
  have he : 0 < η / 4 := by positivity
  have h := Real.log_le_rpow_div hn0.le he
  have hpow : Real.log n ^ 4 ≤ (n ^ (η / 4) / (η / 4)) ^ 4 := by gcongr
  have hrpow : (n ^ (η / 4)) ^ 4 = n ^ η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    push_cast
    ring
  have hb : Real.log n ^ 4 ≤ n ^ η * (4 / η) ^ 4 := by
    calc _ ≤ (n ^ (η / 4) / (η / 4)) ^ 4 := hpow
      _ = n ^ η * (4 / η) ^ 4 := by rw [div_eq_mul_inv, mul_pow, hrpow]; congr 2; field_simp
  rw [le_div_iff₀ (by positivity : 0 < Real.log n ^ 4)]
  have hInv : n ^ (-η) * n ^ η = 1 := by
    rw [← Real.rpow_add hn0]
    simp
  calc n ^ (-η) * Real.log n ^ 4 ≤ n ^ (-η) * (n ^ η * (4 / η) ^ 4) := by gcongr
    _ = (4 / η) ^ 4 := by rw [← mul_assoc, hInv, one_mul]

/-- Song 2020, page 9, the transfer with a positive window margin.
Conditional on Lemma4. The margin is explicit and is absent from the printed theorem. -/
theorem logarithmic_transfer_with_margin591 (H4 : Lemma4) (γ : ℝ)
    (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ (songExponent γ + δ) ≤ y → y ≤ (n : ℝ) / 3 →
      ∃ D : ℝ, 0 ≤ D ∧ (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) ∧
        2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
          (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
            C * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by
  obtain ⟨C4, N4, h4⟩ := H4 γ hγ hγ1 (4 * δ / 31) (by positivity)
  obtain ⟨C5, N5, h5⟩ := song_lemma5 γ hγ hγ1
  let A := max C4 0
  let B := max C5 0
  let η := 4 * δ / 31
  have hA : 0 ≤ A := le_max_right _ _
  have hB : 0 ≤ B := le_max_right _ _
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨4 * A * B * (4 / η) ^ 4, by positivity, max 2 (max N4 N5), ?_⟩
  intro n hn y hy hy3
  have hn2 : 2 ≤ n := by omega
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < n := by linarith
  have hwin : (n : ℝ) ^ songExponent γ < y :=
    (Real.rpow_lt_rpow_of_exponent_lt hn1 (by linarith : songExponent γ < songExponent γ + δ)).trans_le hy
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hn0 _).trans hwin
  let P := (n : ℝ) ^ (21 / 31 - 14 * γ / 31 + 4 * δ / 31) * y ^ ((23 : ℝ) / 31)
  let Q := (n : ℝ) ^ (1 - γ) * y
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hnp : 1 ≤ (n : ℝ) ^ (1 - γ) := Real.one_le_rpow hn1.le (by linarith)
  have hyQ : y ≤ Q := by dsimp [Q]; nlinarith
  obtain ⟨hf, hg⟩ := h5 n (by omega) y hwin hy3
  have hf' : (∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) ≤ B * Q :=
    hf.trans (mul_le_mul_of_nonneg_right (le_max_left C5 0) hQ)
  have hg' : (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2) ≤ B * Q := by
    calc _ ≤ C5 * y := hg
      _ ≤ B * y := mul_le_mul_of_nonneg_right (le_max_left C5 0) hy0.le
      _ ≤ B * Q := mul_le_mul_of_nonneg_left hyQ hB
  refine ⟨A * P, mul_nonneg hA hP, ?_, ?_⟩
  · intro α
    exact (h4 n (by omega) y hwin hy3 α).trans
      (mul_le_mul_of_nonneg_right (le_max_left C4 0) hP)
  · have hscalar := margin_budget591 γ δ (n : ℝ) y hn1.le hδ hy
    have hlog := log_power_absorption591 (n : ℝ) η hn1 hη
    calc 2 * (A * P) * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
          (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2))
        ≤ 2 * (A * P) * (B * Q + B * Q) :=
          mul_le_mul_of_nonneg_left (add_le_add hf' hg') (by positivity)
      _ = 4 * A * B * (P * Q) := by ring
      _ ≤ 4 * A * B * (y ^ 2 * (n : ℝ) ^ (-η)) := by
          have heη : -η = -4 * δ / 31 := by dsimp [η]; ring
          rw [heη]
          exact mul_le_mul_of_nonneg_left hscalar (by positivity)
      _ ≤ 4 * A * B * (y ^ 2 * ((4 / η) ^ 4 / Real.log (n : ℝ) ^ 4)) := by gcongr
      _ = _ := by ring

/-- Song 2020, page 9, the asymptotic formula with an explicit positive window margin.
Conditional on Lemma3 and Lemma4. -/
theorem asymptotic_with_margin591 (H3 : Lemma3 (7 / 8)) (H4 : Lemma4)
    (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ (songExponent γ + δ) ≤ y → y ≤ (n : ℝ) / 3 →
      ‖RS γ n y - (mainTerm n y : ℂ)‖ ≤ C * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by
  obtain ⟨C3, N3, h3⟩ := H3
  obtain ⟨C4, _, N4, h4⟩ := logarithmic_transfer_with_margin591 H4 γ hγ hγ1 δ hδ
  refine ⟨C3 + C4, max 1 (max N3 N4), ?_⟩
  intro n ho hn y hy hy3
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsmall : (n : ℝ) ^ ((7 : ℝ) / 8) ≤ y :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [(songExponent_mem hγ hγ1).1])).trans hy
  have hmain := h3 n ho (by omega) y hsmall hy3
  obtain ⟨D, _, hD, hbudget⟩ := h4 n (by omega) y hy hy3
  have herr := (Decomp139b.song_cube_transfer139 γ n y D hD).trans hbudget
  calc ‖RS γ n y - (mainTerm n y : ℂ)‖
      ≤ ‖RS γ n y - gCube n y‖ + ‖gCube n y - (mainTerm n y : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C4 * (y ^ 2 / Real.log (n : ℝ) ^ 4) + C3 * (y ^ 2 / Real.log (n : ℝ) ^ 4) :=
      add_le_add herr hmain
    _ = _ := by ring

/-- Song 2020, page 9, the representation deduction with an explicit positive margin.
Conditional on Lemma3 and Lemma4. The exact window statement is unchanged. -/
theorem songWindow_with_margin591 (H3 : Lemma3 (7 / 8)) (H4 : Lemma4)
    (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (δ : ℝ) (hδ : 0 < δ)
    (hθ : songExponent γ + δ < 1) : SongWindow γ (songExponent γ + δ) := by
  obtain ⟨c, hc, hclower⟩ := singular_lower
  obtain ⟨C, N0, hAsym⟩ := asymptotic_with_margin591 H3 H4 γ hγ hγ1 δ hδ
  have hloglim : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp
    (hloglim.eventually_gt_atTop (C / (3 * c)))
  have hpowlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - (songExponent γ + δ)))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1 - (songExponent γ + δ))).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hpowlim.eventually_gt_atTop 3)
  refine ⟨max N0 (max N1 (max N2 2)), ?_⟩
  intro n ho hn y hy
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hsmall : (n : ℝ) ^ (songExponent γ + δ) < (n : ℝ) / 3 := by
    have hbig := hN2 n (by omega)
    have hpos := Real.rpow_pos_of_pos hn0 (songExponent γ + δ)
    have he : (n : ℝ) ^ (songExponent γ + δ) * (n : ℝ) ^ (1 - (songExponent γ + δ)) = n := by
      rw [← Real.rpow_add hn0]
      ring_nf
      simp
    nlinarith [mul_lt_mul_of_pos_left hbig hpos]
  let z : ℝ := min y ((n : ℝ) / 3)
  have hz : (n : ℝ) ^ (songExponent γ + δ) < z := lt_min hy hsmall
  have hz0 : 0 < z := (Real.rpow_pos_of_pos hn0 _).trans hz
  have herr := hAsym n ho (by omega) z hz.le (min_le_right _ _)
  have hs : c ≤ singular3 n := hclower n ho
  have hs0 : 0 < singular3 n := hc.trans_le hs
  have hm0 : 0 < mainTerm n z := by unfold mainTerm; positivity
  have hmargin : C < 3 * singular3 n * Real.log (n : ℝ) := by
    have hN := hN1 n (by omega)
    have hC : C < Real.log (n : ℝ) * (3 * c) := (div_lt_iff₀ (by positivity)).mp hN
    nlinarith
  have hfactor : mainTerm n z =
      (3 * singular3 n * Real.log (n : ℝ)) * (z ^ 2 / Real.log (n : ℝ) ^ 4) := by
    unfold mainTerm
    field_simp
  have hlt : C * (z ^ 2 / Real.log (n : ℝ) ^ 4) < mainTerm n z := by
    rw [hfactor]
    exact mul_lt_mul_of_pos_right hmargin (by positivity)
  have hRS : RS γ n z ≠ 0 := by
    intro hzero
    rw [hzero, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hm0] at herr
    exact (not_lt_of_ge herr) hlt
  exact isAlmostEqualPSTernary_mono (min_le_left _ _)
    (representation_of_RS_ne_zero139 γ n z hRS)

end LeanLab.Song2020.Repair591Margin
