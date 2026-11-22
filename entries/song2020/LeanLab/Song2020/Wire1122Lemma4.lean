module

public import LeanLab.Song2020.Audit1122FourierDQ

/-!
AI wrote the Lean code, Claude, 2026-11-22.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, printed pages 4 to 8, the proof of Lemma 4.
Wiring for the S2 step of Lemma 4, `fourier_approximation` in the lab file Decomp139, which is
not proved there: `Prep1121FourierS2` imports `Decomp139`, so `Decomp139` can never import the assembly
`fourier_approximation_of_leaves` without an import cycle. This new downstream file instead
reruns the page 8 assembly `Decomp139.song_lemma4_decomposed` with the S2 step taken as the
named hypothesis `Flag1734.FourierApproxDQ`, then discharges it by the proved
`Audit1122FourierDQ.fourierApproxDQ_of_leaves`, whose Prep1121FourierS2 leaves are proved.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.Wire1122Lemma4

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Song2020.Decomp139
open scoped Classical

noncomputable section

/-- Conditional on Flag1734.FourierApproxDQ, the S2 step of Song 2020 pages 4 and 5, as an argument;
the other Decomp139 inputs characteristic_reduction and optimized_truncated_bound are proved. Page 8, the
assembly of Lemma 4: the proof of `Decomp139.song_lemma4_decomposed` with the S2 step as an
argument in place of the lab step `fourier_approximation`. -/
theorem lemma4_of_fourierApproxDQ (hF : Flag1734.FourierApproxDQ) : Lemma4 := by
  intro γ hγ hγ1 ε hε
  obtain ⟨C₀, hC₀, N₀, hred⟩ := characteristic_reduction γ hγ hγ1
  obtain ⟨a, K, hK, ha, C₁, hC₁, N₁, happ⟩ := hF γ hγ hγ1
  obtain ⟨C₂, hC₂, N₂, hopt⟩ := optimized_truncated_bound γ hγ hγ1 ε hε
  refine ⟨C₀ + 20 * (max 1 C₁ * C₂ * K), max 1 (max N₀ (max N₁ N₂)), ?_⟩
  intro n hn y hy hyupper α
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hn0 _).trans hy
  have hyn : y ≤ (n : ℝ) := by linarith
  obtain ⟨H, hH, hbound⟩ := hopt K hK a ha n (by omega) y hy hyupper α
  have hred' := hred n (by omega) y hy hyupper α
  have happ' := happ n (by omega) y hy hyupper H hH α
  let T : ℝ := (n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * y ^ ((23 : ℝ) / 31)
  have hbase : (n : ℝ) ^ (3 / 2 - γ) ≤ T := by
    have h := monomial_le n y (songExponent γ) (3 / 2 - γ) 0
      (21 / 31 - 14 * γ / 31 + ε) (23 / 31) hnR hy.le hyn
      (by unfold songExponent; linarith) (by linarith)
    simpa [T] using h
  have hb : (n : ℝ) ^ ε * budget γ n y ≤ 20 * T := by
    have h := mul_le_mul_of_nonneg_left (budget_le γ n y hγ hγ1 hnR hy.le hyn)
      (Real.rpow_nonneg hn0.le ε)
    have he : (n : ℝ) ^ ε *
        (20 * ((n : ℝ) ^ (21 / 31 - 14 * γ / 31) * y ^ ((23 : ℝ) / 31))) = 20 * T := by
      dsimp [T]
      rw [show 21 / 31 - 14 * γ / 31 + ε = ε + (21 / 31 - 14 * γ / 31) by ring,
        Real.rpow_add hn0]
      ring
    exact h.trans_eq he
  have ht : 0 ≤ tailBudget γ n y H := by unfold tailBudget; positivity
  have hnorm := norm_nonneg (truncatedSum a H γ n y α)
  have hmax0 : 0 ≤ max 1 C₁ := le_trans (by norm_num) (le_max_left _ _)
  have htri : ‖fS γ n y α - gS n y α‖ ≤
      ‖fS γ n y α - gS n y α - sawSum γ n y α‖ +
      ‖sawSum γ n y α - truncatedSum a H γ n y α‖ + ‖truncatedSum a H γ n y α‖ := by
    calc
      _ = ‖(fS γ n y α - gS n y α - sawSum γ n y α) +
          (sawSum γ n y α - truncatedSum a H γ n y α) + truncatedSum a H γ n y α‖ := by
        congr 1
        ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hlin : ‖fS γ n y α - gS n y α‖ ≤ C₀ * (n : ℝ) ^ (3 / 2 - γ) +
      max 1 C₁ * (‖truncatedSum a H γ n y α‖ + tailBudget γ n y H) := by
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left 1 C₁) hnorm,
      mul_le_mul_of_nonneg_right (le_max_right 1 C₁) ht]
  calc
    ‖fS γ n y α - gS n y α‖ ≤ C₀ * (n : ℝ) ^ (3 / 2 - γ) +
        max 1 C₁ * (‖truncatedSum a H γ n y α‖ + tailBudget γ n y H) := hlin
    _ ≤ C₀ * T + max 1 C₁ * (C₂ * K * (n : ℝ) ^ ε * budget γ n y) :=
      add_le_add (mul_le_mul_of_nonneg_left hbase hC₀)
        (mul_le_mul_of_nonneg_left hbound hmax0)
    _ ≤ C₀ * T + (max 1 C₁ * C₂ * K) * (20 * T) := by
      have h := mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg hmax0 hC₂) (show 0 ≤ K by linarith))
      calc
        _ = C₀ * T + (max 1 C₁ * C₂ * K) * ((n : ℝ) ^ ε * budget γ n y) := by ring
        _ ≤ _ := add_le_add le_rfl h
    _ = (C₀ + 20 * (max 1 C₁ * C₂ * K)) * T := by ring

/-- Proved, axioms propext, Classical.choice, Quot.sound. Song 2020 Lemma 4, the exact
proposition, with the S2 step routed through the
proved Prep1121FourierS2 split instead of the lab step `fourier_approximation`. -/
theorem song_lemma4_of_leaves : Lemma4 :=
  lemma4_of_fourierApproxDQ Audit1122FourierDQ.fourierApproxDQ_of_leaves

end

end LeanLab.Song2020.Wire1122Lemma4
