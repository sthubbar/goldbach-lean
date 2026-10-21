module

public import LeanLab.LZCesaroShort.Layer

/-!
# The dyadic layer bound for `G(H, α)`, used for P0058 eq. (29)

Lab file, unit U-6110, CLOUD 20261020T0618Z-cloud36. AI wrote this file. No cited input.
Binary Goldbach is OPEN. As `Layer.lean`, with `G` in place of `G²`:

* `G_layer`: for `|α| ≤ 1/2` and `1 ≤ H ≤ 2^K`, `G(H, α) ≤ Σ_{k ≤ K} (2H/2^k) [|α| ≤ ξ_k]`;
* `integral_G_le`: `∫ g f ≤ Σ_{k ≤ K} c (2H/2^k) ∫_{-ξ_k}^{ξ_k} f` when `g ≤ c G(H, ·)`.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Finset MeasureTheory Set
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov

theorem G_layer {H K : ℕ} (hH : 1 ≤ H) (hK : (H : ℝ) ≤ 2 ^ K) {α : ℝ} (hα : |α| ≤ 1 / 2) :
    G H α ≤ ∑ k ∈ range (K + 1),
      2 * (H : ℝ) / 2 ^ k * (Icc (-xi H k) (xi H k)).indicator (fun _ => (1 : ℝ)) α := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hex : ∃ j, |α| ≤ xi H j := ⟨K, by
    unfold xi; rw [min_eq_right]; · exact hα
    rw [le_div_iff₀ hH0]; linarith⟩
  set j := Nat.find hex with hj
  have hjs : |α| ≤ xi H j := Nat.find_spec hex
  have hjK : j ≤ K := Nat.find_min' hex (by
    unfold xi; rw [min_eq_right]; · exact hα
    rw [le_div_iff₀ hH0]; linarith)
  have hnn : ∀ k ∈ range (K + 1), (0 : ℝ) ≤
      2 * (H : ℝ) / 2 ^ k * (Icc (-xi H k) (xi H k)).indicator (fun _ => (1 : ℝ)) α := by
    intro k _
    apply mul_nonneg (by positivity)
    unfold indicator; split_ifs <;> norm_num
  have hsingle := single_le_sum hnn (mem_range.mpr (Nat.lt_succ_of_le hjK))
  have hind : (Icc (-xi H j) (xi H j)).indicator (fun _ => (1 : ℝ)) α = 1 := by
    rw [indicator_of_mem]; exact ⟨by linarith [neg_abs_le α], le_trans (le_abs_self α) hjs⟩
  rw [hind, mul_one] at hsingle
  refine le_trans ?_ hsingle
  have hG0 : 0 ≤ G H α := G_nonneg (by positivity) α
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, pow_zero, div_one]
    have := G_le (H : ℝ) α
    linarith
  · have hlt : ¬ |α| ≤ xi H (j - 1) := Nat.find_min hex (by omega)
    push_neg at hlt
    have hxi : xi H (j - 1) = (2 : ℝ) ^ (j - 1) / H := by
      unfold xi; rw [min_eq_left]
      by_contra hc; push_neg at hc
      unfold xi at hlt; rw [min_eq_right hc.le] at hlt; linarith
    rw [hxi] at hlt
    have hapos : 0 < |α| := lt_of_le_of_lt (by positivity) hlt
    have hd : dist0 α = |α| := dist0_eq_abs hα
    have hGle : G H α ≤ 1 / (2 * |α|) := by rw [← hd]; exact G_le_inv (by rw [hd]; exact hapos)
    have h1 : 1 / (2 * |α|) ≤ H / 2 ^ j := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]
      rw [div_lt_iff₀ hH0] at hlt
      nlinarith
    have : (H : ℝ) / 2 ^ j ≤ 2 * (H : ℝ) / 2 ^ j := by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    linarith

theorem integral_G_le {H K : ℕ} (hH : 1 ≤ H) (hK : (H : ℝ) ≤ 2 ^ K) {f g : ℝ → ℝ}
    (hf : Continuous f) (hf0 : ∀ α, 0 ≤ f α) (hg : Continuous g)
    {c : ℝ} (hc : 0 ≤ c) (hgG : ∀ α ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), g α ≤ c * G H α) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), g α * f α
      ≤ ∑ k ∈ range (K + 1), c * (2 * (H : ℝ) / 2 ^ k) * ∫ α in (-xi H k)..(xi H k), f α := by
  have hint : ∀ k, IntervalIntegrable (fun α => (Icc (-xi H k) (xi H k)).indicator f α) volume
      (-(1 / 2 : ℝ)) (1 / 2) := by
    intro k
    refine (hf.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2)).mono_fun
      ((hf.aestronglyMeasurable).indicator measurableSet_Icc) (Filter.Eventually.of_forall fun α => ?_)
    exact norm_indicator_le_norm_self _ _
  have hpt : ∀ α ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), g α * f α ≤
      ∑ k ∈ range (K + 1), c * (2 * (H : ℝ) / 2 ^ k) * (Icc (-xi H k) (xi H k)).indicator f α := by
    intro α hα
    have hab : |α| ≤ 1 / 2 := abs_le.mpr ⟨hα.1, hα.2⟩
    have hl := mul_le_mul_of_nonneg_right ((hgG α hα).trans (mul_le_mul_of_nonneg_left (G_layer hH hK hab) hc)) (hf0 α)
    refine hl.trans (le_of_eq ?_)
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun k _ => ?_
    unfold indicator; split_ifs <;> simp
  calc ∫ α in (-(1 / 2 : ℝ))..(1 / 2), g α * f α
      ≤ ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ∑ k ∈ range (K + 1),
          c * (2 * (H : ℝ) / 2 ^ k) * (Icc (-xi H k) (xi H k)).indicator f α :=
        intervalIntegral.integral_mono_on (by norm_num) ((hg.mul hf).intervalIntegrable _ _)
          (by
            have := IntervalIntegrable.sum (range (K + 1))
              (fun k _ => (hint k).const_mul (c * (2 * (H : ℝ) / 2 ^ k)))
            convert this using 1; ext α; simp [Finset.sum_apply]) hpt
    _ = ∑ k ∈ range (K + 1), c * (2 * (H : ℝ) / 2 ^ k) *
          ∫ α in (-(1 / 2 : ℝ))..(1 / 2), (Icc (-xi H k) (xi H k)).indicator f α := by
        rw [intervalIntegral.integral_finset_sum fun k _ => (hint k).const_mul _]
        simp_rw [intervalIntegral.integral_const_mul]
    _ = _ := by
        refine sum_congr rfl fun k _ => ?_
        rw [integral_indicator_window hf (xi_nonneg H k) (xi_le_half H k)]

end LeanLab.LZCesaroShort

