module

public import LeanLab.LZCesaroShort.Lemma5

/-!
# The dyadic layer bound behind P0058 eq. (29) and (30)

Lab file, unit U-6104, CLOUD 20261020T0618Z-cloud36. AI wrote this file. No cited input.
Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 pp. 9 and 10: `∫ |T_H(N, H; α)| |R̃(α)|² dα` is split at `|α| = 2^k/H`.
Here the split is a pointwise inequality with nested windows, so no shells are needed:

* `dist0_eq_abs`: `‖α‖ = |α|` for `|α| ≤ 1/2`;
* `G_sq_layer`: for `|α| ≤ 1/2`, `1 ≤ H ≤ 2^K`, with `ξ_k = min(2^k/H, 1/2)`,
  `G(H, α)² ≤ Σ_{k ≤ K} (4H²/4^k) [|α| ≤ ξ_k]`;
* `integral_G_sq_le`: `∫_{-1/2}^{1/2} g(α) f(α) dα ≤ Σ_{k ≤ K} (4H²/4^k) ∫_{-ξ_k}^{ξ_k} f`
  for continuous `f ≥ 0` and continuous `g ≤ G(H, ·)²` on `[-1/2, 1/2]`.
-/

@[expose] public section


namespace LeanLab.LZCesaroShort

open Finset MeasureTheory Set
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Vinogradov

lemma dist0_eq_abs {α : ℝ} (h : |α| ≤ 1 / 2) : dist0 α = |α| := by
  unfold dist0
  rcases eq_or_lt_of_le (abs_le.mp h).2 with h2 | h2
  · subst h2; norm_num [round_eq]
  · have : round α = 0 := round_eq_zero_iff.mpr ⟨by linarith [(abs_le.mp h).1], h2⟩
    rw [this]; simp

/-- The window of level `k`. -/
noncomputable def xi (H : ℕ) (k : ℕ) : ℝ := min ((2 : ℝ) ^ k / H) (1 / 2)

lemma xi_le_half (H k : ℕ) : xi H k ≤ 1 / 2 := min_le_right _ _

lemma xi_nonneg (H k : ℕ) : 0 ≤ xi H k := le_min (by positivity) (by norm_num)

lemma xi_le (H k : ℕ) : xi H k ≤ (2 : ℝ) ^ k / H := min_le_left _ _

/-- **The pointwise layer bound.** -/
theorem G_sq_layer {H K : ℕ} (hH : 1 ≤ H) (hK : (H : ℝ) ≤ 2 ^ K) {α : ℝ} (hα : |α| ≤ 1 / 2) :
    G H α ^ 2 ≤ ∑ k ∈ range (K + 1),
      4 * (H : ℝ) ^ 2 / 4 ^ k * (Icc (-xi H k) (xi H k)).indicator (fun _ => (1 : ℝ)) α := by
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
      4 * (H : ℝ) ^ 2 / 4 ^ k * (Icc (-xi H k) (xi H k)).indicator (fun _ => (1 : ℝ)) α := by
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
    nlinarith
  · -- `|α| > ξ_{j-1} = 2^{j-1}/H`
    have hlt : ¬ |α| ≤ xi H (j - 1) := Nat.find_min hex (by omega)
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
    have h2 : G H α ^ 2 ≤ (H / 2 ^ j) ^ 2 := pow_le_pow_left₀ hG0 (hGle.trans h1) 2
    have h3 : ((H : ℝ) / 2 ^ j) ^ 2 = (H : ℝ) ^ 2 / 4 ^ j := by
      rw [div_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h3] at h2
    have : (H : ℝ) ^ 2 / 4 ^ j ≤ 4 * (H : ℝ) ^ 2 / 4 ^ j := by
      apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
    linarith

/-- The window integral as an indicator integral. -/
lemma integral_indicator_window {f : ℝ → ℝ} (hf : Continuous f) {ξ : ℝ} (h0 : 0 ≤ ξ)
    (h1 : ξ ≤ 1 / 2) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), (Icc (-ξ) ξ).indicator f α = ∫ α in (-ξ)..ξ, f α := by
  rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by linarith),
    setIntegral_indicator measurableSet_Icc]
  apply setIntegral_congr_set
  have e1 : Ioc (-(1 / 2 : ℝ)) (1 / 2) ∩ Icc (-ξ) ξ =ᵐ[volume] Icc (-(1 / 2 : ℝ)) (1 / 2) ∩ Icc (-ξ) ξ :=
    (Ioc_ae_eq_Icc).inter (Filter.EventuallyEq.refl _ _)
  have e2 : Icc (-(1 / 2 : ℝ)) (1 / 2) ∩ Icc (-ξ) ξ = Icc (-ξ) ξ := by
    rw [Icc_inter_Icc, max_eq_right (by linarith), min_eq_right h1]
  rw [e2] at e1
  exact e1.trans Ioc_ae_eq_Icc.symm

/-- **The layer bound for the integral.** -/
theorem integral_G_sq_le {H K : ℕ} (hH : 1 ≤ H) (hK : (H : ℝ) ≤ 2 ^ K) {f g : ℝ → ℝ}
    (hf : Continuous f) (hf0 : ∀ α, 0 ≤ f α) (hg : Continuous g)
    (hgG : ∀ α ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), g α ≤ G H α ^ 2) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), g α * f α
      ≤ ∑ k ∈ range (K + 1), 4 * (H : ℝ) ^ 2 / 4 ^ k * ∫ α in (-xi H k)..(xi H k), f α := by
  have hint : ∀ k, IntervalIntegrable (fun α => (Icc (-xi H k) (xi H k)).indicator f α) volume
      (-(1 / 2 : ℝ)) (1 / 2) := by
    intro k
    refine (hf.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2)).mono_fun
      ((hf.aestronglyMeasurable).indicator measurableSet_Icc) (Filter.Eventually.of_forall fun α => ?_)
    exact norm_indicator_le_norm_self _ _
  have hpt : ∀ α ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), g α * f α ≤
      ∑ k ∈ range (K + 1), 4 * (H : ℝ) ^ 2 / 4 ^ k * (Icc (-xi H k) (xi H k)).indicator f α := by
    intro α hα
    have hab : |α| ≤ 1 / 2 := abs_le.mpr ⟨hα.1, hα.2⟩
    have hl := mul_le_mul_of_nonneg_right ((hgG α hα).trans (G_sq_layer hH hK hab)) (hf0 α)
    refine hl.trans (le_of_eq ?_)
    rw [sum_mul]
    refine sum_congr rfl fun k _ => ?_
    unfold indicator; split_ifs <;> simp
  calc ∫ α in (-(1 / 2 : ℝ))..(1 / 2), g α * f α
      ≤ ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ∑ k ∈ range (K + 1),
          4 * (H : ℝ) ^ 2 / 4 ^ k * (Icc (-xi H k) (xi H k)).indicator f α :=
        intervalIntegral.integral_mono_on (by norm_num) ((hg.mul hf).intervalIntegrable _ _)
          (by
            have := IntervalIntegrable.sum (range (K + 1))
              (fun k _ => (hint k).const_mul (4 * (H : ℝ) ^ 2 / 4 ^ k))
            convert this using 1; ext α; simp [Finset.sum_apply]) hpt
    _ = ∑ k ∈ range (K + 1), 4 * (H : ℝ) ^ 2 / 4 ^ k *
          ∫ α in (-(1 / 2 : ℝ))..(1 / 2), (Icc (-xi H k) (xi H k)).indicator f α := by
        rw [intervalIntegral.integral_finset_sum fun k _ => (hint k).const_mul _]
        simp_rw [intervalIntegral.integral_const_mul]
    _ = _ := by
        refine sum_congr rfl fun k _ => ?_
        rw [integral_indicator_window hf (xi_nonneg H k) (xi_le_half H k)]

end LeanLab.LZCesaroShort

