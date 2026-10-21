module

public import LeanLab.PNTPort.ZetaZeros.Sym

/-!
# The Gaussian zero density `∑_ρ m(ρ) e^{-(t - Im ρ)²/2} ≪ log(|t| + 4)`

Lab proof, unit U-5859, CLOUD 20261020T0014Z-cloud30, T2 toward IDEAS I-5100. AI wrote this
file. Known mathematics, no cited input.

`gauss_zero_sum`: there is `C` such that for every real `t` and every finite set `S` of zeros of
`ζ` with `|Im ρ| ≥ 4`, counted with multiplicity `m(ρ)`,
`∑_{ρ ∈ S} m(ρ) e^{-(t - Im ρ)²/2} ≤ C log(|t| + 4)`.

This is the inner sum of `PNTPort.Gallagher.gauss_mean_value` when the frequencies are zeta
ordinates. Proof: put each zero in the window of width `4/5` around `t + 4k/5`, `k` the nearest
integer; the lab's `ZetaZeros.zero_count` bounds each window by `C₀ log |t + 4k/5|`; the Gaussian
weight is at most `e^{-2|k|/25}`; and `∑_k e^{-2|k|/25}(1 + |k|)` converges.
-/

@[expose] public section


namespace LeanLab.PNTPort.Gallagher

open Finset Real
open LeanLab.PNTPort.ZetaZeros

local notation "ζ" => riemannZeta

/-- `g n = e^{-2n/25} (1 + n)`. -/
noncomputable def gz (n : ℕ) : ℝ := Real.exp (-(2 / 25) * n) * (1 + n)

lemma gz_nonneg (n : ℕ) : 0 ≤ gz n := by unfold gz; positivity

lemma summable_gz : Summable gz := by
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 2 / 25)
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 2 / 25)
  refine (h0.add h1).congr fun n => ?_
  unfold gz; simp only [pow_zero, one_mul, pow_one]; ring

/-- A finite sum of `gz |k|` over integers is at most `2 ∑ gz`. -/
lemma sum_int_gz_le (K : Finset ℤ) : ∑ k ∈ K, gz k.natAbs ≤ 2 * ∑' n, gz n := by
  rw [← sum_filter_add_sum_filter_not K (fun k : ℤ => 0 ≤ k)]
  have hinj1 : Set.InjOn Int.natAbs (K.filter (fun k : ℤ => 0 ≤ k) : Set ℤ) := by
    intro a ha b hb hab
    simp only [coe_filter, Set.mem_setOf_eq] at ha hb
    omega
  have hinj2 : Set.InjOn Int.natAbs (K.filter (fun k : ℤ => ¬ 0 ≤ k) : Set ℤ) := by
    intro a ha b hb hab
    simp only [coe_filter, Set.mem_setOf_eq] at ha hb
    omega
  have h1 := sum_image (f := gz) hinj1
  have h2 := sum_image (f := gz) hinj2
  have b1 := summable_gz.sum_le_tsum ((K.filter (fun k : ℤ => 0 ≤ k)).image Int.natAbs)
    (fun n _ => gz_nonneg n)
  have b2 := summable_gz.sum_le_tsum ((K.filter (fun k : ℤ => ¬ 0 ≤ k)).image Int.natAbs)
    (fun n _ => gz_nonneg n)
  rw [h1] at b1; rw [h2] at b2
  linarith

/-- **The Gaussian zero density.** -/
theorem gauss_zero_sum : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (S : Finset ℂ),
    (∀ ρ ∈ S, ζ ρ = 0 ∧ 4 ≤ |ρ.im|) →
    ∑ ρ ∈ S, (analyticOrderNatAt ζ ρ : ℝ) * Real.exp (-(t - ρ.im) ^ 2 / 2)
      ≤ C * Real.log (|t| + 4) := by
  obtain ⟨C₀, hC₀, hZ⟩ := zero_count
  set B := ∑' n, gz n with hB
  have hB1 : 1 ≤ B := by
    have := summable_gz.sum_le_tsum {0} (fun n _ => gz_nonneg n)
    rw [sum_singleton] at this
    have h0 : gz 0 = 1 := by simp [gz]
    rw [h0] at this; exact this
  refine ⟨C₀ * (2 * B), by positivity, fun t S hS => ?_⟩
  set L := Real.log (|t| + 4) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 ≤ 4 := by
      have := Real.exp_one_lt_d9; linarith
    linarith [abs_nonneg t]
  -- the window index and centre
  set idx : ℂ → ℤ := fun ρ => round ((ρ.im - t) / (4 / 5)) with hidx
  set cen : ℤ → ℝ := fun k => t + 4 / 5 * k with hcen
  have hwin : ∀ ρ : ℂ, |ρ.im - cen (idx ρ)| ≤ 2 / 5 := by
    intro ρ
    have h := abs_sub_round ((ρ.im - t) / (4 / 5))
    have : ρ.im - cen (idx ρ) = 4 / 5 * ((ρ.im - t) / (4 / 5) - round ((ρ.im - t) / (4 / 5))) := by
      simp only [hcen, hidx]; field_simp; ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5)]
    linarith
  -- the Gaussian weight is at most `e^{-2|k|/25}`
  have hgauss : ∀ ρ : ℂ, Real.exp (-(t - ρ.im) ^ 2 / 2)
      ≤ Real.exp (-(2 / 25) * ((idx ρ).natAbs : ℝ)) := by
    intro ρ
    apply Real.exp_le_exp.mpr
    have hk : (((idx ρ).natAbs : ℕ) : ℝ) = |((idx ρ : ℤ) : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hk]
    have hw := hwin ρ
    simp only [hcen] at hw
    set k : ℝ := ((idx ρ : ℤ) : ℝ)
    rcases eq_or_ne (idx ρ) 0 with h0 | h0
    · have : k = 0 := by simp [k, h0]
      rw [this, abs_zero]; nlinarith [sq_nonneg (t - ρ.im)]
    · have hk1 : 1 ≤ |k| := by
        have : (1 : ℤ) ≤ |idx ρ| := Int.one_le_abs h0
        have : ((1 : ℤ) : ℝ) ≤ ((|idx ρ| : ℤ) : ℝ) := by exact_mod_cast this
        simpa [k, Int.cast_abs] using this
      -- `|t - Im ρ| ≥ 4|k|/5 - 2/5 ≥ 2|k|/5`
      have hd : 2 / 5 * |k| ≤ |t - ρ.im| := by
        have h1 : |4 / 5 * k| ≤ |t - ρ.im| + |ρ.im - (t + 4 / 5 * k)| := by
          calc |4 / 5 * k| = |(ρ.im - t) - (ρ.im - (t + 4 / 5 * k))| := by ring_nf
            _ ≤ |ρ.im - t| + |ρ.im - (t + 4 / 5 * k)| := abs_sub _ _
            _ = |t - ρ.im| + |ρ.im - (t + 4 / 5 * k)| := by rw [abs_sub_comm]
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5)] at h1
        linarith
      have hd2 : (2 / 5 * |k|) ^ 2 ≤ (t - ρ.im) ^ 2 := by
        rw [← sq_abs (t - ρ.im)]
        exact pow_le_pow_left₀ (by positivity) hd 2
      nlinarith
  -- group the zeros by window
  have hsplit := (sum_fiberwise_of_maps_to (s := S) (t := S.image idx) (g := idx)
    (fun ρ hρ => mem_image_of_mem idx hρ)
    (fun ρ => (analyticOrderNatAt ζ ρ : ℝ) * Real.exp (-(t - ρ.im) ^ 2 / 2))).symm
  rw [hsplit]
  -- each window
  have hfib : ∀ k ∈ S.image idx,
      ∑ ρ ∈ S.filter (fun ρ => idx ρ = k), (analyticOrderNatAt ζ ρ : ℝ) *
          Real.exp (-(t - ρ.im) ^ 2 / 2)
        ≤ C₀ * (L * gz k.natAbs) := by
    intro k hk
    obtain ⟨ρ₀, hρ₀S, hρ₀k⟩ := mem_image.mp hk
    -- the centre is at least `3` in absolute value
    have hc3 : 3 ≤ |cen k| := by
      have hw := hwin ρ₀
      rw [hρ₀k] at hw
      have := (hS ρ₀ hρ₀S).2
      have h' : |ρ₀.im| ≤ |cen k| + |ρ₀.im - cen k| := by
        calc |ρ₀.im| = |cen k + (ρ₀.im - cen k)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith
    obtain ⟨hfin, hcount⟩ := hZ (cen k) hc3
    have hsub : S.filter (fun ρ => idx ρ = k) ⊆ hfin.toFinset := by
      intro ρ hρ
      rw [mem_filter] at hρ
      rw [Set.Finite.mem_toFinset]
      refine ⟨(hS ρ hρ.1).1, ?_⟩
      have := hwin ρ; rw [hρ.2] at this; exact this
    have hlogc : Real.log |cen k| ≤ L + k.natAbs := by
      have hpos : 0 < |cen k| := by linarith
      have hkr : (k.natAbs : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      have hle : |cen k| ≤ (|t| + 4) * (1 + k.natAbs) := by
        simp only [hcen]
        rw [hkr]
        calc |t + 4 / 5 * (k : ℝ)| ≤ |t| + |4 / 5 * (k : ℝ)| := abs_add_le _ _
          _ = |t| + 4 / 5 * |(k : ℝ)| := by
              rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5)]
          _ ≤ (|t| + 4) * (1 + |(k : ℝ)|) := by nlinarith [abs_nonneg t, abs_nonneg (k : ℝ)]
      calc Real.log |cen k| ≤ Real.log ((|t| + 4) * (1 + k.natAbs)) :=
            Real.log_le_log hpos hle
        _ = L + Real.log (1 + k.natAbs) := by
            rw [Real.log_mul (by positivity) (by positivity)]
        _ ≤ L + k.natAbs := by
            have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + k.natAbs)
            linarith
    calc ∑ ρ ∈ S.filter (fun ρ => idx ρ = k), (analyticOrderNatAt ζ ρ : ℝ) *
            Real.exp (-(t - ρ.im) ^ 2 / 2)
        ≤ ∑ ρ ∈ S.filter (fun ρ => idx ρ = k), (analyticOrderNatAt ζ ρ : ℝ) *
            Real.exp (-(2 / 25) * (k.natAbs : ℝ)) := by
          refine sum_le_sum fun ρ hρ => ?_
          rw [mem_filter] at hρ
          have := hgauss ρ; rw [hρ.2] at this
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = (∑ ρ ∈ S.filter (fun ρ => idx ρ = k), (analyticOrderNatAt ζ ρ : ℝ)) *
            Real.exp (-(2 / 25) * (k.natAbs : ℝ)) := by rw [sum_mul]
      _ ≤ (C₀ * Real.log |cen k|) * Real.exp (-(2 / 25) * (k.natAbs : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          refine le_trans (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) hcount
      _ ≤ (C₀ * (L * (1 + k.natAbs))) * Real.exp (-(2 / 25) * (k.natAbs : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hC₀.le
          have : (k.natAbs : ℝ) ≤ L * k.natAbs :=
            le_mul_of_one_le_left (by positivity) hL1
          linarith
      _ = C₀ * (L * gz k.natAbs) := by unfold gz; ring
  calc ∑ k ∈ S.image idx, ∑ ρ ∈ S.filter (fun ρ => idx ρ = k),
        (analyticOrderNatAt ζ ρ : ℝ) * Real.exp (-(t - ρ.im) ^ 2 / 2)
      ≤ ∑ k ∈ S.image idx, C₀ * (L * gz k.natAbs) := sum_le_sum hfib
    _ = C₀ * L * ∑ k ∈ S.image idx, gz k.natAbs := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    _ ≤ C₀ * L * (2 * B) := by
        apply mul_le_mul_of_nonneg_left (sum_int_gz_le _) (by positivity)
    _ = C₀ * (2 * B) * L := by ring

end LeanLab.PNTPort.Gallagher

