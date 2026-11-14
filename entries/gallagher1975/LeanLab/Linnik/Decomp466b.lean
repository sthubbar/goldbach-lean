module

public import LeanLab.Linnik.Decomp466a

/-!
Gallagher 1975 P0094 p.138 before display 5.
Elementary estimates for the averaging proof.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik.Decomp466b

open Finset Filter MeasureTheory
open scoped Topology
open LeanLab.Linnik.Decomp1532a (pairs dif)
open LeanLab.Linnik.Decomp1532b (excSet)
open LeanLab.Linnik.Decomp466a

/-- Gallagher 1975 p.136 proof of Lemma 8 and p.138 before display 5.
A tuple difference has absolute value at most k N. -/
theorem difference_le {k N : ℕ} (hN : 1 ≤ N) (x : pairs k (Nat.log 2 N)) :
    (dif x).natAbs ≤ k * N := by
  have ha := LeanLab.Linnik.U1434Lemma21.sv_le x.1
  have hb := LeanLab.Linnik.U1434Lemma21.sv_le x.2
  have hp : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have ha' := ha.trans (Nat.mul_le_mul_left k hp)
  have hb' := hb.trans (Nat.mul_le_mul_left k hp)
  unfold dif
  omega

/-- Gallagher 1975 p.138 before display 5.
For fixed positive theta the divisor part is uniformly small on 1 at most m at most k N. -/
theorem divisor_error_small {k : ℕ} (hk : 1 ≤ k) {θ δ : ℝ}
    (hθ : 0 < θ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ m : ℕ, 1 ≤ m → m ≤ k * N →
      Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * m.divisors.card ≤ δ := by
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hθ
  let ε : ℝ := ((j + 1 : ℕ) : ℝ)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεθ : ε < θ := by simpa [ε, one_div] using hj
  obtain ⟨C, hC, hdiv⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow (j + 1) (by omega)
  have ht : Tendsto (fun N : ℕ =>
      (C * (k : ℝ) ^ ε * θ) * (Real.log N / (N : ℝ) ^ (θ - ε))) atTop (𝓝 0) := by
    simpa using ((isLittleO_log_rpow_atTop (sub_pos.mpr hεθ)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (C * (k : ℝ) ^ ε * θ)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨max 2 N₀, fun N hN m hm hmN => ?_⟩
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hp : 0 < (N : ℝ) ^ θ := Real.rpow_pos_of_pos hn _
  have hpow : (m : ℝ) ^ ε ≤ (k : ℝ) ^ ε * (N : ℝ) ^ ε := by
    rw [← Real.mul_rpow hk0.le hn.le]
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hε.le
    exact_mod_cast hmN
  have hbound : (m.divisors.card : ℝ) ≤ C * ((k : ℝ) ^ ε * (N : ℝ) ^ ε) :=
    (hdiv m hm).trans (mul_le_mul_of_nonneg_left hpow hC.le)
  calc
    _ ≤ (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ) *
        (C * ((k : ℝ) ^ ε * (N : ℝ) ^ ε)) := by
      apply mul_le_mul_of_nonneg_left hbound
      rw [Real.log_rpow hn]
      positivity
    _ = (C * (k : ℝ) ^ ε * θ) * (Real.log N / (N : ℝ) ^ (θ - ε)) := by
      rw [Real.log_rpow hn, Real.rpow_sub hn]
      field_simp
    _ ≤ δ := (hN₀ N (by omega)).le

/-- Gallagher 1975 p.127 exceptional conductor bound.
At T equal to P to the fifth the exceptional conductor escapes every fixed bound.
The conductor also has the real primitive shape of p.136 display 7. -/
theorem exceptional_conductor_escape :
    ∀ θ : ℝ, 0 < θ → ∀ R : ℕ, ∀ᶠ N : ℕ in atTop,
      ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
        R ≤ x.1 + 1 ∧ ∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧
          (x.1 + 1 = r₀ ∨ x.1 + 1 = 4 * r₀ ∨ x.1 + 1 = 8 * r₀) := by
  let bg := Classical.choose LeanLab.Linnik.Decomp1532b.exceptional_conductor_log_growth
  let br := Classical.choose LeanLab.Linnik.Decomp1532b.page_real
  let bu := Classical.choose LeanLab.Linnik.Decomp1532b.page_subsingleton
  have hg := (Classical.choose_spec LeanLab.Linnik.Decomp1532b.exceptional_conductor_log_growth).2
  have hr := (Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_real).2
  obtain ⟨a, ha, hgrow⟩ := hg 1 one_pos
  intro θ hθ R
  have hT : Tendsto (fun N : ℕ => ((N : ℝ) ^ θ) ^ 5) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0)).comp
      ((tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop)
  have hlarge : Tendsto (fun N : ℕ => a * Real.log (((N : ℝ) ^ θ) ^ 5)) atTop atTop :=
    (Real.tendsto_log_atTop.comp hT).const_mul_atTop ha
  filter_upwards [hT.eventually_ge_atTop 2, hlarge.eventually_ge_atTop (R : ℝ)] with N hT2 hR
  intro x hx
  change x ∈ excSet (min bg (min br bu)) (((N : ℝ) ^ θ) ^ 5) at hx
  have hxg := LeanLab.Linnik.Decomp1532b.excSet_mono (min_le_left bg (min br bu)) hT2 hx
  have hxr := LeanLab.Linnik.Decomp1532b.excSet_mono ((min_le_right bg (min br bu)).trans (min_le_left br bu)) hT2 hx
  have hbound := hgrow _ hT2 x hxg
  rw [Real.rpow_one] at hbound
  have hR' : (R : ℝ) ≤ (x.1 : ℝ) + 1 := hR.trans hbound
  refine ⟨by exact_mod_cast hR', ?_⟩
  exact LeanLab.Linnik.Decomp1532b.lemma9 (by omega) x.2 hx.2.1 (hr _ hT2 x hxr).1

/-- Gallagher 1975 p.136 display 8 and p.138 before display 5.
Above a fixed conductor threshold the exceptional weighted tuple sum is small. -/
theorem exceptional_average_small {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 2 ≤ R ∧ ∀ k N r : ℕ, 1 ≤ k → k ≤ N → R ≤ r → r ≤ N →
      (∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧ (r = r₀ ∨ r = 4 * r₀ ∨ r = 8 * r₀)) →
      (∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
        totientWeight (dif x) * exceptionalWeight r (dif x)) ≤
          δ * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  classical
  obtain ⟨C, hC⟩ := LeanLab.Linnik.Decomp1532b.lemma10
  have ht : Tendsto (fun r : ℕ => C / Real.log r ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, Function.comp_def] using
      (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
        (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))).inv_tendsto_atTop).const_mul C
  obtain ⟨R, hR⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨max 2 R, by omega, fun k N r hk hkN hr hrN hshape => ?_⟩
  have hb := hC k N r hk hkN (by omega) hrN hshape
  change (∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
    totientWeight (dif x) * exceptionalWeight r (dif x)) ≤ _ at hb
  calc
    _ ≤ C * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log r ^ (1 / 3 : ℝ) := hb
    _ = (C / Real.log r ^ (1 / 3 : ℝ)) * (Nat.log 2 N : ℝ) ^ (2 * k) := by ring
    _ ≤ δ * (Nat.log 2 N : ℝ) ^ (2 * k) :=
      mul_le_mul_of_nonneg_right (hR r (by omega)).le (by positivity)

end LeanLab.Linnik.Decomp466b
