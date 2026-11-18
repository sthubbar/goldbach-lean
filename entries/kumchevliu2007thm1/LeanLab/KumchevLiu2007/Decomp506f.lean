module

public import LeanLab.KumchevLiu2007.Decomp506e

/-!
The elementary bridge from rough representation pairs to the weighted sieve model.
The upper weights remain an explicit hypothesis. No analytic input is asserted.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section

namespace LeanLab.KumchevLiu2007.Task506f

open Real Task506b Task506c Task506d Task506e
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Page 16 display 56, rough composites in the square root window belong to the semiprime sequence. -/
theorem rough_pair_semiprime (X B ε : ℝ) (q : ℕ) (hY : 0 ≤ Y X ε)
    (hwindow : 4 ≤ Real.sqrt (Y X ε)) (hz : 1 < z0 X B ε)
    (hcube : Real.sqrt (Y X ε) < z0 X B ε ^ 3)
    (hqrange : q ∈ Finset.range (⌊Real.sqrt (Y X ε)⌋₊ + 1))
    (hqlo : Real.sqrt (Y X ε) / 2 ≤ (q : ℝ)) (hqhi : (q : ℝ) < Real.sqrt (Y X ε))
    (hnp : ¬ q.Prime) (hrough : ∀ p : ℕ, p.Prime → p ∣ q → z0 X B ε ≤ (p : ℝ)) :
    q ∈ semiprimes X B ε := by
  have hq1 : 1 < q := by exact_mod_cast (show (1 : ℝ) < q by linarith)
  obtain ⟨p, r, hp, hr, hpr, hqr, hzp, hpsq⟩ :=
    rough_composite_two_primes q (z0 X B ε) hz hq1 hnp hrough (hqhi.trans hcube)
  have hU0 : 0 ≤ Y X ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hY _
  have hU2 : (Y X ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (Y X ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY, Real.sqrt_eq_rpow]
    norm_num
  have hpsqR : (p : ℝ) ^ 2 ≤ (q : ℝ) := by exact_mod_cast hpsq
  have hpU : (p : ℝ) < Y X ε ^ (1 / 4 : ℝ) := by nlinarith
  have hpwindow : p ∈ primeWindow X B ε := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp, hzp, hpU⟩
    exact Nat.lt_succ_iff.mpr (Nat.le_floor hpU.le)
  exact Finset.mem_filter.mpr ⟨hqrange, hqlo, hqhi, p, hpwindow, r, hr, hpr, hqr⟩

/-- Page 16 display 56, the original sifted pair count is at most the weighted model sifted sum. -/
theorem siftedCount_le_model (X B δ ε : ℝ) (n : ℕ) (hn : InH2 n) (hY : 0 ≤ Y X ε)
    (hwindow : 4 ≤ Real.sqrt (Y X ε)) (hz : 1 < z0 X B ε)
    (hcube : Real.sqrt (Y X ε) < z0 X B ε ^ 3) :
    siftedCount X B δ ε n ≤ (sieveModel X B δ ε n hn).siftedSum := by
  rw [model_siftedSum]
  unfold siftedCount
  apply Nat.cast_le.mpr
  apply representation_pairs_le_window _ _ n
  · intro v hv
    obtain ⟨hvW, hmrough, hqnp, hqrough⟩ := Finset.mem_filter.mp hv
    obtain ⟨hvprod, hmlo, hmhi, hqlo, hqhi, hrep⟩ := Finset.mem_filter.mp hvW
    have hqrange := (Finset.mem_product.mp hvprod).2
    have hqsem := rough_pair_semiprime X B ε v.2 hY hwindow hz hcube hqrange hqlo hqhi hqnp hqrough
    refine Finset.mem_filter.mpr ⟨hqsem, ?_⟩
    have hm : n - v.2 ^ 2 = v.1 := by omega
    rw [hm]
    unfold primeProduct
    apply Nat.Coprime.prod_left
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2.1
    have hplt := (Finset.mem_filter.mp hp).2.2.1
    exact hpp.coprime_iff_not_dvd.mpr (fun hd => (not_lt_of_ge (hmrough p hpp hd)) hplt)
  · intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.2.2.2.2

/-- Page 16, large X makes the rough composite support reduction valid for every fixed positive B and epsilon. -/
theorem rough_support_parameters (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      0 ≤ Y X ε ∧ 4 ≤ Real.sqrt (Y X ε) ∧ 1 < z0 X B ε ∧
        Real.sqrt (Y X ε) < z0 X B ε ^ 3 := by
  let θ : ℝ := 7 / 12 + ε / 2
  let c : ℝ := θ / (48 * (B + 1))
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hs := Real.tendsto_log_atTop.eventually (Real.isLittleO_log_id_atTop.bound hc)
  filter_upwards [hs, Filter.eventually_ge_atTop (256 : ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with X hs hX hL1
  let L := Real.log X
  have hXp : 0 < X := by linarith
  have hL : 0 < L := by dsimp [L]; linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  change ‖Real.log L‖ ≤ c * ‖L‖ at hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogL, abs_of_pos hL] at hs
  have hs' : 48 * (B + 1) * Real.log L ≤ θ * L := by
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 48 * (B + 1) by positivity)
    have he : 48 * (B + 1) * (c * L) = θ * L := by
      dsimp [c]
      field_simp
      <;> ring
    rwa [he] at hh
  have hsmall : 6 * B * Real.log L ≤ θ * L / 8 := by nlinarith
  have hY : 0 < Y X ε := Real.rpow_pos_of_pos hXp _
  have hz : 0 < z0 X B ε := by unfold z0; positivity
  have hlogz : Real.log (z0 X B ε) = θ / 4 * L - 2 * B * Real.log L := by
    unfold z0
    rw [Real.log_mul (by positivity) (by positivity), Real.log_zpow,
      Real.log_rpow hY, Y, Real.log_rpow hXp, Real.log_rpow hL]
    dsimp [θ, L]
    norm_num
    ring
  have hlogsqrt : Real.log (Real.sqrt (Y X ε)) = θ / 2 * L := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hY, Y, Real.log_rpow hXp]
    dsimp [θ, L]
    ring
  have hcube : Real.sqrt (Y X ε) < z0 X B ε ^ 3 := by
    apply (Real.log_lt_log_iff (Real.sqrt_pos.mpr hY) (pow_pos hz 3)).mp
    rw [Real.log_pow, hlogz, hlogsqrt]
    have hθL : 0 < θ * L := mul_pos hθ hL
    nlinarith
  have hY16 : 16 ≤ Y X ε := by
    have hsqrt : (16 : ℝ) ≤ X ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (by linarith)
    exact hsqrt.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  have hroot : 4 ≤ Real.sqrt (Y X ε) := Real.le_sqrt_of_sq_le (by linarith)
  have hz1 : 1 < z0 X B ε := by
    by_contra hh
    have hzle : z0 X B ε ≤ 1 := by linarith
    have hp := pow_le_pow_left₀ hz.le hzle 3
    norm_num at hp
    linarith
  exact ⟨hY.le, hroot, hz1, hcube⟩

/-- Page 17 display 58, a pointwise conditional sieve bound from explicit upper weights.
The hypotheses name the remaining weight construction instead of asserting it. -/
theorem sifted_upper_of_weights (X B δ ε C : ℝ) (n : ℕ) (hn : InH2 n)
    (hY : 0 ≤ Y X ε) (hwindow : 4 ≤ Real.sqrt (Y X ε)) (hz : 1 < z0 X B ε)
    (hcube : Real.sqrt (Y X ε) < z0 X B ε ^ 3) (μ : ℕ → ℝ)
    (hupper : BoundingSieve.IsUpperMoebius μ)
    (hlevel : ∀ d ∈ (primeProduct X δ n).divisors,
      Y X ε ^ (1 / 9 : ℝ) < (d : ℝ) → μ d = 0)
    (hbound : ∀ d ∈ (primeProduct X δ n).divisors, |μ d| ≤ 1)
    (hmain : (sieveModel X B δ ε n hn).mainSum μ ≤ C * sieveProduct X δ n) :
    siftedCount X B δ ε n ≤ C * (primeMass X B ε * sieveProduct X δ n) + remainder X B ε n :=
  (siftedCount_le_model X B δ ε n hn hY hwindow hz hcube).trans
    (model_upper_of_weights X B δ ε C n hn μ hupper hlevel hbound hmain)

end LeanLab.KumchevLiu2007.Task506f
