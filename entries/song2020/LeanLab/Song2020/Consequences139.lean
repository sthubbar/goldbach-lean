module

public import LeanLab.Song2020.State1562

/-!
AI wrote the Lean code, Codex by OpenAI, 2026-10-27.
Elementary consequences of the Section 4 definitions.
Source: https://arxiv.org/abs/2012.06322, Section 4.
The source PDF was unreachable in this run. Page numbers remain unverified.
Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Song2020.State1562

open LeanLab.Song2020
open scoped Classical

noncomputable section

/-- Section 4. Orthogonality for three finite sums with natural frequencies. -/
theorem ternary_nat139 (s : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) :
    (∫ α in (0 : ℝ)..1, (∑ p ∈ s, a p * eC (α * p)) ^ 3 * eC (-(n * α))) =
      ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
        if p + q + r = n then a p * a q * a r else 0 := by
  have h := LeanLab.CircleOrth.ternary_orth
    (s.map (Nat.castEmbedding : ℕ ↪ ℤ)) (fun k => a k.toNat) n
  simp only [LeanLab.CircleOrth.S, Finset.sum_map, Nat.castEmbedding_apply,
    Int.toNat_natCast, Int.cast_natCast] at h
  have he (p q r : ℕ) : (p : ℤ) + (q : ℤ) + (r : ℤ) = (n : ℤ) ↔ p + q + r = n := by omega
  simp only [he] at h
  simpa [eC, LeanLab.CircleOrth.ee, mul_comm] using h

/-- Section 4. R is the finite weighted count of triples in its prime window. -/
theorem RS_eq_sum139 (γ : ℝ) (n : ℕ) (y : ℝ) :
    RS γ n y =
      ∑ p ∈ (windowPrimes n y).filter (fun p => IsPSPrime γ p),
      ∑ q ∈ (windowPrimes n y).filter (fun p => IsPSPrime γ p),
      ∑ r ∈ (windowPrimes n y).filter (fun p => IsPSPrime γ p),
        if p + q + r = n then
          (psWeight γ p : ℂ) * (psWeight γ q : ℂ) * (psWeight γ r : ℂ) else 0 := by
  exact ternary_nat139 ((windowPrimes n y).filter (fun p => IsPSPrime γ p))
    (fun p => (psWeight γ p : ℂ)) n

/-- Section 4. A nonzero weighted count gives the required prime representation. -/
theorem representation_of_RS_ne_zero139 (γ : ℝ) (n : ℕ) (y : ℝ)
    (h : RS γ n y ≠ 0) : IsAlmostEqualPSTernary γ n y := by
  rw [RS_eq_sum139] at h
  obtain ⟨p, hp, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨q, hq, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨r, hr, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have he : p + q + r = n := by
    by_contra he
    simp [he] at h
  have hpp := Finset.mem_filter.mp hp
  have hqp := Finset.mem_filter.mp hq
  have hrp := Finset.mem_filter.mp hr
  exact ⟨p, q, r, hpp.2, hqp.2, hrp.2, he,
    (Finset.mem_filter.mp hpp.1).2.2.le,
    (Finset.mem_filter.mp hqp.1).2.2.le,
    (Finset.mem_filter.mp hrp.1).2.2.le⟩


/-- Section 4. Conditional on Asymptotic, Theorem 1 follows. -/
theorem songTheorem1_of_asymptotic139 (H : Asymptotic) : SongTheorem1 := by
  obtain ⟨c, hc, hclower⟩ := singular_lower
  intro γ hγ hγ1
  obtain ⟨C, N₀, hAsym⟩ := H γ hγ hγ1
  have hloglim : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (hloglim.eventually_gt_atTop (C / (3 * c)))
  have hθ : songExponent γ < 1 := (songExponent_mem hγ hγ1).2
  have hpowlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - songExponent γ))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1 - songExponent γ)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hpowlim.eventually_gt_atTop 3)
  refine ⟨max N₀ (max N₁ (max N₂ 2)), fun n ho hn y hy => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hsmall : (n : ℝ) ^ songExponent γ < (n : ℝ) / 3 := by
    have hbig := hN₂ n (by omega)
    have hpos := Real.rpow_pos_of_pos hn0 (songExponent γ)
    have he : (n : ℝ) ^ songExponent γ * (n : ℝ) ^ (1 - songExponent γ) = n := by
      rw [← Real.rpow_add hn0, show songExponent γ + (1 - songExponent γ) = 1 by ring,
        Real.rpow_one]
    nlinarith [mul_lt_mul_of_pos_left hbig hpos]
  let z : ℝ := min y ((n : ℝ) / 3)
  have hz : (n : ℝ) ^ songExponent γ < z := lt_min hy hsmall
  have hz0 : 0 < z := (Real.rpow_pos_of_pos hn0 _).trans hz
  have herr := hAsym n ho (by omega) z hz (min_le_right _ _)
  have hs : c ≤ singular3 n := hclower n ho
  have hs0 : 0 < singular3 n := hc.trans_le hs
  have hm0 : 0 < mainTerm n z := by unfold mainTerm; positivity
  have hmargin : C < 3 * singular3 n * Real.log (n : ℝ) := by
    have hN := hN₁ n (by omega)
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

end

end LeanLab.Song2020.State1562
