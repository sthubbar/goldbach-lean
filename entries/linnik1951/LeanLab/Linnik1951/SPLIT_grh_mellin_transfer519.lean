module

public import LeanLab.Linnik1951.Decomp519a

/-!
Split of grh_mellin_transfer519 into three leaves. The transfer of a
nonprincipal character prime sum to a Mellin integral is cut into three
independent steps: the uniform bound for the logarithm of the L-function on the
vertical line under the zero hypothesis, the exact prime power expansion of the
difference between the character prime series and that Mellin integral, and the
size of the part of the expansion carrying exponents at least two. The assembly
at the end has no placeholder proof and does not use grh_mellin_transfer519.
AI wrote the Lean code. Binary Goldbach is open.
-/

@[expose] public section

namespace LeanLab.Linnik1951.Task519

open MeasureTheory Filter Finset

/-! ### Telescoping series with a shift -/

private lemma pp519_tel_shift (M : ℕ) (hM : 1 ≤ M) (K : ℕ) :
    ∑ k ∈ Finset.range K, ((1 : ℝ) / ((k : ℝ) + M) - 1 / ((k : ℝ) + M + 1))
      = 1 / (M : ℝ) - 1 / ((K : ℝ) + M) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : ((K : ℝ) + M) ≠ 0 := by
        have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
        positivity
      have h2 : ((K : ℝ) + M + 1) ≠ 0 := by
        have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
        positivity
      push_cast
      field_simp
      try ring

private lemma pp519_tel_nonneg (M : ℕ) (hM : 1 ≤ M) (k : ℕ) :
    0 ≤ (1 : ℝ) / ((k : ℝ) + M) - 1 / ((k : ℝ) + M + 1) := by
  have h1 : (0 : ℝ) < (k : ℝ) + M := by
    have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hle : (1 : ℝ) / ((k : ℝ) + M + 1) ≤ 1 / ((k : ℝ) + M) :=
    one_div_le_one_div_of_le h1 (by linarith)
  linarith

private lemma pp519_shift_tendsto (M : ℕ) :
    Tendsto (fun K : ℕ => (K : ℝ) + M) atTop atTop := by
  refine tendsto_atTop_mono (fun K => ?_) tendsto_natCast_atTop_atTop
  have h : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  linarith

private lemma pp519_tel_hasSum (M : ℕ) (hM : 1 ≤ M) :
    HasSum (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + M) - 1 / ((k : ℝ) + M + 1))
      (1 / (M : ℝ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (pp519_tel_nonneg M hM) (1 / (M : ℝ))]
  have hlim : Tendsto (fun K : ℕ => ((K : ℝ) + M)⁻¹) atTop (nhds 0) :=
    (pp519_shift_tendsto M).inv_tendsto_atTop
  have hlim2 : Tendsto (fun K : ℕ => (1 : ℝ) / ((K : ℝ) + M)) atTop (nhds 0) := by
    simpa only [one_div] using hlim
  have h0 : Tendsto (fun K : ℕ => (1 : ℝ) / (M : ℝ) - 1 / ((K : ℝ) + M)) atTop
      (nhds (1 / (M : ℝ) - 0)) := tendsto_const_nhds.sub hlim2
  simp only [sub_zero] at h0
  refine h0.congr' ?_
  filter_upwards with K
  exact (pp519_tel_shift M hM K).symm

/-! ### The tail of `1/n^2` -/

private lemma pp519_sq_term_le (k M : ℕ) (hM : 1 ≤ M) :
    (1 : ℝ) / ((k : ℝ) + M + 1) ^ 2
      ≤ (1 : ℝ) / ((k : ℝ) + M) - 1 / ((k : ℝ) + M + 1) := by
  set n : ℝ := (k : ℝ) + M + 1 with hn
  set m : ℝ := (k : ℝ) + M with hm
  have hm1 : n = m + 1 := by rw [hn, hm]
  have hm1' : (1 : ℝ) ≤ m := by
    rw [hm]
    have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hmp : (0 : ℝ) < m := by linarith
  have hnp : (0 : ℝ) < n := by rw [hm1]; linarith
  have hkey : (1 : ℝ) / (m * n) = 1 / m - 1 / n := by
    field_simp
    try rw [hm1]
    try ring
  rw [← hkey]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

private lemma pp519_tail_sq (M : ℕ) (hM : 1 ≤ M) :
    ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + M + 1) ^ 2 ≤ 1 / (M : ℝ) := by
  have hsum1 : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + M + 1) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => by positivity) (fun k => pp519_sq_term_le k M hM)
      (pp519_tel_hasSum M hM).summable
  calc ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + M + 1) ^ 2
      ≤ ∑' k : ℕ, ((1 : ℝ) / ((k : ℝ) + M) - 1 / ((k : ℝ) + M + 1)) :=
        hsum1.tsum_le_tsum (fun k => pp519_sq_term_le k M hM) (pp519_tel_hasSum M hM).summable
    _ = 1 / (M : ℝ) := (pp519_tel_hasSum M hM).tsum_eq

/-! ### The telescoping square-root series -/

private lemma pp519_sqrt_tel_shift (M : ℕ) (hM : 1 ≤ M) (K : ℕ) :
    ∑ k ∈ Finset.range K,
        ((1 : ℝ) / Real.sqrt ((k : ℝ) + M) - 1 / Real.sqrt ((k : ℝ) + M + 1))
      = 1 / Real.sqrt (M : ℝ) - 1 / Real.sqrt ((K : ℝ) + M) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private lemma pp519_sqrt_tel_nonneg (M : ℕ) (hM : 1 ≤ M) (k : ℕ) :
    0 ≤ (1 : ℝ) / Real.sqrt ((k : ℝ) + M) - 1 / Real.sqrt ((k : ℝ) + M + 1) := by
  have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : (0 : ℝ) < Real.sqrt ((k : ℝ) + M) := by
    apply Real.sqrt_pos.mpr; linarith
  have hlt : Real.sqrt ((k : ℝ) + M) < Real.sqrt ((k : ℝ) + M + 1) := by
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hle : (1 : ℝ) / Real.sqrt ((k : ℝ) + M + 1) ≤ 1 / Real.sqrt ((k : ℝ) + M) :=
    one_div_le_one_div_of_le h1 hlt.le
  linarith

private lemma pp519_sqrt_tel_hasSum (M : ℕ) (hM : 1 ≤ M) :
    HasSum (fun k : ℕ => (1 : ℝ) / Real.sqrt ((k : ℝ) + M)
        - 1 / Real.sqrt ((k : ℝ) + M + 1)) (1 / Real.sqrt (M : ℝ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (pp519_sqrt_tel_nonneg M hM) (1 / Real.sqrt (M : ℝ))]
  have hlim : Tendsto (fun K : ℕ => (Real.sqrt ((K : ℝ) + M))⁻¹) atTop (nhds 0) :=
    ((Real.tendsto_sqrt_atTop).comp (pp519_shift_tendsto M)).inv_tendsto_atTop
  have hlim2 : Tendsto (fun K : ℕ => (1 : ℝ) / Real.sqrt ((K : ℝ) + M)) atTop (nhds 0) := by
    simpa only [one_div] using hlim
  have h0 : Tendsto (fun K : ℕ => (1 : ℝ) / Real.sqrt (M : ℝ)
      - 1 / Real.sqrt ((K : ℝ) + M)) atTop (nhds (1 / Real.sqrt (M : ℝ) - 0)) :=
    tendsto_const_nhds.sub hlim2
  simp only [sub_zero] at h0
  refine h0.congr' ?_
  filter_upwards with K
  exact (pp519_sqrt_tel_shift M hM K).symm


/-! ### The termwise bound `1/(n √n) ≤ 2 (1/√(n-1) - 1/√n)` -/

private lemma pp519_cube_term_le (k M : ℕ) (hM : 1 ≤ M) :
    (1 : ℝ) / (((k : ℝ) + M + 1) * Real.sqrt ((k : ℝ) + M + 1))
      ≤ 2 * ((1 : ℝ) / Real.sqrt ((k : ℝ) + M)
        - 1 / Real.sqrt ((k : ℝ) + M + 1)) := by
  set n : ℝ := (k : ℝ) + M + 1 with hn
  set a : ℝ := Real.sqrt (n - 1) with ha_def
  set b : ℝ := Real.sqrt n with hb_def
  have hn2 : (2 : ℝ) ≤ n := by
    rw [hn]
    have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hn1 : (0 : ℝ) ≤ n - 1 := by linarith
  have ha2 : a ^ 2 = n - 1 := by rw [ha_def]; exact Real.sq_sqrt hn1
  have hb2 : b ^ 2 = n := by rw [hb_def]; exact Real.sq_sqrt hn0
  have ha : 0 < a := by rw [ha_def]; exact Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < b := by rw [hb_def]; exact Real.sqrt_pos.mpr (by linarith)
  have hna : Real.sqrt ((k : ℝ) + M) = a := by rw [ha_def, hn]; ring_nf
  have hnb : Real.sqrt ((k : ℝ) + M + 1) = b := by rw [hb_def, hn]
  have hnk : ((k : ℝ) + M + 1) = n := by rw [hn]
  -- main inequality on a, b
  have key : a * (1 + 2 * b ^ 2) ≤ 2 * b ^ 3 := by
    have hsq : (a * (1 + 2 * b ^ 2)) ^ 2 ≤ (2 * b ^ 3) ^ 2 := by
      have expand : (a * (1 + 2 * b ^ 2)) ^ 2 = (n - 1) * (1 + 2 * n) ^ 2 := by
        rw [mul_pow, ha2, hb2]
      have expand2 : (2 * b ^ 3) ^ 2 = 4 * n ^ 3 := by
        have h3 : b ^ 3 = n * b := by rw [show b ^ 3 = b ^ 2 * b by ring, hb2]
        rw [h3]
        nlinarith [hb2]
      rw [expand, expand2]
      nlinarith
    have h1 : (0 : ℝ) ≤ a * (1 + 2 * b ^ 2) := by positivity
    by_contra hcon
    push_neg at hcon
    have hb3pos : (0 : ℝ) ≤ 2 * b ^ 3 := by linarith [pow_pos hb 3]
    have := pow_lt_pow_left₀ hcon hb3pos (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  have hkey : (1 : ℝ) / a - 1 / b = (b - a) / (a * b) := by
    field_simp
  have hgoal : (1 : ℝ) / b ^ 3 ≤ 2 * ((b - a) / (a * b)) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < b ^ 3)]
    have e : 2 * ((b - a) / (a * b)) * b ^ 3 = 2 * b ^ 2 * (b - a) / a := by
      field_simp
    rw [e, le_div_iff₀ ha]
    nlinarith [key]
  have hb3 : (n : ℝ) * b = b ^ 3 := by
    have : b ^ 3 = b ^ 2 * b := by ring
    rw [this, hb2]
  have hmain : (1 : ℝ) / (n * b) ≤ 2 * ((b - a) / (a * b)) := by
    rw [hb3]
    exact hgoal
  calc (1 : ℝ) / (((k : ℝ) + M + 1) * Real.sqrt ((k : ℝ) + M + 1))
      = 1 / (n * b) := by rw [hnk, hnb]
    _ ≤ 2 * ((b - a) / (a * b)) := hmain
    _ = 2 * ((1 : ℝ) / Real.sqrt ((k : ℝ) + M)
        - 1 / Real.sqrt ((k : ℝ) + M + 1)) := by rw [hna, hnb, hkey]

private lemma pp519_tail_cube (M : ℕ) (hM : 1 ≤ M) :
    ∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + M + 1) * Real.sqrt ((k : ℝ) + M + 1))
      ≤ 2 / Real.sqrt (M : ℝ) := by
  have hbig : HasSum (fun k : ℕ => 2 * ((1 : ℝ) / Real.sqrt ((k : ℝ) + M)
      - 1 / Real.sqrt ((k : ℝ) + M + 1))) (2 * (1 / Real.sqrt (M : ℝ))) :=
    (pp519_sqrt_tel_hasSum M hM).mul_left 2
  have hsum1 : Summable (fun k : ℕ =>
      (1 : ℝ) / (((k : ℝ) + M + 1) * Real.sqrt ((k : ℝ) + M + 1))) :=
    Summable.of_nonneg_of_le (fun k => by positivity) (fun k => pp519_cube_term_le k M hM)
      hbig.summable
  calc ∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + M + 1) * Real.sqrt ((k : ℝ) + M + 1))
      ≤ ∑' k : ℕ, 2 * ((1 : ℝ) / Real.sqrt ((k : ℝ) + M)
          - 1 / Real.sqrt ((k : ℝ) + M + 1)) :=
        hsum1.tsum_le_tsum (fun k => pp519_cube_term_le k M hM) hbig.summable
    _ = 2 / Real.sqrt (M : ℝ) := by
        rw [hbig.tsum_eq]; ring


/-! ### The exponential is at most the minimum of one and the inverse -/

private lemma pp519_exp_le_min {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ min 1 x⁻¹ := by
  refine le_min ?_ ?_
  · rw [Real.exp_le_one_iff]; linarith
  · rw [Real.exp_neg, ← one_div]
    have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    simpa [one_div] using one_div_le_one_div_of_le hx h1

private lemma pp519_sqrt_pow_two (j : ℕ) :
    Real.sqrt ((2 : ℝ) ^ j) = (Real.sqrt 2) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

private lemma pp519_sqrt_geo (ξ : ℝ) (hξ : 0 < ξ) (j : ℕ) :
    Real.sqrt ((ξ * (2 : ℝ) ^ j)⁻¹) = (Real.sqrt ξ)⁻¹ * ((Real.sqrt 2)⁻¹) ^ j := by
  have hx : (0 : ℝ) ≤ ξ⁻¹ := le_of_lt (inv_pos.mpr hξ)
  rw [show (ξ * (2 : ℝ) ^ j)⁻¹ = ξ⁻¹ * ((2 : ℝ) ^ j)⁻¹ by rw [mul_inv],
    Real.sqrt_mul hx, Real.sqrt_inv, Real.sqrt_inv, pp519_sqrt_pow_two j, inv_pow]

private lemma pp519_min_one_le_sqrt {y : ℝ} (hy : 0 < y) : min 1 y ≤ Real.sqrt y := by
  rcases le_or_gt 1 y with h | h
  · rw [min_eq_left h]
    exact Real.one_le_sqrt.mpr h
  · rw [min_eq_right h.le]
    refine (Real.le_sqrt hy.le hy.le).mpr ?_
    nlinarith

private lemma pp519_geom (ξ : ℝ) (hξ : 0 < ξ) :
    ∑' j : ℕ, min 1 ((ξ * (2 : ℝ) ^ j)⁻¹) ≤ 7 / 2 / Real.sqrt ξ := by
  have hr0 : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
  have hr1 : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two
  have hterm : ∀ j : ℕ, min 1 ((ξ * (2 : ℝ) ^ j)⁻¹)
      ≤ (Real.sqrt ξ)⁻¹ * ((Real.sqrt 2)⁻¹) ^ j := by
    intro j
    have hy : (0 : ℝ) < (ξ * (2 : ℝ) ^ j)⁻¹ := by
      have h2 : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos (by norm_num) _
      exact inv_pos.mpr (mul_pos hξ h2)
    exact (pp519_min_one_le_sqrt hy).trans (le_of_eq (pp519_sqrt_geo ξ hξ j))
  have hsum : Summable (fun j : ℕ => (Real.sqrt ξ)⁻¹ * ((Real.sqrt 2)⁻¹) ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hsumL : Summable (fun j : ℕ => min 1 ((ξ * (2 : ℝ) ^ j)⁻¹)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hterm hsum
  have h70 : (7 : ℝ) / 5 ≤ Real.sqrt 2 := by
    refine (Real.le_sqrt (by norm_num) (by norm_num)).mpr ?_
    norm_num
  have hinv : (Real.sqrt 2)⁻¹ ≤ 5 / 7 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7 / 5) h70
    simpa [one_div] using h
  have hpos : (0 : ℝ) < 1 - (Real.sqrt 2)⁻¹ := by linarith
  have hle : (1 - (Real.sqrt 2)⁻¹)⁻¹ ≤ 7 / 2 := by
    have h2 : (0 : ℝ) < 2 / 7 := by norm_num
    have := (inv_le_inv₀ hpos h2).mpr (by linarith : (2 : ℝ) / 7 ≤ 1 - (Real.sqrt 2)⁻¹)
    simpa using this
  calc ∑' j : ℕ, min 1 ((ξ * (2 : ℝ) ^ j)⁻¹)
      ≤ ∑' j : ℕ, (Real.sqrt ξ)⁻¹ * ((Real.sqrt 2)⁻¹) ^ j := hsumL.tsum_le_tsum hterm hsum
    _ = (Real.sqrt ξ)⁻¹ * (1 - (Real.sqrt 2)⁻¹)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ ≤ 7 / 2 / Real.sqrt ξ := by
        have h0 : (0 : ℝ) ≤ (Real.sqrt ξ)⁻¹ := by positivity
        calc (Real.sqrt ξ)⁻¹ * (1 - (Real.sqrt 2)⁻¹)⁻¹
            ≤ (Real.sqrt ξ)⁻¹ * (7 / 2) := mul_le_mul_of_nonneg_left hle h0
          _ = 7 / 2 / Real.sqrt ξ := by
              rw [div_eq_mul_inv]
              ring

/-! ### Summability corollaries -/

private lemma pp519_summable_sq_shift :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 2) ^ 2)) :=
  Summable.of_nonneg_of_le (fun k => by positivity) (fun k => by
    simpa [Nat.cast_one, add_assoc, one_add_one_eq_two] using pp519_sq_term_le k 1 (by norm_num))
    (pp519_tel_hasSum 1 (by norm_num)).summable

private lemma pp519_summable_sq_tail (M : ℕ) (hM : 1 ≤ M) :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + M + 1) ^ 2)) :=
  Summable.of_nonneg_of_le (fun k => by positivity) (fun k => pp519_sq_term_le k M hM)
    (pp519_tel_hasSum M hM).summable

private lemma pp519_summable_cube_shift :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) :=
  Summable.of_nonneg_of_le (fun k => by positivity) (fun k => by
    simpa [Nat.cast_one, add_assoc, one_add_one_eq_two] using pp519_cube_term_le k 1 (by norm_num))
    ((pp519_sqrt_tel_hasSum 1 (by norm_num)).mul_left 2).summable

/-! ### The two scalar sums over `ℕ` -/

set_option maxHeartbeats 1000000 in
private lemma pp519_sum_one_aux (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hMn : (N : ℝ) ≤ ((M : ℝ)) ^ 2) (hMle : (M : ℝ) ≤ 2 * Real.sqrt (N : ℝ)) :
    ∑' m : ℕ, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)) ≤ 4 * Real.sqrt N := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsum : Summable (fun m : ℕ => min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))) := by
    refine Summable.of_nonneg_of_le (fun m => le_min zero_le_one (by positivity))
      (fun m => min_le_right _ _) ?_
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      (pp519_summable_sq_shift.mul_left (N : ℝ))
    rw [show (N : ℝ) * (1 / (((m : ℝ) + 2) ^ 2)) = (N : ℝ) / (((m : ℝ) + 2) ^ 2) by ring]
  have hsplit := (hsum.sum_add_tsum_nat_add M).symm
  have hhead : ∑ m ∈ Finset.range M, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)) ≤ (M : ℝ) := by
    have hle : ∀ m ∈ Finset.range M, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)) ≤ 1 :=
      fun m _ => min_le_left _ _
    calc ∑ m ∈ Finset.range M, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))
        ≤ ∑ _m ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum hle
      _ = (M : ℝ) := by simp
  have hshift : ∀ k : ℕ, (((k + M : ℕ) : ℝ) + 2) = ((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) := by
    intro k; push_cast; ring
  have htail : ∑' k : ℕ, min 1 ((N : ℝ) / ((((k + M : ℕ) : ℝ) + 2) ^ 2))
      ≤ (N : ℝ) * (1 / ((M : ℝ) + 1)) := by
    have hmaj : ∀ k : ℕ, min 1 ((N : ℝ) / ((((k + M : ℕ) : ℝ) + 2) ^ 2))
        ≤ (N : ℝ) * (1 / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2)) := by
      intro k
      rw [hshift k]
      calc min 1 ((N : ℝ) / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2))
          ≤ (N : ℝ) / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2) := min_le_right _ _
        _ = (N : ℝ) * (1 / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2)) := by ring
    have hs : Summable (fun k : ℕ => (N : ℝ) * (1 / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2))) :=
      (pp519_summable_sq_tail (M + 1) (by omega)).mul_left (N : ℝ)
    have hs' : Summable (fun k : ℕ => min 1 ((N : ℝ) / ((((k + M : ℕ) : ℝ) + 2) ^ 2))) :=
      Summable.of_nonneg_of_le (fun k => le_min zero_le_one (by positivity)) hmaj hs
    calc ∑' k : ℕ, min 1 ((N : ℝ) / ((((k + M : ℕ) : ℝ) + 2) ^ 2))
        ≤ ∑' k : ℕ, (N : ℝ) * (1 / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2)) :=
          hs'.tsum_le_tsum hmaj hs
      _ = (N : ℝ) * (∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + ((M + 1 : ℕ) : ℝ) + 1) ^ 2)) := by
          rw [tsum_mul_left]
      _ ≤ (N : ℝ) * (1 / ((M : ℝ) + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hNpos)
          have h := pp519_tail_sq (M + 1) (by omega)
          have hcast : (((M + 1 : ℕ)) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
          rw [hcast] at h
          simpa [Nat.cast_add, Nat.cast_one] using h
  have hNM : (N : ℝ) * (1 / ((M : ℝ) + 1)) ≤ (M : ℝ) := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [hMn, hMpos]
  calc ∑' m : ℕ, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))
      = ∑ m ∈ Finset.range M, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))
        + ∑' k : ℕ, min 1 ((N : ℝ) / ((((k + M : ℕ) : ℝ) + 2) ^ 2)) := hsplit
    _ ≤ (M : ℝ) + (M : ℝ) := by linarith
    _ ≤ 4 * Real.sqrt (N : ℝ) := by linarith

private lemma pp519_sum_one (N : ℕ) (hN : 1 ≤ N) :
    ∑' m : ℕ, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)) ≤ 4 * Real.sqrt N := by
  have hM1 : 1 ≤ Nat.sqrt N + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hMn : (N : ℝ) ≤ (((Nat.sqrt N + 1 : ℕ)) : ℝ) ^ 2 := by
    have h2 : ((N : ℕ) : ℝ) ≤ (((Nat.sqrt N + 1) ^ 2 : ℕ) : ℝ) :=
      by exact_mod_cast Nat.le_of_lt (Nat.lt_succ_sqrt' N)
    simpa using h2
  have hsqr : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have h : (((Nat.sqrt N : ℕ) : ℝ)) ^ 2 ≤ (N : ℝ) := by exact_mod_cast Nat.sqrt_le' N
    have h' := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (by positivity)] at h'
  have hMle : (((Nat.sqrt N + 1 : ℕ)) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hN)
    have h2 : (((Nat.sqrt N + 1 : ℕ)) : ℝ) = ((Nat.sqrt N : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [h2]; linarith
  exact pp519_sum_one_aux N (Nat.sqrt N + 1) hN hM1 hMn hMle

set_option maxHeartbeats 1000000 in
private lemma pp519_sum_two (N : ℕ) (hN : 1 ≤ N) :
    ∑' m : ℕ, Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3)) ≤ 2 * Real.sqrt N := by
  have hcongr : (∑' m : ℕ, Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3)))
      = Real.sqrt (N : ℝ) *
        ∑' m : ℕ, (1 : ℝ) / (((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2)) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    have hx : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have h3 : ((m : ℝ) + 2) ^ 3 = ((m : ℝ) + 2) ^ 2 * ((m : ℝ) + 2) := by ring
    rw [Real.sqrt_div (by positivity), h3, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hx.le]
    field_simp
  have h2 : (∑' m : ℕ, (1 : ℝ) / (((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2))) ≤ 2 := by
    have h := pp519_tail_cube 1 (by norm_num)
    simpa [Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  rw [hcongr]
  calc Real.sqrt (N : ℝ) * (∑' m : ℕ, (1 : ℝ) / (((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2)))
      ≤ Real.sqrt (N : ℝ) * 2 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt N := by ring

/-! ### The norm of a single prime power term -/

private lemma pp519_inv_cast_norm (k : ℕ) : ‖((k : ℂ) + 2)⁻¹‖ = ((k : ℝ) + 2)⁻¹ := by
  have hk : ((k : ℂ) + 2) = ((k + 2 : ℕ) : ℂ) := by push_cast; ring
  have hn : ‖(k : ℂ) + 2‖ = (k : ℝ) + 2 := by
    rw [hk, Complex.norm_natCast]
    push_cast
    ring
  rw [norm_inv, hn]

private lemma pp519_term_norm (N : ℕ) (hN : 1 ≤ N) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (α : ℝ) (p : Nat.Primes) (k : ℕ) :
    ‖((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
        (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)‖
      ≤ ((k : ℝ) + 2)⁻¹ * Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) := by
  have hexp : ‖Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)‖
      = 1 := Complex.norm_exp_ofReal_mul_I _
  have hchi : ‖χ ((p : ℕ) ^ (k + 2))‖ ≤ 1 := χ.norm_le_one _
  have hreal : ‖(Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ)‖
      = Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hpos : (0 : ℝ) < Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) := Real.exp_pos _
  have hchip : ((k : ℝ) + 2)⁻¹ * ‖χ ((p : ℕ) ^ (k + 2))‖ ≤ ((k : ℝ) + 2)⁻¹ := by
    have h0 : (0 : ℝ) ≤ ((k : ℝ) + 2)⁻¹ := by positivity
    calc ((k : ℝ) + 2)⁻¹ * ‖χ ((p : ℕ) ^ (k + 2))‖ ≤ ((k : ℝ) + 2)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hchi h0
      _ = ((k : ℝ) + 2)⁻¹ := mul_one _
  calc ‖((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
        (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)‖
      = ‖((k : ℂ) + 2)⁻¹‖ * ‖χ ((p : ℕ) ^ (k + 2))‖ *
          ‖(Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ)‖ *
            ‖Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)‖ := by
        rw [norm_mul, norm_mul, norm_mul]
    _ = ((k : ℝ) + 2)⁻¹ * ‖χ ((p : ℕ) ^ (k + 2))‖ *
          Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) * 1 := by
        rw [pp519_inv_cast_norm, hreal, hexp]
    _ = ((k : ℝ) + 2)⁻¹ * ‖χ ((p : ℕ) ^ (k + 2))‖ *
          Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) := by rw [mul_one]
    _ ≤ ((k : ℝ) + 2)⁻¹ * Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hchip (le_of_lt hpos)

/-! ### The bound for one prime -/

set_option maxHeartbeats 1000000 in
private lemma pp519_inner (N : ℕ) (hN : 1 ≤ N) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (α : ℝ) (p : Nat.Primes) :
    ‖∑' k : ℕ, (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
        (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
      ≤ 1 / 2 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
        + 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3)) := by
  let g : ℕ → ℂ := fun k => ((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
        (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I)
  change ‖∑' k : ℕ, g k‖ ≤ 1 / 2 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
        + 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hP0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hkey : ∀ k : ℕ, ‖g k‖ ≤ ((k : ℝ) + 2)⁻¹ * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2))) := by
    intro k
    have h := pp519_term_norm N hN q χ α p k
    have hPk : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (k + 2) := pow_pos hP0 _
    have hpos : (0 : ℝ) < (((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ)) := div_pos hPk hN0
    have h2 := pp519_exp_le_min hpos
    have heq : ((((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ)))⁻¹
        = (N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)) := by rw [inv_div]
    rw [heq] at h2
    exact h.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hgeo : Summable (fun k : ℕ => ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)) *
      ((((p : ℕ) : ℝ)⁻¹)) ^ k) := by
    have hr0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ)⁻¹ := by positivity
    have hr1 : ((p : ℕ) : ℝ)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      right
      linarith
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hmaj : ∀ k : ℕ, ((k : ℝ) + 2)⁻¹ * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)))
      ≤ ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)) * ((((p : ℕ) : ℝ)⁻¹)) ^ k := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by linarith
    have hPk : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (k + 2) := pow_pos hP0 _
    have hX : (0 : ℝ) < (N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)) := div_pos hN0 hPk
    have h1 : ((k : ℝ) + 2)⁻¹ ≤ 1 := by
      have hge : (1 : ℝ) ≤ (k : ℝ) + 2 := by linarith
      calc ((k : ℝ) + 2)⁻¹ ≤ (1 : ℝ)⁻¹ :=
            (inv_le_inv₀ hk2 (by norm_num : (0 : ℝ) < 1)).mpr hge
        _ = 1 := inv_one
    have h2 : min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)))
        ≤ (N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)) := min_le_right _ _
    have h3 : (N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2))
        = ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)) * ((((p : ℕ) : ℝ)⁻¹)) ^ k := by
      rw [inv_pow]
      field_simp
      ring
    have hstep1 : ((k : ℝ) + 2)⁻¹ * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)))
        ≤ ((k : ℝ) + 2)⁻¹ * ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2))) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have hstep2 : ((k : ℝ) + 2)⁻¹ * ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2)))
        ≤ 1 * ((N : ℝ) / (((p : ℕ) : ℝ) ^ (k + 2))) := by
      rw [one_mul]
      exact mul_le_of_le_one_left (le_of_lt hX) h1
    exact hstep1.trans (hstep2.trans (le_of_eq (by rw [one_mul, h3])))
  have hsum : Summable (fun k : ℕ => ‖g k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => (hkey k).trans (hmaj k)) hgeo
  have hsplit := (hsum.sum_add_tsum_nat_add 1).symm
  rw [Finset.sum_range_one] at hsplit
  have hk0 : ‖g 0‖ ≤ 1 / 2 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)) := by
    have h := hkey 0
    simpa using h
  have hcube : Summable (fun i : ℕ => min 1 ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹) := by
    have hxi : (0 : ℝ) < (((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) := by
      have h3 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 3 := pow_pos hP0 _
      exact div_pos h3 hN0
    have hr0 : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
    have hr1 : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_sqrt_two
    have hsumgeo : Summable (fun i : ℕ => (Real.sqrt ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ))))⁻¹
        * ((Real.sqrt 2)⁻¹) ^ i) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hsumgeo
    have hy : (0 : ℝ) < ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ := by
      have h2i : (0 : ℝ) < (2 : ℝ) ^ i := pow_pos (by norm_num) _
      exact inv_pos.mpr (mul_pos hxi h2i)
    exact (pp519_min_one_le_sqrt hy).trans (le_of_eq (pp519_sqrt_geo _ hxi i))
  have htail : ∑' i : ℕ, ‖g (i + 1)‖ ≤ 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3)) := by
    have hmaj2 : ∀ i : ℕ, ‖g (i + 1)‖ ≤ min 1 ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ := by
      intro i
      refine (hkey (i + 1)).trans ?_
      have h1 : (((i + 1 : ℕ)) : ℝ) + 2 = (i : ℝ) + 3 := by push_cast; ring
      have hexp : (i + 1) + 2 = i + 3 := by omega
      rw [h1, hexp]
      have hfac : ((i : ℝ) + 3)⁻¹ ≤ 1 := by
        have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        have hi3 : (0 : ℝ) < (i : ℝ) + 3 := by linarith
        have hge : (1 : ℝ) ≤ (i : ℝ) + 3 := by linarith
        calc ((i : ℝ) + 3)⁻¹ ≤ (1 : ℝ)⁻¹ :=
              (inv_le_inv₀ hi3 (by norm_num : (0 : ℝ) < 1)).mpr hge
          _ = 1 := inv_one
      have hP3 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 3 := pow_pos hP0 _
      have h2i : (0 : ℝ) < (2 : ℝ) ^ i := pow_pos (by norm_num) _
      have hPi : (2 : ℝ) ^ i ≤ ((p : ℕ) : ℝ) ^ i :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp2 i
      have hden : ((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i ≤ ((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i :=
        mul_le_mul_of_nonneg_left hPi (le_of_lt hP3)
      have hstep : (N : ℝ) / (((p : ℕ) : ℝ) ^ (i + 3))
          ≤ ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ := by
        have hpos1 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i := mul_pos hP3 h2i
        have hpos2 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i :=
          mul_pos hP3 (pow_pos hP0 i)
        have hinv : (((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i)⁻¹
            ≤ (((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i)⁻¹ :=
          (inv_le_inv₀ hpos2 hpos1).mpr hden
        have hle : (N : ℝ) / (((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i)
            ≤ (N : ℝ) / (((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i) := by
          calc (N : ℝ) / (((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i)
              = (N : ℝ) * ((((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i))⁻¹ := by
                rw [div_eq_mul_inv]
            _ ≤ (N : ℝ) * ((((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i))⁻¹ :=
                mul_le_mul_of_nonneg_left hinv (le_of_lt hN0)
            _ = (N : ℝ) / (((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i) := by
                rw [div_eq_mul_inv]
        have e1 : ((p : ℕ) : ℝ) ^ (i + 3) = ((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ i := by
          rw [pow_add, mul_comm]
        have e2 : ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹
            = (N : ℝ) / (((p : ℕ) : ℝ) ^ 3 * (2 : ℝ) ^ i) := by
          rw [mul_inv]
          field_simp
        rw [e1, e2]
        exact hle
      have hmin : min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ ((i + 1) + 2)))
          ≤ min 1 ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ := by
        rw [show (i + 1) + 2 = i + 3 by omega]
        exact min_le_min_left 1 hstep
      have hstep1 : ((i : ℝ) + 3)⁻¹ * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ ((i + 1) + 2)))
          ≤ 1 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ ((i + 1) + 2))) := by
        rw [one_mul]
        have hNk : (0 : ℝ) ≤ (N : ℝ) / (((p : ℕ) : ℝ) ^ ((i + 1) + 2)) := by
          have h3 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ ((i + 1) + 2) := pow_pos hP0 _
          exact le_of_lt (div_pos hN0 h3)
        exact mul_le_of_le_one_left (le_min (by norm_num : (0 : ℝ) ≤ 1) hNk) hfac
      have hstep2 : 1 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ ((i + 1) + 2)))
          ≤ min 1 ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ := by
        rw [one_mul]
        exact hmin
      exact hstep1.trans hstep2
    have hs1 : Summable (fun i : ℕ => ‖g (i + 1)‖) :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) hmaj2 hcube
    calc ∑' i : ℕ, ‖g (i + 1)‖
        ≤ ∑' i : ℕ, min 1 ((((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) * (2 : ℝ) ^ i)⁻¹ :=
          hs1.tsum_le_tsum hmaj2 hcube
      _ ≤ 7 / 2 / Real.sqrt (((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) := by
          have hxi : (0 : ℝ) < (((p : ℕ) : ℝ) ^ 3 / (N : ℝ)) := by
            have h3 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 3 := pow_pos hP0 _
            exact div_pos h3 hN0
          exact pp519_geom _ hxi
      _ = 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3)) := by
          rw [div_eq_mul_inv]
          congr 1
          rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity), inv_div]
  have hnn : ‖∑' k : ℕ, g k‖ ≤ ∑' k : ℕ, ‖g k‖ := norm_tsum_le_tsum_norm hsum
  have hfin : ∑' k : ℕ, ‖g k‖ = ‖g 0‖ + ∑' i : ℕ, ‖g (i + 1)‖ := hsplit
  linarith [hnn, hk0, htail]

/-! ### Square root of a quotient cube -/

private lemma pp519_sqrt_div_eq (N : ℕ) (m : ℕ) :
    Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3))
      = Real.sqrt (N : ℝ) * ((1 : ℝ) / (((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2))) := by
  have hx : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have h3 : ((m : ℝ) + 2) ^ 3 = ((m : ℝ) + 2) ^ 2 * ((m : ℝ) + 2) := by ring
  rw [Real.sqrt_div (by positivity), h3, Real.sqrt_mul (by positivity), Real.sqrt_sq hx.le]
  field_simp

/-! ### Summability of the two scalar families -/

private lemma pp519_summable_min (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun m : ℕ => min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => min_le_right _ _) ?_
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    (pp519_summable_sq_shift.mul_left (N : ℝ))
  rw [show (N : ℝ) * (1 / (((m : ℝ) + 2) ^ 2)) = (N : ℝ) / (((m : ℝ) + 2) ^ 2) by ring]

private lemma pp519_summable_sqrtN (N : ℕ) :
    Summable (fun m : ℕ => Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3))) := by
  refine Summable.of_nonneg_of_le (fun m => Real.sqrt_nonneg _) (fun m => ?_)
    (pp519_summable_cube_shift.mul_left (Real.sqrt (N : ℝ)))
  rw [pp519_sqrt_div_eq N m]

/-! ### From primes to natural numbers -/

private lemma pp519_prime_shift_inj :
    Function.Injective (fun p : Nat.Primes => (p : ℕ) - 2) := by
  intro p q h
  have hp : ((p : ℕ) - 2) + 2 = (p : ℕ) := Nat.sub_add_cancel p.prop.two_le
  have hq : ((q : ℕ) - 2) + 2 = (q : ℕ) := Nat.sub_add_cancel q.prop.two_le
  have h' : ((p : ℕ) - 2) = ((q : ℕ) - 2) := h
  have h2 : (p : ℕ) = (q : ℕ) := by
    calc (p : ℕ) = ((p : ℕ) - 2) + 2 := hp.symm
      _ = ((q : ℕ) - 2) + 2 := by rw [h']
      _ = (q : ℕ) := hq
  exact Nat.Primes.coe_nat_injective h2

private lemma pp519_shift_cast (p : Nat.Primes) :
    (((p : ℕ) - 2 : ℕ) : ℝ) + 2 = ((p : ℕ) : ℝ) := by
  have hp : 2 ≤ (p : ℕ) := p.prop.two_le
  have h : ((p : ℕ) - 2 : ℕ) + 2 = (p : ℕ) := Nat.sub_add_cancel hp
  calc (((p : ℕ) - 2 : ℕ) : ℝ) + 2 = (((((p : ℕ) - 2 : ℕ)) + 2 : ℕ) : ℝ) := by push_cast; ring
    _ = ((p : ℕ) : ℝ) := by rw [h]

private lemma pp519_prime_le_one (N : ℕ) (hN : 1 ≤ N) :
    ∑' p : Nat.Primes, min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
      ≤ ∑' m : ℕ, min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)) := by
  have hcongr : (∑' p : Nat.Primes, min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)))
      = ∑' p : Nat.Primes, (fun m : ℕ => min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)))
          ((p : ℕ) - 2) := by
    refine tsum_congr (fun p : Nat.Primes => ?_)
    show min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
      = min 1 ((N : ℝ) / (((((p : ℕ) - 2 : ℕ) : ℝ)) + 2) ^ 2)
    rw [pp519_shift_cast p]
  rw [hcongr]
  exact tsum_comp_le_tsum_of_inj (pp519_summable_min N hN) (fun m => by positivity)
    pp519_prime_shift_inj

private lemma pp519_prime_le_two (N : ℕ) :
    ∑' p : Nat.Primes, Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))
      ≤ ∑' m : ℕ, Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3)) := by
  have hcongr : (∑' p : Nat.Primes, Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3)))
      = ∑' p : Nat.Primes, (fun m : ℕ => Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3)))
          ((p : ℕ) - 2) := by
    refine tsum_congr (fun p : Nat.Primes => ?_)
    show Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))
      = Real.sqrt ((N : ℝ) / (((((p : ℕ) - 2 : ℕ) : ℝ)) + 2) ^ 3)
    rw [pp519_shift_cast p]
  rw [hcongr]
  exact tsum_comp_le_tsum_of_inj (pp519_summable_sqrtN N) (fun m => Real.sqrt_nonneg _)
    pp519_prime_shift_inj

private lemma pp519_summable_prime_one (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun p : Nat.Primes => min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))) := by
  have h0 : Summable ((fun m : ℕ => min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2)))
      ∘ (fun p : Nat.Primes => (p : ℕ) - 2)) :=
    (pp519_summable_min N hN).comp_injective pp519_prime_shift_inj
  exact h0.congr (fun p => by
    show min 1 ((N : ℝ) / (((((p : ℕ) - 2 : ℕ) : ℝ)) + 2) ^ 2)
      = min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
    rw [pp519_shift_cast p])

private lemma pp519_summable_prime_two (N : ℕ) :
    Summable (fun p : Nat.Primes => Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))) := by
  have h0 : Summable ((fun m : ℕ => Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3)))
      ∘ (fun p : Nat.Primes => (p : ℕ) - 2)) :=
    (pp519_summable_sqrtN N).comp_injective pp519_prime_shift_inj
  exact h0.congr (fun p => by
    show Real.sqrt ((N : ℝ) / (((((p : ℕ) - 2 : ℕ) : ℝ)) + 2) ^ 3)
      = Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))
    rw [pp519_shift_cast p])



/-- LEAF. Prime power tail step. The part of the prime power double sum with
exponents at least two, summed over all primes and all such exponents, is at
most a constant independent of N, of the character and of alpha, times the
square root of N. The exponential damping at the prime powers is what makes the
double sum absolutely convergent. No zero hypothesis, no Mellin integral and no
estimate on the character occur here. -/
theorem prime_power_tail519 :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ α : ℝ,
        ‖∑' p : Nat.Primes, ∑' k : ℕ,
            (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
          ≤ B * Real.sqrt N := by
  refine ⟨11, by norm_num, 0, ?_⟩
  intro N hN q hq χ α
  have hmin : Summable (fun m : ℕ => min 1 ((N : ℝ) / (((m : ℝ) + 2) ^ 2))) :=
    pp519_summable_min N hN
  have hsq : Summable (fun m : ℕ => Real.sqrt ((N : ℝ) / (((m : ℝ) + 2) ^ 3))) :=
    pp519_summable_sqrtN N
  have hp1 : Summable (fun p : Nat.Primes => min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))) :=
    pp519_summable_prime_one N hN
  have hp2 : Summable (fun p : Nat.Primes => Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))) :=
    pp519_summable_prime_two N
  have hmaj : Summable (fun p : Nat.Primes =>
      1 / 2 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
        + 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))) :=
    (hp1.mul_left (1 / 2)).add (hp2.mul_left (7 / 2))
  have hinner : Summable (fun p : Nat.Primes =>
      ‖∑' k : ℕ, (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => pp519_inner N hN q χ α p) hmaj
  have h1 := pp519_prime_le_one N hN
  have h2 := pp519_prime_le_two N
  have hb1 := pp519_sum_one N hN
  have hb2 := pp519_sum_two N hN
  calc ‖∑' p : Nat.Primes, ∑' k : ℕ,
        (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
          (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
            Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖
      ≤ ∑' p : Nat.Primes, ‖∑' k : ℕ, (((k : ℂ) + 2)⁻¹ * χ ((p : ℕ) ^ (k + 2)) *
          (Real.exp (-(((p : ℕ) : ℝ) ^ (k + 2) / (N : ℝ))) : ℂ) *
            Complex.exp ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (k + 2))) : ℝ) * Complex.I))‖ :=
        norm_tsum_le_tsum_norm hinner
    _ ≤ ∑' p : Nat.Primes, (1 / 2 * min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2))
          + 7 / 2 * Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))) :=
        hinner.tsum_le_tsum (fun p => pp519_inner N hN q χ α p) hmaj
    _ = 1 / 2 * (∑' p : Nat.Primes, min 1 ((N : ℝ) / (((p : ℕ) : ℝ) ^ 2)))
          + 7 / 2 * (∑' p : Nat.Primes, Real.sqrt ((N : ℝ) / (((p : ℕ) : ℝ) ^ 3))) := by
        rw [Summable.tsum_add (hp1.mul_left (1 / 2)) (hp2.mul_left (7 / 2)),
          tsum_mul_left, tsum_mul_left]
    _ ≤ 1 / 2 * (4 * Real.sqrt (N : ℝ)) + 7 / 2 * (2 * Real.sqrt (N : ℝ)) := by
        have h3 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
        nlinarith [h1, h2, hb1, hb2]
    _ ≤ 11 * Real.sqrt (N : ℝ) := by
        have h3 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
        linarith


end LeanLab.Linnik1951.Task519
