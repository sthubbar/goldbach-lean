module

public import LeanLab.LZCesaroShort.Lemma8Proof

/-!
# P0058 Section 5 under RH, proved

Lab proof, unit U-5323, CLOUD 20261019T0914Z-cloud21. AI wrote this file. Known mathematics,
CONDITIONAL ON `RiemannHypothesis`, Mathlib's own definition, and on nothing else.
Under RH, `S/H ≪ H √N log² N + N` for `3 ≤ N`, `2 ≤ H ≤ N`, where
`S = Σ_ρ ((N+H)^{ρ+2} - 2N^{ρ+2} + (N-H)^{ρ+2})/(ρ(ρ+1)(ρ+2))`.
Each term is `≪ H² √N/|ρ|` by writing the second difference as a double integral of `y^ρ`, and
`≪ N³/|ρ|³` trivially; the sum splits at `|ρ| = N²/H`, with the zero counts of
`PNTPort.ExplicitPsi1.fiber_count`. Binary Goldbach is open.
-/

@[expose] public section


open Finset Complex
open scoped ArithmeticFunction.vonMangoldt Chebyshev

noncomputable section
namespace LeanLab.LZCesaroShort

open PNTPort.ExplicitPsi1

/-- Under RH every zero in `Zall` has real part `1/2`. -/
lemma rh_re (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ Zall) : ρ.re = 1 / 2 := by
  have h := hρ
  rw [Zall_eq] at h
  obtain ⟨hz, h0, h1⟩ := h
  apply hRH ρ hz
  · rintro ⟨n, rfl⟩
    simp at h0
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · rintro rfl; simp at h1

lemma norm_le_norm_add {ρ : ℂ} (h : 0 ≤ ρ.re) {k : ℝ} (hk : 0 ≤ k) : ‖ρ‖ ≤ ‖ρ + k‖ := by
  have e1 : ‖ρ‖ ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e2 : ‖ρ + k‖ ^ 2 = (ρ.re + k) ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have : ‖ρ‖ ^ 2 ≤ ‖ρ + k‖ ^ 2 := by rw [e1, e2]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- The `ρ`-term of `S`. -/
def Dz (N H : ℕ) (ρ : ℂ) : ℂ :=
  (((N : ℂ) + H) ^ (ρ + 2) - 2 * (N : ℂ) ^ (ρ + 2) + ((N : ℂ) - H) ^ (ρ + 2)) /
    (ρ * (ρ + 1) * (ρ + 2))

lemma norm_cpow_le_of_le {y B : ℝ} (hy : 0 ≤ y) (hyB : y ≤ B) (hB : 1 ≤ B) {r : ℂ}
    (hr0 : 0 < r.re) {e : ℝ} (hre : r.re ≤ e) : ‖(y : ℂ) ^ r‖ ≤ B ^ e := by
  rcases eq_or_lt_of_le hy with h0 | hpos
  · rw [← h0, ofReal_zero, zero_cpow (by intro h; rw [h] at hr0; simp at hr0), norm_zero]
    positivity
  · rw [norm_cpow_eq_rpow_re_of_pos hpos]
    calc y ^ r.re ≤ B ^ r.re := Real.rpow_le_rpow hy hyB hr0.le
      _ ≤ B ^ e := Real.rpow_le_rpow_of_exponent_le hB hre

/-- **Bound A**: under `Re ρ = 1/2`, the `ρ`-term of `S` is at most `H² √(2N)/|ρ|`. -/
lemma Dz_bound_A {N H : ℕ} (hHN : H ≤ N) (hN : 1 ≤ N) {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖Dz N H ρ‖ ≤ (H : ℝ) ^ 2 * (2 * N) ^ (1 / 2 : ℝ) / ‖ρ‖ := by
  have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set a : ℝ := (N : ℝ) - H with ha
  set c : ℝ := (N : ℝ) + H with hc
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hρ1 : ρ + 1 ≠ 0 := by intro h; have := congr_arg re h; simp at this; linarith
  have hρ2 : ρ + 2 ≠ 0 := by intro h; have := congr_arg re h; simp at this; linarith
  have hr1 : -1 < (ρ + 1).re := by simp; linarith
  have hr0 : -1 < ρ.re := by linarith
  have hcont : Continuous fun u : ℝ => (u : ℂ) ^ (ρ + 1) :=
    continuous_ofReal_cpow_const (by simp; linarith)
  -- step 1: the numerator as a difference of two integrals
  have hI : ∀ α β : ℝ, ∫ u in α..β, (u : ℂ) ^ (ρ + 1) =
      ((β : ℂ) ^ (ρ + 2) - (α : ℂ) ^ (ρ + 2)) / (ρ + 2) := by
    intro α β
    rw [integral_cpow (Or.inl hr1), show ρ + 1 + 1 = ρ + 2 by ring]
  have hnum : ((N : ℂ) + H) ^ (ρ + 2) - 2 * (N : ℂ) ^ (ρ + 2) + ((N : ℂ) - H) ^ (ρ + 2) =
      (ρ + 2) * ((∫ u in (N : ℝ)..c, (u : ℂ) ^ (ρ + 1)) - ∫ u in a..(N : ℝ), (u : ℂ) ^ (ρ + 1)) := by
    rw [hI, hI, hc, ha]; push_cast; field_simp; ring
  -- step 2: shift the second integral
  have hshift : ∫ u in a..(N : ℝ), (u : ℂ) ^ (ρ + 1) =
      ∫ u in (N : ℝ)..c, ((u - H : ℝ) : ℂ) ^ (ρ + 1) := by
    rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => (u : ℂ) ^ (ρ + 1))]
    congr 1 <;> simp [ha, hc]
  have hdiff : (∫ u in (N : ℝ)..c, (u : ℂ) ^ (ρ + 1)) - ∫ u in a..(N : ℝ), (u : ℂ) ^ (ρ + 1) =
      ∫ u in (N : ℝ)..c, ((u : ℂ) ^ (ρ + 1) - ((u - H : ℝ) : ℂ) ^ (ρ + 1)) := by
    rw [hshift, ← intervalIntegral.integral_sub]
    · exact hcont.intervalIntegrable _ _
    · exact (hcont.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  -- step 3: the inner difference
  have hinner : ∀ u : ℝ, (N : ℝ) < u → u ≤ c →
      ‖(u : ℂ) ^ (ρ + 1) - ((u - H : ℝ) : ℂ) ^ (ρ + 1)‖ ≤ ‖ρ + 1‖ * (H * (2 * N) ^ (1 / 2 : ℝ)) := by
    intro u hu1 hu2
    have e : (u : ℂ) ^ (ρ + 1) - ((u - H : ℝ) : ℂ) ^ (ρ + 1) =
        (ρ + 1) * ∫ y in (u - H)..u, (y : ℂ) ^ ρ := by
      rw [integral_cpow (Or.inl hr0)]; field_simp
    rw [e, norm_mul]
    gcongr
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := u - H) (b := u)
      (C := (2 * N) ^ (1 / 2 : ℝ)) (f := fun y : ℝ => (y : ℂ) ^ ρ) (fun y hy => by
        rw [Set.uIoc_of_le (by linarith)] at hy
        exact norm_cpow_le_of_le (by linarith [hy.1]) (by linarith [hy.2]) (by linarith)
          (by rw [hre]; norm_num) (le_of_eq hre))
    have hl : |u - (u - H)| = (H : ℝ) := by
      rw [show u - (u - H) = (H : ℝ) by ring]; exact abs_of_nonneg (by positivity)
    rw [hl] at this
    linarith [this]
  have houter : ‖∫ u in (N : ℝ)..c, ((u : ℂ) ^ (ρ + 1) - ((u - H : ℝ) : ℂ) ^ (ρ + 1))‖ ≤
      ‖ρ + 1‖ * (H * (2 * N) ^ (1 / 2 : ℝ)) * H := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (N : ℝ)) (b := c)
      (C := ‖ρ + 1‖ * (H * (2 * N) ^ (1 / 2 : ℝ)))
      (f := fun u : ℝ => (u : ℂ) ^ (ρ + 1) - ((u - H : ℝ) : ℂ) ^ (ρ + 1)) (fun u hu => by
        rw [Set.uIoc_of_le (by rw [hc]; linarith)] at hu
        exact hinner u hu.1 hu.2)
    have hl : |c - N| = (H : ℝ) := by
      rw [hc, show (N : ℝ) + H - N = H by ring]; exact abs_of_nonneg (by positivity)
    rwa [hl] at this
  -- assemble
  rw [Dz, hnum, hdiff]
  have e2 : (ρ + 2) * (∫ u in (N : ℝ)..c, ((u : ℂ) ^ (ρ + 1) - ((u - H : ℝ) : ℂ) ^ (ρ + 1))) /
      (ρ * (ρ + 1) * (ρ + 2)) =
      (∫ u in (N : ℝ)..c, ((u : ℂ) ^ (ρ + 1) - ((u - H : ℝ) : ℂ) ^ (ρ + 1))) / (ρ * (ρ + 1)) := by
    field_simp
  rw [e2, norm_div, norm_mul]
  have hn0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hn1 : 0 < ‖ρ + 1‖ := norm_pos_iff.mpr hρ1
  rw [div_le_div_iff₀ (by positivity) hn0]
  calc _ ≤ ‖ρ + 1‖ * (H * (2 * N) ^ (1 / 2 : ℝ)) * H * ‖ρ‖ := by gcongr
    _ = (H : ℝ) ^ 2 * (2 * N) ^ (1 / 2 : ℝ) * (‖ρ‖ * ‖ρ + 1‖) := by ring

/-- **Bound B**: for `0 < Re ρ < 1`, the `ρ`-term of `S` is at most `4 (2N)³/|ρ|³`. -/
lemma Dz_bound_B {N H : ℕ} (hHN : H ≤ N) (hN : 1 ≤ N) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ‖Dz N H ρ‖ ≤ 4 * (2 * (N : ℝ)) ^ 3 / ‖ρ‖ ^ 3 := by
  have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have hr : 0 < (ρ + 2).re := by simp; linarith
  have hre : (ρ + 2).re ≤ 3 := by simp; linarith
  have hB : (1 : ℝ) ≤ 2 * N := by linarith
  have b : ∀ y : ℝ, 0 ≤ y → y ≤ 2 * N → ‖(y : ℂ) ^ (ρ + 2)‖ ≤ (2 * (N : ℝ)) ^ 3 := by
    intro y hy hyB
    have := norm_cpow_le_of_le hy hyB hB hr hre
    rwa [show (2 * (N : ℝ)) ^ (3 : ℝ) = (2 * (N : ℝ)) ^ 3 by norm_cast] at this
  have b1 := b ((N : ℝ) + H) (by positivity) (by linarith)
  have b2 := b (N : ℝ) (by positivity) (by linarith)
  have b3 := b ((N : ℝ) - H) (by linarith) (by linarith)
  push_cast at b1 b2 b3
  have hden : ‖ρ‖ ^ 3 ≤ ‖ρ * (ρ + 1) * (ρ + 2)‖ := by
    rw [norm_mul, norm_mul]
    have e1 := norm_le_norm_add h0.le (k := 1) zero_le_one
    have e2 := norm_le_norm_add h0.le (k := 2) zero_le_two
    push_cast at e1 e2
    calc ‖ρ‖ ^ 3 = ‖ρ‖ * ‖ρ‖ * ‖ρ‖ := by ring
      _ ≤ ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ := by gcongr
  have hn0 : 0 < ‖ρ‖ ^ 3 := by have := norm_pos_iff.mpr hρ0; positivity
  rw [Dz, norm_div, div_le_div_iff₀ (lt_of_lt_of_le hn0 hden) hn0]
  have hnum : ‖((N : ℂ) + H) ^ (ρ + 2) - 2 * (N : ℂ) ^ (ρ + 2) + ((N : ℂ) - H) ^ (ρ + 2)‖ ≤
      4 * (2 * (N : ℝ)) ^ 3 := by
    have t1 := norm_add_le (((N : ℂ) + H) ^ (ρ + 2) - 2 * (N : ℂ) ^ (ρ + 2)) (((N : ℂ) - H) ^ (ρ + 2))
    have t2 := norm_sub_le (((N : ℂ) + H) ^ (ρ + 2)) (2 * (N : ℂ) ^ (ρ + 2))
    have t3 : ‖2 * (N : ℂ) ^ (ρ + 2)‖ = 2 * ‖(N : ℂ) ^ (ρ + 2)‖ := by
      rw [norm_mul]; simp
    linarith
  have : 0 ≤ 4 * (2 * (N : ℝ)) ^ 3 := by positivity
  calc _ ≤ 4 * (2 * (N : ℝ)) ^ 3 * ‖ρ‖ ^ 3 := by gcongr
    _ ≤ 4 * (2 * (N : ℝ)) ^ 3 * ‖ρ * (ρ + 1) * (ρ + 2)‖ := by gcongr

lemma sum_inv_le_log (N : ℕ) : ∑ n ∈ Icc 5 N, 1 / ((n : ℝ) - 1) ≤ 1 + Real.log N := by
  have h1 : ∑ n ∈ Icc 5 N, 1 / ((n : ℝ) - 1) ≤ ∑ n ∈ Ico 2 (N + 2), 1 / ((n : ℝ) - 1) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn; rw [mem_Icc] at hn; rw [mem_Ico]; omega
    · intro n hn _
      rw [mem_Ico] at hn
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
      have : 0 < (n : ℝ) - 1 := by linarith
      positivity
  have h2 : ∑ n ∈ Ico 2 (N + 2), 1 / ((n : ℝ) - 1) = (harmonic N : ℝ) := by
    rw [sum_Ico_eq_sum_range, show N + 2 - 2 = N by omega, harmonic]
    push_cast
    apply sum_congr rfl; intro k _
    rw [one_div]; congr 1; push_cast; ring
  rw [h2] at h1
  exact h1.trans (harmonic_le_one_add_log N)

/-- `Σ_{ρ, |Im ρ| ≤ T} m(ρ)/|ρ| ≤ C (log T + 1)²`, unconditional. -/
theorem zero_sum_inv_bound : ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ T : ℝ, 1 ≤ T →
    ∑ ρ ∈ (zeros_rect_finite 2 T).toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤
      C1 * (Real.log T + 1) ^ 2 := by
  obtain ⟨C, hC, hfib⟩ := fiber_count
  set Z4 := (zeros_rect_finite 2 4).toFinset
  set B4 := ∑ ρ ∈ Z4, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖
  have hB4 : 0 ≤ B4 := sum_nonneg fun ρ _ => by positivity
  refine ⟨B4 + 8 * C, by positivity, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  set s := (zeros_rect_finite 2 T).toFinset with hs
  set f : ℂ → ℝ := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ with hf
  have hf0 : ∀ ρ, 0 ≤ f ρ := fun ρ => by simp only [hf]; positivity
  have hmemT := fun z => mem_rect (c := 2) (T := T) (by norm_num) hT0 (z := z)
  have hmem4 := fun z => mem_rect (c := 2) (T := 4) (by norm_num) (by norm_num) (z := z)
  have hsZ : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ ((-1 / 2 ≤ ρ.re ∧ ρ.re ≤ 2) ∧ (-T ≤ ρ.im ∧ ρ.im ≤ T)) := by
    intro ρ hρ
    rw [hs, Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.2, (hmemT ρ).mp hρ.1⟩
  rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ => |ρ.im| ≤ 4)]
  have hA : ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 4), f ρ ≤ B4 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun x _ _ => hf0 x)
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hz, hre, _⟩ := hsZ ρ hρ.1
    rw [Set.Finite.mem_toFinset]
    exact ⟨(hmem4 ρ).mpr ⟨hre, abs_le.mp hρ.2⟩, hz⟩
  set N := ⌈T⌉₊ with hN
  have hNT : (N : ℝ) ≤ T + 1 := (Nat.ceil_lt_add_one hT0).le
  have hmaps : ∀ ρ ∈ s.filter (fun ρ => ¬ |ρ.im| ≤ 4), ⌈|ρ.im|⌉₊ ∈ Finset.Icc 5 N := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨_, _, him⟩ := hsZ ρ hρ.1
    rw [Finset.mem_Icc]
    constructor
    · have : (4 : ℝ) < |ρ.im| := lt_of_not_ge hρ.2
      have h4 : 4 < ⌈|ρ.im|⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast this)
      omega
    · exact Nat.ceil_mono (abs_le.mpr him)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hB : ∀ n ∈ Finset.Icc 5 N,
      ∑ ρ ∈ (s.filter (fun ρ => ¬ |ρ.im| ≤ 4)).filter (fun ρ => ⌈|ρ.im|⌉₊ = n), f ρ ≤
        4 * C * Real.log N * (1 / ((n : ℝ) - 1)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
    set u := (s.filter (fun ρ => ¬ |ρ.im| ≤ 4)).filter (fun ρ => ⌈|ρ.im|⌉₊ = n)
    have hu : ∀ ρ ∈ u, riemannZeta ρ = 0 ∧ (n : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ n := by
      intro ρ hρ
      simp only [u, Finset.mem_filter] at hρ
      have hc := (Nat.ceil_eq_iff (by omega)).mp hρ.2
      rw [Nat.cast_sub (by omega)] at hc
      push_cast at hc
      exact ⟨(hsZ ρ hρ.1.1).1, hc⟩
    have hcount := hfib n hn.1 u hu
    have hd : 0 < (n : ℝ) - 1 := by linarith
    calc ∑ ρ ∈ u, f ρ ≤ ∑ ρ ∈ u, (analyticOrderNatAt riemannZeta ρ : ℝ) / ((n : ℝ) - 1) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          obtain ⟨_, hlo, _⟩ := hu ρ hρ
          simp only [hf]
          apply div_le_div_of_nonneg_left (by positivity) hd
          exact le_trans hlo.le (abs_im_le_norm ρ)
      _ = (∑ ρ ∈ u, (analyticOrderNatAt riemannZeta ρ : ℝ)) / ((n : ℝ) - 1) := by
          rw [Finset.sum_div]
      _ ≤ 4 * C * Real.log n / ((n : ℝ) - 1) := div_le_div_of_nonneg_right hcount hd.le
      _ ≤ 4 * C * Real.log N / ((n : ℝ) - 1) := by
          gcongr
      _ = 4 * C * Real.log N * (1 / ((n : ℝ) - 1)) := by ring
  have hsum := Finset.sum_le_sum hB
  rw [← Finset.mul_sum] at hsum
  have hh := sum_inv_le_log N
  have hlog : Real.log N ≤ Real.log T + 1 := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith [Real.log_nonneg hT]
    have : Real.log N ≤ Real.log (T + 1) := Real.log_le_log (by exact_mod_cast hpos) hNT
    have h2 : Real.log (T + 1) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h2
    have := Real.log_two_lt_d9
    linarith
  have hL : 0 ≤ Real.log T := Real.log_nonneg hT
  have e1 : 4 * C * Real.log N * ∑ n ∈ Icc 5 N, 1 / ((n : ℝ) - 1) ≤
      4 * C * (Real.log T + 1) * (Real.log T + 2) := by
    calc 4 * C * Real.log N * ∑ n ∈ Icc 5 N, 1 / ((n : ℝ) - 1)
        ≤ 4 * C * Real.log N * (1 + Real.log N) := by gcongr
      _ ≤ 4 * C * (Real.log T + 1) * (1 + (Real.log T + 1)) := by gcongr
      _ = 4 * C * (Real.log T + 1) * (Real.log T + 2) := by ring
  have e2 : B4 ≤ B4 * (Real.log T + 1) ^ 2 := by
    have : 1 ≤ (Real.log T + 1) ^ 2 := by nlinarith
    nlinarith
  have e3 : 4 * C * (Real.log T + 1) * (Real.log T + 2) ≤ 8 * C * (Real.log T + 1) ^ 2 := by
    have : 0 ≤ 4 * C * (Real.log T + 1) := by positivity
    nlinarith
  calc _ ≤ B4 + 4 * C * Real.log N * ∑ n ∈ Icc 5 N, 1 / ((n : ℝ) - 1) := add_le_add hA hsum
    _ ≤ B4 * (Real.log T + 1) ^ 2 + 8 * C * (Real.log T + 1) ^ 2 := by linarith
    _ = (B4 + 8 * C) * (Real.log T + 1) ^ 2 := by ring

lemma inv_sq_le_hw {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2 ≤ 3 * hw ρ := by
  have hpos : 1 / 2 ≤ ‖ρ‖ := by rw [← hre]; exact (le_abs_self _).trans (abs_re_le_norm ρ)
  have h1 : ‖ρ + 1‖ ≤ 3 * ‖ρ‖ := by
    calc ‖ρ + 1‖ ≤ ‖ρ‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 * ‖ρ‖ := by rw [norm_one]; linarith
  have hn : 0 < ‖ρ‖ := by linarith
  have hn1 : 0 < ‖ρ + 1‖ := by
    have := norm_le_norm_add (k := 1) (by rw [hre]; norm_num) zero_le_one (ρ := ρ)
    push_cast at this; linarith
  unfold hw
  rw [norm_mul, show 3 * ((analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)) =
    3 * (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖) by ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hm : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by positivity
  have : ‖ρ‖ * ‖ρ + 1‖ ≤ 3 * ‖ρ‖ ^ 2 := by nlinarith
  nlinarith

/-- **Languasco-Zaccagnini Section 5**, CONDITIONAL ON RH only: `S/H ≪ H √N log² N + N`. -/
theorem lz_sec5_rh_proved : RiemannHypothesis → Sec5RH := by
  intro hRH
  obtain ⟨C1, hC1, hZ1⟩ := zero_sum_inv_bound
  set SH := ∑' ρ : Zall, hw ρ with hSH
  have hSH0 : 0 ≤ SH := tsum_nonneg fun ρ => hw_nonneg ρ
  refine ⟨3, 18 * C1 + 96 * SH, fun N H hN hH2 hHN => ?_⟩
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hH2r : (2 : ℝ) ≤ H := by exact_mod_cast hH2
  have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hN1 : 1 ≤ N := by omega
  set T : ℝ := (N : ℝ) ^ 2 / H with hT
  have hHpos : (0 : ℝ) < H := by linarith
  have hTN : (N : ℝ) ≤ T := by rw [hT, le_div_iff₀ hHpos]; nlinarith
  have hT1 : 1 ≤ T := by linarith
  set A : ℝ := (H : ℝ) ^ 2 * (2 * N) ^ (1 / 2 : ℝ) with hA
  set B : ℝ := 4 * (2 * (N : ℝ)) ^ 3 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  set g : Zall → ℝ := fun ρ => ‖(analyticOrderNatAt riemannZeta ρ.1 : ℂ) * Dz N H ρ.1‖ with hg
  have hre : ∀ ρ : Zall, ρ.1.re = 1 / 2 := fun ρ => rh_re hRH ρ.2
  have hgB : ∀ ρ : Zall, g ρ ≤ B * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 3) := by
    intro ρ
    simp only [hg, norm_mul, Complex.norm_natCast]
    have hρ : ρ.1 ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} := by
      rw [← Zall_eq]; exact ρ.2
    have := Dz_bound_B hHN hN1 hρ.2.1 hρ.2.2
    calc (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * ‖Dz N H ρ.1‖
        ≤ (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * (B / ‖ρ.1‖ ^ 3) := by gcongr
      _ = B * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 3) := by ring
  have hhalf : ∀ ρ : Zall, 1 / 2 ≤ ‖ρ.1‖ := fun ρ => by
    rw [← hre ρ]; exact (le_abs_self _).trans (abs_re_le_norm _)
  have hcube : ∀ ρ : Zall, ∀ t : ℝ, 0 < t → t ≤ ‖ρ.1‖ →
      (analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 3 ≤
        (1 / t) * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2) := by
    intro ρ t ht htρ
    have hn : 0 < ‖ρ.1‖ := by linarith
    rw [show ‖ρ.1‖ ^ 3 = ‖ρ.1‖ * ‖ρ.1‖ ^ 2 by ring, ← div_div]
    rw [show (1 / t) * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2) =
      (analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2 / t by ring, div_right_comm]
    apply div_le_div_of_nonneg_left (by positivity) ht htρ
  have hgsum : Summable g := by
    refine Summable.of_nonneg_of_le (fun ρ => norm_nonneg _) (fun ρ => ?_)
      (summable_hw.mul_left (B * 2 * 3))
    refine (hgB ρ).trans ?_
    have := hcube ρ (1 / 2) (by norm_num) (hhalf ρ)
    have h3 := inv_sq_le_hw (hre ρ)
    calc B * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 3)
        ≤ B * ((1 / (1 / 2)) * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2)) := by
          gcongr
      _ ≤ B * ((1 / (1 / 2)) * (3 * hw ρ.1)) := by gcongr
      _ = B * 2 * 3 * hw ρ.1 := by ring
  -- the split bound for every finite partial sum
  have hpart : ∀ u : Finset Zall, ∑ ρ ∈ u, g ρ ≤
      A * (C1 * (Real.log T + 1) ^ 2) + B / T * (3 * SH) := by
    intro u
    rw [← Finset.sum_filter_add_sum_filter_not u (fun ρ => ‖ρ.1‖ ≤ T)]
    apply add_le_add
    · calc ∑ ρ ∈ u.filter (fun ρ => ‖ρ.1‖ ≤ T), g ρ
          ≤ ∑ ρ ∈ u.filter (fun ρ => ‖ρ.1‖ ≤ T),
              A * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖) := by
            apply sum_le_sum; intro ρ _
            simp only [hg, norm_mul, Complex.norm_natCast]
            have := Dz_bound_A hHN hN1 (hre ρ)
            calc (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * ‖Dz N H ρ.1‖
                ≤ (analyticOrderNatAt riemannZeta ρ.1 : ℝ) * (A / ‖ρ.1‖) := by gcongr
              _ = A * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖) := by ring
        _ = A * ∑ ρ ∈ (u.filter (fun ρ => ‖ρ.1‖ ≤ T)).map (Function.Embedding.subtype _),
              (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
            rw [Finset.sum_map, Finset.mul_sum]; rfl
        _ ≤ A * ∑ ρ ∈ (zeros_rect_finite 2 T).toFinset,
              (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
            gcongr
            intro ρ hρ
            rw [Finset.mem_map] at hρ
            obtain ⟨⟨ρ', hρ'Z⟩, hρ'u, rfl⟩ := hρ
            rw [Finset.mem_filter] at hρ'u
            rw [Set.Finite.mem_toFinset]
            have hre1 := Zall_re_lt hρ'Z
            have him : |ρ'.im| ≤ T := le_trans (abs_im_le_norm _) hρ'u.2
            refine ⟨(mem_rect (by norm_num) (by linarith)).mpr
              ⟨⟨hρ'Z.2, by simp; linarith⟩, abs_le.mp ?_⟩, hρ'Z.1⟩
            simpa using him
        _ ≤ A * (C1 * (Real.log T + 1) ^ 2) := by gcongr; exact hZ1 T hT1
    · calc ∑ ρ ∈ u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ T), g ρ
          ≤ ∑ ρ ∈ u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ T), B / T * (3 * hw ρ.1) := by
            apply sum_le_sum; intro ρ hρ
            rw [Finset.mem_filter] at hρ
            refine (hgB ρ).trans ?_
            have := hcube ρ T (by linarith) (le_of_lt (lt_of_not_ge hρ.2))
            have h3 := inv_sq_le_hw (hre ρ)
            calc B * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 3)
                ≤ B * ((1 / T) * ((analyticOrderNatAt riemannZeta ρ.1 : ℝ) / ‖ρ.1‖ ^ 2)) := by
                  gcongr
              _ ≤ B * ((1 / T) * (3 * hw ρ.1)) := by gcongr
              _ = B / T * (3 * hw ρ.1) := by ring
        _ = B / T * (3 * ∑ ρ ∈ u.filter (fun ρ => ¬ ‖ρ.1‖ ≤ T), hw ρ.1) := by
            rw [Finset.mul_sum, Finset.mul_sum]
        _ ≤ B / T * (3 * SH) := by
            gcongr
            exact summable_hw.sum_le_tsum _ (fun ρ _ => hw_nonneg ρ)
  have htsum : ∑' ρ, g ρ ≤ A * (C1 * (Real.log T + 1) ^ 2) + B / T * (3 * SH) :=
    Real.tsum_le_of_sum_le (fun ρ => norm_nonneg _) hpart
  have hZH : ZH N H = ∑' ρ : Zall, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * Dz N H ρ.1 := by
    have e : (∑' ρ : Zall, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * Dz N H ρ.1) =
        ∑' ρ : NontrivialZero, (analyticOrderNatAt riemannZeta ρ.1 : ℂ) * Dz N H ρ.1 := by
      rw [Zall_eq]; rfl
    rw [e]; rfl
  have hnorm : ‖ZH N H‖ ≤ A * (C1 * (Real.log T + 1) ^ 2) + B / T * (3 * SH) := by
    rw [hZH]
    exact (norm_tsum_le_tsum_norm hgsum).trans htsum
  -- the final arithmetic
  have hlogN : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlogT : Real.log T ≤ 2 * Real.log N := by
    rw [hT, Real.log_div (by positivity) hHpos.ne', Real.log_pow]
    have : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    push_cast; linarith
  have hL : (Real.log T + 1) ^ 2 ≤ 9 * Real.log N ^ 2 := by
    have : 0 ≤ Real.log T := Real.log_nonneg hT1
    nlinarith
  have hsq : (2 * (N : ℝ)) ^ (1 / 2 : ℝ) ≤ 2 * Real.sqrt N := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    gcongr
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hHpos]
  refine hnorm.trans ?_
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have e1 : A * (C1 * (Real.log T + 1) ^ 2) ≤ 18 * C1 * (H * Real.sqrt N * Real.log N ^ 2) * H := by
    rw [hA]
    calc (H : ℝ) ^ 2 * (2 * N) ^ (1 / 2 : ℝ) * (C1 * (Real.log T + 1) ^ 2)
        ≤ (H : ℝ) ^ 2 * (2 * Real.sqrt N) * (C1 * (9 * Real.log N ^ 2)) := by gcongr
      _ = 18 * C1 * (H * Real.sqrt N * Real.log N ^ 2) * H := by ring
  have e2 : B / T * (3 * SH) = 96 * SH * N * H := by
    rw [hB, hT]; field_simp; ring
  have : 0 ≤ H * Real.sqrt N * Real.log N ^ 2 := by positivity
  calc A * (C1 * (Real.log T + 1) ^ 2) + B / T * (3 * SH)
      ≤ 18 * C1 * (H * Real.sqrt N * Real.log N ^ 2) * H + 96 * SH * N * H := by rw [e2]; linarith
    _ ≤ (18 * C1 + 96 * SH) * (H * Real.sqrt N * Real.log N ^ 2 + N) * H := by
        have : 0 ≤ 18 * C1 * N * H := by positivity
        have : 0 ≤ 96 * SH * (H * Real.sqrt N * Real.log N ^ 2) * H := by positivity
        nlinarith

end LeanLab.LZCesaroShort

namespace LeanLab.LZCesaroShort

/-- With Section 5 now proved, the window positivity of `cesaro_pos_of` is CONDITIONAL ON RH and
the cited Theorem 1 only: under RH, every window `[N - H, N + H]` with `C log N ≤ H ≤ N` and `N`
large carries a positive Fejér weighted count of prime power pairs. Unit U-5323. -/
theorem cesaro_pos_of_thm1 (hRH : RiemannHypothesis) (h1 : Theorem1) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ, N₀ ≤ N → C * Real.log N ≤ H → H ≤ N → 0 < cesaro N H :=
  cesaro_pos_of h1 (lz_sec5_rh_proved hRH)

end LeanLab.LZCesaroShort

