module

public import LeanLab.PNTPort.Selberg.AdditiveBlocks
public import LeanLab.PNTPort.Selberg.AdditiveMeanB

/-!
# Blocks with the sharper remainder

Lab proof, unit U-6014, CLOUD 20261020T0415Z-cloud34, T2 toward IDEAS I-5100. AI wrote this
file: `discrete_mean_w` and `selberg_wide` of `AdditiveBlocks.lean` on `additive_mean_b`.
CONDITIONAL ON RiemannHypothesis only.

`selberg_wide_b`: with `X = e^U`, for `1 ≤ L ≤ X/23` and `X/e² ≤ a`, `b ≤ e²X`,
`Σ_{a ≤ m < b} (ψ(m + L) - ψ(m) - L)² ≤ C (X L (log(X/L) + 3)² + X (log X + 2)²/√L)`;
the second term is below the first for every `L ≥ 1`, up to `log X` against `log(X/L)`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open MeasureTheory Set
open LeanLab.PNTPort.Gallagher

/-- **The discrete mean square on blocks of width `w` in `log`, free parameters.** -/
theorem discrete_mean_w_b (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ w : ℝ, 0 ≤ w → ∀ (η : ℝ) (K : ℕ), 0 < η → 3 ≤ K → 2 * K * η ≤ 1 →
    ∀ (U : ℝ) (L a b : ℕ), Real.exp (U - w) ≤ a → (b : ℝ) ≤ Real.exp (U + w) →
    (L : ℝ) ≤ Real.exp (U - w) → (L : ℝ) ≤ Real.exp (U - w) * ((K : ℝ) - 2) * η →
    ∑ m ∈ Finset.Ico a b, (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 ≤
      C * Real.exp (w ^ 2 / 2 + 2 * w) * Real.exp (2 * U) *
        (2 * K * η * (Real.log (1 / (2 * K * η)) + 3) ^ 2 +
          η ^ 2 * Real.exp U + (η ^ (-1 : ℝ) * (|Real.log η| + 2) ^ 2) * Real.exp (-(2 * U))) := by
  obtain ⟨C1, hC1, hadd⟩ := additive_mean_b hRH
  refine ⟨C1, hC1, fun w hw η K hη hK3 hK U L a b ha hb hL1 hL2 => ?_⟩
  set B := 2 * K * η * (Real.log (1 / (2 * K * η)) + 3) ^ 2 +
    η ^ 2 * Real.exp U + (η ^ (-1 : ℝ) * (|Real.log η| + 2) ^ 2) * Real.exp (-(2 * U)) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ (Real.log (1 / (2 * K * η)) + 3) ^ 2 := sq_nonneg _
    rw [hB]; positivity
  set x₀ := Real.exp (U - w) with hx₀
  have hx₀0 : 0 < x₀ := Real.exp_pos _
  have hLU : (L : ℝ) ≤ Real.exp U := hL1.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨hI, hV⟩ := hadd η K hη hK3 hK U x₀ L hx₀0 (Nat.cast_nonneg L) hL1 hLU hL2
  set f := fun x : ℝ => (Chebyshev.psi (x + L) - Chebyshev.psi x - L) ^ 2 * omg U x with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg (sq_nonneg _) (omg_nonneg _ _)
  set c := Real.exp (-(w ^ 2 / 2)) * Real.exp (-(2 * (U + w))) with hc
  have hc0 : 0 < c := by positivity
  have hkey : Real.exp (w ^ 2 / 2 + 2 * w) * Real.exp (2 * U) * c = 1 := by
    rw [hc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    ring_nf; exact Real.exp_zero
  have hRHS : C1 * Real.exp (w ^ 2 / 2 + 2 * w) * Real.exp (2 * U) * B = C1 * B / c := by
    rw [eq_div_iff hc0.ne']
    calc C1 * Real.exp (w ^ 2 / 2 + 2 * w) * Real.exp (2 * U) * B * c
        = C1 * B * (Real.exp (w ^ 2 / 2 + 2 * w) * Real.exp (2 * U) * c) := by ring
      _ = C1 * B := by rw [hkey, mul_one]
  rw [hRHS, le_div_iff₀ hc0]
  rcases lt_or_ge b a with hba | hab
  · rw [Finset.Ico_eq_empty_of_le hba.le, Finset.sum_empty, zero_mul]; positivity
  have hsub : ∀ m, a ≤ m → Icc (m : ℝ) (m + 1) ⊆ Ici x₀ := by
    intro m hm y hy
    exact le_trans (ha.trans (by exact_mod_cast hm)) hy.1
  have hii : ∀ m, a ≤ m → m < b → IntervalIntegrable f volume (m : ℝ) (m + 1) := by
    intro m hm _
    refine IntegrableOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith)]
    exact hI.mono_set (hsub m hm)
  have hpiece : ∀ m ∈ Finset.Ico a b,
      (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 * c ≤
        ∫ x in (m : ℝ)..(m + 1), f x := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm1 : (m : ℝ) + 1 ≤ b := by exact_mod_cast hm.2
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    have hlow : ∀ x ∈ Ioo (m : ℝ) (m + 1),
        (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 * c ≤ f x := by
      intro x hx
      rw [hf]; simp only
      rw [window_const (m := m) (L := L) ⟨hx.1.le, hx.2⟩]
      refine mul_le_mul_of_nonneg_left (omg_lower_w hw ?_ ?_) (sq_nonneg _)
      · exact le_trans (ha.trans (by exact_mod_cast hm.1)) hx.1.le
      · exact le_trans (by linarith [hx.2]) hb
    have hIoo : IntegrableOn f (Ioo (m : ℝ) (m + 1)) :=
      hI.mono_set (Ioo_subset_Icc_self.trans (hsub m hm.1))
    calc (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 * c
        = ∫ x in Ioo (m : ℝ) (m + 1),
            (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 * c := by
          rw [setIntegral_const, Measure.real, Real.volume_Ioo,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]; ring
      _ ≤ ∫ x in Ioo (m : ℝ) (m + 1), f x :=
          setIntegral_mono_on (integrableOn_const (by simp)) hIoo measurableSet_Ioo hlow
  calc (∑ m ∈ Finset.Ico a b, (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2) * c
      = ∑ m ∈ Finset.Ico a b, (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 * c :=
        Finset.sum_mul _ _ _
    _ ≤ ∑ m ∈ Finset.Ico a b, ∫ x in (m : ℝ)..(m + 1), f x := Finset.sum_le_sum hpiece
    _ = ∫ x in (a : ℝ)..b, f x := sum_unit_intervals f hab hii
    _ = ∫ x in Ioc (a : ℝ) b, f x := intervalIntegral.integral_of_le (by exact_mod_cast hab)
    _ ≤ ∫ x in Ici x₀, f x := by
        refine setIntegral_mono_set hI (ae_of_all _ hf0) (Filter.Eventually.of_forall ?_)
        intro y hy; exact ha.trans hy.1.le
    _ ≤ C1 * B := hV


set_option maxHeartbeats 1000000 in
/-- **Selberg's discrete mean square on the blocks `[X/e², e²X)`, under RH.** With `X = e^U`,
for naturals `1 ≤ L ≤ X/23` and `X/e² ≤ a`, `b ≤ e²X`:
`Σ_{a ≤ m < b} (ψ(m + L) - ψ(m) - L)² ≤ C (X L (log(X/L) + 3)² + X^{5/4} L^{-5/8})`. -/
theorem selberg_wide_b (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (U : ℝ) (L a b : ℕ), 1 ≤ L → 23 * (L : ℝ) ≤ Real.exp U →
    Real.exp (U - 2) ≤ a → (b : ℝ) ≤ Real.exp (U + 2) →
    ∑ m ∈ Finset.Ico a b, (Chebyshev.psi ((m : ℝ) + L) - Chebyshev.psi m - L) ^ 2 ≤
      C * (Real.exp U * L * (Real.log (Real.exp U / L) + 3) ^ 2 +
        Real.exp U / Real.sqrt L * (U + 2) ^ 2) := by
  obtain ⟨C0, hC0, hdm⟩ := discrete_mean_w_b hRH
  set E := Real.exp (2 ^ 2 / 2 + 2 * 2) with hE
  refine ⟨24 * C0 * E, by positivity, fun U L a b hL hLX ha hb => ?_⟩
  set X := Real.exp U with hX
  have hX0 : 0 < X := Real.exp_pos U
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  set r := Real.sqrt L with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hL0
  have hrr : r * r = L := Real.mul_self_sqrt hL0.le
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr hL1
  have hrL : r ≤ L := by nlinarith
  set η := r / X with hη
  have hη0 : 0 < η := div_pos hr0 hX0
  set e2 := Real.exp 2 with he2def
  have he2 : e2 = Real.exp 1 * Real.exp 1 := by rw [he2def, ← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have he2hi : e2 < 7.39 := by rw [he2]; nlinarith
  have he2lo : 7 < e2 := by rw [he2]; nlinarith
  set K := ⌈e2 * r⌉₊ + 3 with hK
  have hKlo : e2 * r + 1 ≤ (K : ℝ) - 2 := by
    rw [hK]; push_cast; linarith [Nat.le_ceil (e2 * r)]
  have hKhi : (K : ℝ) ≤ e2 * r + 4 := by
    rw [hK]; push_cast; linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ e2 * r)]
  have hK3 : 3 ≤ K := by rw [hK]; omega
  have hΔ : 2 * K * η ≤ 23 * L / X := by
    rw [hη, le_div_iff₀ hX0]
    have : 2 * K * (r / X) * X = 2 * K * r := by field_simp
    rw [this]
    nlinarith
  have hΔ1 : 23 * L / X ≤ 1 := by rw [div_le_one hX0]; exact hLX
  have hΔ0 : 0 < 2 * K * η := by
    have : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    positivity
  have hU2 : Real.exp (U - 2) = X / e2 := by rw [hX, Real.exp_sub]
  have hLe : (L : ℝ) ≤ Real.exp (U - 2) := by
    rw [hU2, le_div_iff₀ (by linarith)]; nlinarith
  have hLK : (L : ℝ) ≤ Real.exp (U - 2) * ((K : ℝ) - 2) * η := by
    rw [hU2, hη]
    have : X / e2 * (e2 * r) * (r / X) = L := by
      have : e2 ≠ 0 := by linarith
      field_simp; rw [← hrr]; ring
    calc (L : ℝ) = X / e2 * (e2 * r) * (r / X) := this.symm
      _ ≤ X / e2 * ((K : ℝ) - 2) * (r / X) := by
          have : 0 < e2 := by linarith
          gcongr; linarith
  have hmain := hdm 2 (by norm_num) η K hη0 hK3 (hΔ.trans hΔ1) U L a b ha hb hLe hLK
  refine hmain.trans ?_
  set ℓ := Real.log (X / L) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ hL0]; linarith)
  have hb1 : 2 * K * η * (Real.log (1 / (2 * K * η)) + 3) ^ 2 ≤
      23 * L / X * (ℓ + 3) ^ 2 := by
    refine (bmain_mono hΔ0 hΔ hΔ1).trans ?_
    have hlog : Real.log (1 / (23 * L / X)) ≤ ℓ := by
      rw [hℓ]; apply Real.log_le_log (by positivity)
      rw [one_div_div, div_le_div_iff₀ (by positivity) hL0]; nlinarith
    have hlog0 : 0 ≤ Real.log (1 / (23 * L / X)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hb2 : η ^ 2 * Real.exp U = L / X := by
    rw [hη, ← hX, div_pow, ← hrr]; field_simp
  have hb3 : (η ^ (-1 : ℝ) * (|Real.log η| + 2) ^ 2) * Real.exp (-(2 * U)) * Real.exp (2 * U) ≤
      X / r * (U + 2) ^ 2 := by
    rw [mul_assoc, ← Real.exp_add, show -(2 * U) + 2 * U = 0 by ring, Real.exp_zero, mul_one,
      Real.rpow_neg_one, hη, inv_div]
    have hrX : r ≤ X := by nlinarith
    have hη1 : r / X ≤ 1 := by rw [div_le_one hX0]; exact hrX
    have hlog : |Real.log (r / X)| ≤ U := by
      rw [abs_of_nonpos (Real.log_nonpos (by positivity) hη1), Real.log_div hr0.ne' hX0.ne', hX,
        Real.log_exp]
      have : 0 ≤ Real.log r := Real.log_nonneg hr1
      linarith
    have hU0 : 0 ≤ U := by
      have : (1 : ℝ) ≤ X := by linarith
      rw [hX] at this; linarith [Real.add_one_le_exp U, Real.one_le_exp_iff.mp this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hE2 : Real.exp (2 * U) = X * X := by rw [hX, ← Real.exp_add]; ring_nf
  have hsq : 1 ≤ (ℓ + 3) ^ 2 := by nlinarith
  have hXL : 0 ≤ X * L := by positivity
  set P := (η ^ (-1 : ℝ) * (|Real.log η| + 2) ^ 2) * Real.exp (-(2 * U)) with hP
  have hP0 : 0 ≤ P := by positivity
  have hE0 : 0 ≤ C0 * E := by positivity
  calc C0 * E * Real.exp (2 * U) * (2 * K * η * (Real.log (1 / (2 * K * η)) + 3) ^ 2 +
        η ^ 2 * Real.exp U + P)
      ≤ C0 * E * Real.exp (2 * U) * (23 * L / X * (ℓ + 3) ^ 2 + L / X + P) := by
        rw [hb2]; gcongr
    _ = C0 * E * (23 * (X * L * (ℓ + 3) ^ 2) + X * L + P * Real.exp (2 * U)) := by
        rw [hE2]; field_simp
    _ ≤ C0 * E * (24 * (X * L * (ℓ + 3) ^ 2) + X / r * (U + 2) ^ 2) := by
        rw [hP]
        apply mul_le_mul_of_nonneg_left _ hE0
        nlinarith [mul_le_mul_of_nonneg_left hsq hXL, hb3]
    _ ≤ 24 * C0 * E * (X * L * (ℓ + 3) ^ 2 + X / r * (U + 2) ^ 2) := by
        have : 0 ≤ X / r * (U + 2) ^ 2 := by positivity
        nlinarith

set_option maxHeartbeats 2000000 in
/-- **Selberg's mean square summed over `k < M`, under RH.** -/
theorem selberg_sum_b (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ M L N : ℕ, 1 ≤ L → L ≤ N → M ≤ N →
    ∑ k ∈ Finset.range M, (Chebyshev.psi ((k : ℝ) + L) - Chebyshev.psi k - L) ^ 2 ≤
      C * (N * L * (Real.log (N / L) + 3) ^ 2 + N * ((Real.log N + 2) ^ 2 / Real.sqrt L)
        + (L : ℝ) ^ 3) := by
  obtain ⟨C2, hC2, hw⟩ := selberg_wide_b hRH
  refine ⟨2 * C2 + 476928, by positivity, fun M L N hL hLN hMN => ?_⟩
  set f := fun k : ℕ => (Chebyshev.psi ((k : ℝ) + L) - Chebyshev.psi k - L) ^ 2 with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => sq_nonneg _
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLNr : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hMNr : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hN0 : (0 : ℝ) < N := by linarith
  set ℓ := Real.log (N / L) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ hL0]; linarith)
  have hT1 : 0 ≤ (N : ℝ) * L * (ℓ + 3) ^ 2 := by positivity
  have hT2 : 0 ≤ N * ((Real.log N + 2) ^ 2 / Real.sqrt L) := by positivity
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range M) (fun k => k < 23 * L)]
  -- the small range
  have hsmall : ∑ k ∈ (Finset.range M).filter (fun k => k < 23 * L), f k ≤ 476928 * (L : ℝ) ^ 3 := by
    have hcard : (((Finset.range M).filter (fun k => k < 23 * L)).card : ℝ) ≤ 23 * L := by
      have : (Finset.range M).filter (fun k => k < 23 * L) ⊆ Finset.range (23 * L) := by
        intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; exact hk.2
      have := Finset.card_le_card this
      rw [Finset.card_range] at this
      exact_mod_cast this
    calc ∑ k ∈ (Finset.range M).filter (fun k => k < 23 * L), f k
        ≤ ∑ k ∈ (Finset.range M).filter (fun k => k < 23 * L), 20736 * (L : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          simp only [Finset.mem_filter] at hk
          exact window_small (by exact_mod_cast hk.2)
      _ = ((Finset.range M).filter (fun k => k < 23 * L)).card * (20736 * (L : ℝ) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 23 * L * (20736 * (L : ℝ) ^ 2) := by gcongr
      _ = 476928 * (L : ℝ) ^ 3 := by ring
  -- the large range
  have hlarge : ∑ k ∈ (Finset.range M).filter (fun k => ¬ k < 23 * L), f k ≤
      C2 * (2 * (N * L * (ℓ + 3) ^ 2) + 2 * (N * ((Real.log N + 2) ^ 2 / Real.sqrt L))) := by
    rcases le_or_gt M (23 * L) with hM | hM
    · have : (Finset.range M).filter (fun k => ¬ k < 23 * L) = ∅ := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
        omega
      rw [this, Finset.sum_empty]; positivity
    have hMr : 23 * (L : ℝ) < M := by exact_mod_cast hM
    have hM0 : (0 : ℝ) < M := by linarith
    set q := Real.exp (-2) with hq
    have hq0 : 0 < q := Real.exp_pos _
    have hq1 : q < 1 / 2 := by
      rw [hq, Real.exp_neg]
      have : (2 : ℝ) < Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
      rw [inv_lt_comm₀ (Real.exp_pos 2) (by norm_num)]; linarith
    set J := ⌊Real.log (M / (23 * L)) / 2⌋₊ + 1 with hJ
    set X := fun j : ℕ => (M : ℝ) * q ^ j with hX
    have hqj : ∀ j : ℕ, q ^ j = Real.exp (-(2 * j)) := fun j => by
      rw [hq, ← Real.exp_nat_mul]; ring_nf
    have hX0 : ∀ j, 0 < X j := fun j => by simp only [hX]; positivity
    have hXM : ∀ j, X j ≤ M := fun j => by
      simp only [hX]
      have : q ^ j ≤ 1 := pow_le_one₀ hq0.le (by linarith)
      nlinarith
    have hXL : ∀ j < J, 23 * (L : ℝ) ≤ X j := by
      intro j hj
      have hj' : (j : ℝ) ≤ Real.log (M / (23 * L)) / 2 := by
        have h1 : j ≤ ⌊Real.log (M / (23 * L)) / 2⌋₊ := by omega
        have hpos : 0 ≤ Real.log (M / (23 * L)) / 2 := by
          apply div_nonneg _ (by norm_num)
          exact Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
        exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hpos)
      simp only [hX]; rw [hqj]
      have : Real.exp (2 * j) ≤ M / (23 * L) := by
        rw [← Real.exp_log (show 0 < (M : ℝ) / (23 * L) by positivity)]
        exact Real.exp_le_exp.mpr (by linarith)
      rw [le_div_iff₀ (by positivity)] at this
      rw [Real.exp_neg]
      rw [← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      linarith
    set a := fun j : ℕ => ⌈X j * Real.exp (-2)⌉₊ with ha
    set b := fun j : ℕ => ⌊X j * Real.exp 2⌋₊ with hb
    -- each block
    have hblock : ∀ j ∈ Finset.range J, ∑ k ∈ Finset.Ico (a j) (b j), f k ≤
        C2 * (X j * L * (ℓ + 3) ^ 2 + X j * ((Real.log N + 2) ^ 2 / Real.sqrt L)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hXj := hX0 j
      have hU : Real.exp (Real.log (X j)) = X j := Real.exp_log hXj
      have h := hw (Real.log (X j)) L (a j) (b j) hL (by rw [hU]; exact hXL j hj)
        (by rw [Real.exp_sub, hU, div_eq_mul_inv, ← Real.exp_neg]; exact Nat.le_ceil _)
        (by rw [Real.exp_add, hU]; exact Nat.floor_le (by positivity))
      rw [hU] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hC2)
      have hlog : Real.log (X j / L) ≤ ℓ :=
        Real.log_le_log (by positivity) (div_le_div_of_nonneg_right ((hXM j).trans hMNr) hL0.le)
      have hlog0 : 0 ≤ Real.log (X j / L) :=
        Real.log_nonneg (by rw [le_div_iff₀ hL0]; linarith [hXL j hj])
      have h1 : X j * L * (Real.log (X j / L) + 3) ^ 2 ≤ X j * L * (ℓ + 3) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by positivity)
      have hlX : Real.log (X j) ≤ Real.log N := Real.log_le_log hXj ((hXM j).trans hMNr)
      have hlX0 : 0 ≤ Real.log (X j) := Real.log_nonneg (by linarith [hXL j hj])
      have h2 : X j / Real.sqrt L * (Real.log (X j) + 2) ^ 2 ≤ X j * ((Real.log N + 2) ^ 2 / Real.sqrt L) := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ hXj.le
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
      linarith
    -- covering
    have hcover : ∀ k ∈ (Finset.range M).filter (fun k => ¬ k < 23 * L),
        f k ≤ ∑ j ∈ Finset.range J, if k ∈ Finset.Ico (a j) (b j) then f k else 0 := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hk
      have hkr : 23 * (L : ℝ) ≤ k := by exact_mod_cast hk.2
      have hkM : (k : ℝ) < M := by exact_mod_cast hk.1
      have hk0 : (0 : ℝ) < k := by linarith
      set t := Real.log (M / k) / 2 with ht
      have ht0 : 0 ≤ t := div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hk0]; linarith))
        (by norm_num)
      set j := ⌊t⌋₊ with hjdef
      have hj1 : (j : ℝ) ≤ t := Nat.floor_le ht0
      have hj2 : t < j + 1 := Nat.lt_floor_add_one t
      have hjJ : j < J := by
        have : j ≤ ⌊Real.log (M / (23 * L)) / 2⌋₊ := by
          apply Nat.floor_mono
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact Real.log_le_log (by positivity)
            (div_le_div_of_nonneg_left hM0.le (by positivity) hkr)
        omega
      -- `M e^{-2j-2} < k ≤ M e^{-2j}`
      have hMk : Real.log (M / k) = Real.log M - Real.log k := Real.log_div hM0.ne' hk0.ne'
      have hXj : X j = Real.exp (Real.log M - 2 * j) := by
        simp only [hX]; rw [hqj, Real.exp_sub, Real.exp_log hM0, Real.exp_neg, div_eq_mul_inv]
      have hk_le : (k : ℝ) ≤ X j := by
        rw [hXj, ← Real.exp_log hk0]
        exact Real.exp_le_exp.mpr (by linarith)
      have hk_gt : X j * Real.exp (-2) < k := by
        rw [hXj, ← Real.exp_add, ← Real.exp_log hk0]
        exact Real.exp_lt_exp.mpr (by linarith)
      have hin : k ∈ Finset.Ico (a j) (b j) := by
        rw [Finset.mem_Ico]
        constructor
        · simp only [ha]; exact Nat.ceil_le.mpr hk_gt.le
        · simp only [hb]
          apply Nat.lt_of_succ_le
          apply Nat.le_floor
          push_cast
          have he2 : 7 ≤ Real.exp 2 := by
            have := Real.add_one_le_exp (2 : ℝ)
            have h' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
            have := Real.exp_one_gt_d9
            nlinarith
          have hk1 : (1 : ℝ) ≤ k := by linarith
          nlinarith
      have hmem : j ∈ Finset.range J := Finset.mem_range.mpr hjJ
      calc f k = (if k ∈ Finset.Ico (a j) (b j) then f k else 0) := by rw [ite_eq_left_iff.mpr (fun h => absurd hin h)]
        _ ≤ ∑ j ∈ Finset.range J, if k ∈ Finset.Ico (a j) (b j) then f k else 0 :=
            Finset.single_le_sum (f := fun j => if k ∈ Finset.Ico (a j) (b j) then f k else 0)
              (fun i _ => by split_ifs <;> simp [hf0]) hmem
    have hgeom : ∑ j ∈ Finset.range J, X j ≤ 2 * N := by
      simp only [hX]
      rw [← Finset.mul_sum]
      have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hq0.le (by linarith)
      rw [Finset.range_eq_Ico]
      have h2 : q ^ 0 / (1 - q) ≤ 2 := by
        rw [pow_zero, div_le_iff₀ (by linarith)]; linarith
      nlinarith [h.trans h2]
    calc ∑ k ∈ (Finset.range M).filter (fun k => ¬ k < 23 * L), f k
        ≤ ∑ k ∈ (Finset.range M).filter (fun k => ¬ k < 23 * L),
            ∑ j ∈ Finset.range J, (if k ∈ Finset.Ico (a j) (b j) then f k else 0) :=
          Finset.sum_le_sum hcover
      _ = ∑ j ∈ Finset.range J, ∑ k ∈ (Finset.range M).filter (fun k => ¬ k < 23 * L),
            (if k ∈ Finset.Ico (a j) (b j) then f k else 0) := Finset.sum_comm
      _ ≤ ∑ j ∈ Finset.range J, ∑ k ∈ Finset.Ico (a j) (b j), f k := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hf0 k)
          intro k hk; exact (Finset.mem_filter.mp hk).2
      _ ≤ ∑ j ∈ Finset.range J,
            C2 * (X j * L * (ℓ + 3) ^ 2 + X j * ((Real.log N + 2) ^ 2 / Real.sqrt L)) :=
          Finset.sum_le_sum hblock
      _ = C2 * ((∑ j ∈ Finset.range J, X j) * (L * (ℓ + 3) ^ 2) +
            (∑ j ∈ Finset.range J, X j) * (((Real.log N + 2) ^ 2 / Real.sqrt L))) := by
          rw [← Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ C2 * ((2 * N) * (L * (ℓ + 3) ^ 2) +
            (2 * N) * (((Real.log N + 2) ^ 2 / Real.sqrt L))) := by
          apply mul_le_mul_of_nonneg_left _ hC2
          have : 0 ≤ ((Real.log N + 2) ^ 2 / Real.sqrt L) := by positivity
          have : 0 ≤ (L : ℝ) * (ℓ + 3) ^ 2 := by positivity
          gcongr
      _ = C2 * (2 * (N * L * (ℓ + 3) ^ 2) +
            2 * (N * ((Real.log N + 2) ^ 2 / Real.sqrt L))) := by
          ring
  have hL3 : 0 ≤ (L : ℝ) ^ 3 := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Gallagher's lemma with Selberg's mean square, under RH.** For `1 ≤ L ≤ N`,
`∫_{|β| ≤ 1/(2L)} |Σ_{n<N} (Λ(n) - 1) e(nβ)|² ≤ C (N (log(N/L) + 3)²/L + N^{5/4} L^{-21/8} + L (log N + 1)²)`. -/
theorem gallagher_selberg_b (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N L : ℕ, 1 ≤ L → L ≤ N →
    ∫ β in (-(1 / (2 * L) : ℝ))..(1 / (2 * L)), ‖∑ n ∈ Finset.range N, lam1 n * LeanLab.PNTPort.LargeSieve.e (n * β)‖ ^ 2
      ≤ C * (N * (Real.log (N / L) + 3) ^ 2 / L + N * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2
        + L * (Real.log N + 1) ^ 2) := by
  obtain ⟨C, hC, hs⟩ := selberg_sum_b hRH
  refine ⟨3 * C + 5, by positivity, fun N L hL hLN => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (hL.trans hLN)
  have hg := gallagher_psi N L (by omega)
  have hS : ∑ m ∈ Finset.Ico L N, (Chebyshev.psi (m : ℝ) - Chebyshev.psi ((m - L : ℕ) : ℝ) - L) ^ 2
      = ∑ k ∈ Finset.range (N - L), (Chebyshev.psi ((k : ℝ) + L) - Chebyshev.psi k - L) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.add_sub_cancel_left]; push_cast; ring_nf
  rw [hS] at hg
  have hb := hs (N - L) L N hL hLN (Nat.sub_le N L)
  set q := (Real.log (N / L) + 3) ^ 2 with hq
  set l := (Real.log N + 1) ^ 2 with hl
  set P := N * ((Real.log N + 2) ^ 2 / Real.sqrt L) with hP
  set R := N * ((Real.log N + 2) ^ 2 / Real.sqrt L) / (L : ℝ) ^ 2 with hR
  have hPR : P = R * L ^ 2 := by
    rw [hP, hR]; field_simp
  have hq0 : 0 ≤ q := sq_nonneg _
  have hl1 : 1 ≤ l := by
    have : 0 ≤ Real.log N := Real.log_nonneg hN1
    nlinarith
  have hR0 : 0 ≤ R := by positivity
  have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hsq : (Real.pi / (2 * L)) ^ 2 = Real.pi ^ 2 / 4 / L ^ 2 := by field_simp; ring
  have hinner : (∑ k ∈ Finset.range (N - L), (Chebyshev.psi ((k : ℝ) + L) - Chebyshev.psi k - L) ^ 2)
      + 2 * L * (L * (Real.log N + 1)) ^ 2 ≤ L ^ 2 * (C * (N * q / L + R + L) + 2 * L * l) := by
    have e1 : L ^ 2 * (C * (N * q / L + R + L) + 2 * L * l) =
        C * (N * L * q + P + L ^ 3) + 2 * L * (L ^ 2 * l) := by
      rw [hPR]; field_simp
    rw [e1, hl, mul_pow]
    linarith
  calc _ ≤ _ := hg
    _ ≤ (Real.pi / (2 * L)) ^ 2 * (L ^ 2 * (C * (N * q / L + R + L) + 2 * L * l)) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = Real.pi ^ 2 / 4 * (C * (N * q / L + R + L) + 2 * L * l) := by
        rw [hsq]; field_simp
    _ ≤ 10 / 4 * (C * (N * q / L + R + L * l) + 2 * L * l) := by
        have h1 : 0 ≤ C * (N * q / L + R + L) + 2 * L * l := by positivity
        have h2 : C * (N * q / L + R + L) ≤ C * (N * q / L + R + L * l) := by
          apply mul_le_mul_of_nonneg_left _ hC; nlinarith
        nlinarith
    _ ≤ (3 * C + 5) * (N * q / L + R + L * l) := by
        have : 0 ≤ N * q / L := by positivity
        have : 0 ≤ L * l := by positivity
        nlinarith


end LeanLab.PNTPort.Selberg

