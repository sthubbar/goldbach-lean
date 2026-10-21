module

public import LeanLab.PNTPort.Selberg.AdditiveBlocksB
public import LeanLab.PNTPort.Selberg.CramerSum

/-!
# Selberg's discrete mean square with the small range by Cramér

Lab proof, unit U-6200, CLOUD 20261020T0817Z-cloud38, T2 toward P0058 Lemma 1 for small `ξ`.
AI wrote this file, a copy of `selberg_sum_b` of `AdditiveBlocksB.lean` whose small range
`k < 23L` is bounded by `cramer_sum` instead of the trivial bound. CONDITIONAL ON
RiemannHypothesis only.

`selberg_sum_c`: for `1 ≤ L ≤ N` and `M ≤ N`,
`∑_{k<M} (ψ(k + L) - ψ(k) - L)² ≤ C (N L (log(N/L) + 3)² + N (log N + 2)²/√L + L²)`;
the last term was `L³`, which is larger than the main term once `L > √N`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open MeasureTheory Set
open LeanLab.PNTPort.Gallagher

set_option maxHeartbeats 2000000 in
/-- **Selberg's mean square summed over `k < M`, under RH, with the small range by Cramér.** -/
theorem selberg_sum_c (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ M L N : ℕ, 1 ≤ L → L ≤ N → M ≤ N →
    ∑ k ∈ Finset.range M, (Chebyshev.psi ((k : ℝ) + L) - Chebyshev.psi k - L) ^ 2 ≤
      C * (N * L * (Real.log (N / L) + 3) ^ 2 + N * ((Real.log N + 2) ^ 2 / Real.sqrt L)
        + (L : ℝ) ^ 2) := by
  obtain ⟨C2, hC2, hw⟩ := selberg_wide_b hRH
  obtain ⟨Kc, hKc0, hKc⟩ := cramer_sum hRH
  refine ⟨2 * C2 + 2304 * Kc, by positivity, fun M L N hL hLN hMN => ?_⟩
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
  -- the small range, by Cramér
  have hsmall : ∑ k ∈ (Finset.range M).filter (fun k => k < 23 * L), f k ≤ 2304 * Kc * (L : ℝ) ^ 2 := by
    have hsub : (Finset.range M).filter (fun k => k < 23 * L) ⊆ Finset.range (23 * L) := by
      intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; exact hk.2
    set e := fun j : ℕ => (Chebyshev.psi j - j) ^ 2 with he
    have he0 : ∀ j, 0 ≤ e j := fun j => sq_nonneg _
    have hpt : ∀ k : ℕ, f k ≤ 2 * e (k + L) + 2 * e k := by
      intro k
      simp only [hf, he]
      push_cast
      nlinarith [sq_nonneg (Chebyshev.psi ((k : ℝ) + L) - (k + L) + (Chebyshev.psi k - k))]
    have h1 : ∑ k ∈ (Finset.range M).filter (fun k => k < 23 * L), f k ≤
        ∑ k ∈ Finset.range (23 * L), f k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hf0 k)
    have h2 : ∑ k ∈ Finset.range (23 * L), f k ≤
        2 * ∑ k ∈ Finset.range (23 * L), e (k + L) + 2 * ∑ k ∈ Finset.range (23 * L), e k := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun k _ => hpt k
    have h3 : ∑ k ∈ Finset.range (23 * L), e (k + L) ≤ ∑ j ∈ Finset.range (24 * L), e j := by
      have : ∑ k ∈ Finset.range (23 * L), e (k + L) = ∑ j ∈ Finset.Ico L (24 * L), e j := by
        rw [Finset.sum_Ico_eq_sum_range, show 24 * L - L = 23 * L by omega]
        exact Finset.sum_congr rfl fun k _ => by rw [add_comm]
      rw [this]
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => by
        simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega) (fun j _ _ => he0 j)
    have h4 : ∑ k ∈ Finset.range (23 * L), e k ≤ ∑ j ∈ Finset.range (24 * L), e j :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => by
        simp only [Finset.mem_range] at hj ⊢; omega) (fun j _ _ => he0 j)
    have h5 : ∑ j ∈ Finset.range (24 * L), e j ≤ Kc * ((24 * L : ℕ) : ℝ) ^ 2 := hKc _
    push_cast at h5
    nlinarith
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
  have hL3 : 0 ≤ (L : ℝ) ^ 2 := by positivity
  have hKL : 0 ≤ Kc * (L : ℝ) ^ 2 := by positivity
  nlinarith

end LeanLab.PNTPort.Selberg

