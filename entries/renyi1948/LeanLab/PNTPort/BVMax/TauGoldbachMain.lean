module

public import LeanLab.PNTPort.BVMax.TauGoldbach
public import LeanLab.HeathBrown1985.Elementary
public import LeanLab.PNTPort.BVMax.CoprimeHarm

/-!
# The divisor analogue of binary Goldbach, the main term

Lab proof, unit U-5304, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics.

* in `CoprimeHarm.lean`, `harm_le_prod_mul`: for a finset `S` of primes, `Σ_{d ≤ Q} 1/d ≤ Π_{p ∈ S} p/(p - 1) ·
  Σ_{d ≤ Q, p ∤ d for p ∈ S} 1/d`, by splitting off the `p`-part of `d` one prime at a time;
* `coprime_harm_ge`: `Σ_{d ≤ Q, (d,N)=1} 1/d ≥ (φ(N)/N) log(Q + 1)`;
* `tauSum_ge_totient`: `Σ_{p<N} τ(N - p) ≥ φ(N)/16` for all large `N`, unconditional, ineffective.
  The asymptotic is `c(N) N` with `c(N) ≍ φ(N)/N`, so this is the true order.
-/

@[expose] public section


namespace LeanLab.PNTPort.BVMax

open Finset Real Filter

/-- `liD(N - 1) ≥ (N - 2)/log N`. -/
lemma liD_ge (N : ℕ) (hN : 2 ≤ N) :
    ((N : ℝ) - 2) / Real.log N ≤ liD ((N - 1 : ℕ) : ℝ) := by
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  unfold liD liN
  rw [Nat.floor_natCast]
  have hsub : Icc 2 (N - 1) ⊆ Icc 1 (N - 1) := Icc_subset_Icc_left (by norm_num)
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => div_nonneg zero_le_one (Real.log_natCast_nonneg n)))
  have hterm : ∀ n ∈ Icc 2 (N - 1), (1 : ℝ) / Real.log N ≤ 1 / Real.log n := by
    intro n hn
    rw [mem_Icc] at hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
    exact one_div_le_one_div_of_le (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) hnN)
  have := card_nsmul_le_sum _ _ _ hterm
  rw [nsmul_eq_mul, Nat.card_Icc] at this
  have hc : (((N - 1 + 1 - 2 : ℕ)) : ℝ) = (N : ℝ) - 2 := by
    rw [show N - 1 + 1 - 2 = N - 2 by omega, Nat.cast_sub hN]; norm_num
  rw [hc, mul_one_div] at this
  exact this

/-- The divisor analogue of binary Goldbach: `Σ_{p<N} τ(N - p) ≥ φ(N)/16` for all large `N`,
unconditional, ineffective. -/
theorem tauSum_ge_totient : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (N.totient : ℝ) / 16 ≤ tauSum N := by
  obtain ⟨B, hB, K, hK⟩ := tauSum_lower 2 (by norm_num)
  set K' := max K 1 with hK'
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hll : ∀ᶠ x in atTop, B * Real.log (Real.log x) ≤ Real.log x / 4 := by
    have ho := (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).bound
      (show (0 : ℝ) < 1 / (4 * B) by positivity)
    filter_upwards [ho, Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx hx0
    simp only [Function.comp, id, Real.norm_eq_abs] at hx
    rw [abs_of_nonneg hx0] at hx
    have := le_abs_self (Real.log (Real.log x))
    have h2 : B * Real.log (Real.log x) ≤ B * (1 / (4 * B) * Real.log x) :=
      mul_le_mul_of_nonneg_left (this.trans hx) hB.le
    calc _ ≤ _ := h2
      _ = Real.log x / 4 := by field_simp
  have hbig : ∀ᶠ x in atTop, 144 * K' ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (hll.and hbig)
  refine ⟨max ⌈X0⌉₊ 4, fun N hN => ?_⟩
  have hN4 : 4 ≤ N := le_of_max_le_right hN
  have hNX : X0 ≤ N := (Nat.le_ceil X0).trans (by exact_mod_cast le_of_max_le_left hN)
  obtain ⟨h1, h2⟩ := hX0 N hNX
  set L := Real.log N with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN4' : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφN : (N.totient : ℝ) ≤ N := by exact_mod_cast Nat.totient_le N
  set Q := ⌊Real.sqrt N / L ^ B⌋₊ with hQ
  -- log(Q + 1) ≥ L/4
  have hlogQ : L / 4 ≤ Real.log ((Q : ℝ) + 1) := by
    have hQ1 : Real.sqrt N / L ^ B < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
    have hpos : 0 < Real.sqrt N / L ^ B :=
      div_pos (Real.sqrt_pos.mpr hN0) (Real.rpow_pos_of_pos hL0 B)
    have hl : Real.log (Real.sqrt N / L ^ B) = L / 2 - B * Real.log L := by
      rw [Real.log_div (Real.sqrt_pos.mpr hN0).ne' (Real.rpow_pos_of_pos hL0 B).ne',
        Real.log_sqrt hN0.le, Real.log_rpow hL0]
    have := Real.log_le_log hpos hQ1.le
    linarith
  -- the main term
  have hcop := coprime_harm_ge N Q (by omega)
  have hφd : ∑ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N), (1 : ℝ) / d ≤
      ∑ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N), (1 : ℝ) / d.totient := by
    apply sum_le_sum; intro d hd
    simp only [mem_filter, mem_Icc] at hd
    have h1d : (1 : ℝ) ≤ d.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    exact one_div_le_one_div_of_le (by linarith) (by exact_mod_cast Nat.totient_le d)
  have hli := liD_ge N (by omega)
  have hli0 : 0 ≤ ((N : ℝ) - 2) / L := div_nonneg (by linarith) hL0.le
  have hmain : (N.totient : ℝ) / 8 ≤ liD ((N - 1 : ℕ) : ℝ) *
      ∑ d ∈ (Icc 1 Q).filter (fun d => Nat.Coprime d N), (1 : ℝ) / d.totient := by
    have hS0 : 0 ≤ (N.totient : ℝ) / N * (L / 4) := by positivity
    calc (N.totient : ℝ) / 8 ≤ ((N : ℝ) - 2) / L * ((N.totient : ℝ) / N * (L / 4)) := by
          rw [show ((N : ℝ) - 2) / L * ((N.totient : ℝ) / N * (L / 4)) =
            (N.totient : ℝ) * ((N - 2) / N) / 4 by field_simp]
          have : (1 : ℝ) / 2 ≤ ((N : ℝ) - 2) / N := by
            rw [le_div_iff₀ hN0]; linarith
          nlinarith
      _ ≤ liD ((N - 1 : ℕ) : ℝ) * ((N.totient : ℝ) / N * Real.log ((Q : ℝ) + 1)) := by
          apply mul_le_mul hli _ hS0 (hli0.trans hli)
          exact mul_le_mul_of_nonneg_left hlogQ (by positivity)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left (hcop.trans hφd) (hli0.trans hli)
  -- the error term
  have herr : K * N / L ^ (2 : ℝ) ≤ (N.totient : ℝ) / 16 := by
    have hdt := HeathBrown1985.div_totient_le N (by omega)
    have hom := HeathBrown1985.card_primeFactors_mul_log_two_le N (by omega)
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hom' : (N.primeFactors.card : ℝ) ≤ 2 * L := by
      have h0 : (0 : ℝ) ≤ N.primeFactors.card := Nat.cast_nonneg _
      nlinarith
    have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have hNφ : (N : ℝ) / N.totient ≤ 9 * L := by
      calc (N : ℝ) / N.totient ≤ Real.exp 1 * (1 + N.primeFactors.card) := hdt
        _ ≤ 3 * (1 + 2 * L) :=
            mul_le_mul he (by linarith) (by positivity) (by norm_num)
        _ ≤ 9 * L := by linarith
    have hL2 : L ^ (2 : ℝ) = L * L := by rw [Real.rpow_two, sq]
    rw [hL2]
    have hKN : K * N ≤ K' * N := mul_le_mul_of_nonneg_right (le_max_left _ _) hN0.le
    have hN : (N : ℝ) ≤ 9 * L * N.totient := by
      rw [div_le_iff₀ hφ] at hNφ; linarith
    rw [div_le_iff₀ (by positivity)]
    calc K * N ≤ K' * N := hKN
      _ ≤ K' * (9 * L * N.totient) := mul_le_mul_of_nonneg_left hN (by linarith)
      _ ≤ (N.totient : ℝ) / 16 * (L * L) := by
          have : 144 * K' * (L * N.totient) ≤ L * (L * N.totient) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
          nlinarith
  have hlow := hK N (by omega)
  linarith

end LeanLab.PNTPort.BVMax

