module

public import LeanLab.PNTPort.Selberg.CramerSum

/-!
# Cramér's mean square under RH, exponential weight

Lab proof, unit U-6117, CLOUD 20261020T0618Z-cloud36, T2 toward P0058 Lemma 1 for small `ξ`.
AI wrote this file. CONDITIONAL ON RiemannHypothesis only, through `cramer_sum`.

* `abel_geom`: `Σ_{m<M} e_m q^m = (1 − q) Σ_{X<M} q^X S(X + 1) + q^M S(M)`, `S(X) = Σ_{m<X} e_m`;
* `cramer_weighted`: **under RH**, `Σ_{m<M} (ψ(m) − m)² e^{−m/N} ≤ K' N²` for all `N ≥ 1`, `M`.
-/

@[expose] public section


namespace LeanLab.PNTPort.Selberg

open Finset

lemma abel_geom (e : ℕ → ℝ) (q : ℝ) (M : ℕ) :
    ∑ m ∈ range M, e m * q ^ m
      = (1 - q) * ∑ X ∈ range M, q ^ X * ∑ m ∈ range (X + 1), e m
        + q ^ M * ∑ m ∈ range M, e m := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun X => q ^ X * ∑ m ∈ range (X + 1), e m),
      sum_range_succ e M]
    ring

/-- `x² e^{−x} ≤ 4` for `x ≥ 0`. -/
lemma sq_mul_exp_neg_le {x : ℝ} (hx : 0 ≤ x) : x ^ 2 * Real.exp (-x) ≤ 4 := by
  have h1 : 1 + x / 2 ≤ Real.exp (x / 2) := by linarith [Real.add_one_le_exp (x / 2)]
  have h2 : (x / 2) ^ 2 ≤ Real.exp (x / 2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h3 : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have h4 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have h5 := Real.exp_pos (-x)
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Cramér with the weight `e^{−m/N}`, under RH.** -/
theorem cramer_weighted (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ, 1 ≤ N → ∀ M : ℕ,
      ∑ m ∈ range M, (Chebyshev.psi m - m) ^ 2 * Real.exp (-(m / N)) ≤ K * (N : ℝ) ^ 2 := by
  obtain ⟨K, hK, hS⟩ := cramer_sum hRH
  refine ⟨24 * K, by positivity, fun N hN M => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set q := Real.exp (-(1 / (N : ℝ))) with hq
  set t := 1 - q with ht
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have h := Real.exp_lt_exp.mpr (show -(1 / (N : ℝ)) < 0 by
      have : 0 < 1 / (N : ℝ) := by positivity
      linarith)
    rwa [Real.exp_zero] at h
  have ht0 : 0 < t := by linarith
  have hpow : ∀ m : ℕ, Real.exp (-(m / N)) = q ^ m := by
    intro m; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  -- `1/t ≤ 1 + N`
  have hinv : 1 / t ≤ 1 + N := by
    have h1 : 1 + 1 / (N : ℝ) ≤ Real.exp (1 / N) := by linarith [Real.add_one_le_exp (1 / (N : ℝ))]
    have he : q * Real.exp (1 / N) = 1 := by rw [hq, ← Real.exp_add]; simp
    rw [div_le_iff₀ ht0]
    have : 1 ≤ (1 + N) * (1 - q) := by
      have hqe : q ≤ N / (N + 1) := by
        rw [le_div_iff₀ (by linarith)]
        have : q * (1 + 1 / N) ≤ 1 := by nlinarith
        have e : q * (N + 1) = N * (q * (1 + 1 / N)) := by field_simp
        nlinarith
      have : (1 + (N : ℝ)) * (1 - q) ≥ (1 + N) * (1 - N / (N + 1)) := by nlinarith
      have e : (1 + (N : ℝ)) * (1 - N / (N + 1)) = 1 := by field_simp; ring
      linarith
    linarith
  set e : ℕ → ℝ := fun m => (Chebyshev.psi m - m) ^ 2 with he_def
  have he0 : ∀ m, 0 ≤ e m := fun m => sq_nonneg _
  have hrw : ∑ m ∈ range M, (Chebyshev.psi m - m) ^ 2 * Real.exp (-(m / N))
      = ∑ m ∈ range M, e m * q ^ m := by
    refine sum_congr rfl fun m _ => ?_; rw [hpow]
  rw [hrw, abel_geom e q M]
  -- first term
  have hA : ∑ X ∈ range M, q ^ X * ∑ m ∈ range (X + 1), e m
      ≤ K * ∑ X ∈ range M, ((X : ℝ) + 1) ^ 2 * q ^ X := by
    rw [mul_sum]
    refine sum_le_sum fun X _ => ?_
    have := hS (X + 1)
    push_cast at this
    have hq' : 0 ≤ q ^ X := by positivity
    nlinarith
  have hsum2 : ∑ X ∈ range M, ((X : ℝ) + 1) ^ 2 * q ^ X ≤ 2 / t ^ 3 := by
    -- `Σ (X + 1)² q^X ≤ Σ' = (1 + q)/(1 − q)³`
    have hs : Summable (fun X : ℕ => ((X : ℝ) + 1) ^ 2 * q ^ X) := by
      have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (r := q)
        (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
      have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
        (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
      have h0 := summable_geometric_of_lt_one hq0.le hq1
      refine ((h2.add (h1.mul_left 2)).add h0).congr fun X => ?_
      simp only [pow_one]; ring
    refine (hs.sum_le_tsum _ fun X _ => by positivity).trans ?_
    -- crude: `(X + 1)² q^X ≤ 2 (X + 1)(X + 2)/2 q^X` and the closed form via `tsum` of the
    -- second derivative is avoided: bound termwise by the coefficients of `2/(1 − q)³`
    have hcoef : ∀ X : ℕ, ((X : ℝ) + 1) ^ 2 * q ^ X ≤ 2 * (((X + 2).choose 2 : ℕ) : ℝ) * q ^ X := by
      intro X
      rw [Nat.cast_choose_two]
      push_cast
      have : ((X : ℝ) + 1) ^ 2 ≤ 2 * (((X : ℝ) + 2) * ((X : ℝ) + 2 - 1) / 2) := by
        have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
        ring_nf; nlinarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hgen : HasSum (fun X : ℕ => (((X + 2).choose 2 : ℕ) : ℝ) * q ^ X) (1 / (1 - q) ^ 3) := by
      have := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2
        (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
      simpa [one_div] using this
    calc ∑' X : ℕ, ((X : ℝ) + 1) ^ 2 * q ^ X
        ≤ ∑' X : ℕ, 2 * ((((X + 2).choose 2 : ℕ) : ℝ) * q ^ X) :=
          hs.tsum_le_tsum (fun X => by rw [← mul_assoc]; exact hcoef X) (hgen.summable.mul_left 2)
      _ = 2 * (1 / (1 - q) ^ 3) := by rw [tsum_mul_left, hgen.tsum_eq]
      _ = 2 / t ^ 3 := by rw [ht]; field_simp
  -- second term
  have hB : q ^ M * ∑ m ∈ range M, e m ≤ 4 * K / t ^ 2 := by
    have h1 := hS M
    have hqM : q ^ M ≤ Real.exp (-(t * M)) := by
      have : q ≤ Real.exp (-t) := by
        have := Real.add_one_le_exp (-t); rw [ht] at this ⊢; linarith
      calc q ^ M ≤ Real.exp (-t) ^ M := pow_le_pow_left₀ hq0.le this M
        _ = Real.exp (-(t * M)) := by rw [← Real.exp_nat_mul]; ring_nf
    have hx := sq_mul_exp_neg_le (x := t * M) (by positivity)
    have : q ^ M * (M : ℝ) ^ 2 ≤ 4 / t ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hqM (show 0 ≤ (t * M) ^ 2 by positivity)
      nlinarith
    calc q ^ M * ∑ m ∈ range M, e m ≤ q ^ M * (K * (M : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K * (q ^ M * (M : ℝ) ^ 2) := by ring
      _ ≤ K * (4 / t ^ 2) := mul_le_mul_of_nonneg_left this hK
      _ = 4 * K / t ^ 2 := by ring
  -- assembly
  have hinv2 : 1 / t ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
    have h1 : 1 / t ≤ 2 * N := by linarith
    have : 1 / t ^ 2 = (1 / t) ^ 2 := by rw [one_div_pow]
    rw [this]; nlinarith [show 0 ≤ 1 / t by positivity]
  have hfirst : (1 - q) * ∑ X ∈ range M, q ^ X * ∑ m ∈ range (X + 1), e m ≤ 2 * K / t ^ 2 := by
    rw [← ht]
    calc t * ∑ X ∈ range M, q ^ X * ∑ m ∈ range (X + 1), e m
        ≤ t * (K * (2 / t ^ 3)) := by
          apply mul_le_mul_of_nonneg_left _ ht0.le
          exact hA.trans (mul_le_mul_of_nonneg_left hsum2 hK)
      _ = 2 * K / t ^ 2 := by field_simp
  have : 2 * K / t ^ 2 + 4 * K / t ^ 2 = 6 * K * (1 / t ^ 2) := by ring
  have h6 : 6 * K * (1 / t ^ 2) ≤ 6 * K * (4 * (N : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hinv2 (by positivity)
  linarith

end LeanLab.PNTPort.Selberg

