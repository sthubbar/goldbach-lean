module

public import LeanLab.Tolev2009.CoefficientMoment314

/-!
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 pages 9 to 11, the lcm multiplicity weights.
The fixed denominator gcd map is injective on every lcm fiber.
-/

@[expose] public section

open Finset Real
namespace LeanLab.Tolev2009.LcmMultiplicity346
open LeanLab.HeathBrown1985

/-- Halupczok page 9, count the progression moduli with a prescribed lcm. -/
def fiberCount (K q h : ℕ) : ℕ := ((Icc 1 K).filter (fun k => Nat.lcm k q = h)).card

/-- Halupczok page 9, a fixed q lcm fiber injects into the divisors of q via gcd. -/
theorem fiberCount_le_divisors (K q h : ℕ) (hq : 1 ≤ q) :
    fiberCount K q h ≤ q.divisors.card := by
  unfold fiberCount
  apply Finset.card_le_card_of_injOn (fun k => Nat.gcd k q)
  · intro k hk
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right k q, by omega⟩
  · intro k hk k' hk' he
    change Nat.gcd k q = Nat.gcd k' q at he
    have hk0 := (mem_filter.mp hk).2
    have hk1 := (mem_filter.mp hk').2
    apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < q)
    calc
      k * q = Nat.gcd k q * Nat.lcm k q := (Nat.gcd_mul_lcm k q).symm
      _ = Nat.gcd k' q * Nat.lcm k' q := by rw [hk0, hk1, he]
      _ = k' * q := Nat.gcd_mul_lcm k' q

/-- Halupczok pages 9 to 11, the r fold multiplicity weight at a common denominator. -/
noncomputable def fiberMoment (r R : ℕ) (K h : Fin r → ℕ) : ℝ :=
  ∑ q ∈ Icc 1 R, (∏ i : Fin r, (fiberCount (K i) q (h i) : ℝ)) / (q : ℝ) ^ r

/-- Halupczok pages 9 to 11, all positive degree multiplicity weights have a harmonic bound.
This sufficient bound keeps the common denominator rather than discarding its powers. -/
theorem fiberMoment_le (r R : ℕ) (K h : Fin r → ℕ) (hr : 1 ≤ r) :
    fiberMoment r R K h ≤ Hn R ^ (2 ^ r) := by
  unfold fiberMoment
  refine (sum_le_sum fun q hq => ?_).trans (CoefficientMoment314.reciprocal_moment r R)
  have hq1 := (mem_Icc.mp hq).1
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < q := by linarith
  have hcount : (∏ i : Fin r, (fiberCount (K i) q (h i) : ℝ)) ≤ (q.divisors.card : ℝ) ^ r := by
    calc
      _ ≤ ∏ _i : Fin r, (q.divisors.card : ℝ) := by
        apply prod_le_prod₀
        · intro i _; positivity
        · intro i _; exact_mod_cast fiberCount_le_divisors (K i) q (h i) hq1
      _ = _ := by simp
  have hden : (q : ℝ) ≤ (q : ℝ) ^ r := by
    simpa only [pow_one] using pow_le_pow_right₀ hqR hr
  exact (div_le_div_of_nonneg_right hcount (by positivity)).trans
    (div_le_div_of_nonneg_left (by positivity) hqpos hden)

/-- Halupczok page 9, the one error multiplicity weight is at most the harmonic square. -/
theorem linear_fiber_weight (K R h : ℕ) :
    (∑ q ∈ Icc 1 R, (fiberCount K q h : ℝ) / q) ≤ Hn R ^ 2 := by
  simpa only [fiberMoment, Fin.prod_univ_one, pow_one, Nat.reducePow] using
    fiberMoment_le 1 R (fun _ => K) (fun _ => h) (by norm_num)

/-- Halupczok page 10, a sufficient fourth harmonic power for the two error multiplicity. -/
theorem quadratic_fiber_weight (K H R h t : ℕ) :
    (∑ q ∈ Icc 1 R, (fiberCount K q h : ℝ) * fiberCount H q t / (q : ℝ) ^ 2) ≤
      Hn R ^ 4 := by
  simpa only [fiberMoment, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Nat.reducePow] using
    fiberMoment_le 2 R ![K, H] ![h, t] (by norm_num)

/-- Halupczok pages 10 to 11, a sufficient eighth harmonic power for three errors. -/
theorem cubic_fiber_weight (K H J R h t u : ℕ) :
    (∑ q ∈ Icc 1 R, (fiberCount K q h : ℝ) * fiberCount H q t * fiberCount J q u /
      (q : ℝ) ^ 3) ≤ Hn R ^ 8 := by
  simpa [fiberMoment, Fin.prod_univ_three, mul_assoc] using
    fiberMoment_le 3 R ![K, H, J] ![h, t, u] (by norm_num)

/-- Halupczok page 9, regroup any scalar progression weight by its exact lcm value. -/
theorem sum_lcm_eq (K q M : ℕ) (hq : 1 ≤ q) (f : ℕ → ℝ)
    (hM : ∀ k ∈ Icc 1 K, Nat.lcm k q ≤ M) :
    (∑ k ∈ Icc 1 K, f (Nat.lcm k q)) =
      ∑ h ∈ Icc 1 M, (fiberCount K q h : ℝ) * f h := by
  have hmap : ∀ k ∈ Icc 1 K, Nat.lcm k q ∈ Icc 1 M := by
    intro k hk
    exact mem_Icc.mpr ⟨Nat.lcm_pos (mem_Icc.mp hk).1 hq, hM k hk⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro h hh
  have he : (∑ k ∈ (Icc 1 K).filter (fun k => Nat.lcm k q = h), f (Nat.lcm k q)) =
      ∑ _k ∈ (Icc 1 K).filter (fun k => Nat.lcm k q = h), f h := by
    apply sum_congr rfl
    intro k hk
    rw [(mem_filter.mp hk).2]
  rw [he, sum_const, nsmul_eq_mul]
  rfl

/-- Halupczok page 9, a positive lcm sum is controlled by the divisor multiplicity of q. -/
theorem sum_lcm_le (K q M : ℕ) (hq : 1 ≤ q) (f : ℕ → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hM : ∀ k ∈ Icc 1 K, Nat.lcm k q ≤ M) :
    (∑ k ∈ Icc 1 K, f (Nat.lcm k q)) ≤
      (q.divisors.card : ℝ) * ∑ h ∈ Icc 1 M, f h := by
  rw [sum_lcm_eq K q M hq f hM, mul_sum]
  apply sum_le_sum
  intro h hh
  apply mul_le_mul_of_nonneg_right _ (hf h)
  exact_mod_cast fiberCount_le_divisors K q h hq

/-- Halupczok page 9, transfer a positive reciprocal lcm average to an ordinary discrepancy sum. -/
theorem weighted_lcm_sum_le (K R M : ℕ) (f : ℕ → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hM : ∀ q ∈ Icc 1 R, ∀ k ∈ Icc 1 K, Nat.lcm k q ≤ M) :
    (∑ q ∈ Icc 1 R, ∑ k ∈ Icc 1 K, f (Nat.lcm k q) / q) ≤
      Hn R ^ 2 * ∑ h ∈ Icc 1 M, f h := by
  calc
    _ = ∑ q ∈ Icc 1 R, ∑ h ∈ Icc 1 M, (fiberCount K q h : ℝ) * f h / q := by
      apply sum_congr rfl
      intro q hq
      rw [← sum_div, sum_lcm_eq K q M (mem_Icc.mp hq).1 f (hM q hq), sum_div]
    _ = ∑ h ∈ Icc 1 M, (∑ q ∈ Icc 1 R, (fiberCount K q h : ℝ) / q) * f h := by
      rw [sum_comm]
      apply sum_congr rfl
      intro h hh
      rw [sum_mul]
      apply sum_congr rfl
      intro q hq
      ring
    _ ≤ ∑ h ∈ Icc 1 M, Hn R ^ 2 * f h := by
      apply sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_right (linear_fiber_weight K R h) (hf h)
    _ = _ := by rw [mul_sum]

/-- Halupczok pages 9 to 11, the rth divisor ratio moment has a sufficient harmonic bound. -/
theorem divisor_ratio_moment_le (r R : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈ Icc 1 R, (q.divisors.card : ℝ) ^ r / (q : ℝ) ^ r) ≤ Hn R ^ (2 ^ r) := by
  refine (sum_le_sum fun q hq => ?_).trans (CoefficientMoment314.reciprocal_moment r R)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
  have hq0 : (0 : ℝ) < q := by linarith
  have hden : (q : ℝ) ≤ (q : ℝ) ^ r := by
    simpa only [pow_one] using pow_le_pow_right₀ hq1 hr
  exact div_le_div_of_nonneg_left (by positivity) hq0 hden

/-- Halupczok pages 9 to 11, all positive discrepancy product averages reduce to one ordinary mean.
The r progression ranges can differ, and the common denominator is retained. -/
theorem lcm_product_sum_le (r R M : ℕ) (K : Fin r → ℕ) (hr : 1 ≤ r)
    (f : ℕ → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hM : ∀ q ∈ Icc 1 R, ∀ i : Fin r, ∀ k ∈ Icc 1 (K i), Nat.lcm k q ≤ M) :
    (∑ q ∈ Icc 1 R, (∏ i : Fin r, ∑ k ∈ Icc 1 (K i), f (Nat.lcm k q)) /
      (q : ℝ) ^ r) ≤ Hn R ^ (2 ^ r) * (∑ h ∈ Icc 1 M, f h) ^ r := by
  have hF : 0 ≤ ∑ h ∈ Icc 1 M, f h := sum_nonneg fun h hh => hf h
  calc
    _ ≤ ∑ q ∈ Icc 1 R, ((q.divisors.card : ℝ) ^ r *
        (∑ h ∈ Icc 1 M, f h) ^ r) / (q : ℝ) ^ r := by
      apply sum_le_sum
      intro q hq
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ ∏ _i : Fin r, (q.divisors.card : ℝ) * ∑ h ∈ Icc 1 M, f h := by
          apply prod_le_prod₀
          · intro i _; exact sum_nonneg fun k hk => hf _
          · intro i _; exact sum_lcm_le (K i) q M (mem_Icc.mp hq).1 f hf (hM q hq i)
        _ = _ := by simp [mul_pow]
    _ = (∑ q ∈ Icc 1 R, (q.divisors.card : ℝ) ^ r / (q : ℝ) ^ r) *
        (∑ h ∈ Icc 1 M, f h) ^ r := by
      rw [sum_mul]
      apply sum_congr rfl
      intro q hq
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (divisor_ratio_moment_le r R hr) (pow_nonneg hF r)

end LeanLab.Tolev2009.LcmMultiplicity346
