module

public import Mathlib

/-!
KPP1993 pages 279 through 281, displays 13 through 17.
P0071 page 353, displays 7 through 10.
The finite algebra is independent of the analytic circle method inputs.
AI wrote the Lean code. Goldbach is open.
-/

@[expose] public section


namespace LeanLab.LanguascoPerelli1996.Arithmetic597
open Finset Real Filter

/-- KPP1993 page 279 display 13, with its implicit constant made explicit. -/
theorem display13 {ι : Type*} (s : Finset ι) (rep main err minor tail : ι → ℂ)
    (h : ∀ n ∈ s, rep n - main n + err n = minor n - tail n) :
    ∑ n ∈ s, ‖rep n - main n + err n‖ ^ 2 ≤
      2 * (∑ n ∈ s, ‖minor n‖ ^ 2) + 2 * ∑ n ∈ s, ‖tail n‖ ^ 2 := by
  calc
    _ ≤ ∑ n ∈ s, (2 * ‖minor n‖ ^ 2 + 2 * ‖tail n‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [h n hn]
      have hp := parallelogram_law_with_norm ℂ (minor n) (tail n)
      nlinarith [sq_nonneg ‖minor n + tail n‖]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- KPP1993 page 280 displays 14 through 16, scalar second moment assembly.
The two moment hypotheses are the separate arithmetic estimates in that proof. -/
theorem lemma2_arithmetic {ι : Type*} (s : Finset ι) (tail : ι → ℂ)
    (large small : ι → ℝ) {A B C : ℝ}
    (hpoint : ∀ n ∈ s, ‖tail n‖ ≤ C * (large n + small n))
    (hlarge : ∑ n ∈ s, large n ^ 2 ≤ A)
    (hsmall : ∑ n ∈ s, small n ^ 2 ≤ B) :
    ∑ n ∈ s, ‖tail n‖ ^ 2 ≤ 2 * C ^ 2 * (A + B) := by
  have hpoint2 : ∀ n ∈ s, ‖tail n‖ ^ 2 ≤
      2 * C ^ 2 * (large n ^ 2 + small n ^ 2) := by
    intro n hn
    have hs : ‖tail n‖ ^ 2 ≤ (C * (large n + small n)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hpoint n hn) 2
    have hd : (large n + small n) ^ 2 ≤ 2 * (large n ^ 2 + small n ^ 2) := by
      nlinarith [sq_nonneg (large n - small n)]
    calc
      _ ≤ (C * (large n + small n)) ^ 2 := hs
      _ = C ^ 2 * (large n + small n) ^ 2 := by ring
      _ ≤ C ^ 2 * (2 * (large n ^ 2 + small n ^ 2)) :=
        mul_le_mul_of_nonneg_left hd (sq_nonneg C)
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ s, 2 * C ^ 2 * (large n ^ 2 + small n ^ 2) :=
      Finset.sum_le_sum hpoint2
    _ = 2 * C ^ 2 * ((∑ n ∈ s, large n ^ 2) + ∑ n ∈ s, small n ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hlarge hsmall) (by positivity)

/-- KPP1993 page 281 display 17, the weight transfer from Lemma 2.
For P0071 the weight is the stopped representation count, bounded by a constant times X. -/
theorem display17 {ι : Type*} (s : Finset ι) (weight : ι → ℝ) (tail : ι → ℂ)
    {N B : ℝ} (hweight : ∀ n ∈ s, |weight n| ≤ 2 * N)
    (h : ∑ n ∈ s, ‖tail n‖ ^ 2 ≤ B) :
    ∑ n ∈ s, ‖(weight n : ℂ) * tail n‖ ^ 2 ≤ 4 * N ^ 2 * B := by
  calc
    _ ≤ ∑ n ∈ s, 4 * N ^ 2 * ‖tail n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
      have hw := pow_le_pow_left₀ (abs_nonneg (weight n)) (hweight n hn) 2
      nlinarith [mul_nonneg (show 0 ≤ 4 * N ^ 2 - |weight n| ^ 2 by nlinarith) (sq_nonneg ‖tail n‖)]
    _ = 4 * N ^ 2 * ∑ n ∈ s, ‖tail n‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

/-- KPP1993 page 280 display 15, exact finite expansion of a divisor second moment.
The right side counts simultaneous divisibility before the interval counting bound. -/
theorem divisor_moment_identity (s d : Finset ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ s, (∑ k ∈ d.filter (fun k => k ∣ m), f k) ^ 2) =
      ∑ k ∈ d, ∑ l ∈ d, f k * f l *
        ((s.filter fun m => k ∣ m ∧ l ∣ m).card : ℝ) := by
  simp only [Finset.sum_filter, sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp_rw [ite_mul, mul_ite, zero_mul, mul_zero]
  simp [← ite_and, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm, and_comm]

/-- KPP1993 page 280 display 15, simultaneous divisibility means divisibility by the lcm. -/
theorem divisor_pair_filter (s : Finset ℕ) (d e : ℕ) :
    (s.filter fun m => d ∣ m ∧ e ∣ m) = s.filter (fun m => Nat.lcm d e ∣ m) := by
  ext m
  simp only [Finset.mem_filter, Nat.lcm_dvd_iff]

/-- P0071 page 353, the parameter H is 4 Q squared. -/
theorem short_interval_geometry {X Q : ℝ} (hX : 0 ≤ X) (hQ : 0 ≤ Q)
    (hupper : Q ≤ X ^ (1 / 2 : ℝ) / 2) : 4 * Q ^ 2 ≤ X := by
  have hp := Real.sq_sqrt hX
  rw [← Real.sqrt_eq_rpow] at hupper
  nlinarith [Real.sqrt_nonneg X]

/-- P0071 page 353, every fixed logarithmic power is absorbed by a positive power. -/
theorem eventually_log_pow_le_rpow (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, Real.log X ^ k ≤ X ^ ε := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop (k : ℝ) hε).bound
    (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have hh : |Real.log X ^ k| ≤ X ^ ε := by
    simpa only [Real.norm_eq_abs, one_mul, Real.rpow_natCast,
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ X) _)] using hX
  exact (le_abs_self _).trans hh

/-- KPP1993 page 280 display 15, a short interval contains at most H over k plus one multiples.
This half open version uses Mathlib's exact interval residue count. -/
theorem multiples_Ioc_bound (N H k : ℕ) (hk : 0 < k) :
    (((Finset.Ioc N (N + H)).filter (fun m => k ∣ m)).card : ℝ) ≤ (H : ℝ) / k + 1 := by
  have hc := Nat.Ioc_filter_modEq_card N (N + H) hk 0
  have heq : ((Finset.Ioc N (N + H)).filter (fun m => m ≡ 0 [MOD k])) =
      ((Finset.Ioc N (N + H)).filter fun m => k ∣ m) := by
    ext m
    simp only [Finset.mem_filter, Nat.modEq_zero_iff_dvd]
  rw [heq] at hc
  have hqk : (0 : ℚ) < k := by exact_mod_cast hk
  have hqH : (0 : ℚ) ≤ H := by positivity
  have hb := Int.floor_le (((N + H : ℕ) : ℚ) / k)
  have ha := Int.lt_floor_add_one ((N : ℚ) / k)
  have hh : (max (⌊(((N + H : ℕ) : ℚ) - 0) / k⌋ - ⌊((N : ℚ) - 0) / k⌋) 0 : ℤ) ≤
      (H : ℚ) / k + 1 := by
    push_cast
    simp only [sub_zero]
    apply max_le
    · push_cast at hb
      have hsub : ((N : ℚ) + H) / k - (N : ℚ) / k = (H : ℚ) / k := by ring
      linarith
    · positivity
  have hcQ : ((((Finset.Ioc N (N + H)).filter (fun m => k ∣ m)).card : ℕ) : ℚ) ≤
      (H : ℚ) / k + 1 := by exact_mod_cast hc ▸ hh
  have hmul : ((((Finset.Ioc N (N + H)).filter (fun m => k ∣ m)).card : ℕ) : ℚ) * k ≤ H + k := by
    calc
      _ ≤ ((H : ℚ) / k + 1) * k := mul_le_mul_of_nonneg_right hcQ hqk.le
      _ = H + k := by field_simp
  have hmulR : (((Finset.Ioc N (N + H)).filter (fun m => k ∣ m)).card : ℝ) * k ≤ H + k := by
    exact_mod_cast hmul
  have hRk : (0 : ℝ) < k := by exact_mod_cast hk
  apply (le_div_iff₀ hRk).2 at hmulR
  simpa only [add_div, div_self hRk.ne'] using hmulR

/-- KPP1993 page 280 display 15, the inclusive interval version costs at most one extra endpoint. -/
theorem multiples_Icc_bound (N H k : ℕ) (hk : 0 < k) :
    (((Finset.Icc N (N + H)).filter (fun m => k ∣ m)).card : ℝ) ≤ (H : ℝ) / k + 2 := by
  have hsub : ((Finset.Icc N (N + H)).filter fun m => k ∣ m) ⊆
      insert N ((Finset.Ioc N (N + H)).filter fun m => k ∣ m) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    by_cases heq : m = N
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · exact Finset.mem_insert.mpr (Or.inr (by
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by omega, hm.1.2⟩, hm.2⟩))
  have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le ..)
  have hcR : (((Finset.Icc N (N + H)).filter fun m => k ∣ m).card : ℝ) ≤
      (((Finset.Ioc N (N + H)).filter fun m => k ∣ m).card : ℝ) + 1 := by
    exact_mod_cast hc
  linarith [multiples_Ioc_bound N H k hk]

/-- KPP1993 page 280 display 15, the divisor second moment is controlled by an explicit lcm double sum. -/
theorem divisor_moment_lcm_bound (N H : ℕ) (d : Finset ℕ) (f : ℕ → ℝ)
    (hd : ∀ k ∈ d, 0 < k) (hf : ∀ k ∈ d, 0 ≤ f k) :
    (∑ m ∈ Finset.Icc N (N + H), (∑ k ∈ d.filter (fun k => k ∣ m), f k) ^ 2) ≤
      ∑ k ∈ d, ∑ l ∈ d, f k * f l * ((H : ℝ) / Nat.lcm k l + 2) := by
  rw [divisor_moment_identity]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro l hl
  rw [divisor_pair_filter]
  exact mul_le_mul_of_nonneg_left
    (multiples_Icc_bound N H (Nat.lcm k l) (Nat.lcm_pos (hd k hk) (hd l hl)))
    (mul_nonneg (hf k hk) (hf l hl))

/-- P0071 page 359 corrects the general character loss to log fourth power.
Cauchy Schwarz therefore gives X times log squared in KPP display 12.
The cutoff Q over log to the ten still makes that error at most X over log cubed. -/
theorem corrected_display12_scalar {X Q P L A B E : ℝ} (hX : 0 ≤ X)
    (hQ : 0 < Q) (hL : 1 ≤ L) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hQQ : Q ^ 2 ≤ X) (hP : P = Q / L ^ 10)
    (hE : E ≤ A * Real.sqrt (P / Q) * X * L ^ 2 + B * P * Q) :
    E ≤ (A + B) * X / L ^ 3 := by
  have hL0 : 0 < L := by linarith
  have hratio : P / Q = (1 / L ^ 5) ^ 2 := by
    rw [hP]
    field_simp
  have hsqrt : Real.sqrt (P / Q) = 1 / L ^ 5 := by
    rw [hratio, Real.sqrt_sq (by positivity)]
  have hfirst : Real.sqrt (P / Q) * X * L ^ 2 = X / L ^ 3 := by
    rw [hsqrt]
    field_simp
  have hpow : L ^ 3 ≤ L ^ 10 := pow_le_pow_right₀ hL (by norm_num)
  have hPQ : P * Q ≤ X / L ^ 3 := by
    calc
      _ = Q ^ 2 / L ^ 10 := by rw [hP]; ring
      _ ≤ X / L ^ 10 := div_le_div_of_nonneg_right hQQ (by positivity)
      _ ≤ X / L ^ 3 := div_le_div_of_nonneg_left hX (by positivity) hpow
  calc
    E ≤ A * (Real.sqrt (P / Q) * X * L ^ 2) + B * (P * Q) := by nlinarith [hE]
    _ = A * (X / L ^ 3) + B * (P * Q) := by rw [hfirst]
    _ ≤ A * (X / L ^ 3) + B * (X / L ^ 3) := by gcongr
    _ = _ := by ring

/-- KPP1993 display 17 and P0071 display 7, substitution H equals 4Q squared and P equals Q over L to the ten. -/
theorem tail_cutoff_scalar {X Q P L t : ℝ} (hQ : 0 < Q) (hL : 1 ≤ L)
    (ht : 0 ≤ t) (htL : t ≤ L) (hP : P = Q / L ^ 10) :
    X ^ 2 * (4 * Q ^ 2 * t ^ 3 / P ^ 2 + L ^ 2) ≤ 5 * X ^ 2 * L ^ 23 := by
  have hL0 : 0 < L := by linarith
  have hterm : 4 * Q ^ 2 * t ^ 3 / P ^ 2 = 4 * L ^ 20 * t ^ 3 := by
    rw [hP]
    field_simp
  have htp : t ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ ht htL 3
  have hLp : L ^ 2 ≤ L ^ 23 := pow_le_pow_right₀ hL (by norm_num)
  rw [hterm]
  have hmul := mul_le_mul_of_nonneg_left htp (show 0 ≤ 4 * L ^ 20 by positivity)
  have heq : L ^ 20 * L ^ 3 = L ^ 23 := by ring
  have hinside : 4 * L ^ 20 * t ^ 3 + L ^ 2 ≤ 5 * L ^ 23 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg X) (sub_nonneg.mpr hinside)]

/-- P0071 page 353 display 9, the minor arc envelope after substituting the cutoff. -/
theorem minor_cutoff_identity {X Q P L B δ : ℝ} (hX : 0 < X) (hQ : 0 < Q)
    (hL : 0 < L) (hP : P = Q / L ^ 10) :
    4 * Q ^ 2 * X * L * (B * X ^ (1 + δ) / (P * Q)) =
      4 * B * X ^ (2 + δ) * L ^ 11 := by
  rw [hP, Real.rpow_add hX 1 δ, Real.rpow_add hX 2 δ]
  norm_num
  field_simp

/-- Derived obstruction for the crude divisor route to KPP1993 page 280 display 16.
A polynomial loss cannot be absorbed into the logarithmic bound demanded there. -/
theorem polynomial_loss_not_logarithmic :
    ¬ ((fun x : ℝ => x) =O[atTop] fun x => Real.log x ^ 3) := by
  have hsmall : (fun x : ℝ => Real.log x ^ 3) =o[atTop] (fun x : ℝ => x) := by
    simpa only [Real.rpow_one, Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 1))
  have hne : ∀ᶠ x : ℝ in atTop, Real.log x ^ 3 ≠ 0 := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hlog : 1 ≤ Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
    positivity
  exact hsmall.not_isBigO hne.frequently

end LeanLab.LanguascoPerelli1996.Arithmetic597
